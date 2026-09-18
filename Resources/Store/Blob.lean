import Resources.Core.Receipt
import Resources.Store.Repo

/-!
# Receipts

Content-addressed storage: a file is named by the SHA-256 of its bytes, so
attaching the same PDF twice costs one copy, the URL is permanently cacheable,
and verifying the store is a directory walk.
-/

open Lean SQLite

namespace Resources

private structure AttachmentRow where
  sha256 : String
  mime : String
  bytes : Int64
  origName : Option String
  createdAt : String
  cipherHash : Option String
  wrappedKey : Option String
  deriving Row

namespace Blobs

private def ofRow (r : AttachmentRow) : Attachment :=
  { sha256 := r.sha256, mime := r.mime, bytes := r.bytes.toInt.toNat,
    origName := r.origName, createdAt := r.createdAt,
    cipherHash := r.cipherHash, wrappedKey := r.wrappedKey }

/-- The columns `AttachmentRow` reads, in its order. -/
private def columns : String :=
  "sha256, mime, bytes, orig_name, created_at, cipher_hash, wrapped_key"

/-- Where a blob lives on disk: `blobs/ab/abcdef…`. -/
def path (ctx : Ctx) (sha : String) : System.FilePath :=
  ctx.cfg.blobDir / (sha.take 2).toString / sha

/-- Guesses a content type from a file extension. -/
def mimeOfExtension (name : String) : String :=
  match (name.splitOn ".").getLast? with
  | some e =>
    match e.toLower with
    | "pdf" => "application/pdf"
    | "png" => "image/png"
    | "jpg" | "jpeg" => "image/jpeg"
    | "webp" => "image/webp"
    | "gif" => "image/gif"
    | "svg" => "image/svg+xml"
    | "txt" => "text/plain; charset=utf-8"
    | "csv" => "text/csv; charset=utf-8"
    | "json" => "application/json"
    | "html" => "text/html; charset=utf-8"
    | "js" => "text/javascript; charset=utf-8"
    | "css" => "text/css; charset=utf-8"
    | _ => "application/octet-stream"
  | none => "application/octet-stream"

/--
Stores bytes, returning their hash. Storing the same bytes twice is a no-op.

`cipher` is what a synced node knows and a local-only store does not: the hash
of the ciphertext this file was uploaded to the sequencer as, and the per-blob
key sealed under a realm key. It is a parameter rather than something this file
works out because `Store` sits below `Node` and holds no keys — encrypting and
uploading is `Node/Blobs.lean`, which calls this with what it did.

`realm` is which realm the registration is written in, and it should be the one
whose key sealed the file: the record says where the ciphertext is and what
opens it, and a record kept in a realm that cannot open it tells its readers
about a file they have no way to read.
-/
def put (ctx : Ctx) (bytes : ByteArray) (mime : String)
    (origName : Option String := none)
    (cipher : Option (String × String) := none)
    (realm : RealmId := Realm.selfId) : IO String := do
  let sha := Sha256.hexBytes bytes
  let p := path ctx sha
  if !(← p.pathExists) then
    Files.writeSecretBin p bytes
  let now ← nowStamp
  discard <| ctx.commit "system" [.registerBlob
    { sha256 := sha, mime, bytes := bytes.size, origName, createdAt := now,
      cipherHash := cipher.map (·.1), wrappedKey := cipher.map (·.2) }]
    (realm := realm)
  return sha

/-- Writes a blob's bytes into the store's cache, under the hash they have. -/
def cache (ctx : Ctx) (sha : String) (bytes : ByteArray) : IO Unit := do
  let p := path ctx sha
  unless ← p.pathExists do
    Files.writeSecretBin p bytes

/-- Stores a file from disk. -/
def putFile (ctx : Ctx) (file : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile file
  let name := file.fileName.getD "receipt"
  put ctx bytes (mimeOfExtension name) (some name)

/-- Reads a blob's bytes. -/
def get? (ctx : Ctx) (sha : String) : IO (Option ByteArray) := do
  let p := path ctx sha
  if ← p.pathExists then some <$> IO.FS.readBinFile p else return none

/-- Reads a blob's metadata. -/
def meta? (ctx : Ctx) (sha : String) : IO (Option Attachment) := do
  let r ← Db.row? AttachmentRow ctx.db
    s!"SELECT {columns} FROM attachment WHERE sha256 = {Db.lit sha}"
  return r.map ofRow

/-- Every stored receipt. -/
def list (ctx : Ctx) : IO (Array Attachment) := do
  let rs ← Db.rows AttachmentRow ctx.db
    s!"SELECT {columns} FROM attachment ORDER BY created_at DESC"
  return rs.map ofRow

/-- Links a receipt to a transaction. -/
def attach (ctx : Ctx) (txn : TxId) (sha : String) : IO Unit :=
  discard <| ctx.commit "system" [.attach txn sha]

/-- Unlinks a receipt from a transaction. The bytes stay until `gc`. -/
def detach (ctx : Ctx) (txn : TxId) (sha : String) : IO Unit :=
  discard <| ctx.commit "system" [.detach txn sha]

/--
Deletes blobs no transaction references any more. Returns how many were removed.

The bytes are a file and the record is state, so this is two steps: the file
goes, and the ledger is told to forget it. Doing only the second would leave a
receipt nothing can open.
-/
def gc (ctx : Ctx) : IO Nat := do
  let orphans ← Db.rows String ctx.db
    "SELECT sha256 FROM attachment WHERE sha256 NOT IN (SELECT sha256 FROM txn_attachment)"
  for sha in orphans do
    let p := path ctx sha
    if ← p.pathExists then IO.FS.removeFile p
    discard <| ctx.commit "system" [.forgetBlob sha]
  return orphans.size

end Blobs

end Resources
