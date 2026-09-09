import Resources.Store.Repo

/-!
# Receipts

Content-addressed storage: a file is named by the SHA-256 of its bytes, so
attaching the same PDF twice costs one copy, the URL is permanently cacheable,
and verifying the store is a directory walk.
-/

open Lean SQLite

namespace Resources

/-- Metadata for a stored file. -/
structure Attachment where
  sha256 : String
  mime : String
  bytes : Nat
  origName : Option String
  createdAt : String
  deriving Repr, ToJson

private structure AttachmentRow where
  sha256 : String
  mime : String
  bytes : Int64
  origName : Option String
  createdAt : String
  deriving Row

namespace Blobs

private def ofRow (r : AttachmentRow) : Attachment :=
  { sha256 := r.sha256, mime := r.mime, bytes := r.bytes.toInt.toNat,
    origName := r.origName, createdAt := r.createdAt }

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

/-- Stores bytes, returning their hash. Storing the same bytes twice is a no-op. -/
def put (ctx : Ctx) (bytes : ByteArray) (mime : String)
    (origName : Option String := none) : IO String := do
  let sha := Sha256.hexBytes bytes
  let p := path ctx sha
  if !(← p.pathExists) then
    IO.FS.createDirAll (p.parent.getD ctx.cfg.blobDir)
    IO.FS.writeBinFile p bytes
  let now ← nowStamp
  Db.exec ctx.db s!"INSERT INTO attachment (sha256, mime, bytes, orig_name, created_at)
    VALUES ({Db.lit sha}, {Db.lit mime}, {bytes.size}, {Db.litOpt origName}, {Db.lit now})
    ON CONFLICT(sha256) DO NOTHING"
  return sha

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
    s!"SELECT sha256, mime, bytes, orig_name, created_at FROM attachment
       WHERE sha256 = {Db.lit sha}"
  return r.map ofRow

/-- Every stored receipt. -/
def list (ctx : Ctx) : IO (Array Attachment) := do
  let rs ← Db.rows AttachmentRow ctx.db
    "SELECT sha256, mime, bytes, orig_name, created_at FROM attachment ORDER BY created_at DESC"
  return rs.map ofRow

/-- Links a receipt to a transaction. -/
def attach (ctx : Ctx) (txn : TxId) (sha : String) : IO Unit :=
  Db.exec ctx.db s!"INSERT OR IGNORE INTO txn_attachment (txn_id, sha256)
                    VALUES ({Db.lit txn.val}, {Db.lit sha})"

/-- Unlinks a receipt from a transaction. The bytes stay until `gc`. -/
def detach (ctx : Ctx) (txn : TxId) (sha : String) : IO Unit :=
  Db.exec ctx.db s!"DELETE FROM txn_attachment
                    WHERE txn_id = {Db.lit txn.val} AND sha256 = {Db.lit sha}"

/-- Deletes blobs no transaction references any more. Returns how many were removed. -/
def gc (ctx : Ctx) : IO Nat := do
  let orphans ← Db.rows String ctx.db
    "SELECT sha256 FROM attachment WHERE sha256 NOT IN (SELECT sha256 FROM txn_attachment)"
  for sha in orphans do
    let p := path ctx sha
    if ← p.pathExists then IO.FS.removeFile p
    Db.exec ctx.db s!"DELETE FROM attachment WHERE sha256 = {Db.lit sha}"
  return orphans.size

end Blobs

end Resources
