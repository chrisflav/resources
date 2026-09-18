import Resources.Node.Session
import Resources.Store.Blob

/-!
# Receipts on a sequencer

A receipt is too big for the order, so the order carries its hash and the bytes
go somewhere else. On a synced node that somewhere else is the sequencer, which
must be able to store the bytes without being able to read them.

## What is stored where

* the plaintext, in `blobs/` on this machine, under the SHA-256 of the
  plaintext — which is the name the ledger uses and the name every transaction
  attaches;
* the ciphertext, on the sequencer, under the SHA-256 of the *ciphertext*, which
  is the only name a server that cannot decrypt can check;
* the key, in the ledger, as `Attachment.wrappedKey`: a fresh key per blob,
  sealed under a realm key, so that whoever holds the realm can open the file
  and nobody else can.

The two hashes are both stored in the attachment's metadata, which is what
`Blobs.get?` needs to fetch a file it has never seen: the metadata arrives in
the order, the bytes are fetched on first use, and a node that never opens a
receipt never downloads it.

## Which realm's key

The spec wraps a blob key under the realm of the transaction it is attached to.
But a blob is registered *before* it is attached — a receipt is scanned, then
matched — so at the moment of encryption there is no transaction to ask. So it
is wrapped under whichever realm the node was working in, this node's own unless
`put` is told otherwise, and that realm is recorded in the metadata: whoever can
read the realm a receipt was filed in can read the receipt.

`attach` is where the two meet. A payment in another realm needs its paper
readable by that realm's readers, so attaching across one re-seals the file
under a fresh key of its own, wraps that key under the target realm's current
key, and uploads the new ciphertext — all in the same event as the attachment.
Both halves of that move are in `rewrap?`, and what makes it a re-wrap rather
than a re-registration is that the file keeps its *name*: the plaintext hash is
what the ledger calls it and what every attachment points at.

The key is fresh because the associated data changes. Re-sealing the same
plaintext under the same key and the same nonce with a second associated-data
value produces two Poly1305 tags under one one-time key, and anybody holding
both — the sequencer holds both by construction — can recover that key and forge
a tag for arbitrary bytes under it. Two ciphertexts differing only in their tag
also tell the server at a glance that a file in realm A and a file in realm B
are the same file. A fresh key costs nothing and removes both.

## The framing

```
body    = nonce ++ seal(blobKey, nonce, seg("resources/blob/v1") ++ seg(ledger)
                        ++ seg(realm) ++ seg(generation) ++ seg(sha), plaintext)
wrapped = nonce ++ seal(realmKey[generation], nonce,
                        seg("resources/blob-key/v1") ++ seg(ledger) ++ seg(realm)
                        ++ seg(generation) ++ seg(sha), blobKey)
```

Both name the plaintext's hash, so neither the file nor its key can be moved
onto another file, and both name the realm and generation, so neither can be
replayed under a key that has been rotated away.
-/

open Lean SQLite

namespace Resources
namespace Node

/-- The domain a blob's ciphertext is bound to. -/
def blobTag : String := "resources/blob/v1"

/-- The domain a blob's key is sealed under. -/
def blobKeyTag : String := "resources/blob-key/v1"

/-- The associated data a blob's bytes are sealed under. -/
def blobAd (ledger realm : String) (generation : Nat) (sha : String) : ByteArray :=
  Sync.segStr blobTag ++ Sync.segStr ledger ++ Sync.segStr realm ++ Sync.segNat generation
    ++ Sync.segStr sha

/-- The associated data a blob's key is sealed under. -/
def blobKeyAd (ledger realm : String) (generation : Nat) (sha : String) : ByteArray :=
  Sync.segStr blobKeyTag ++ Sync.segStr ledger ++ Sync.segStr realm ++ Sync.segNat generation
    ++ Sync.segStr sha

/-- The domain a blob's nonce is derived under. -/
def blobNonceTag : String := "resources/blob-nonce/v1"

/--
The nonce a blob's bytes are sealed under: derived from its own key and its
plaintext hash rather than drawn at random.

A nonce must never repeat under one key, and this one cannot: the key is fresh
for this file and is used for nothing else. What deriving it buys is that
sealing the same file twice gives the same ciphertext, so an upload that failed
can be made again under the name the ledger already recorded — which a random
nonce would rename with every attempt.
-/
def blobNonce (suite : CryptoSuite) (blobKey : ByteArray) (sha : String) : ByteArray :=
  take (Sha256.hash (Sync.segStr blobNonceTag ++ Sync.seg blobKey ++ Sync.segStr sha))
    suite.nonceSize

namespace Blobs

/--
How `Attachment.wrappedKey` is written down: the realm, the generation, and the
sealed key in base64, separated by colons.

The realm comes first and the bytes last because base64 carries no colon: a
realm id that contained one would still be read back whole.
-/
def renderWrapped (realm : String) (generation : Nat) (wrapped : ByteArray) : String :=
  realm ++ ":" ++ toString generation ++ ":" ++ Sync.toBase64 wrapped

/-- Reads back what `renderWrapped` wrote. -/
def readWrapped? (s : String) : Option (String × Nat × ByteArray) := do
  let parts := s.splitOn ":"
  let sealed ← parts.getLast?
  let generation ← (parts.take (parts.length - 1)).getLast?
  let n ← generation.toNat?
  let realm := String.intercalate ":" (parts.take (parts.length - 2))
  let bytes ← Sync.ofBase64? sealed
  return (realm, n, bytes)

/--
Reads a blob's bytes, fetching them from the sequencer the first time.

Everything that comes back is checked against something already known: the
ciphertext against the hash the metadata names, the key against the associated
data it was sealed under, and the plaintext against the hash the ledger calls
the file. So a sequencer that hands back the wrong bytes is caught, and one that
hands back nothing leaves the store exactly as it was.

What is fetched is cached in `blobs/` under its plaintext hash, which is the
same place a file stored on this machine lives — after the first read the two
are indistinguishable, as they should be.
-/
def get? (s : Session) (sha : String) : IO (Option ByteArray) := do
  if let some bytes ← Resources.Blobs.get? s.ctx sha then return some bytes
  let some file ← Resources.Blobs.meta? s.ctx sha | return none
  let some cipherHash := file.cipherHash | return none
  let some stated := file.wrappedKey | return none
  let some (realm, generation, wrapped) := readWrapped? stated | return none
  let reply ← s.transport (Transport.get (s.route ["blobs", cipherHash]))
  let some body := Transport.bytes? reply | return none
  unless Sha256.hexBytes body == cipherHash do return none
  -- A realm that has been re-keyed since the file was stored is still opened by
  -- the generation it was stored under, which is why old generations are kept.
  let realmKey ← match ← Keys.get s.keys realm generation with
    | some key => pure (some key)
    | none =>
      if ← fetchKey s realm generation then Keys.get s.keys realm generation else pure none
  let some key := realmKey | return none
  let nonceSize := s.suite.nonceSize
  if wrapped.size < nonceSize || body.size < nonceSize then return none
  let some blobKey := s.suite.openPart key (take wrapped nonceSize)
    (blobKeyAd s.ledger realm generation sha) (drop wrapped nonceSize) | return none
  let some plain := s.suite.openPart blobKey (take body nonceSize)
    (blobAd s.ledger realm generation sha) (drop body nonceSize) | return none
  unless Sha256.hexBytes plain == sha do return none
  Resources.Blobs.cache s.ctx sha plain
  return some plain

/--
The realm a transaction's legs sit in, as far as this node can see.

Every leg of one part is in one realm — `checkPostings` refuses anything else —
so the first of them answers for all of them. A transaction this node cannot see
at all is taken to be in its own realm, which is where an attachment would have
gone before any of this.
-/
private def realmOf (st : State) (txn : TxId) : RealmId :=
  match (st.txn? txn).bind (fun t => t.postings.head?) with
  | some p => (st.realmOf p.account).getD Realm.selfId
  | none => Realm.selfId

/--
Seals a file this node holds again under another realm's key, and returns the
`registerBlob` that records where it now lives.

`none` when there is nothing to do or nothing to do it with: the file is already
under that realm's current key, this node holds no key for one of the two
realms, or the wrap it is under does not open.

The bytes are the same bytes and the key is a new one. A blob's ciphertext is
sealed under associated data naming the realm and the generation, precisely so
that neither the file nor its key can be presented under a key that has been
rotated away — which is also what makes the old ciphertext useless in a realm it
was not sealed for. So the file is sealed again, under a key drawn for this
sealing, and uploaded under the hash it now has; the operation carries both
halves of the result, which is what `Core/Apply.lean` takes from a second
registration and all that it takes.

The nonce is derived from the blob key and the plaintext hash, so an upload that
failed can be made again under the name the ledger already recorded. With a
fresh key that derivation cannot repeat a (key, nonce) pair, which is the whole
reason the key is fresh: the same pair under two associated-data values is two
authenticators under one one-time key, and that is a forgery, not an
inefficiency.
-/
def rewrap? (s : Session) (sha : String) (realm : String) : IO (Option Op) := do
  let some file ← Resources.Blobs.meta? s.ctx sha | return none
  let some stated := file.wrappedKey | return none
  let some (held, heldGeneration, wrapped) := readWrapped? stated | return none
  let some (generation, realmKey) ← Keys.latest s.keys realm | return none
  if held == realm && heldGeneration == generation then return none
  let some plain ← get? s sha | return none
  let nonceSize := s.suite.nonceSize
  if wrapped.size < nonceSize then return none
  -- The wrap this node holds has to open, even though nothing from inside it is
  -- used: it is the difference between re-wrapping a file this node may read and
  -- re-registering somebody else's under a key of one's own.
  let some heldKey ← Keys.get s.keys held heldGeneration | return none
  if (s.suite.openPart heldKey (take wrapped nonceSize)
      (blobKeyAd s.ledger held heldGeneration sha) (drop wrapped nonceSize)).isNone then
    return none
  let blobKey ← s.suite.randomBytes s.suite.keySize
  let nonce := blobNonce s.suite blobKey sha
  let body := nonce ++ s.suite.sealPart blobKey nonce (blobAd s.ledger realm generation sha) plain
  let cipherHash := Sha256.hexBytes body
  let keyNonce ← s.suite.randomBytes nonceSize
  let sealedKey := keyNonce ++ s.suite.sealPart realmKey keyNonce
    (blobKeyAd s.ledger realm generation sha) blobKey
  discard <| Transport.result s.transport
    (Transport.upload "PUT" (s.route ["blobs", cipherHash]) body)
  return some (.registerBlob
    { file with cipherHash := some cipherHash
                wrappedKey := some (renderWrapped realm generation sealedKey) })

/--
Stores a file, encrypts it under a fresh key of its own, and uploads the
ciphertext.

The local store is written first and the upload second, so a sequencer that is
unreachable costs the upload and never the receipt: the file is on this machine,
its metadata is in the ledger, and a later `resources blob push` can send it.
That ordering is why the upload cannot be inside `Blobs.put` — the record has to
name the ciphertext it will be uploaded as, which is known before the request
and true whether or not the request succeeds.

`realm` says whose readers are meant to be able to open it, and defaults to this
node's own. Storing the same bytes twice is one file and one record, and the
second call's fresh key is dropped along with the rest of the second
registration: the ledger already knows this file, and re-keying it would strand
every reader holding the first key. What a second call does do is re-wrap, when
it names a realm the file is not sealed under — the same move an attachment
across realms makes, and for the same reason.
-/
def put (s : Session) (bytes : ByteArray) (mime : String)
    (origName : Option String := none) (realm : String := Realm.selfId.val) : IO String := do
  let sha := Sha256.hexBytes bytes
  if (← Resources.Blobs.meta? s.ctx sha).isSome then
    -- A file the ledger already knows. The bytes are put where this store keeps
    -- them, in case they arrived from somewhere else, and the only thing that
    -- can be said about it now is where a copy of it is and under whose key.
    Resources.Blobs.cache s.ctx sha bytes
    if let some op ← rewrap? s sha realm then
      discard <| s.ctx.commit "system" [op] (realm := ⟨realm⟩)
    return sha
  let (generation, realmKey) ← Keys.create s.keys realm
  let blobKey ← s.suite.randomBytes s.suite.keySize
  let nonce := blobNonce s.suite blobKey sha
  let body := nonce ++ s.suite.sealPart blobKey nonce (blobAd s.ledger realm generation sha) bytes
  let cipherHash := Sha256.hexBytes body
  let keyNonce ← s.suite.randomBytes s.suite.nonceSize
  let wrapped := keyNonce ++ s.suite.sealPart realmKey keyNonce
    (blobKeyAd s.ledger realm generation sha) blobKey
  discard <| Resources.Blobs.put s.ctx bytes mime origName
    (some (cipherHash, renderWrapped realm generation wrapped)) ⟨realm⟩
  -- The record is what the ledger keeps; the upload is what the sequencer keeps.
  -- Only the file this node registered is uploaded, so a second caller storing
  -- the same bytes does not overwrite a ciphertext somebody else can open.
  match ← Resources.Blobs.meta? s.ctx sha with
  | some stored =>
    if stored.cipherHash == some cipherHash then
      discard <| Transport.result s.transport
        (Transport.upload "PUT" (s.route ["blobs", cipherHash]) body)
  | none => pure ()
  return sha

/-- Stores a file from disk, encrypted and uploaded. -/
def putFile (s : Session) (file : System.FilePath) (realm : String := Realm.selfId.val) :
    IO String := do
  let bytes ← IO.FS.readBinFile file
  let name := file.fileName.getD "receipt"
  put s bytes (Resources.Blobs.mimeOfExtension name) (some name) realm

/--
Links a receipt to a transaction, bringing the file's key into the realm that
transaction lives in.

A receipt is filed before it is matched — it is scanned into whichever realm the
node was working in, and only afterwards attached to a payment, which may be in
another. Everybody who can read that payment has to be able to read the paper
behind it, so the attachment and the re-wrap are one event: two parts, both in
the transaction's realm, the `registerBlob` saying where the ciphertext is now
and under whose key, and the `attach` itself. A reader of that realm who had
never heard of the file learns of it from the first part and opens it with the
second.
-/
def attach (s : Session) (txn : TxId) (sha : String) : IO Unit := do
  let realm := realmOf (← s.ctx.state.get) txn
  let ops := (← rewrap? s sha realm.val).toList ++ [Op.attach txn sha]
  discard <| s.ctx.commit "system" ops (kind := "attach") (realm := realm)

/--
Uploads the ciphertext of a file this node holds, sealing it again from what the
ledger records.

The whole of the sealing is recoverable from the metadata and the keyring — the
key out of `wrappedKey`, the nonce out of the key — so this reproduces exactly
the ciphertext the ledger names, and refuses to upload anything that does not
hash to it.
-/
def push (s : Session) (sha : String) : IO Bool := do
  let some file ← Resources.Blobs.meta? s.ctx sha | return false
  let some cipherHash := file.cipherHash | return false
  let some stated := file.wrappedKey | return false
  let some (realm, generation, wrapped) := readWrapped? stated | return false
  let some bytes ← Resources.Blobs.get? s.ctx sha | return false
  let nonceSize := s.suite.nonceSize
  if wrapped.size < nonceSize then return false
  let some key ← Keys.get s.keys realm generation | return false
  let some blobKey := s.suite.openPart key (take wrapped nonceSize)
    (blobKeyAd s.ledger realm generation sha) (drop wrapped nonceSize) | return false
  let nonce := blobNonce s.suite blobKey sha
  let body := nonce ++ s.suite.sealPart blobKey nonce
    (blobAd s.ledger realm generation sha) bytes
  unless Sha256.hexBytes body == cipherHash do return false
  let (code, _) ← Transport.result s.transport
    (Transport.upload "PUT" (s.route ["blobs", cipherHash]) body)
  return code == 201

end Blobs

end Node
end Resources
