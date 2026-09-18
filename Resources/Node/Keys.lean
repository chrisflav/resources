import Resources.Node.Identity

/-!
# The realm keys this node holds

A realm has one key per generation, and a node holds the ones it was given: the
ones it made, because it administers the realm, and the ones it unwrapped out of
a grant or an invite. They live in `keys.json` beside the identity, encrypted
the same way — one AEAD box under a key stretched from the same passphrase, with

    seg("resources/keyring/v1") ++ seg(signPkHex)
      ++ seg(alg) ++ seg(ops) ++ seg(mem)

as associated data, so a keyring cannot be lifted onto another identity's file
and the stretcher's parameters cannot be edited under it. The `kdf` object is
read back and checked by `Identity.readKdf`, which is where the rules are written
down; the parameters a file was written with are kept and written again, so that
rotating a key does not quietly re-stretch a keyring more cheaply than whoever
made it asked for.

The plaintext inside is the canonical encoding of a list of
`(realm, generation, key)`, which is `Core/Codec.lean`'s job rather than JSON's:
a key is bytes, and base64 inside JSON inside a box is one encoding too many.

Old generations are kept. A revoke moves the realm forward and everything
written from then on is written under the new key, but everything written
before it is still there to be read, and a node that threw the old key away
could no longer replay the order it already has.

The passphrase is held in memory for the lifetime of the keyring, because
rotating a key writes the file again. That is the same bargain `resources node`
makes by staying up: a running node can decrypt, and a node that is not running
cannot.
-/

open Lean

namespace Resources
namespace Node

/-- The domain a keyring's ciphertext is bound to. -/
def keyringTag : String := "resources/keyring/v1"

/-- The associated data a keyring is sealed under, the stretcher's parameters included. -/
def keyringAd (signPkHex : String) (kdf : KdfParams) : ByteArray :=
  Sync.segStr keyringTag ++ Sync.segStr signPkHex
    ++ Sync.segStr kdf.alg ++ Sync.segNat kdf.ops ++ Sync.segNat kdf.mem

/-- One realm key, at the generation it belongs to. -/
structure KeyEntry where
  /-- The realm, by the id the ledger and the sequencer both call it. -/
  realm : String
  /-- Which generation of that realm's key this is. -/
  generation : Nat
  /-- The key itself. -/
  key : ByteArray
  deriving Inhabited

/-- An open keyring: the keys in memory, and what it takes to write them back. -/
structure Keyring where
  /-- The primitives the file is encrypted with. -/
  suite : CryptoSuite
  /-- Where the file lives. -/
  path : System.FilePath
  /-- What opens it. -/
  passphrase : String
  /-- Whose it is; its signing key is in the associated data and its agreement key unwraps. -/
  identity : Identity
  /-- How the passphrase is stretched: the file's own parameters, or the suite's for a new one. -/
  kdf : KdfParams
  /-- The keys held, newest generation last. -/
  entries : IO.Ref (Array KeyEntry)

namespace Keys

/-- The keys as the flat triples the file stores. -/
private def toTriples (es : Array KeyEntry) : List (String × Nat × ByteArray) :=
  (es.map (fun e => (e.realm, e.generation, e.key))).toList

/-- The entries a file's triples stand for. -/
private def ofTriples (ts : List (String × Nat × ByteArray)) : Array KeyEntry :=
  (ts.map (fun (realm, generation, key) => ({ realm, generation, key } : KeyEntry))).toArray

/-- Where a store keeps its keyring. -/
def pathIn (cfg : Config) : System.FilePath := cfg.dataDir / "keys.json"

/-- Writes the keyring out, under a fresh salt and nonce. -/
def save (kr : Keyring) : IO Unit := do
  let suite := kr.suite
  let salt ← suite.randomBytes suite.saltSize
  let nonce ← suite.randomBytes suite.nonceSize
  let plain := Codec.encode (toTriples (← kr.entries.get))
  let secret :=
    suite.sealPart (suite.deriveKey kr.passphrase salt kr.kdf) nonce
      (keyringAd kr.identity.id kr.kdf) plain
  let j := Json.mkObj [
    ("v", Sync.jnat 1), ("id", kr.identity.id), ("kdf", kdfJson kr.kdf salt),
    ("nonce", Sync.toBase64 nonce), ("secret", Sync.toBase64 secret)]
  -- Written to a sibling and renamed over the old file. This is rewritten whole
  -- on every grant unwrapped during a pull, and a crash halfway through a
  -- truncating write would lose every realm key this node holds.
  Files.writeSecret kr.path (j.pretty ++ "\n")

/--
Opens the keyring at `path`, or starts an empty one.

An absent file is not an error: a node that has never been granted anything
holds no keys, and the file appears the first time one does.
-/
def «open» (suite : CryptoSuite) (path : System.FilePath) (passphrase : String)
    (identity : Identity) : IO Keyring := do
  let entries ← IO.mkRef (#[] : Array KeyEntry)
  let kr : Keyring := { suite, path, passphrase, identity, kdf := suite.kdf, entries }
  unless ← path.pathExists do return kr
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let version := (j.getObjValAs? Nat "v").toOption.getD 0
  unless version == 1 do
    throw <| IO.userError s!"keyring {path} is version {version}, and this binary reads 1"
  let b64 (obj : Json) (key : String) : IO ByteArray := do
    match Sync.bytesField obj key with
    | .ok bs => return bs
    | .error e => throw <| IO.userError s!"{e} in {path}"
  let (kdf, salt) ← readKdf suite path j
  let nonce ← b64 j "nonce"
  let secret ← b64 j "secret"
  let some plain :=
      suite.openPart (suite.deriveKey passphrase salt kdf) nonce (keyringAd identity.id kdf) secret
    | throw <| IO.userError s!"the passphrase does not open {path}, or its stretcher's \
                              parameters have been changed under it"
  let some triples := (Codec.decode plain : Option (List (String × Nat × ByteArray)))
    | throw <| IO.userError s!"the keys in {path} are not in a shape this binary reads"
  entries.set (ofTriples triples)
  return { kr with kdf }

/-- Every key held, in the order the file lists them. -/
def all (kr : Keyring) : IO (Array KeyEntry) := kr.entries.get

/-- The key for one generation of one realm, if this node holds it. -/
def get (kr : Keyring) (realm : String) (generation : Nat) : IO (Option ByteArray) := do
  let es ← kr.entries.get
  return (es.find? (fun e => e.realm == realm && e.generation == generation)).map (·.key)

/-- The newest generation this node holds for a realm, and its key. -/
def latest (kr : Keyring) (realm : String) : IO (Option (Nat × ByteArray)) := do
  let es := (← kr.entries.get).filter (·.realm == realm)
  return es.foldl (fun best e =>
    match best with
    | some (g, _) => if e.generation > g then some (e.generation, e.key) else best
    | none => some (e.generation, e.key)) none

/-- Records a key, replacing whatever was held for that realm and generation. -/
def put (kr : Keyring) (realm : String) (generation : Nat) (key : ByteArray) : IO Unit := do
  kr.entries.modify fun es =>
    (es.filter (fun e => !(e.realm == realm && e.generation == generation))).push
      { realm, generation, key }
  save kr

/--
The key this node uses for a realm, making one if it holds none.

Idempotent, because it is called on the way into every push: a realm whose key
is already here is not re-keyed by being mentioned.
-/
def create (kr : Keyring) (realm : String) : IO (Nat × ByteArray) := do
  match ← latest kr realm with
  | some found => return found
  | none =>
    let key ← kr.suite.randomBytes kr.suite.keySize
    put kr realm 0 key
    return (0, key)

/--
Makes the next generation of a realm's key.

The old one stays: what was written under it is still readable, and what is
written from now on is not readable by whoever was just put out.
-/
def rotate (kr : Keyring) (realm : String) : IO (Nat × ByteArray) := do
  let next := match ← latest kr realm with
    | some (g, _) => g + 1
    | none => 0
  let key ← kr.suite.randomBytes kr.suite.keySize
  put kr realm next key
  return (next, key)

/--
A realm key wrapped to somebody's agreement key: what a grant and an invite
both carry.

The recipient's key comes from their member record on the sequencer, or from an
invite's ephemeral key, and nothing about them has to be true for this to be
safe — a key wrapped to the wrong public key is a key nobody can open.
-/
def wrapFor (kr : Keyring) (memberBoxPk : ByteArray) (realm : String) (generation : Nat) :
    IO ByteArray := do
  let some key ← get kr realm generation
    | throw <| IO.userError s!"this node holds no key for realm '{realm}' at generation \
                              {generation}"
  return kr.suite.wrapKey memberBoxPk key

/--
Opens a grant and keeps what was inside it.

`unwrapKey` says no when the bytes were sealed to somebody else, which is the
whole check: a grant is a claim that a key was wrapped for you, and unwrapping
it is how the claim is settled.
-/
def unwrapGrant (kr : Keyring) (realm : String) (generation : Nat) (wrapped : ByteArray) :
    IO ByteArray := do
  let some key := kr.suite.unwrapKey kr.identity.boxSk wrapped
    | throw <| IO.userError s!"the grant on realm '{realm}' was not wrapped to this node's key"
  put kr realm generation key
  return key

end Keys

end Node
end Resources
