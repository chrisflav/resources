import Resources.Node.Crypto
import Resources.Store.Commit

/-!
# The node's identity

A node is a key pair, and the member id in the ledger is the lowercase hex of
its signing public key. That is the whole of what an identity is: there is no
account on the sequencer, no password, and nothing to recover — a ledger knows
you because you can sign, and for no other reason.

`identity.json` sits in the data directory beside `resources.db` and holds both
public keys in the clear and both secret keys encrypted under a key stretched
from a passphrase. The shape is the one the thin client keeps in
`localStorage`, byte for byte, so that the same passphrase opens the same
identity in a browser:

```json
{ "v": 1, "id": "<hex signPk>", "signPk": "<hex>", "boxPk": "<hex>",
  "kdf": { "alg": "argon2id", "ops": 2, "mem": 67108864, "salt": "<base64>" },
  "nonce": "<base64>", "secret": "<base64>" }
```

Every field is read back and used; none of them is assumed.

* `v` is the format version and is `1`. Anything else is refused.
* `id` has to be the lowercase hex of `signPk`, so a file cannot be filed under
  somebody else's name.
* `kdf` says how the passphrase was stretched: which stretcher, how many passes,
  how much memory, and under which salt. All four come out of the file and go
  into the derivation, because a file written on another machine, by an older
  build or by the thin client may have been written with parameters this binary
  would not have chosen and is still yours. `alg` has to be the one this binary
  can compute — nothing else can be derived — and `ops` and `mem` have to be
  inside `minKdfOps … maxKdfOps` and `minKdfMem … maxKdfMem`. Outside that range
  they are not a choice anybody made: one pass over no memory is a passphrase a
  laptop guesses at millions of tries a second, and a terabyte is an
  out-of-memory kill on the way into your own identity.
* `nonce` and `secret` are the box. The plaintext inside is `signSk ++ boxSk`,
  and the associated data is

      seg("resources/identity/v1") ++ seg(signPkHex)
        ++ seg(alg) ++ seg(ops) ++ seg(mem)

  so the parameters are covered by the authenticator as well as fed to the
  stretcher. Feeding them in would already be enough for a stretcher that uses
  all of them, and a suite is free not to — binding them makes an edited `ops` a
  box that does not open rather than a box that opens more cheaply. The signing
  key is in there for the older reason: a file's ciphertext cannot be lifted onto
  another file claiming another key.

The keyring beside it, `keys.json`, has the same `v`, `id` and `kdf`, is read the
same way, and is sealed under `seg("resources/keyring/v1") ++ …`; see
`Node/Keys.lean`.

## Joining the ledger you already have

`Identity.install` is the migration from phase 1's single member. The ledger
opened with one member, `self`, who administers the one realm; a node that has
just generated a key pair has to become a member in the ledger's own terms
before it can author anything. So it appends `addMember` with the new id — the
same party as `self`, because it is the same person — and `grant` on the self
realm with the admin role, which also opens the bridge account the new member
holds a balance in.

`removeMember "self"` is *not* appended, because `Core`'s `applyOp` refuses it:
`removeMember` throws on `Member.selfId` ("the member this ledger belongs to
cannot be removed"). So `self` stays a member and stays an admin of the self
realm, and the log's first author stays `self` for ever — genesis was written
before there was a key to sign it with, and no rewriting of history would make
it verifiable. Two consequences worth stating plainly: events authored by
`self` predate signatures and are not verified by anybody, and a node that
syncs a ledger where `self` is still an admin is trusting that nobody else ever
held that ledger's database. Both end the day `Core` allows the member to go.
-/

open Lean

namespace Resources
namespace Node

/-! ## Small JSON helpers

The node keeps three small files beside its database — `identity.json`,
`keys.json` and `sync.json` — and reads them with `Sync/Protocol.lean`'s field
readers plus this one, which the protocol has no use for.
-/

/-- A nested object field, or an empty object when it is missing or not one. -/
def objField (j : Json) (key : String) : Json :=
  match j.getObjVal? key with
  | .ok (.obj o) => .obj o
  | _ => Json.mkObj []

/-! ## How a passphrase was stretched -/

/-- The fewest passes over memory a file may ask for. -/
def minKdfOps : Nat := 1

/-- The most. -/
def maxKdfOps : Nat := 10

/-- The least memory a file may ask a stretcher for: 16 MiB. -/
def minKdfMem : Nat := 16 * 1024 * 1024

/-- The most: 1 GiB. -/
def maxKdfMem : Nat := 1024 * 1024 * 1024

/--
The `kdf` object of a node file, read back and checked.

`salt` is returned beside the parameters because the two are one decision: the
key that opens a file is the one derived from this passphrase, under this salt,
at this cost, and nothing else.
-/
def readKdf (suite : CryptoSuite) (path : System.FilePath) (j : Json) :
    IO (KdfParams × ByteArray) := do
  let kdf := objField j "kdf"
  let field (key : String) : IO Nat :=
    match kdf.getObjValAs? Nat key with
    | .ok n => return n
    | .error _ => throw <| IO.userError s!"the 'kdf' object in {path} has no '{key}'"
  let alg ← IO.ofExcept (Sync.strField kdf "alg")
  let ops ← field "ops"
  let mem ← field "mem"
  let salt ←
    match Sync.bytesField kdf "salt" with
    | .ok bs => pure bs
    | .error e => throw <| IO.userError s!"{e} in {path}"
  unless alg == suite.kdf.alg do
    throw <| IO.userError s!"{path} was written with '{alg}', and this binary stretches \
                            passphrases with '{suite.kdf.alg}'"
  unless minKdfOps ≤ ops && ops ≤ maxKdfOps do
    throw <| IO.userError s!"{path} asks for {ops} passes over memory, and this binary takes \
                            {minKdfOps} to {maxKdfOps}"
  unless minKdfMem ≤ mem && mem ≤ maxKdfMem do
    throw <| IO.userError s!"{path} asks for {mem} bytes of memory, and this binary takes \
                            {minKdfMem} to {maxKdfMem}"
  unless salt.size == suite.saltSize do
    throw <| IO.userError s!"the salt in {path} is {salt.size} bytes, and this suite's are \
                            {suite.saltSize}"
  return ({ alg, ops, mem }, salt)

/-- The `kdf` object a file records: the parameters, and the salt they were used with. -/
def kdfJson (kdf : KdfParams) (salt : ByteArray) : Json :=
  Json.mkObj [("alg", kdf.alg), ("ops", Sync.jnat kdf.ops), ("mem", Sync.jnat kdf.mem),
              ("salt", Sync.toBase64 salt)]

/-! ## The identity file -/

/-- The domain an identity file's ciphertext is bound to. -/
def identityTag : String := "resources/identity/v1"

/--
The associated data an identity's secret keys are sealed under.

The stretcher's parameters are in here as well as in the derivation, so that a
file whose `ops` somebody edited is a box that does not open rather than a box
that opens at a cost they chose.
-/
def identityAd (signPkHex : String) (kdf : KdfParams) : ByteArray :=
  Sync.segStr identityTag ++ Sync.segStr signPkHex
    ++ Sync.segStr kdf.alg ++ Sync.segNat kdf.ops ++ Sync.segNat kdf.mem

/--
One node's key pairs: the signing pair that says who wrote an event, and the
agreement pair that realm keys are wrapped to.
-/
structure Identity where
  /-- Lowercase hex of `signPk`. This is the member id in the ledger. -/
  id : String
  /-- The signing public key. -/
  signPk : ByteArray
  /-- The signing secret key. -/
  signSk : ByteArray
  /-- The agreement public key. -/
  boxPk : ByteArray
  /-- The agreement secret key. -/
  boxSk : ByteArray
  deriving Inhabited

namespace Identity

/-- The ledger's name for this identity. -/
def memberId (i : Identity) : MemberId := ⟨i.id⟩

/-- The agreement public key as hex, which is how the sequencer publishes it. -/
def boxPkHex (i : Identity) : String := toHex i.boxPk

/-- Signs a message with this identity's signing key. -/
def sign (suite : CryptoSuite) (i : Identity) (msg : ByteArray) : ByteArray :=
  suite.sign i.signSk msg

/-- Signs a message and renders the signature as hex, which is how the wire carries it. -/
def signHex (suite : CryptoSuite) (i : Identity) (msg : ByteArray) : String :=
  toHex (sign suite i msg)

/--
Writes the identity file, encrypting the secret keys under a fresh salt and nonce.

`kdf` defaults to what this suite would choose and is an argument so that a file
can be written at another cost — which is what a machine with more memory, or a
test, wants — and still be opened by the same `load`, because `load` reads the
cost back rather than assuming it.
-/
def save (suite : CryptoSuite) (path : System.FilePath) (passphrase : String)
    (i : Identity) (kdf : KdfParams := suite.kdf) : IO Unit := do
  let salt ← suite.randomBytes suite.saltSize
  let nonce ← suite.randomBytes suite.nonceSize
  let key := suite.deriveKey passphrase salt kdf
  let secret := suite.sealPart key nonce (identityAd i.id kdf) (i.signSk ++ i.boxSk)
  let j := Json.mkObj [
    ("v", Sync.jnat 1), ("id", i.id), ("signPk", toHex i.signPk), ("boxPk", toHex i.boxPk),
    ("kdf", kdfJson kdf salt),
    ("nonce", Sync.toBase64 nonce), ("secret", Sync.toBase64 secret)]
  -- Mode 0600, written through a temporary file: the secret keys are in here,
  -- and a half-written identity is one nothing opens.
  Files.writeSecret path (j.pretty ++ "\n")

/-- Generates a key pair and writes it out. Refuses to overwrite an identity that exists. -/
def create (suite : CryptoSuite) (path : System.FilePath) (passphrase : String) :
    IO Identity := do
  if ← path.pathExists then
    throw <| IO.userError s!"an identity already exists at {path}"
  let (signPk, signSk) ← suite.signKeypair
  let (boxPk, boxSk) ← suite.boxKeypair
  let i : Identity := { id := toHex signPk, signPk, signSk, boxPk, boxSk }
  save suite path passphrase i
  return i

/--
Reads the identity file and opens its secret keys.

Everything that can be wrong is one sentence: no file, a file this binary does
not understand, a stretcher's parameters outside the range anybody would choose,
a passphrase that does not open it, or a secret that does not match the public
key it is filed under.
-/
def load (suite : CryptoSuite) (path : System.FilePath) (passphrase : String) :
    IO Identity := do
  unless ← path.pathExists do
    throw <| IO.userError s!"no identity at {path}; run 'resources identity init'"
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let version := (j.getObjValAs? Nat "v").toOption.getD 0
  unless version == 1 do
    throw <| IO.userError s!"identity {path} is version {version}, and this binary reads 1"
  let hexField (key : String) : IO ByteArray := do
    let s ← IO.ofExcept (Sync.strField j key)
    match Sync.ofHex? s with
    | some bs => return bs
    | none => throw <| IO.userError s!"'{key}' in {path} is not hex"
  let b64Field (j : Json) (key : String) : IO ByteArray := do
    match Sync.bytesField j key with
    | .ok bs => return bs
    | .error e => throw <| IO.userError s!"{e} in {path}"
  let signPk ← hexField "signPk"
  let boxPk ← hexField "boxPk"
  let id := (Sync.strField? j "id" (toHex signPk)).toLower
  unless id == toHex signPk do
    throw <| IO.userError s!"identity {path} is filed under an id that is not its signing key"
  let (kdf, salt) ← readKdf suite path j
  let nonce ← b64Field j "nonce"
  let secret ← b64Field j "secret"
  let some plain :=
      suite.openPart (suite.deriveKey passphrase salt kdf) nonce (identityAd id kdf) secret
    | throw <| IO.userError s!"the passphrase does not open {path}, or its \
                              stretcher's parameters have been changed under it"
  unless plain.size == suite.signSkSize + suite.boxSkSize do
    throw <| IO.userError s!"the secret keys in {path} are {plain.size} bytes, \
                            and this suite's are {suite.signSkSize + suite.boxSkSize}"
  return { id, signPk, boxPk,
           signSk := take plain suite.signSkSize, boxSk := drop plain suite.signSkSize }

/-- The identity at `path`, or `none` if there is none there. -/
def load? (suite : CryptoSuite) (path : System.FilePath) (passphrase : String) :
    IO (Option Identity) := do
  if ← path.pathExists then return some (← load suite path passphrase) else return none

/--
The two public keys in an identity file, without opening it.

`resources identity show` asks nothing of the passphrase, because nothing it
prints is secret: the public halves are in the clear in the file, and they are
what somebody else needs in order to grant you anything.
-/
def publicKeys? (path : System.FilePath) : IO (Option (String × String)) := do
  unless ← path.pathExists do return none
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  return some ((Sync.strField? j "signPk").toLower, (Sync.strField? j "boxPk").toLower)

/-- Where a store keeps its identity. -/
def pathIn (cfg : Config) : System.FilePath := cfg.dataDir / "identity.json"

/-! ## Becoming a member of the ledger -/

/--
An account name nothing holds yet, by adding a number to `base` until one is
free.

A `grant` that names an account somebody already holds hands out that account
rather than opening one, which is right — a purse is not moved between realms by
being granted again — and wrong for a newcomer who happens to share a name with
somebody already here. So every purse this node opens is asked for under a name
nothing answers to, here and in `Node/Sync.lean` where a joiner writes itself
into the realm it has just been let into.
-/
def freeAccountName (s : State) (base : String) : String := Id.run do
  let taken (name : String) : Bool := s.accounts.toList.any (fun (_, a) => a.name == name)
  if !taken base then return base
  let mut n := 2
  while taken s!"{base}{n}" && n < 1000 do
    n := n + 1
  return s!"{base}{n}"

/--
Makes this identity a member of the ledger in the store, and returns the `Ctx`
that commits on its behalf.

Idempotent: a member that is already there is adopted rather than added again,
so `resources identity init` can be run twice without writing a second event.
-/
def install (ctx : Ctx) (i : Identity) (name : String) : IO Ctx := do
  let st ← ctx.state.get
  let me := i.memberId
  if (st.member? me).isSome then
    return { ctx with member := me }
  let party := ((st.member? ctx.member).map (·.party)).getD Party.selfId
  let bridge : Account :=
    { id := ⟨← freshId⟩, name := freeAccountName st s!"Assets.Purse.{name}", kind := .asset,
      owner := party, realm := Realm.selfId, bridgeOf := some me }
  discard <| ctx.commit "identity" [
    .addMember { id := me, name, party },
    -- The grant carries the role, so no `setRole` follows it: `grant` with
    -- `.admin` *is* "make this key an admin of the self realm", and it is the
    -- one operation that also opens the bridge account.
    .grant Realm.selfId me .admin bridge] "identity"
  return { ctx with member := me }

end Identity

end Node
end Resources
