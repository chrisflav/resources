import Resources.Sync.Protocol

/-!
# The primitives a node needs, as a record

Everything the node does with cryptography goes through one value of type
`CryptoSuite`: signing an envelope, sealing a part under a realm key, wrapping
that key for somebody else, stretching a passphrase into the key the identity
file is encrypted with. Nothing below `Node/Crypto.lean` ever names a primitive.

That is deliberate, and it is the whole point of this file. The record came
first and the primitives came second: every line of the sync path — composing an
envelope, appending it, pulling somebody else's, unwrapping a grant, joining by
invite — was written and tested against this interface before anything
satisfied it for real. `Resources/Crypto/Sodium.lean` now does, as
`CryptoSuite.sodium`, and not one file that syncs had to be opened for it.

That file, rather than this one, is also where `CryptoSuite.forNode` chooses
which suite a command-line node runs with, because choosing means naming both of
them.

The sizes are fields rather than constants for the same reason: a nonce is 24
bytes because XChaCha20-Poly1305 says so, and the code that generates one asks
the suite instead of knowing.

## The test suite is not encryption

`CryptoSuite.insecureForTests` implements every operation with SHA-256 and
XOR. It hides nothing, proves nothing and forges trivially — its "public" key
*is* its secret key. It exists so that the sync path can be exercised end to
end today, and it must never be handed to anything but a test.
-/

namespace Resources
namespace Node

/-! ## Byte helpers -/

/-- The first `n` bytes, or all of them when there are fewer. -/
def take (bs : ByteArray) (n : Nat) : ByteArray := bs.extract 0 (min n bs.size)

/-- Everything after the first `n` bytes. -/
def drop (bs : ByteArray) (n : Nat) : ByteArray := bs.extract (min n bs.size) bs.size

/-- Two byte strings XORed, truncated to the shorter of them. -/
def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0 : min a.size b.size] do
    out := out.push (a[i]! ^^^ b[i]!)
  return out

/--
A deterministic byte stream of any length from a seed: SHA-256 of the seed and
a counter, block after block.

Not a stream cipher. It is how the test suite stretches a 32-byte digest over a
plaintext of whatever size, so that its "encryption" has one shape at every
length rather than a special case below 32 bytes.
-/
def keyStream (seed : ByteArray) (len : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut block : Nat := 0
  while out.size < len do
    out := out ++ Sha256.hash (seed ++ (toString block).toUTF8)
    block := block + 1
  return take out len

/-! ## Stretching a passphrase -/

/--
What it takes to stretch a passphrase into a key: which stretcher, how many
passes, and how much memory.

These are in the identity and keyring files rather than compiled in, because a
file written on another machine, by an older build or by the thin client may have
been written with different ones and is still yours. `Node/Identity.lean` reads
them back, checks them against a range, derives with them and binds them into the
associated data of the box they describe.
-/
structure KdfParams where
  /-- The name of the stretcher, e.g. `argon2id`. -/
  alg : String
  /-- Passes over the memory. -/
  ops : Nat
  /-- Bytes of memory. -/
  mem : Nat
  deriving Repr, DecidableEq, Inhabited

/-! ## The interface -/

/--
Every cryptographic operation the node performs, and the sizes it has to know
to perform them.

A signing key pair is `(pk, sk)` in that order throughout, as is an agreement
key pair. A part's ciphertext does *not* include its nonce: `Envelope.lean`
prepends that, because the nonce is part of the wire format rather than of the
primitive.
-/
structure CryptoSuite where
  /-- What this suite is, for `resources sync status` and for error messages. -/
  name : String
  /--
  What a sequencer built on this suite calls itself in `GET health`.

  One of `sodium`, `insecure` or `reject-all`, so that an operator — and the
  thin client's own chrome — can see from the outside whether the signatures a
  deployment checks mean anything.
  -/
  verifierName : String := "sodium"
  /-- Bytes in a signing public key. -/
  signPkSize : Nat
  /-- Bytes in a signing secret key. -/
  signSkSize : Nat
  /-- Bytes in a signature. -/
  signatureSize : Nat
  /-- Bytes in an agreement public key. -/
  boxPkSize : Nat
  /-- Bytes in an agreement secret key. -/
  boxSkSize : Nat
  /-- Bytes in a realm key. -/
  keySize : Nat
  /-- Bytes in a part nonce. -/
  nonceSize : Nat
  /-- Bytes an authenticated encryption adds to its plaintext. -/
  tagSize : Nat
  /-- Bytes in a passphrase salt. -/
  saltSize : Nat
  /-- The stretcher, and the cost, that this suite writes into a new file. -/
  kdf : KdfParams
  /-- Signs `msg` under a signing secret key. -/
  sign : (sk : ByteArray) → (msg : ByteArray) → ByteArray
  /-- Whether `signature` is a signature of `msg` under a signing public key. -/
  verify : (pk : ByteArray) → (msg : ByteArray) → (signature : ByteArray) → Bool
  /-- Seals a part's plaintext under a realm key, with a nonce and associated data. -/
  sealPart : (key : ByteArray) → (nonce : ByteArray) → (ad : ByteArray) →
    (plaintext : ByteArray) → ByteArray
  /-- Opens what `sealPart` produced, or `none` if anything about it has changed. -/
  openPart : (key : ByteArray) → (nonce : ByteArray) → (ad : ByteArray) →
    (ciphertext : ByteArray) → Option ByteArray
  /-- Wraps a realm key to an agreement public key, so only its holder can read it. -/
  wrapKey : (recipientPk : ByteArray) → (key : ByteArray) → ByteArray
  /-- Unwraps what `wrapKey` produced, given the matching agreement secret key. -/
  unwrapKey : (recipientSk : ByteArray) → (bytes : ByteArray) → Option ByteArray
  /--
  Stretches a passphrase and a salt into a `keySize`-byte key, at a stated cost.

  The parameters are an argument rather than a field because they come out of the
  file being opened: a key derived at the cost the file records is the only key
  that opens it, whoever wrote it and with whatever this binary would have chosen.
  -/
  deriveKey : (passphrase : String) → (salt : ByteArray) → (params : KdfParams) → ByteArray
  /-- `n` bytes from the operating system's random source. -/
  randomBytes : Nat → IO ByteArray
  /-- A signing key pair from a seed. -/
  signSeedKeypair : (seed : ByteArray) → ByteArray × ByteArray
  /-- An agreement key pair from a seed. -/
  boxSeedKeypair : (seed : ByteArray) → ByteArray × ByteArray
  /-- A fresh signing key pair. -/
  signKeypair : IO (ByteArray × ByteArray)
  /-- A fresh agreement key pair. -/
  boxKeypair : IO (ByteArray × ByteArray)

namespace CryptoSuite

/-- The seed length a key pair is derived from: 32 bytes, as libsodium's is. -/
def seedSize : Nat := 32

/--
Whether a hex signature checks out under a hex public key.

Every key and every signature this protocol carries travels as hex, and bad hex
is a failed check rather than an error: a field that is not a key cannot have
signed anything, which is the same answer as a key that did not sign this.

The lengths are checked here rather than left to the primitive, and the same
answer comes back for a key of the wrong size. Both of these fields arrive from
an untrusted sequencer, and `crypto_sign_verify_detached` is a C function that
reads 32 bytes of public key and 64 of signature because that is what its
contract says it is given — so handing it a two-byte "key" would be a buffer
over-read on this node rather than a failed check, which is why the shim behind
`CryptoSuite.sodium` measures both again before libsodium is handed a pointer.
`Sync.Verifier.ofSuite` makes the sequencer ask the same question of the hex
width; this is the node's side of it.
-/
def checkHex (suite : CryptoSuite) (pubKeyHex : String) (msg : ByteArray)
    (sigHex : String) : Bool :=
  match Sync.ofHex? pubKeyHex, Sync.ofHex? sigHex with
  | some pk, some sig =>
    pk.size == suite.signPkSize && sig.size == suite.signatureSize && suite.verify pk msg sig
  | _, _ => false

/-! ## The test suite -/

/-- The domain a test signature is taken under. -/
private def insecureSignTag : String := "resources/insecure/sign/v1"

/-- The domain a test realm key is wrapped under. -/
private def insecureWrapTag : String := "resources/insecure/wrap/v1"

/-- The domain a test part's authenticator is taken under. -/
private def insecureSealTag : String := "resources/insecure/seal/v1"

/-- The domain a test passphrase is stretched under. -/
private def insecureKdfTag : String := "resources/insecure/kdf/v1"

/--
**Test-only. This suite provides no confidentiality and no authenticity.**

Read what it actually does, because every one of these is a hole somebody could
drive a ledger through:

* a *signature* is `SHA-256(sk ++ msg)`, and the public key is the seed itself
  while the secret key is that seed twice — so `verify pk msg sig` recomputes
  the signature from the public key, and anybody who can check a signature can
  forge one;
* *encryption* is the plaintext, unchanged, followed by a 16-byte tag
  `SHA-256(key ++ nonce ++ ad ++ plaintext)` — the tag catches a change to the
  ciphertext, the associated data or the key, and the plaintext is in the clear
  for anybody holding the bytes;
* *wrapping* is the key XORed with a stream derived from the recipient's public
  key, with a 16-byte check value — and since the agreement secret key is its
  own public key, anybody who knows who a key was wrapped for can unwrap it;
* the *passphrase* is stretched by one pass of SHA-256 over the parameters, the
  passphrase and the salt, which is no work at all for somebody guessing — the
  parameters change the key without costing anything to compute, which is shape
  and not work, and is the whole bargain of this value. Its `kdf` field records a
  cost inside the range `Node/Identity.lean` accepts for the same reason: the
  files it writes have to be the shape the real suite's files are.

What it does faithfully is *shape*: every size, every tag, every failure mode
and every byte string that gets signed or sealed is the one the real suite will
use. That is what makes the sync path testable before libsodium is bound, and
it is the only thing this value is for.
-/
def insecureForTests : CryptoSuite :=
  let signSeedKeypair := fun (seed : ByteArray) =>
    let pk := keyStream (insecureSignTag.toUTF8 ++ seed) 32
    (pk, pk ++ pk)
  let boxSeedKeypair := fun (seed : ByteArray) =>
    let pk := keyStream (insecureWrapTag.toUTF8 ++ seed) 32
    (pk, pk)
  let sign := fun (sk msg : ByteArray) =>
    Sha256.hash (insecureSignTag.toUTF8 ++ sk ++ msg)
  let wrapMask := fun (pk : ByteArray) (len : Nat) =>
    keyStream (insecureWrapTag.toUTF8 ++ pk) len
  let wrapCheck := fun (pk key : ByteArray) =>
    take (Sha256.hash (insecureWrapTag.toUTF8 ++ "check".toUTF8 ++ pk ++ key)) 16
  let sealTag := fun (key nonce ad plaintext : ByteArray) =>
    take (Sha256.hash (insecureSealTag.toUTF8 ++ key ++ nonce ++ ad ++ plaintext)) 16
  { name := "insecure-sha256 (TEST ONLY)", verifierName := "insecure"
    signPkSize := 32, signSkSize := 64, signatureSize := 32
    boxPkSize := 32, boxSkSize := 32
    keySize := 32, nonceSize := 24, tagSize := 16, saltSize := 16
    kdf := { alg := "insecure-sha256", ops := 1, mem := 64 * 1024 * 1024 }
    sign
    verify := fun pk msg signature =>
      Sha256.constantTimeEq signature (sign (pk ++ pk) msg)
    sealPart := fun key nonce ad plaintext =>
      plaintext ++ sealTag key nonce ad plaintext
    openPart := fun key nonce ad ciphertext =>
      if ciphertext.size < 16 then none
      else
        let plaintext := take ciphertext (ciphertext.size - 16)
        let stated := drop ciphertext (ciphertext.size - 16)
        if Sha256.constantTimeEq stated (sealTag key nonce ad plaintext) then some plaintext
        else none
    wrapKey := fun recipientPk key =>
      xorBytes key (wrapMask recipientPk key.size) ++ wrapCheck recipientPk key
    unwrapKey := fun recipientSk bytes =>
      if bytes.size < 16 then none
      else
        let body := take bytes (bytes.size - 16)
        let stated := drop bytes (bytes.size - 16)
        let key := xorBytes body (wrapMask recipientSk body.size)
        if Sha256.constantTimeEq stated (wrapCheck recipientSk key) then some key else none
    deriveKey := fun passphrase salt params =>
      Sha256.hash (insecureKdfTag.toUTF8 ++ params.alg.toUTF8 ++ (toString params.ops).toUTF8
        ++ (toString params.mem).toUTF8 ++ passphrase.toUTF8 ++ salt)
    randomBytes := fun n => IO.getRandomBytes n.toUSize
    signSeedKeypair, boxSeedKeypair
    signKeypair := do return signSeedKeypair (← IO.getRandomBytes seedSize.toUSize)
    boxKeypair := do return boxSeedKeypair (← IO.getRandomBytes seedSize.toUSize) }

/-! ## Asking for the test suite out loud

Two things have to say it, and they are deliberately different kinds of thing.

`RESOURCES_INSECURE_CRYPTO=1` is the environment, which is what a service
manager, a container image or a stray line in a shell profile sets — and which
is therefore exactly what gets inherited by a process nobody meant to start that
way. `--insecure-dev` is on the command line of the run in front of you, which
nothing inherits and nothing carries forward. One without the other is a
mistake, so one without the other is a refusal rather than a rehearsal, and the
error says which half is missing.
-/

/--
Whether this run was asked, on its own command line, to accept the test suite.

A reference rather than an argument because the thing that reads it is several
layers below the thing that parses flags: `Node/Realms.lean` builds a suite from
inside a route, and a route has no command line. The command handler sets it
once, before anything opens a key.
-/
initialize insecureDevFlag : IO.Ref Bool ← IO.mkRef false

/-- Records that `--insecure-dev` was given on this command line. -/
def allowInsecureDev : IO Unit := insecureDevFlag.set true

/-- Whether `--insecure-dev` was given on this command line. -/
def insecureDevAsked : IO Bool := insecureDevFlag.get

/-- What is printed, on every command, by a run that is using the test suite. -/
def insecureWarning : String :=
  "warning: RESOURCES_INSECURE_CRYPTO=1 --insecure-dev — this node is using the test suite. \
   It signs with a hash of its own public key and encrypts nothing. Every event it pushes is \
   readable by whoever holds the bytes."

end CryptoSuite

end Node

namespace Sync

/--
The verifier a sequencer built on this suite checks signatures with.

`Sync/Protocol.lean` left the check as a field precisely so that this line could
exist: the sequencer is written against `Verifier`, and binding a scheme is one
value, not a change to a route.
-/
def Verifier.ofSuite (suite : Node.CryptoSuite) : Verifier :=
  { name := suite.verifierName, verify := suite.verify,
    -- The suite knows its own signature width, so the verifier gets the exact
    -- length check rather than the range `Verifier.check` falls back on when a
    -- scheme did not say. Ed25519 is 128 hex characters and the test suite is
    -- 64, and neither of them ever hands the primitive a short buffer.
    signatureHexWidth := 2 * suite.signatureSize }

end Sync

end Resources
