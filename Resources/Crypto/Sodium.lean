import Resources.Node.Crypto

/-!
# libsodium

The suite `Node/Crypto.lean` was written against, bound to the primitives the
design names: Ed25519 to say who wrote an event, X25519 and `crypto_box_seal` to
hand a realm key to somebody, XChaCha20-Poly1305 to seal what an event says, and
Argon2id to turn a passphrase into the key that opens this node's files.

`CryptoSuite.sodium` is one value of the record that file defines, so nothing
above it changes: `Node/Envelope.lean`, `Node/Keys.lean` and the rest were
composing these operations already, and what arrives here is the operations.

## These functions are axioms

Every `@[extern]` below is a hole in what this repository proves. Lean sees an
opaque constant of some type; what it does is decided by `c/sodium_shim.c` and
by libsodium, and no theorem here covers either. So each one is documented with
the property it is *assumed* to have, in the terms the callers rely on, and the
tests in `Test/Crypto.lean` check the assumptions that can be checked from
outside: round trips, rejections, and the published test vectors for Ed25519 and
XChaCha20-Poly1305, which are the two primitives that have to agree byte for
byte with another implementation -- the thin client's libsodium-wrappers, and
anybody else's client.

What cannot be checked from outside is the part that matters most: that these
functions keep secrets. That is an assumption about libsodium, and binding it
rather than writing it is the whole point.

## Sizes come from the constants

Every size this suite reports is read out of libsodium's own compile-time
constants through the shim rather than written here as a number. A build against
a libsodium whose sizes differed would report the sizes it has, and the tests
below pin them to the numbers the protocol documents, so a disagreement is a
failed test rather than a truncated key.

## What a deployment has to install

The binding is linked at build time against whatever `pkg-config libsodium`
reports, and at run time against the shared library that was found then. The
lakefile says this in full; in short, a NixOS build wants `pkgs.libsodium` in
`buildInputs` and `pkgs.pkg-config` in `nativeBuildInputs`, which is enough for
both the link and the `RPATH` the binary keeps, and a Debian machine wants
`libsodium-dev` to build and `libsodium23` to run.
-/

namespace Resources
namespace Sodium

/-! ## Starting up -/

/--
`sodium_init`.

Assumed: it picks the implementations this CPU has and seeds the random
generator, it must be called before anything else here, and it is an error to
carry on if it fails.

It is called from the module initializer below, which runs once, when this
module is loaded -- in a linked binary before `main`, and in the interpreter
when a later module imports this one. Nothing in this file can be reached
without having gone through it.
-/
@[extern "resources_sodium_init"] private opaque initSodium : IO Unit

initialize initSodium

/-! ## Sizes

Each of these is one libsodium constant, read through the shim. They are
`Unit → USize` rather than constants because an `@[extern]` with no arguments is
a symbol Lean would have to fetch rather than call.
-/

@[extern "resources_sodium_sign_pk_size"] private opaque signPkSizeC : Unit → USize
@[extern "resources_sodium_sign_sk_size"] private opaque signSkSizeC : Unit → USize
@[extern "resources_sodium_sign_seed_size"] private opaque signSeedSizeC : Unit → USize
@[extern "resources_sodium_signature_size"] private opaque signatureSizeC : Unit → USize
@[extern "resources_sodium_box_pk_size"] private opaque boxPkSizeC : Unit → USize
@[extern "resources_sodium_box_sk_size"] private opaque boxSkSizeC : Unit → USize
@[extern "resources_sodium_box_seed_size"] private opaque boxSeedSizeC : Unit → USize
@[extern "resources_sodium_seal_overhead"] private opaque sealOverheadC : Unit → USize
@[extern "resources_sodium_aead_key_size"] private opaque aeadKeySizeC : Unit → USize
@[extern "resources_sodium_aead_nonce_size"] private opaque aeadNonceSizeC : Unit → USize
@[extern "resources_sodium_aead_tag_size"] private opaque aeadTagSizeC : Unit → USize
@[extern "resources_sodium_pwhash_salt_size"] private opaque saltSizeC : Unit → USize
@[extern "resources_sodium_pwhash_ops_interactive"] private opaque opsInteractiveC : Unit → USize
@[extern "resources_sodium_pwhash_mem_interactive"] private opaque memInteractiveC : Unit → USize

/-- `crypto_sign_PUBLICKEYBYTES`: 32, and a member id is its hex. -/
def signPkSize : Nat := (signPkSizeC ()).toNat

/-- `crypto_sign_SECRETKEYBYTES`: 64, the seed followed by the public key. -/
def signSkSize : Nat := (signSkSizeC ()).toNat

/-- `crypto_sign_SEEDBYTES`: 32. -/
def signSeedSize : Nat := (signSeedSizeC ()).toNat

/-- `crypto_sign_BYTES`: 64. -/
def signatureSize : Nat := (signatureSizeC ()).toNat

/-- `crypto_box_PUBLICKEYBYTES`: 32. -/
def boxPkSize : Nat := (boxPkSizeC ()).toNat

/-- `crypto_box_SECRETKEYBYTES`: 32. -/
def boxSkSize : Nat := (boxSkSizeC ()).toNat

/-- `crypto_box_SEEDBYTES`: 32. -/
def boxSeedSize : Nat := (boxSeedSizeC ()).toNat

/-- `crypto_box_SEALBYTES`: 48, the ephemeral public key and the tag. -/
def sealOverhead : Nat := (sealOverheadC ()).toNat

/-- `crypto_aead_xchacha20poly1305_ietf_KEYBYTES`: 32. -/
def keySize : Nat := (aeadKeySizeC ()).toNat

/-- `crypto_aead_xchacha20poly1305_ietf_NPUBBYTES`: 24, which is why it is the X variant. -/
def nonceSize : Nat := (aeadNonceSizeC ()).toNat

/-- `crypto_aead_xchacha20poly1305_ietf_ABYTES`: 16. -/
def tagSize : Nat := (aeadTagSizeC ()).toNat

/-- `crypto_pwhash_SALTBYTES`: 16. -/
def saltSize : Nat := (saltSizeC ()).toNat

/-- `crypto_pwhash_OPSLIMIT_INTERACTIVE`: the passes libsodium recommends for a login. -/
def opsInteractive : Nat := (opsInteractiveC ()).toNat

/-- `crypto_pwhash_MEMLIMIT_INTERACTIVE`: the memory it recommends for one, 64 MiB. -/
def memInteractive : Nat := (memInteractiveC ()).toNat

/-! ## Randomness -/

/--
`randombytes_buf`.

Assumed: `n` bytes from the operating system's generator, unpredictable to
anybody who does not have them, and failing rather than returning if the system
cannot provide them.
-/
@[extern "resources_sodium_random_bytes"] private opaque randomBytesC : USize → IO ByteArray

/-- `n` bytes from the operating system's random source. -/
def randomBytes (n : Nat) : IO ByteArray := randomBytesC n.toUSize

/-! ## Ed25519

A signature says that whoever holds the secret key put their name to exactly
these bytes. `Sync/Protocol.lean` decides what those bytes are; this decides
nothing at all about them.
-/

/--
`crypto_sign_seed_keypair`, returning the public key followed by the secret key.

Assumed: the key pair is a function of the seed alone, so the same seed gives
the same pair on every machine and in every implementation -- which is what
makes an invite work, since the inviter derives the key pair the joiner will
derive from the secret in the link. A seed that is not `signSeedSize` bytes
comes back empty.
-/
@[extern "resources_sodium_sign_seed_keypair"]
private opaque signSeedKeypairC : @&ByteArray → ByteArray

/--
`crypto_sign_detached`.

Assumed: 64 bytes that `verify` accepts under the matching public key and this
message, that nobody without the secret key can produce for a message its holder
has not signed, and that reveal nothing about the key. A secret key of the wrong
length comes back empty, which is a signature every verifier rejects.
-/
@[extern "resources_sodium_sign"] private opaque signC : @&ByteArray → @&ByteArray → ByteArray

/--
`crypto_sign_verify_detached`.

Assumed: true exactly when this signature was produced by the secret key
matching this public key, over these exact bytes. A key or a signature of the
wrong length is false, checked in C before libsodium is handed a pointer.
-/
@[extern "resources_sodium_verify"]
private opaque verifyC : @&ByteArray → @&ByteArray → @&ByteArray → Bool

/-- The key pair a seed determines, as `(pk, sk)`. -/
def signSeedKeypair (seed : ByteArray) : ByteArray × ByteArray :=
  let both := signSeedKeypairC seed
  if both.size == signPkSize + signSkSize then
    (both.extract 0 signPkSize, both.extract signPkSize both.size)
  else
    (ByteArray.empty, ByteArray.empty)

/-- A fresh signing key pair, from a fresh seed. -/
def signKeypair : IO (ByteArray × ByteArray) := do
  return signSeedKeypair (← randomBytes signSeedSize)

/-- Signs `msg` under a signing secret key. -/
def sign (sk msg : ByteArray) : ByteArray := signC sk msg

/-- Whether `signature` is a signature of `msg` under a signing public key. -/
def verify (pk msg signature : ByteArray) : Bool := verifyC pk msg signature

/-! ## X25519 and sealed boxes

A realm key is handed to somebody by sealing it to their agreement key. The box
is anonymous -- it carries an ephemeral public key rather than the sender's --
and who granted what is said by the signed grant record instead, where it can be
checked by a sequencer that cannot read either.
-/

/--
`crypto_box_seed_keypair`, returning the public key followed by the secret key.

Assumed: a function of the seed alone, as the signing pair is, and unrelated to
the signing pair derived from the same seed beyond both being derived from it.
-/
@[extern "resources_sodium_box_seed_keypair"]
private opaque boxSeedKeypairC : @&ByteArray → ByteArray

/--
`crypto_box_seal`.

Assumed: `sealOverhead` bytes longer than the message; readable only by the
holder of the matching secret key; saying nothing about who sealed it; and
different every time, because the ephemeral key pair is fresh -- so two grants
of one key to one member do not look alike.

That last part makes this the one function in this file that is not a function
of its arguments, while the field it fills -- `CryptoSuite.wrapKey` -- is a pure
one. Lean is therefore entitled to evaluate two identical applications once and
share the answer, and does. Nothing relies on two boxes differing: what a caller
needs is that what comes back unwraps to what went in, and every caller wraps
once and keeps the result.
-/
@[extern "resources_sodium_box_seal"]
private opaque boxSealC : @&ByteArray → @&ByteArray → ByteArray

/--
`crypto_box_seal_open`, with the public key recomputed from the secret one.

Assumed: the message when this is a box sealed to this key pair, and `none`
otherwise -- including for a box sealed to somebody else, and for one whose
bytes have been changed.
-/
@[extern "resources_sodium_box_seal_open"]
private opaque boxSealOpenC : @&ByteArray → @&ByteArray → Option ByteArray

/-- The agreement key pair a seed determines, as `(pk, sk)`. -/
def boxSeedKeypair (seed : ByteArray) : ByteArray × ByteArray :=
  let both := boxSeedKeypairC seed
  if both.size == boxPkSize + boxSkSize then
    (both.extract 0 boxPkSize, both.extract boxPkSize both.size)
  else
    (ByteArray.empty, ByteArray.empty)

/-- A fresh agreement key pair, from a fresh seed. -/
def boxKeypair : IO (ByteArray × ByteArray) := do
  return boxSeedKeypair (← randomBytes boxSeedSize)

/-- Seals `bytes` to an agreement public key, so only its holder can read them. -/
def wrap (recipientPk bytes : ByteArray) : ByteArray := boxSealC recipientPk bytes

/-- Opens what `wrap` produced, given the matching agreement secret key. -/
def unwrap? (recipientSk bytes : ByteArray) : Option ByteArray := boxSealOpenC recipientSk bytes

/-! ## XChaCha20-Poly1305 IETF

The nonce is 24 bytes, which is the reason for the X: at that width a random
nonce per part is safe without any counter to keep, and `Node/Envelope.lean`
draws one from `randomBytes` for every part it seals.
-/

/--
`crypto_aead_xchacha20poly1305_ietf_encrypt`, with the tag appended.

Assumed: `tagSize` bytes longer than the plaintext; readable only with the key;
and openable only with this key, this nonce and this associated data, so that
changing any byte of the ciphertext, of the associated data, or of either key
makes it unopenable rather than opening it to something else.

Assumed of the caller, and not enforced here: a nonce is used once per key. Every
caller takes one from `randomBytes`.
-/
@[extern "resources_sodium_aead_encrypt"]
private opaque aeadEncryptC : @&ByteArray → @&ByteArray → @&ByteArray → @&ByteArray → ByteArray

/--
`crypto_aead_xchacha20poly1305_ietf_decrypt`.

Assumed: the plaintext when everything matches, and `none` when anything does
not -- and in particular that it verifies the tag before returning any of the
plaintext, so `none` is what a reader gets rather than bytes somebody chose.
-/
@[extern "resources_sodium_aead_decrypt"]
private opaque aeadDecryptC :
  @&ByteArray → @&ByteArray → @&ByteArray → @&ByteArray → Option ByteArray

/-- Seals `plaintext` under `key` and `nonce`, authenticating `ad` as well. -/
def sealPart (key nonce ad plaintext : ByteArray) : ByteArray :=
  aeadEncryptC key nonce ad plaintext

/-- Opens what `sealPart` produced, or `none` if anything about it has changed. -/
def openPart? (key nonce ad ciphertext : ByteArray) : Option ByteArray :=
  aeadDecryptC key nonce ad ciphertext

/-! ## Argon2id -/

/-- The name this suite writes into the `kdf` object of every file it encrypts. -/
def kdfAlg : String := "argon2id"

/--
`crypto_pwhash` with `crypto_pwhash_ALG_ARGON2ID13`.

Assumed: a function of the passphrase, the salt, the length and the two cost
parameters alone -- the same everywhere, which is what lets a file written on one
machine open on another -- and one that costs `mem` bytes of memory and `ops`
passes over them to compute, so that guessing passphrases costs the guesser the
same. A salt of the wrong length, a cost outside what libsodium accepts, or
memory it could not obtain, all come back empty, which is a key that opens
nothing.
-/
@[extern "resources_sodium_pwhash"]
private opaque pwhashC : @&String → @&ByteArray → USize → USize → USize → ByteArray

/--
Stretches a passphrase and a salt into a `keySize`-byte key at the stated cost.

A `KdfParams` naming another stretcher is refused here rather than computed as
Argon2id: the parameters come out of the file being opened, and a file that says
`scrypt` was not written by this suite. `Node/Identity.lean` refuses it earlier
still, by comparing the name against the suite's own before it derives anything.
-/
def deriveKey (passphrase : String) (salt : ByteArray) (params : Node.KdfParams) : ByteArray :=
  if params.alg == kdfAlg then
    pwhashC passphrase salt keySize.toUSize params.ops.toUSize params.mem.toUSize
  else
    ByteArray.empty

end Sodium

namespace Node
namespace CryptoSuite

/--
The primitives, as the node's interface to them.

Every field is one call into `Resources/Crypto/Sodium.lean` and every size is
one of libsodium's constants. There is nothing else in here -- no framing, no
domain separation, no encoding -- because all of that is already above this line
in `Node/Envelope.lean`, `Node/Identity.lean` and `Sync/Protocol.lean`, written
against this record and tested against `insecureForTests` long before there was
anything to bind.
-/
def sodium : CryptoSuite :=
  { name := "sodium", verifierName := "sodium"
    signPkSize := Sodium.signPkSize
    signSkSize := Sodium.signSkSize
    signatureSize := Sodium.signatureSize
    boxPkSize := Sodium.boxPkSize
    boxSkSize := Sodium.boxSkSize
    keySize := Sodium.keySize
    nonceSize := Sodium.nonceSize
    tagSize := Sodium.tagSize
    saltSize := Sodium.saltSize
    -- What a file written by this build records, and what a file written by
    -- another one is read at: `Node/Identity.lean` derives with the parameters
    -- it finds rather than with these.
    kdf := { alg := Sodium.kdfAlg, ops := Sodium.opsInteractive, mem := Sodium.memInteractive }
    sign := Sodium.sign
    verify := Sodium.verify
    sealPart := Sodium.sealPart
    openPart := Sodium.openPart?
    wrapKey := Sodium.wrap
    unwrapKey := Sodium.unwrap?
    deriveKey := Sodium.deriveKey
    randomBytes := Sodium.randomBytes
    signSeedKeypair := Sodium.signSeedKeypair
    boxSeedKeypair := Sodium.boxSeedKeypair
    signKeypair := Sodium.signKeypair
    boxKeypair := Sodium.boxKeypair }

/--
The suite a command-line node runs with: this one.

It lives here rather than beside the test suite in `Node/Crypto.lean` because it
is the one function that has to name both of them, and the real one is defined
in this file.

The test suite is still reachable, and still only by asking for it out loud
twice -- `RESOURCES_INSECURE_CRYPTO=1` in the environment *and* `--insecure-dev`
on this command line -- with a warning on every run. Half of that is a mistake
rather than a decision, and a mistake gets a refusal that says which half is
missing: a variable alone is something a service manager or a stray line in a
profile can set without anybody meaning it, and a flag alone is somebody
expecting the test suite and about to be handed real encryption they cannot read
with it.
-/
def forNode : IO CryptoSuite := do
  let asked := (← IO.getEnv "RESOURCES_INSECURE_CRYPTO") == some "1"
  let flagged ← insecureDevFlag.get
  if asked && flagged then
    IO.eprintln insecureWarning
    return insecureForTests
  if asked then
    throw <| IO.userError "RESOURCES_INSECURE_CRYPTO=1 is set, but the test suite protects \
                           nothing and an inherited environment is not a decision: pass \
                           --insecure-dev on this command as well, or unset the variable."
  if flagged then
    throw <| IO.userError "--insecure-dev was given, but RESOURCES_INSECURE_CRYPTO=1 was not \
                           set, so the test suite was not reached: unset the flag to run the \
                           real one, or set the variable if a test suite is what was wanted."
  return sodium

end CryptoSuite
end Node
end Resources
