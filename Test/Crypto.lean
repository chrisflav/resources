import Test.Sync
import Resources.Node.Sync
import Resources.Crypto.Sodium

/-!
# The libsodium binding

`Resources/Crypto/Sodium.lean` binds five primitives, and every one of them is an
axiom as far as Lean is concerned: an opaque constant whose meaning is decided by
C. What can be checked from outside is checked here.

Three kinds of thing are asked. *Round trips* — what was signed verifies, what
was sealed opens — which catch a binding that passes arguments in the wrong
order or truncates a buffer. *Rejections* — a flipped bit, other associated
data, another recipient's key — which catch a binding that authenticates nothing,
because a round trip alone is satisfied by a suite that returns its input.

And *test vectors*, which are the only thing here that checks agreement with
another implementation. The signature in `Test 1` of RFC 8032 and the ciphertext
in `A.3.1` of `draft-irtf-cfrg-xchacha` are the bytes every other Ed25519 and
XChaCha20-Poly1305 does produce, so a node whose envelopes the thin client
cannot verify, or whose parts it cannot open, fails here rather than in
somebody's browser.

The last test is the whole of `Test/Node.lean`'s subject in miniature: two nodes
and a sequencer, this time over the real primitives, from creating an identity
to both of them holding the same state.
-/

open Lean Resources

/-- The primitives under test. -/
private def suite : Node.CryptoSuite := Node.CryptoSuite.sodium

/-- Hex, decoded, or nothing at all — every literal below is hex this file wrote. -/
private def bytes (hex : String) : ByteArray := (Sync.ofHex? hex).getD ByteArray.empty

/-- The same byte string with the lowest bit of its first byte flipped. -/
private def flipBit (bs : ByteArray) : ByteArray :=
  if bs.size == 0 then bs else bs.set! 0 (bs[0]! ^^^ 1)

/-! ## Sizes, keys, signatures, boxes and the stretcher -/

private def primitiveTests (r : Report) : IO Report := do
  let mut r := r

  /- ## The sizes are the ones the protocol documents

  They are read out of libsodium's constants rather than written into the Lean,
  so this is the check that the library this build linked is the one the wire
  format was designed against. -/
  r := checkEq r "an Ed25519 public key is 32 bytes" suite.signPkSize 32
  r := checkEq r "an Ed25519 secret key is 64" suite.signSkSize 64
  r := checkEq r "an Ed25519 signature is 64" suite.signatureSize 64
  r := checkEq r "an X25519 public key is 32" suite.boxPkSize 32
  r := checkEq r "an X25519 secret key is 32" suite.boxSkSize 32
  r := checkEq r "a realm key is 32" suite.keySize 32
  r := checkEq r "an XChaCha20 nonce is 24" suite.nonceSize 24
  r := checkEq r "a Poly1305 tag is 16" suite.tagSize 16
  r := checkEq r "an Argon2id salt is 16" suite.saltSize 16
  r := checkEq r "a sealed box costs 48 bytes over its contents" Sodium.sealOverhead 48
  r := checkEq r "both key pairs are derived from a seed of the size the suite states"
    (Sodium.signSeedSize, Sodium.boxSeedSize)
    (Node.CryptoSuite.seedSize, Node.CryptoSuite.seedSize)
  r := checkEq r "the stretcher this build writes into a file is Argon2id" suite.kdf.alg "argon2id"
  r := check r "at a cost inside the range this binary reads files at"
    (Node.minKdfOps ≤ suite.kdf.ops && suite.kdf.ops ≤ Node.maxKdfOps
      && Node.minKdfMem ≤ suite.kdf.mem && suite.kdf.mem ≤ Node.maxKdfMem)
  r := checkEq r "which is what libsodium recommends for a login"
    (suite.kdf.ops, suite.kdf.mem) (Sodium.opsInteractive, Sodium.memInteractive)

  /- ## Signing -/
  let (pk, sk) ← suite.signKeypair
  r := checkEq r "a generated signing key pair is the pair of sizes it says"
    (pk.size, sk.size) (suite.signPkSize, suite.signSkSize)
  let msg := "an entry, as it would be signed".toUTF8
  let sig := suite.sign sk msg
  r := checkEq r "a signature is 64 bytes" sig.size suite.signatureSize
  r := check r "and verifies under the public key, over the bytes it was taken over"
    (suite.verify pk msg sig)
  r := check r "a signature with a bit flipped does not verify" (!suite.verify pk msg (flipBit sig))
  r := check r "nor does a good signature over a message with a bit flipped"
    (!suite.verify pk (flipBit msg) sig)
  let (otherPk, _) ← suite.signKeypair
  r := check r "nor does it verify under somebody else's key" (!suite.verify otherPk msg sig)
  r := check r "and a signature is the same one every time, because Ed25519 is deterministic"
    (toHex (suite.sign sk msg) == toHex sig)
  r := check r "a key pair derived twice from one seed is one key pair"
    (let seed := Sha256.hash "a seed".toUTF8
     let (pk₁, sk₁) := suite.signSeedKeypair seed
     let (pk₂, sk₂) := suite.signSeedKeypair seed
     toHex pk₁ == toHex pk₂ && toHex sk₁ == toHex sk₂)

  /- ## RFC 8032, Test 1

  The seed, the public key it determines and the signature over the empty
  message. Every Ed25519 in the world produces these three, so a client written
  against another library and this node agree about who wrote an entry. -/
  let rfcSeed := bytes "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
  let rfcPk := "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let rfcSig := "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e0652249015\
                 55fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
  let (vecPk, vecSk) := suite.signSeedKeypair rfcSeed
  r := checkEq r "RFC 8032 test 1: the seed determines the published public key"
    (toHex vecPk) rfcPk
  r := checkEq r "and the published signature over the empty message"
    (toHex (suite.sign vecSk ByteArray.empty)) rfcSig
  r := check r "which verifies, decoded from the document rather than computed"
    (suite.verify (bytes rfcPk) ByteArray.empty (bytes rfcSig))

  /- ## Sealing a part -/
  let key ← suite.randomBytes suite.keySize
  let nonce ← suite.randomBytes suite.nonceSize
  let ad := "the realm, the generation and the author".toUTF8
  let plaintext := "what the entry actually says".toUTF8
  let sealed := suite.sealPart key nonce ad plaintext
  r := checkEq r "a sealed part is its plaintext plus a tag" sealed.size (plaintext.size + 16)
  r := check r "and is not its plaintext" (toHex sealed != toHex plaintext)
  r := checkEq r "it opens under the same key, nonce and associated data"
    ((suite.openPart key nonce ad sealed).map toHex) (some (toHex plaintext))
  r := check r "a ciphertext with a bit flipped does not open"
    (suite.openPart key nonce ad (flipBit sealed)).isNone
  r := check r "nor does it open under other associated data"
    (suite.openPart key nonce (ad.push 0) sealed).isNone
  r := check r "nor under another nonce" (suite.openPart key (flipBit nonce) ad sealed).isNone
  r := check r "nor under another key" (suite.openPart (flipBit key) nonce ad sealed).isNone

  /- ## draft-irtf-cfrg-xchacha, A.3.1

  The AEAD vector: key, 24-byte nonce, associated data and the plaintext from
  RFC 8439, with the ciphertext and the tag the draft publishes. This is the
  format an event's parts travel in, so it is the one that has to be the same
  in a browser. -/
  let vecKey := bytes "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let vecNonce := bytes "404142434445464748494a4b4c4d4e4f5051525354555657"
  let vecAd := bytes "50515253c0c1c2c3c4c5c6c7"
  let vecPlain :=
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the \
     future, sunscreen would be it.".toUTF8
  let vecSealed :=
    "bd6d179d3e83d43b9576579493c0e939572a1700252bfaccbed2902c21396cbb731c7f1b0b4aa6440bf3a\
     82f4eda7e39ae64c6708c54c216cb96b72e1213b4522f8c9ba40db5d945b11b69b982c1bb9e3f3fac2bc3\
     69488f76b2383565d3fff921f9664c97637da9768812f615c68b13b52e\
     c0875924c1c7987947deafd8780acf49"
  r := checkEq r "the XChaCha20-Poly1305 vector seals to the published ciphertext and tag"
    (toHex (suite.sealPart vecKey vecNonce vecAd vecPlain)) vecSealed
  r := checkEq r "and the published bytes open to the published plaintext"
    ((suite.openPart vecKey vecNonce vecAd (bytes vecSealed)).bind String.fromUTF8?)
    (String.fromUTF8? vecPlain)

  /- ## Handing a realm key to somebody -/
  let (boxPk, boxSk) ← suite.boxKeypair
  let (otherBoxPk, otherBoxSk) ← suite.boxKeypair
  r := checkEq r "a generated agreement key pair is the pair of sizes it says"
    (boxPk.size, boxSk.size) (suite.boxPkSize, suite.boxSkSize)
  let realmKey ← suite.randomBytes suite.keySize
  let wrapped := suite.wrapKey boxPk realmKey
  r := checkEq r "a wrapped key costs the sealed-box overhead"
    wrapped.size (realmKey.size + Sodium.sealOverhead)
  r := checkEq r "and comes back to the key it was wrapped for"
    ((suite.unwrapKey boxSk wrapped).map toHex) (some (toHex realmKey))
  r := check r "somebody else's key does not unwrap it"
    (suite.unwrapKey otherBoxSk wrapped).isNone
  r := check r "nor does the right key on a changed box"
    (suite.unwrapKey boxSk (flipBit wrapped)).isNone
  -- Copies of the same bytes rather than the same bytes: `wrapKey` is a pure
  -- Lean function, so two identical applications of it may be evaluated once
  -- and shared, and what is being asked about here is the second call.
  r := check r "wrapping one key for one recipient twice does not produce the same box, \
                because the sender is ephemeral"
    (toHex (suite.wrapKey (boxPk.extract 0 boxPk.size) (realmKey.extract 0 realmKey.size))
      != toHex wrapped)
  r := check r "and the other recipient's box is not this one's"
    (toHex (suite.wrapKey otherBoxPk realmKey) != toHex wrapped)

  /- ## Stretching a passphrase

  Nothing is pinned to a published vector here: the cost parameters this build
  writes are libsodium's interactive limits, and a vector at those limits would
  pin the cost rather than the function. What is checked is what the identity
  file depends on — that one passphrase, salt and cost give one key, everywhere
  and every time, and that changing any of the three changes the key. -/
  let salt ← suite.randomBytes suite.saltSize
  let otherSalt ← suite.randomBytes suite.saltSize
  let derived := suite.deriveKey "a passphrase" salt suite.kdf
  r := checkEq r "a stretched passphrase is a realm key's worth of bytes" derived.size suite.keySize
  r := checkEq r "and the same passphrase, salt and cost give the same key every time"
    (toHex (suite.deriveKey "a passphrase" salt suite.kdf)) (toHex derived)
  r := check r "another salt gives another key"
    (toHex (suite.deriveKey "a passphrase" otherSalt suite.kdf) != toHex derived)
  r := check r "another passphrase gives another key"
    (toHex (suite.deriveKey "a passphrase " salt suite.kdf) != toHex derived)
  r := check r "and another cost gives another key"
    (toHex (suite.deriveKey "a passphrase" salt { suite.kdf with ops := suite.kdf.ops + 1 })
      != toHex derived)
  r := check r "a stretcher this suite does not compute yields no key at all"
    ((suite.deriveKey "a passphrase" salt { suite.kdf with alg := "scrypt" }).size == 0)

  /- ## What the sequencer does with all of this

  `Verifier.ofSuite` is the sequencer's whole relationship with cryptography: an
  envelope is accepted if its author's key signed exactly `signingBytes`. -/
  let verifier := Sync.Verifier.ofSuite suite
  r := checkEq r "the sequencer's verifier says which scheme it is" verifier.name "sodium"
  r := checkEq r "and that a signature is 128 hex characters wide" verifier.signatureHexWidth 128
  let unsigned : Sync.Envelope :=
    { ledger := "home", seq := 1, prevHash := "", author := toHex pk,
      parts := [{ realm := "home", generation := 1, ciphertext := sealed }], signature := "" }
  let envelope := { unsigned with signature := toHex (suite.sign sk unsigned.signingBytes) }
  r := check r "an envelope signed over its signing bytes is accepted"
    (verifier.check envelope.author envelope.signingBytes envelope.signature)
  r := check r "one signed by another key is not"
    (!verifier.check (toHex otherPk) envelope.signingBytes envelope.signature)
  r := check r "nor is one whose fields changed after it was signed"
    (!verifier.check envelope.author { envelope with seq := 2 }.signingBytes envelope.signature)
  r := check r "nor a signature of the right shape that is not one"
    (!verifier.check envelope.author envelope.signingBytes
      (String.ofList (List.replicate 128 '0')))
  r := check r "and a 32-byte signature, which the test suite's width is, is not even asked about"
    (!verifier.check envelope.author envelope.signingBytes
      (String.ofList (List.replicate 64 'a')))
  return r

/-! ## Two nodes over the real primitives -/

/-- One node: its store, its identity, its keys and its way to the sequencer. -/
private structure Peer where
  ctx : Ctx
  identity : Node.Identity
  keys : Node.Keyring
  transport : Node.Transport

/-- Opens a store, gives it an identity, and points it at the sequencer. -/
private def makePeer (root : System.FilePath) (name : String) (seq : Sync.Node) : IO Peer := do
  let cfg := Config.atDir (root / name)
  let opened ← Ctx.open cfg
  let identity ← Node.Identity.create suite (Node.Identity.pathIn cfg) s!"pass-{name}"
  let ctx ← Node.Identity.install opened identity name
  Node.Settings.setMember cfg identity.id
  let keys ← Node.Keys.open suite (Node.Keys.pathIn cfg) s!"pass-{name}" identity
  return { ctx, identity, keys, transport := ← Node.Transport.inProcess suite identity seq }

/-- An instant a week from now, in the one shape the sequencer stores. -/
private def aWeekFromNow : IO String := do
  let seconds := ((Sync.isoSeconds? (← Sync.Log.utcNow)).getD 0) + 7 * 86400
  let days := seconds / 86400 - (if seconds % 86400 < 0 then 1 else 0)
  let secondOfDay := (seconds - days * 86400).toNat
  let (y, m, d) := Sync.civilFromDays days
  return Sync.isoCanonical y m d (secondOfDay / 3600) (secondOfDay / 60 % 60) (secondOfDay % 60)

-- One long `do` block, for the same reason as in `Test/Node.lean`: every step
-- below depends on the ledger the ones before it built.
set_option maxRecDepth 20000

/--
The whole path, once, with nothing simulated: an identity encrypted under a
passphrase Argon2id stretched, a ledger taken onto a sequencer that checks every
Ed25519 signature, a second node let in by an invite whose realm key travelled in
a sealed box, an entry it wrote, and the same state on both of them.

`Test/Node.lean` does all of this and a great deal more against
`insecureForTests`, which is deliberate — that file is about the protocol, and a
suite that forges trivially still has every size, every tag and every failure
mode of this one. What this adds is that the protocol still works when the
primitives are real, which is a different claim and is why it is not a parameter
of that file.
-/
private def twoNodeSmoke (r : Report) : IO Report := do
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-sodium-{← freshId}"
  try
    let mut r := r
    let log ← Sync.Log.open (Sync.Config.atDir (root / "seq"))
    -- No `testOnly`: this verifier proves something, so `make` has nothing to
    -- refuse. That argument exists for the suite that does not.
    let seq ← Sync.Node.make log (Sync.Verifier.ofSuite suite)
    let a ← makePeer root "alice" seq
    let b ← makePeer root "bob" seq
    r := checkEq r "a member id is the hex of an Ed25519 public key"
      a.identity.id (toHex a.identity.signPk)
    r := checkEq r "which is 64 hex characters" a.identity.id.length Sync.keyHexWidth
    r := check r "two nodes are two identities" (a.identity.id != b.identity.id)
    let reopened ← Node.Identity.load suite (Node.Identity.pathIn a.ctx.cfg) "pass-alice"
    r := checkEq r "an identity file opens under the passphrase it was stretched from"
      reopened.id a.identity.id
    r := check r "and not under another one"
      (← (do discard <| Node.Identity.load suite (Node.Identity.pathIn a.ctx.cfg) "wrong"
             pure false) <|> pure true)

    let sessionA ← Node.initAsAdmin a.ctx suite a.keys a.transport "test:in-process" "home"
    r := checkEq r "taking a ledger onto a sequencer puts the entry it begins with there"
      (← Node.remoteHead a.ctx).seq 1
    r := checkEq r "signed by this node, with nothing of it left waiting"
      (← Node.pendingCount a.ctx) 0

    let bank : Account := { id := ⟨"acc-bank"⟩, name := "Assets.Bank.Main", kind := .asset }
    let weekend : Budget :=
      { id := ⟨"b-weekend"⟩, name := "Weekend", note := none, closed := false }
    discard <| a.ctx.commit "test"
      [.putAccount bank, .openBudget weekend { id := ⟨"acc-weekend"⟩, name := "Weekend",
                                               kind := .equity }]
    let pushed ← Node.push sessionA
    r := checkEq r "a commit made afterwards is one more entry, sealed and signed" pushed.pushed 1
    r := checkEq r "with nothing refused" pushed.blocked none

    let link ← Node.invite sessionA Realm.selfId.val (← aWeekFromNow)
    let some inv := Node.readInvite? link
      | throw <| IO.userError "the invite link does not read back"
    let sessionB ← Node.join b.ctx suite b.keys b.transport "test:in-process" inv
    r := check r "redeeming an invite leaves the joiner holding the realm key it wrapped"
      ((← Node.Keys.latest b.keys inv.realm).isSome)
    discard <| Node.pull sessionA
    let bobId : MemberId := ⟨b.identity.id⟩
    r := checkEq r "and the inviter's books say who arrived"
      (((← a.ctx.state.get).member? bobId).map (·.name)) (some "bob")

    let bobsPurse := ((← b.ctx.state.get).accountByNameIn? Realm.selfId "Members.bob").map (·.id)
    let contribution : Transaction :=
      { id := ⟨"tx-bob-share"⟩, date := (Date.ofIso? "2026-05-02").getD default,
        narration := "bob puts in his half",
        postings := [{ account := bobsPurse.getD ⟨""⟩, amount := ⟨Commodity.eur, -4000⟩ },
                     { account := ⟨"acc-weekend"⟩, amount := ⟨Commodity.eur, 4000⟩ }] }
    discard <| b.ctx.commit "test" [.putTransaction contribution]
    let contributed ← Node.push sessionB
    r := checkEq r "the joiner's own entry is accepted, signed by the key it joined with"
      contributed.pushed 1
    r := checkEq r "with nothing refused" contributed.blocked none
    let seen ← Node.pull sessionA
    r := checkEq r "and reaches the other node, which could open it" seen.applied 1

    r := check r "the two nodes hold the same state"
      ((← a.ctx.state.get) == (← b.ctx.state.get))
    r := checkEq r "down to the bytes a checkpoint would commit to"
      (Encode.hashState (← b.ctx.state.get)) (Encode.hashState (← a.ctx.state.get))
    return r
  finally
    IO.FS.removeDirAll root <|> pure ()

/-- Everything this file checks. -/
def cryptoTests (r : Report) : IO Report := do
  let r ← primitiveTests r
  twoNodeSmoke r
