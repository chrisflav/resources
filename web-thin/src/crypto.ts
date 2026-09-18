/**
 * Keys, envelopes and the byte strings a key signs.
 *
 * The primitives are libsodium's, through `libsodium-wrappers-sumo`: Ed25519
 * for identity, X25519 for agreement, XChaCha20-Poly1305 IETF for the realm
 * key, `crypto_box_seal` for wrapping it, Argon2id for the passphrase and
 * SHA-256 for the chain. Nothing here reimplements a primitive, and nothing
 * here invents a framing: every canonical byte string is built out of `seg`,
 * exactly as `Resources/Sync/Protocol.lean` builds it, so that bytes signed for
 * one purpose can never be replayed as bytes signed for another.
 *
 * `await ready()` before anything else: the WASM module has to be up.
 */

import sodium from 'libsodium-wrappers-sumo'
import { concat, fromBase64, fromHex, seg, segNat, segStr, toBase64, toHex, utf8 } from './bytes'

let started: Promise<void> | null = null

/** Brings the WASM module up. Idempotent, and safe to await from anywhere. */
export function ready(): Promise<void> {
  if (started === null) started = sodium.ready
  return started
}

/** SHA-256, as bytes: what a derived nonce is truncated from. */
export function sha256(bs: Uint8Array): Uint8Array {
  return sodium.crypto_hash_sha256(bs)
}

/** SHA-256, lowercase hex: what a chain hash and a content address are. */
export function sha256Hex(bs: Uint8Array): string {
  return toHex(sha256(bs))
}

/* ------------------------------------------------------------------ */
/* Identity                                                            */
/* ------------------------------------------------------------------ */

/**
 * One member's keys.
 *
 * `id` is the lowercase hex of the Ed25519 public key, which is what a
 * `MemberId` is from phase 3 on, and what the sequencer knows a caller by.
 */
export interface Identity {
  id: string
  signPk: Uint8Array
  signSk: Uint8Array
  boxPk: Uint8Array
  boxSk: Uint8Array
}

/** The public half, which is what a `member` record on the sequencer carries. */
export interface PublicIdentity {
  id: string
  signPk: string
  boxPk: string
}

/** A fresh identity: an Ed25519 pair for signing and an X25519 pair for agreement. */
export function generateIdentity(): Identity {
  const sign = sodium.crypto_sign_keypair()
  const box = sodium.crypto_box_keypair()
  return {
    id: toHex(sign.publicKey),
    signPk: sign.publicKey,
    signSk: sign.privateKey,
    boxPk: box.publicKey,
    boxSk: box.privateKey,
  }
}

/** The public half of an identity. */
export function publicOf(i: Identity): PublicIdentity {
  return { id: i.id, signPk: toHex(i.signPk), boxPk: toHex(i.boxPk) }
}

/* ------------------------------------------------------------------ */
/* The identity at rest                                                */
/* ------------------------------------------------------------------ */

/**
 * An identity as it is stored: public keys in the clear, secret keys under an
 * Argon2id key from a passphrase, with the salt and nonce beside them.
 *
 * `kdf` is recorded rather than assumed, because a stored blob outlives the
 * code that wrote it and "which limits were these" is not a question anybody
 * can answer afterwards.
 */
export interface StoredIdentity {
  v: 1
  id: string
  signPk: string
  boxPk: string
  kdf: { alg: 'argon2id'; ops: number; mem: number; salt: string }
  nonce: string
  secret: string
}

/**
 * The widest Argon2id parameters this client will run.
 *
 * `decryptIdentity` is handed its own stored record, and a stored record is a
 * `localStorage` blob anything that can reach the page can rewrite. A tampered
 * one naming a gigabyte of memory turns unlocking into a crash, so the numbers
 * are bounded the way everything else read off the wire is.
 */
const maxKdfOps = 10
const maxKdfMem = 1024 * 1024 * 1024

/** The additional data the secret keys are sealed under: the identity they are for. */
function identityAd(signPk: string): Uint8Array {
  return concat(segStr('resources/identity/v1'), segStr(signPk))
}

/**
 * Derives the wrapping key for an identity file from a passphrase.
 *
 * MODERATE rather than INTERACTIVE. What is being protected is not a session
 * but a `localStorage` blob that outlives the tab and travels in profile
 * backups, and the cost is paid twice in the life of a browser: once when the
 * identity is written and once when it is unlocked.
 */
export function identityKey(passphrase: string, salt: Uint8Array): Uint8Array {
  return sodium.crypto_pwhash(
    32,
    passphrase,
    salt,
    sodium.crypto_pwhash_OPSLIMIT_MODERATE,
    sodium.crypto_pwhash_MEMLIMIT_MODERATE,
    sodium.crypto_pwhash_ALG_ARGON2ID13,
  )
}

/** Encrypts an identity's secret keys under a passphrase. */
export function encryptIdentity(i: Identity, passphrase: string): StoredIdentity {
  const salt = sodium.randombytes_buf(sodium.crypto_pwhash_SALTBYTES)
  const key = identityKey(passphrase, salt)
  const nonce = sodium.randombytes_buf(24)
  const plain = concat(i.signSk, i.boxSk)
  const sealed = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(
    plain,
    identityAd(toHex(i.signPk)),
    null,
    nonce,
    key,
  )
  // The shape is `Resources/Node/Identity.lean`'s, field for field: the two
  // public keys and the id as hex, the salt, the nonce and the ciphertext as
  // base64, and `alg` naming the algorithm rather than libsodium's constant.
  // That is what makes an identity movable between a node's `identity.json`
  // and this browser, which is the only reason to fix a format at all.
  return {
    v: 1,
    id: i.id,
    signPk: toHex(i.signPk),
    boxPk: toHex(i.boxPk),
    kdf: {
      alg: 'argon2id',
      ops: sodium.crypto_pwhash_OPSLIMIT_MODERATE,
      mem: sodium.crypto_pwhash_MEMLIMIT_MODERATE,
      salt: toBase64(salt),
    },
    nonce: toBase64(nonce),
    secret: toBase64(sealed),
  }
}

/**
 * Recovers an identity from its stored form. Throws when the passphrase is wrong.
 *
 * Everything the record states about itself is checked before it is used. The
 * id has to be the hex of the signing key it is filed under — which is what the
 * node's loader insists on, and what makes "the id" a fact rather than a label
 * — and the KDF parameters have to be ones this client is willing to run.
 */
export function decryptIdentity(stored: StoredIdentity, passphrase: string): Identity {
  if (stored.v !== 1) throw new Error(`this identity is version ${stored.v}, and this client reads 1`)
  const signPk = mustHex(stored.signPk, 'signPk')
  if (stored.id.toLowerCase() !== toHex(signPk)) {
    throw new Error('this identity is filed under an id that is not its signing key')
  }
  if (stored.kdf.alg !== 'argon2id') {
    throw new Error(`this identity was stretched with ${stored.kdf.alg}, which this client does not run`)
  }
  if (
    !Number.isInteger(stored.kdf.ops) ||
    stored.kdf.ops < 1 ||
    stored.kdf.ops > maxKdfOps ||
    !Number.isInteger(stored.kdf.mem) ||
    stored.kdf.mem < 1 ||
    stored.kdf.mem > maxKdfMem
  ) {
    throw new Error('this identity names key-stretching limits outside what this client will run')
  }
  const salt = fromBase64(stored.kdf.salt)
  const nonce = fromBase64(stored.nonce)
  const sealed = fromBase64(stored.secret)
  const key = sodium.crypto_pwhash(
    32,
    passphrase,
    salt,
    stored.kdf.ops,
    stored.kdf.mem,
    sodium.crypto_pwhash_ALG_ARGON2ID13,
  )
  const plain = sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(
    null,
    sealed,
    identityAd(stored.signPk),
    nonce,
    key,
  )
  if (plain.length !== 96) throw new Error('the stored identity is the wrong length')
  const signSk = plain.slice(0, 64)
  const boxSk = plain.slice(64, 96)
  return {
    id: toHex(signPk),
    signPk,
    signSk,
    boxPk: mustHex(stored.boxPk, 'boxPk'),
    boxSk,
  }
}

function mustHex(s: string, what: string): Uint8Array {
  const bs = fromHex(s)
  if (bs === null) throw new Error(`${what} is not hex`)
  return bs
}

/* ------------------------------------------------------------------ */
/* The envelope                                                        */
/* ------------------------------------------------------------------ */

/**
 * One realm's slice of an envelope: `Sync.Part`.
 *
 * `cipherHash` is what the signature and the envelope hash are taken over, so
 * it travels whether or not the ciphertext does. A part the sequencer stripped
 * — because this caller holds no grant on its realm — carries a `null`
 * ciphertext and the digest all the same.
 */
export interface WirePart {
  realm: string
  generation: number
  /** The hex SHA-256 of the ciphertext as its author sealed it. Always present. */
  cipherHash: string
  /** The ciphertext, or `null` for a part whose payload was withheld. */
  ciphertext: Uint8Array | null
}

/** One entry in a ledger's total order: `Sync.Envelope`. */
export interface Envelope {
  ledger: string
  seq: number
  prevHash: string
  author: string
  parts: WirePart[]
  signature: string
}

/** The domain tag under which an envelope's signature is taken. */
export const envelopeSigTag = 'resources/seq/v2/envelope-sig'

/** The domain tag under which an envelope is hashed. */
export const envelopeHashTag = 'resources/seq/v2/envelope'

/** The domain tag under which an authentication challenge is signed. */
export const challengeTag = 'resources/seq/v2/challenge'

/** The domain tag under which a checkpoint commitment is signed. */
export const checkpointTag = 'resources/seq/v2/checkpoint'

/** The domain tag under which a grant is signed by whoever issued it. */
export const grantTag = 'resources/grant/v1'

/** The domain tag under which a member publishes their own agreement key. */
export const memberTag = 'resources/member/v1'

/**
 * The fields both an envelope's signature and its hash are taken over.
 *
 * Version 1 covered each part's *ciphertext*, and a fetch hands back only the
 * parts the caller holds a grant for — so a filtered reader was shown neither
 * the bytes the signature covered nor the bytes the hash digested. Version 2
 * covers `cipherHash` instead, which is the same string for every reader, so
 * anybody who receives an envelope can check who wrote it and recompute where
 * it sits in the chain.
 */
function envelopeCore(e: Envelope, tag: string): Uint8Array {
  return concat(
    segStr(tag),
    segStr(e.ledger),
    segNat(e.seq),
    segStr(e.prevHash),
    segStr(e.author),
    segNat(e.parts.length),
    ...e.parts.map((p) =>
      concat(segStr(p.realm), segNat(p.generation), segStr(p.cipherHash)),
    ),
  )
}

/** The bytes an envelope's signature covers. `Envelope.signingBytes`. */
export function signingBytes(e: Envelope): Uint8Array {
  return envelopeCore(e, envelopeSigTag)
}

/** The bytes `hash` digests: the signed fields, plus the signature. */
export function hashBytes(e: Envelope): Uint8Array {
  return concat(envelopeCore(e, envelopeHashTag), segStr(e.signature))
}

/**
 * `hash(envelope)`: the lowercase hex SHA-256 of `hashBytes`.
 *
 * It is the same value for every reader, because nothing it digests is ever
 * withheld from one. A reader recomputes it rather than believing a server that
 * states it.
 */
export function envelopeHash(e: Envelope): string {
  return sha256Hex(hashBytes(e))
}

/**
 * The bytes a checkpoint's signature covers. `Checkpoint.commitmentBytes`.
 *
 * `headHash` is the hash of the envelope at `seq`, and it is what ties the
 * commitment to the order it speaks about: the first envelope after a
 * checkpoint carries a `prevHash`, and this is the value it has to match.
 * `snapshotHash` ties it to the bytes it ships with — without it the binding
 * rested on a reader decrypting the snapshot and recomputing `stateHash` from
 * it, which nothing forced them to do, so a server could swap the snapshot and
 * keep the signature valid.
 */
export function checkpointBytes(c: {
  ledger: string
  realm: string
  generation: number
  seq: number
  stateHash: string
  headHash: string
  snapshotHash: string
}): Uint8Array {
  return concat(
    segStr(checkpointTag),
    segStr(c.ledger),
    segStr(c.realm),
    segNat(c.generation),
    segNat(c.seq),
    segStr(c.stateHash),
    segStr(c.headHash),
    segStr(c.snapshotHash),
  )
}

/**
 * The bytes whoever issues a grant signs. `Sync.grantBytes`.
 *
 * A grant says "this realm key, at this generation, wrapped for this member, in
 * this role". Every one of those is in here, so a grant cannot be lifted onto
 * another realm, another member, another role or an older generation, and a
 * sequencer that substituted a wrapped key of its own would be signing for
 * somebody whose key it does not hold.
 *
 * The wrapped key is segmented as its raw bytes, not as the base64 that carries
 * it: base64 is not canonical here, and a signature over a non-canonical
 * encoding is a signature two parties can disagree about.
 */
export function grantBytes(
  ledger: string,
  realm: string,
  generation: number,
  member: string,
  role: string,
  wrappedKey: Uint8Array,
): Uint8Array {
  return concat(
    segStr(grantTag),
    segStr(ledger),
    segStr(realm),
    segNat(generation),
    segStr(member),
    segStr(role),
    seg(wrappedKey),
  )
}

/**
 * The bytes a member signs to publish the agreement key realm keys are sealed
 * to. `Sync.memberBytes`.
 *
 * The agreement key used to be whatever the server said it was, so an operator
 * could substitute a key they held and be re-granted every realm on the next
 * rotation. Now the key is only ever a claim its own signing key made, and the
 * signing key *is* the member id.
 *
 * `keyGeneration` is what makes the claim replaceable, and it sits between the
 * member and the key. Without it a member who published a second key — because
 * the secret half of the first had leaked — left the first `(boxPk, signature)`
 * pair a perfectly valid self-attestation for ever, and an untrusted sequencer
 * could go on serving it: the next rotation would seal the realm key to the
 * compromised one, and the member had no way to say "not that one". It defaults
 * to zero, which is the number a member's first key carries, so a client that
 * never rotates signs exactly what it signed before.
 */
export function memberBytes(
  ledger: string,
  member: string,
  boxPk: string,
  keyGeneration = 0,
): Uint8Array {
  return concat(
    segStr(memberTag),
    segStr(ledger),
    segStr(member),
    segStr(String(keyGeneration)),
    segStr(boxPk),
  )
}

/** Signs an envelope; the result is the hex signature it carries. */
export function signEnvelope(e: Envelope, signSk: Uint8Array): string {
  return toHex(sodium.crypto_sign_detached(signingBytes(e), signSk))
}

/**
 * Whether `signature` is a valid signature of `message` under the hex key.
 *
 * Bad hex is a failed check rather than an exception, because a verifier that
 * throws on malformed input is a verifier somebody will wrap in a `try` that
 * swallows a real failure too.
 */
export function verifySigned(pubKeyHex: string, message: Uint8Array, sigHex: string): boolean {
  const key = fromHex(pubKeyHex)
  const sig = fromHex(sigHex)
  if (key === null || sig === null || key.length !== 32 || sig.length !== 64) return false
  try {
    return sodium.crypto_sign_verify_detached(sig, message, key)
  } catch {
    return false
  }
}

/** Whether an envelope's signature verifies under its own author. */
export function verifyEnvelope(e: Envelope): boolean {
  return verifySigned(e.author, signingBytes(e), e.signature)
}

/** Signs a grant, as its issuer. */
export function signGrant(
  signSk: Uint8Array,
  ledger: string,
  realm: string,
  generation: number,
  member: string,
  role: string,
  wrappedKey: Uint8Array,
): string {
  return toHex(
    sodium.crypto_sign_detached(
      grantBytes(ledger, realm, generation, member, role, wrappedKey),
      signSk,
    ),
  )
}

/** Signs an agreement key, as the member it belongs to, at one generation. */
export function signBoxPk(
  signSk: Uint8Array,
  ledger: string,
  member: string,
  boxPk: string,
  keyGeneration = 0,
): string {
  return toHex(
    sodium.crypto_sign_detached(memberBytes(ledger, member, boxPk, keyGeneration), signSk),
  )
}

/**
 * The bytes a key signs to answer a challenge. `Sync.challengeBytes`.
 *
 * The origin is in them because a signature that named no sequencer was valid
 * at every sequencer: anybody who could lure a member to a second instance —
 * and an invite link is a URL, so luring is easy — could relay a challenge from
 * the real one and open a session as them.
 */
export function challengeBytes(nonce: string, origin: string): Uint8Array {
  return concat(segStr(challengeTag), segStr(origin), segStr(nonce))
}

/** Answers a challenge, at the origin the client meant to talk to. */
export function signChallenge(nonce: string, origin: string, signSk: Uint8Array): string {
  return toHex(sodium.crypto_sign_detached(challengeBytes(nonce, origin), signSk))
}

/* ------------------------------------------------------------------ */
/* Part encryption                                                     */
/* ------------------------------------------------------------------ */

/** The domain tag a part's additional data starts with. */
export const partAdTag = 'resources/part/v1'

/**
 * The additional data a part is sealed under.
 *
 * The realm id is inside the plaintext too, so a part cannot be re-labelled;
 * this binds the ciphertext to the ledger, the generation and the author as
 * well, so it cannot be moved between them either.
 */
export function partAd(
  ledger: string,
  realm: string,
  generation: number,
  author: string,
): Uint8Array {
  return concat(
    segStr(partAdTag),
    segStr(ledger),
    segStr(realm),
    segNat(generation),
    segStr(author),
  )
}

/** `nonce (24 random bytes) ++ aead_seal(realmKey, nonce, ad, plaintext)`. */
export function sealPart(
  key: Uint8Array,
  ad: Uint8Array,
  plaintext: Uint8Array,
): Uint8Array {
  const nonce = sodium.randombytes_buf(24)
  const sealed = sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(plaintext, ad, null, nonce, key)
  return concat(nonce, sealed)
}

/** Opens what `sealPart` produced. Throws when the key, the nonce or the ad is wrong. */
export function openPart(key: Uint8Array, ad: Uint8Array, ciphertext: Uint8Array): Uint8Array {
  if (ciphertext.length < 24 + 16) throw new Error('the ciphertext is too short to be a part')
  const nonce = ciphertext.slice(0, 24)
  const body = ciphertext.slice(24)
  return sodium.crypto_aead_xchacha20poly1305_ietf_decrypt(null, body, ad, nonce, key)
}

/**
 * The additional data a checkpoint's snapshot is sealed under.
 *
 * The spec used to fix the framing for a *part* and say only that a snapshot is
 * "the canonical `State` bytes, decrypted"; this was written as the part framing
 * with its own domain tag and the checkpoint's author in the last segment, on
 * the grounds that it is the only shape binding a snapshot to the commitment
 * that announces it. That is what `Resources/Node/Checkpoint.lean` settled on —
 * `snapshotAd`, segment for segment — so it is no longer a guess.
 */
export function snapshotAd(
  ledger: string,
  realm: string,
  generation: number,
  author: string,
): Uint8Array {
  return concat(
    segStr('resources/snapshot/v1'),
    segStr(ledger),
    segStr(realm),
    segNat(generation),
    segStr(author),
  )
}

/* ------------------------------------------------------------------ */
/* Key wrapping                                                        */
/* ------------------------------------------------------------------ */

/** A fresh 32-byte realm key. */
export function generateRealmKey(): Uint8Array {
  return sodium.randombytes_buf(32)
}

/** `crypto_box_seal(realmKey, recipientX25519Pk)`: anonymous, 48 bytes of overhead. */
export function wrapKey(key: Uint8Array, recipientBoxPk: Uint8Array): Uint8Array {
  return sodium.crypto_box_seal(key, recipientBoxPk)
}

/** Opens a wrapped key with the recipient's X25519 pair. */
export function unwrapKey(
  wrapped: Uint8Array,
  boxPk: Uint8Array,
  boxSk: Uint8Array,
): Uint8Array {
  return sodium.crypto_box_seal_open(wrapped, boxPk, boxSk)
}

/* ------------------------------------------------------------------ */
/* Invites                                                             */
/* ------------------------------------------------------------------ */

/** The domain tag a join proof is signed under. */
export const joinTag = 'resources/join/v1'

/**
 * What an invite secret is, on both sides.
 *
 * One 32-byte secret does two jobs: it *seeds* the X25519 pair the realm key
 * was sealed to, and it seeds the Ed25519 pair whose signature proves to the
 * server that the holder of the link is the one joining. Both are seeds rather
 * than secret keys — `crypto_box_seed_keypair` and `crypto_sign_seed_keypair` —
 * which is what the spec settled on and what the inviter's node does, so a link
 * made by one and spent by the other names the same two public keys.
 */
export interface InviteKeys {
  boxPk: Uint8Array
  boxSk: Uint8Array
  signPk: Uint8Array
  signSk: Uint8Array
}

/** Derives both key pairs from an invite secret. */
export function inviteKeys(secret: Uint8Array): InviteKeys {
  if (secret.length !== 32) throw new Error('an invite secret is 32 bytes')
  const sign = sodium.crypto_sign_seed_keypair(secret)
  const box = sodium.crypto_box_seed_keypair(secret)
  return {
    boxPk: box.publicKey,
    boxSk: box.privateKey,
    signPk: sign.publicKey,
    signSk: sign.privateKey,
  }
}

/** The bytes a joiner signs with the invite's own key. */
export function joinProofBytes(ledger: string, realm: string, memberId: string): Uint8Array {
  return concat(segStr(joinTag), segStr(ledger), segStr(realm), segStr(memberId))
}

/** The proof that the holder of the link is the one joining. */
export function signJoinProof(
  keys: InviteKeys,
  ledger: string,
  realm: string,
  memberId: string,
): string {
  return toHex(sodium.crypto_sign_detached(joinProofBytes(ledger, realm, memberId), keys.signSk))
}

/* ------------------------------------------------------------------ */
/* Odds and ends                                                       */
/* ------------------------------------------------------------------ */

/** Random bytes, from libsodium's generator. */
export function randomBytes(n: number): Uint8Array {
  return sodium.randombytes_buf(n)
}

/**
 * A fresh identifier in the shape `Resources.freshId` produces: ten characters
 * of millisecond timestamp and sixteen of randomness, both Crockford base32, so
 * that lexicographic order is chronological order.
 */
export function freshId(): string {
  return base32(BigInt(Date.now()), 10) + base32FromBytes(randomBytes(10))
}

const base32Alphabet = '0123456789ABCDEFGHJKMNPQRSTVWXYZ'

function base32(n: bigint, width: number): string {
  let out = ''
  let v = n
  for (let i = 0; i < width; i++) {
    out = base32Alphabet[Number(v % 32n)] + out
    v /= 32n
  }
  return out
}

function base32FromBytes(bs: Uint8Array): string {
  let n = 0n
  for (const b of bs) n = n * 256n + BigInt(b)
  return base32(n, 16)
}

/** The UTF-8 of a string, re-exported so callers need only this module. */
export { utf8 }
