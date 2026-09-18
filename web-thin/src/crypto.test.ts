/**
 * The primitives, against libsodium's own round trips, and every canonical byte
 * string of protocol v2 against the literals `Test/Sync.lean` pins.
 *
 * Those literals are the interface a client in another language has to
 * reproduce exactly, and a mistake in one of them shows up as "the signature
 * does not verify" with nothing to say why. Everything else here proves the
 * framings bind what they claim to bind: a part sealed for one realm does not
 * open under another's additional data, and a signature over one envelope does
 * not verify over a different one.
 */

import { beforeAll, describe, expect, it } from 'vitest'
import { fromBase64, fromHex, toHex, utf8 } from './bytes'
import {
  challengeBytes,
  checkpointBytes,
  decryptIdentity,
  encryptIdentity,
  envelopeHash,
  generateIdentity,
  generateRealmKey,
  grantBytes,
  hashBytes,
  inviteKeys,
  joinProofBytes,
  memberBytes,
  openPart,
  partAd,
  publicOf,
  randomBytes,
  ready,
  sealPart,
  sha256Hex,
  signBoxPk,
  signChallenge,
  signEnvelope,
  signGrant,
  signJoinProof,
  signingBytes,
  unwrapKey,
  verifyEnvelope,
  verifySigned,
  wrapKey,
} from './crypto'
import type { Envelope } from './crypto'
import sodium from 'libsodium-wrappers-sumo'

beforeAll(async () => {
  await ready()
})

describe('identity', () => {
  it('names a member by the hex of their signing key', () => {
    const i = generateIdentity()
    expect(i.id).toBe(toHex(i.signPk))
    expect(i.id).toHaveLength(64)
    expect(i.signSk).toHaveLength(64)
    expect(i.boxPk).toHaveLength(32)
    expect(i.boxSk).toHaveLength(32)
    expect(publicOf(i)).toEqual({ id: i.id, signPk: toHex(i.signPk), boxPk: toHex(i.boxPk) })
  })

  it('survives a round trip through a passphrase, and only that passphrase', () => {
    const i = generateIdentity()
    const stored = encryptIdentity(i, 'a hut in the Valais')
    expect(stored.secret).not.toContain(toHex(i.signSk))
    const back = decryptIdentity(stored, 'a hut in the Valais')
    expect(toHex(back.signSk)).toBe(toHex(i.signSk))
    expect(toHex(back.boxSk)).toBe(toHex(i.boxSk))
    expect(back.id).toBe(i.id)
    expect(() => decryptIdentity(stored, 'a hut in the Alps')).toThrow()
  })

  it('is written in the shape the node writes identity.json in', () => {
    // `Resources/Node/Identity.lean`: `{ v, id, signPk, boxPk, kdf: { alg, ops,
    // mem, salt }, nonce, secret }`, the two public keys and the id as hex and
    // the salt, the nonce and the ciphertext as base64. "The same file shape on
    // the node and in the browser" is what lets an identity move between them.
    const i = generateIdentity()
    const stored = encryptIdentity(i, 'a hut in the Valais')
    expect(Object.keys(stored).sort()).toEqual(
      ['boxPk', 'id', 'kdf', 'nonce', 'secret', 'signPk', 'v'].sort(),
    )
    expect(stored.v).toBe(1)
    expect(stored.id).toBe(toHex(i.signPk))
    expect(stored.signPk).toBe(toHex(i.signPk))
    expect(stored.boxPk).toBe(toHex(i.boxPk))
    expect(stored.kdf.alg).toBe('argon2id')
    expect(Object.keys(stored.kdf).sort()).toEqual(['alg', 'mem', 'ops', 'salt'])
    // Base64, not hex: every one of the three carries a character hex has not.
    for (const field of [stored.kdf.salt, stored.nonce, stored.secret]) {
      expect(field).toMatch(/^[A-Za-z0-9+/]+=*$/)
    }
    expect(fromBase64(stored.kdf.salt)).toHaveLength(
      sodium.crypto_pwhash_SALTBYTES as unknown as number,
    )
    expect(fromBase64(stored.nonce)).toHaveLength(24)
  })

  it('is stretched at the moderate limits, and records which they were', () => {
    const stored = encryptIdentity(generateIdentity(), 'a hut in the Valais')
    expect(stored.kdf.ops).toBe(sodium.crypto_pwhash_OPSLIMIT_MODERATE)
    expect(stored.kdf.mem).toBe(sodium.crypto_pwhash_MEMLIMIT_MODERATE)
  })

  it('refuses a record that has been tampered with', () => {
    const i = generateIdentity()
    const stored = encryptIdentity(i, 'a hut in the Valais')
    const pass = 'a hut in the Valais'
    // An id that is not the hex of the signing key it is filed under: the node's
    // loader refuses it, and so does this.
    expect(() => decryptIdentity({ ...stored, id: 'ff'.repeat(32) }, pass)).toThrow(
      /not its signing key/,
    )
    // A memory limit chosen by whoever could rewrite `localStorage`.
    expect(() =>
      decryptIdentity({ ...stored, kdf: { ...stored.kdf, mem: 8 * 1024 * 1024 * 1024 } }, pass),
    ).toThrow(/limits outside what this client will run/)
    expect(() =>
      decryptIdentity({ ...stored, kdf: { ...stored.kdf, ops: 1000000 } }, pass),
    ).toThrow(/limits outside what this client will run/)
    // A version this client does not read, and an algorithm it does not run.
    expect(() =>
      decryptIdentity({ ...stored, v: 2 as unknown as 1 }, pass),
    ).toThrow(/version 2/)
    expect(() =>
      decryptIdentity(
        { ...stored, kdf: { ...stored.kdf, alg: 'scrypt' as unknown as 'argon2id' } },
        pass,
      ),
    ).toThrow(/does not run/)
  })
})

describe('part encryption', () => {
  const ledger = 'home'
  const realm = 'flat'
  const author = 'aa'.repeat(32)

  it('round-trips under the right key and additional data', () => {
    const key = generateRealmKey()
    const plain = utf8('the taxi, 42.50')
    const ad = partAd(ledger, realm, 3, author)
    const sealed = sealPart(key, ad, plain)
    // nonce (24) + ciphertext + tag (16)
    expect(sealed.length).toBe(24 + plain.length + 16)
    expect(toHex(openPart(key, ad, sealed))).toBe(toHex(plain))
  })

  it('does not open under another realm, generation, author or key', () => {
    const key = generateRealmKey()
    const ad = partAd(ledger, realm, 3, author)
    const sealed = sealPart(key, ad, utf8('the taxi'))
    expect(() => openPart(key, partAd(ledger, 'other', 3, author), sealed)).toThrow()
    expect(() => openPart(key, partAd(ledger, realm, 4, author), sealed)).toThrow()
    expect(() => openPart(key, partAd('elsewhere', realm, 3, author), sealed)).toThrow()
    expect(() => openPart(key, partAd(ledger, realm, 3, 'bb'.repeat(32)), sealed)).toThrow()
    expect(() => openPart(generateRealmKey(), ad, sealed)).toThrow()
  })

  it('frames the additional data the way the spec says', () => {
    // Built a second time, by hand, from the `seg` rule: the byte length in
    // ASCII decimal, a colon, then the bytes.
    const expected = utf8(
      '17:resources/part/v1' + '4:home' + '4:flat' + '1:3' + `64:${author}`,
    )
    expect(toHex(partAd(ledger, realm, 3, author))).toBe(toHex(expected))
  })
})

describe('envelopes', () => {
  const ciphertext = new Uint8Array([1, 2, 3])
  // `sha256Hex([1,2,3])`, computed once and written out, so that the pinned
  // byte string below is a literal rather than a call to the thing it checks.
  const digest = '039058c6f2c0cb492c533b0a4d14ef77cc0f78abccced5287d84a1a2011cfb81'
  const base: Envelope = {
    ledger: 'home',
    seq: 1,
    prevHash: '',
    author: '',
    parts: [{ realm: 'flat', generation: 0, cipherHash: digest, ciphertext }],
    signature: '',
  }

  it('digests the ciphertext to the hash the part carries', () => {
    expect(sha256Hex(ciphertext)).toBe(digest)
  })

  it('signs over exactly the bytes Sync/Protocol.lean pins', () => {
    // `Test/Sync.lean`: "an envelope's signature covers each part's digest, not
    // its bytes". The author is the empty string here, so the segment is `0:`;
    // in the Lean pin it is a 64-character member id.
    const expected = utf8(
      '29:resources/seq/v2/envelope-sig' +
        '4:home' +
        '1:1' +
        '0:' +
        '0:' +
        '1:1' +
        '4:flat' +
        '1:0' +
        `64:${digest}`,
    )
    expect(toHex(signingBytes(base))).toBe(toHex(expected))
  })

  it('hashes the same fields plus the signature, under the other tag', () => {
    const signed: Envelope = { ...base, signature: 'ab' }
    const expected = utf8(
      '25:resources/seq/v2/envelope' +
        '4:home' +
        '1:1' +
        '0:' +
        '0:' +
        '1:1' +
        '4:flat' +
        '1:0' +
        `64:${digest}` +
        '2:ab',
    )
    expect(toHex(hashBytes(signed))).toBe(toHex(expected))
    expect(envelopeHash(signed)).toBe(sha256Hex(expected))
  })

  it('hashes the same for a reader who was given the bytes and one who was not', () => {
    // The whole of what version 2 bought: the digest travels either way, so a
    // filtered envelope hashes to exactly what the whole one does and a reader
    // who was handed half of it can still check who wrote it.
    const stripped: Envelope = {
      ...base,
      signature: 'ab',
      parts: [{ ...base.parts[0], ciphertext: null }],
    }
    expect(envelopeHash(stripped)).toBe(envelopeHash({ ...base, signature: 'ab' }))
  })

  it('verifies under its own author and not another', () => {
    const me = generateIdentity()
    const you = generateIdentity()
    const e: Envelope = { ...base, author: me.id }
    e.signature = signEnvelope(e, me.signSk)
    expect(verifyEnvelope(e)).toBe(true)
    expect(verifyEnvelope({ ...e, author: you.id })).toBe(false)
    expect(verifyEnvelope({ ...e, seq: 2 })).toBe(false)
    expect(verifyEnvelope({ ...e, ledger: 'elsewhere' })).toBe(false)
    expect(verifyEnvelope({ ...e, signature: 'not hex' })).toBe(false)
    // And the digest is inside the signed bytes, so a part re-pointed at other
    // ciphertext is a signature that no longer holds.
    expect(
      verifyEnvelope({ ...e, parts: [{ ...e.parts[0], cipherHash: 'ff'.repeat(32) }] }),
    ).toBe(false)
  })

  it('still verifies when the ciphertext was stripped from the fetch', () => {
    const me = generateIdentity()
    const e: Envelope = { ...base, author: me.id }
    e.signature = signEnvelope(e, me.signSk)
    expect(verifyEnvelope({ ...e, parts: [{ ...e.parts[0], ciphertext: null }] })).toBe(true)
  })

  it('hashes the author and the signature as well as the signed fields', () => {
    const me = generateIdentity()
    const e: Envelope = { ...base, author: me.id }
    e.signature = signEnvelope(e, me.signSk)
    const h = envelopeHash(e)
    expect(h).toHaveLength(64)
    expect(envelopeHash({ ...e, author: 'ff'.repeat(32) })).not.toBe(h)
    expect(envelopeHash({ ...e, signature: '00'.repeat(64) })).not.toBe(h)
  })

  it('answers a challenge with a signature over the origin and the nonce', () => {
    const me = generateIdentity()
    const origin = 'https://resources.example/seq'
    const sig = signChallenge('beef', origin, me.signSk)
    expect(
      sodium.crypto_sign_verify_detached(
        fromHex(sig)!,
        challengeBytes('beef', origin),
        me.signPk,
      ),
    ).toBe(true)
    // `Test/Sync.lean`: "a challenge names the sequencer it is answered to".
    expect(toHex(challengeBytes('beef', origin))).toBe(
      toHex(utf8(`26:resources/seq/v2/challenge${utf8(origin).length}:${origin}4:beef`)),
    )
    // A signature taken for another sequencer does not open a session here.
    expect(
      sodium.crypto_sign_verify_detached(
        fromHex(sig)!,
        challengeBytes('beef', 'https://evil.example/seq'),
        me.signPk,
      ),
    ).toBe(false)
  })
})

describe('the byte strings a grant and a member key are signed under', () => {
  const bob = 'b'.repeat(64)
  const alice = 'a'.repeat(64)

  it('a grant names realm, generation, member, role and the wrapped key', () => {
    // `Test/Sync.lean`, pinned literal for literal. The wrapped key is
    // segmented as its raw bytes, not as the base64 that carries it.
    expect(toHex(grantBytes('home', 'money', 2, bob, 'viewer', utf8('wk')))).toBe(
      toHex(utf8(`18:resources/grant/v14:home5:money1:264:${bob}6:viewer2:wk`)),
    )
  })

  it("a member's agreement key is signed under their own id, at a generation", () => {
    // `Sync.memberBytes`: the generation sits between the member and the key,
    // and it defaults to zero — which is the number every key published before
    // the field existed was signed under, so an old client and a new one agree.
    expect(toHex(memberBytes('home', alice, 'aabb'))).toBe(
      toHex(utf8(`19:resources/member/v14:home64:${alice}1:04:aabb`)),
    )
    expect(toHex(memberBytes('home', alice, 'aabb', 0))).toBe(
      toHex(memberBytes('home', alice, 'aabb')),
    )
  })

  it('and a rotated key is a different claim, which is the point of the generation', () => {
    // Without it, the first (key, signature) pair stayed a valid self-attestation
    // for ever: a member whose secret half had leaked could publish a second key
    // and an untrusted sequencer could go on serving the first.
    expect(toHex(memberBytes('home', alice, 'aabb', 1))).not.toBe(
      toHex(memberBytes('home', alice, 'aabb', 0)),
    )
    const me = generateIdentity()
    const sig = signBoxPk(me.signSk, 'home', me.id, 'aabb', 3)
    expect(verifySigned(me.id, memberBytes('home', me.id, 'aabb', 3), sig)).toBe(true)
    expect(verifySigned(me.id, memberBytes('home', me.id, 'aabb', 2), sig)).toBe(false)
  })

  it('a join proof covers the ledger, the realm and the joiner', () => {
    const carol = 'c'.repeat(64)
    expect(toHex(joinProofBytes('home', 'money', carol))).toBe(
      toHex(utf8(`17:resources/join/v14:home5:money64:${carol}`)),
    )
  })

  it('a grant this member signed verifies, and one re-pointed does not', () => {
    const me = generateIdentity()
    const wrapped = new Uint8Array([9, 9, 9])
    const sig = signGrant(me.signSk, 'home', 'money', 2, bob, 'viewer', wrapped)
    expect(
      verifySigned(me.id, grantBytes('home', 'money', 2, bob, 'viewer', wrapped), sig),
    ).toBe(true)
    // Another realm, another generation, another member, another role, another
    // key: every one of them is inside the bytes.
    expect(
      verifySigned(me.id, grantBytes('home', 'other', 2, bob, 'viewer', wrapped), sig),
    ).toBe(false)
    expect(
      verifySigned(me.id, grantBytes('home', 'money', 1, bob, 'viewer', wrapped), sig),
    ).toBe(false)
    expect(
      verifySigned(me.id, grantBytes('home', 'money', 2, alice, 'viewer', wrapped), sig),
    ).toBe(false)
    expect(
      verifySigned(me.id, grantBytes('home', 'money', 2, bob, 'admin', wrapped), sig),
    ).toBe(false)
    expect(
      verifySigned(
        me.id,
        grantBytes('home', 'money', 2, bob, 'viewer', new Uint8Array([9, 9, 8])),
        sig,
      ),
    ).toBe(false)
  })

  it("an agreement key is only ever a claim its own signing key made", () => {
    const me = generateIdentity()
    const you = generateIdentity()
    const boxPk = toHex(me.boxPk)
    const sig = signBoxPk(me.signSk, 'home', me.id, boxPk)
    expect(verifySigned(me.id, memberBytes('home', me.id, boxPk), sig)).toBe(true)
    // The server substituting a key it holds is exactly this, and it fails.
    expect(
      verifySigned(me.id, memberBytes('home', me.id, toHex(you.boxPk)), sig),
    ).toBe(false)
    expect(verifySigned(you.id, memberBytes('home', me.id, boxPk), sig)).toBe(false)
  })
})

describe('key wrapping and invites', () => {
  it('seals a realm key to a member and back', () => {
    const me = generateIdentity()
    const key = generateRealmKey()
    const wrapped = wrapKey(key, me.boxPk)
    expect(wrapped.length).toBe(key.length + 48)
    expect(toHex(unwrapKey(wrapped, me.boxPk, me.boxSk))).toBe(toHex(key))
  })

  it('derives both halves of an invite from one secret, as seeds', () => {
    const secret = randomBytes(32)
    const a = inviteKeys(secret)
    const b = inviteKeys(secret)
    expect(toHex(a.boxPk)).toBe(toHex(b.boxPk))
    expect(toHex(a.signPk)).toBe(toHex(b.signPk))
    expect(() => inviteKeys(randomBytes(31))).toThrow()
    // Both are seeds, not secret keys: the inviter's node uploads the public
    // halves `crypto_box_seed_keypair` and `crypto_sign_seed_keypair` give, so
    // taking the secret for an X25519 scalar would name a key nobody stored.
    expect(toHex(a.boxPk)).toBe(toHex(sodium.crypto_box_seed_keypair(secret).publicKey))
    expect(toHex(a.signPk)).toBe(toHex(sodium.crypto_sign_seed_keypair(secret).publicKey))
    expect(toHex(a.boxPk)).not.toBe(toHex(sodium.crypto_scalarmult_base(secret)))
  })

  it('opens the wrapped key with the invite secret and re-seals it to the joiner', () => {
    const secret = randomBytes(32)
    const invite = inviteKeys(secret)
    const realmKey = generateRealmKey()
    const onServer = wrapKey(realmKey, invite.boxPk)
    const joiner = generateIdentity()
    const opened = unwrapKey(onServer, invite.boxPk, invite.boxSk)
    expect(toHex(opened)).toBe(toHex(realmKey))
    const resealed = wrapKey(opened, joiner.boxPk)
    expect(toHex(unwrapKey(resealed, joiner.boxPk, joiner.boxSk))).toBe(toHex(realmKey))
  })

  it('proves the holder of the link is the one joining', () => {
    const secret = randomBytes(32)
    const invite = inviteKeys(secret)
    const joiner = generateIdentity()
    const proof = signJoinProof(invite, 'home', 'flat', joiner.id)
    expect(
      sodium.crypto_sign_verify_detached(
        fromHex(proof)!,
        joinProofBytes('home', 'flat', joiner.id),
        invite.signPk,
      ),
    ).toBe(true)
    // The proof is about this member joining this realm, and nothing else.
    expect(
      sodium.crypto_sign_verify_detached(
        fromHex(proof)!,
        joinProofBytes('home', 'other', joiner.id),
        invite.signPk,
      ),
    ).toBe(false)
  })
})

describe('hashes', () => {
  it('is SHA-256 in lowercase hex', () => {
    expect(sha256Hex(utf8('abc'))).toBe(
      'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad',
    )
    expect(sha256Hex(new Uint8Array())).toBe(
      'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
    )
  })
})

describe('a checkpoint commitment', () => {
  const base = {
    ledger: 'home',
    realm: 'money',
    generation: 1,
    seq: 3,
    stateHash: 'ab',
    headHash: 'cd',
    // The empty snapshot's digest, written out: this block is evaluated when
    // the module loads, and libsodium is not up until `beforeAll`.
    snapshotHash: 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
  }

  it('covers the head and the snapshot it ships with', () => {
    // `Test/Sync.lean`, pinned: the empty snapshot's digest is the last segment.
    expect(toHex(checkpointBytes(base))).toBe(
      toHex(
        utf8(
          `27:resources/seq/v2/checkpoint4:home5:money1:11:32:ab2:cd64:${base.snapshotHash}`,
        ),
      ),
    )
  })

  it('is bound to every field it names', () => {
    const mine = toHex(checkpointBytes(base))
    for (const other of [
      { ...base, ledger: 'elsewhere' },
      { ...base, realm: 'other' },
      { ...base, generation: 2 },
      { ...base, seq: 4 },
      { ...base, stateHash: 'ff' },
      { ...base, headHash: 'ee' },
      { ...base, snapshotHash: 'dd' },
    ]) {
      expect(toHex(checkpointBytes(other))).not.toBe(mine)
    }
  })

  it('is signed by its author and verifies under nobody else', () => {
    const me = generateIdentity()
    const you = generateIdentity()
    const sig = toHex(sodium.crypto_sign_detached(checkpointBytes(base), me.signSk))
    expect(verifySigned(me.id, checkpointBytes(base), sig)).toBe(true)
    expect(verifySigned(you.id, checkpointBytes(base), sig)).toBe(false)
    expect(verifySigned(me.id, checkpointBytes({ ...base, seq: 4 }), sig)).toBe(false)
  })
})
