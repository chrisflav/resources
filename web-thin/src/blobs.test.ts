/**
 * Fetching a receipt, against bytes sealed the way a node seals them.
 *
 * There are no conformance vectors for a blob — the vectors are about `step`,
 * and a blob never reaches it — so what these tests do is the next best thing:
 * they build a ciphertext exactly as `Resources/Node/Blobs.lean`'s `put`
 * builds one, out of the same three framings, and ask `fetchBlob` to open it.
 * A framing that drifted from the Lean source would fail here rather than in a
 * browser looking at a receipt nobody can read.
 */

import sodium from 'libsodium-wrappers-sumo'
import { beforeAll, describe, expect, it } from 'vitest'
import { concat, toBase64, toHex, utf8 } from './bytes'
import { blobAd, blobKeyAd, blobNonce, fetchBlob, readWrapped } from './blobs'
import { generateIdentity, generateRealmKey, randomBytes, ready, sealPart, sha256Hex } from './crypto'
import type { Sequencer } from './sequencer'
import type { RealmSession } from './sync'
import type { Attachment } from './types'

const ledger = 'led-1'
const realm = 'realm-1'
const generation = 3

/** A file sealed and "uploaded" the way `Blobs.put` does it. */
function upload(
  realmKey: Uint8Array,
  plain: Uint8Array,
): { file: Attachment; body: Uint8Array } {
  const sha = sha256Hex(plain)
  const blobKey = randomBytes(32)
  const nonce = blobNonce(blobKey, sha)
  const body = concat(
    nonce,
    sodium.crypto_aead_xchacha20poly1305_ietf_encrypt(
      plain,
      blobAd(ledger, realm, generation, sha),
      null,
      nonce,
      blobKey,
    ),
  )
  const wrapped = sealPart(realmKey, blobKeyAd(ledger, realm, generation, sha), blobKey)
  return {
    body,
    file: {
      sha256: sha,
      mime: 'image/jpeg',
      bytes: plain.length,
      origName: 'till.jpg',
      createdAt: '2026-03-09T10:00:00',
      cipherHash: sha256Hex(body),
      wrappedKey: `${realm}:${generation}:${toBase64(wrapped)}`,
    },
  }
}

/** A session that holds one realm key and a sequencer that holds one blob. */
function sessionFor(
  realmKey: Uint8Array,
  hash: string,
  body: Uint8Array | null,
): { session: RealmSession; fetches: () => number } {
  let fetches = 0
  const seq = {
    blob: async (_ledger: string, h: string) => {
      fetches++
      return h === hash ? body : null
    },
  } as unknown as Sequencer
  return {
    session: {
      seq,
      identity: generateIdentity(),
      ledger,
      realm,
      keys: new Map([[generation, realmKey]]),
      trustedInviter: null,
    },
    fetches: () => fetches,
  }
}

beforeAll(async () => {
  await ready()
})

describe('a wrapped key', () => {
  it('reads back what a node wrote', () => {
    const w = readWrapped('realm-1:7:AAEC')
    expect(w).not.toBeNull()
    expect(w?.realm).toBe('realm-1')
    expect(w?.generation).toBe(7)
    expect(toHex(w?.sealed ?? new Uint8Array())).toBe('000102')
  })

  it('keeps a realm id that contains a colon, because base64 carries none', () => {
    const w = readWrapped('a:b:2:AAEC')
    expect(w?.realm).toBe('a:b')
    expect(w?.generation).toBe(2)
  })

  it('refuses what is not one', () => {
    expect(readWrapped('realm-1:AAEC')).toBeNull()
    expect(readWrapped('realm-1:later:AAEC')).toBeNull()
  })
})

describe('a blob nonce', () => {
  it('is derived, so sealing the same file twice gives the same bytes', () => {
    const key = randomBytes(32)
    expect(toHex(blobNonce(key, 'aabbcc'))).toBe(toHex(blobNonce(key, 'aabbcc')))
    expect(blobNonce(key, 'aabbcc')).toHaveLength(24)
    expect(toHex(blobNonce(key, 'aabbcc'))).not.toBe(toHex(blobNonce(key, 'ddeeff')))
    expect(toHex(blobNonce(key, 'aabbcc'))).not.toBe(toHex(blobNonce(randomBytes(32), 'aabbcc')))
  })
})

describe('fetching a receipt', () => {
  it('opens what a node sealed, and fetches it once', async () => {
    const realmKey = generateRealmKey()
    const plain = utf8('the scan of a hut receipt')
    const { file, body } = upload(realmKey, plain)
    const { session, fetches } = sessionFor(realmKey, file.cipherHash ?? '', body)

    expect(toHex(await fetchBlob(session, file))).toBe(toHex(plain))
    // The second read is the cache, not the sequencer.
    expect(toHex(await fetchBlob(session, file))).toBe(toHex(plain))
    expect(fetches()).toBe(1)
  })

  it('says so when the file was never uploaded', async () => {
    const realmKey = generateRealmKey()
    const { file } = upload(realmKey, utf8('never sent anywhere'))
    const local = { ...file, cipherHash: null, wrappedKey: null }
    const { session } = sessionFor(realmKey, '', null)
    await expect(fetchBlob(session, local)).rejects.toThrow('never been uploaded')
  })

  it('refuses bytes that are not the ones the ledger names', async () => {
    const realmKey = generateRealmKey()
    const { file, body } = upload(realmKey, utf8('a receipt that arrives corrupted'))
    const bent = body.slice()
    bent[bent.length - 1] ^= 1
    const { session } = sessionFor(realmKey, file.cipherHash ?? '', bent)
    await expect(fetchBlob(session, file)).rejects.toThrow('not the ones the ledger names')
  })

  it('refuses a key sealed to a realm this member does not hold', async () => {
    const realmKey = generateRealmKey()
    const { file, body } = upload(realmKey, utf8('a receipt filed in another realm'))
    const elsewhere = { ...file, wrappedKey: `other:${generation}:AAEC` }
    const { session } = sessionFor(realmKey, file.cipherHash ?? '', body)
    await expect(fetchBlob(session, elsewhere)).rejects.toThrow('sealed to other')
  })

  it('refuses a key sealed under a generation this member does not hold', async () => {
    const realmKey = generateRealmKey()
    const { file, body } = upload(realmKey, utf8('a receipt from before a re-key'))
    const older = { ...file, wrappedKey: `${realm}:1:AAEC` }
    const { session } = sessionFor(realmKey, file.cipherHash ?? '', body)
    await expect(fetchBlob(session, older)).rejects.toThrow('generation 1')
  })

  it('refuses to open under the wrong realm key', async () => {
    const realmKey = generateRealmKey()
    const { file, body } = upload(realmKey, utf8('a receipt sealed to somebody else'))
    const { session } = sessionFor(generateRealmKey(), file.cipherHash ?? '', body)
    await expect(fetchBlob(session, file)).rejects.toThrow('does not open under the key you hold')
  })

  it('says so when the sequencer has lost the bytes', async () => {
    const realmKey = generateRealmKey()
    const { file } = upload(realmKey, utf8('a receipt the sequencer forgot'))
    const { session } = sessionFor(realmKey, 'some other hash', new Uint8Array())
    await expect(fetchBlob(session, file)).rejects.toThrow('does not hold this receipt')
  })
})
