/**
 * Fetching a receipt, and opening it.
 *
 * A receipt is too big for the order, so the order carries its hash and the
 * bytes go to the sequencer — which stores them without being able to read
 * them. Three names are in play and they are not the same name:
 *
 * - `sha256` is the hash of the *plaintext*. It is what the ledger calls the
 *   file and what a transaction attaches.
 * - `cipherHash` is the hash of the *ciphertext*. It is what the sequencer
 *   files the bytes under, because it is the only one a server that cannot
 *   decrypt can check for itself.
 * - `wrappedKey` is the file's own key, sealed under a realm key, written down
 *   as `realm ':' generation ':' base64(nonce ++ sealed)`.
 *
 * All three arrive in the order, inside the `Attachment` that `registerBlob`
 * wrote; nothing here is taken from the server. The bytes are fetched on first
 * use, so a client that never opens a receipt never downloads one.
 *
 * This is `Resources/Node/Blobs.lean`'s `get?`, with the same checks in the
 * same order: the ciphertext against the hash the metadata names, the key
 * against the additional data it was sealed under, and the plaintext against
 * the hash the ledger calls the file. A sequencer that hands back the wrong
 * bytes is caught at one of the three, and what is shown is never something
 * the server chose.
 */

import { concat, fromBase64, seg, segNat, segStr } from './bytes'
import { openPart, sha256, sha256Hex } from './crypto'
import type { RealmSession } from './sync'
import type { Attachment } from './types'

/** The domain a blob's ciphertext is bound to. */
export const blobTag = 'resources/blob/v1'

/** The domain a blob's key is sealed under. */
export const blobKeyTag = 'resources/blob-key/v1'

/** The domain a blob's nonce is derived under. */
export const blobNonceTag = 'resources/blob-nonce/v1'

/**
 * The additional data a blob's bytes are sealed under.
 *
 * It names the plaintext's hash, so the file cannot be moved onto another
 * name, and the realm and generation, so it cannot be replayed under a key
 * that has been rotated away.
 */
export function blobAd(
  ledger: string,
  realm: string,
  generation: number,
  sha: string,
): Uint8Array {
  return concat(
    segStr(blobTag),
    segStr(ledger),
    segStr(realm),
    segNat(generation),
    segStr(sha),
  )
}

/** The additional data a blob's key is sealed under: the same five segments, another tag. */
export function blobKeyAd(
  ledger: string,
  realm: string,
  generation: number,
  sha: string,
): Uint8Array {
  return concat(
    segStr(blobKeyTag),
    segStr(ledger),
    segStr(realm),
    segNat(generation),
    segStr(sha),
  )
}

/**
 * The nonce a blob's bytes are sealed under: derived from its own key and its
 * plaintext hash rather than drawn at random, and truncated to 24 bytes.
 *
 * A nonce must never repeat under one key, and this one cannot: the key is
 * fresh for that one file and is used for nothing else. What deriving it buys
 * is that sealing the same file twice gives the same ciphertext, so an upload
 * that failed can be made again under the name the ledger already recorded.
 */
export function blobNonce(blobKey: Uint8Array, sha: string): Uint8Array {
  return sha256(concat(segStr(blobNonceTag), seg(blobKey), segStr(sha))).slice(0, 24)
}

/** What `Attachment.wrappedKey` says: which key sealed the file's own key, and the seal. */
export interface WrappedKey {
  realm: string
  generation: number
  /** `nonce ++ sealed`, as `openPart` wants it. */
  sealed: Uint8Array
}

/**
 * Reads `realm ':' generation ':' base64`.
 *
 * The realm comes first and the bytes last because base64 carries no colon: a
 * realm id that contained one is still read back whole, which is why this
 * splits from the right rather than from the left.
 */
export function readWrapped(s: string): WrappedKey | null {
  const parts = s.split(':')
  if (parts.length < 3) return null
  const sealed = parts[parts.length - 1]
  const digits = parts[parts.length - 2]
  if (!/^\d+$/.test(digits)) return null
  const generation = Number(digits)
  const realm = parts.slice(0, parts.length - 2).join(':')
  try {
    return { realm, generation, sealed: fromBase64(sealed) }
  } catch {
    return null
  }
}

/** Why a receipt could not be shown. The message is meant to be read by a person. */
export class BlobError extends Error {}

/** The plaintext of every blob opened in this tab, by the hash the ledger calls it. */
const cache = new Map<string, Uint8Array>()

/**
 * Fetches a file's ciphertext and opens it.
 *
 * Every refusal names the step that refused, because the four of them are four
 * different situations: a file that was never uploaded, a key sealed to a realm
 * this member does not hold, a sequencer that has lost the bytes, and bytes
 * that are not the ones the ledger recorded.
 */
export async function fetchBlob(session: RealmSession, file: Attachment): Promise<Uint8Array> {
  const held = cache.get(file.sha256)
  if (held !== undefined) return held

  if (file.cipherHash === null || file.wrappedKey === null) {
    throw new BlobError('this receipt has never been uploaded, so there is nothing to fetch')
  }
  const wrapped = readWrapped(file.wrappedKey)
  if (wrapped === null) throw new BlobError('this receipt’s key is not written down properly')
  // A node wraps a blob key under the realm it filed the receipt in, which is
  // not always the realm the transaction ended up in; this client holds one
  // key, so it says which one it would have needed rather than failing to
  // decrypt something.
  if (wrapped.realm !== session.realm) {
    throw new BlobError(`this receipt is sealed to ${wrapped.realm}, which you hold no key for`)
  }
  const key = session.keys.get(wrapped.generation)
  if (key === undefined) {
    throw new BlobError(
      `this receipt is sealed under generation ${wrapped.generation}, ` +
        'which you hold no key for',
    )
  }

  const body = await session.seq.blob(session.ledger, file.cipherHash)
  if (body === null) throw new BlobError('the sequencer does not hold this receipt')
  if (sha256Hex(body) !== file.cipherHash) {
    throw new BlobError('the bytes that came back are not the ones the ledger names')
  }

  const ad = { ledger: session.ledger, realm: wrapped.realm, generation: wrapped.generation }
  let plain: Uint8Array
  try {
    const keyAd = blobKeyAd(ad.ledger, ad.realm, ad.generation, file.sha256)
    const blobKey = openPart(key, keyAd, wrapped.sealed)
    plain = openPart(blobKey, blobAd(ad.ledger, ad.realm, ad.generation, file.sha256), body)
  } catch {
    throw new BlobError('this receipt does not open under the key you hold')
  }
  if (sha256Hex(plain) !== file.sha256) {
    throw new BlobError('what came out is not the file the ledger recorded')
  }

  cache.set(file.sha256, plain)
  return plain
}
