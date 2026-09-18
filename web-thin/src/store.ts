/**
 * Where the browser keeps an identity.
 *
 * Two places, and the difference is the whole point of having both.
 *
 * `localStorage`, under a key derived from a passphrase the person chooses on
 * first use: the identity survives closing the tab, and what is stored is
 * useless without the passphrase.
 *
 * `sessionStorage`, unencrypted, for a one-off guest who is not going to invent
 * a passphrase for a weekend in a hut. It is the weaker option and it is named
 * as such here and in the README: anything that can read the page can read the
 * secret keys, and they are gone when the tab closes.
 *
 * Every accessor is wrapped, because a private window, cleared site data or a
 * blocked origin makes `localStorage` throw rather than return nothing.
 */

import { decryptIdentity, encryptIdentity } from './crypto'
import type { Identity, StoredIdentity } from './crypto'

const IDENTITY_KEY = 'resources.thin.identity'
const GUEST_KEY = 'resources.thin.guest'
const REALM_KEY = 'resources.thin.realm'

/**
 * Which realm of which ledger this browser is looking at, and the two things it
 * pinned when it accepted the link.
 *
 * `inviterSignPk` is the member id of the admin who made the invite. It is the
 * only key a newcomer has any reason to trust before they have replayed a
 * single entry, so it is what makes the first grant and the first checkpoint
 * something other than the server's word.
 *
 * `keyHash` is the SHA-256 of the realm key at `generation`, and it is what
 * catches a sequencer that seals a key of its own choosing to this member:
 * `crypto_box_seal` is anonymous, so without it the realm key is whatever the
 * server says it is.
 */
export interface RealmRef {
  sequencer: string
  ledger: string
  realm: string
  /** The inviter's signing key, hex, pinned from the link. */
  inviterSignPk: string
  /** The generation `keyHash` speaks about. */
  generation: number
  /** SHA-256 of the realm key at `generation`, hex. */
  keyHash: string
  /**
   * `genesisFingerprint` of entry 1 of the order this browser joined, or empty.
   *
   * Empty means the link said `none` — there was no entry to name when it was
   * written — and this browser has nothing to compare against. A digest is
   * compared on every session open, because the fold accepts a genesis on its
   * author's signature alone and that proves only that some member wrote it.
   *
   * It does not stay empty: the first fold that starts from nothing and reaches
   * position 1 writes what it found there back here, through
   * `noteGenesisHash`, and every later cold open is checked against it.
   */
  genesisHash: string
  /**
   * The highest key generation this browser has seen each member publish.
   *
   * A member's agreement key is signed by them at a generation, and the
   * generation only goes up — but every triple `(boxPk, signature, generation)`
   * a member ever published stays valid on its own terms, so a sequencer can
   * serve an *old* one consistently and a client with no memory will seal the
   * realm key to a public half whose secret has since been replaced. The
   * sequencer refuses a lower generation; this is the same refusal made by the
   * side that does not have to be trusted.
   */
  keyGenerations: Record<string, number>
}

function readLocal(key: string): string | null {
  try {
    return localStorage.getItem(key)
  } catch {
    return null
  }
}

function writeLocal(key: string, value: string | null): void {
  try {
    if (value === null) localStorage.removeItem(key)
    else localStorage.setItem(key, value)
  } catch {
    /* private browsing; the session simply does not outlive the tab */
  }
}

function readSession(key: string): string | null {
  try {
    return sessionStorage.getItem(key)
  } catch {
    return null
  }
}

function writeSession(key: string, value: string | null): void {
  try {
    if (value === null) sessionStorage.removeItem(key)
    else sessionStorage.setItem(key, value)
  } catch {
    /* nothing to do: the guest simply has to accept the invite again */
  }
}

/** Whether a passphrase-protected identity is waiting in this browser. */
export function hasStoredIdentity(): boolean {
  return readLocal(IDENTITY_KEY) !== null
}

/** Whether an unencrypted guest identity is alive in this tab. */
export function hasGuestIdentity(): boolean {
  return readSession(GUEST_KEY) !== null
}

/**
 * Stores an identity under a passphrase.
 *
 * Deliberately not idempotent about what is already there: replacing an
 * identity throws away the only copy of a secret key, and the grants on the old
 * realm are sealed to a public key whose secret half is then gone. `App` asks
 * before calling this when `hasStoredIdentity()` is true, and `forgetIdentity`
 * is the deliberate way back.
 */
export function saveIdentity(i: Identity, passphrase: string): void {
  writeLocal(IDENTITY_KEY, JSON.stringify(encryptIdentity(i, passphrase)))
}

/** Recovers the stored identity. Throws when the passphrase is wrong. */
export function loadIdentity(passphrase: string): Identity {
  const raw = readLocal(IDENTITY_KEY)
  if (raw === null) throw new Error('there is no identity stored in this browser')
  return decryptIdentity(JSON.parse(raw) as StoredIdentity, passphrase)
}

/** Forgets the stored identity. */
export function forgetIdentity(): void {
  writeLocal(IDENTITY_KEY, null)
  writeSession(GUEST_KEY, null)
}

/** Stores an identity for this tab only, in the clear. The weaker option. */
export function saveGuestIdentity(i: Identity): void {
  writeSession(
    GUEST_KEY,
    JSON.stringify({
      id: i.id,
      signPk: [...i.signPk],
      signSk: [...i.signSk],
      boxPk: [...i.boxPk],
      boxSk: [...i.boxSk],
    }),
  )
}

/** Recovers this tab's guest identity, or `null` when there is none. */
export function loadGuestIdentity(): Identity | null {
  const raw = readSession(GUEST_KEY)
  if (raw === null) return null
  const j = JSON.parse(raw) as {
    id: string
    signPk: number[]
    signSk: number[]
    boxPk: number[]
    boxSk: number[]
  }
  return {
    id: j.id,
    signPk: Uint8Array.from(j.signPk),
    signSk: Uint8Array.from(j.signSk),
    boxPk: Uint8Array.from(j.boxPk),
    boxSk: Uint8Array.from(j.boxSk),
  }
}

/** Remembers which realm this browser is looking at. */
export function saveRealmRef(ref: RealmRef): void {
  writeLocal(REALM_KEY, JSON.stringify(ref))
  writeSession(REALM_KEY, JSON.stringify(ref))
}

/**
 * The realm this browser was last looking at, if any.
 *
 * The two youngest fields are filled in rather than required: a ref written
 * before they existed is a browser that has joined already, and refusing to read
 * it would lock somebody out of their own ledger over a field they never had.
 * An absent `genesisHash` is "this browser cannot say", which is exactly what an
 * older join knew, and an absent `keyGenerations` is a high-water mark of
 * nothing, which is where every browser starts.
 */
export function loadRealmRef(): RealmRef | null {
  const raw = readSession(REALM_KEY) ?? readLocal(REALM_KEY)
  if (raw === null) return null
  try {
    const ref = JSON.parse(raw) as RealmRef
    return {
      ...ref,
      genesisHash: ref.genesisHash ?? '',
      keyGenerations: ref.keyGenerations ?? {},
    }
  } catch {
    return null
  }
}

/**
 * Writes down the entry this browser's order begins with, once.
 *
 * Trust on first use, and the same backfill `Node/Sync.lean`'s `noteProgress`
 * makes: a node that was never told what its order begins with writes down the
 * first entry 1 it folds and is pinned to it from then on. A link that said
 * `none` had no entry to name — there was none yet when it was written — and
 * without this the browser that joined on it re-derives its whole state from an
 * unchecked entry 1 on every cold open, for ever, which is the door the
 * positional-genesis rule leaves open: a genesis is accepted by the fold on its
 * author's signature alone.
 *
 * Never overwritten, because a digest already here is the order this browser
 * agreed to read and a sequencer serving a second chain is exactly what it is
 * against. The window it leaves is the one fold between joining on such a link
 * and seeing an entry 1, which is the window the node leaves too.
 */
export function noteGenesisHash(fingerprint: string): void {
  if (fingerprint === '') return
  const ref = loadRealmRef()
  if (ref === null || ref.genesisHash !== '') return
  saveRealmRef({ ...ref, genesisHash: fingerprint })
}

/**
 * The highest generation this browser has seen `member` publish a key at.
 *
 * Zero when it has seen none, which is also the generation every key published
 * before the field existed carries — so a first sighting is never a refusal.
 */
export function seenKeyGeneration(member: string): number {
  const ref = loadRealmRef()
  if (ref === null) return 0
  return ref.keyGenerations[member] ?? 0
}

/**
 * Remembers a member's key generation, and never moves one backwards.
 *
 * Called only after the member's own signature over `memberBytes` at that
 * generation has been checked, so what is remembered is something they said.
 */
export function noteKeyGeneration(member: string, generation: number): void {
  const ref = loadRealmRef()
  if (ref === null) return
  if ((ref.keyGenerations[member] ?? 0) >= generation) return
  saveRealmRef({ ...ref, keyGenerations: { ...ref.keyGenerations, [member]: generation } })
}
