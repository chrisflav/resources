/**
 * Composing an envelope and reading it back, and every refusal version 2 added.
 *
 * This is the one path that touches everything at once: the operation is
 * encoded, sealed under the realm key with the spec's additional data, signed,
 * and then taken apart again by the same code that reads a stranger's envelope
 * off the sequencer.
 *
 * Most of what is checked is the negative space, because that is where the
 * security review found the client. An envelope whose signature does not
 * verify, whose ciphertext does not hash to the digest the signature covers,
 * whose `seq` skips a position, whose `prevHash` names something else, or whose
 * event id has been applied already: none of them reaches the state, and the
 * first four stop the fold rather than being folded in and mentioned in a table
 * at the bottom of the page.
 */

import { beforeAll, beforeEach, describe, expect, it } from 'vitest'
import sodium from 'libsodium-wrappers-sumo'
import { toHex } from './bytes'
import { encode, stateCodec } from './codec'
import {
  checkpointBytes,
  envelopeHash,
  generateIdentity,
  generateRealmKey,
  ready,
  sealPart,
  sha256Hex,
  signEnvelope,
  snapshotAd,
} from './crypto'
import type { Identity } from './crypto'
import { eur } from './money'
import { Sequencer } from './sequencer'
import type { Checkpoint, FetchedEnvelope, Head } from './sequencer'
import { emptyState, realmAdmins, sortedValues } from './state'
import { loadRealmRef, noteGenesisHash, saveRealmRef } from './store'
import {
  applyTail,
  chooseSnapshot,
  compose,
  gapMessage,
  genesisFingerprint,
  loadRealm,
  pinStillAdmin,
  selfIntroduction,
  trustedAuthor,
} from './sync'
import type { RealmSession } from './sync'
import { selfMemberId } from './types'
import type { Account, Op, State, Transaction } from './types'

const REALM = 'flat'
const day = { year: 2026, month: 3, day: 9 }

beforeAll(async () => {
  await ready()
})

function account(over: Partial<Account> & Pick<Account, 'id' | 'name' | 'kind'>): Account {
  return {
    owner: 'p-me',
    commodity: null,
    iban: null,
    note: null,
    closedOn: null,
    realm: REALM,
    bridgeOf: null,
    posters: [],
    mirrorOf: null,
    ...over,
  }
}

function session(): RealmSession {
  const identity = generateIdentity()
  return {
    seq: new Sequencer(),
    identity,
    ledger: 'home',
    realm: REALM,
    keys: new Map([[0, generateRealmKey()]]),
    trustedInviter: null,
  }
}

/** A realm the composing member may write a cost into. */
function realm(author: string): State {
  const s = emptyState()
  s.realms.set(REALM, { id: REALM, name: 'the flat', members: [[author, 'admin']], generation: 0 })
  s.accounts.set('acc-budget', account({ id: 'acc-budget', name: 'Budget.Hut', kind: 'equity' }))
  s.accounts.set(
    'acc-me',
    account({ id: 'acc-me', name: 'Assets.Purse.Me', kind: 'asset', bridgeOf: author }),
  )
  return s
}

const blank = { party: null, note: null, origin: null, tag: null }

const cost: Transaction = {
  id: 'cost-1',
  date: day,
  payee: 'the hut',
  narration: 'the hut',
  state: 'posted',
  postings: [
    { account: 'acc-budget', amount: { commodity: eur, minor: 10000n }, ...blank },
    { account: 'acc-me', amount: { commodity: eur, minor: -10000n }, ...blank },
  ],
  labels: [],
  source: { kind: 'manual', actor: 'test' },
  attachments: [],
}

const putCost: Op = { tag: 15, kind: 'putTransaction', txn: cost }

const head: Head = { seq: 0, hash: '' }

/** What the sequencer would hand back for an envelope it accepted. */
function fetched(e: ReturnType<typeof compose>['envelope']): FetchedEnvelope {
  return { ...e, hash: envelopeHash(e) }
}

/** The same, with the ciphertext of every part stripped, as a fetch strips it. */
function stripped(e: FetchedEnvelope): FetchedEnvelope {
  return { ...e, parts: e.parts.map((p) => ({ ...p, ciphertext: null })) }
}

describe('compose and read back', () => {
  it('seals one part per operation, digests it, and signs the envelope', () => {
    const s = session()
    const { envelope } = compose(s, 0, [putCost], head)
    expect(envelope.parts).toHaveLength(1)
    expect(envelope.parts[0].realm).toBe(REALM)
    expect(envelope.parts[0].generation).toBe(0)
    // The digest the signature covers is the digest of the bytes that travel.
    expect(envelope.parts[0].cipherHash).toBe(sha256Hex(envelope.parts[0].ciphertext!))
    expect(envelope.seq).toBe(1)
    expect(envelope.prevHash).toBe('')
    expect(envelope.author).toBe(s.identity.id)
    expect(envelope.signature).toHaveLength(128)
  })

  it('applies what it composed, and calls it verified', () => {
    const s = session()
    const { envelope } = compose(s, 0, [putCost], head)
    const out = applyTail(s, realm(s.identity.id), [fetched(envelope)], 0, '')
    expect(out.refused).toBeNull()
    expect(out.events).toHaveLength(1)
    expect(out.events[0]).toMatchObject({ seq: 1, status: 'applied' })
    expect(out.events[0].hash).toBe(envelopeHash(envelope))
    expect(out.verifiedUpTo).toBe(1)
    expect(out.verifiedHash).toBe(envelopeHash(envelope))
    expect(out.state.txns.get('cost-1')?.postings).toHaveLength(2)
  })

  it('applies an operation the interface never offers, because the bytes ask it to', () => {
    const s = session()
    const rotate: Op = { tag: 49, kind: 'rotateRealmKey', realm: REALM }
    const { envelope } = compose(s, 0, [rotate], head)
    const out = applyTail(s, realm(s.identity.id), [fetched(envelope)], 0, '')
    expect(out.events[0].status).toBe('applied')
    expect(out.verifiedUpTo).toBe(1)
    expect(out.state.realms.get(REALM)!.generation).toBe(1)
  })

  it('records an operation it understood and refused as rejected, and carries on', () => {
    const s = session()
    const unbalanced: Op = {
      tag: 15,
      kind: 'putTransaction',
      txn: { ...cost, postings: [cost.postings[0]] },
    }
    const { envelope } = compose(s, 0, [unbalanced], head)
    const out = applyTail(s, realm(s.identity.id), [fetched(envelope)], 0, '')
    expect(out.events[0].status).toBe('rejected')
    expect(out.events[0].detail).toMatch(/does not balance/)
    expect(out.state.txns.size).toBe(0)
    // Rejected is not refused: the chain held, so verification went past it.
    expect(out.refused).toBeNull()
    expect(out.verifiedUpTo).toBe(1)
  })

  it('cannot read a part sealed under a key it does not hold, and verifies it anyway', () => {
    const s = session()
    const { envelope } = compose(s, 0, [putCost], head)
    const stranger: RealmSession = { ...s, keys: new Map([[0, generateRealmKey()]]) }
    const out = applyTail(stranger, realm(s.identity.id), [fetched(envelope)], 0, '')
    expect(out.events[0].status).toBe('unreadable')
    expect(out.state.txns.size).toBe(0)
    // This is the whole of what version 2 bought: the signature and the hash are
    // over the digests, which travel whether or not the payload does.
    expect(out.refused).toBeNull()
    expect(out.verifiedUpTo).toBe(1)
  })

  it('verifies an envelope whose payloads the sequencer stripped', () => {
    const s = session()
    const { envelope } = compose(s, 0, [putCost], head)
    const out = applyTail(s, realm(s.identity.id), [stripped(fetched(envelope))], 0, '')
    expect(out.refused).toBeNull()
    expect(out.verifiedUpTo).toBe(1)
    expect(out.events[0].status).toBe('unreadable')
    // The chain held; the realm still did not. A part of *this* realm that did
    // not arrive is a gap, and a gap is what a checkpoint is asked to cover.
    expect(out.gap).toEqual({ seq: 1, generation: 0 })
  })
})

describe('what stops the fold', () => {
  /** An envelope at `seq`, claiming to follow `prev`. */
  function at(s: RealmSession, seq: number, prev: string, op: Op = putCost): FetchedEnvelope {
    return fetched(compose(s, 0, [op], { seq: seq - 1, hash: prev }).envelope)
  }

  it('refuses a ciphertext that was touched, rather than skipping it', () => {
    const s = session()
    const e = at(s, 1, '')
    e.parts[0].ciphertext![30] ^= 0xff
    const out = applyTail(s, realm(s.identity.id), [e], 0, '')
    expect(out.refused).toMatchObject({ seq: 1 })
    expect(out.refused!.reason).toMatch(/is not the one its digest names/)
    expect(out.verifiedUpTo).toBe(0)
    expect(out.state.txns.size).toBe(0)
  })

  it('refuses a signature that does not verify against its author', () => {
    const s = session()
    const e = at(s, 1, '')
    e.signature = '00'.repeat(64)
    const out = applyTail(s, realm(s.identity.id), [e], 0, '')
    expect(out.refused!.reason).toMatch(/signature does not verify/)
    expect(out.verifiedUpTo).toBe(0)
  })

  it('gets nothing out of an envelope re-signed by somebody else over the same parts', () => {
    const s = session()
    const mallory = generateIdentity()
    const e = at(s, 1, '')
    const forged = { ...e, author: mallory.id }
    forged.signature = signEnvelope(forged, mallory.signSk)
    // The envelope verifies — Mallory really did sign these bytes — and the
    // part inside it does not open, because the additional data a part is
    // sealed under names its author. Lifting somebody's ciphertext into an
    // envelope of your own buys a signature over a payload nobody can read.
    const out = applyTail(
      s,
      realm(s.identity.id),
      [{ ...forged, hash: envelopeHash(forged) }],
      0,
      '',
    )
    expect(out.refused).toBeNull()
    expect(out.events[0].status).toBe('unreadable')
    expect(out.state.txns.size).toBe(0)
  })

  it('refuses a gap in the order', () => {
    const s = session()
    const first = at(s, 1, '')
    // Envelope 2 is never served; 3 claims to follow 2, which this client has
    // not seen. Before, a gap in `seq` went unnoticed and the link was checked
    // against a hash the server chose.
    const third = at(s, 3, envelopeHash(first))
    const out = applyTail(s, realm(s.identity.id), [first, third], 0, '')
    expect(out.verifiedUpTo).toBe(1)
    expect(out.refused).toMatchObject({ seq: 3 })
    expect(out.refused!.reason).toMatch(/sits at 3 where 2 was expected/)
  })

  it('refuses an envelope that follows something else', () => {
    const s = session()
    const first = at(s, 1, '')
    const second = at(s, 2, '00'.repeat(32))
    const out = applyTail(s, realm(s.identity.id), [first, second], 0, '')
    expect(out.verifiedUpTo).toBe(1)
    expect(out.refused!.reason).toMatch(/does not follow the entry before it/)
  })

  it('chains on the hash it recomputed, not the one the server states', () => {
    const s = session()
    const first = at(s, 1, '')
    const second = at(s, 2, envelopeHash(first))
    // The server states a hash for the first that the second names. That used to
    // be the whole of the link check, so any subsequence the server cared to
    // deliver satisfied it.
    const lying: FetchedEnvelope = { ...first, hash: '11'.repeat(32) }
    const out = applyTail(s, realm(s.identity.id), [lying, second], 0, '')
    expect(out.verifiedUpTo).toBe(0)
    expect(out.refused).toMatchObject({ seq: 1 })
    expect(out.refused!.reason).toMatch(/not the hash of what it sent/)
  })

  it('refuses an envelope filed under another ledger', () => {
    const s = session()
    const e = { ...at(s, 1, ''), ledger: 'elsewhere' }
    const out = applyTail(s, realm(s.identity.id), [e], 0, '')
    expect(out.refused!.reason).toMatch(/belongs to the ledger/)
  })

  it('refuses an event id it has already applied', () => {
    const s = session()
    const st = realm(s.identity.id)
    const first = compose(s, 0, [putCost], head)
    const e1 = fetched(first.envelope)
    // The same plaintext, at the next position: the author saying the same thing
    // twice. The envelope is signed and linked, so the chain is intact — but the
    // cost is not written a second time.
    const e2 = fetched({
      ...first.envelope,
      seq: 2,
      prevHash: envelopeHash(first.envelope),
      signature: '',
    })
    const signed = { ...e2, signature: signEnvelope(e2, s.identity.signSk) }
    const out = applyTail(s, st, [e1, { ...signed, hash: envelopeHash(signed) }], 0, '')
    expect(out.refused).toBeNull()
    expect(out.events.map((e) => e.status)).toEqual(['applied', 'duplicate'])
    expect(out.verifiedUpTo).toBe(2)
  })

  it('applies nothing after the entry that stopped it', () => {
    const s = session()
    const first = at(s, 1, '')
    const bad = at(s, 2, envelopeHash(first))
    bad.signature = '00'.repeat(64)
    const third = at(s, 3, envelopeHash(bad), {
      tag: 16,
      kind: 'deleteTransaction',
      id: 'cost-1',
    })
    const out = applyTail(s, realm(s.identity.id), [first, bad, third], 0, '')
    expect(out.verifiedUpTo).toBe(1)
    expect(out.events).toHaveLength(1)
    // The cost the first envelope wrote is still there; the deletion the third
    // asked for is not on the screen and never was.
    expect(out.state.txns.has('cost-1')).toBe(true)
  })
})

describe('the join between a checkpoint and the tail', () => {
  /** An envelope at `seq`, claiming to follow `prev`. */
  function at(s: RealmSession, seq: number, prev: string): FetchedEnvelope {
    return fetched(compose(s, 0, [putCost], { seq: seq - 1, hash: prev }).envelope)
  }

  it('links the first envelope to the head hash the commitment carries', () => {
    const s = session()
    const e = at(s, 8, 'head-of-seven')
    const out = applyTail(s, realm(s.identity.id), [e], 7, 'head-of-seven')
    expect(out.refused).toBeNull()
    expect(out.verifiedUpTo).toBe(8)
  })

  it('refuses the first envelope when it follows something else', () => {
    const s = session()
    const e = at(s, 8, 'somewhere-else')
    const out = applyTail(s, realm(s.identity.id), [e], 7, 'head-of-seven')
    // There is no longer a case where a link is taken on trust: the state is
    // not applied, and verification stays where the checkpoint left it.
    expect(out.refused).toMatchObject({ seq: 8 })
    expect(out.verifiedUpTo).toBe(7)
    expect(out.state.txns.size).toBe(0)
  })
})

describe('introducing yourself to a realm you were let into', () => {
  /** The realm as a joiner reads it: somebody else's, and saying nothing of them. */
  function strangers(): State {
    const s = emptyState()
    s.realms.set(REALM, {
      id: REALM,
      name: 'the flat',
      members: [['someone-else', 'admin']],
      generation: 0,
    })
    return s
  }

  it('writes the member, the party behind it and the purse, in one event', () => {
    const s = session()
    const me = s.identity.id
    const { envelope } = compose(s, 0, selfIntroduction(s, 'Nils'), head)
    expect(envelope.parts).toHaveLength(2)
    const out = applyTail(s, strangers(), [fetched(envelope)], 0, '')
    expect(out.events[0].status).toBe('applied')

    const member = out.state.members.get(me)
    expect(member).toMatchObject({ id: me, name: 'Nils' })
    // The party is written by `addMember` itself, so no reader of this realm is
    // left holding a member whose spending lands on nothing.
    expect(out.state.parties.get(member!.party)).toMatchObject({ name: 'Nils', kind: 'contact' })
    expect(out.state.realms.get(REALM)!.members).toContainEqual([me, 'viewer'])

    const purse = sortedValues(out.state.accounts).find((a) => a.bridgeOf === me)
    expect(purse).toMatchObject({
      name: 'Members.Nils',
      kind: 'asset',
      realm: REALM,
      owner: member!.party,
      mirrorOf: null,
    })
  })

  it('cannot hand itself more than a view, whatever it asks for', () => {
    const s = session()
    const ops = selfIntroduction(s, 'Nils')
    const grant = ops[1]
    if (grant.kind !== 'grant') throw new Error('the second operation is the grant')
    const { envelope } = compose(s, 0, [ops[0], { ...grant, role: 'admin' }], head)
    const out = applyTail(s, strangers(), [fetched(envelope)], 0, '')
    expect(out.events[0].status).toBe('rejected')
    expect(out.events[0].detail).toMatch(/only an admin of that realm may do that for somebody else/)
    // The member record still landed: the parts of an event are applied one by
    // one, and refusing one does not undo its neighbours.
    expect(out.state.members.has(s.identity.id)).toBe(true)
    expect(out.state.realms.get(REALM)!.members).toHaveLength(1)
  })

  it('cannot introduce anybody but itself', () => {
    const s = session()
    const ops = selfIntroduction(s, 'Nils')
    const add = ops[0]
    if (add.kind !== 'addMember') throw new Error('the first operation is the member')
    const { envelope } = compose(
      s,
      0,
      [{ ...add, member: { ...add.member, id: 'somebody-else' } }],
      head,
    )
    const out = applyTail(s, strangers(), [fetched(envelope)], 0, '')
    expect(out.events[0].status).toBe('rejected')
    expect(out.events[0].detail).toMatch(/only an admin of that realm may do that for somebody else/)
    expect(out.state.members.size).toBe(0)
    expect(out.state.parties.size).toBe(0)
  })
})

/* ------------------------------------------------------------------ */
/* Choosing a checkpoint                                               */
/* ------------------------------------------------------------------ */

/**
 * A checkpoint is one member's claim about what they replayed, so it is worth
 * exactly as much as the member. These are the questions this client asks
 * before it starts from one, each of them a way the old client could be handed
 * an arbitrary state and made to print "verified up to seq N" over it.
 */
describe('choosing a checkpoint', () => {
  const LEDGER = 'home'

  /** A state with one cost in it, which a commitment can be taken over. */
  function committed(author: string): State {
    const s = realm(author)
    s.txns.set(cost.id, cost)
    return s
  }

  /** A checkpoint over `state`, signed by `by`, at `seq` after `headHash`. */
  function checkpointOf(
    key: Uint8Array,
    by: Identity,
    state: State,
    seq: number,
    headHash: string,
    over: Partial<Checkpoint> = {},
  ): Checkpoint {
    const bytes = encode(stateCodec, state)
    const snapshot = sealPart(key, snapshotAd(LEDGER, REALM, 0, by.id), bytes)
    const c: Checkpoint = {
      ledger: LEDGER,
      realm: REALM,
      generation: 0,
      seq,
      stateHash: sha256Hex(bytes),
      headHash,
      snapshotHash: sha256Hex(snapshot),
      author: by.id,
      signature: '',
      snapshot,
      ...over,
    }
    return { ...c, signature: toHex(sodium.crypto_sign_detached(checkpointBytes(c), by.signSk)) }
  }

  /** A sequencer that answers with the checkpoints and the entry it was given. */
  function stub(checkpoints: Checkpoint[], at: FetchedEnvelope | null): Sequencer {
    return {
      checkpoints: async () => checkpoints,
      event: async (_l: string, seq: number) => (at !== null && at.seq === seq ? at : null),
    } as unknown as Sequencer
  }

  /** A session whose pinned inviter is `inviter`, over the key `key`. */
  function sessionWith(key: Uint8Array, inviter: string | null, seq: Sequencer): RealmSession {
    return {
      seq,
      identity: generateIdentity(),
      ledger: LEDGER,
      realm: REALM,
      keys: new Map([[0, key]]),
      trustedInviter: inviter,
    }
  }

  it('takes one signed by the inviter this browser pinned', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose(
        { ...sessionWith(key, null, stub([], null)), identity: admin },
        0,
        [putCost],
        head,
      ).envelope,
    )
    const c = checkpointOf(key, admin, state, 1, envelopeHash(entry))
    const s = sessionWith(key, admin.id, stub([c], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).not.toBeNull()
    expect(chosen.snapshot!.seq).toBe(1)
    expect(chosen.snapshot!.state.txns.has(cost.id)).toBe(true)
  })

  it('ignores one signed by somebody it has no reason to trust', async () => {
    const key = generateRealmKey()
    const mallory = generateIdentity()
    const admin = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    // Mallory is an ordinary viewer: she holds the realm key, so she can encode
    // any state she likes, seal it correctly and sign her own commitment.
    const c = checkpointOf(key, mallory, state, 1, envelopeHash(entry))
    const s = sessionWith(key, admin.id, stub([c], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).toBeNull()
    expect(chosen.note).toMatch(/is not an admin of this realm/)
  })

  it('takes one signed by an admin of the state it already holds', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    const c = checkpointOf(key, admin, state, 1, envelopeHash(entry))
    const s = sessionWith(key, null, stub([c], entry))
    expect((await chooseSnapshot(s)).snapshot).toBeNull()
    // The same checkpoint, offered to a client that has already replayed the
    // realm and knows who administers it.
    expect((await chooseSnapshot(s, state)).snapshot).not.toBeNull()
  })

  it('refuses a commitment whose signature does not hold', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    const c = checkpointOf(key, admin, state, 1, envelopeHash(entry))
    const s = sessionWith(key, admin.id, stub([{ ...c, seq: 1, stateHash: 'ff' }], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).toBeNull()
    expect(chosen.note).toMatch(/not signed by the member it names/)
  })

  it('refuses a snapshot that is not the one the commitment covers', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    const c = checkpointOf(key, admin, state, 1, envelopeHash(entry))
    // The bytes swapped for somebody else's, with the signature left alone.
    const other = sealPart(key, snapshotAd(LEDGER, REALM, 0, admin.id), encode(stateCodec, realm(admin.id)))
    const s = sessionWith(key, admin.id, stub([{ ...c, snapshot: other }], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).toBeNull()
    expect(chosen.note).toMatch(/not the one the commitment covers/)
  })

  it('refuses a snapshot that is not the state the commitment names', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    // A commitment whose `stateHash` names one state and whose snapshot holds
    // another, signed and digested consistently: only re-encoding catches it.
    const claimed = sha256Hex(encode(stateCodec, committed(admin.id)))
    const c = checkpointOf(key, admin, realm(admin.id), 1, envelopeHash(entry), {
      stateHash: claimed,
    })
    const s = sessionWith(key, admin.id, stub([c], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).toBeNull()
    expect(chosen.note).toMatch(/not the state the commitment names/)
  })

  it('refuses a commitment naming a head the chain does not have there', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    const c = checkpointOf(key, admin, state, 1, 'ab'.repeat(32))
    const s = sessionWith(key, admin.id, stub([c], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).toBeNull()
    expect(chosen.note).toMatch(/not the one the commitment names/)
  })

  it('takes the newest of the ones that verify', async () => {
    const key = generateRealmKey()
    const admin = generateIdentity()
    const mallory = generateIdentity()
    const state = committed(admin.id)
    const entry = fetched(
      compose({ ...sessionWith(key, null, stub([], null)), identity: admin }, 0, [putCost], head)
        .envelope,
    )
    const good = checkpointOf(key, admin, state, 1, envelopeHash(entry))
    // Mallory's is further along, and worth nothing.
    const hers = checkpointOf(key, mallory, state, 9, envelopeHash(entry))
    const s = sessionWith(key, admin.id, stub([good, hers], entry))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot!.author).toBe(admin.id)
    expect(chosen.snapshot!.seq).toBe(1)
  })

  it('replays from the beginning when there is nothing it can verify', async () => {
    const key = generateRealmKey()
    const s = sessionWith(key, null, stub([], null))
    const chosen = await chooseSnapshot(s)
    expect(chosen.snapshot).toBeNull()
    expect(chosen.note).toBeNull()
  })
})

/* ------------------------------------------------------------------ */
/* Where a log starts, and what a reader does about a hole in it       */
/* ------------------------------------------------------------------ */

/**
 * Genesis is a *position*, not a permission.
 *
 * It used to be decided by asking whether the state the reader had folded so
 * far looked untouched, and that is a question about the reader rather than
 * about the log. A browser holds one key generation while a node holds every
 * one, so after any revoke or key rotation a browser replaying from the
 * beginning skips every part written before the rotation and arrives, part way
 * along, at a state indistinguishable from a new ledger. One snapshot by
 * anybody still in the realm then replaced the whole of what it displayed — and
 * since a snapshot can name its author an admin, every checkpoint they
 * published afterwards was trusted too.
 */
describe('where a log starts', () => {
  /** A state worth taking over: somebody else's realm, with a cost in it. */
  function planted(author: string): State {
    const s = realm(author)
    s.txns.set(cost.id, cost)
    return s
  }

  it('takes a snapshot that is the whole first entry of the fold', () => {
    const s = session()
    const g = planted(s.identity.id)
    const op: Op = { tag: 50, kind: 'snapshot', state: g }
    const { envelope } = compose(s, 0, [op], head)
    const out = applyTail(s, emptyState(), [fetched(envelope)], 0, '')
    expect(out.refused).toBeNull()
    expect(out.events[0]).toMatchObject({ seq: 1, status: 'applied' })
    expect(out.state.txns.has(cost.id)).toBe(true)
  })

  it('refuses the same snapshot one position later', () => {
    const s = session()
    const first = fetched(compose(s, 0, [putCost], head).envelope)
    const op: Op = { tag: 50, kind: 'snapshot', state: planted(s.identity.id) }
    const second = fetched(
      compose(s, 0, [op], { seq: 1, hash: envelopeHash(first) }).envelope,
    )
    const out = applyTail(s, realm(s.identity.id), [first, second], 0, '')
    expect(out.refused).toBeNull()
    expect(out.events.map((e) => e.status)).toEqual(['applied', 'rejected'])
    expect(out.events[1].detail).toMatch(/a snapshot is where a log starts/)
  })

  it('refuses one at the reader’s first position when the reader began at a checkpoint', () => {
    const s = session()
    const op: Op = { tag: 50, kind: 'snapshot', state: planted(s.identity.id) }
    const e = fetched(compose(s, 0, [op], { seq: 7, hash: 'head-of-seven' }).envelope)
    const out = applyTail(s, realm(s.identity.id), [e], 7, 'head-of-seven')
    expect(out.events[0].status).toBe('rejected')
    expect(out.state.txns.size).toBe(0)
  })

  it('is not a beginning when the envelope carries a part this reader cannot open', () => {
    // The distinction the whole rule turns on: the question is asked of the
    // *envelope*'s part count, never of how many parts opened. How many parts an
    // envelope carries is a fact every reader sees; which of them decrypt is a
    // fact about one key ring — so a reader that asked the second question would
    // adopt a snapshot that an honest reader of the same order applies as an
    // ordinary event, the two would hold different states, and checkpoint
    // comparison would have them accusing each other of it.
    const s = session()
    const op: Op = { tag: 50, kind: 'snapshot', state: planted(s.identity.id) }
    const { envelope } = compose(s, 0, [op], head)
    // A second part, in a realm this browser holds no key for, whose ciphertext
    // a fetch therefore withholds. It is inside the signature, because the
    // signature covers every part's realm, generation and `cipherHash`.
    const two = {
      ...envelope,
      parts: [
        ...envelope.parts,
        {
          realm: 'somewhere-else',
          generation: 0,
          cipherHash: sha256Hex(Uint8Array.from([1, 2, 3])),
          ciphertext: null,
        },
      ],
    }
    const signed = { ...two, signature: signEnvelope(two, s.identity.signSk) }
    const out = applyTail(s, emptyState(), [fetched(signed)], 0, '')
    // The chain verified: one part opened and it is a snapshot. It is still not
    // a beginning, so the snapshot is refused like any other invalid part and
    // nothing it named reaches the state.
    expect(out.refused).toBeNull()
    expect(out.events[0].status).toBe('rejected')
    expect(out.events[0].detail).toMatch(/a snapshot is where a log starts/)
    expect(out.state.txns.has(cost.id)).toBe(false)
  })

  it('is a beginning this reader cannot read when the one part will not open', () => {
    // One part in the envelope, so this *is* position 1's genesis — and this
    // browser holds no key for it. The fold begins from the empty state and the
    // hole is recorded, because what it holds is then a fold around something it
    // never saw. A node does the same and files the realm in `event_unreadable`.
    const s = session()
    const op: Op = { tag: 50, kind: 'snapshot', state: planted(s.identity.id) }
    const e = fetched(compose(s, 0, [op], head).envelope)
    const rotated: RealmSession = { ...s, keys: new Map([[1, generateRealmKey()]]) }
    const out = applyTail(rotated, emptyState(), [e], 0, '')
    expect(out.refused).toBeNull()
    expect(out.state.txns.size).toBe(0)
    expect(out.gap).toEqual({ seq: 1, generation: 0 })
    expect(out.events[0].status).toBe('unreadable')
  })

  it('refuses an order that does not begin with the entry the link named', () => {
    // A genesis is accepted by the fold on its author's signature alone, and
    // that proves only that *some* member wrote it — so a member of the realm
    // plus any sequencer willing to serve their chain could otherwise decide the
    // whole of a joiner's initial state, including who it says administers the
    // realm. The link's author knew what their order begins with and the
    // fragment never reached a server.
    const s = session()
    const op: Op = { tag: 50, kind: 'snapshot', state: planted(s.identity.id) }
    const e = fetched(compose(s, 0, [op], head).envelope)
    const right = genesisFingerprint(envelopeHash(e))

    const pinned: RealmSession = { ...s, genesisHash: right }
    const ok = applyTail(pinned, emptyState(), [e], 0, '')
    expect(ok.refused).toBeNull()
    expect(ok.state.txns.has(cost.id)).toBe(true)

    const elsewhere: RealmSession = { ...s, genesisHash: 'ff'.repeat(16) }
    const out = applyTail(elsewhere, emptyState(), [e], 0, '')
    expect(out.refused).toMatchObject({ seq: 1 })
    expect(out.refused!.reason).toMatch(/not the ledger you joined/)
    expect(out.state.txns.size).toBe(0)
  })

  it('asks nothing about the beginning when the fold starts from a checkpoint', () => {
    // A store that starts from a checkpoint never sees position 1, which is the
    // same answer `linksToGenesis` gives on a node whose store begins at one.
    const s: RealmSession = { ...session(), genesisHash: 'ff'.repeat(16) }
    const e = fetched(compose(s, 0, [putCost], { seq: 7, hash: 'head-of-seven' }).envelope)
    const out = applyTail(s, realm(s.identity.id), [e], 7, 'head-of-seven')
    expect(out.refused).toBeNull()
    expect(out.events[0].status).toBe('applied')
  })

  it('is not a beginning when the snapshot travels beside something else', () => {
    const s = session()
    const op: Op = { tag: 50, kind: 'snapshot', state: planted(s.identity.id) }
    const { envelope } = compose(s, 0, [op, putCost], head)
    const out = applyTail(s, realm(s.identity.id), [fetched(envelope)], 0, '')
    // The snapshot part is refused like any other invalid one, and its
    // neighbour applies: the something else would otherwise have to land either
    // before or after a state that replaced everything, and neither reading is
    // one two implementations would agree on.
    expect(out.events[0].status).toBe('rejected')
    expect(out.state.txns.get(cost.id)?.postings).toHaveLength(2)
  })
})

/**
 * A link that said `none` is a link with nothing to check the order against,
 * and without this it stays that way: the browser re-derives its whole state
 * from an unchecked entry 1 on every cold open, for ever, while a genesis is
 * accepted by the fold on its author's signature alone. So the first fold that
 * reaches position 1 writes down what it found there, which is trust on first
 * use and exactly what `Node/Sync.lean`'s `noteProgress` does on a node.
 */
describe('the entry this browser writes down', () => {
  const LEDGER = 'home'

  /** A `localStorage` and a `sessionStorage`, which the test environment has not. */
  function shim(): Storage {
    const m = new Map<string, string>()
    return {
      get length() {
        return m.size
      },
      clear: () => m.clear(),
      getItem: (k: string) => m.get(k) ?? null,
      key: (i: number) => [...m.keys()][i] ?? null,
      removeItem: (k: string) => void m.delete(k),
      setItem: (k: string, v: string) => void m.set(k, v),
    } as Storage
  }

  /** The ref a browser that joined on a `none` link holds: no digest at all. */
  const unpinned = {
    sequencer: '/seq/v2',
    ledger: LEDGER,
    realm: REALM,
    inviterSignPk: 'a1'.repeat(32),
    generation: 0,
    keyHash: 'b2'.repeat(16),
    genesisHash: '',
    keyGenerations: {},
  }

  /** A sequencer with no checkpoints, serving one run of entries. */
  function serving(events: FetchedEnvelope[]): Sequencer {
    const last = events[events.length - 1]
    return {
      checkpoints: async () => [],
      events: async () => ({
        head: last === undefined ? head : { seq: last.seq, hash: envelopeHash(last) },
        events,
      }),
    } as unknown as Sequencer
  }

  /** A genesis entry: one envelope, one part, one snapshot of a realm. */
  function genesis(s: RealmSession): FetchedEnvelope {
    const state = realm(s.identity.id)
    state.txns.set(cost.id, cost)
    return fetched(compose(s, 0, [{ tag: 50, kind: 'snapshot', state }], head).envelope)
  }

  beforeEach(() => {
    globalThis.localStorage = shim()
    globalThis.sessionStorage = shim()
  })

  it('reports the fingerprint of entry 1 when nothing was pinned', () => {
    const s: RealmSession = { ...session(), genesisHash: '' }
    const e = genesis(s)
    const out = applyTail(s, emptyState(), [e], 0, '')
    expect(out.refused).toBeNull()
    expect(out.genesisNoted).toBe(genesisFingerprint(envelopeHash(e)))
  })

  it('reports nothing when a digest was pinned, because then it checked one', () => {
    const s = session()
    const e = genesis(s)
    const pinned: RealmSession = { ...s, genesisHash: genesisFingerprint(envelopeHash(e)) }
    expect(applyTail(pinned, emptyState(), [e], 0, '').genesisNoted).toBeNull()
  })

  it('reports nothing when the fold starts from a checkpoint', () => {
    // Such a fold never sees position 1, which is the same answer
    // `linksToGenesis` gives on a node whose store begins at a checkpoint.
    const s: RealmSession = { ...session(), genesisHash: '' }
    const e = fetched(compose(s, 0, [putCost], { seq: 7, hash: 'head-of-seven' }).envelope)
    const out = applyTail(s, realm(s.identity.id), [e], 7, 'head-of-seven')
    expect(out.refused).toBeNull()
    expect(out.genesisNoted).toBeNull()
  })

  it('persists it into the stored ref, and onto the session in hand', async () => {
    saveRealmRef(unpinned)
    const s: RealmSession = { ...session(), ledger: LEDGER, genesisHash: '' }
    const e = genesis(s)
    const view = await loadRealm({ ...s, seq: serving([e]) })
    expect(view.refused).toBeNull()
    expect(loadRealmRef()!.genesisHash).toBe(genesisFingerprint(envelopeHash(e)))
  })

  it('checks every later cold open against what it wrote down', async () => {
    saveRealmRef(unpinned)
    const s: RealmSession = { ...session(), ledger: LEDGER, genesisHash: '' }
    const first = genesis(s)
    await loadRealm({ ...s, seq: serving([first]) })

    // A second tab, opened cold: it builds its session out of the stored ref,
    // which now says what the order begins with. A sequencer serving a second
    // chain — a hostile operator, a typo-squatted host — is refused before the
    // entry it offers is anything.
    const cold: RealmSession = {
      ...s,
      seq: serving([genesis({ ...s, identity: generateIdentity() })]),
      genesisHash: loadRealmRef()!.genesisHash,
    }
    const view = await loadRealm(cold)
    expect(view.refused).toMatchObject({ seq: 1 })
    expect(view.refused!.reason).toMatch(/not the ledger you joined/)
    expect(view.state.txns.size).toBe(0)
  })

  it('writes one down once and never moves it', async () => {
    saveRealmRef({ ...unpinned, genesisHash: 'c3'.repeat(16) })
    noteGenesisHash('ab'.repeat(16))
    expect(loadRealmRef()!.genesisHash).toBe('c3'.repeat(16))
    // And a fold cannot move it either: with a digest in hand the fold checks
    // rather than learns, so there is nothing for `loadRealm` to write back.
    const s: RealmSession = { ...session(), ledger: LEDGER, genesisHash: '' }
    const e = genesis(s)
    await loadRealm({ ...s, seq: serving([e]) })
    expect(loadRealmRef()!.genesisHash).toBe('c3'.repeat(16))
  })

  it('writes nothing when this browser holds no realm ref at all', () => {
    // Nothing to backfill into, and nothing thrown at the caller either.
    expect(() => noteGenesisHash('ab'.repeat(16))).not.toThrow()
    expect(loadRealmRef()).toBeNull()
  })
})

/**
 * A reader that cannot read every part of a realm between its start and the
 * head refuses to display that realm rather than folding around the gap.
 */
describe('a part this reader holds no key for', () => {
  it('is a gap, and a gap is not something to fold around', () => {
    const s = session()
    const rotated: RealmSession = {
      ...s,
      keys: new Map([[1, generateRealmKey()]]),
    }
    // Written under generation 0, read by a browser that holds only generation 1.
    const e = fetched(compose(s, 0, [putCost], head).envelope)
    const out = applyTail(rotated, realm(s.identity.id), [e], 0, '')
    // The chain still verified — the signature and the digests travel whether or
    // not the payload does — and the realm is still not something to display.
    expect(out.refused).toBeNull()
    expect(out.verifiedUpTo).toBe(1)
    expect(out.gap).toEqual({ seq: 1, generation: 0 })
    expect(gapMessage(out.gap!)).toMatch(/cannot verify: no checkpoint covers/)
  })

  it('is not raised by a part of somebody else’s realm', () => {
    const s = session()
    const elsewhere: RealmSession = { ...s, realm: 'another-realm' }
    const e = fetched(compose(s, 0, [putCost], head).envelope)
    const out = applyTail(elsewhere, realm(s.identity.id), [e], 0, '')
    expect(out.gap).toBeNull()
    expect(out.events[0].status).toBe('unreadable')
  })

  it('is not raised when every part of the realm opens', () => {
    const s = session()
    const e = fetched(compose(s, 0, [putCost], head).envelope)
    expect(applyTail(s, realm(s.identity.id), [e], 0, '').gap).toBeNull()
  })
})

/**
 * The pinned inviter is a bootstrap, not a root.
 *
 * It used to be honoured unconditionally, with no expiry and no way to unpin:
 * an admin who was later demoted or revoked was still trusted by every browser
 * they ever invited, for both grants and checkpoints — and a checkpoint is an
 * arbitrary `State`, including one naming them an admin, which made the
 * takeover self-sustaining.
 */
describe('the pinned inviter', () => {
  function pinned(inviter: string): RealmSession {
    return { ...session(), trustedInviter: inviter }
  }

  it('is trusted while the state records nobody as an admin of the realm', () => {
    const inviter = 'inviter-key'
    const s = pinned(inviter)
    expect(trustedAuthor(s, null, inviter)).toBe(true)
    expect(trustedAuthor(s, emptyState(), inviter)).toBe(true)
    expect(pinStillAdmin(s, emptyState())).toBeNull()
  })

  it('stops being trusted once the state names admins it is not among', () => {
    const inviter = 'inviter-key'
    const s = pinned(inviter)
    const state = realm('somebody-else')
    expect(trustedAuthor(s, state, inviter)).toBe(false)
    expect(trustedAuthor(s, state, 'somebody-else')).toBe(true)
    expect(pinStillAdmin(s, state)).toBe(false)
  })

  it('goes on being trusted while the state still calls it an admin', () => {
    const inviter = 'inviter-key'
    const s = pinned(inviter)
    const state = realm(inviter)
    expect(trustedAuthor(s, state, inviter)).toBe(true)
    expect(pinStillAdmin(s, state)).toBe(true)
  })

  it('never displaces this member’s own word about their own checkpoint', () => {
    const s = pinned('inviter-key')
    expect(trustedAuthor(s, realm('somebody-else'), s.identity.id)).toBe(true)
  })
})

/**
 * `self` is not an admin anybody can have heard from.
 *
 * It is the member a ledger belongs to before there is a key to sign with, it
 * is in `State.init` from the start, and it cannot have signed anything — so a
 * realm whose only admin is `self` is one this reader has not read, and the pin
 * is what it has. `Node/Session.lean`'s `trusts` spells the same clause
 * `m != Member.selfId`; a client that counted `self` would spend its bootstrap
 * against a state nobody wrote and show an empty page instead.
 */
describe('the member id `self`', () => {
  /** A realm whose members are exactly these, in the order given. */
  function withMembers(members: [string, 'admin' | 'viewer'][]): State {
    const s = emptyState()
    s.realms.set(REALM, { id: REALM, name: 'the flat', members, generation: 0 })
    return s
  }

  it('is the literal `Member.selfId` carries', () => {
    expect(selfMemberId).toBe('self')
  })

  it('is not counted among a realm’s admins', () => {
    expect(realmAdmins(withMembers([[selfMemberId, 'admin']]), REALM)).toEqual([])
  })

  it('is dropped from beside the admins that did sign something', () => {
    const state = withMembers([
      [selfMemberId, 'admin'],
      ['anna', 'admin'],
      ['bo', 'viewer'],
    ])
    expect(realmAdmins(state, REALM)).toEqual(['anna'])
  })

  it('leaves the pin consulted, because such a realm has not been read', () => {
    const inviter = 'inviter-key'
    const s: RealmSession = { ...session(), trustedInviter: inviter }
    const state = withMembers([[selfMemberId, 'admin']])
    expect(trustedAuthor(s, state, inviter)).toBe(true)
    expect(trustedAuthor(s, state, 'a-stranger')).toBe(false)
    expect(pinStillAdmin(s, state)).toBeNull()
  })

  it('is not itself somebody to believe about a realm', () => {
    const s: RealmSession = { ...session(), trustedInviter: 'inviter-key' }
    expect(trustedAuthor(s, withMembers([[selfMemberId, 'admin']]), selfMemberId)).toBe(false)
  })

  it('stops the pin as soon as somebody else administers the realm', () => {
    const inviter = 'inviter-key'
    const s: RealmSession = { ...session(), trustedInviter: inviter }
    const state = withMembers([
      [selfMemberId, 'admin'],
      ['anna', 'admin'],
    ])
    expect(trustedAuthor(s, state, inviter)).toBe(false)
    expect(trustedAuthor(s, state, 'anna')).toBe(true)
    expect(pinStillAdmin(s, state)).toBe(false)
  })
})
