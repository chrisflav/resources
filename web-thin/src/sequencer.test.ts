/**
 * The two things the client checks about the sequencer itself.
 *
 * *The origin.* A signature over a nonce that named no sequencer was valid at
 * every sequencer, so the origin is inside the signed bytes — and the server
 * states it in three places, on `health`, on the challenge and on the reply that
 * hands out the token. That is as much as a server can do, and it is not the
 * half that closes the attack. A relay at `evil.example` can report the real
 * sequencer's origin from every route it serves, fetch a challenge from the real
 * one, hand it over as its own and pass the answer back; what it cannot do is be
 * the host this browser dialled. So all three are compared against that.
 *
 * *The agreement key's generation.* An attestation with no number was a valid
 * self-attestation for ever, so a member whose secret half had leaked could
 * publish a second key and an untrusted sequencer could go on serving the first.
 */

import { beforeAll, beforeEach, describe, expect, it } from 'vitest'
import { toHex } from './bytes'
import { generateIdentity, ready, signBoxPk } from './crypto'
import { SeqError, Sequencer } from './sequencer'
import {
  loadRealmRef,
  noteKeyGeneration,
  saveRealmRef,
  seenKeyGeneration,
} from './store'
import { verifiedBoxPk } from './App'

describe('the origin a client dialled', () => {
  it('is the origin of the base URL, resolved against the page', () => {
    expect(new Sequencer('https://ledger.example/seq/v2').origin).toBe('https://ledger.example')
    // The ordinary deployment: the client is served from the sequencer, so the
    // base is relative and the origin is the page's own.
    expect(new Sequencer('/seq/v2').origin).toBe(
      new URL('/seq/v2', globalThis.location?.href ?? 'http://localhost/').origin,
    )
  })

  it('refuses a sequencer that names an origin this client did not dial', () => {
    const seq = new Sequencer('https://ledger.example/seq/v2')
    expect(() => seq.checkOrigin('https://ledger.example', 'health route')).not.toThrow()
    expect(() => seq.checkOrigin('https://evil.example', 'health route')).toThrow(SeqError)
    try {
      seq.checkOrigin('https://evil.example', 'challenge')
    } catch (e) {
      expect((e as Error).message).toMatch(/challenge names the origin 'https:\/\/evil.example'/)
    }
  })

  it('binds nothing when the sequencer has not been told its own public name', () => {
    // Configuration rather than protocol: one embedded in a test, or reached
    // only over a loopback socket, binds nothing — and both ends then agree on
    // nothing, which is the same agreement.
    expect(() => new Sequencer('https://ledger.example/seq/v2').checkOrigin('', 'health route'))
      .not.toThrow()
  })
})

describe('a member row', () => {
  it('reads the key generation, and an absent one is zero', async () => {
    const rows = [
      { member: 'a'.repeat(64), boxPk: 'aa', boxPkSignature: 'bb', keyGeneration: 3 },
      { member: 'b'.repeat(64), boxPk: 'cc', boxPkSignature: 'dd' },
    ]
    const seq = new Sequencer('/seq/v2')
    const original = globalThis.fetch
    globalThis.fetch = (async () =>
      new Response(JSON.stringify(rows), {
        status: 200,
        headers: { 'content-type': 'application/json' },
      })) as typeof fetch
    try {
      const members = await seq.members('home')
      expect(members.map((m) => m.keyGeneration)).toEqual([3, 0])
    } finally {
      globalThis.fetch = original
    }
  })
})

/**
 * The client half of the key-generation rule.
 *
 * The sequencer refuses a generation below the one it holds, and that is the
 * half that has to be trusted. Every triple `(boxPk, signature, generation)` a
 * member ever published stays valid on its own terms, so an operator holding a
 * replaced key can serve the old row and a client with no memory will seal the
 * realm key to a public half whose secret has since gone. This browser
 * remembers the highest it has seen, per member, in the realm ref it already
 * stores, and refuses anything below it.
 */
describe('the highest key generation this browser has seen', () => {
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

  const ref = {
    sequencer: '/seq/v2',
    ledger: 'home',
    realm: 'flat',
    inviterSignPk: 'a1'.repeat(32),
    generation: 0,
    keyHash: 'b2'.repeat(16),
    genesisHash: 'c3'.repeat(16),
    keyGenerations: {},
  }

  beforeAll(async () => {
    await ready()
  })

  beforeEach(() => {
    globalThis.localStorage = shim()
    globalThis.sessionStorage = shim()
  })

  it('is zero for a member this browser has never seen publish one', () => {
    saveRealmRef(ref)
    expect(seenKeyGeneration('nobody')).toBe(0)
  })

  it('goes up and never down', () => {
    saveRealmRef(ref)
    noteKeyGeneration('anna', 2)
    expect(seenKeyGeneration('anna')).toBe(2)
    noteKeyGeneration('anna', 1)
    expect(seenKeyGeneration('anna')).toBe(2)
    noteKeyGeneration('anna', 5)
    expect(seenKeyGeneration('anna')).toBe(5)
  })

  it('reads a ref stored before either field existed', () => {
    // Refusing one would lock somebody out of their own ledger over a field they
    // never had: an absent digest is "this browser cannot say", and an absent
    // high-water mark is where every browser starts.
    const old = { ...ref } as Partial<typeof ref>
    delete old.genesisHash
    delete old.keyGenerations
    localStorage.setItem('resources.thin.realm', JSON.stringify(old))
    expect(loadRealmRef()).toMatchObject({ genesisHash: '', keyGenerations: {} })
  })

  it('refuses a member row served below a generation already seen', async () => {
    saveRealmRef(ref)
    const identity = generateIdentity()
    const boxPk = toHex(identity.boxPk)
    const row = (keyGeneration: number) => ({
      member: identity.id,
      boxPk,
      boxPkSignature: signBoxPk(identity.signSk, 'home', identity.id, boxPk, keyGeneration),
      keyGeneration,
    })
    const seq = new Sequencer('/seq/v2')
    const original = globalThis.fetch
    const serving = (rows: unknown[]) => {
      globalThis.fetch = (async () =>
        new Response(JSON.stringify(rows), {
          status: 200,
          headers: { 'content-type': 'application/json' },
        })) as typeof fetch
    }
    try {
      // Signed at generation 3, taken, and remembered.
      serving([row(3)])
      expect(toHex(await verifiedBoxPk(seq, 'home', identity.id))).toBe(boxPk)
      expect(seenKeyGeneration(identity.id)).toBe(3)
      // The same member's earlier attestation, which verifies perfectly well.
      serving([row(1)])
      await expect(verifiedBoxPk(seq, 'home', identity.id)).rejects.toThrow(/has been replaced/)
      // And the one it has is still taken.
      serving([row(3)])
      expect(toHex(await verifiedBoxPk(seq, 'home', identity.id))).toBe(boxPk)
    } finally {
      globalThis.fetch = original
    }
  })
})
