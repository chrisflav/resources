/**
 * A typed client for `/seq/v2`.
 *
 * The sequencer is the only server this client talks to, and it only ever sees
 * ciphertext: it orders parts, counts them and refuses them, and can read none
 * of them. Everything below is the route table of `Resources/Sync/Routes.lean`,
 * one method per route, with the JSON shapes of `Sync/Protocol.lean`.
 *
 * Three things are worth saying out loud about the shapes.
 *
 * *A fetched envelope carries only the parts the caller holds a grant for, and
 * every part's `cipherHash` either way.* That digest is what the signature and
 * the hash are taken over, so a filtered reader can still check who wrote an
 * envelope and recompute where it sits in the chain. The `hash` the server
 * states is carried but never believed: `sync.ts` recomputes it.
 *
 * *Nothing here decides whether a record is trustworthy.* A grant carries the
 * signature of whoever issued it, a member carries their own signature over
 * their agreement key, and a checkpoint carries its author's commitment; this
 * file reads them off the wire and `sync.ts` checks them. The split is
 * deliberate — a transport that also decided what to believe would be a
 * transport nobody could audit.
 *
 * *A 409 on append is a fact, not a failure.* It carries the head that moved,
 * which is exactly what a retry needs, so it comes back as a value rather than
 * as a thrown error.
 */

import { fromBase64, toBase64 } from './bytes'
import type { Envelope, WirePart } from './crypto'

/** A request the sequencer refused, with its status. */
export class SeqError extends Error {
  constructor(
    message: string,
    readonly status: number,
  ) {
    super(message)
  }
}

/** Where a ledger's chain has got to. `seq = 0` with an empty hash is an empty ledger. */
export interface Head {
  seq: number
  hash: string
}

/** An envelope as it comes back from a fetch: filtered parts, and the stored hash. */
export interface FetchedEnvelope extends Envelope {
  hash: string
}

/**
 * One member's access to one realm: the realm key, wrapped to their public key,
 * and the signature of whoever said so.
 *
 * `grantedBy` is a realm admin, or the member themselves when the grant came
 * out of an invite they redeemed. A client accepts a grant for its own use only
 * from a signer it has a reason to trust — itself, the inviter pinned from the
 * link it joined by, or a realm admin its own replayed state records.
 */
export interface Grant {
  realm: string
  member: string
  generation: number
  wrappedKey: Uint8Array
  role: string
  grantedBy: string
  signature: string
}

/**
 * A signed commitment, plus the encrypted snapshot a newcomer starts from.
 *
 * One is kept per author rather than one per realm: a checkpoint is one
 * member's claim about what they replayed, and keeping only the newest of them
 * all let any grant holder erase everybody else's.
 */
export interface Checkpoint {
  ledger: string
  realm: string
  generation: number
  seq: number
  stateHash: string
  /**
   * The hash of the envelope at `seq`; empty when `seq` is 0.
   *
   * It is what lets the first envelope after a checkpoint be chain-checked
   * instead of taken on trust: the first envelope of the tail carries a
   * `prevHash`, and this is the value it has to match.
   */
  headHash: string
  /** The digest of the encrypted snapshot, which the commitment covers. */
  snapshotHash: string
  author: string
  signature: string
  snapshot: Uint8Array
}

/** One realm this member holds a grant on, as `GET realms` lists it. */
export interface RealmAccess {
  realm: string
  /** The generation this member holds a key for, which falls behind after a revoke. */
  generation: number
  role: string
}

/**
 * What redeeming an invite hands back: the sealed realm key, and what it is for.
 *
 * `inviterSignPk` is the member id of the admin who made the invite, which is
 * the one key a newcomer has any reason to trust before they have replayed a
 * single entry. The link carries it too, and the joiner insists the two agree.
 */
export interface Redeemed {
  wrappedKey: Uint8Array
  inviteBoxPk: string
  inviterSignPk: string
  generation: number
  role: string
}

/**
 * A member of a ledger, by public key, with the agreement key they published
 * for themselves and the signature that says they did.
 *
 * `boxPk` is empty for a member an admin wrote in and who has not authenticated
 * since: only the member may set it, and only with their own signature over
 * `memberBytes`.
 */
export interface LedgerMember {
  key: string
  boxPk: string
  boxPkSignature: string
  /**
   * Which generation of this member's agreement key `boxPkSignature` covers.
   *
   * It is inside the signed bytes, it only goes up, and the sequencer refuses a
   * lower one — so an operator serving an old attestation cannot make a client
   * seal a realm key to a public half whose secret has leaked. Absent means
   * zero, which is what every key published before this field existed carried.
   */
  keyGeneration: number
  admin: boolean
  addedAt: string
}

/** What an append came to: it landed, or the head moved under it. */
export type AppendResult =
  | { kind: 'appended'; head: Head }
  | { kind: 'conflict'; head: Head }

function partToJson(p: WirePart): unknown {
  const base = { realm: p.realm, generation: p.generation, cipherHash: p.cipherHash }
  return p.ciphertext === null ? base : { ...base, ciphertext: toBase64(p.ciphertext) }
}

/**
 * Reads a part.
 *
 * `cipherHash` is required, because it is what the signature covers;
 * `ciphertext` is optional, because a fetch strips it from the realms the
 * caller holds no grant on. Whether it was there is remembered rather than
 * guessed at from an empty byte string — an author may seal an empty plaintext,
 * and "withheld" and "empty" are different facts.
 */
function partOfJson(j: Record<string, unknown>): WirePart {
  return {
    realm: String(j.realm ?? ''),
    generation: Number(j.generation ?? 0),
    cipherHash: String(j.cipherHash ?? ''),
    ciphertext:
      j.ciphertext === undefined || j.ciphertext === null
        ? null
        : fromBase64(String(j.ciphertext)),
  }
}

/** An envelope, with its ciphertext base64-encoded. `Envelope.toJson`. */
export function envelopeToJson(e: Envelope): unknown {
  return {
    ledger: e.ledger,
    seq: e.seq,
    prevHash: e.prevHash,
    author: e.author,
    parts: e.parts.map(partToJson),
    signature: e.signature,
  }
}

/** Reads an envelope, keeping the `hash` the server stored. */
export function envelopeOfJson(j: Record<string, unknown>): FetchedEnvelope {
  const parts = Array.isArray(j.parts) ? (j.parts as Record<string, unknown>[]) : []
  return {
    ledger: String(j.ledger ?? ''),
    seq: Number(j.seq ?? 0),
    prevHash: String(j.prevHash ?? ''),
    author: String(j.author ?? ''),
    parts: parts.map(partOfJson),
    signature: String(j.signature ?? ''),
    hash: String(j.hash ?? ''),
  }
}

/** A live session with a sequencer: a bearer token bound to one public key. */
export interface Session {
  token: string
  key: string
  /**
   * The origin this sequencer says it is, stated again on the reply that hands
   * out the token.
   *
   * The client has it from the same exchange it signed, so it can compare all
   * three — the origin `health` reported, the one the challenge named and this
   * one — against the URL it dialled. A relay that fetches challenges from the
   * real sequencer can repeat the string; what it cannot do is be the host the
   * client typed.
   */
  origin: string
  expires: number
}

/**
 * A sequencer, addressed by base URL.
 *
 * The token is held in the object rather than in storage: it is worth nothing
 * after an hour, and a client that has to authenticate again loses a round trip
 * and nothing else.
 */
export class Sequencer {
  private token: string | null = null

  constructor(readonly base: string = '/seq/v2') {}

  /**
   * The origin this client actually dialled.
   *
   * The half of the origin check that closes the attack, and it is the client's
   * half: a relay at `evil.example` can report the real sequencer's origin from
   * every route it serves, fetch a challenge from the real one, hand it over as
   * its own and pass the answer back. What it cannot do is be the host in the
   * URL this browser opened.
   */
  get origin(): string {
    try {
      return new URL(this.base, globalThis.location?.href ?? 'http://localhost/').origin
    } catch {
      return ''
    }
  }

  /**
   * Refuses a sequencer whose stated origin is not the one this client dialled.
   *
   * An empty string is configuration rather than protocol: a sequencer that has
   * not been told its own public name — one embedded in a test, or reached only
   * over a loopback socket — binds nothing, and both ends then agree on nothing,
   * which is the same agreement.
   */
  checkOrigin(stated: string, where: string): void {
    if (stated === '') return
    if (stated !== this.origin) {
      throw new SeqError(
        `the ${where} names the origin '${stated}', and this client dialled '${this.origin}'`,
        0,
      )
    }
  }

  /** The bearer token in play, if any. */
  get session(): string | null {
    return this.token
  }

  /** Adopts a token obtained elsewhere. */
  useToken(token: string | null): void {
    this.token = token
  }

  private async request<T>(
    method: string,
    path: string,
    opts: { query?: Record<string, string>; body?: unknown; raw?: BodyInit } = {},
  ): Promise<T> {
    const query = opts.query
      ? '?' +
        Object.entries(opts.query)
          .filter(([, v]) => v !== '')
          .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`)
          .join('&')
      : ''
    const headers: Record<string, string> = {}
    if (this.token) headers.authorization = `Bearer ${this.token}`
    let body: BodyInit | undefined
    if (opts.raw !== undefined) {
      body = opts.raw
    } else if (opts.body !== undefined) {
      headers['content-type'] = 'application/json'
      body = JSON.stringify(opts.body)
    }
    const res = await fetch(`${this.base}/${path}${query}`, { method, headers, body })
    const text = await res.text()
    let payload: unknown = null
    try {
      payload = text ? JSON.parse(text) : null
    } catch {
      payload = text
    }
    if (!res.ok) {
      const message =
        payload && typeof payload === 'object' && 'error' in payload
          ? String((payload as { error: unknown }).error)
          : `request failed with status ${res.status}`
      throw new SeqError(message, res.status)
    }
    return payload as T
  }

  /* ---------------- authentication ---------------- */

  /**
   * Asks for a nonce to sign, and for the origin the answer will be bound to.
   *
   * The origin is in the signed bytes because a signature that named no
   * sequencer was valid at every sequencer: anybody running a second instance
   * could relay a challenge from the real one and open a session as whoever
   * answered it. The client checks the origin it is about to sign against the
   * one `health` reports for the sequencer it meant to talk to.
   */
  challenge(
    key: string,
  ): Promise<{ key: string; nonce: string; origin: string; expires: number }> {
    return this.request('POST', 'challenge', { body: { key } })
  }

  /** Turns a signature over an outstanding nonce into a session, and adopts it. */
  async authenticate(key: string, signature: string): Promise<Session> {
    const s = await this.request<Session>('POST', 'authenticate', { body: { key, signature } })
    // The third statement of the origin, on the reply that hands out the token.
    this.checkOrigin(String(s.origin ?? ''), 'reply that handed out the token')
    this.token = s.token
    return s
  }

  /* ---------------- the order ---------------- */

  /** Where the chain has got to. */
  head(ledger: string): Promise<Head> {
    return this.request('GET', `ledgers/${encodeURIComponent(ledger)}/head`)
  }

  /** The envelopes after `since`, and the head as it was at the time of the read. */
  async events(ledger: string, since: number): Promise<{ head: Head; events: FetchedEnvelope[] }> {
    const j = await this.request<{ head: Head; events: Record<string, unknown>[] }>(
      'GET',
      `ledgers/${encodeURIComponent(ledger)}/events`,
      { query: { since: String(since) } },
    )
    return { head: j.head, events: (j.events ?? []).map(envelopeOfJson) }
  }

  /**
   * One entry by position, filtered exactly as a fetch is.
   *
   * A checkpoint names the head it speaks about by hash, and this is how the
   * client that starts from the snapshot gets hold of that envelope without
   * walking the order back to it — so the join between a snapshot and the tail
   * is a hash this client recomputed rather than one a server stated.
   */
  async event(ledger: string, seq: number): Promise<FetchedEnvelope | null> {
    try {
      const j = await this.request<Record<string, unknown>>(
        'GET',
        `ledgers/${encodeURIComponent(ledger)}/events/${encodeURIComponent(String(seq))}`,
      )
      return envelopeOfJson(j)
    } catch (err) {
      if (err instanceof SeqError && err.status === 404) return null
      throw err
    }
  }

  /**
   * Appends an envelope.
   *
   * A 409 is the head having moved under the claim this envelope makes about
   * where it belongs, which is ordinary and comes back as a value: fetch, apply
   * what arrived, re-compose against the new head and try again.
   */
  async append(ledger: string, e: Envelope): Promise<AppendResult> {
    try {
      const j = await this.request<{ head: Head }>(
        'POST',
        `ledgers/${encodeURIComponent(ledger)}/events`,
        { body: envelopeToJson(e) },
      )
      return { kind: 'appended', head: j.head }
    } catch (err) {
      if (err instanceof SeqError && err.status === 409) {
        const head = await this.head(ledger)
        return { kind: 'conflict', head }
      }
      throw err
    }
  }

  /* ---------------- membership, realms and grants ---------------- */

  async members(ledger: string): Promise<LedgerMember[]> {
    const rows = await this.request<Record<string, unknown>[]>(
      'GET',
      `ledgers/${encodeURIComponent(ledger)}/members`,
    )
    return (rows ?? []).map((j) => ({
      key: String(j.member ?? j.signPk ?? ''),
      boxPk: String(j.boxPk ?? ''),
      boxPkSignature: String(j.boxPkSignature ?? ''),
      keyGeneration: Number(j.keyGeneration ?? 0),
      admin: j.admin === true,
      addedAt: String(j.addedAt ?? ''),
    }))
  }

  /**
   * Publishes this member's own agreement key, with their own signature over it.
   *
   * The one route that writes an agreement key, and it only ever writes the
   * caller's own. The server supplying the key realm keys are sealed to was the
   * hole that made every realm readable by whoever ran the server.
   */
  async putBoxPk(
    ledger: string,
    me: string,
    boxPk: string,
    boxPkSignature: string,
    keyGeneration = 0,
  ): Promise<void> {
    await this.request(
      'PUT',
      `ledgers/${encodeURIComponent(ledger)}/members/${encodeURIComponent(me)}/boxPk`,
      { body: { boxPk, boxPkSignature, keyGeneration } },
    )
  }

  /**
   * The realms this member can open.
   *
   * Not "which realms exist": a realm they hold no grant on is none of their
   * business, down to its name. The generation is the one they hold a key for,
   * so a client that sees it fall behind the realm knows it has been re-keyed
   * without it.
   */
  async realms(ledger: string): Promise<RealmAccess[]> {
    const rows = await this.request<Record<string, unknown>[]>(
      'GET',
      `ledgers/${encodeURIComponent(ledger)}/realms`,
    )
    return (rows ?? []).map((j) => ({
      realm: String(j.realm ?? ''),
      generation: Number(j.generation ?? 0),
      role: String(j.role ?? 'viewer'),
    }))
  }

  /** Every grant on a realm: who holds what, which is how a revoke becomes visible. */
  async grants(ledger: string, realm: string): Promise<Grant[]> {
    const rows = await this.request<Record<string, unknown>[]>(
      'GET',
      `ledgers/${encodeURIComponent(ledger)}/realms/${encodeURIComponent(realm)}/grants`,
    )
    return (rows ?? []).map(grantOfJson)
  }

  /** One member's grant, or `null` when they hold none. */
  async grant(ledger: string, realm: string, who: string): Promise<Grant | null> {
    try {
      const j = await this.request<Record<string, unknown>>(
        'GET',
        `ledgers/${encodeURIComponent(ledger)}/realms/${encodeURIComponent(realm)}/grants/${encodeURIComponent(who)}`,
      )
      return grantOfJson(j)
    } catch (err) {
      if (err instanceof SeqError && err.status === 404) return null
      throw err
    }
  }

  /**
   * Wraps a realm key to a member. Only the realm's admin may.
   *
   * The signature is the issuer's over `grantBytes`, and the sequencer refuses
   * a grant it cannot check — but so does every client that reads one back, so
   * the signature is the record and the route is only where it is filed.
   */
  async putGrant(
    ledger: string,
    realm: string,
    who: string,
    body: { wrappedKey: Uint8Array; role: string; grantedBy: string; signature: string },
  ): Promise<Grant> {
    const j = await this.request<Record<string, unknown>>(
      'POST',
      `ledgers/${encodeURIComponent(ledger)}/realms/${encodeURIComponent(realm)}/grants/${encodeURIComponent(who)}`,
      {
        body: {
          wrappedKey: toBase64(body.wrappedKey),
          role: body.role,
          grantedBy: body.grantedBy,
          signature: body.signature,
        },
      },
    )
    return grantOfJson(j)
  }

  /* ---------------- checkpoints ---------------- */

  /**
   * Every checkpoint on a realm: one per author, furthest along first.
   *
   * Which of them is worth anything is the reader's decision, not the server's.
   * Keeping one row per realm let any grant holder erase everybody else's, so
   * the route hands back the list and `sync.ts` picks the newest one signed by
   * somebody it has a reason to trust.
   */
  async checkpoints(ledger: string, realm: string): Promise<Checkpoint[]> {
    const rows = await this.request<Record<string, unknown>[]>(
      'GET',
      `ledgers/${encodeURIComponent(ledger)}/realms/${encodeURIComponent(realm)}/checkpoint`,
    )
    return (rows ?? []).map((j) => ({
      ledger: String(j.ledger ?? ledger),
      realm: String(j.realm ?? realm),
      generation: Number(j.generation ?? 0),
      seq: Number(j.seq ?? 0),
      stateHash: String(j.stateHash ?? ''),
      headHash: String(j.headHash ?? ''),
      snapshotHash: String(j.snapshotHash ?? ''),
      author: String(j.author ?? ''),
      signature: String(j.signature ?? ''),
      snapshot: fromBase64(String(j.snapshot ?? '')),
    }))
  }

  /* ---------------- joining ---------------- */

  /**
   * Reads the sealed realm key an invite holds, without spending the invite.
   *
   * The link carries the invite's secret and nothing else, so the sealed key
   * has to be fetchable from here — by whoever can prove they hold the matching
   * signing key. The proof is the same signature over the same bytes the join
   * itself takes, which is why reading is safe: anybody who could unseal what
   * comes back could have joined outright. Nothing is consumed, because the key
   * the grant must hold is one only the joiner can compute, and computing it
   * needs this reply first.
   */
  async redeem(
    ledger: string,
    realm: string,
    inviteSignPk: string,
    proof: string,
  ): Promise<Redeemed> {
    const j = await this.request<Record<string, unknown>>(
      'POST',
      `ledgers/${encodeURIComponent(ledger)}/realms/${encodeURIComponent(realm)}` +
        `/invites/${encodeURIComponent(inviteSignPk)}/redeem`,
      { body: { proof } },
    )
    return {
      wrappedKey: fromBase64(String(j.wrappedKey ?? '')),
      inviteBoxPk: String(j.inviteBoxPk ?? ''),
      inviterSignPk: String(j.inviterSignPk ?? j.createdBy ?? ''),
      generation: Number(j.generation ?? 0),
      role: String(j.role ?? 'viewer'),
    }
  }

  /**
   * Spends an invite: how somebody who is not a member yet becomes one.
   *
   * The caller is already authenticated as themselves, so what the invite adds
   * is not "who are you" but "who said you could". `wrappedKey` is the realm
   * key the joiner unsealed with the invite secret and sealed again to their own
   * agreement key, and `boxPk` is that key — the server stores both as the
   * grant and can read neither.
   */
  async join(
    ledger: string,
    realm: string,
    body: {
      inviteSignPk: string
      proof: string
      wrappedKey: Uint8Array
      signature: string
    },
  ): Promise<{ generation: number; grant: Grant }> {
    const j = await this.request<Record<string, unknown>>(
      'POST',
      `ledgers/${encodeURIComponent(ledger)}/realms/${encodeURIComponent(realm)}/join`,
      {
        body: {
          inviteSignPk: body.inviteSignPk,
          proof: body.proof,
          wrappedKey: toBase64(body.wrappedKey),
          signature: body.signature,
        },
      },
    )
    return {
      generation: Number(j.generation ?? 0),
      grant: grantOfJson((j.grant ?? {}) as Record<string, unknown>),
    }
  }

  /* ---------------- blobs ---------------- */

  /** Stores ciphertext under the hash of the ciphertext, which the server checks. */
  putBlob(ledger: string, hash: string, bytes: Uint8Array): Promise<{ hash: string; bytes: number }> {
    return this.request(
      'PUT',
      `ledgers/${encodeURIComponent(ledger)}/blobs/${encodeURIComponent(hash)}`,
      { raw: bytes as unknown as BodyInit },
    )
  }

  /** Fetches a blob's ciphertext, or `null` when there is none. */
  async blob(ledger: string, hash: string): Promise<Uint8Array | null> {
    const headers: Record<string, string> = {}
    if (this.token) headers.authorization = `Bearer ${this.token}`
    const res = await fetch(
      `${this.base}/ledgers/${encodeURIComponent(ledger)}/blobs/${encodeURIComponent(hash)}`,
      { headers },
    )
    if (res.status === 404) return null
    if (!res.ok) throw new SeqError(`request failed with status ${res.status}`, res.status)
    return new Uint8Array(await res.arrayBuffer())
  }

  /**
   * The sequencer's own health: its schema, which verifier it runs, and the
   * origin it binds challenges to.
   *
   * The origin is the one a client signs, so asking for it is not chrome: a
   * client that took the origin from the challenge it was handed would be
   * letting a relay choose what it signed.
   */
  health(): Promise<{ status: string; schema: number; verifier: string; origin: string }> {
    return this.request('GET', 'health')
  }
}

function grantOfJson(j: Record<string, unknown>): Grant {
  return {
    realm: String(j.realm ?? ''),
    member: String(j.member ?? ''),
    generation: Number(j.generation ?? 0),
    wrappedKey: fromBase64(String(j.wrappedKey ?? '')),
    role: String(j.role ?? 'viewer'),
    grantedBy: String(j.grantedBy ?? ''),
    signature: String(j.signature ?? ''),
  }
}
