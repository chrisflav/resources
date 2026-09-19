/**
 * Reading a realm, and writing to it.
 *
 * The whole of what the thin client does with a sequencer: pick a checkpoint it
 * has a reason to trust, fetch the tail of envelopes after it, verify every
 * signature and recompute every hash, decrypt the parts this member holds a key
 * for, and apply them.
 *
 * ## An event is verified and applied, or it is refused
 *
 * Version 1 of the protocol signed and hashed each part's *ciphertext*, and a
 * fetch hands back only the parts the caller holds a grant for — so a filtered
 * reader was shown neither the bytes the signature covered nor the bytes the
 * hash digested. That is where the state called "unverifiable" came from, and
 * behind it stood nothing but the sequencer's word. The client folded those
 * envelopes into the balances on screen anyway and mentioned them in a table at
 * the bottom of the page.
 *
 * There is no such state now. Version 2 signs and hashes each part's
 * `cipherHash`, which is the same string for every reader, so this client:
 *
 * - verifies every envelope's signature against its own author;
 * - recomputes `hash(envelope)` rather than believing the one the server states,
 *   and refuses an envelope whose stated hash disagrees;
 * - requires `seq = previous + 1`, so an envelope cannot be dropped from the
 *   middle of the order;
 * - requires `prevHash` to equal the hash it recomputed for the entry before —
 *   never a hash the server supplied;
 * - checks every ciphertext it actually receives against that part's
 *   `cipherHash`;
 * - refuses an event id it has already seen in this run.
 *
 * The first envelope that fails any of these stops the fold. Nothing after it
 * is applied, `verifiedUpTo` stays where it was, and the view says which entry
 * stopped it and why. A figure on the screen is a figure this client checked.
 *
 * *Rejected is not refused.* A rejected part is one this client verified,
 * decrypted, understood and then refused on the ledger's own rules — somebody's
 * mistake, not an attack — and it leaves the chain intact. An unreadable
 * envelope is one whose parts all belong to realms or generations this member
 * holds no key for, which is nobody's mistake and also leaves the chain intact:
 * the signature and the hash were checked either way.
 *
 * ## Where the state starts
 *
 * A checkpoint is somebody's claim about what they replayed, so it is worth
 * exactly as much as the somebody. This client takes the newest one whose
 * author it has a reason to trust — the inviter pinned when the link was
 * accepted, an admin of the realm in the state it already holds, or itself —
 * and only after checking the commitment's signature, that `snapshotHash` names
 * the bytes that arrived, that `stateHash` names the state they decode to, and
 * that `headHash` is the hash this client recomputes for the envelope at that
 * position. A checkpoint that fails any of those is ignored and reported, and
 * the realm is replayed from the beginning instead, which is always correct and
 * only slower.
 */

import { decode, encode, partPlaintextCodec, stateCodec } from './codec'
import type { PartPlaintext } from './codec'
import { applyPart } from './apply'
import {
  checkpointBytes,
  envelopeHash,
  freshId,
  openPart,
  partAd,
  sealPart,
  sha256Hex,
  signEnvelope,
  snapshotAd,
  verifyEnvelope,
  verifySigned,
} from './crypto'
import type { Envelope, Identity, WirePart } from './crypto'
import { emptyState, realmAdmins } from './state'
import { noteGenesisHash } from './store'
import type { Checkpoint, FetchedEnvelope, Head, Sequencer } from './sequencer'
import type { Account, Member, Op, Part, State } from './types'
import { utf8 } from './bytes'

/* ------------------------------------------------------------------ */
/* Where an order begins                                               */
/* ------------------------------------------------------------------ */

/**
 * What a link says when the order it offers has no entry yet.
 *
 * A literal rather than an empty field, because an empty field is what a link
 * written by something else looks like: a link this client reads always says
 * where the order begins, and `none` is one of the two things it can say.
 */
export const noGenesis = 'none'

/**
 * The digest of an order's first entry that an invite link carries.
 *
 * Sixteen bytes of the SHA-256 of the *hash* of entry 1's envelope: a digest of
 * a digest, because what is being fingerprinted is the hex string every reader
 * that has taken that entry in already holds — so this hashes the UTF-8 of that
 * string and not the bytes it names. Half a SHA-256 for the same reason
 * `realmKeyHash` is half of one: a link is typed and pasted by people, and this
 * is a check against a value the reader has in hand rather than a commitment
 * somebody must be unable to find a collision against.
 *
 * `Resources.Node.genesisFingerprint`, byte for byte.
 */
export function genesisFingerprint(envelopeHashHex: string): string {
  return sha256Hex(utf8(envelopeHashHex)).slice(0, 32)
}

/**
 * The fingerprint of the entry this sequencer says the order begins with.
 *
 * Computed from the envelope it serves rather than read out of any field it
 * states: `envelopeHash` digests each part's `cipherHash`, so it is the same
 * value for a reader handed every part and for one handed none, and it is the
 * value the inviter's own node wrote into the link. `noGenesis` when the order
 * is empty or its first entry is not at position 1, which are both "there is
 * nothing here that the link could have meant".
 *
 * `Resources.Node.genesisOffered`.
 */
export async function genesisOffered(seq: Sequencer, ledger: string): Promise<string> {
  const { events } = await seq.events(ledger, 0)
  const first = events[0]
  if (first === undefined || first.seq !== 1) return noGenesis
  return genesisFingerprint(envelopeHash(first))
}

/** What became of one envelope this client verified. */
export interface EventRecord {
  seq: number
  /** The hash this client recomputed, never the one the server stated. */
  hash: string
  author: string
  composedAt: string | null
  /** What happened to the parts this member could read. */
  status: 'applied' | 'rejected' | 'unreadable' | 'duplicate' | 'disagreed'
  detail: string | null
}

/** Why the client stopped short of the head. */
export interface Refusal {
  seq: number
  reason: string
}

/** Everything the client knows about one realm at one moment. */
export interface RealmView {
  state: State
  head: Head
  /** The sequence number the snapshot this was built on speaks about, or 0. */
  checkpointSeq: number
  /**
   * The last sequence number whose signature, chain link and digests all held.
   *
   * Everything up to it has been verified *and* applied; there is nothing in
   * between. When it falls short of `head.seq`, `refused` says which entry
   * stopped the fold.
   */
  verifiedUpTo: number
  /**
   * The hash this client recomputed for the entry at `verifiedUpTo`.
   *
   * Empty when `verifiedUpTo` is zero. It is what the next envelope this client
   * composes names as its `prevHash`, so an entry that did not verify is never
   * something this member signs a position after.
   */
  verifiedHash: string
  /** The entry that stopped the fold, when one did. */
  refused: Refusal | null
  /** Why the snapshot was not used, when it was offered and not taken. */
  snapshotNote: string | null
  /**
   * The first part of this realm, between the fold's start and the head, that
   * this member holds no key for.
   *
   * A reader that cannot read every part of a realm between where it started and
   * the head has to refuse to display that realm rather than fold around the gap:
   * what it would show is not a ledger anybody wrote. A browser holds the
   * generations it was granted and a node holds every one, so after a revoke or a
   * rotation a browser replaying from the beginning skips everything written
   * before it — and arrives, part way along, at something that looks like a new
   * ledger. The answer is a checkpoint that covers the gap, not a best effort.
   */
  gap: Gap | null
  /** Every envelope after the checkpoint that this client verified, oldest first. */
  events: EventRecord[]
}

/**
 * A part of this realm that the fold could not read.
 *
 * A realm with one is `unverified`, which is the word the node uses for exactly
 * this state in `GET realms` and in `resources sync status`: the projection is a
 * fold *around* a hole, so no checkpoint can be published for it and nobody
 * else's can be checked against it. Where a node shows such a realm under that
 * mark, this client shows nothing of it at all — see `gapMessage`.
 */
export interface Gap {
  seq: number
  /** The key generation it was sealed under. */
  generation: number
}

/**
 * The sentence a reader shows instead of a realm it cannot vouch for.
 *
 * The first clause is the one `conformance/README.md` pins as the wording of
 * this refusal; what follows says which entry and which generation, because a
 * reader who is told only that something is missing cannot ask anybody for the
 * right thing.
 *
 * Two things put an entry out of reach and the answer to both is the same
 * checkpoint: a part sealed under a key this browser was never given, and a
 * part written before the byte format this browser speaks. From in here they
 * are indistinguishable — an old shape and a wrong key both come out of
 * `openPart`/`decode` as a failure — so the sentence names both rather than
 * guessing which.
 */
export function gapMessage(gap: Gap): string {
  return (
    `cannot verify: no checkpoint covers the parts you cannot read — entry ${gap.seq} of this ` +
    `realm is sealed under generation ${gap.generation}, which this browser either holds no ` +
    'key for or cannot read at the byte format it speaks. Whoever administers the realm can ' +
    'publish a checkpoint past it, and an older client is upgraded rather than re-invited'
  )
}

/** What the client needs to read and write one realm. */
export interface RealmSession {
  seq: Sequencer
  identity: Identity
  ledger: string
  realm: string
  /** The realm key, per generation: a revoke bumps the generation and mints a new one. */
  keys: Map<number, Uint8Array>
  /**
   * The inviter's signing key, pinned when this browser accepted the link.
   *
   * It is the one key a newcomer has any reason to trust before they have
   * replayed a single entry, so it is what makes a first checkpoint usable and
   * what makes the first grant something other than the server's word.
   */
  trustedInviter: string | null
  /**
   * `genesisFingerprint` of entry 1, pinned from the same link.
   *
   * Empty or absent when the link said `none` — there was no entry to name — and
   * then there is nothing to compare against *yet*: the first fold that reaches
   * position 1 writes what it found there into the stored ref and onto this
   * field, which is `noteProgress`'s trust on first use and leaves only the one
   * fold unchecked instead of every fold for ever. When it is set, a fold that
   * starts from nothing checks it against the entry the sequencer serves at
   * position 1 and refuses the whole order if it differs: a genesis is accepted
   * on its author's signature alone, and that proves only that *some* member
   * wrote it.
   *
   * Checked here rather than by a request of its own, because a cold replay has
   * entry 1 in hand already. A fold that starts from a checkpoint never sees
   * position 1 and so never asks, which is the same answer `linksToGenesis`
   * gives on a node whose store begins at a checkpoint.
   */
  genesisHash?: string
}

/** The key for a generation, or `null` when this member never held one. */
function keyFor(session: RealmSession, generation: number): Uint8Array | null {
  return session.keys.get(generation) ?? null
}

/* ------------------------------------------------------------------ */
/* Trust                                                               */
/* ------------------------------------------------------------------ */

/**
 * Whether this client has a reason to believe what a member says about a realm.
 *
 * Three reasons, and there are no others: it is this member themselves, the
 * state this client has already replayed records them as an admin of the realm,
 * or — and only until that state says anything at all about who administers it —
 * they are the inviter this browser pinned when it accepted the link.
 *
 * "Says anything at all" means an admin other than `self`, which is what
 * `realmAdmins` returns and what `Node/Session.lean`'s `trusts` asks: `self` is
 * in `State.init` before anything is folded and cannot have signed anything, so
 * a realm it alone administers is one this reader has not read.
 *
 * **The pin is a bootstrap, not a root.** It used to be honoured unconditionally,
 * with no expiry and no way to unpin: the admin who made your invite link stayed
 * trusted by your browser for ever, so one who was later demoted or revoked
 * could still hand you any checkpoint they liked — and a checkpoint is an
 * arbitrary `State`, including one that names them an admin, which then satisfied
 * the clause below for everything afterwards. Once the replayed state records an
 * admin set for the realm, that set is the whole of the answer.
 */
export function trustedAuthor(
  session: RealmSession,
  known: State | null,
  author: string,
): boolean {
  if (author === session.identity.id) return true
  // Admins other than `self`, because that is the set with something behind it:
  // `realmAdmins` has already dropped `self`, so a non-empty list here is a
  // realm this client has read somebody's word about.
  const admins = known === null ? [] : realmAdmins(known, session.realm)
  if (admins.length > 0) return admins.includes(author)
  return session.trustedInviter !== null && author === session.trustedInviter
}

/**
 * Whether the pin this browser holds is still somebody the realm calls an admin.
 *
 * `null` while the state says nothing — the bootstrap is all there is, and that
 * is the ordinary first load. `false` once the state names admins and the pinned
 * key is not among them, which is a sentence for the screen: everything this
 * browser believed on that key's word is worth re-checking.
 */
export function pinStillAdmin(session: RealmSession, known: State | null): boolean | null {
  if (session.trustedInviter === null || known === null) return null
  const admins = realmAdmins(known, session.realm)
  if (admins.length === 0) return null
  return admins.includes(session.trustedInviter)
}

/* ------------------------------------------------------------------ */
/* The snapshot                                                        */
/* ------------------------------------------------------------------ */

/** A decoded checkpoint: the state it commits to, and where in the order it sits. */
export interface Snapshot {
  state: State
  seq: number
  /** The hash of the envelope at `seq`, recomputed by this client. */
  headHash: string
  /** The author whose commitment this is. */
  author: string
}

/**
 * Checks one checkpoint end to end, or says in one sentence why it is no good.
 *
 * Every question is asked here, in the order that makes each one cheap: whether
 * this client holds the key at all, whether the author is somebody it trusts,
 * whether the bytes that arrived are the bytes the commitment covers, whether
 * the signature holds, whether the snapshot decodes to a state whose own hash is
 * the one committed to, and whether the position it names really carries the
 * envelope it claims.
 */
async function openCheckpoint(
  session: RealmSession,
  known: State | null,
  c: Checkpoint,
): Promise<{ snapshot: Snapshot } | { error: string }> {
  const key = keyFor(session, c.generation)
  if (key === null) {
    return { error: `it is sealed under generation ${c.generation}, which you hold no key for` }
  }
  if (!trustedAuthor(session, known, c.author)) {
    return { error: `${c.author.slice(0, 12)}… is not an admin of this realm as far as you know` }
  }
  // The digest of the bytes that arrived, before anything is done with them:
  // the commitment covers it, so a server that swapped the snapshot and kept
  // the signature is caught here rather than three checks later.
  const digest = sha256Hex(c.snapshot)
  if (c.snapshotHash !== digest) {
    return { error: 'the snapshot that came back is not the one the commitment covers' }
  }
  if (
    !verifySigned(
      c.author,
      checkpointBytes({
        ledger: c.ledger,
        realm: c.realm,
        generation: c.generation,
        seq: c.seq,
        stateHash: c.stateHash,
        headHash: c.headHash,
        snapshotHash: digest,
      }),
      c.signature,
    )
  ) {
    return { error: 'the commitment is not signed by the member it names' }
  }
  let state: State
  try {
    const plain = openPart(key, snapshotAd(c.ledger, c.realm, c.generation, c.author), c.snapshot)
    state = decode(stateCodec, plain)
  } catch (e) {
    return { error: `the snapshot does not open: ${e instanceof Error ? e.message : String(e)}` }
  }
  // The state has to be the state the commitment names. Re-encoding it is what
  // makes that a question about bytes rather than about fields, and the decoder
  // refuses every non-canonical spelling, so there is exactly one answer.
  if (sha256Hex(encode(stateCodec, state)) !== c.stateHash) {
    return { error: 'the snapshot is not the state the commitment names' }
  }
  // And the position it speaks about has to be a position the chain reached,
  // with the hash the commitment names — recomputed here from the envelope's
  // own bytes, never read off the server's `hash` field.
  if (c.seq === 0) {
    if (c.headHash !== '') return { error: 'a commitment at position zero names a head' }
  } else {
    const at = await session.seq.event(session.ledger, c.seq)
    if (at === null) return { error: `the ledger has no entry at ${c.seq}` }
    if (!verifyEnvelope(at)) return { error: `the entry at ${c.seq} is not signed by its author` }
    if (envelopeHash(at) !== c.headHash) {
      return { error: `the entry at ${c.seq} is not the one the commitment names` }
    }
  }
  return { snapshot: { state, seq: c.seq, headHash: c.headHash, author: c.author } }
}

/**
 * The newest checkpoint this client can verify, or nothing.
 *
 * The list is one row per author, so "newest" is a choice between claims rather
 * than a fact the server settled; taking the furthest along of the ones that
 * verify is the only reading that cannot be steered by somebody who holds a
 * grant and nothing else.
 */
export async function chooseSnapshot(
  session: RealmSession,
  known: State | null = null,
): Promise<{ snapshot: Snapshot | null; note: string | null }> {
  let offered: Checkpoint[]
  try {
    offered = await session.seq.checkpoints(session.ledger, session.realm)
  } catch {
    return { snapshot: null, note: null }
  }
  const newestFirst = [...offered].sort((a, b) => b.seq - a.seq)
  const complaints: string[] = []
  for (const c of newestFirst) {
    const result = await openCheckpoint(session, known, c)
    if ('snapshot' in result) {
      return {
        snapshot: result.snapshot,
        note:
          complaints.length === 0
            ? null
            : `${complaints.length} newer checkpoint(s) were ignored: ${complaints.join('; ')}`,
      }
    }
    complaints.push(result.error)
  }
  return {
    snapshot: null,
    note:
      complaints.length === 0
        ? null
        : `replaying from the beginning: ${complaints.join('; ')}`,
  }
}

/* ------------------------------------------------------------------ */
/* The tail                                                            */
/* ------------------------------------------------------------------ */

/** The parts of one envelope this member can read, and whether they agree. */
function readParts(
  session: RealmSession,
  e: FetchedEnvelope,
): { parts: Part[]; plain: PartPlaintext[]; error: string | null; missed: number | null } {
  const parts: Part[] = []
  const plain: PartPlaintext[] = []
  // A part of *this* realm that will not open is a hole in what this reader can
  // vouch for, and it is remembered rather than skipped: see `RealmView.gap`.
  let missed: number | null = null
  for (const p of e.parts) {
    if (p.realm !== session.realm) continue
    if (p.ciphertext === null) {
      if (missed === null) missed = p.generation
      continue
    }
    const key = keyFor(session, p.generation)
    if (key === null) {
      if (missed === null) missed = p.generation
      continue
    }
    let decoded: PartPlaintext
    try {
      const bytes = openPart(key, partAd(e.ledger, p.realm, p.generation, e.author), p.ciphertext)
      decoded = decode(partPlaintextCodec, bytes)
    } catch {
      if (missed === null) missed = p.generation
      continue
    }
    // The realm is inside the plaintext too, so a part cannot be re-labelled.
    if (decoded.part.realm !== p.realm) {
      return {
        parts: [],
        plain: [],
        error: 'a part names a realm it was not filed under',
        missed,
      }
    }
    plain.push(decoded)
    parts.push(decoded.part)
  }
  // All readable parts of one envelope have to agree on the per-event fields; a
  // disagreement makes every part of it a no-op.
  const first = plain[0]
  if (first !== undefined) {
    for (const q of plain) {
      if (
        q.eventId !== first.eventId ||
        q.composedAt !== first.composedAt ||
        q.basedOn !== first.basedOn
      ) {
        return {
          parts: [],
          plain: [],
          error: 'the readable parts of this envelope disagree about the event they belong to',
          missed,
        }
      }
    }
  }
  return { parts, plain, error: null, missed }
}

/**
 * What this client insists on before an envelope is anything but bytes.
 *
 * Returns the sentence that refuses it, or `null`. Nothing here needs a key: a
 * reader who holds no grant on any of an envelope's realms still checks all of
 * it, which is the whole of what version 2 bought.
 */
function verifyEnvelopeAt(
  e: FetchedEnvelope,
  ledger: string,
  expectedSeq: number,
  expectedPrev: string,
): string | null {
  if (e.ledger !== ledger) return `it belongs to the ledger '${e.ledger}'`
  if (e.seq !== expectedSeq) return `it sits at ${e.seq} where ${expectedSeq} was expected`
  if (!verifyEnvelope(e)) return 'its signature does not verify against its author'
  if (e.prevHash !== expectedPrev) return 'it does not follow the entry before it'
  // The hash the server states is carried so that a disagreement is loud rather
  // than invisible; it is never what the chain is checked against.
  const hash = envelopeHash(e)
  if (e.hash !== '' && e.hash !== hash) {
    return 'the hash the sequencer states is not the hash of what it sent'
  }
  for (const p of e.parts) {
    if (p.ciphertext === null) continue
    if (sha256Hex(p.ciphertext) !== p.cipherHash) {
      return `the ciphertext for realm '${p.realm}' is not the one its digest names`
    }
  }
  return null
}

/** What folding a run of envelopes came to. */
export interface Tail {
  state: State
  events: EventRecord[]
  verifiedUpTo: number
  verifiedHash: string
  refused: Refusal | null
  /** The first part of this realm the fold could not open, when there was one. */
  gap: Gap | null
  /**
   * The fingerprint of entry 1, when this fold met it and nothing was pinned.
   *
   * `null` whenever there is nothing to write down: the fold started from a
   * checkpoint, or it never reached position 1, or a digest was pinned already
   * and was therefore checked rather than learned. `loadRealm` is what persists
   * it; folding stays a pure function of what it was handed.
   */
  genesisNoted: string | null
}

/**
 * Folds a run of envelopes into a state, verifying each before it is anything.
 *
 * `fromHash` is the hash the first envelope must name: the checkpoint's
 * `headHash`, or the empty string when the replay starts at the beginning. It
 * is never `null` — there is no longer a case where a link is taken on trust.
 */
export function applyTail(
  session: RealmSession,
  start: State,
  envelopes: readonly FetchedEnvelope[],
  fromSeq: number,
  fromHash: string,
  seen: Set<string> = new Set(),
): Tail {
  let state = start
  const events: EventRecord[] = []
  let prevHash = fromHash
  let expected = fromSeq + 1
  let verifiedUpTo = fromSeq
  let gap: Gap | null = null
  let genesisNoted: string | null = null

  for (const e of envelopes) {
    const wrong = verifyEnvelopeAt(e, session.ledger, expected, prevHash)
    if (wrong !== null) {
      return {
        state,
        events,
        verifiedUpTo,
        verifiedHash: prevHash,
        refused: { seq: e.seq, reason: wrong },
        gap,
        genesisNoted,
      }
    }
    const hash = envelopeHash(e)
    // The entry this browser was told the order begins with, when it was told
    // anything. `Node/Sync.lean`'s `linksToGenesis` asks the same question of the
    // same value, and a sequencer serving a second chain — a hostile operator, a
    // typo-squatted host in a link — is what it refuses.
    //
    // And when it was told nothing, this is where it learns: a link that said
    // `none` had no entry to name, so the first fold that reaches position 1
    // writes down what it found there and every later cold open is checked
    // against that. Trust on first use, exactly as `noteProgress` does it on a
    // node, and asked of the entry the fold is about to take in rather than of a
    // request of its own — the two can be answered differently, and it is this
    // one that becomes the state.
    if (fromSeq === 0 && e.seq === 1) {
      const fingerprint = genesisFingerprint(hash)
      if (session.genesisHash !== undefined && session.genesisHash !== '') {
        if (fingerprint !== session.genesisHash) {
          return {
            state,
            events,
            verifiedUpTo,
            verifiedHash: prevHash,
            refused: {
              seq: e.seq,
              reason:
                `this browser joined an order beginning with entry ${session.genesisHash}, and ` +
                `this one begins with ${fingerprint}: it is not the ledger you joined`,
            },
            gap,
            genesisNoted,
          }
        }
      } else {
        genesisNoted = fingerprint
      }
    }
    const record: EventRecord = {
      seq: e.seq,
      hash,
      author: e.author,
      composedAt: null,
      status: 'unreadable',
      detail: null,
    }
    prevHash = hash
    expected = e.seq + 1
    verifiedUpTo = e.seq

    const read = readParts(session, e)
    if (read.missed !== null && gap === null) gap = { seq: e.seq, generation: read.missed }
    if (read.error !== null) {
      record.status = 'disagreed'
      record.detail = read.error
      events.push(record)
      continue
    }
    const first = read.plain[0]
    if (first !== undefined) {
      record.composedAt = first.composedAt
      // An event id seen before is refused. The envelope is signed and linked,
      // so this is its author saying the same thing twice rather than anybody
      // replaying it — but applying it twice would double a cost all the same.
      if (seen.has(first.eventId)) {
        record.status = 'duplicate'
        record.detail = 'an event with this id has already been applied'
        events.push(record)
        continue
      }
      seen.add(first.eventId)
    }

    // Where a log starts is a *position*, and this is the only position it can
    // be: the first entry of the reader's own order, when the reader started
    // from nothing. `Resources.stepAt` with `pos = 1`, and `Node/Sync.lean`'s
    // `genesisOf`.
    //
    // The question is asked of the **envelope** — `e.parts`, which lists every
    // part the entry carries and gives a `null` ciphertext for the ones this
    // reader was not handed — and never of what opened. How many parts an
    // envelope carries is a fact every reader sees; which of them decrypt is a
    // fact about one key ring, so a reader that asked the second question would
    // hold a different state from an honest reader of the same order, and
    // checkpoint comparison would have them accusing each other of it.
    //
    // So, at position 1, the three cases the node's module header states:
    //
    //  - one part in the envelope, readable, and a snapshot → the state this
    //    order begins from;
    //  - one part, and this reader cannot open it → the fold begins from the
    //    empty state and `gap` already records the hole, because what this
    //    browser holds is then a fold around something it never saw;
    //  - more than one part → an ordinary event applied to the empty state,
    //    whatever this reader could open of it. A snapshot beside something else
    //    is not a beginning: the something else would have to apply either
    //    before or after a state that replaced everything, and neither reading
    //    is one two implementations would agree on.
    //
    // A snapshot anywhere later is a part `applyPart` refuses like any other
    // invalid one.
    if (fromSeq === 0 && e.seq === 1 && e.parts.length === 1) {
      const only = read.parts[0]
      if (read.parts.length === 1 && only.op.kind === 'snapshot') {
        state = only.op.state
        record.status = 'applied'
        record.detail = 'the state this log starts from'
        events.push(record)
        continue
      }
    }

    let applied = 0
    const problems: string[] = []
    for (const part of read.parts) {
      const result = applyPart(state, e.author, part)
      if (result.kind === 'ok') {
        state = result.state
        applied++
      } else {
        problems.push(result.message)
      }
    }
    record.status = problems.length > 0 ? 'rejected' : applied > 0 ? 'applied' : 'unreadable'
    if (problems.length > 0) record.detail = problems.join('; ')
    events.push(record)
  }

  return { state, events, verifiedUpTo, verifiedHash: prevHash, refused: null, gap, genesisNoted }
}

/**
 * Loads the snapshot, fetches everything after it and folds it in.
 *
 * `known` is the state this client already holds, if any: it is what says who
 * administers the realm, and so which checkpoints are worth anything. On a cold
 * start there is none, and the only author a newcomer can trust is the inviter
 * their link named.
 */
export async function loadRealm(
  session: RealmSession,
  known: State | null = null,
): Promise<RealmView> {
  const chosen = await chooseSnapshot(session, known)
  const from = chosen.snapshot
  const start = from === null ? emptyState() : from.state
  const fromSeq = from === null ? 0 : from.seq
  const fromHash = from === null ? '' : from.headHash
  const { head, events } = await session.seq.events(session.ledger, fromSeq)
  const folded = applyTail(session, start, events, fromSeq, fromHash)
  // A fold that met position 1 with nothing pinned is the one that pins it: into
  // the stored ref, so the next cold open in this browser is checked, and onto
  // the session in hand, so the next fold in this tab is too. It is written once
  // and never moved — `noteGenesisHash` refuses to overwrite one.
  if (folded.genesisNoted !== null) {
    noteGenesisHash(folded.genesisNoted)
    session.genesisHash = folded.genesisNoted
  }
  return {
    state: folded.state,
    head,
    checkpointSeq: fromSeq,
    verifiedUpTo: folded.verifiedUpTo,
    verifiedHash: folded.verifiedHash,
    refused: folded.refused,
    snapshotNote: chosen.note,
    gap: folded.gap,
    events: folded.events,
  }
}

/* ------------------------------------------------------------------ */
/* Composing                                                           */
/* ------------------------------------------------------------------ */

/** One composed envelope, and the plaintext it was built from. */
export interface Composed {
  envelope: Envelope
  eventId: string
}

/**
 * Encrypts, signs and addresses an event at one position in the order.
 *
 * Every part carries the per-event fields in its own plaintext, so a reader who
 * can open any one of them can rebuild the event; the envelope gains no field
 * the sequencer could read. What the envelope does carry, for every part, is
 * the digest of its ciphertext — which is what the signature covers, so that
 * every reader can check it whether or not they were given the bytes.
 */
export function compose(
  session: RealmSession,
  generation: number,
  ops: readonly Op[],
  head: Head,
  now: string = new Date().toISOString().replace(/\.\d+Z$/, ''),
): Composed {
  const key = keyFor(session, generation)
  if (key === null) throw new Error(`no realm key for generation ${generation}`)
  const eventId = freshId()
  const basedOn = head.seq
  const parts: WirePart[] = ops.map((op) => {
    const part: Part = { realm: session.realm, op }
    const plaintext = encode(partPlaintextCodec, {
      eventId,
      composedAt: now,
      basedOn,
      part,
    })
    const ciphertext = sealPart(
      key,
      partAd(session.ledger, session.realm, generation, session.identity.id),
      plaintext,
    )
    return {
      realm: session.realm,
      generation,
      cipherHash: sha256Hex(ciphertext),
      ciphertext,
    }
  })
  const envelope: Envelope = {
    ledger: session.ledger,
    seq: head.seq + 1,
    prevHash: head.hash,
    author: session.identity.id,
    parts,
    signature: '',
  }
  envelope.signature = signEnvelope(envelope, session.identity.signSk)
  return { envelope, eventId }
}

/**
 * The two operations a joiner writes about themselves, as one event.
 *
 * An invite is spent against the sequencer, not against the log: the admin who
 * wrote the link was a browser tab rather than a node composing events, so
 * nothing in the realm's own history says the newcomer is there. These are that
 * sentence, and they are the two operations `Core/Apply.lean` lets somebody
 * perform about themselves alone — a member record under their own id, and the
 * weakest grant there is, a view of the realm they were already let into.
 *
 * `addMember` comes first because `grant` refuses a member it has never heard
 * of, and the two travel in one event so a reader never sees half of it. The
 * member record names a fresh party, which `addMember` writes for a newcomer so
 * the reference does not dangle for everybody downstream; the bridge is the
 * purse they hold a balance in here, and the core points its owner at that same
 * party whatever this client puts in the field.
 */
export function selfIntroduction(session: RealmSession, name: string): Op[] {
  const member: Member = { id: session.identity.id, name, party: freshId() }
  const bridge: Account = {
    id: freshId(),
    name: `Members.${name}`,
    kind: 'asset',
    owner: member.party,
    commodity: null,
    iban: null,
    note: null,
    closedOn: null,
    realm: session.realm,
    bridgeOf: member.id,
    posters: [],
    mirrorOf: null,
  }
  return [
    { tag: 44, kind: 'addMember', member },
    { tag: 46, kind: 'grant', realm: session.realm, member: member.id, role: 'viewer', bridge },
  ]
}

/** What a submission came to. */
export interface SubmitResult {
  view: RealmView
  /** The envelope that landed, by its hash, or `null` when nothing was appended. */
  hash: string | null
  /** The sentence to show when the intent could not be carried out. */
  error: string | null
}

/**
 * Composes, submits, and on a 409 re-reads and tries again.
 *
 * There is no automatic rebase: the operations are composed again against the
 * new head, and if the intent no longer makes sense against what arrived in the
 * meantime the sequencer takes it and the next fetch shows it as rejected. That
 * is the honest outcome — the alternative is a client that quietly rewrites
 * what somebody asked for.
 */
export async function submit(
  session: RealmSession,
  generation: number,
  ops: readonly Op[],
  known: State | null = null,
  attempts = 3,
): Promise<SubmitResult> {
  let view = await loadRealm(session, known)
  for (let i = 0; i < attempts; i++) {
    // The head to build on is the one this client verified up to, not the one
    // the server states: appending after an entry that did not verify would be
    // signing a position in a chain nobody has checked.
    if (view.refused !== null) {
      return {
        view,
        hash: null,
        error:
          `entry ${view.refused.seq} did not verify (${view.refused.reason}), ` +
          'so nothing was written',
      }
    }
    const composed = compose(session, generation, ops, {
      seq: view.verifiedUpTo,
      hash: view.verifiedHash,
    })
    const result = await session.seq.append(session.ledger, composed.envelope)
    if (result.kind === 'appended') {
      const after = await loadRealm(session, view.state)
      const hash = envelopeHash(composed.envelope)
      const landed = after.events.find((e) => e.seq === composed.envelope.seq)
      return {
        view: after,
        hash,
        error:
          landed && (landed.status === 'rejected' || landed.status === 'disagreed')
            ? landed.detail
            : null,
      }
    }
    view = await loadRealm(session, view.state)
  }
  return { view, hash: null, error: 'the head kept moving; nothing was appended' }
}
