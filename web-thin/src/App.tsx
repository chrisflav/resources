import { useCallback, useEffect, useMemo, useState } from 'react'
import { fromBase64Url, fromHex, fromUtf8, toHex } from './bytes'
import {
  budgetAccount,
  budgetBalance,
  claims as budgetClaims,
  costs as budgetCosts,
  remaining,
  shortName,
  standings,
} from './budgets'
import { fetchBlob } from './blobs'
import { sortedValues } from './codec'
import {
  freshId,
  generateIdentity,
  grantBytes,
  inviteKeys,
  memberBytes,
  ready,
  sha256Hex,
  signBoxPk,
  signChallenge,
  signGrant,
  signJoinProof,
  unwrapKey,
  verifySigned,
  wrapKey,
} from './crypto'
import type { Identity } from './crypto'
import { claimAmount, dateOfIso, dateToIso } from './ledger'
import { eur, parseAmount, render } from './money'
import { Sequencer } from './sequencer'
import type { Grant } from './sequencer'
import { accountOfId, accountsSorted, emptyState, partyOfId } from './state'
import {
  forgetIdentity,
  hasGuestIdentity,
  hasStoredIdentity,
  loadGuestIdentity,
  loadIdentity,
  loadRealmRef,
  noteKeyGeneration,
  saveGuestIdentity,
  saveIdentity,
  saveRealmRef,
  seenKeyGeneration,
} from './store'
import type { RealmRef } from './store'
import {
  gapMessage,
  genesisOffered,
  loadRealm,
  noGenesis,
  pinStillAdmin,
  selfIntroduction,
  submit,
  trustedAuthor,
} from './sync'
import type { RealmSession, RealmView } from './sync'
import type { Attachment, Budget, Op, Posting, State, Transaction } from './types'

/* ------------------------------------------------------------------ */
/* Sessions                                                            */
/* ------------------------------------------------------------------ */

/** A session, and everything about it that had to be checked to open one. */
interface Opened {
  session: RealmSession
  generation: number
  /** The grant this session's key came out of. */
  grant: Grant
  /**
   * Whether the grant's issuer is somebody this client already trusted.
   *
   * `false` means the key was taken provisionally — the signature holds, but
   * the signer is neither this member nor the pinned inviter — and the realm's
   * own replayed state has to record them as an admin before anything is shown.
   */
  issuerTrusted: boolean
  /**
   * Which signature scheme this deployment is running.
   *
   * `sodium` is the real one. `insecure` and `reject-all` exist so that a test
   * can exercise a refusal that has nothing to do with cryptography, and a
   * deployment running either is one where nothing on this page is signed by
   * anybody — which is worth saying on the page rather than in a log.
   */
  verifier: string
}

/**
 * Opens a session, and takes nothing about it on the server's word.
 *
 * Four things are checked here, and each of them used to be a hole.
 *
 * *The origin.* A signature over a nonce that named no sequencer was valid at
 * every sequencer, so the challenge is answered only for the origin this
 * deployment reports as its own.
 *
 * *The grant.* `crypto_box_seal` is anonymous — it needs only the recipient's
 * public key, which the sequencer stores — so a server could seal a key of its
 * own choosing to this member and hand it over. A grant now carries the
 * signature of whoever issued it, over the realm, the generation, the member,
 * the role and the wrapped key, and a signature this client cannot check is a
 * grant it does not use.
 *
 * *The issuer.* A valid signature by a stranger is still a stranger. The only
 * issuers taken without further evidence are this member and the inviter pinned
 * from the link; anybody else has to be an admin of the realm in the state this
 * client replays, which is checked once the key has opened it.
 *
 * *The key itself.* The hash of the realm key was pinned at the generation the
 * invite named, so a second key at that same generation is refused outright.
 */
async function openSession(
  seq: Sequencer,
  identity: Identity,
  ref: RealmRef,
): Promise<Opened> {
  const { ledger, realm } = ref
  // The origin a client signs is the one the sequencer states about itself, not
  // the one inside the challenge it was handed: a relay controls the second.
  // And "states about itself" is not enough on its own — a relay can repeat the
  // real sequencer's origin from every route it serves — so all three statements
  // are compared against the URL this browser dialled as well as against each
  // other. That is the half of the check the client owns, and it is the half a
  // relay cannot satisfy.
  const health = await seq.health()
  seq.checkOrigin(health.origin, 'health route')
  const c = await seq.challenge(identity.id)
  if (c.origin !== health.origin) {
    throw new Error('this sequencer disagrees with itself about which origin it is')
  }
  seq.checkOrigin(c.origin, 'challenge')
  await seq.authenticate(identity.id, signChallenge(c.nonce, health.origin, identity.signSk))
  // The agreement key realm keys are sealed to is only ever a claim this
  // member's own signing key made. Publishing it is idempotent, and doing it on
  // every session open is what repairs a record an admin wrote without one.
  await publishOwnBoxPk(seq, identity, ledger)
  // The realms this member can open, which is not the question "which realms
  // exist". Asking first turns "you hold no grant" into a sentence that says
  // what they *can* open, and it is where a revoke becomes visible.
  const mine = await seq.realms(ledger)
  const grant = await seq.grant(ledger, realm, identity.id)
  if (grant === null) {
    const others = mine.map((r) => r.realm).join(', ')
    throw new Error(
      others === ''
        ? 'you hold no grant on this realm; ask to be let back in'
        : `you hold no grant on ${realm}; what you can open is ${others}`,
    )
  }
  if (grant.member !== identity.id || grant.realm !== realm) {
    throw new Error('the grant that came back is for somebody else')
  }
  if (
    !verifySigned(
      grant.grantedBy,
      grantBytes(ledger, realm, grant.generation, grant.member, grant.role, grant.wrappedKey),
      grant.signature,
    )
  ) {
    throw new Error('this grant is not signed by whoever it says issued it')
  }
  const issuerTrusted =
    grant.grantedBy === identity.id || grant.grantedBy === ref.inviterSignPk
  const key = unwrapKey(grant.wrappedKey, identity.boxPk, identity.boxSk)
  // The key was pinned at the generation the invite named. A revoke moves the
  // generation on and mints a new key, which is why a later one is allowed;
  // a *different* key at the pinned generation is a substitution.
  if (grant.generation === ref.generation && ref.keyHash !== '' && sha256Hex(key) !== ref.keyHash) {
    throw new Error(
      'the realm key this sequencer handed back is not the one the invite delivered',
    )
  }
  return {
    session: {
      seq,
      identity,
      ledger,
      realm,
      keys: new Map([[grant.generation, key]]),
      trustedInviter: ref.inviterSignPk === '' ? null : ref.inviterSignPk,
      // The other half of the same bootstrap: the fold checks it against entry 1
      // whenever it starts from nothing, which costs no request of its own.
      genesisHash: ref.genesisHash,
    },
    generation: grant.generation,
    grant,
    issuerTrusted,
    verifier: health.verifier,
  }
}

/**
 * Publishes this member's own agreement key, when the sequencer's record of it
 * is not the one they would sign.
 *
 * An admin who adds a member leaves the key empty and the member fills it in;
 * a member who joined through an invite has never filled it in at all. Either
 * way this is the only route that writes one, and it takes the member's own
 * signature over `memberBytes`.
 */
async function publishOwnBoxPk(
  seq: Sequencer,
  identity: Identity,
  ledger: string,
): Promise<void> {
  const boxPk = toHex(identity.boxPk)
  const members = await seq.members(ledger)
  const me = members.find((m) => m.key === identity.id) ?? null
  if (me !== null && me.boxPk === boxPk) return
  // A key that replaces one carries the next generation, because that is what
  // makes the old attestation stop counting: the sequencer refuses a generation
  // below the one it holds, and refuses the same one with different bytes. A
  // record with no key yet is at whatever generation it says, which is zero.
  //
  // And never below the highest generation this browser has already seen this
  // member publish at: a sequencer that serves an old row would otherwise have
  // us re-publish at a generation it is bound to refuse, which is a stall rather
  // than a leak but is the same downgrade read from the other side.
  const stated = me !== null && me.boxPk !== '' ? me.keyGeneration + 1 : (me?.keyGeneration ?? 0)
  const generation = Math.max(stated, seenKeyGeneration(identity.id))
  await seq.putBoxPk(
    ledger,
    identity.id,
    boxPk,
    signBoxPk(identity.signSk, ledger, identity.id, boxPk, generation),
    generation,
  )
}

/**
 * The agreement key a member published for themselves, with their signature on
 * it checked.
 *
 * Nothing is ever sealed to a key that has not been through here. The key used
 * to be whatever the server said it was, so whoever ran the server could
 * substitute one they held and be handed every realm on the next rotation.
 */
export async function verifiedBoxPk(
  seq: Sequencer,
  ledger: string,
  member: string,
): Promise<Uint8Array> {
  const members = await seq.members(ledger)
  const row = members.find((m) => m.key === member) ?? null
  if (row === null) throw new Error(`${member.slice(0, 12)}… is not a member of this ledger`)
  if (row.boxPk === '') {
    throw new Error(`${member.slice(0, 12)}… has published no agreement key yet`)
  }
  // At the generation the row states, because that is what the member signed.
  // Verifying at zero refused every rotated key and accepted the one it replaced.
  if (
    !verifySigned(
      member,
      memberBytes(ledger, member, row.boxPk, row.keyGeneration),
      row.boxPkSignature,
    )
  ) {
    throw new Error(`${member.slice(0, 12)}…'s agreement key is not signed by them`)
  }
  // Signed, and not a generation this browser has already seen this member move
  // past. Every triple a member ever published stays valid on its own terms, so
  // an operator holding a replaced key can serve the old row and be handed the
  // realm again on the next rotation; the sequencer refuses a lower generation
  // and so does this, which is the half that does not have to be trusted.
  const seen = seenKeyGeneration(member)
  if (row.keyGeneration < seen) {
    throw new Error(
      `${member.slice(0, 12)}… has published an agreement key at generation ${seen} and this ` +
        `sequencer is serving generation ${row.keyGeneration}: it is serving a key that has ` +
        'been replaced',
    )
  }
  noteKeyGeneration(member, row.keyGeneration)
  const bytes = fromHex(row.boxPk)
  if (bytes === null || bytes.length !== 32) {
    throw new Error(`${member.slice(0, 12)}…'s agreement key is not a key`)
  }
  return bytes
}

/* ------------------------------------------------------------------ */
/* The invite link                                                     */
/* ------------------------------------------------------------------ */

/** What the fragment of a `/join/#…` link carries. */
export interface Invite {
  ledger: string
  realm: string
  secret: Uint8Array
  /** The inviter's signing key, hex: what this browser pins as a trusted admin. */
  inviterSignPk: string
  /** The first sixteen bytes of the SHA-256 of the realm key, hex. */
  keyHash: string
  /**
   * `genesisFingerprint` of entry 1 of the order, or `noGenesis`.
   *
   * The sixth field, and the one that closes the last door in the bootstrap. A
   * signature on a genesis proves that *some* member wrote it and nothing more,
   * and the state a genesis names is an arbitrary `State`: it can say whatever
   * its author likes about who administers the realm, which then makes every
   * grant and every checkpoint after it trusted too. The inviter knows which
   * entry the order really begins with; the fragment never reaches a server; so
   * they say so, and `Join` recomputes it from the envelope the sequencer
   * serves and refuses a different one.
   */
  genesisHash: string
}

/**
 * Reads the fragment of a `/join/#…` link.
 *
 * The fragment is `base64url(ledger ':' realm ':' hex(secret) ':'
 * inviterSignPk ':' keyHash ':' genesisHash)` — `Node/Sync.lean`'s
 * `Invitation.fragment`, and read back the way `readInvite?` reads it. The
 * secret is hex rather than raw bytes precisely so that the whole fragment is
 * text a colon can be split on: version 1 put the raw secret last to dodge that
 * question, and there are four fields after it now.
 *
 * The realm is whatever lies between the first field and the last four, joined
 * again, so a realm id containing a colon survives the round trip; the ledger is
 * the first field, because that one is a name somebody chose and the outermost
 * thing here.
 */
export function parseInvite(fragment: string): Invite {
  const raw = fromBase64Url(fragment.replace(/^#/, '').trim())
  let text: string
  try {
    text = fromUtf8(raw)
  } catch {
    throw new Error('this invite link is not in the shape this client reads')
  }
  const fields = text.split(':')
  const n = fields.length
  if (n < 6) throw new Error('this invite link is too short to be one')
  const genesisHash = fields[n - 1].toLowerCase()
  const keyHash = fields[n - 2].toLowerCase()
  const inviterSignPk = fields[n - 3].toLowerCase()
  const secret = fromHex(fields[n - 4])
  const ledger = fields[0]
  const realm = fields.slice(1, n - 4).join(':')
  if (secret === null || secret.length !== 32) {
    throw new Error('this invite link does not carry a secret this client can use')
  }
  if (!/^[0-9a-f]{64}$/.test(inviterSignPk) || !/^[0-9a-f]{32}$/.test(keyHash)) {
    throw new Error('this invite link names an inviter or a key that is not a key')
  }
  // Either a digest or the word that says there is nothing to digest. An empty
  // field would be a link that says nothing at all about where the order begins,
  // which is the one thing a link written by this project always says.
  if (genesisHash !== noGenesis && !/^[0-9a-f]{32}$/.test(genesisHash)) {
    throw new Error('this invite link does not say where the ledger begins')
  }
  if (ledger === '' || realm === '') {
    throw new Error('this invite link is missing its ledger or its realm')
  }
  return { ledger, realm, secret, inviterSignPk, keyHash, genesisHash }
}

/** The first sixteen bytes of a realm key's SHA-256, as the link writes them. */
export function realmKeyHash(key: Uint8Array): string {
  return sha256Hex(key).slice(0, 32)
}

/* ------------------------------------------------------------------ */
/* The app                                                             */
/* ------------------------------------------------------------------ */

type Screen =
  | { at: 'booting' }
  | { at: 'join'; invite: Invite; replacing: boolean }
  | { at: 'unlock' }
  | { at: 'lost' }
  | { at: 'realm'; identity: Identity; ref: RealmRef }

export default function App() {
  const [screen, setScreen] = useState<Screen>({ at: 'booting' })
  const [error, setError] = useState<string | null>(null)

  useEffect(() => {
    let live = true
    void ready().then(() => {
      if (!live) return
      try {
        const joining = window.location.pathname.replace(/\/+$/, '') === '/join'
        if (joining && window.location.hash.length > 1) {
          const fragment = window.location.hash
          // The fragment carries a thirty-two-byte secret that opens the realm
          // key, and it is in the address bar until something takes it out of
          // there: in screenshots, in a shared screen, in the profile's history
          // database and in browser sync. So it leaves first, before the parse
          // that might throw, and the secret lives in component state from here.
          window.history.replaceState(null, '', '/join/')
          setScreen({
            at: 'join',
            invite: parseInvite(fragment),
            replacing: hasStoredIdentity() || hasGuestIdentity(),
          })
          return
        }
        const ref = loadRealmRef()
        if (ref === null) {
          setScreen({ at: 'lost' })
          return
        }
        const guest = hasGuestIdentity() ? loadGuestIdentity() : null
        if (guest !== null) {
          setScreen({ at: 'realm', identity: guest, ref })
          return
        }
        setScreen(hasStoredIdentity() ? { at: 'unlock' } : { at: 'lost' })
      } catch (e) {
        setError(e instanceof Error ? e.message : String(e))
        setScreen({ at: 'lost' })
      }
    })
    return () => {
      live = false
    }
  }, [])

  if (screen.at === 'booting') {
    return (
      <Shell title="Resources">
        <div className="muted">Starting up…</div>
      </Shell>
    )
  }

  if (screen.at === 'join') {
    return (
      <Join
        invite={screen.invite}
        replacing={screen.replacing}
        onJoined={(identity, ref) => setScreen({ at: 'realm', identity, ref })}
      />
    )
  }

  if (screen.at === 'unlock') {
    return (
      <Unlock
        onOpened={(identity) => {
          const ref = loadRealmRef()
          if (ref === null) setScreen({ at: 'lost' })
          else setScreen({ at: 'realm', identity, ref })
        }}
      />
    )
  }

  if (screen.at === 'lost') {
    return (
      <Shell title="Resources">
        {error && <div className="error">{error}</div>}
        <div className="card">
          <div className="card-head">nothing to show yet</div>
          <div className="card-body">
            <div className="muted">
              This client holds exactly one realm, and it learns about it from an invite link.
              Open the link somebody sent you — the part after the <code>#</code> is the secret and
              never reaches the server, so the whole link has to be pasted, not just the address.
            </div>
            {(hasStoredIdentity() || hasGuestIdentity()) && (
              <>
                <div className="muted">
                  There are keys stored in this browser that no realm here points at. Forgetting
                  them cannot be undone: anything sealed to them stops opening.
                </div>
                <div className="row">
                  <button
                    className="btn quiet"
                    onClick={() => {
                      forgetIdentity()
                      setError('the keys stored in this browser have been forgotten')
                    }}
                  >
                    Forget the keys stored here
                  </button>
                </div>
              </>
            )}
          </div>
        </div>
      </Shell>
    )
  }

  return <RealmScreen identity={screen.identity} realmRef={screen.ref} />
}

/* ------------------------------------------------------------------ */
/* Furniture                                                           */
/* ------------------------------------------------------------------ */

function Shell({
  title,
  status,
  children,
}: {
  title: string
  status?: React.ReactNode
  children: React.ReactNode
}) {
  return (
    <div className="shell">
      <header className="top">
        <div className="wordmark">
          {title}
          <span>.</span>
        </div>
      </header>
      {status && <div className="statusline">{status}</div>}
      <main style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>{children}</main>
    </div>
  )
}

/* ------------------------------------------------------------------ */
/* Accepting an invite                                                 */
/* ------------------------------------------------------------------ */

function Join({
  invite,
  replacing,
  onJoined,
}: {
  invite: Invite
  replacing: boolean
  onJoined: (identity: Identity, ref: RealmRef) => void
}) {
  const { ledger, realm, secret } = invite
  const [name, setName] = useState('')
  const [passphrase, setPassphrase] = useState('')
  const [guest, setGuest] = useState(false)
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)
  // A second invite on a browser that already holds an identity throws away the
  // only copy of a secret key: the grants on the old realm are sealed to a
  // public key whose secret half would then be gone, and there is no export and
  // no way back. So it is asked for in so many words before anything is made.
  const [confirmed, setConfirmed] = useState(!replacing)

  const accept = async () => {
    const trimmed = name.trim()
    if (trimmed === '') {
      setError('the realm needs something to call you')
      return
    }
    if (replacing && !confirmed) {
      setError('this browser already holds an identity; say so above before replacing it')
      return
    }
    setBusy(true)
    setError(null)
    try {
      const keys = inviteKeys(secret)
      const inviteSignPk = toHex(keys.signPk)
      const identity = generateIdentity()
      const seq = new Sequencer()
      const health = await seq.health()
      seq.checkOrigin(health.origin, 'health route')
      const c = await seq.challenge(identity.id)
      if (c.origin !== health.origin) {
        throw new Error('this sequencer disagrees with itself about which origin it is')
      }
      seq.checkOrigin(c.origin, 'challenge')
      await seq.authenticate(identity.id, signChallenge(c.nonce, health.origin, identity.signSk))
      // One proof does both halves: it names this ledger, this realm and this
      // member, so it cannot be lifted off one join and used for another.
      const proof = signJoinProof(keys, ledger, realm, identity.id)
      const redeemed = await seq.redeem(ledger, realm, inviteSignPk, proof)
      if (redeemed.inviteBoxPk.toLowerCase() !== toHex(keys.boxPk)) {
        throw new Error('this invite was sealed to a different key than the link carries')
      }
      // The inviter the server names has to be the one the link named. The link
      // is the one authenticated channel a newcomer has, and this key is what
      // they pin as the admin whose checkpoints and grants are worth anything.
      if (redeemed.inviterSignPk.toLowerCase() !== invite.inviterSignPk) {
        throw new Error('this invite was made by somebody other than the link says')
      }
      // The realm key was sealed to the invite; it is unsealed here and sealed
      // again to this identity, so the server never sees it either way.
      const realmKey = unwrapKey(redeemed.wrappedKey, keys.boxPk, keys.boxSk)
      // And it is the key the link says it is. Without this the sealed key is
      // whatever the server put there: `crypto_box_seal` is anonymous, so a
      // sequencer can seal a key of its own to the invite's public half.
      if (realmKeyHash(realmKey) !== invite.keyHash) {
        throw new Error('the key this invite opens is not the one the link names')
      }
      // This member's own agreement key, published with their own signature,
      // before anything is sealed to it — including by them.
      await publishOwnBoxPk(seq, identity, ledger)
      const mine = await verifiedBoxPk(seq, ledger, identity.id)
      const wrapped = wrapKey(realmKey, mine)
      // The grant a joiner writes is the one case where a grant's issuer is its
      // holder, and it is sound because the key inside it is one they already
      // hold: the invite handed it to them, and re-sealing it to themselves
      // adds nothing they did not have.
      const joined = await seq.join(ledger, realm, {
        inviteSignPk,
        proof,
        wrappedKey: wrapped,
        signature: signGrant(
          identity.signSk,
          ledger,
          realm,
          redeemed.generation,
          identity.id,
          redeemed.role,
          wrapped,
        ),
      })
      // Which order this is. A genesis at position 1 is accepted by the fold on
      // its author's signature alone, and that signature proves only that *some*
      // member wrote it — so a member of this realm plus any sequencer willing
      // to serve their chain could decide the whole of a joiner's initial state,
      // including who administers the realm, which makes the takeover
      // self-sustaining. The link's author knew what their order begins with and
      // the fragment never reached a server, so this compares a number the
      // inviter knew against a number the sequencer cannot choose: the envelope
      // hash is one every reader recomputes for itself.
      //
      // `none` is a link made before there was any entry to name, and it has to
      // match a sequencer that is still serving an empty order — otherwise
      // somebody has put a beginning there since the link was written.
      const offered = await genesisOffered(seq, ledger)
      if (offered !== invite.genesisHash) {
        throw new Error(
          invite.genesisHash === noGenesis
            ? 'this link was made for a ledger with nothing in it yet, and this sequencer is ' +
              'already serving an order: it is not the one the person who invited you meant. ' +
              'Ask them for a fresh link.'
            : `this link says the ledger begins with entry ${invite.genesisHash} and this ` +
              `sequencer's begins with ${offered}: it is not serving the order the person who ` +
              'invited you meant. Ask them for a fresh link.',
        )
      }
      const ref: RealmRef = {
        sequencer: seq.base,
        ledger,
        realm,
        inviterSignPk: invite.inviterSignPk,
        generation: joined.generation,
        keyHash: sha256Hex(realmKey),
        // Empty when the link said `none`: there is no digest to compare
        // against, and the first entry this browser sees is the one it will
        // start from. A digest is kept and re-checked on every session open.
        genesisHash: invite.genesisHash === noGenesis ? '' : invite.genesisHash,
        keyGenerations: {},
      }
      // Saved before anything is written to the log: from here the invite is
      // spent, so a failure further down has to leave something that reloading
      // can pick up rather than a key nobody can find again.
      if (guest) saveGuestIdentity(identity)
      else saveIdentity(identity, passphrase)
      saveRealmRef(ref)
      window.history.replaceState(null, '', '/')
      // The sequencer now holds a grant, which is what let this part through;
      // the realm's own history still says nothing about the newcomer. These
      // two operations are that sentence, and until they land there is no purse
      // here to contribute out of.
      const session: RealmSession = {
        seq,
        identity,
        ledger,
        realm,
        keys: new Map([[joined.generation, realmKey]]),
        trustedInviter: invite.inviterSignPk,
        genesisHash: invite.genesisHash === noGenesis ? '' : invite.genesisHash,
      }
      const introduced = await submit(
        session,
        joined.generation,
        selfIntroduction(session, trimmed),
      )
      if (introduced.error !== null) {
        throw new Error(
          `you were let in, but the realm did not take your introduction: ${introduced.error}. ` +
            'Reload this page to go in anyway.',
        )
      }
      onJoined(identity, ref)
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  return (
    <Shell title={realm}>
      {error && <div className="error">{error}</div>}
      <div className="card">
        <div className="card-head">you have been invited to {realm}</div>
        <div className="card-body">
          <div className="muted">
            Accepting makes a key pair in this browser and hands its public half to the
            sequencer. The secret in the link opens the realm key once; it is then sealed again to
            your own key, so the server holds something only you can open.
          </div>
          <div className="muted">
            Your name is then written into the realm itself, with a purse of your own, because
            spending the invite told the sequencer you are here and told the ledger nothing.
          </div>
          <div className="row">
            <label className="field" style={{ flex: '1 1 260px' }}>
              What the others should call you
              <input
                autoComplete="nickname"
                placeholder="your name"
                value={name}
                onChange={(e) => setName(e.target.value)}
              />
            </label>
          </div>
          <div className="row">
            <label className="field" style={{ flex: '1 1 260px' }}>
              A passphrase of at least twelve characters
              <input
                type="password"
                autoComplete="new-password"
                placeholder="twelve characters or more"
                value={passphrase}
                disabled={guest}
                onChange={(e) => setPassphrase(e.target.value)}
              />
            </label>
          </div>
          <div className="row">
            <label className="field">
              <span>
                <input
                  type="checkbox"
                  checked={guest}
                  onChange={(e) => setGuest(e.target.checked)}
                />{' '}
                just this visit, no passphrase
              </span>
            </label>
          </div>
          <div className="muted">
            Without a passphrase the keys live in this tab only, in the clear, and are gone when
            it closes. That is the weaker option, and it is the right one for a single weekend.
          </div>
          {replacing && (
            <>
              <div className="error">
                This browser already holds an identity. Accepting a second invitation makes a new
                key pair and writes it over the old one — and the grants on the old realm are
                sealed to a public key whose secret half would then be gone. There is no export
                and no way back.
              </div>
              <div className="row">
                <label className="field">
                  <span>
                    <input
                      type="checkbox"
                      checked={confirmed}
                      onChange={(e) => setConfirmed(e.target.checked)}
                    />{' '}
                    replace the identity stored here
                  </span>
                </label>
              </div>
            </>
          )}
          <div className="row">
            <button
              className="btn"
              disabled={
                busy ||
                name.trim() === '' ||
                !confirmed ||
                (!guest && passphrase.length < 12)
              }
              onClick={() => void accept()}
            >
              {busy ? 'Joining…' : 'Accept the invitation'}
            </button>
          </div>
        </div>
      </div>
    </Shell>
  )
}

/* ------------------------------------------------------------------ */
/* Unlocking a stored identity                                         */
/* ------------------------------------------------------------------ */

function Unlock({ onOpened }: { onOpened: (identity: Identity) => void }) {
  const [passphrase, setPassphrase] = useState('')
  const [error, setError] = useState<string | null>(null)

  const open = () => {
    try {
      onOpened(loadIdentity(passphrase))
    } catch {
      setError('that passphrase does not open the identity stored here')
    }
  }

  return (
    <Shell title="Resources">
      {error && <div className="error">{error}</div>}
      <div className="card">
        <div className="card-head">unlock</div>
        <div className="card-body">
          <div className="row">
            <label className="field" style={{ flex: '1 1 260px' }}>
              Passphrase
              <input
                type="password"
                autoComplete="current-password"
                value={passphrase}
                onChange={(e) => setPassphrase(e.target.value)}
                onKeyDown={(e) => {
                  if (e.key === 'Enter') open()
                }}
              />
            </label>
          </div>
          <div className="row">
            <button className="btn" onClick={open} disabled={passphrase === ''}>
              Open
            </button>
          </div>
        </div>
      </div>
    </Shell>
  )
}

/* ------------------------------------------------------------------ */
/* The realm                                                           */
/* ------------------------------------------------------------------ */

function RealmScreen({ identity, realmRef }: { identity: Identity; realmRef: RealmRef }) {
  const { realm } = realmRef
  const [session, setSession] = useState<RealmSession | null>(null)
  const [generation, setGeneration] = useState(0)
  const [view, setView] = useState<RealmView | null>(null)
  const [error, setError] = useState<string | null>(null)
  const [busy, setBusy] = useState(false)
  const [verifier, setVerifier] = useState('sodium')
  const [pinDropped, setPinDropped] = useState<string | null>(null)

  useEffect(() => {
    let live = true
    void (async () => {
      try {
        const opened = await openSession(new Sequencer(), identity, realmRef)
        if (live) setVerifier(opened.verifier)
        if (!live) return
        const first = await loadRealm(opened.session)
        // A grant signed by somebody this client had no prior reason to trust
        // is taken provisionally — the key opens the realm, which is how the
        // realm's own account of who administers it can be read at all — and
        // then checked against that account. A stranger's key is not a view.
        //
        // `trustedAuthor` is the same question the checkpoints go through, and
        // it is asked here against the replayed state: the pinned inviter counts
        // only while that state records nobody as an admin.
        if (!trustedAuthor(opened.session, first.state, opened.grant.grantedBy)) {
          throw new Error(
            `the key you were handed was granted by ${opened.grant.grantedBy.slice(0, 12)}…, ` +
              'who does not administer this realm; nothing here has been shown',
          )
        }
        // A generation downgrade is a ledger frozen at the last rotation, shown
        // under a status line that says everything verified. The sequencer can
        // serve an *older* grant — validly signed when it was issued — and
        // everything written since decrypts to nothing and is filed as
        // unreadable. The realm's own record of its generation is what settles it.
        const record = first.state.realms.get(realm) ?? null
        if (record === null) {
          if (opened.grant.grantedBy !== identity.id) {
            throw new Error(
              'this realm has no record of itself in what you can read, and the key you ' +
                'were handed was granted by somebody else; ask for a checkpoint',
            )
          }
        } else if (record.generation !== opened.grant.generation) {
          throw new Error(
            `this realm is at key generation ${record.generation} and you were handed a key ` +
              `for generation ${opened.grant.generation}; ask to be re-granted, because ` +
              'everything written since the rotation is unreadable to this browser',
          )
        }
        if (!live) return
        const pin = pinStillAdmin(opened.session, first.state)
        setPinDropped(
          pin === false && opened.session.trustedInviter !== null
            ? opened.session.trustedInviter
            : null,
        )
        setSession(opened.session)
        setGeneration(opened.generation)
        setView(first)
      } catch (e) {
        if (live) setError(e instanceof Error ? e.message : String(e))
      }
    })()
    return () => {
      live = false
    }
  }, [identity, realmRef, realm])

  const state: State = view?.state ?? emptyState()

  const budgets = useMemo(
    () => sortedValues(state.budgets).map((b) => b.budget),
    [state],
  )
  const [chosen, setChosen] = useState<string | null>(null)
  const budget: Budget | null =
    budgets.find((b) => b.id === chosen) ?? budgets[0] ?? null

  const act = useCallback(
    async (ops: Op[]) => {
      if (session === null) return
      setBusy(true)
      setError(null)
      try {
        const result = await submit(session, generation, ops, view?.state ?? null)
        setView(result.view)
        if (result.error !== null) setError(result.error)
      } catch (e) {
        setError(e instanceof Error ? e.message : String(e))
      } finally {
        setBusy(false)
      }
    },
    [session, generation, view],
  )

  if (error !== null && view === null) {
    return (
      <Shell title={realm}>
        <div className="error">{error}</div>
      </Shell>
    )
  }

  if (view === null) {
    return (
      <Shell title={realm}>
        <div className="muted">Reading the realm…</div>
      </Shell>
    )
  }

  const rejected = view.events.filter((e) => e.status === 'rejected' || e.status === 'disagreed')

  // A reader that cannot read every part of this realm between where it started
  // and the head refuses to display the realm rather than folding around the
  // gap: what it would show is not a ledger anybody wrote. The way out is a
  // checkpoint whose author this client trusts and whose position is past the
  // parts it cannot open — not a best effort.
  //
  // `unverified` is the word for this state, and it is the node's: `GET realms`
  // and `resources sync status` mark a realm whose projection folds around a
  // hole exactly that way. A node still shows such a realm under the mark; this
  // client shows nothing of it, which is the stronger half of the same rule.
  if (view.gap !== null) {
    return (
      <Shell title={realm}>
        <div className="error">{gapMessage(view.gap)}</div>
        <div className="card">
          <div className="card-head">{realm} is unverified, so nothing is shown for it</div>
          <div className="card-body">
            <div className="muted">
              Folding around a part you cannot open would put a number on this screen that
              nobody wrote: every part before a key rotation is skipped, and what is left
              reads like a different ledger. No checkpoint can be published for a realm in
              this state and nobody else's can be checked against it. Ask somebody who
              administers {realm} to publish a checkpoint at a position past entry{' '}
              {view.gap.seq}, or to re-grant you the keys for the generations you are missing.
            </div>
          </div>
        </div>
        <Ledger view={view} />
      </Shell>
    )
  }

  return (
    <Shell
      title={budget ? shortName(budget) : realm}
      status={
        <>
          <span>
            verified and applied up to seq {view.verifiedUpTo}
            {view.head.seq > view.verifiedUpTo ? ` of ${view.head.seq}` : ''}
          </span>
          {view.checkpointSeq > 0 && <span>from a checkpoint at {view.checkpointSeq}</span>}
          {rejected.length > 0 && <span>{rejected.length} rejected</span>}
          {realmRef.inviterSignPk !== '' && (
            <span className="mono">invited by {realmRef.inviterSignPk.slice(0, 12)}…</span>
          )}
          <span className="mono">you are {identity.id.slice(0, 12)}…</span>
        </>
      }
    >
      {error && <div className="error">{error}</div>}
      {pinDropped !== null && (
        <div className="error">
          This browser pinned <span className="mono">{pinDropped.slice(0, 12)}…</span> when it
          accepted the invite link, and {realm} no longer records them as an admin. That key is
          not trusted here any more — for grants or for checkpoints — and anything this client
          believed on its word before now is worth checking with somebody who is still an admin.
        </div>
      )}
      {verifier !== 'sodium' && (
        <div className="error">
          This sequencer reports its signature scheme as <strong>{verifier}</strong>. Nothing on
          this page is signed by anybody it can check, so nothing on it is evidence of anything.
        </div>
      )}
      {view.refused !== null && (
        <div className="error">
          Entry {view.refused.seq} did not verify: {view.refused.reason}. Nothing after it is on
          this screen, and nothing will be written until it is resolved.
        </div>
      )}
      {view.snapshotNote !== null && <div className="muted">{view.snapshotNote}</div>}
      {budgets.length > 1 && (
        <nav className="tabs">
          {budgets.map((b) => (
            <button
              key={b.id}
              aria-current={budget !== null && b.id === budget.id ? true : undefined}
              onClick={() => setChosen(b.id)}
            >
              {shortName(b)}
            </button>
          ))}
        </nav>
      )}
      {budget === null ? (
        <div className="card">
          <div className="card-head">nothing shared here yet</div>
          <div className="card-body">
            <div className="muted">
              This realm has no budget in the part of it you can read. Once somebody opens one
              and adds a cost it appears here.
            </div>
          </div>
        </div>
      ) : (
        <BudgetView
          // Switching budgets starts again: the half-typed cost and the open
          // receipt both belonged to the one being left.
          key={budget.id}
          budget={budget}
          state={state}
          identity={identity}
          realm={realm}
          session={session}
          busy={busy}
          act={act}
        />
      )}
      <Ledger view={view} />
    </Shell>
  )
}

/* ------------------------------------------------------------------ */
/* One budget                                                          */
/* ------------------------------------------------------------------ */

function BudgetView({
  budget,
  state,
  identity,
  realm,
  session,
  busy,
  act,
}: {
  budget: Budget
  state: State
  identity: Identity
  realm: string
  session: RealmSession | null
  busy: boolean
  act: (ops: Op[]) => Promise<void>
}) {
  const [amount, setAmount] = useState('')
  const [what, setWhat] = useState('')
  const [when, setWhen] = useState('')
  const [formError, setFormError] = useState<string | null>(null)
  // Which receipt is open, by the hash the ledger calls it. Nothing is fetched
  // until one is, which is the whole point of holding only the hash in the
  // order: a client that never opens a receipt never downloads one.
  const [receipt, setReceipt] = useState<string | null>(null)

  const acc = budgetAccount(budget, state)
  const bridge =
    accountsSorted(state).find((a) => a.bridgeOf === identity.id && a.realm === realm) ?? null
  const costs = budgetCosts(budget, state)
  // What people have said was theirs. A cost several of them take is split
  // equally between them when the budget is divided; one nobody takes is
  // divided by the weights, the way every cost is until somebody says otherwise.
  const record = state.budgets.get(budget.id) ?? null
  const takers = (t: Transaction): string[] =>
    (record?.claims ?? []).filter((c) => c.txn === t.id).map((c) => c.member)
  const took = (t: Transaction): boolean => takers(t).includes(identity.id)
  const nameOfMember = (m: string): string =>
    state.members.get(m)?.name ?? `${m.slice(0, 8)}…`
  const take = (t: Transaction) =>
    act([{ tag: 52, kind: 'claimCost', budget: budget.id, txn: t.id }])
  const giveBack = (t: Transaction) =>
    act([{ tag: 53, kind: 'releaseCost', budget: budget.id, txn: t.id, member: identity.id }])
  const stand = standings(budget, state, eur)
  const claims = budgetClaims(budget, state).filter((c) => c.state === 'pending')
  const undivided = remaining(budget, state, eur)
  const held = budgetBalance(budget, state, eur)

  const mine = (t: Transaction): boolean =>
    bridge !== null && t.postings.some((p) => p.account === bridge.id && p.amount.minor < 0n)

  const isUndivided = (t: Transaction): boolean => undivided.some(([u]) => u.id === t.id)

  const paidBy = (t: Transaction): string => {
    const leg = t.postings.find((p) => p.amount.minor < 0n)
    if (leg === undefined) return '—'
    const a = accountOfId(state, leg.account)
    if (a === null) return '—'
    if (bridge !== null && a.id === bridge.id) return 'you'
    return partyOfId(state, a.owner)?.name ?? a.name
  }

  const total = (t: Transaction): string => {
    const leg = acc === null ? undefined : t.postings.find((p) => p.account === acc.id)
    return leg ? render({ commodity: leg.amount.commodity, minor: leg.amount.minor }) : '—'
  }

  const addCost = async () => {
    setFormError(null)
    if (acc === null) {
      setFormError('this budget has no account in the part of the realm you can read')
      return
    }
    if (bridge === null) {
      setFormError('you have no account of your own in this realm yet')
      return
    }
    let minor: bigint
    try {
      minor = parseAmount(amount, eur).minor
    } catch (e) {
      setFormError(e instanceof Error ? e.message : String(e))
      return
    }
    if (minor <= 0n) {
      setFormError('a cost is an amount that was spent')
      return
    }
    const date = (when === '' ? null : dateOfIso(when)) ?? today()
    const blank = { party: null, note: null, origin: null, tag: null }
    const txn: Transaction = {
      id: freshId(),
      date,
      payee: what.trim() === '' ? null : what.trim(),
      narration: what.trim(),
      state: 'posted',
      postings: [
        { account: acc.id, amount: { commodity: eur, minor }, ...blank } as Posting,
        { account: bridge.id, amount: { commodity: eur, minor: -minor }, ...blank } as Posting,
      ],
      labels: [],
      source: { kind: 'manual', actor: identity.id },
      attachments: [],
      items: null,
    }
    await act([{ tag: 15, kind: 'putTransaction', txn }])
    setAmount('')
    setWhat('')
    setWhen('')
  }

  const withdraw = (t: Transaction) => act([{ tag: 16, kind: 'deleteTransaction', id: t.id }])

  /**
   * Marking a claim met is one operation, not two.
   *
   * It used to be a `putTransaction` for the payment and a `resolveClaim`
   * against it, and that composition asked the wrong person for rights: one leg
   * of the payment lands in the *other* party's account, which nobody but its
   * owner or the realm's admin may write. `payClaim` is the single decision —
   * either end of the claim may take it — and nothing about the payment is the
   * author's to choose, because the amount and both accounts are the claim's.
   */
  const markMet = (claim: Transaction) =>
    act([{ tag: 51, kind: 'payClaim', claim: claim.id, payment: freshId(), date: today() }])

  return (
    <>
      <div className="statusline">
        <span>{costs.length} cost(s)</span>
        {held.minor !== 0n && <span>{render(held)} not divided up yet</span>}
        {budget.closed && <span>closed</span>}
      </div>

      <div className="grid-2">
        {stand.map((s) => (
          <div className="stat" key={s.owner}>
            <div className="k">{s.name}</div>
            <div className="v">{render(s.amount)}</div>
            <div className="muted" style={{ fontSize: 12 }}>
              {s.amount.minor === 0n
                ? 'square'
                : s.amount.minor > 0n
                  ? 'has spent less than their share'
                  : 'has spent more than their share'}
            </div>
          </div>
        ))}
        {stand.length === 0 && <div className="muted">Nothing divided up yet.</div>}
      </div>

      {claims.length > 0 && (
        <div className="card">
          <div className="card-head">still to settle</div>
          <div className="table-wrap">
            <table>
              <thead>
                <tr>
                  <th>what</th>
                  <th className="num">amount</th>
                  <th>by</th>
                  <th />
                </tr>
              </thead>
              <tbody>
                {claims.map((c) => (
                  <tr key={c.id}>
                    <td>{c.narration}</td>
                    <td className="num">
                      <strong>{render(claimAmount(c))}</strong>
                    </td>
                    <td className="mono muted">{dateToIso(c.date)}</td>
                    <td>
                      <button
                        className="btn quiet"
                        disabled={busy}
                        onClick={() => void markMet(c)}
                      >
                        mark met
                      </button>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <div className="card-body">
            <div className="muted">
              These are the payments that would leave everybody square. Nothing here has happened
              yet; marking one met records the payment beside it.
            </div>
          </div>
        </div>
      )}

      {!budget.closed && (
        <div className="card">
          <div className="card-head">add something you paid for</div>
          <div className="card-body">
            {formError && <div className="error">{formError}</div>}
            <div className="row">
              <label className="field" style={{ flex: '1 1 200px' }}>
                What
                <input
                  type="text"
                  placeholder="the taxi"
                  value={what}
                  onChange={(e) => setWhat(e.target.value)}
                />
              </label>
              <label className="field" style={{ flex: '0 1 120px' }}>
                How much
                <input
                  type="text"
                  inputMode="decimal"
                  placeholder="42.50"
                  value={amount}
                  onChange={(e) => setAmount(e.target.value)}
                />
              </label>
              <label className="field">
                When
                <input type="date" value={when} onChange={(e) => setWhen(e.target.value)} />
              </label>
            </div>
            <div className="row">
              <button
                className="btn"
                disabled={busy || amount.trim() === ''}
                onClick={() => void addCost()}
              >
                Add it
              </button>
            </div>
            <div className="muted">
              What you paid goes in beside everyone else's and is set against your own share when
              the costs are divided up. The figures above only move once somebody divides it up.
            </div>
            <div className="muted">
              Marking a cost <em>mine</em> says you bear it rather than everybody: several people
              marking one split it equally between them, and a cost nobody marks is divided by
              the shares. Nothing moves until it is divided, so you can change your mind.
            </div>
          </div>
        </div>
      )}

      <div className="card">
        <div className="card-head">everything shared so far</div>
        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th>date</th>
                <th>what</th>
                <th>paid by</th>
                <th className="num">amount</th>
                <th>whose</th>
                <th />
              </tr>
            </thead>
            <tbody>
              {costs.map((t) => (
                <tr key={t.id}>
                  <td className="mono">{dateToIso(t.date)}</td>
                  <td>{t.payee ?? t.narration}</td>
                  <td>{paidBy(t) === 'you' ? <strong>you</strong> : paidBy(t)}</td>
                  <td className="num">{total(t)}</td>
                  <td className="muted">
                    {takers(t)
                      .map((m) => (m === identity.id ? 'you' : nameOfMember(m)))
                      .join(', ')}
                  </td>
                  <td>
                    {!budget.closed && (
                      <button
                        className="btn quiet"
                        style={{ padding: '2px 9px', marginRight: 6 }}
                        disabled={busy}
                        onClick={() => void (took(t) ? giveBack(t) : take(t))}
                        title={
                          took(t)
                            ? 'Take it off your share'
                            : 'Say this one was yours: a cost several people take is split ' +
                              'equally between them'
                        }
                      >
                        {took(t) ? 'not mine' : 'mine'}
                      </button>
                    )}
                    {t.attachments.map((sha, i) => (
                      <button
                        key={sha}
                        className="btn quiet"
                        style={{ padding: '2px 9px', marginRight: 6 }}
                        aria-expanded={receipt === sha}
                        onClick={() => setReceipt(receipt === sha ? null : sha)}
                      >
                        {t.attachments.length > 1 ? `receipt ${i + 1}` : 'receipt'}
                      </button>
                    ))}
                    {mine(t) && isUndivided(t) && !budget.closed && (
                      <button
                        className="btn quiet"
                        style={{ padding: '2px 9px' }}
                        disabled={busy}
                        onClick={() => void withdraw(t)}
                        aria-label={`remove ${t.payee ?? t.narration}`}
                      >
                        ×
                      </button>
                    )}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          {costs.length === 0 && <div className="empty">Nothing yet.</div>}
        </div>
        <div className="card-body">
          <div className="muted">
            Only a cost of yours that has not been divided up yet can be withdrawn. Once it has
            been, taking it back would change what somebody was told they owed.
          </div>
        </div>
      </div>

      {receipt !== null && (
        <Receipt
          sha={receipt}
          file={state.blobs.get(receipt)?.file ?? null}
          session={session}
          onClose={() => setReceipt(null)}
        />
      )}
    </>
  )
}

/* ------------------------------------------------------------------ */
/* One receipt                                                         */
/* ------------------------------------------------------------------ */

/**
 * The picture behind a cost, fetched when somebody asks for it.
 *
 * The order carries only the file's hash, its size and its type; the bytes sit
 * on the sequencer as ciphertext under a different hash, sealed under a key of
 * their own that is itself sealed under the realm key. `fetchBlob` does all
 * three checks — the ciphertext against the name the metadata gives it, the
 * key against what it was sealed under, and the plaintext against the hash the
 * ledger calls the file — so what is on the screen is what the ledger recorded
 * and not what the server felt like sending.
 *
 * The object URL is revoked when this goes away, and the plaintext itself is
 * kept for the life of the tab and never written anywhere.
 */
function Receipt({
  sha,
  file,
  session,
  onClose,
}: {
  sha: string
  file: Attachment | null
  session: RealmSession | null
  onClose: () => void
}) {
  const [url, setUrl] = useState<string | null>(null)
  const [error, setError] = useState<string | null>(null)

  useEffect(() => {
    let live = true
    let made: string | null = null
    setUrl(null)
    setError(null)
    void (async () => {
      if (session === null) return
      if (file === null) {
        setError('this cost names a file that is not in the part of the realm you can read')
        return
      }
      try {
        const bytes = await fetchBlob(session, file)
        if (!live) return
        // A copy, so the object URL does not alias the cached plaintext, and an
        // `ArrayBuffer` rather than a view because `Blob` will not take one.
        const buffer = bytes.buffer.slice(
          bytes.byteOffset,
          bytes.byteOffset + bytes.byteLength,
        ) as ArrayBuffer
        // Never the ledger's own string. `file.mime` was chosen by whoever
        // registered the blob, a `blob:` URL inherits this page's origin, and
        // "open link in a new tab" navigates to it — so a "receipt" whose bytes
        // are HTML and whose type says `text/html` would run script here, with
        // the stored identity, the session token and the live realm key in
        // reach. Anything off the list is handed over as bytes to save.
        made = URL.createObjectURL(new Blob([buffer], { type: blobTypeFor(file.mime) }))
        setUrl(made)
      } catch (e) {
        if (live) setError(e instanceof Error ? e.message : String(e))
      }
    })()
    return () => {
      live = false
      if (made !== null) URL.revokeObjectURL(made)
    }
  }, [sha, file, session])

  const name = safeFileName(file?.origName ?? null, sha)
  const inline = file !== null && renderedInline(file.mime)
  return (
    <div className="card">
      <div className="card-head">
        {name}
        <button className="btn quiet" style={{ padding: '2px 9px' }} onClick={onClose}>
          close
        </button>
      </div>
      <div className="card-body">
        {error !== null && <div className="error">{error}</div>}
        {error === null && url === null && <div className="muted">Fetching it…</div>}
        {url !== null &&
          (inline ? (
            <img
              src={url}
              alt={name}
              style={{ maxWidth: '100%', borderRadius: 6, display: 'block' }}
            />
          ) : (
            <>
              <a href={url} download={name}>
                save it
              </a>
              <div className="muted" style={{ fontSize: 12 }}>
                {file === null ? '' : `A ${file.mime} is not something this page will render, `}
                so it is handed over as bytes to save rather than opened here.
              </div>
            </>
          ))}
        {file !== null && (
          <div className="muted" style={{ fontSize: 12 }}>
            <span className="mono">{sha.slice(0, 16)}…</span> · {file.mime} · {file.bytes} bytes ·
            decrypted here, and checked against the hash the ledger records
          </div>
        )}
      </div>
    </div>
  )
}

/**
 * The media types this page will render, and nothing else.
 *
 * `Attachment.mime` is a string whoever registered the blob chose, and it
 * passes every hash check in `blobs.ts` — those are about integrity, not about
 * type. An allow-list is the only defence that does not depend on guessing what
 * a browser will do with an unexpected one.
 */
const renderedTypes = ['image/png', 'image/jpeg', 'image/gif', 'image/webp']

/** Whether a receipt of this type is put on the screen rather than handed over. */
export function renderedInline(mime: string): boolean {
  return renderedTypes.includes(mime.trim().toLowerCase())
}

/**
 * The type a `Blob` is built with.
 *
 * `image/svg+xml` is deliberately not on the list even though `<img>` will not
 * run its script, because the same URL opened in a tab is a document.
 */
export function blobTypeFor(mime: string): string {
  return renderedInline(mime) ? mime.trim().toLowerCase() : 'application/octet-stream'
}

/**
 * A name safe to put in a `download` attribute.
 *
 * `origName` is another string from the ledger, so path separators and control
 * characters are stripped rather than trusted, and an empty result falls back
 * to the hash the file is filed under.
 */
export function safeFileName(origName: string | null, sha: string): string {
  const cleaned = (origName ?? '')
    // eslint-disable-next-line no-control-regex
    .replace(/[\u0000-\u001f\u007f/\\]/g, '')
    .replace(/^\.+/, '')
    .trim()
    .slice(0, 100)
  return cleaned === '' ? sha.slice(0, 12) : cleaned
}

function today(): { year: number; month: number; day: number } {
  const d = new Date()
  return { year: d.getFullYear(), month: d.getMonth() + 1, day: d.getDate() }
}

/* ------------------------------------------------------------------ */
/* What was read, and what was not                                     */
/* ------------------------------------------------------------------ */

function Ledger({ view }: { view: RealmView }) {
  const interesting = view.events.filter((e) => e.status !== 'applied')
  if (interesting.length === 0) return null
  return (
    <div className="card">
      <div className="card-head">verified, and not applied</div>
      <div className="table-wrap">
        <table>
          <thead>
            <tr>
              <th className="num">seq</th>
              <th>author</th>
              <th>what happened</th>
              <th>why</th>
            </tr>
          </thead>
          <tbody>
            {interesting.map((e) => (
              <tr key={e.seq}>
                <td className="num mono">{e.seq}</td>
                <td className="mono muted">{e.author.slice(0, 12)}…</td>
                <td>{e.status}</td>
                <td className="muted">{e.detail ?? ''}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <div className="card-body">
        <div className="muted">
          Every entry in this table was verified: its signature holds against its author, its
          hash was recomputed here, and it follows the entry before it. What it did not do is
          change anything. An <strong>unreadable</strong> one is encrypted under a key this
          browser does not hold, which is nobody's mistake; a <strong>rejected</strong> one was
          understood and refused on the ledger's own rules, and the sentence beside it says why;
          a <strong>duplicate</strong> carries an event id already applied. An entry that failed
          verification is not here — it stopped the fold, and the line above the page says so.
        </div>
      </div>
    </div>
  )
}
