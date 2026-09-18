import Resources.Core.Commute
import Resources.Node.Checkpoint

/-!
# Node sync

One round is a pull, then a push, then a checkpoint. Pull first, because an
event composed on top of what everybody else has already said is one the
sequencer will accept, and an event composed in ignorance is one that comes back
as a conflict. Checkpoint last, because what it commits to is where the round
left the order.

Where a node syncs, who it commits as and how the two chains are kept is
`Node/Session.lean`; what a checkpoint is and how one is published and checked
is `Node/Checkpoint.lean`.

## Who wrote what

Every entry of the remote order is authored by the key that signed its envelope,
because that is the only authorship anybody can check. A store from before
`resources identity init` is full of events authored by `self`, a member who
predates having a key, so those are not pushed at all: `sync init` writes one
fresh entry carrying the whole state instead, and everything after it is an
ordinary signed event. See `seedGenesis`.

## Where an order begins

Entry 1 of an order may be a *genesis*: one event carrying one snapshot part,
which is the state every reader of that order starts from. Everywhere else a
snapshot is a part `applyOp` refuses, so the question is only ever asked about
the first entry — and it is asked of the **envelope**, never of what this node
could open.

That distinction is the whole rule, and every implementation has to follow the
same one or two honest readers of one order hold different states and
`Checkpoint.verify` has them accusing each other of it. How many parts an
envelope carries is a fact every reader sees; which of them decrypt is a fact
about one key ring. So, at position 1:

* the envelope carries **exactly one part** → this entry is the genesis. If that
  part is readable and decodes to a snapshot, the store begins from it; if it is
  unreadable, the store begins from `State.init` and the realm is recorded in
  `event_unreadable`, because what this node holds is then a fold around
  something it never saw;
* the one part is readable and is **not** a snapshot → an ordinary event applied
  to `State.init`;
* the envelope carries **more than one part** → an ordinary event applied to
  `State.init`, whatever this node could open of it. A snapshot beside something
  else is not a beginning: the something else would have to apply either before
  or after a state that replaced everything, and neither reading is one two
  implementations would agree on.

The thin client follows the identical rule and reads it off the same two
numbers: `fromSeq === 0 && e.seq === 1 && e.parts.length === 1`, where
`e.parts` is the envelope's parts and not the ones that opened.

Which entry that is, is itself pinned. An invite link carries
`genesisFingerprint` of entry 1, `join` refuses an order that begins with
another one, and `sync.json` keeps the digest — because a signature on a genesis
proves that *some* member wrote it and nothing more, and the state it names can
say whatever its author likes about who administers what.

The digest is checked where it decides something, which is the fold and not the
handshake. `join` asks the sequencer what its order begins with, and then `pull`
asks a second time for the entries it will actually apply; the two are separate
requests and a sequencer may answer them differently, so checking only the first
checks nothing — it is the second that becomes this node's state. `pull` therefore
refuses an entry at position 1 whose fingerprint is not the pinned one, and `join`
asks `linksToGenesis` again once its first pull is done.

A node that was never told writes down the first entry 1 it meets and is pinned
to it from then on: that is `noteProgress`, it is trust on first use, and the
window it leaves is the one pull between joining and seeing an entry 1. This
binary no longer mints a link that leaves it open — `initAsAdmin` pushes what it
seeds, and `invite` refuses to write a link for an order with no first entry —
but `noGenesis` stays readable, because links written before it are still out
there. **Any other client has to backfill the same way**: the thin client keeps
`genesisHash` in its `RealmRef`, and a browser that joined on such a link and
never wrote the digest back re-derives its whole state from an unchecked entry 1
on every cold open, for ever.

## Conflicts, and the rebase that resolves most of them

A push that is refused with 409 has lost a race: somebody else's entry is where
this one was going. The node pulls, applies what it missed, and then asks two
questions about the event it was trying to place, in this order.

*Does it still do anything?* Every part is applied, in order, to the state as it
now stands. The first one the state refuses stops the push, and the message
names the event and that part, because the alternative is to write an entry
every reader will skip.

*Would the author have written the same thing?* The parts of the entries just
taken in are the operations that arrived in front of this one. For each part of
the local event, `Rebase.check` is asked whether that part is independent of
*all* of them — every readable part of every realm, not only the ones in the
part's own realm. `Core/Commute.lean` is where `rebase_sound` is stated, and it
is stated about the operations that took the state from where the event was
composed to where it is now; the node reaches that state by applying every
readable part of every intervening entry, so those are the operations the
hypothesis is about. Filtering them to one realm asked a question the theorem
does not answer, and a co-member's `deleteLabel` in another realm could move
state a pending part depended on. Asking about all of them costs a question to
the user now and then, and `Rebase.check` is conservative anyway.

If both answers are yes the event is offered again with `basedOn` set to the new
head, unchanged and without asking anybody. If either is no the push stops and
says which event conflicts and which of its parts. That is deliberately
conservative: `Rebase.check` refuses pairs that would in fact have commuted, and
a refused rebase costs a question to the user while a wrong one costs the
ledger. Two writers adding unrelated transactions never notice each other; two
writers numbering an invoice or dividing a budget are told.

## Being re-keyed

A revoke or a rotation moves a realm onto a new key, and the first this node
hears of it is usually a part it cannot open. So a pull that meets a part in a
realm it holds an *older* generation of asks the sequencer for its own grant at
the new one, unwraps it, files it and goes on. A node that was the one revoked
asks and is told no — there is no grant to fetch — and the parts stay
unreadable, which is exactly what being put out means.

## A node with no sequencer

Everything here is reached only when `sync.json` says where to sync. Without it
the store is exactly what phase 2 left: `Ctx.commit` appends to the local log,
`remote_seq` stays `NULL` on every row, and nothing ever asks.
-/

open Lean SQLite

namespace Resources
namespace Node

/-! ## Where an order begins -/

/--
The digest of an order's first entry that an invite link carries.

Sixteen bytes of the SHA-256 of the *hash* of entry 1's envelope: a digest of a
digest, because what is being fingerprinted is a hex string every node that has
taken that entry in already holds. Half a SHA-256 for the same reason
`realmKeyHash` is half of one — a link is typed and pasted by people, and this
is a check against a value the reader has in hand rather than a commitment
somebody must be unable to find a collision against.
-/
def genesisFingerprint (envelopeHash : String) : String :=
  toHex (take (Sha256.hash envelopeHash.toUTF8) 16)

/--
Whether an entry is the order's genesis, and what state it begins from.

The rule the module header states, as one function, so that the node and anybody
reading it are looking at the same three lines. `pos` is the position this entry
takes in the local log, `envParts` is how many parts its **envelope** carried,
and `e` is what this node could open of it.

`envParts` rather than `e.parts.length` is the whole of it. `e` has been through
a key ring, so a two-part envelope carrying a snapshot in a realm you hold and
something else in a realm you do not arrives here as a one-part event — and a
reader who holds both keys sees two. Reading the count off `e` therefore makes
"does this order have a genesis" a question about who is asking, which is the
one thing a shared order cannot afford: the two readers hold different states
from entry 1 onwards and `Checkpoint.verify` has each accusing the other.
-/
def genesisAt? (pos envParts : Nat) (e : Event) : Option State :=
  if pos == 1 && envParts == 1 then e.genesis? else none

/-- What a link says about an order that had no entry when it was written. -/
def noGenesis : String := "none"

/--
The fingerprint of entry 1 of the order this store holds, or `noGenesis`.

Two places it can come from and they are the same number. A node that has taken
entry 1 in has the envelope's hash in its own `event` table and fingerprints it.
A node that started from a checkpoint has no row there at all — that is the whole
of what starting from a checkpoint means — and still knows which entry the order
begins with, because its own link said so and `sync.json` kept it. Only a store
that has never been told and has never seen one answers `noGenesis`.
-/
def genesisHere (ctx : Ctx) : IO String := do
  match ← Checkpoint.remoteHashAt ctx 1 with
  | some h => return genesisFingerprint h
  | none =>
    let settings ← Settings.load ctx.cfg
    if settings.genesisHash.isEmpty then return noGenesis else return settings.genesisHash

/--
Whether this node holds the order unbroken from its first entry up to a
position.

Two questions, and both have to be yes. The entry at position 1 has to be the
one this node was told the order begins with — when it was told anything — and
every position from there to `upTo` has to be one this node has a row for. A
commitment about `upTo` is then a commitment about a chain this node can follow
back to a beginning it recognises, which is the only thing that makes it more
than its author's word.

A store that started from a checkpoint has no row at position 1 and answers no,
which is correct and is the case `seedFromOffer` is written around.
-/
private def linksToGenesis (ctx : Ctx) (upTo : Nat) : IO Bool := do
  if upTo == 0 then return false
  let some first ← Checkpoint.remoteHashAt ctx 1 | return false
  let settings ← Settings.load ctx.cfg
  unless settings.genesisHash.isEmpty || settings.genesisHash == genesisFingerprint first do
    return false
  let held ← Db.scalarInt ctx.db
    s!"SELECT COUNT(*) FROM event WHERE remote_seq >= 1 AND remote_seq <= {upTo}"
  return held.toNat == upTo

/--
Whether a state offered as an order's beginning says nothing about any realm but
one.

A commitment is its author's word about the realm they signed for, and nothing
else: `Checkpoint.offered?` asks whether this node trusts them *on that realm*,
and that is the only authority anybody in this system has. What a genesis does,
though, is replace every table — so an offer whose state carried an account in
another realm, or a record for another realm at all, would be one member's word
about a realm they were never in, taken as the whole truth about it.

The self realm is the exception and has to be: `State.init` records it before a
single part has been folded, so it is in every projection of every realm,
including this one. It carries no accounts, which is why the accounts are held to
the stricter rule.
-/
private def confinedTo (st : State) (realm : String) : Bool :=
  st.realms.toList.all (fun (id, _) => id == realm || id == Realm.selfId.val)
    && st.accounts.toList.all (fun (_, a) => a.realm.val == realm)

/-! ## Realms on the sequencer -/

/--
Makes sure the sequencer knows a realm and that this node holds its key there.

Three cases, and only the third is a refusal. The realm may be new, in which
case this node creates it, makes a key and grants it to itself. It may already
be one this node holds a grant on, which is the ordinary case and costs one
request. Or it may exist under somebody else's administration with no grant for
this node — and then the node has written into a realm it was never let into,
which nothing here can fix.
-/
def ensureRealm (s : Session) (realm : String) : IO Unit := do
  let mine ← Transport.json s.transport (Transport.get (s.route ["realms"]))
  let held := (mine.getArr?.toOption.getD #[]).filterMap fun g =>
    if Sync.strField? g "realm" == realm then
      some ((g.getObjValAs? Nat "generation").toOption.getD 0)
    else none
  if let some generation := held[0]? then
    -- A grant we hold already: keep the key we were given filed under its
    -- generation, once it is clear who issued it. An unchecked grant here would
    -- be the key everything this node writes next is sealed under.
    if (← Keys.get s.keys realm generation).isNone then
      let grant ← Transport.json s.transport
        (Transport.get (s.route ["realms", realm, "grants", s.member]))
      let some g := GrantRecord.ofJson? grant
        | throw <| IO.userError s!"the grant on realm '{realm}' is not in a shape this \
                                   binary reads"
      if g.realm != realm || g.generation != generation then
        throw <| IO.userError s!"the sequencer offered a grant on realm '{realm}' at another \
                                 generation than the one it says this node holds"
      match ← s.useGrant g with
      | .ok _ => pure ()
      | .error why => throw <| IO.userError why
    return
  let (code, _) ← Transport.result s.transport
    (Transport.send "POST" (s.route ["realms"]) (Json.mkObj [("realm", realm)]))
  if code != 201 && code != 409 then
    throw <| IO.userError s!"the sequencer would not take realm '{realm}'"
  let (generation, _) ← Keys.create s.keys realm
  let wrapped ← Keys.wrapFor s.keys s.identity.boxPk realm generation
  -- This node is the realm's admin and the grant is to itself, so it signs it:
  -- a grant nobody signed is a grant a sequencer could have written.
  let signature := Identity.signHex s.suite s.identity
    (Sync.grantBytes s.ledger realm generation s.member "admin" wrapped)
  let (grantCode, grant) ← Transport.result s.transport
    (Transport.send "POST" (s.route ["realms", realm, "grants", s.member])
      (Json.mkObj [("wrappedKey", Json.str (Sync.toBase64 wrapped)), ("role", "admin"),
                   ("grantedBy", s.member), ("signature", signature)]))
  if grantCode != 201 then
    throw <| IO.userError s!"this node holds no key for realm '{realm}' on the sequencer: \
                            {Transport.errorOf (.json grantCode grant)}"

/-! ## Pushing -/

/-- What a push came to. -/
structure Pushed where
  /-- How many local events are now on the sequencer. -/
  pushed : Nat := 0
  /-- How many times the head had moved under us. -/
  conflicts : Nat := 0
  /-- Why the push stopped, when it did. -/
  blocked : Option String := none
  deriving Inhabited

private structure PendingRow where
  seq : Int64
  bytes : ByteArray
  deriving Row

/--
The operations one node missed, as realm and operation.

The realm travels beside each operation because the caller reports it, not
because it filters on it: the rebase asks about all of them.

These are read out of the local log rather than kept from the pull, because the
pull is a parameter of `pushWith` and may have been any number of rounds: what
matters is everything that landed between the position this event was composed
onto and the position the order has reached now. Entries this node could not
read carry no parts and so contribute nothing — which is the honest answer,
since a part in a realm it holds no key for cannot touch anything it can write.
-/
private def interveningOps (ctx : Ctx) (from_ upto : Nat) : IO (List (RealmId × Op)) := do
  if upto ≤ from_ then return []
  let rows ← Db.rows PendingRow ctx.db
    s!"SELECT seq, bytes FROM event
       WHERE remote_seq > {from_} AND remote_seq <= {upto} ORDER BY remote_seq"
  let mut out : List (RealmId × Op) := []
  for row in rows do
    if let some e := (Codec.decode row.bytes : Option Event) then
      out := out ++ e.parts.map fun p => (p.realm, p.op)
  return out

/--
Why an event cannot simply be offered again over what arrived in front of it.

Both questions the module comment states, in that order, and the answer names
the part that failed: an event with seven parts and one bad one is a sentence
about that one.
-/
private def conflict? (st : State) (intervening : List (RealmId × Op)) (e : Event) :
    Option String := Id.run do
  let mut s := st
  for (p, i) in e.parts.zipIdx do
    match applyOp s e.author p.realm p.op with
    | .ok (next, _) => s := next
    | .error why =>
      return some s!"event {e.id} conflicts with what the sequencer has: its part {i}, \
                     in realm '{p.realm.val}', {why}"
  for (p, i) in e.parts.zipIdx do
    -- Every intervening operation, in every realm this node could read. See the
    -- header: the state this part is being replayed onto is the one all of them
    -- left behind, so all of them are what it has to be independent of.
    let arrived := intervening.map (·.2)
    unless Rebase.check arrived p.op do
      return some s!"event {e.id} cannot be replayed over what the sequencer has: its part {i}, \
                     in realm '{p.realm.val}', is not independent of what arrived in front of it"
  return none

/--
How many times one event is offered before the node gives up on it.

Every attempt past the first costs a pull, and a node that loses this many races
in a row is not racing but starving.
-/
private def attempts : Nat := 8

/-- Records where the sequencer put one of our events. -/
private def recordPlacement (ctx : Ctx) (localSeq : Nat) (head : Sync.Head) : IO Unit :=
  Db.exec ctx.db s!"UPDATE event SET remote_seq = {head.seq}, remote_hash = {Db.lit head.hash}
    WHERE seq = {localSeq}"

/--
Offers every local event the sequencer has not seen, oldest first.

`pull` is a parameter rather than a call so that this function says what it does
and not how the other half of a round works: a conflict is resolved by taking in
what was missed, and taking in is `Sync.pull`.
-/
def pushWith (s : Session) (pull : IO (Option String)) : IO Pushed := do
  let rows ← Db.rows PendingRow s.ctx.db
    "SELECT seq, bytes FROM event WHERE remote_seq IS NULL ORDER BY seq"
  let mut out : Pushed := {}
  let mut ensured : Array String := #[]
  for row in rows do
    let localSeq := row.seq.toInt.toNat
    let some e := (Codec.decode row.bytes : Option Event)
      | return { out with blocked := some s!"local event {localSeq} cannot be decoded" }
    for p in e.parts do
      unless ensured.contains p.realm.val do
        ensureRealm s p.realm.val
        ensured := ensured.push p.realm.val
    let mut attempt := 0
    let mut placed := false
    while !placed && attempt < attempts do
      attempt := attempt + 1
      let head ← remoteHead s.ctx
      let env ← Envelope.compose s.suite s.keys s.ledger e (head.seq + 1) head.hash head.seq
      let (code, payload) ← Transport.result s.transport
        (Transport.send "POST" (s.route ["events"]) env.toJson)
      if code == 201 then
        -- Where it landed is the sequencer's answer; what it hashes to is this
        -- node's own arithmetic. The two are compared, because a sequencer whose
        -- stored hash is not the hash of what it was handed is one whose next
        -- `prevHash` nobody can chain onto.
        let headJson := (payload.getObjVal? "head").toOption.getD Json.null
        let acceptedSeq := (headJson.getObjValAs? Nat "seq").toOption.getD (head.seq + 1)
        let stated := Sync.strField? headJson "hash"
        if acceptedSeq != env.seq then
          return { out with blocked := some s!"the sequencer took entry {env.seq} and says it \
                                               put it at {acceptedSeq}" }
        if stated != env.hash then
          return { out with blocked := some s!"the sequencer stored entry {env.seq} under a \
                                               hash that is not the hash of what it was given" }
        recordPlacement s.ctx localSeq { seq := env.seq, hash := env.hash }
        out := { out with pushed := out.pushed + 1 }
        placed := true
      else if code == 409 then
        out := { out with conflicts := out.conflicts + 1 }
        if let some why ← pull then
          return { out with blocked := some why }
        -- What landed between where this event was going and where the order
        -- has got to is exactly what it has to be independent of.
        let arrived ← interveningOps s.ctx head.seq (← remoteHead s.ctx).seq
        if let some why := conflict? (← s.ctx.state.get) arrived e then
          return { out with blocked := some why }
      else
        return { out with blocked := some (Transport.errorOf (.json code payload)) }
    unless placed do
      let msg := s!"event {e.id} keeps losing the race for the head"
      return { out with blocked := some msg }
  return out

/-! ## Pulling -/

/-- What a pull came to. -/
structure Pulled where
  /-- How many entries were decrypted and applied. -/
  applied : Nat := 0
  /-- How many entries were already this node's own. -/
  mine : Nat := 0
  /-- How many entries carried nothing this node holds a key for. -/
  unreadable : Nat := 0
  /-- How many entries were coherent bytes saying incoherent things. -/
  rejected : Array (Nat × String) := #[]
  /-- Where the pull stopped and why, when something did not open or did not follow. -/
  refused : Option (Nat × String) := none
  /-- How many realm keys were fetched again because a realm had been re-keyed. -/
  rekeyed : Nat := 0
  /-- How many of the sequencer's checkpoints said what this node says. -/
  checkpointsAgreed : Nat := 0
  /-- Realms whose checkpoint this node disagrees with: realm, entry, and why. -/
  checkpointMismatch : Array (String × Nat × String) := #[]
  /-- Where the remote order stands for this node now. -/
  seq : Nat := 0
  deriving Inhabited

/-- An event with no parts: what an entry this node cannot read leaves behind. -/
private def placeholder (env : Sync.Envelope) (why : String) : Event :=
  { id := s!"{why}:{env.ledger}:{env.seq}", author := ⟨env.author⟩, composedAt := "",
    basedOn := env.seq, parts := [] }

/--
Stores one entry of the remote order locally and projects what it changed.

The local log gains a row whose bytes are the parts this node could read, and
that row carries the remote position and hash beside its own. Both chains
therefore run through it, which is what lets `resources rebuild` replay a synced
store without a sequencer in sight.

The first entry of the local log is where a genesis may be read, and the only
one: `Core.stepAt` takes the position this row is about to be written at, so an
event of one snapshot part at position 1 is the state this store begins from and
the same event anywhere else is a part `applyOp` refuses. That is why the
position is read *before* the append rather than after it.

`envParts` is how many parts the *envelope* carried, and it is the reason this
argument exists at all. `e` is what this node could decrypt, so asking `e` how
many parts it has asks a question about a key ring: an envelope of two parts,
one a snapshot in a realm you hold and one anything at all in a realm you do
not, looks like a one-part genesis to you and like an ordinary event to everyone
who can read both. Two honest readers of one order would then hold different
states — which is precisely what positional genesis was introduced to prevent,
and what `Checkpoint.verify` would report as one of them lying. So the rule is
read off the envelope, exactly as the thin client reads it, and the header says
what it is.

A genesis empties the projection first. A snapshot *replaces* the state, and the
changes it produces only ever write rows — so a store that held something the
snapshot does not would keep it in its tables while its state had forgotten it,
and the two would disagree from then on. The reset follows the rule rather than
the presence of the operation, or a refused snapshot would empty the tables
under a state that still held everything.

The remote hash is the one this node computed. In version 2 the envelope hash
digests each part's `cipherHash` rather than its ciphertext, so it is the same
value for a reader who was handed every part and one who was handed none — which
is what makes recomputing it possible at all, and what makes the stored value
evidence rather than a note of what a server once said.
-/
private def absorb (s : Session) (remote : Sync.Head) (e : Event) (envParts : Nat)
    (missed : List String := []) : IO Nat := do
  let before ← s.ctx.state.get
  let (seq, _) ← EventLog.head s.ctx.db
  let pos := seq + 1
  -- An envelope of anything but one part is an ordinary event wherever it
  -- stands, so `step` and not `stepAt`: only a one-part envelope is even
  -- offered to the positional rule.
  let (after, changes) := if envParts == 1 then stepAt pos before e else step before e
  s.ctx.atomically do
    let (localSeq, _) ← EventLog.append s.ctx.db e
    recordPlacement s.ctx localSeq remote
    -- What was *not* read is stored beside what was, because a projection of a
    -- realm is only comparable with another node's when nothing in that realm
    -- was missed. See `Node/Checkpoint.lean`.
    --
    -- One row per realm, rather than the realms joined into one column with
    -- commas: a realm id is a name a member chose, and a name that is joined
    -- into a list has to be taken back out of it again — by splitting on a
    -- character it may contain, and by matching a `LIKE` pattern it may itself
    -- be a pattern for. Neither question is asked here any more.
    for realm in missed do
      Db.exec s.ctx.db s!"INSERT OR IGNORE INTO event_unreadable (seq, realm)
        VALUES ({localSeq}, {Db.lit realm})"
    -- Only when the snapshot really applied: at position 1, and carried by an
    -- event that is nothing else. Resetting the tables for a refused operation
    -- would leave them saying something the state does not.
    if (genesisAt? pos envParts e).isSome then
      Project.reset s.ctx.db
    for c in changes do
      Project.apply s.ctx.db c
  s.ctx.state.set after
  return changes.length

/--
Starts a store from a checkpoint somebody published, instead of from the first
entry of the order.

A newcomer let into a realm that has been re-keyed cannot read the entries that
predate the key it was given, and the first of them is the genesis the whole
ledger stands on. Folding what it *can* read gives an empty realm and a stream of
operations refused by rights it has no way to see — so the way in is a snapshot,
taken from an author it has a reason to trust and checked in every particular
before it is used. `Checkpoint.offered?` is that check.

Two things bound what the snapshot may say, and both exist because a genesis
*replaces everything*.

It has to be confined to its own realm. `Checkpoint.offered?` settles that the
author is trusted **on this realm**, which is the only authority anybody has
here, and an admin of R who wanted to lie about R could have written that lie
into R anyway — so a state that speaks about R is bounded by what its author
could have done. A state that also names accounts in S is not: it would put its
author in charge of a realm they administer nothing in, and `Session.trusts`
would then read that very state back as the reason to believe them. So every
account in the offer has to be in this realm, and the only other realm it may
record is the self one, which `State.init` puts there before anything is folded.

And the fallback — taking the snapshot on the pinned inviter's word, because the
chain back to entry 1 cannot be walked — is a *first* join's and no other's. A
join always empties the store, so a second join's `seedFromOffer` looks exactly
like a first's from inside; what tells them apart is `sync.json`, where the pins
of every realm this node has been let into are kept. If one of them names another
realm then this node has read a realm before, its projection of that realm is
about to be replaced by a state a different person chose, and the honest thing is
to refuse and pull from the beginning instead. Then the only way in is the one
that needs nobody's word: `linksToGenesis`.

What lands here is one local event, the same shape `seedGenesis` writes: one
part, in that realm, carrying the state. So the log this node keeps replays to
the state it holds, from `State.init`, exactly as every other node's does — and
the row carries the remote position and the hash the commitment named, so the
next entry chains onto it. The entries the snapshot covers are ones this node
never saw, and it does not pretend otherwise: it never claims to have read them,
it claims to have been told what they came to by somebody it trusts.
-/
def seedFromOffer (s : Session) (realm : String) (offer : Checkpoint.Offer) : IO Unit := do
  -- Position 1 or nothing. A genesis is read off the first entry of the order
  -- and nowhere else, so a store with a log of its own is one this cannot seed:
  -- `join` empties it first (`adoptLedger`), and a caller that has not is asking
  -- for a state its own log would not replay to.
  let (seq, _) ← EventLog.head s.ctx.db
  if seq != 0 then
    throw <| IO.userError "a checkpoint can only start a store whose log is empty; \
                           this one has a history of its own"
  -- What is written at position 1 is the whole of what this store says, so it
  -- may only say what its author was entitled to say: this realm, and the
  -- records `State.init` makes before anybody has written anything.
  unless confinedTo offer.state realm do
    throw <| IO.userError s!"the commitment offered for realm '{realm}' carries entities in \
                             other realms, and a commitment is only its author's word about \
                             the realm they signed for"
  -- What a snapshot buys is not having to read the order, and what that costs
  -- is the anchor: a state that replaces everything, taken from an author whose
  -- authority this node can only read *out of that very state*, is a state its
  -- author may write freely. So either this node can follow the chain from the
  -- entry its link named up to the one committed to, or the commitment has to be
  -- the pinned inviter's own — the one key this node has an out-of-band reason
  -- to believe — and the store writes down that it never saw the beginning.
  unless ← linksToGenesis s.ctx offer.seq do
    let settings ← Settings.load s.ctx.cfg
    -- And the inviter's word is only good enough the first time. A node that has
    -- been let into a realm before is a node whose projection of that realm this
    -- would silently replace, on the word of somebody who administers none of it.
    -- Two ways of asking whether this is the first: what the store still holds,
    -- which after `adoptLedger` is `State.init` and its self realm and nothing
    -- else, and what `sync.json` remembers, which a join does not empty. The
    -- second is the one that catches a second join, because the first join's
    -- realm is gone from the store by the time this runs.
    let firstJoin := settings.pinned.all (fun p => p.realm == realm)
      && (← s.ctx.state.get).realms.toList.all (fun (id, _) => id == Realm.selfId.val)
    unless firstJoin do
      throw <| IO.userError s!"the commitment offered for realm '{realm}' cannot be linked back \
                               to the entry this node's invite named, and this store has been \
                               let into a realm before: a snapshot taken on one inviter's word \
                               would replace what the other realm says. Read the order instead."
    unless settings.pinned.contains { realm, member := offer.author } do
      throw <| IO.userError s!"the commitment offered for realm '{realm}' is signed by \
                               {offer.author}: this node cannot link it back to the entry its \
                               invite named, and it was not the inviter it pinned who signed it"
    Settings.save s.ctx.cfg { settings with genesisSeen := false }
  let e : Event :=
    { id := ← freshId, author := ⟨offer.author⟩, composedAt := ← nowStamp, basedOn := 0,
      parts := [{ realm := ⟨realm⟩, op := .snapshot offer.state }] }
  let before ← s.ctx.state.get
  let (after, changes) := stepAt 1 before e
  s.ctx.atomically do
    let (localSeq, _) ← EventLog.append s.ctx.db e
    recordPlacement s.ctx localSeq { seq := offer.seq, hash := offer.headHash }
    Project.reset s.ctx.db
    for c in changes do
      Project.apply s.ctx.db c
  s.ctx.state.set after

/--
Makes sure this node holds whatever keys an entry's parts were sealed under, as
far as it is entitled to.

Only realms this node already holds *some* generation of are asked about: a
realm it has never been let into is none of its business, and asking would be
one request per entry per stranger.
-/
private def refreshKeys (s : Session) (env : Sync.Envelope) : IO Nat := do
  let mut fetched := 0
  for p in env.parts do
    if (← Keys.get s.keys p.realm p.generation).isNone then
      if (← Keys.latest s.keys p.realm).isSome then
        if ← fetchKey s p.realm p.generation then fetched := fetched + 1
  return fetched

/--
Takes in everything the sequencer has that this node has not.

The chain is checked before anything is decrypted, against hashes this node
computed: each entry has to sit at the position after the last one and name it
by the hash this node worked out for it, starting from the `remote_hash` it
stored. Then the signature, then each received part against the digest that
signature covers. An entry that fails any of them is where the pull stops — the
node keeps its position, so a fetch that was corrupted in flight costs a round
and not the ledger.

An entry arriving at a position this node already holds has to be the one it
holds, byte for byte, or the pull refuses. Counting it as "mine" without looking
was how a sequencer could serve everybody else something the author never wrote
and have the author see nothing amiss.
-/
def pull (s : Session) : IO Pulled := do
  let mut out : Pulled := {}
  let mut head ← remoteHead s.ctx
  out := { out with seq := head.seq }
  let mut more := true
  let mut rounds := 0
  while more && rounds < 1000 do
    rounds := rounds + 1
    let fetched ← Transport.json s.transport
      (Transport.get (s.route ["events"]) [("since", toString head.seq)])
    let entries := ((fetched.getObjVal? "events").bind Json.getArr?).toOption.getD #[]
    if entries.isEmpty then
      more := false
    for entry in entries do
      let env ← IO.ofExcept (Sync.Envelope.ofJson? entry)
      -- Never the `hash` field the fetch carried. The chain is what says an
      -- entry belongs where it was served, and a chain checked against the
      -- server's own assertions is a chain that server can rewrite at will.
      let hash := env.hash
      if env.seq != head.seq + 1 then
        out := { out with refused := some (env.seq, "the remote order skips a position") }
        more := false
        break
      if env.prevHash != head.hash then
        out := { out with refused := some (env.seq, "the remote chain does not follow") }
        more := false
        break
      match ← Db.row? String s.ctx.db
          s!"SELECT remote_hash FROM event WHERE remote_seq = {env.seq}" with
      | some stored =>
        -- An entry this node already has. Being handed a *different* one at the
        -- same position is a sequencer rewriting the order under everybody who
        -- has not looked, so it stops the pull rather than being counted.
        if stored != hash then
          out := { out with refused := some (env.seq, "the entry at this position is not the \
                                                       one this node stored there") }
          more := false
          break
        out := { out with mine := out.mine + 1 }
      | none =>
        -- The pin, against the entry this node is about to fold rather than
        -- against a copy of it fetched in another request. `join` asks the
        -- sequencer once what its order begins with and this loop asks again;
        -- the two are the sequencer's to answer differently, and it is this one
        -- that decides the state — an entry at position 1 is a genesis, and a
        -- genesis replaces everything. Whoever signed it only ever proved that
        -- some member wrote it, so this digest is the whole of what stands
        -- between a co-member and a ledger of their own invention.
        if env.seq == 1 then
          let pinned := (← Settings.load s.ctx.cfg).genesisHash
          unless pinned.isEmpty || genesisFingerprint hash == pinned do
            out := { out with refused := some (env.seq, s!"this order begins with an entry \
              this node was not told it begins with: the link said {pinned}, and entry 1 \
              here fingerprints to {genesisFingerprint hash}") }
            more := false
            break
        out := { out with rekeyed := out.rekeyed + (← refreshKeys s env) }
        let realmsOf := env.parts.map (·.realm)
        match ← Envelope.read s.suite s.keys s.ledger env with
        | .refused why =>
          out := { out with refused := some (env.seq, why) }
          more := false
          break
        | .rejected why =>
          -- Nothing in it is applied, so every realm it touched is one this
          -- node cannot project: an entry it refused to read is a hole in each.
          discard <| absorb s { seq := env.seq, hash } (placeholder env "rejected")
            env.parts.length realmsOf
          out := { out with rejected := out.rejected.push (env.seq, why) }
        | .ok opened =>
          match opened.event with
          | none =>
            discard <| absorb s { seq := env.seq, hash } (placeholder env "unreadable")
              env.parts.length opened.unreadableRealms
            out := { out with unreadable := out.unreadable + 1 }
          | some e =>
            discard <| absorb s { seq := env.seq, hash } e env.parts.length
              opened.unreadableRealms
            out := { out with applied := out.applied + 1,
                              unreadable := out.unreadable + opened.unreadable }
      head := { seq := env.seq, hash }
      out := { out with seq := env.seq }
  -- Whatever the sequencer holds a checkpoint for is checked against this node's
  -- own projection at the same entry. By determinism the two agree unless one of
  -- them is wrong, so a mismatch is carried back rather than swallowed.
  for realm in ← Checkpoint.heldRealms s do
    match ← Checkpoint.verify s realm head with
    | .agreed _ _ => out := { out with checkpointsAgreed := out.checkpointsAgreed + 1 }
    | .mismatch seq why =>
      out := { out with checkpointMismatch := out.checkpointMismatch.push (realm, seq, why) }
    | .absent | .skipped _ => pure ()
  return out

/--
Writes down where the order has got to, and what it begins with.

`remoteSeq` in `sync.json` is a convenience — the `event` table's columns are
the truth — but `genesisHash` is not: it is what a later commitment is anchored
to, and this is the moment a node that made its own order first has an entry 1
to fingerprint. It is filled in once and never moved, because a value that
changed when the order changed would anchor nothing.
-/
private def noteProgress (ctx : Ctx) : IO Unit := do
  let current ← Settings.load ctx.cfg
  let genesisHash ←
    if current.genesisHash.isEmpty then
      match ← Checkpoint.remoteHashAt ctx 1 with
      | some h => pure (genesisFingerprint h)
      | none => pure ""
    else pure current.genesisHash
  Settings.save ctx.cfg { current with remoteSeq := (← remoteHead ctx).seq, genesisHash }

/-! ## A round -/

/-- What one round came to: what came in, what went out, and what was committed to. -/
structure Round where
  /-- What the pull took in. -/
  pulled : Pulled := {}
  /-- What the push offered. -/
  pushed : Pushed := {}
  /-- One outcome per realm this node holds a key for. -/
  checkpoints : Array (String × Checkpoint.Outcome) := #[]
  deriving Inhabited

/--
Pull, then push, then checkpoint: one round of sync.

The checkpoint comes last because it commits to a position, and the position it
should commit to is the one the round has just reached. It is also the only part
of a round that can fail without the round having failed: publishing is a
courtesy to whoever reads next, and a sequencer that refuses one has still taken
every entry.
-/
def round (s : Session) : IO Round := do
  let pulled ← pull s
  let pushed ← pushWith s do
    let again ← pull s
    return (again.refused.map fun (seq, why) => s!"entry {seq}: {why}")
  noteProgress s.ctx
  let checkpoints ← Checkpoint.publishAll s (← remoteHead s.ctx)
  return { pulled, pushed, checkpoints }

/-- Publishes a checkpoint for one realm, or for every realm this node holds a key for. -/
def checkpoint (s : Session) (realm : Option String := none) :
    IO (Array (String × Checkpoint.Outcome)) := do
  let head ← remoteHead s.ctx
  match realm with
  | none => Checkpoint.publishAll s head
  | some r =>
    let out := #[(r, ← Checkpoint.publish s r head)]
    Checkpoint.recordLocal s.ctx
    return out

/-- Push on its own, pulling when the head moves under us. -/
def push (s : Session) : IO Pushed := do
  let out ← pushWith s do
    let again ← pull s
    return (again.refused.map fun (seq, why) => s!"entry {seq}: {why}")
  noteProgress s.ctx
  return out

/-! ## Setting a node up -/

/--
Writes the entry a shared ledger begins with: this store, entire, as one event.

The same move `Store/Load.lean` makes when a database that already existed
adopts a log, made a second time for a second order. It has to be a fresh event
rather than the local log replayed, because of who wrote that log: everything
composed before `resources identity init` is authored by `self`, a member that
predates having a key at all, and an envelope is authored by the key that signs
it. A reader rebuilds an event's author from the envelope — which is the honest
reading, since it is the only claim anybody proved — so a pre-identity event
pushed as it stands would arrive attributed to a member who, at that point in
the replay, was not yet allowed to do what it does.

So the local history stays local, and the remote order opens with one entry
saying "this is where we came in", signed by the key that will sign everything
after it.
-/
def seedGenesis (ctx : Ctx) : IO Unit := do
  let st ← ctx.state.get
  let e : Event :=
    { id := ← freshId, author := ctx.member, composedAt := ← nowStamp, basedOn := 0,
      parts := [{ realm := Realm.selfId, op := .snapshot st }] }
  -- Nothing is projected: the tables already hold exactly this state, which is
  -- where it was read from.
  ctx.atomically (discard <| EventLog.append ctx.db e)

/--
Creates this store's ledger on the sequencer and takes the keys for it.

The node that runs this is the ledger's first member and its admin, and the
realm it creates is the one its own books live in. What is already here is not
exported, re-entered or replayed: it becomes the first entry of the new order,
and everything after it is an ordinary event.

And that entry is pushed here rather than left for the next round, which is a
security property and not a convenience. An invite link names the entry the order
begins with, and a founder whose genesis is still sitting unpushed in the local
log has no such entry to name — so `invite` would have had to write `noGenesis`,
and a link carrying `noGenesis` is a link with no pin at all. The documented
sequence is `identity init`, `sync init`, `invite`, with nothing in between; so
`sync init` is where the order gains its first entry.
-/
def initAsAdmin (ctx : Ctx) (suite : CryptoSuite) (keys : Keyring) (transport : Transport)
    (sequencer ledger : String) : IO Session := do
  let s : Session := { ctx, suite, keys, transport, ledger }
  -- No agreement key here, not even this node's own. A member publishes theirs
  -- through one route, with their own signature over it, and there being exactly
  -- one such route is most of what makes the key worth sealing anything to.
  let (code, payload) ← Transport.result transport
    (Transport.send "POST" ["ledgers"] (Json.mkObj [("ledger", ledger)]))
  if code != 201 && code != 409 then
    throw <| IO.userError (Transport.errorOf (.json code payload))
  if code == 409 then
    let (memberCode, _) ← Transport.result transport (Transport.get (s.route ["members"]))
    if memberCode != 200 then
      throw <| IO.userError s!"ledger '{ledger}' is on that sequencer already and this node is \
                              not a member of it"
  s.publishBoxPk
  ensureRealm s Realm.selfId.val
  markPrehistory ctx
  seedGenesis ctx
  -- Whatever was already written down is kept, as a join keeps it: a pin and a
  -- member's key generation are facts about other people, not about which
  -- sequencer this store happens to be pointed at. Written before the push,
  -- because the push is what fills `genesisHash` in.
  Settings.save ctx.cfg
    { ← Settings.load ctx.cfg with sequencer, ledger, member := s.member }
  let placed ← push s
  if let some why := placed.blocked then
    throw <| IO.userError s!"this ledger was made on the sequencer and the entry it begins \
                             with was not taken: {why}"
  return s

/-! ## Invites -/

/-- Base64 as a URL fragment carries it: `-` and `_` for `+` and `/`, and no padding. -/
def toBase64Url (bs : ByteArray) : String :=
  ((Sync.toBase64 bs).replace "+" "-").replace "/" "_" |>.replace "=" ""

/-- Inverse of `toBase64Url`. -/
def ofBase64Url? (s : String) : Option ByteArray :=
  Sync.ofBase64? ((s.replace "-" "+").replace "_" "/")

/--
The short digest of a realm key an invite link carries.

Sixteen bytes of the SHA-256 of the key itself. It is the joiner's only way of
telling the key their inviter wrapped from a key the sequencer substituted:
`crypto_box_seal` is anonymous, so the sealed blob in an invite says nothing
about who sealed it, and a joiner who simply unwrapped whatever came back would
encrypt everything they ever write under a key the server chose. The digest
travels in the fragment, which never reaches the server.

Half a SHA-256 is short because a link is typed and pasted by people. It is a
check on a key that the holder of the link's secret already has in their hand,
not a commitment anybody has to be unable to forge a collision against.
-/
def realmKeyHash (key : ByteArray) : String := toHex (take (Sha256.hash key) 16)

/--
What an invite link's fragment carries.

Six fields, because a joiner has six things to settle before they can use what
comes back: which ledger and which realm they are joining, the secret that
proves they hold the invite, the inviter's signing key — which they pin as a
reason to trust that realm's grants and commitments until they have replayed its
membership for themselves — the digest of the realm key, which is what says the
sealed key they are handed is the one that was meant, and the digest of the
order's first entry, which is what says the whole ledger they are handed is the
one that was meant.

That last one is sixteen bytes and it closes the door the rest of this design
would otherwise leave open. The first entry of an order decides the entire
initial state of a reader who has no checkpoint they can verify, and the only
thing anybody can check about it is that *a* member signed it. A member holding
a realm key, plus any sequencer willing to serve their chain, could therefore
write a genesis naming themselves the realm's admin and hand a joiner a ledger
of their own invention — self-sustaining, because every later grant and
commitment is then checked against a membership that genesis itself stated. The
inviter knows what the order really begins with, and the fragment never reaches
a server, so they say so.
-/
structure Invitation where
  /-- The ledger the realm belongs to. -/
  ledger : String
  /-- The realm being offered. -/
  realm : String
  /-- The seed of the invite's two key pairs. -/
  secret : ByteArray
  /-- The inviter's member id, which is their signing key. -/
  inviter : String
  /-- `realmKeyHash` of the key the invite wraps. -/
  keyHash : String
  /-- `genesisFingerprint` of entry 1 of the order, or `noGenesis` when there is none yet. -/
  genesisHash : String
  deriving Inhabited

/--
The fragment of a link that offers `inv`.

`base64url(ledger ':' realm ':' secret ':' inviterSignPk ':' keyHash ':'
genesisHash)`, with the secret rendered as hex rather than raw bytes so that the
whole fragment is text a colon can be split on. Version 1 put the raw secret
last precisely to dodge that question, and there are four fields after it now.
-/
def Invitation.fragment (inv : Invitation) : String :=
  toBase64Url (String.intercalate ":"
    [inv.ledger, inv.realm, toHex inv.secret, inv.inviter, inv.keyHash,
     inv.genesisHash]).toUTF8

/--
Offers a realm to somebody who is not a member yet.

The invite's secret seeds both of its key pairs, and only its public halves
reach the sequencer: the signing one because a joiner has to prove they hold the
secret, the agreement one because the realm key is wrapped to it. The secret
itself goes in the link's fragment, which a browser never sends to a server, and
so do the two things that make the sealed key checkable — who sealed it, and
what it should turn out to be.

There is a third, and it is the one this refuses without. An order this node has
no first entry for is an order a link cannot name, and a link that names none is
a link whose holder folds whatever entry 1 turns up. That used to be the ordinary
outcome of the documented setup — `sync init` seeded a genesis into the local log
and pushed nothing, so the very next command minted a pinless link — and it is
now two refusals: `initAsAdmin` pushes, and this says so when somebody has
managed to get here anyway.
-/
def invite (s : Session) (realm expires : String) (role : String := "viewer") :
    IO String := do
  -- First, and before the sequencer is told anything: a refusal here costs
  -- nothing, and a refusal after the POST would have spent an invite.
  let genesisHash ← genesisHere s.ctx
  if genesisHash == noGenesis then
    throw <| IO.userError "this ledger has no first entry yet, so a link would have nothing to \
                           say about where its order begins — and a joiner would take whichever \
                           entry the sequencer served first. Run 'resources sync' and offer the \
                           realm again."
  let secret ← s.suite.randomBytes CryptoSuite.seedSize
  let (signPk, _) := s.suite.signSeedKeypair secret
  let (boxPk, _) := s.suite.boxSeedKeypair secret
  let some (generation, key) ← Keys.latest s.keys realm
    | throw <| IO.userError s!"this node holds no key for realm '{realm}'"
  let wrapped ← Keys.wrapFor s.keys boxPk realm generation
  discard <| Transport.json s.transport (Transport.send "POST"
    (s.route ["realms", realm, "invites"])
    (Json.mkObj [("inviteSignPk", toHex signPk), ("inviteBoxPk", toHex boxPk),
                 ("wrappedKey", Json.str (Sync.toBase64 wrapped)), ("role", role),
                 ("expires", expires)]))
  return Invitation.fragment
    { ledger := s.ledger, realm, secret, inviter := s.member, keyHash := realmKeyHash key,
      genesisHash }

/--
Reads an invite link's fragment back.

The realm is whatever is between the first field and the last four, joined
again, so a realm id containing a colon survives the round trip; the ledger is
the first field, because that one is a name somebody chose and the outermost
thing here.
-/
def readInvite? (fragment : String) : Option Invitation := do
  let bytes ← ofBase64Url? fragment
  let text ← String.fromUTF8? bytes
  let fields := text.splitOn ":"
  let n := fields.length
  guard (n ≥ 6)
  let genesisHash ← fields[n - 1]?
  let keyHash ← fields[n - 2]?
  let inviter ← fields[n - 3]?
  let secretHex ← fields[n - 4]?
  let ledger ← fields[0]?
  let secret ← Sync.ofHex? secretHex
  guard (secret.size == CryptoSuite.seedSize)
  guard (Sync.isMemberId inviter.toLower)
  guard (!keyHash.isEmpty)
  -- The sixth field has two spellings and no others: `genesisFingerprint`, which
  -- is half a SHA-256 as thirty-two lowercase hex digits, or the literal `none`
  -- from a link written before an order had a first entry. Anything else is a
  -- fragment this parser is not reading the way it was written, and a malformed
  -- value would otherwise travel as far as the comparison in `join` and be
  -- refused there with the wrong sentence. The thin client holds the field to
  -- the same two shapes (`App.tsx`), so the two parsers agree about which links
  -- exist.
  guard (genesisHash.toLower == noGenesis || Sync.isLowerHex genesisHash.toLower 32)
  let realm := String.intercalate ":" ((fields.drop 1).take (n - 5))
  return { ledger, realm, secret, inviter := inviter.toLower, keyHash := keyHash.toLower,
           genesisHash := genesisHash.toLower }

/--
The fingerprint of the entry the sequencer says this order begins with.

Computed from the envelope it serves rather than read out of any field it
states: `Envelope.hash` digests each part's `cipherHash`, so it is the same
value for a reader handed every part and one handed none, and it is the value
the author's own node wrote into the link. `noGenesis` when the order is empty
or its first entry is not at position 1, which are both "there is nothing here
that the link could have meant".
-/
private def genesisOffered (s : Session) : IO String := do
  let fetched ← Transport.json s.transport
    (Transport.get (s.route ["events"]) [("since", "0")])
  let entries := ((fetched.getObjVal? "events").bind Json.getArr?).toOption.getD #[]
  let some first := entries[0]? | return noGenesis
  let env ← IO.ofExcept (Sync.Envelope.ofJson? first)
  if env.seq != 1 then return noGenesis
  return genesisFingerprint env.hash

/--
Writes a newcomer into the realm they have just been let into.

An invite is spent on the sequencer, where keys and grants live; the ledger
hears nothing of it. So the first thing a joiner does with the key it was handed
is to say who it is in the realm's own terms — one event, two parts, both in
that realm:

* `addMember`, naming a party of its own, so that everybody reading the realm
  has a record of the person and somewhere to hang their spending;
* `grant`, of the weakest role there is, which is what opens the purse they hold
  a balance on here. The account is `Members.<name>`, under a name nothing here
  answers to yet, and whose it is comes from the member record rather than from
  the operation.

`Core/Apply.lean` takes both from the member themselves, and says why: the
sequencer accepted a part for this realm only from somebody it already holds a
grant for there, so the log is repeating a decision that has been made, in its
weakest form. The admin who invited them was a link in a browser rather than a
node composing events, and without this nothing in the log would say the
newcomer is here at all.

It happens between a pull and a push for the ordinary reason: an event is
composed against the realm as it stands, and a realm this node has not read is
one it cannot write itself into — which is also the one case where nothing is
written, along with a realm that already lists this member and has therefore
already been told.
-/
private def introduce (s : Session) (realm : String) (name : String) : IO Unit := do
  let st ← s.ctx.state.get
  let me := s.ctx.member
  match st.realm? ⟨realm⟩ with
  | none => return
  | some r => if r.isMember me then return
  let party : PartyId ← match st.member? me with
    | some m => pure m.party
    | none => do let fresh ← freshId; pure ⟨fresh⟩
  -- The name is the canonical one and nothing else: a self-grant may only make
  -- `Members.<name>`, and only when no account of that name or id is in the
  -- realm already. `Identity.freeAccountName` used to pick a free variant, which
  -- is exactly the adoption the attest door no longer allows.
  let bridge : Account :=
    { id := ⟨← freshId⟩, name := s!"Members.{name}", kind := .asset,
      owner := party, realm := ⟨realm⟩, bridgeOf := some me }
  discard <| s.ctx.commit "join"
    [.addMember { id := me, name, party }, .grant ⟨realm⟩ me .viewer bridge]
    (kind := "join") (realm := ⟨realm⟩)

/--
Spends an invite: reads the sealed key, checks it is the key the link promised,
re-seals it to this node's own agreement key, and becomes a member.

Two requests, because the key the grant has to hold is one only the joiner can
compute. The proof is the same signature in both, over bytes that name this
ledger, this realm and this member — so it admits nobody else anywhere else.

Three checks the first version did not make, and each closes the same hole from
a different side. The `inviterSignPk` the sequencer states has to be the one in
the link, or the key came from somewhere the person who sent the link did not
name. The unsealed key has to hash to the digest in the link, or it is not the
key that was meant — `crypto_box_seal` is anonymous, so a server can seal
anything to an invite's public key and a joiner who did not check would go on to
encrypt every future write under it. And the inviter is pinned in `sync.json`,
because a newcomer who has replayed nothing knows nobody, and every grant and
every checkpoint on this realm is about to arrive signed by somebody.

The grant this node writes for itself is signed by this node, in the role the
invite named. That is the one case where a grant's issuer is its holder, and it
is sound because the key inside it is one the invite already handed over.

Then a whole round, in the order a round goes: read the realm, say who has
arrived, and offer it. A join that stopped at the keys would leave a node able
to read a ledger that has never heard of it.
-/
def join (ctx : Ctx) (suite : CryptoSuite) (keys : Keyring) (transport : Transport)
    (sequencer : String) (inv : Invitation) : IO Session := do
  let ledger := inv.ledger
  let realm := inv.realm
  let s : Session := { ctx, suite, keys, transport, ledger }
  -- Read before the pull, because a pull carrying a snapshot replaces the state
  -- this store had, and the name is this node's own rather than the realm's.
  let name := (((← ctx.state.get).member? ctx.member).map (·.name)).getD "member"
  let (signPk, signSk) := suite.signSeedKeypair inv.secret
  let (_, boxSk) := suite.boxSeedKeypair inv.secret
  let proof := toHex (suite.sign signSk (Sync.joinBytes ledger realm s.member))
  let offered ← Transport.json transport (Transport.send "POST"
    (s.route ["realms", realm, "invites", toHex signPk, "redeem"])
    (Json.mkObj [("proof", proof)]))
  let statedInviter := (Sync.strField? offered "inviterSignPk").toLower
  unless statedInviter == inv.inviter do
    throw <| IO.userError s!"this invite was made by {statedInviter}, and the link says it was \
                             made by {inv.inviter}"
  let wrapped ← IO.ofExcept (Sync.bytesField offered "wrappedKey")
  let generation := (offered.getObjValAs? Nat "generation").toOption.getD 0
  let role := Sync.strField? offered "role" "viewer"
  let some key := suite.unwrapKey boxSk wrapped
    | throw <| IO.userError "the invite's sealed key does not open under the link's secret"
  unless realmKeyHash key == inv.keyHash do
    throw <| IO.userError "the key this invite handed back is not the key the link names; \
                           somebody between the inviter and here has substituted one"
  let resealed := suite.wrapKey s.identity.boxPk key
  let signature := Identity.signHex suite s.identity
    (Sync.grantBytes ledger realm generation s.member role resealed)
  discard <| Transport.json transport (Transport.send "POST" (s.route ["realms", realm, "join"])
    (Json.mkObj [("inviteSignPk", toHex signPk), ("proof", proof),
                 ("wrappedKey", Json.str (Sync.toBase64 resealed)),
                 ("role", role), ("grantedBy", s.member), ("signature", signature)]))
  Keys.put keys realm generation key
  -- Which order this is, before this store is emptied to make room for it. The
  -- envelope's hash is one every reader computes for itself, so this compares a
  -- number the link's author knew against a number the sequencer cannot choose;
  -- and doing it here means a refusal costs the invite and not the books.
  let offered ← genesisOffered s
  unless offered == inv.genesisHash do
    throw <| IO.userError s!"this link says the ledger begins with entry {inv.genesisHash} \
                             and this sequencer's begins with {offered}: it is not serving the \
                             order the person who invited you meant. Ask them for a fresh link."
  adoptLedger ctx
  let previous ← Settings.load ctx.cfg
  Settings.save ctx.cfg
    { previous with
      sequencer, ledger, member := s.member, remoteSeq := 0, genesisSeen := true,
      genesisHash := if inv.genesisHash == noGenesis then "" else inv.genesisHash }
  -- Appended, not assigned: a node let into a second realm by a second person
  -- needs both anchors, and the first realm's grants and commitments are
  -- checked against the first one until its membership has been replayed.
  Settings.pin ctx.cfg realm inv.inviter
  -- Now a member, so now there is a member record to publish a key on.
  s.publishBoxPk
  -- A realm that has been re-keyed since it began is one whose order this node
  -- cannot read from the start, so it starts from what its inviter committed to.
  if let some offer ← Checkpoint.offered? s realm then
    seedFromOffer s realm offer
  discard <| pull s
  -- And now the same question of the store rather than of the server. The check
  -- above was against an entry the sequencer served in one request; this is
  -- against the entries this node has just written down, which are the ones its
  -- state is now a fold of. A store seeded from a commitment has no entry 1 and
  -- says so in `genesisSeen`, and is the one case where there is nothing here to
  -- compare — which is exactly what `genesisSeen` is for.
  let settled ← Settings.load ctx.cfg
  if settled.genesisSeen && !settled.genesisHash.isEmpty then
    unless ← linksToGenesis ctx (← remoteHead ctx).seq do
      throw <| IO.userError s!"this sequencer served one order to the check this link made and \
                               another to the pull that followed it: what it has handed over \
                               does not run unbroken from entry {settled.genesisHash}. Nothing \
                               of it has been applied. Ask for a fresh link."
  introduce s realm name
  discard <| push s
  return s

end Node
end Resources
