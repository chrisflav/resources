import Resources.Node.Session

/-!
# Checkpoints

A checkpoint is a signed sentence: *at entry `seq` of this ledger, the state of
realm `R` was the one whose canonical bytes hash to `stateHash`, and the
envelope at that entry hashed to `headHash`*. Beside it travels the state
itself, encrypted under the realm key, so that somebody arriving later can start
from it instead of replaying the whole order.

## What exactly is committed to

The realm's *projection*: the fold of the parts written in that realm, in the
sequencer's order, up to `seq`. Not this node's whole state — that includes
realms other readers hold no key for, and two honest nodes would then commit to
different bytes for the same realm and accuse each other of lying. `Realm.projection`
is that fold, and it is deliberately a pure function of a list of events, so it
can be stated, tested and ported.

The determinism argument is the whole point. Two nodes that hold the same realm
key see exactly the same parts in that realm, in exactly the same order, and
`step` has no clock and no randomness — so they compute the same state and sign
the same hash. A disagreement is therefore never a difference of opinion: one of
the two is wrong, and saying so loudly is more useful than picking a winner.

## When a node may not check

A node that could not open every part written in a realm is missing pieces of
that realm's history, and its projection is not the thing the checkpoint commits
to. That is what the `event_unreadable` table records, one row per realm, and a
realm named in it at or before the checkpoint's position makes the check
`skipped` rather than failed. A node that has been revoked is in exactly this
position, which is why losing a key costs the ability to verify and never
produces a false accusation.

One gap this phase does not close: a node that was revoked and later let back in
was not *shown* the entries written while it was out — a fetch drops the parts of
realms the caller holds no grant on, so those parts never arrived and nothing
recorded that they were missing. Its projection of that realm is therefore
incomplete in a way it cannot see, and it would report a mismatch it is itself
the cause of. Such a node should start from a published snapshot rather than
from its own fold; making that automatic is a phase of its own.

## The framing

```
snapshot = nonce ++ seal(realmKey[generation], nonce, ad, encode state)
ad       = seg("resources/snapshot/v1") ++ seg(ledger) ++ seg(realm)
           ++ seg(generation) ++ seg(author)
commitment = seg("resources/seq/v2/checkpoint") ++ seg(ledger) ++ seg(realm)
           ++ seg(generation) ++ seg(seq) ++ seg(stateHash) ++ seg(headHash)
           ++ seg(snapshotHash)
```

`snapshotHash` is the SHA-256 of the encrypted snapshot that ships beside the
commitment. Without it the signature said nothing about the bytes it travelled
with, so a server could keep the signature and swap the snapshot, and the only
thing that would have caught it is a reader who decrypted the snapshot and
recomputed `stateHash` from it — which nothing forced them to do.

`headHash` is what ties a snapshot to the chain: it is the `prevHash` the next
envelope carries, so a reader who starts from the snapshot can join the order
without walking back to the beginning. The sequencer checks it against the
entry it stored, which is a thing only the sequencer knows.

## Whose commitment is worth checking

The sequencer stores one checkpoint per author and hands back all of them, which
is deliberate: keeping only the newest of them all let any grant holder erase
everybody else's. Which of them counts is the reader's decision, and it is the
same policy as for a grant — the author has to be this node, the inviter it
pinned when it joined, or an admin of that realm in its own replayed state.
Anybody else's commitment is `skipped` and never a `mismatch`, because the
mismatch channel is the only integrity alarm this design has and a stranger who
could set it off would make it worthless.

## What is kept locally

Every published checkpoint is also written into the local `checkpoint` table,
and so is a snapshot of everything this node can read at its own log's head. The
first is a record of what this node has signed; the second is what
`resources rebuild --from-checkpoint` starts from. Neither deletes an event.
-/

open Lean SQLite

namespace Resources

namespace Realm

/--
The state one realm's parts add up to, in the order they were written.

An event contributes the parts that name this realm and nothing else: the same
fold the ledger uses, over events trimmed to one realm. An event with no parts
in the realm is dropped entirely rather than applied empty, so that a
placeholder standing for an entry this node could not read leaves the projection
alone.

Genesis is positional here too, and the position is the realm's rather than the
order's: the genesis of a realm is the first entry that says anything about it,
so the trimmed log is handed to `Core.replay` and a snapshot at any later
position is a part `applyOp` refuses. That is the same rule every reader of this
system follows, and it has to be, or two readers of one order would disagree
about which state they were folding from.

One thing this cannot decide, and the caller has to: whether every part of the
realm between the start and the head was *readable*. A projection folded around
a part this node could not open is not a projection of that realm, and comparing
it with somebody else's would raise an alarm about a difference nobody made.
`Checkpoint.missedParts` is where that is asked, from `event_unreadable`, and a
realm with a gap is skipped rather than compared — the thin client makes the
same decision by refusing to display such a realm at all.
-/
def projection (log : List Event) (realm : RealmId) : State :=
  Resources.replay (log.filterMap fun e =>
    match e.parts.filter (fun p => p.realm == realm) with
    | [] => none
    | parts => some { e with parts })

end Realm

namespace Node

/-- The domain a snapshot's ciphertext is bound to. -/
def snapshotTag : String := "resources/snapshot/v1"

/-- The associated data a realm's snapshot is sealed under. -/
def snapshotAd (ledger realm : String) (generation : Nat) (author : String) : ByteArray :=
  Sync.segStr snapshotTag ++ Sync.segStr ledger ++ Sync.segStr realm
    ++ Sync.segNat generation ++ Sync.segStr author

namespace Checkpoint

/-! ## Reading the remote order out of the local log -/

private structure BytesRow where
  bytes : ByteArray
  deriving Row

/--
The entries of the remote order this node holds, up to a position, in order.

The local log *is* the remote log, filtered to what this node could read: every
entry it has taken in carries the remote position it arrived at. Prehistory
(`remote_seq = 0`) and events not yet pushed (`NULL`) are not part of the shared
order and are left out, which is what makes this the same list on every node.
-/
def remoteEvents (ctx : Ctx) (upTo : Nat) : IO (List Event) := do
  let rows ← Db.rows BytesRow ctx.db
    s!"SELECT bytes FROM event WHERE remote_seq >= 1 AND remote_seq <= {upTo}
       ORDER BY remote_seq"
  return rows.toList.filterMap fun r => (Codec.decode r.bytes : Option Event)

/-- The hash this node stored for the envelope at a position in the remote order. -/
def remoteHashAt (ctx : Ctx) (seq : Nat) : IO (Option String) := do
  if seq == 0 then return some ""
  Db.row? String ctx.db s!"SELECT remote_hash FROM event WHERE remote_seq = {seq}"

/-! ## Where the gaps are

`missedParts` and `gappedRealms` — the two ways of asking which realms this node
folded around — are in `Node/Session.lean` rather than here, because
`Session.trusts` has to ask the same question and this file sits above that one.
What both of them are for is the header's "When a node may not check".
-/

/-- The state a realm's parts add up to at a position in the remote order. -/
def projectionAt (ctx : Ctx) (realm : String) (upTo : Nat) : IO State := do
  return Realm.projection (← remoteEvents ctx upTo) ⟨realm⟩

/-! ## Publishing -/

/-- What was committed to, when one was. -/
structure Published where
  /-- The realm the commitment is about. -/
  realm : String
  /-- The position in the remote order it speaks for. -/
  seq : Nat
  /-- The key generation the snapshot is sealed under. -/
  generation : Nat
  /-- `Encode.hashState` of the projection. -/
  stateHash : String
  deriving Inhabited

/-- How publishing one realm's checkpoint ended. -/
inductive Outcome
  /-- The sequencer took it. -/
  | published (p : Published)
  /-- There was nothing to say: no key, an empty order, or parts this node never read. -/
  | skipped (why : String)
  /-- The sequencer would not take it. -/
  | refused (why : String)
  deriving Inhabited

/-- What an outcome says, for a person reading a round. -/
def Outcome.describe (realm : String) : Outcome → String
  | .published p => s!"{realm}  entry {p.seq}, generation {p.generation}, {p.stateHash}"
  | .skipped why => s!"{realm}  not published: {why}"
  | .refused why => s!"{realm}  refused: {why}"

/-- The realms this node holds a key for, each once, in the order the keyring lists them. -/
def heldRealms (s : Session) : IO (Array String) := do
  let mut out : Array String := #[]
  for e in ← Keys.all s.keys do
    unless out.contains e.realm do out := out.push e.realm
  return out

/--
Computes a realm's projection, seals it, signs the commitment and PUTs it.

The three refusals are three different things and are answered differently. A
realm this node holds no key for is not this node's to commit to. A realm whose
history this node has holes in is one it cannot honestly speak about — see the
header. And a sequencer that says no is a fact worth reporting, never a reason
to stop the round: a checkpoint is an optimisation for other readers, and a node
that failed to publish one has still pushed and pulled everything.
-/
def publish (s : Session) (realm : String) (head : Sync.Head) : IO Outcome := do
  let some (generation, key) ← Keys.latest s.keys realm
    | return .skipped "this node holds no key for it"
  if head.seq == 0 then return .skipped "the order is empty"
  if ← missedParts s.ctx realm head.seq then
    return .skipped "this node could not read every part written in it"
  let projected ← projectionAt s.ctx realm head.seq
  let bytes := Codec.encode projected
  let stateHash := Encode.hashState projected
  let nonce ← s.suite.randomBytes s.suite.nonceSize
  let sealed := s.suite.sealPart key nonce (snapshotAd s.ledger realm generation s.member) bytes
  let unsigned : Sync.Checkpoint :=
    { ledger := s.ledger, realm, generation, seq := head.seq, stateHash,
      headHash := head.hash, author := s.member, signature := "",
      snapshot := nonce ++ sealed }
  let c := { unsigned with
             signature := Identity.signHex s.suite s.identity unsigned.commitmentBytes }
  let (code, payload) ← Transport.result s.transport
    (Transport.send "PUT" (s.route ["realms", realm, "checkpoint"]) c.toJson)
  if code != 200 then return .refused (Transport.errorOf (.json code payload))
  Checkpoints.put s.ctx.db realm head.seq stateHash bytes
  return .published { realm, seq := head.seq, generation, stateHash }

/--
Records what this node can read of its own log, at its own head.

This is the local half of a checkpoint and has nothing to do with the sequencer:
it is the state `resources rebuild --from-checkpoint` starts from, which is why
it is the whole state rather than one realm's projection. The events it covers
are untouched.
-/
def recordLocal (ctx : Ctx) : IO Unit := do
  let (seq, _) ← EventLog.head ctx.db
  if seq == 0 then return
  let st ← ctx.state.get
  Checkpoints.put ctx.db "" seq (Encode.hashState st) (Codec.encode st)

/-- Publishes a checkpoint for every realm this node holds a key for. -/
def publishAll (s : Session) (head : Sync.Head) : IO (Array (String × Outcome)) := do
  let mut out : Array (String × Outcome) := #[]
  for realm in ← heldRealms s do
    out := out.push (realm, ← publish s realm head)
  recordLocal s.ctx
  return out

/-! ## Checking somebody else's -/

/-! ## Starting from one -/

/--
A published checkpoint this node trusts and can open: the realm's state as its
author computed it, and where in the order that was.

The `author` is kept because it is the whole reason to believe any of it. A
newcomer let into a realm that has been re-keyed cannot read the entries that
predate the key it was given — the order begins with a genesis sealed under a
generation it will never hold — so its own fold of that realm would be empty and
every operation it did read would be refused by rights it cannot see. The
snapshot is the way in, and it is worth taking only from somebody whose word
means something: the inviter pinned from the link, or an admin this node's own
state already records.
-/
structure Offer where
  /-- The position in the remote order the state stands at. -/
  seq : Nat
  /-- The hash of the envelope at that position, which the next entry chains onto. -/
  headHash : String
  /-- The realm's state as of that position. -/
  state : State
  /-- Who committed to it. -/
  author : String
  deriving Inhabited

/-- How checking a realm's checkpoint ended. -/
inductive Verdict
  /-- The sequencer holds none for this realm. -/
  | absent
  /-- It could not be checked, and why. -/
  | skipped (why : String)
  /-- It says what this node says. -/
  | agreed (seq : Nat) (stateHash : String)
  /-- It does not, and why. Two honest nodes cannot land here. -/
  | mismatch (seq : Nat) (why : String)
  deriving Inhabited

/--
Checks one of the commitments the sequencer holds for a realm.

Five claims, in the order it costs least to disbelieve them: that its author is
somebody this node trusts on this realm, that they signed the commitment — over
the snapshot that arrived with it, not one it was told about — that the entry it
names hashes to what it says, that this node has reached that entry with nothing
missing, and that the state at that entry is the state this node computes. All
but the last can be wrong without anybody being dishonest — an old checkpoint, a
node behind the order, a member this node has not seen made an admin yet — and
only the last is the one worth shouting about.
-/
private def verifyOne (s : Session) (realm : String) (head : Sync.Head) (j : Json) :
    IO Verdict := do
  let seq := (j.getObjValAs? Nat "seq").toOption.getD 0
  let generation := (j.getObjValAs? Nat "generation").toOption.getD 0
  let stateHash := Sync.strField? j "stateHash"
  let headHash := Sync.strField? j "headHash"
  let author := (Sync.strField? j "author").toLower
  let signature := (Sync.strField? j "signature").toLower
  -- Whose word this is, before what it says. A commitment signed by somebody
  -- this node has no reason to trust on this realm is not evidence of anything,
  -- and treating it as one would make the alarm attacker-controlled noise.
  unless ← s.trusts realm author do
    return .skipped s!"the commitment at entry {seq} is signed by {author}, who is not an \
                       admin of this realm as far as this node can see"
  -- The snapshot is hashed as it arrived, because the commitment covers that
  -- digest: a server that swapped the bytes and kept the signature is caught
  -- here rather than by a reader who happened to decrypt them.
  let snapshot := (Sync.bytesField j "snapshot").toOption.getD ByteArray.empty
  let commitment : Sync.Checkpoint :=
    { ledger := s.ledger, realm, generation, seq, stateHash, headHash, author,
      signature, snapshot }
  unless s.suite.checkHex author commitment.commitmentBytes signature do
    return .mismatch seq s!"the commitment signed by {author} does not verify"
  if seq > head.seq then
    return .skipped "it speaks about an entry this node has not reached"
  match ← remoteHashAt s.ctx seq with
  | some stored =>
    if stored != headHash then
      return .mismatch seq s!"it names entry {seq} as {headHash}, and this node stored \
                              {stored}"
  | none => return .skipped "this node has no entry at that position"
  if ← missedParts s.ctx realm seq then
    return .skipped "this node could not read every part written in it"
  let mine := Encode.hashState (← projectionAt s.ctx realm seq)
  if mine == stateHash then return .agreed seq stateHash
  return .mismatch seq s!"it commits to {stateHash} at entry {seq}, and this node computes \
                          {mine}"

/--
How loud a verdict is, so that a realm with several commitments reports the one
worth hearing.

A disagreement outranks an agreement, an agreement outranks a commitment that
could not be checked, and anything outranks there being none. So one trusted
author who disagrees is reported even when another agrees — which is the right
way round: two of them cannot both be right.
-/
private def loudness : Verdict → Nat
  | .mismatch .. => 3
  | .agreed .. => 2
  | .skipped _ => 1
  | .absent => 0

/--
Fetches every commitment the sequencer holds for a realm and reports the loudest
verdict among them.

A list rather than one, because the sequencer keeps one per author: a realm with
four members who sync has four of them, and they should all say the same thing.
-/
def verify (s : Session) (realm : String) (head : Sync.Head) : IO Verdict := do
  let (code, payload) ← Transport.result s.transport
    (Transport.get (s.route ["realms", realm, "checkpoint"]))
  if code == 404 then return .absent
  if code != 200 then return .skipped (Transport.errorOf (.json code payload))
  let entries := payload.getArr?.toOption.getD #[]
  let mut verdict : Verdict := .absent
  for entry in entries do
    let one ← verifyOne s realm head entry
    if loudness one > loudness verdict then verdict := one
  return verdict

/--
The furthest-along checkpoint on a realm that this node trusts, can open, and
has checked.

Every claim in it is settled before it is used, and in the order that costs
least: the author has to be somebody this node trusts on that realm, the
signature has to verify over the snapshot that arrived rather than a digest of
one, this node has to hold the key the snapshot is sealed under, the plaintext
has to decode, and the state it decodes to has to be the state the commitment
names. A checkpoint that fails any of those is passed over in silence, because
the next one in the list may be sound and there is nothing here worth stopping
a join for.
-/
def offered? (s : Session) (realm : String) : IO (Option Offer) := do
  let (code, payload) ← Transport.result s.transport
    (Transport.get (s.route ["realms", realm, "checkpoint"]))
  if code != 200 then return none
  let mut best : Option Offer := none
  for j in payload.getArr?.toOption.getD #[] do
    let author := (Sync.strField? j "author").toLower
    unless ← s.trusts realm author do continue
    let seq := (j.getObjValAs? Nat "seq").toOption.getD 0
    if let some found := best then
      if found.seq ≥ seq then continue
    let generation := (j.getObjValAs? Nat "generation").toOption.getD 0
    let some key ← Keys.get s.keys realm generation | continue
    let snapshot := (Sync.bytesField j "snapshot").toOption.getD ByteArray.empty
    let stateHash := Sync.strField? j "stateHash"
    let headHash := Sync.strField? j "headHash"
    let commitment : Sync.Checkpoint :=
      { ledger := s.ledger, realm, generation, seq, stateHash, headHash, author,
        signature := Sync.strField? j "signature", snapshot }
    unless s.suite.checkHex author commitment.commitmentBytes commitment.signature do continue
    if snapshot.size < s.suite.nonceSize then continue
    let some plain := s.suite.openPart key (take snapshot s.suite.nonceSize)
      (snapshotAd s.ledger realm generation author) (drop snapshot s.suite.nonceSize) | continue
    let some state := (Codec.decode plain : Option State) | continue
    unless Encode.hashState state == stateHash do continue
    best := some { seq, headHash, state, author }
  return best

end Checkpoint

end Node
end Resources
