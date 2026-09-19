import Resources.Core.Apply
import Resources.Core.Encode
import Resources.Store.Db

/-!
# The log, and reading the ledger back out of it

The `event` table is the ledger. Every write is one event — an author, the
operations they composed, and the canonical bytes of both — chained to the event
before it by the SHA-256 of those bytes. The ledger tables are a cache of what
the events add up to, and this file is what says so: `Replay.state` folds the log
from `State.init` and hands back a state that owes the tables nothing.

Three namespaces. `EventLog` writes: `head` reads where the chain has got to and
`append` extends it, which `Ctx.open` does once for genesis and `Ctx.commit`
does for every write after that. `Replay` reads: `events` decodes the rows and
checks the chain, and `state` folds them. `Checkpoints` holds snapshots of
states already folded, so that `Replay.stateFrom` can start part way along.

A checkpoint shortens the fold and nothing else. The events it covers stay in
the table, chained as they were, and `Replay.state` goes on folding all of them
— which is what makes a snapshot checkable rather than merely trusted, and is
why this phase deliberately deletes nothing.

The chain is verified against the stored bytes rather than against the decoded
event, and that is deliberate. `hash` is the SHA-256 of the `bytes` column, so
checking it needs no encoder and cannot be fooled by one: a byte changed in the
table is caught whether or not it still decodes, and whether or not this binary's
encoding still agrees with the one that wrote the row.
-/

open Lean SQLite

namespace Resources

/-! ## Writing -/

namespace EventLog

/-- What stands before the first event: sixty-four zeros, one for each hex digit of a hash. -/
def zeroHash : String := String.ofList (List.replicate 64 '0')

private structure HeadRow where
  seq : Int64
  hash : String
  deriving Row

/-- The sequence number and hash of the last event, or `(0, zeroHash)` on an empty log. -/
def head (db : SQLite) : IO (Nat × String) := do
  match (← Db.row? HeadRow db "SELECT seq, hash FROM ledger_head WHERE id = 1") with
  | some r => return (r.seq.toInt.toNat, r.hash)
  | none =>
    -- The head row is a cache of the last event, so a missing one is a question
    -- the log itself can answer rather than a log that has to start again.
    match (← Db.row? HeadRow db "SELECT seq, hash FROM event ORDER BY seq DESC LIMIT 1") with
    | some r => return (r.seq.toInt.toNat, r.hash)
    | none => return (0, zeroHash)

/--
Appends an event to the log and moves the head onto it.

Returns the sequence number and hash it was written under. The caller is inside
a transaction: an event that is in the table while the head still points before
it is a torn write, and the projection of the same event belongs with it.
-/
def append (db : SQLite) (e : Event) : IO (Nat × String) := do
  let (seq, prev) ← head db
  let bytes := Encode.eventBytes e
  let hash := Encode.hashEvent e
  let next := seq + 1
  -- Stamped with the format that wrote it, which is the one thing about an entry
  -- that its own bytes cannot say.
  Db.execBlob db s!"INSERT INTO event
    (seq, id, author, composed_at, based_on, prev_hash, hash, bytes, format)
    VALUES ({next}, {Db.lit e.id}, {Db.lit e.author.val}, {Db.lit e.composedAt},
            {e.basedOn}, {Db.lit prev}, {Db.lit hash}, ?, {Encode.formatVersion})" bytes
  Db.exec db s!"INSERT INTO ledger_head (id, seq, hash) VALUES (1, {next}, {Db.lit hash})
    ON CONFLICT(id) DO UPDATE SET seq = excluded.seq, hash = excluded.hash"
  return (next, hash)

end EventLog

/-! ## Snapshots this node has already folded -/

namespace Checkpoints

/-- A stored snapshot: canonical state bytes, their hash, and what they stand for. -/
structure Stored where
  /-- Which state: a realm id for that realm's projection, empty for the whole log. -/
  realm : String
  /-- The position it speaks for: the sequencer's for a realm, this log's for the whole. -/
  seq : Nat
  /-- `Encode.hashState` of the state inside. -/
  stateHash : String
  /-- The state itself, in canonical bytes. -/
  bytes : ByteArray
  deriving Inhabited

private structure Row where
  seq : Int64
  stateHash : String
  bytes : ByteArray
  deriving SQLite.Row

private structure Listing where
  realm : String
  seq : Int64
  stateHash : String
  deriving SQLite.Row

/--
Records a snapshot, replacing whatever was held for that realm.

Only the newest is kept, for the reason the sequencer keeps only the newest: an
older snapshot of the same thing shortens the fold by less and proves nothing
the newer one does not.
-/
def put (db : SQLite) (realm : String) (seq : Nat) (stateHash : String)
    (bytes : ByteArray) : IO Unit := do
  let now ← nowStamp
  Db.execBlob db s!"INSERT INTO checkpoint (realm, seq, state_hash, bytes, written_at)
    VALUES ({Db.lit realm}, {seq}, {Db.lit stateHash}, ?, {Db.lit now})
    ON CONFLICT(realm) DO UPDATE SET seq = excluded.seq, state_hash = excluded.state_hash,
      bytes = excluded.bytes, written_at = excluded.written_at" bytes

/-- The snapshot held for a realm, or for the whole log when `realm` is empty. -/
def get? (db : SQLite) (realm : String) : IO (Option Stored) := do
  let r ← Db.row? Row db
    s!"SELECT seq, state_hash, bytes FROM checkpoint WHERE realm = {Db.lit realm}"
  return r.map fun r =>
    { realm, seq := r.seq.toInt.toNat, stateHash := r.stateHash, bytes := r.bytes }

/-- Every snapshot held, realm by realm. -/
def all (db : SQLite) : IO (Array Stored) := do
  let rs ← Db.rows Listing db
    "SELECT realm, seq, state_hash FROM checkpoint ORDER BY realm"
  return rs.map fun r =>
    { realm := r.realm, seq := r.seq.toInt.toNat, stateHash := r.stateHash,
      bytes := ByteArray.empty }

end Checkpoints

/-! ## Reading -/

namespace Replay

private structure EventRow where
  seq : Int64
  prevHash : String
  hash : String
  bytes : ByteArray
  deriving Row

/--
Every event after a position, in order, with the chain checked as it goes.

Three things have to hold of each row and all three throw if they do not: its
sequence number follows the one before, its `prev_hash` is the hash of the event
before it, and its `hash` is the SHA-256 of its own bytes. A log that passes is
one nobody has edited behind the ledger's back.

Starting part way along is what a checkpoint buys: `after` is the position a
stored snapshot speaks for and `prevHash` is the hash the row at that position
carries, so the tail is chained onto the snapshot exactly as it was chained onto
the events the snapshot stands for. Everything before `after` is still in the
table, unread — this phase archives nothing.
-/
def eventsAfter (db : SQLite) (after : Nat) (prevHash : String) : IO (Array Event) := do
  let rows ← Db.rows EventRow db
    s!"SELECT seq, prev_hash, hash, bytes FROM event WHERE seq > {after} ORDER BY seq"
  let mut out : Array Event := #[]
  let mut prev := prevHash
  for (row, i) in rows.zipIdx do
    let seq := after + i + 1
    if row.seq.toInt != seq then
      throw <| IO.userError s!"event {row.seq} is out of sequence: expected {seq}"
    if Sha256.hexBytes row.bytes != row.hash then
      throw <| IO.userError s!"event {seq} does not hash to what the log says it does"
    if row.prevHash != prev then
      throw <| IO.userError s!"event {seq} does not follow the event before it"
    let some e := (Codec.decode row.bytes : Option Event)
      | throw <| IO.userError s!"event {seq} cannot be decoded"
    out := out.push e
    prev := row.hash
  return out

/-- Every event in the log, in order, with the chain checked from its first link. -/
def events (db : SQLite) : IO (Array Event) := eventsAfter db 0 EventLog.zeroHash

/--
The last entry written before this binary's format, or zero when there is none.

`format` is NULL for everything appended before the column existed, which is the
same thing as an entry this binary's decoder has grown past: both are entries
whose bytes are still in the chain, still hash to what the log says, and no
longer parse. What they are *not* is corrupt, and this is the only place that
difference can be seen -- from inside `ofBytes` the two are identical.
-/
def formatBoundary (db : SQLite) : IO Nat := do
  let seq ← Db.scalarInt db
    s!"SELECT IFNULL(MAX(seq), 0) FROM event
       WHERE format IS NULL OR format < {Encode.formatVersion}"
  return seq.toNat

/-- The sequence number and hash `ledger_head` claims, if the row is there. -/
private structure HeadRow where
  seq : Int64
  hash : String
  deriving Row

/--
Whether the stored chain is whole, without folding a single event.

This is `eventsAfter`'s three checks and no more: each row's sequence number
follows the one before, its `hash` is the SHA-256 of its own `bytes`, and its
`prev_hash` is the hash of the row before it — plus the one thing `eventsAfter`
has no reason to ask, which is whether `ledger_head` still names the last row.
The head is a cache of the end of the chain and the thing every append compares
against, so a head that has drifted is a store that will write its next event
onto a fork of its own history.

Nothing here decodes and nothing here applies. Hashing the rows is the price of
opening a store, and it is the same price the log already pays on a rebuild;
`step` is what costs, and `step` is `Replay.state`'s business. That is also why
the check is on the bytes rather than on the events: a row edited into something
that no longer decodes is caught either way, and one edited into something that
still does is caught only here.

Returns the sentence to refuse with, or `none` when the log is whole.
-/
def chainError? (db : SQLite) : IO (Option String) := do
  let rows ← Db.rows EventRow db "SELECT seq, prev_hash, hash, bytes FROM event ORDER BY seq"
  let mut prev := EventLog.zeroHash
  for (row, i) in rows.zipIdx do
    let seq := i + 1
    if row.seq.toInt != seq then
      return some s!"event {row.seq} is out of sequence: expected {seq}"
    if Sha256.hexBytes row.bytes != row.hash then
      return some s!"event {seq} does not hash to what the log says it does"
    if row.prevHash != prev then
      return some s!"event {seq} does not follow the event before it"
    prev := row.hash
  match ← Db.row? HeadRow db "SELECT seq, hash FROM ledger_head WHERE id = 1" with
  | none => return none
  | some head =>
    if head.seq.toInt != rows.size then
      return some s!"the head says the log has got to event {head.seq}, and it has \
                     {rows.size} events"
    if head.hash != prev then
      return some s!"the head names an event {head.hash} that is not the last one in the log"
    return none

/--
The state the log adds up to.

`Core.replay` is what makes this the ledger's own reading rather than a second
one: an operation that does not apply is a no-op, exactly as it is when it is
committed, so replaying a log that contains one gives the state the writer saw.

The fold starts at position 1 and nowhere else, which is what makes the genesis
the genesis: the first event's snapshot is the state this log begins from, and a
snapshot anywhere else is a part `applyOp` refuses. A reader that starts
elsewhere starts from a checkpoint it has verified — `stateFrom` — and never
from part way along.
-/
def state (db : SQLite) : IO State := do
  let log ← events db
  return Resources.replay log.toList

/--
The sentence to refuse with when the fold cannot start where it has to.

A log whose older entries predate this binary's format can still be *checked* --
the chain is over bytes and needs no decoder -- but it cannot be folded from the
beginning by anything that has grown past it. What stands in for those entries
is a checkpoint at or past the last of them: a state somebody who could read
them wrote down, which is the same bargain a newcomer already makes.
-/
def beyondFormat (boundary : Nat) : String :=
  s!"the first {boundary} entries of this log were written before format \
     {Encode.formatVersion}, which this binary speaks, and no checkpoint covers them. \
     Their bytes are intact and the chain still verifies; what is missing is a state to \
     start folding from. 'resources upgrade-format' writes one at the head, from the \
     tables, and nothing has to be re-entered."

/--
The state the log adds up to, starting from the stored snapshot if there is one.

The saving is the fold, not the reading: the events before the checkpoint stay
in the table and are deliberately not deleted, so this is a shortcut and never a
one-way door. What it does skip is `step` over all of them, which is the part
that costs.

Everything the snapshot claims is checked before it is trusted: its bytes have
to hash to the hash stored beside them, the log has to still have a row at the
position it names, and the tail has to chain onto that row. A snapshot that
fails any of these is ignored rather than repaired — the log is the ledger, and
falling back to folding all of it always gives the right answer.

Returns the state and the position it started folding from, which is 0 when it
folded everything.
-/
def stateFrom (db : SQLite) : IO (State × Nat) := do
  -- Folding everything is the right answer whenever it is possible, and it is
  -- possible exactly when nothing in the log predates this binary's format.
  -- Past that line it is not a fallback at all, and saying so is better than a
  -- decoder failing three screens later on a byte string nobody has touched.
  let boundary ← formatBoundary db
  let fallback : IO (State × Nat) := do
    if boundary > 0 then throw <| IO.userError (beyondFormat boundary)
    return (← state db, 0)
  let some cp ← Checkpoints.get? db "" | fallback
  if cp.seq == 0 then fallback
  else if cp.seq < boundary then fallback
  else if Sha256.hexBytes cp.bytes != cp.stateHash then fallback
  else
    let some (start : State) := (Codec.decode cp.bytes : Option State) | fallback
    let some rowHash ← Db.row? String db s!"SELECT hash FROM event WHERE seq = {cp.seq}"
      | fallback
    let tail ← eventsAfter db cp.seq rowHash
    -- `step`, not `replay`: the fold starts at a position the checkpoint speaks
    -- for rather than at position 1, so nothing in the tail is a genesis.
    return (tail.foldl (fun s e => (Resources.step s e).1) start, cp.seq)

end Replay

end Resources
