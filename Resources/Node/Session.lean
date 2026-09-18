import Resources.Node.Envelope
import Resources.Node.Transport
import Resources.Store.Commit
import Resources.Store.Replay

/-!
# What a node knows about the sequencer it syncs with

Where it syncs (`sync.json`), who it commits as, where the remote order has got
to, and the session every request goes through. `Node/Sync.lean` is the round
itself; this file is everything the round is written against, split out because
checkpoints and blobs need the same session and sit below sync rather than
inside it.

## Where a node keeps what it knows

`sync.json`, beside the database, mode 0600:

```json
{ "sequencer": "https://seq.example/", "ledger": "home",
  "member": "<hex signing key>", "remoteSeq": 41,
  "genesisHash": "<16 hex>", "genesisSeen": true,
  "pinned": [ { "realm": "<realm id>", "member": "<hex signing key>" } ],
  "generations": [ { "member": "<hex signing key>", "keyGeneration": 2 } ] }
```

`pinned` is what an invite link left behind: the member id of the admin who
issued the invite, for the realm it was issued on. Before a node has replayed a
single entry it knows nobody, so a grant or a checkpoint signed by anybody at
all would have to be taken on the sequencer's word. The link carries the
inviter's signing key, the joiner writes it down here, and from then on that one
key is a reason to believe a wrapped key or a commitment — but only until this
node's own replayed state records an admin of that realm, after which the state
is the answer and the pin is spent. See `Session.trusts`. Nothing removes a pin:
it says who let this node in, which does not stop being true, and a second join
appends to the list rather than replacing it.

`genesisHash` is what the order this node syncs begins with: the first sixteen
bytes of the SHA-256 of the hash of entry 1's envelope, as hex. An invite link
carries the same digest, which is what lets a joiner refuse a ledger whose first
entry is not the one its inviter meant — the whole of a reader's state is
decided by that entry, and a signature on it proves only that *some* member
wrote it. `genesisSeen` is false when this node started from a checkpoint
instead of from entry 1 and therefore never saw the beginning for itself.

It is written once and never moved: `noteProgress` fills it in the first time
there is an entry 1 to fingerprint and leaves it alone afterwards, because a
value that changed when the order changed would anchor nothing. That backfill is
what a store with no link to read the digest out of has instead, and every other
client of this protocol owes its users the same one — see `Node/Sync.lean`.

`generations` is the highest `keyGeneration` this node has seen each member
publish an agreement key under. The sequencer refuses a write that lowers one,
but a sequencer is not what this is protection against: without a record of its
own, a client can be served the consistent `(boxPk, signature, generation)`
triple from before a member's agreement secret leaked, for ever. A generation
below the one on file here is not read.

and three columns on the `event` table. Migration 19 added the first two:
`remote_seq` is `NULL` for a local event that has not been pushed, `0` for one
from before this node joined somebody else's ledger, and otherwise the position
the sequencer gave it; `remote_hash` is the hash of the envelope at that
position. Migration 20 added `unreadable_realms`, which named the realms an
entry carried parts for that this node could not open — what a projection of
one of those realms would be missing, and therefore what stops this node from
comparing its projection with anybody else's. Migration 23 moved that fact into
the `event_unreadable` table, a row per realm, so that a realm id is asked about
as a value rather than as a `LIKE` pattern inside a comma-joined list; the
column is still there and nothing reads it.

The columns are the truth — `remoteSeq` in the file is a convenience for
`resources sync status` — because they are written in the same transaction as
the event they speak about.

*The local chain and the remote chain are two different chains, and both are
verified.* The local one hashes the bytes this node stores, which for somebody
else's event are the parts it could read. The remote one hashes the envelopes
the sequencer ordered, which cover parts this node will never see. Neither chain
implies the other, and a node that treated one hash as evidence for the other
would be claiming to have verified ciphertext it cannot open.
-/

open Lean SQLite

namespace Resources
namespace Node

/-! ## sync.json -/

/--
One admin this node has a reason to trust on one realm, because an invite link
said so.

Two fields and no role: the pin is not a claim about what that member may do in
the ledger, it is a record of who this node was let in by. What it buys is the
right to be believed about a wrapped key and a commitment on that realm, until
the node has replayed enough of the order to see the realm's admins for itself.
-/
structure Pin where
  /-- The realm the invite was for. -/
  realm : String
  /-- The inviter's member id, which is their signing key. -/
  member : String
  deriving Inhabited, BEq

/-- Where a node syncs, how far it has got, and who let it in. -/
structure Settings where
  /-- Base URL of the sequencer; empty when this node is local-only. -/
  sequencer : String := ""
  /-- Which ledger on it this store is. -/
  ledger : String := ""
  /-- The member id this node commits as: the hex of its signing key. -/
  member : String := ""
  /-- The last position in the remote order this node has taken in. -/
  remoteSeq : Nat := 0
  /-- The inviters this node pinned when it joined, one per realm it joined by link. -/
  pinned : List Pin := []
  /-- `genesisFingerprint` of entry 1 of the order, or empty when this node cannot say. -/
  genesisHash : String := ""
  /-- Whether this node holds entry 1 itself, rather than having started from a checkpoint. -/
  genesisSeen : Bool := true
  /-- The highest agreement-key generation seen for each member, by member id. -/
  generations : List (String × Nat) := []
  deriving Inhabited

namespace Settings

/-- Where a store keeps its sync configuration. -/
def pathIn (cfg : Config) : System.FilePath := cfg.dataDir / "sync.json"

/-- Whether this node has a sequencer to talk to. -/
def configured (s : Settings) : Bool := !s.sequencer.isEmpty && !s.ledger.isEmpty

/-- The pins a `sync.json` records, ignoring anything in the array that is not one. -/
private def readPins (j : Json) : List Pin :=
  match (j.getObjVal? "pinned").bind Json.getArr? with
  | .ok arr =>
    arr.toList.filterMap fun p =>
      let realm := Sync.strField? p "realm"
      let member := (Sync.strField? p "member").toLower
      if realm.isEmpty || !Sync.isMemberId member then none else some { realm, member }
  | .error _ => []

/--
The generations a `sync.json` records, ignoring anything that is not one.

A member id that is not one is dropped rather than kept: the list is consulted
by id, so an entry nothing can ever match is an entry nothing can ever refuse.
-/
private def readGenerations (j : Json) : List (String × Nat) :=
  match (j.getObjVal? "generations").bind Json.getArr? with
  | .ok arr =>
    arr.toList.filterMap fun g =>
      let member := (Sync.strField? g "member").toLower
      if Sync.isMemberId member then
        some (member, (g.getObjValAs? Nat "keyGeneration").toOption.getD 0)
      else none
  | .error _ => []

/-- Reads `sync.json`, or `none` when there is none. -/
def load? (cfg : Config) : IO (Option Settings) := do
  let path := pathIn cfg
  unless ← path.pathExists do return none
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  return some { sequencer := Sync.strField? j "sequencer", ledger := Sync.strField? j "ledger",
                member := Sync.strField? j "member",
                remoteSeq := (j.getObjValAs? Nat "remoteSeq").toOption.getD 0,
                pinned := readPins j,
                genesisHash := (Sync.strField? j "genesisHash").toLower,
                -- A file written before this field existed is one whose node did
                -- read the order from its first entry, which is what every node
                -- but a checkpoint-seeded one did.
                genesisSeen := (j.getObjValAs? Bool "genesisSeen").toOption.getD true,
                generations := readGenerations j }

/-- Reads `sync.json`, or an empty configuration. -/
def load (cfg : Config) : IO Settings := do return (← load? cfg).getD {}

/-- Writes `sync.json`, mode 0600, through a temporary file. -/
def save (cfg : Config) (s : Settings) : IO Unit := do
  let j := Json.mkObj [("sequencer", s.sequencer), ("ledger", s.ledger), ("member", s.member),
                       ("remoteSeq", Sync.jnat s.remoteSeq),
                       ("genesisHash", s.genesisHash),
                       ("genesisSeen", Json.bool s.genesisSeen),
                       ("pinned", Json.arr ((s.pinned.map fun p =>
                          Json.mkObj [("realm", p.realm), ("member", p.member)]).toArray)),
                       ("generations", Json.arr ((s.generations.map fun (m, g) =>
                          Json.mkObj [("member", m),
                                      ("keyGeneration", Sync.jnat g)]).toArray))]
  Files.writeSecret (pathIn cfg) (j.pretty ++ "\n")

/-- Records the member id this node commits as, keeping whatever else was there. -/
def setMember (cfg : Config) (member : String) : IO Unit := do
  save cfg { ← load cfg with member }

/--
Pins an inviter as an admin of the realm they let this node into.

An append, never a replacement. A node let into a second realm by a second
person has two anchors and needs both: the first join's pin is what makes the
first realm's grants and commitments believable until its membership has been
replayed, and a second join that dropped it would quietly leave that realm with
no bootstrap at all.
-/
def pin (cfg : Config) (realm member : String) : IO Unit := do
  let current ← load cfg
  let p : Pin := { realm, member := member.toLower }
  unless current.pinned.contains p do
    save cfg { current with pinned := current.pinned ++ [p] }

/-- The highest agreement-key generation this node has seen a member publish. -/
def generationOf (s : Settings) (member : String) : Nat :=
  ((s.generations.find? (fun g => g.1 == member.toLower)).map (·.2)).getD 0

/--
Records that a member has published an agreement key at a generation.

Only ever upwards, and only when it moves, so that the ordinary case costs a
read and no write. What is on file is a floor: a member's own attestation at a
lower number has been superseded by one this node has already seen, and a
sequencer offering it again is offering the pair from before a rotation.
-/
def noteGeneration (cfg : Config) (member : String) (generation : Nat) : IO Unit := do
  let who := member.toLower
  let current ← load cfg
  if generation ≤ current.generationOf who then return
  save cfg { current with
             generations := (current.generations.filter (fun g => g.1 != who))
                              ++ [(who, generation)] }

end Settings

/--
The `Ctx` that commits as whoever `sync.json` names.

A store opened by a node that has run `resources identity init` must write
events under that identity, or the parts it pushes are authored by a member the
other nodes have never heard of. This is the one line that makes that true, and
it is deliberately forgiving: an id nobody has added to the ledger yet is
ignored rather than refused, so a half-finished setup still opens.
-/
def adopt (ctx : Ctx) : IO Ctx := do
  let settings ← Settings.load ctx.cfg
  if settings.member.isEmpty then return ctx
  let st ← ctx.state.get
  let me : MemberId := ⟨settings.member⟩
  if (st.member? me).isSome then return { ctx with member := me } else return ctx

/-! ## Where the remote order has got to -/

private structure RemoteRow where
  remoteSeq : Int64
  remoteHash : String
  deriving Row

/-- The last entry of the remote order this node has stored, or the empty head. -/
def remoteHead (ctx : Ctx) : IO Sync.Head := do
  match ← Db.row? RemoteRow ctx.db
    "SELECT remote_seq, remote_hash FROM event
     WHERE remote_seq IS NOT NULL AND remote_seq > 0 ORDER BY remote_seq DESC LIMIT 1" with
  | some r => return { seq := r.remoteSeq.toInt.toNat, hash := r.remoteHash }
  | none => return {}

/-- How many local events are waiting to be pushed. -/
def pendingCount (ctx : Ctx) : IO Nat := do
  return (← Db.scalarInt ctx.db "SELECT COUNT(*) FROM event WHERE remote_seq IS NULL").toNat

/--
Marks everything in the local log as this node's own prehistory.

Taking a store onto a sequencer is not the same as offering its history. The
events it already has describe a ledger nobody else has ever seen, and pushing
them into the shared order would arrive attributed to `self`, a member who
predates having a key. They stay where they are, readable and replayable, and
are never offered; `seedGenesis` writes one entry saying where this store came
in, and the shared order starts from that.
-/
def markPrehistory (ctx : Ctx) : IO Unit :=
  Db.exec ctx.db "UPDATE event SET remote_seq = 0 WHERE remote_seq IS NULL"

/--
Empties this store of its own books, so that the order it is about to join is
the whole of what it says.

This is what joining somebody else's ledger costs, and it is a real cost, so it
is worth saying why it is not optional. A genesis is a *position* and not an
operation: the first entry of an order is the state that order begins from, and
`applyOp` refuses a snapshot everywhere, position 1 included. So the snapshot at
the head of somebody else's order is read only by a reader for whom it really is
entry 1, and a store that kept its own log would put it at some position other
than the first — where it is an operation that applies nothing at all.

Such a store would then hold an in-memory state its own log does not replay to,
which is the one thing this design does not allow: the tables are a cache of the
events, and a cache of events that never happened is not recoverable from
anything.

So a join adopts, rather than merges. The events go, the projection goes, and
the state is `State.init` again, which is exactly where the order being joined
begins. What was here is not pushed anywhere, and a store with books worth
keeping should be joined from a copy.
-/
def adoptLedger (ctx : Ctx) : IO Unit := do
  ctx.atomically do
    Db.exec ctx.db "DELETE FROM event"
    Db.exec ctx.db "DELETE FROM event_unreadable"
    Db.exec ctx.db "DELETE FROM ledger_head"
    Db.exec ctx.db "DELETE FROM checkpoint"
    Project.reset ctx.db
    -- `State.init` is not the empty state — it has the member, the party and the
    -- realm a ledger belongs to — so the tables are written to say so, or the
    -- projection and the state would disagree from the first row.
    Project.all ctx.db State.init
  ctx.state.set State.init

/-! ## The realms this node folded around

Two questions about `event_unreadable`, asked from either end. They belong with
checkpoints and are written about in `Node/Checkpoint.lean`, and they live here
because `Session.trusts` needs them: a realm this node missed a part of is a
realm whose membership it has not really read, so the admin set it would consult
is one entry out of date in a direction it cannot see. That file sits above this
one, so the answer had to move down rather than the question up.
-/

namespace Checkpoint

/--
Whether any entry up to a position carried a part in this realm that did not open.

A realm id is a value here and not a pattern: the gaps are one row per realm in
`event_unreadable` (migration 23), so the question is an equality. It used to be
a `LIKE` over a comma-joined column, where a realm id containing `_` matched its
neighbours and one containing `,` was two other realms — either of which answers
"nothing was missed" about a realm where something was, which is the one answer
that turns a node's own blind spot into an accusation against everybody else.
-/
def missedParts (ctx : Ctx) (realm : String) (upTo : Nat) : IO Bool := do
  return (← Db.scalarInt ctx.db
    s!"SELECT COUNT(*) FROM event_unreadable u JOIN event e ON e.seq = u.seq
       WHERE u.realm = {Db.lit realm} AND e.remote_seq >= 1 AND e.remote_seq <= {upTo}") > 0

/--
Every realm this node missed a part of, at or before a position in the order.

`missedParts` asked of one realm; this is the same question asked the other way
round, because the answer is what a reader of this node's projection needs to be
told. A realm with a gap is a realm this node folded *around*: it cannot publish
a commitment for it, it cannot check anybody else's, it cannot take its admin set
at face value, and what it shows of that realm is not what the realm says.
`GET realms` and `resources sync status` mark such a realm `unverified` for
exactly that reason — the thin client refuses to display one at all, and a node
that quietly showed a partial projection would be worse off than one that could
not show it.
-/
def gappedRealms (ctx : Ctx) (upTo : Nat) : IO (Array String) := do
  Db.rows String ctx.db
    s!"SELECT DISTINCT u.realm FROM event_unreadable u JOIN event e ON e.seq = u.seq
       WHERE e.remote_seq >= 1 AND e.remote_seq <= {upTo} ORDER BY u.realm"

end Checkpoint

/-! ## A session -/

/--
Everything one round of sync needs: the store, the keys, and the way to the
sequencer.

The transport is a field rather than something derived from `settings.sequencer`
so that a test can hand in a sequencer running in the same process, and so that
`resources node` can keep one session, with one live token, across every round
of its loop.
-/
structure Session where
  /-- The store being synced. -/
  ctx : Ctx
  /-- The primitives. -/
  suite : CryptoSuite
  /-- The keys this node holds. -/
  keys : Keyring
  /-- The way to the sequencer. -/
  transport : Transport
  /-- Which ledger is being synced. -/
  ledger : String

/--
A grant as the sequencer serves it: the wrapped key, and every field its issuer
signed over.

It is read into a record of its own rather than picked field by field out of
JSON at each use, because the signature is over all of them together: a client
that checked the signature against one reading and then used another would be
checking nothing.
-/
structure GrantRecord where
  /-- The realm granted. -/
  realm : String
  /-- Who holds it. -/
  member : String
  /-- Which generation of the realm key is inside. -/
  generation : Nat
  /-- What the holder is meant to do with it. -/
  role : String
  /-- The realm key, sealed to the holder's agreement key. -/
  wrappedKey : ByteArray
  /-- Who issued it. -/
  grantedBy : String
  /-- `grantedBy`'s signature over `Sync.grantBytes`, hex. -/
  signature : String
  deriving Inhabited

/-- Reads a grant out of what a grant route hands back. -/
def GrantRecord.ofJson? (j : Json) : Option GrantRecord := do
  let wrappedKey ← (Sync.bytesField j "wrappedKey").toOption
  return { realm := Sync.strField? j "realm", member := (Sync.strField? j "member").toLower,
           generation := (j.getObjValAs? Nat "generation").toOption.getD 0,
           role := Sync.strField? j "role" "viewer", wrappedKey,
           grantedBy := (Sync.strField? j "grantedBy").toLower,
           signature := (Sync.strField? j "signature").toLower }

namespace Session

/-- Whose session this is. -/
def identity (s : Session) : Identity := s.keys.identity

/-- The member id this node appends as. -/
def member (s : Session) : String := s.keys.identity.id

/-- A path below this session's ledger. -/
def route (s : Session) (rest : List String) : List String :=
  ["ledgers", s.ledger] ++ rest

/-! ## Who this node believes about a realm

The sequencer is untrusted, and everything it hands a client that a client then
*acts* on — a realm key, a commitment about a state — is signed by somebody. The
question this section answers is which somebodies count, and there are exactly
three: this node itself, the inviter it pinned when it joined, and whoever its
own replayed state records as an administrator of the realm in question.

That last one is the interesting case and the reason the policy is a function of
the realm rather than a list of keys. Membership moves: an admin who is revoked
stops being one the moment this node applies the entry that says so, and a grant
they sign after that is a grant this node ignores.
-/

/--
Whether this node has a reason to believe what `signer` says about `realm`.

The order matters and it is not the cheap-first order. This node's own word
first, then its own replayed state, and the pin last and only while that state
records nobody as an admin of the realm at all.

That last clause is the whole of what a pin is. It is a bootstrap: a node that
has replayed nothing knows nobody, so the key its invite link named is the one
reason it has to believe a wrapped key or a commitment before it has read the
realm's membership for itself. The moment it *has* read that membership, the
membership is the answer — otherwise the admin who sent the link stays trusted
after the entry revoking them has been applied, and `Checkpoint.offered?` takes
the highest `seq` among trusted authors, so one stale commitment from a demoted
inviter outranks every honest one below it and starts a whole store from itself.

"Has read that membership" is asked of `event_unreadable` as well as of the
state. A node that could not open a part written in this realm has folded around
whatever that part said, and one of the things it may have said is that somebody
is no longer an admin — so the set this node would consult is a set it has no
reason to think current. Such a realm is treated as one it has not read: the pin
is consulted again, which is the fail-closed direction, since a pin names one
key and the stale set may name several. `Checkpoint.verifyOne` already declines
to compare a projection of a gapped realm for the same reason.
-/
def trusts (s : Session) (realm signer : String) : IO Bool := do
  if signer.isEmpty then return false
  if signer == s.member then return true
  let st ← s.ctx.state.get
  if st.canAdminister ⟨signer⟩ ⟨realm⟩ then return true
  -- A realm this node's state records admins for is a realm whose admins are
  -- the answer, and `signer` is not one of them. `self` does not count: it is
  -- the member a ledger belongs to before there is a key to sign with, it is in
  -- `State.init` from the start, and it cannot have signed anything — so a realm
  -- administered by nobody else is a realm this node has not read yet. Neither
  -- is one this node read part of and not the rest.
  if let some r := st.realm? ⟨realm⟩ then
    let gapped ← Checkpoint.gappedRealms s.ctx (← remoteHead s.ctx).seq
    if !gapped.contains realm
        && r.members.any (fun (m, role) => role == .admin && m != Member.selfId) then
      return false
  return (← Settings.load s.ctx.cfg).pinned.contains { realm, member := signer }

/--
Whether a grant made out to this node was really issued by somebody entitled to
issue it.

Three questions, and the order is the cheap one first: is this grant even for
this node, is the signature on it one its stated issuer could have produced, and
is that issuer somebody this node trusts on that realm. A grant that fails any
of them is never unwrapped — which matters more than it sounds, because
`Keys.latest` picks the highest generation held and that is the key everything
this node writes next is sealed under. A key filed on a sequencer's say-so is a
key the sequencer reads every future write with.
-/
def checkGrant (s : Session) (g : GrantRecord) : IO (Except String Unit) := do
  if g.member != s.member then
    return .error s!"the grant on realm '{g.realm}' is made out to {g.member}, not to this node"
  unless s.suite.checkHex g.grantedBy
      (Sync.grantBytes s.ledger g.realm g.generation g.member g.role g.wrappedKey)
      g.signature do
    return .error s!"the grant on realm '{g.realm}' is not signed by the member it names \
                     as its issuer"
  unless ← trusts s g.realm g.grantedBy do
    return .error s!"the grant on realm '{g.realm}' was issued by {g.grantedBy}, who is not an \
                     admin of it as far as this node can see"
  return .ok ()

/-- Checks a grant and, if it stands up, files the key inside it. -/
def useGrant (s : Session) (g : GrantRecord) : IO (Except String Unit) := do
  match ← checkGrant s g with
  | .error why => return .error why
  | .ok _ =>
    try
      discard <| Keys.unwrapGrant s.keys g.realm g.generation g.wrappedKey
      return .ok ()
    catch e =>
      return .error (toString e)

/--
The agreement key a member published, if they are the ones who published it.

`boxPk` on a member record is the key a realm key would be sealed to, and the
server is the one handing it over. Without the member's own signature over it,
an operator could substitute a key they hold and be re-granted every realm on
the next rotation — which is the hole this check closes. `none` means "do not
seal anything to this", and every caller treats it as "this member cannot be
granted" rather than as "grant them anyway".

`keyGeneration` is inside the bytes that were signed, so it is read off the same
record the key was read off and passed in here. That is what makes a key
replaceable: an attestation the member made at generation 3 does not verify at
2, so a sequencer serving the pair from before a leak is serving a signature
that no longer checks out against the record it is serving it in. Absent means
zero, which is what every first key was signed under.
-/
def memberBoxPk? (s : Session) (member boxPk signature : String)
    (keyGeneration : Nat := 0) : Option ByteArray := do
  guard (!boxPk.isEmpty)
  guard (s.suite.checkHex member (Sync.memberBytes s.ledger member boxPk keyGeneration) signature)
  Sync.ofHex? boxPk

/--
The same question, asked of a node that remembers what it has already been told.

`memberBoxPk?` checks that a member signed for the key beside the generation the
record states, which is what makes a key replaceable: the attestation made at
three does not verify at two. What it cannot see on its own is that this node
was shown three yesterday. An untrusted sequencer that kept the pair from before
a member's agreement secret leaked can serve it for ever otherwise — it is
internally consistent, it verifies, and nothing in one record says another one
exists.

So the highest generation seen per member is written down in `sync.json`, and a
record below it is not read. `none` is the same answer as an unsigned key, and
every caller treats it as "this member cannot be granted" rather than as "grant
them anyway".
-/
def memberKey? (s : Session) (member boxPk signature : String) (keyGeneration : Nat) :
    IO (Option ByteArray) := do
  let settings ← Settings.load s.ctx.cfg
  if keyGeneration < settings.generationOf member then return none
  let some key := s.memberBoxPk? member boxPk signature keyGeneration | return none
  Settings.noteGeneration s.ctx.cfg member keyGeneration
  return some key

/--
This node's own member record on the sequencer, when it has one.

A refusal is `none` rather than an error: this is asked in order to decide which
generation to sign under, and a sequencer that will not list its members has
told this node nothing about what it holds. The write that follows is the one
that has to be loud, and it is — the route refuses a generation that does not
follow the one on file.
-/
private def ownRecord? (s : Session) : IO (Option Json) := do
  let (code, payload) ← Transport.result s.transport (Transport.get (s.route ["members"]))
  if code != 200 then return none
  return (payload.getArr?.toOption.getD #[]).find? fun m =>
    (Sync.strField? m "member").toLower == s.member

/--
Publishes this node's own agreement key, signed under its own signing key.

One route writes an agreement key and it only ever writes the caller's own, so
this is the only way a realm key ever becomes sealable to this node. It is
called after creating a ledger and after joining one, which are the two moments
this node is newly a member of something.

It is also how a key is *replaced*, which is why it reads the record before it
writes one. The generation is inside the signed bytes and only ever goes up, so
re-publishing the key already on file must re-use its number — a bump would be a
second attestation for the same key and would age out the one the ledger's other
clients are holding — while publishing a different key must raise it, or the
sequencer refuses the write and the old pair stays valid for ever. Both are one
comparison: the same key keeps its generation, a new one gets the next.
-/
def publishBoxPk (s : Session) : IO Unit := do
  let boxPk := s.identity.boxPkHex
  let generation ←
    match ← ownRecord? s with
    | none => pure 0
    | some m =>
      let held := (Sync.strField? m "boxPk").toLower
      let g := (m.getObjValAs? Nat "keyGeneration").toOption.getD 0
      pure (if held.isEmpty || held == boxPk then g else g + 1)
  let signature := Identity.signHex s.suite s.identity
    (Sync.memberBytes s.ledger s.member boxPk generation)
  discard <| Transport.json s.transport
    (Transport.send "PUT" (s.route ["members", s.member, "boxPk"])
      (Json.mkObj [("boxPk", boxPk), ("boxPkSignature", signature),
                   ("keyGeneration", Sync.jnat generation)]))

end Session

/-! ## Being re-keyed -/

/--
Asks the sequencer for this node's own grant on a realm at a stated generation,
checks who issued it, and files the key inside it.

This is what a revoke looks like from the other side. A part arrives sealed
under a generation this node holds no key for; if the node still holds a grant,
the sequencer hands back the new key wrapped to its agreement key, and the pull
carries on. If it does not — because this is the node that was put out — the
answer is a 404 or a grant at the wrong generation, and the part stays
unreadable, which is the whole of what being revoked means.

A grant that arrives from anybody this node does not trust on that realm is the
same answer as no grant at all. That is deliberately a quiet refusal: the part
stays unreadable and the pull goes on, because an unreadable part is an ordinary
thing and a node that stopped syncing over one would be a node any sequencer
could stop.
-/
def fetchKey (s : Session) (realm : String) (generation : Nat) : IO Bool := do
  let (code, payload) ← Transport.result s.transport
    (Transport.get (s.route ["realms", realm, "grants", s.member]))
  if code != 200 then return false
  let some g := GrantRecord.ofJson? payload | return false
  if g.realm != realm || g.generation != generation then return false
  match ← s.useGrant g with
  | .ok _ => return true
  | .error _ => return false

end Node
end Resources
