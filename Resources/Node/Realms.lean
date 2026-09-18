import Resources.Node.Blobs
import Resources.Node.Sync
import Resources.Crypto.Sodium

/-!
# Realms, invites and sync, as the node's own API

`Api/Routes.lean` is below `Node` in the import order and always will be: the
sequencer's route table is written over `Api.Req` as well, so `Node.Transport`
imports the API and the API cannot import the node. The routes that need a
keyring or a sequencer therefore take an `Api.NodeApi` — a handful of functions
— and this file is what fills it in.

Everything here degrades rather than fails. A store with no `sync.json` has no
sequencer, no keys and nothing to sync, and `POST realms` still writes a realm
into its ledger: a realm is a set of accounts with one viewer set, and that is
true of a store nobody else will ever see.

## Where the keys come from

The identity and the keyring are encrypted under a passphrase that was typed
once and is written down nowhere. A running `resources node` has already opened
them, so it says so here with `hold`, and the routes borrow what it holds. A
command run from a shell has no such process to borrow from and opens them
itself, which needs `$RESOURCES_PASSPHRASE` because there is nobody at the
terminal to ask by the time a route is running.
-/

open Lean

namespace Resources
namespace Node
namespace Realms

/-! ## The session to work through -/

/-- The session a running node has opened, for the routes underneath it. -/
initialize held : IO.Ref (Option Session) ← IO.mkRef none

/-- What the last round this process ran came to, for `GET sync/status` to report. -/
initialize lastRound : IO.Ref (Option Wire.Round) ← IO.mkRef none

/-- Lends this process's session to the routes. `resources node` calls it once. -/
def hold (s : Session) : IO Unit := held.set (some s)

/-- The passphrase a process nobody can be asked by can still find. -/
private def passphrase? : IO (Option String) := IO.getEnv "RESOURCES_PASSPHRASE"

/--
The session to work through, or `none` when there is not one.

Not an error, because two of the three reasons are ordinary: this store syncs
with nothing, or its keys are not open in this process. The third — a passphrase
that does not open the files — is an error and is raised as one.
-/
def session? (ctx : Ctx) : IO (Option Session) := do
  if let some s ← held.get then return some { s with ctx }
  let settings ← Settings.load ctx.cfg
  unless settings.configured do return none
  let some pass ← passphrase? | return none
  let suite ← CryptoSuite.forNode
  let identity ← Identity.load suite (Identity.pathIn ctx.cfg) pass
  let keys ← Keys.open suite (Keys.pathIn ctx.cfg) pass identity
  let transport ← Transport.overCurl suite identity settings.sequencer
  return some { ctx, suite, keys, transport, ledger := settings.ledger }

/-- The session, or the reason there is not one, for the things that need it. -/
def session (ctx : Ctx) : IO Session := do
  match ← session? ctx with
  | some s => return s
  | none =>
    if (← Settings.load ctx.cfg).configured then
      throw <| IO.userError "this node's keys are not open here: run it from 'resources node', \
                            or set RESOURCES_PASSPHRASE"
    else
      throw <| IO.userError "this store syncs with nothing; run \
                            'resources sync init --sequencer URL' first"

/-! ## What the routes ask for -/

/-- The sequencer this store syncs with, or empty when it syncs with nothing. -/
def sequencer (ctx : Ctx) : IO String := do
  let settings ← Settings.load ctx.cfg
  return if settings.configured then settings.sequencer else ""

/--
Every realm key this node holds, as realm id and generation.

A keyring that will not open is no keys rather than a failed request: this
answers a read, and "this node cannot show you a key" and "this node holds none"
are the same thing to everybody but its owner.
-/
def keysHeld (ctx : Ctx) : IO (Array (String × Nat)) := do
  try
    match ← session? ctx with
    | none => return #[]
    | some s => return (← Keys.all s.keys).map fun e => (e.realm, e.generation)
  catch _ => return #[]

/--
Takes the key for a realm that has just been made, and puts the realm on the
sequencer.

`ensureRealm` is both halves at once and is idempotent in both, which is what
makes it safe to call on a realm that a push has already announced.
-/
def create (ctx : Ctx) (realm : RealmId) : IO Unit := do
  match ← session? ctx with
  | some s => ensureRealm s realm.val
  | none =>
    -- No sequencer to tell, but a node that has a keyring keeps this realm's key
    -- beside the others, so that putting the store on a sequencer later does not
    -- have to invent one for a realm that has been written in since.
    let path := Identity.pathIn ctx.cfg
    unless ← path.pathExists do return
    let some pass ← passphrase? | return
    let suite ← CryptoSuite.forNode
    let identity ← Identity.load suite path pass
    let keys ← Keys.open suite (Keys.pathIn ctx.cfg) pass identity
    discard <| Keys.create keys realm.val

/--
Offers a realm to somebody who is not a member yet, and returns the link.

The secret is in the fragment, which a browser never sends to a server, so the
sequencer serving `/join/` learns nothing by serving it.
-/
def invite (ctx : Ctx) (realm : RealmId) (role expires : String) : IO String := do
  let s ← session ctx
  let fragment ← _root_.Resources.Node.invite s realm.val expires role
  let base := ((← Settings.load ctx.cfg).sequencer.dropEndWhile (· == '/')).toString
  return s!"{base}/join/#{fragment}"

/--
Which members the sequencer holds a grant for in a realm.

`none` when nobody was asked — there is no sequencer, or its keys are not open
here — because an empty list would say "nobody holds a key", which is a
different and much more alarming thing.
-/
def members (ctx : Ctx) (realm : RealmId) : IO (Option (Array String)) := do
  let some s ← session? ctx | return none
  let grants ← Transport.json s.transport
    (Transport.get (s.route ["realms", realm.val, "grants"]))
  return some ((grants.getArr?.toOption.getD #[]).map (Sync.strField? · "member"))

/--
Stores a file, encrypted under a realm key when this node holds one.

A store with no node in it, or one whose keys are not open here, writes the
plaintext and nothing else — which is what it did before there was a sequencer
to keep a copy on, and the only thing it can honestly do.
-/
def stored (ctx : Ctx) (bytes : ByteArray) (mime : String) (origName : Option String) :
    IO String := do
  match ← session? ctx with
  | some s => Blobs.put s bytes mime origName
  | none => Resources.Blobs.put ctx bytes mime origName

/--
Links a receipt to a transaction, moving the file's key into that transaction's
realm when it is wrapped under another one.

The same degrading: without keys there is no wrap to move, and the attachment is
the one thing the ledger records.
-/
def attached (ctx : Ctx) (txn : TxId) (sha : String) : IO Unit := do
  match ← session? ctx with
  | some s => Blobs.attach s txn sha
  | none => Resources.Blobs.attach ctx txn sha

/--
Realms this node missed a part of, somewhere in the order it has taken in.

Read from `event_unreadable` rather than worked out from the keyring: a realm
this node holds no key for at all is not a gap, it is somebody else's room, and
the thing that matters is a realm it does read and has holes in. A node revoked
and later let back in is the case this is for.
-/
def unverified (ctx : Ctx) : IO (Array String) := do
  Checkpoint.gappedRealms ctx (← remoteHead ctx).seq

/-- Where this store syncs, and how far it has got. -/
def status (ctx : Ctx) : IO Wire.SyncStatus := do
  let settings ← Settings.load ctx.cfg
  let head ← remoteHead ctx
  let (signPk, boxPk) := (← Identity.publicKeys? (Identity.pathIn ctx.cfg)).getD ("", "")
  return { configured := settings.configured, sequencer := settings.sequencer,
           ledger := settings.ledger,
           member := if settings.member.isEmpty then signPk else settings.member,
           boxPk, seq := head.seq, hash := head.hash,
           pending := ← pendingCount ctx, events := (← EventLog.head ctx.db).1,
           unverified := (← Checkpoint.gappedRealms ctx head.seq).toList,
           lastRound := ← lastRound.get }

/--
Records what a round came to, and hands back the summary the API reports.

The sync loop inside `resources node` calls this as well, so that a status read
between rounds says when the last one ran rather than "never".
-/
def record (r : Round) : IO Wire.Round := do
  let trouble :=
    match r.pulled.refused, r.pushed.blocked with
    | some (seq, why), _ => s!"the fetch stopped at entry {seq}: {why}"
    | none, some why => why
    | none, none => ""
  let summary : Wire.Round :=
    { ran := ← nowStamp, applied := r.pulled.applied, unreadable := r.pulled.unreadable,
      rejected := r.pulled.rejected.size, pushed := r.pushed.pushed,
      conflicts := r.pushed.conflicts, seq := r.pulled.seq, trouble }
  lastRound.set (some summary)
  return summary

/-- One round of sync, recorded so that a status read afterwards can report it. -/
def round (ctx : Ctx) : IO Wire.Round := do
  let s ← session ctx
  -- Rooted, because `round` is this very declaration everywhere else in here.
  record (← _root_.Resources.Node.round s)

/-- Everything above, as the record the route table takes. -/
def api : Api.NodeApi :=
  { sequencer, keysHeld, unverified, created := create, invited := invite, granted := members,
    stored, attached, status, round }

end Realms
end Node
end Resources
