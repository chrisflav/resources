import Resources.Store.Load

/-!
# Committing a set of operations

`Ctx.commit` is the only way anything reaches the ledger. It applies the
operations to the state in memory, and — if every one of them succeeded —
appends them to the log and projects what came back into SQL, inside a single
database transaction.

*The log is written first, and it is what is kept.* The operations become one
event: this member's parts, in one realm, chained by hash to the event before
them. The tables are what that event implies, so the append and the projection go
into the same transaction — an event nobody projected is a table that can be
rebuilt, and a projection with no event behind it is a write nobody can account
for.

Two more properties are worth stating, because the store's callers rely on both.

*A commit is all or nothing.* The operations are applied to a copy of the state;
the first failure throws, with the sentence `applyOp` produced, and neither the
state nor the database has been touched. The store's callers already turn an
`IO.userError` into a 400, so a refused operation reads to the user exactly as
it did when the check lived in the store.

*The audit trail follows the transactions, not the operations.* One commit can
write several transactions and retire several others — a merge does both — so
the revision it records is per transaction, and the caller says which kind each
id was written under.
-/

open Lean SQLite

namespace Resources

namespace Revisions

/-- Appends an audit record for a transaction. -/
def record (db : SQLite) (id : TxId) (actor kind : String) (patch : Json) : IO Unit := do
  let seq ← Db.scalarInt db
    s!"SELECT IFNULL(MAX(seq), 0) + 1 FROM revision WHERE txn_id = {Db.lit id.val}"
  let stamp ← nowStamp
  Db.exec db s!"INSERT INTO revision (txn_id, seq, at, actor, kind, patch)
    VALUES ({Db.lit id.val}, {seq}, {Db.lit stamp}, {Db.lit actor}, {Db.lit kind},
            {Db.lit patch.compress})"

end Revisions

namespace Ctx

/--
Applies operations to the state and projects what they changed into the tables.

`kind` names what the transactions this commit writes were written for
("split", "import", "trip"); `kinds` overrides it per id, which is how a merge
records its sources as `merged-away` while the entry that absorbed them is a
`merge`. `actor` is the token the request arrived under, and it is what the
revision log records — the member the operations are applied on behalf of is
`ctx.member`.
-/
def commitParts (ctx : Ctx) (actor : String) (parts : List (RealmId × Op))
    (kind : String := "write") (kinds : TxId → Option String := fun _ => none) :
    IO (List Change) := do
  let before ← ctx.state.get
  let mut st := before
  let mut changes : List Change := []
  for (realm, op) in parts do
    match applyOp st ctx.member realm op with
    | .error e => throw <| IO.userError e
    | .ok (st', cs) =>
      st := st'
      changes := changes ++ cs
  let eventId ← freshId
  let composedAt ← nowStamp
  ctx.atomically do
    unless parts.isEmpty do
      let (seq, _) ← EventLog.head ctx.db
      discard <| EventLog.append ctx.db
        { id := eventId, author := ctx.member, composedAt, basedOn := seq
          parts := parts.map fun (realm, op) => { realm, op } }
    for c in changes do
      Project.apply ctx.db c
    for c in changes do
      match c with
      | .txn t => Revisions.record ctx.db t.id actor ((kinds t.id).getD kind) (toJson t)
      | .txnDeleted id =>
        -- The patch is what is being retired, so it is read from the state as
        -- it stood before this commit: afterwards there is nothing to record.
        let patch := (before.txn? id).map toJson
        Revisions.record ctx.db id actor ((kinds id).getD "delete") (patch.getD Json.null)
      | _ => pure ()
  ctx.state.set st
  return changes

/--
The same, for operations that all speak about one realm.

Which is nearly all of them: a part names one realm, and only the handful of
things that are true in two rooms at once -- a purse and the bridge it mirrors,
a cost moved into a realm somebody else can read -- are written any other way.
-/
def commit (ctx : Ctx) (actor : String) (ops : List Op) (kind : String := "write")
    (kinds : TxId → Option String := fun _ => none)
    (realm : RealmId := Realm.selfId) : IO (List Change) :=
  ctx.commitParts actor (ops.map fun op => (realm, op)) kind kinds

end Ctx

namespace Change

/-- The transactions a set of changes wrote, in the order they were written. -/
def written (changes : List Change) : Array Transaction :=
  (changes.filterMap fun
    | .txn t => some t
    | _ => none).toArray

end Change

end Resources
