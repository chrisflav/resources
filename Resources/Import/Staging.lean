import Resources.Import.Profile
import Resources.Store.Repo

/-!
# Staging, deduplication and promotion

Importing never writes to the ledger. It writes `staged_entry` rows keyed by a
fingerprint; a human then promotes the ones they accept. Re-importing an
overlapping date range — which happens constantly — is therefore a no-op, and
that is the property that makes the whole import path safe to re-run.
-/

open Lean SQLite

namespace Resources

/-- A parsed bank line awaiting review. -/
structure StagedEntry where
  id : StagedId
  batch : BatchId
  fingerprint : String
  raw : RawRecord
  /-- `new`, `duplicate`, `promoted` or `ignored`. -/
  state : String
  suggestedAccount : Option String
  txnId : Option TxId
  deriving Repr, ToJson, Inhabited

/-- One run of an importer over one file. -/
structure ImportBatch where
  id : BatchId
  profile : String
  filename : Option String
  account : Option AccountId
  stamp : String
  total : Nat
  duplicates : Nat
  deriving Repr, ToJson

private structure StagedRow where
  id : String
  batchId : String
  fingerprint : String
  date : String
  payee : Option String
  purpose : Option String
  minor : Int64
  commodity : String
  counterIban : Option String
  bankRef : Option String
  state : String
  suggestedAccount : Option String
  txnId : Option String
  deriving Row

private structure BatchRow where
  id : String
  profile : String
  filename : Option String
  accountId : Option String
  stamp : String
  total : Int64
  duplicates : Int64
  deriving Row

private structure RuleRow where
  id : String
  name : String
  filter : String
  setAccount : Option String
  addLabels : Option String
  setParty : Option String
  priority : Int64
  deriving Row

/-! ## Rules -/

/-- A categorisation rule: a filter plus what to do when it matches. -/
structure Rule where
  id : RuleId
  name : String
  /-- Source text of the filter, so it round-trips through the database. -/
  filterSrc : String
  filter : Filter
  setAccount : Option String
  addLabels : List String
  setParty : Option String
  priority : Int
  deriving Repr

namespace Rules

private def ofRow (r : RuleRow) : Rule :=
  { id := ⟨r.id⟩, name := r.name, filterSrc := r.filter,
    filter := (Filter.parse r.filter).toOption.getD .all,
    setAccount := r.setAccount,
    addLabels := ((r.addLabels.getD "").splitOn ",").filter (fun s => !s.isEmpty),
    setParty := r.setParty, priority := r.priority.toInt }

/-- Every rule, highest priority first. -/
def list (ctx : Ctx) : IO (Array Rule) := do
  let rs ← Db.rows RuleRow ctx.db
    "SELECT id, name, filter, set_account, add_labels, set_party, priority FROM rule
     ORDER BY priority DESC, name"
  return rs.map ofRow

/-- Creates a rule. The filter is parsed eagerly so a broken one is rejected at creation. -/
def add (ctx : Ctx) (name filterSrc : String) (setAccount : Option String := none)
    (addLabels : List String := []) (setParty : Option String := none)
    (priority : Int := 0) : IO Rule := do
  let f ← IO.ofExcept (Filter.parse filterSrc)
  let id ← freshId
  Db.exec ctx.db s!"INSERT INTO rule
    (id, name, filter, set_account, add_labels, set_party, priority)
    VALUES ({Db.lit id}, {Db.lit name}, {Db.lit filterSrc}, {Db.litOpt setAccount},
            {Db.lit (String.intercalate "," addLabels)}, {Db.litOpt setParty}, {priority})"
  return { id := ⟨id⟩, name, filterSrc, filter := f, setAccount, addLabels, setParty, priority }

/-- Deletes a rule by id or name. -/
def delete (ctx : Ctx) (idOrName : String) : IO Unit :=
  Db.exec ctx.db
    s!"DELETE FROM rule WHERE id = {Db.lit idOrName} OR name = {Db.lit idOrName}"

end Rules

/-! ## Import batches -/

namespace Imports

/--
The dedup key.

Prefers the bank's own reference when there is one. Without it the key falls
back to the visible fields, plus how many times that combination has already
occurred in this file — because a statement legitimately contains two identical
transfers on the same day, and collapsing them loses one silently. Counting
occurrences keeps re-importing idempotent (the same file yields the same
indices) while still admitting genuine repeats.
-/
def fingerprint (account : AccountId) (r : RawRecord) (occurrence : Nat := 0) : String :=
  let key :=
    match r.bankRef with
    | some ref => ref
    | none => (r.payee.getD "") ++ "|" ++ (r.purpose.getD "") ++ "|#" ++ toString occurrence
  Sha256.hex <| String.intercalate " "
    [ account.val, r.date.toIso, toString r.amount.minor, r.amount.commodity.code, key ]

private def ofStagedRow (r : StagedRow) : StagedEntry :=
  { id := ⟨r.id⟩, batch := ⟨r.batchId⟩, fingerprint := r.fingerprint
    raw := { date := (Date.ofIso? r.date).getD default
             amount := ⟨Commodity.ofCode r.commodity, r.minor.toInt⟩
             payee := r.payee, purpose := r.purpose
             counterIban := r.counterIban, bankRef := r.bankRef }
    state := r.state, suggestedAccount := r.suggestedAccount, txnId := r.txnId.map (⟨·⟩) }

private def ofBatchRow (r : BatchRow) : ImportBatch :=
  { id := ⟨r.id⟩, profile := r.profile, filename := r.filename,
    account := r.accountId.map (⟨·⟩), stamp := r.stamp,
    total := r.total.toInt.toNat, duplicates := r.duplicates.toInt.toNat }

private def stagedCols : String :=
  "SELECT id, batch_id, fingerprint, date, payee, purpose, minor, commodity,
          counter_iban, bank_ref, state, suggested_account, txn_id FROM staged_entry"

private def batchCols : String :=
  "SELECT id, profile, filename, account_id, at, total, duplicates FROM import_batch"

/--
Stages parsed records against a bank account. Records whose fingerprint is
already known are recorded as duplicates and never become transactions.
-/
def stage (ctx : Ctx) (account : AccountId) (profile : String) (filename : Option String)
    (records : Array RawRecord) : IO (ImportBatch × Array StagedEntry) := do
  let batchId ← freshId
  let stamp ← nowStamp
  ctx.transaction do
    Db.exec ctx.db s!"INSERT INTO import_batch
      (id, profile, filename, account_id, at, total, duplicates)
      VALUES ({Db.lit batchId}, {Db.lit profile}, {Db.litOpt filename}, {Db.lit account.val},
              {Db.lit stamp}, 0, 0)"
    let mut dups := 0
    let mut occurrences : Std.HashMap String Nat := {}
    for r in records do
      -- Count identical-looking rows within this file, so a real pair of them
      -- both survive while a re-import of the same file still dedupes.
      let base := r.date.toIso ++ "|" ++ toString r.amount.minor ++ "|"
        ++ (r.payee.getD "") ++ "|" ++ (r.purpose.getD "")
      let occurrence := occurrences.getD base 0
      occurrences := occurrences.insert base (occurrence + 1)
      let fp := fingerprint account r occurrence
      let seen ← Db.scalarInt ctx.db
        s!"SELECT COUNT(*) FROM staged_entry WHERE fingerprint = {Db.lit fp}"
      if seen > 0 then
        dups := dups + 1
      else
        let id ← freshId
        Db.exec ctx.db s!"INSERT INTO staged_entry
          (id, batch_id, fingerprint, date, payee, purpose, minor, commodity,
           counter_iban, bank_ref, state, suggested_account, txn_id)
          VALUES ({Db.lit id}, {Db.lit batchId}, {Db.lit fp}, {Db.lit r.date.toIso},
                  {Db.litOpt r.payee}, {Db.litOpt r.purpose}, {r.amount.minor},
                  {Db.lit r.amount.commodity.code}, {Db.litOpt r.counterIban},
                  {Db.litOpt r.bankRef}, 'new', NULL, NULL)"
    Db.exec ctx.db s!"UPDATE import_batch SET total = {records.size}, duplicates = {dups}
                      WHERE id = {Db.lit batchId}"
  let batch ← Db.row? BatchRow ctx.db (batchCols ++ s!" WHERE id = {Db.lit batchId}")
  let staged ← Db.rows StagedRow ctx.db
    (stagedCols ++ s!" WHERE batch_id = {Db.lit batchId} ORDER BY date, id")
  return ((batch.map ofBatchRow).getD
            { id := ⟨batchId⟩, profile, filename, account := some account,
              stamp, total := records.size, duplicates := 0 },
          staged.map ofStagedRow)

/-- Import batches, newest first. -/
def listBatches (ctx : Ctx) : IO (Array ImportBatch) := do
  let rs ← Db.rows BatchRow ctx.db (batchCols ++ " ORDER BY at DESC")
  return rs.map ofBatchRow

/-- Staged entries, optionally restricted to a batch and/or a state. -/
def listStaged (ctx : Ctx) (batch : Option BatchId := none) (state : Option String := none) :
    IO (Array StagedEntry) := do
  let conds := (batch.map (fun b => s!"batch_id = {Db.lit b.val}")).toList
             ++ (state.map (fun s => s!"state = {Db.lit s}")).toList
  let whereClause := if conds.isEmpty then "" else " WHERE " ++ String.intercalate " AND " conds
  let rs ← Db.rows StagedRow ctx.db (stagedCols ++ whereClause ++ " ORDER BY date, id")
  return rs.map ofStagedRow

/-- One staged entry. -/
def staged? (ctx : Ctx) (id : StagedId) : IO (Option StagedEntry) := do
  let r ← Db.row? StagedRow ctx.db (stagedCols ++ s!" WHERE id = {Db.lit id.val}")
  return r.map ofStagedRow

/-- Sets the account a staged entry will be categorised into when promoted. -/
def suggest (ctx : Ctx) (id : StagedId) (account : String) : IO Unit :=
  Db.exec ctx.db s!"UPDATE staged_entry SET suggested_account = {Db.lit account}
                    WHERE id = {Db.lit id.val}"

/-- Marks staged entries as deliberately not imported. -/
def ignore (ctx : Ctx) (ids : Array StagedId) : IO Unit := do
  for id in ids do
    Db.exec ctx.db s!"UPDATE staged_entry SET state = 'ignored' WHERE id = {Db.lit id.val}"

/-- The default counter account for an uncategorised amount. -/
def defaultCounterAccount (a : Amount) : String :=
  if a.minor < 0 then "Expenses.Unclassified" else "Income.Unclassified"

/-- Builds the transaction a staged entry would become, without writing it. -/
def previewTxn (ctx : Ctx) (e : StagedEntry) (bankAccount : AccountId)
    (env : Filter.Env) (rules : Array Rule) : IO Transaction := do
  let base : Transaction :=
    { id := ⟨e.id.val⟩
      date := e.raw.date
      payee := e.raw.payee
      narration := e.raw.purpose.getD ""
      postings := [{ account := bankAccount, amount := e.raw.amount }]
      source := .imported e.batch e.fingerprint }
  -- Rules see the entry as a transaction, so the filter language is reused verbatim.
  let matched := rules.find? (fun r => r.filter.eval env base)
  let accountName :=
    e.suggestedAccount.getD
      ((matched.bind (·.setAccount)).getD (defaultCounterAccount e.raw.amount))
  let counter ← Accounts.ensure ctx accountName
  let labelIds ← ((matched.map (·.addLabels)).getD []).mapM fun n => do
    return (← Labels.ensure ctx n).id
  let partyName : Option String := (matched.bind (·.setParty)) <|> e.raw.payee
  let partyId ← match partyName with
    | some p => do let pt ← Parties.ensure ctx p; pure (some pt.id)
    | none => pure none
  let withParty : Transaction :=
    { base with labels := labelIds
                postings := base.postings.map (fun p => { p with party := partyId }) }
  -- Both legs carry the bank line they came from, so a later merge is reversible.
  return (withParty.autoBalance counter.id).withOrigin e.fingerprint

/--
Turns staged entries into transactions. Returns the ids created. Entries that
are not in the `new` state are skipped.
-/
def promote (ctx : Ctx) (ids : Array StagedId) (actor : String) : IO (Array TxId) := do
  let accounts ← Accounts.list ctx
  let labels ← Labels.list ctx
  let parties ← Parties.list ctx
  let env := Filter.Env.ofLists accounts.toList labels.toList parties.toList
  let rules ← Rules.list ctx
  let mut created : Array TxId := #[]
  for id in ids do
    let some e ← staged? ctx id | continue
    if e.state != "new" then continue
    let batchRow ← Db.row? BatchRow ctx.db (batchCols ++ s!" WHERE id = {Db.lit e.batch.val}")
    let some batch := batchRow.map ofBatchRow | continue
    let some bankAccount := batch.account | continue
    let t ← previewTxn ctx e bankAccount env rules
    let txId ← freshId
    let t := { t with id := (⟨txId⟩ : TxId) }
    match t.validate with
    | .error err => throw <| IO.userError s!"staged entry {id.val}: {err}"
    | .ok bt =>
      Txns.put ctx bt actor "import"
      Db.exec ctx.db s!"UPDATE staged_entry SET state = 'promoted', txn_id = {Db.lit txId}
                        WHERE id = {Db.lit id.val}"
      created := created.push ⟨txId⟩
  return created

/-- Promotes every new entry in a batch. -/
def promoteBatch (ctx : Ctx) (batch : BatchId) (actor : String) : IO (Array TxId) := do
  let entries ← listStaged ctx (some batch) (some "new")
  promote ctx (entries.map (·.id)) actor

end Imports

end Resources
