import Resources.Store.Project
import Resources.Store.Replay

/-!
# Reading the state back out of the tables

`Load.fromDb` is the inverse of `Store/Project.lean`: it reads every table and
builds the one value the tables are a projection of. It runs once, when the
store is opened, and after that the state in memory is the authoritative copy.

It is also the test that the projection is faithful. Project a change, load the
database again, and the two states have to be equal — which is exactly what the
`agree` check in the test suite does after every group that writes. Anything a
projection forgot to store shows up there as a difference, rather than as a
surprise on the next restart.

The row shapes here are deliberately this module's own. The reading code in
`Store/Repo.lean` and its neighbours has shapes of the same names, but they sit
*above* this file — the store's writers go through `Ctx.commit`, which needs the
projection, which needs these — so sharing them would be a cycle.
-/

open Lean SQLite

namespace Resources

namespace Load

/-! ## Row shapes -/

private structure RealmRow where
  id : String
  name : String
  generation : Int64
  deriving Row

private structure PairRow where
  a : String
  b : String
  deriving Row

private structure TripleRow where
  a : String
  b : String
  c : String
  deriving Row

private structure MemberRow where
  id : String
  name : String
  partyId : String
  deriving Row

private structure AccountRow where
  id : String
  name : String
  kind : String
  ownerId : Option String
  commodity : Option String
  iban : Option String
  note : Option String
  closedOn : Option String
  realmId : Option String
  bridgeOf : Option String
  posters : Option String
  deriving Row

private structure LabelRow where
  id : String
  name : String
  colour : Option String
  realmId : String
  deriving Row

private structure PartyRow where
  id : String
  name : String
  iban : Option String
  email : Option String
  note : Option String
  kind : String
  realmId : String
  deriving Row

private structure TripRow where
  id : String
  name : String
  starts : String
  ends : String
  payer : String
  note : Option String
  realmId : String
  deriving Row

private structure RuleRow where
  id : String
  name : String
  filter : String
  setAccount : Option String
  addLabels : Option String
  setParty : Option String
  priority : Int64
  realmId : String
  deriving Row

private structure TxnRow where
  id : String
  date : String
  payee : Option String
  narration : String
  state : String
  source : String
  deriving Row

private structure PostingRow where
  txnId : String
  accountId : String
  minor : Int64
  commodity : String
  partyId : Option String
  note : Option String
  origin : Option String
  tag : Option String
  deriving Row

private structure BudgetRow where
  id : String
  name : String
  note : Option String
  closedAt : Option String
  realmId : String
  accountId : String
  labelId : String
  deriving Row

private structure ParticipantRow where
  budgetId : String
  ownerId : String
  ownerName : String
  account : String
  weight : Int64
  deriving Row

private structure InvoiceRow where
  id : String
  number : String
  issued : String
  due : String
  payerId : Option String
  payerName : String
  commodity : String
  reference : String
  status : String
  note : Option String
  settledTxn : Option String
  paymentKind : String
  paymentData : String
  sourceAccount : Option String
  budgetId : Option String
  pendingTxn : Option String
  realmId : String
  deriving Row

private structure LineRow where
  invoiceId : String
  description : String
  qtyMilli : Int64
  unitMinor : Int64
  taxBp : Int64
  deriving Row

private structure AttachmentRow where
  sha256 : String
  mime : String
  bytes : Int64
  origName : Option String
  createdAt : String
  merchant : Option String
  docDate : Option String
  totalMinor : Option Int64
  commodity : Option String
  rawText : Option String
  extractor : Option String
  cipherHash : Option String
  wrappedKey : Option String
  realmId : String
  registeredBy : String
  deriving Row

private structure ItemRow where
  sha256 : String
  description : String
  qty : Option Int64
  minor : Int64
  commodity : String
  deriving Row

private structure BatchRow where
  id : String
  profile : String
  filename : Option String
  accountId : Option String
  stamp : String
  total : Int64
  duplicates : Int64
  realmId : String
  deriving Row

private structure CounterRow where
  name : String
  value : Int64
  deriving Row

/-! ## Helpers -/

/-- Groups rows under the key they belong to, keeping the order they arrived in. -/
private def groupBy {α : Type} (rows : Array α) (key : α → String) :
    Std.HashMap String (Array α) :=
  rows.foldl (fun m r => m.insert (key r) ((m.getD (key r) #[]).push r)) {}

/-- A comma-separated column as a list, with the empty string meaning nothing. -/
private def splitList (s : Option String) : List String :=
  ((s.getD "").splitOn ",").filter (fun x => !x.isEmpty)

/-! ## Reading each table -/

/-- The realms, each carrying the members who may see it. -/
private def realms (db : SQLite) : IO (Std.HashMap String Realm) := do
  let rows ← Db.rows RealmRow db "SELECT id, name, generation FROM realm"
  let members ← Db.rows TripleRow db
    "SELECT realm_id, member_id, role FROM realm_member ORDER BY realm_id, member_id"
  let byRealm := groupBy members (·.a)
  return rows.foldl (fun m r =>
    m.insert r.id
      { id := ⟨r.id⟩, name := r.name, generation := r.generation.toInt.toNat
        members := (byRealm.getD r.id #[]).toList.map fun x =>
          (⟨x.b⟩, (RealmRole.ofString? x.c).getD .viewer) }) {}

/-- The identities this ledger knows. -/
private def members (db : SQLite) : IO (Std.HashMap String Member) := do
  let rows ← Db.rows MemberRow db "SELECT id, name, party_id FROM member"
  return rows.foldl
    (fun m r => m.insert r.id { id := ⟨r.id⟩, name := r.name, party := ⟨r.partyId⟩ }) {}

/-- The accounts, with the realm and the rights each carries. -/
private def accounts (db : SQLite) : IO (Std.HashMap String Account) := do
  let rows ← Db.rows AccountRow db
    "SELECT id, name, kind, owner_id, commodity, iban, note, closed_on,
            realm_id, bridge_of, posters FROM account"
  return rows.foldl (fun m r =>
    m.insert r.id
      { id := ⟨r.id⟩, name := r.name
        kind := (AccountKind.ofString? r.kind).getD .expense
        owner := ⟨r.ownerId.getD Party.selfId.val⟩
        commodity := r.commodity.map Commodity.ofCode
        iban := r.iban, note := r.note
        closedOn := r.closedOn.bind Date.ofIso?
        realm := ⟨r.realmId.getD Realm.selfId.val⟩
        bridgeOf := r.bridgeOf.map (⟨·⟩)
        posters := (splitList r.posters).map (⟨·⟩) }) {}

/-- Every transaction, in every state, with its postings, labels and receipts. -/
private def txns (db : SQLite) : IO (Std.HashMap String Transaction) := do
  let heads ← Db.rows TxnRow db "SELECT id, date, payee, narration, state, source FROM txn"
  -- `posting_all` deliberately: a claim is a transaction that has not happened,
  -- and reading one back must show what it says. It is *summing* that excludes
  -- pendings, which is what the `posting` view is for.
  let postings ← Db.rows PostingRow db
    "SELECT txn_id, account_id, minor, commodity, party_id, note, origin, tag
     FROM posting_all ORDER BY txn_id, idx"
  let labels ← Db.rows PairRow db
    "SELECT txn_id, label_id FROM txn_label ORDER BY txn_id, idx"
  let attachments ← Db.rows PairRow db
    "SELECT txn_id, sha256 FROM txn_attachment ORDER BY txn_id, idx"
  let byTxn := groupBy postings (·.txnId)
  let labelsByTxn := groupBy labels (·.a)
  let filesByTxn := groupBy attachments (·.a)
  return heads.foldl (fun m h =>
    m.insert h.id
      { id := ⟨h.id⟩
        date := (Date.ofIso? h.date).getD default
        payee := h.payee
        narration := h.narration
        state := (TxnState.ofString? h.state).getD .posted
        source := Provenance.decode h.source
        postings := (byTxn.getD h.id #[]).toList.map fun p =>
          { account := ⟨p.accountId⟩
            amount := ⟨Commodity.ofCode p.commodity, p.minor.toInt⟩
            party := p.partyId.map (⟨·⟩)
            note := p.note, origin := p.origin, tag := p.tag }
        labels := (labelsByTxn.getD h.id #[]).toList.map (fun l => ⟨l.b⟩)
        attachments := (filesByTxn.getD h.id #[]).toList.map (·.b) }) {}

/-- The budgets and who each is divided among. -/
private def budgets (db : SQLite) : IO (Std.HashMap String BudgetState) := do
  let rows ← Db.rows BudgetRow db
    "SELECT id, name, note, closed_at, realm_id, account_id, label_id FROM budget"
  let people ← Db.rows ParticipantRow db
    "SELECT p.budget_id, p.owner_id, pa.name, p.account, p.weight
     FROM budget_participant p JOIN party pa ON pa.id = p.owner_id
     ORDER BY p.budget_id, p.idx"
  let byBudget := groupBy people (·.budgetId)
  return rows.foldl (fun m r =>
    m.insert r.id
      { budget := { id := ⟨r.id⟩, name := r.name, note := r.note, closed := r.closedAt.isSome }
        participants := (byBudget.getD r.id #[]).toList.map fun p =>
          { owner := ⟨p.ownerId⟩, name := p.ownerName, account := p.account
            weight := p.weight.toInt.toNat }
        realm := ⟨r.realmId⟩, account := ⟨r.accountId⟩, label := ⟨r.labelId⟩ }) {}

/-- The invoices, their lines and the outlays they bill for. -/
private def invoices (db : SQLite) : IO (Std.HashMap String InvoiceState) := do
  let rows ← Db.rows InvoiceRow db
    "SELECT id, number, issued, due, payer_id, payer_name, commodity, reference, status,
            note, settled_txn, payment_kind, payment_data, source_account,
            budget_id, pending_txn, realm_id FROM invoice"
  let lines ← Db.rows LineRow db
    "SELECT invoice_id, description, qty_milli, unit_minor, tax_bp FROM invoice_line
     ORDER BY invoice_id, idx"
  let sources ← Db.rows PairRow db
    "SELECT invoice_id, txn_id FROM invoice_source ORDER BY invoice_id, idx"
  let linesByInvoice := groupBy lines (·.invoiceId)
  let sourcesByInvoice := groupBy sources (·.a)
  return rows.foldl (fun m r =>
    let commodity := Commodity.ofCode r.commodity
    m.insert r.id
      { invoice :=
          { id := ⟨r.id⟩, number := r.number
            issued := (Date.ofIso? r.issued).getD default
            due := (Date.ofIso? r.due).getD default
            payerId := r.payerId.map (⟨·⟩), payerName := r.payerName
            commodity, reference := r.reference
            status := (InvoiceStatus.ofString? r.status).getD .draft
            note := r.note, settledTxn := r.settledTxn.map (⟨·⟩)
            payment := PaymentRequest.decode r.paymentKind r.paymentData
            sourceAccount := r.sourceAccount
            budgetId := r.budgetId.map (⟨·⟩)
            pendingTxn := r.pendingTxn.map (⟨·⟩)
            lines := (linesByInvoice.getD r.id #[]).toList.map fun l =>
              { description := l.description, qtyMilli := l.qtyMilli.toInt
                unitPrice := ⟨commodity, l.unitMinor.toInt⟩, taxBp := l.taxBp.toInt } }
        sources := (sourcesByInvoice.getD r.id #[]).toList.map (fun s => ⟨s.b⟩)
        realm := ⟨r.realmId⟩ }) {}

/-- The stored files, what was read off each and the lines each prints. -/
private def blobs (db : SQLite) : IO (Std.HashMap String BlobState) := do
  let rows ← Db.rows AttachmentRow db
    "SELECT sha256, mime, bytes, orig_name, created_at, merchant, doc_date, total_minor,
            commodity, raw_text, extractor, cipher_hash, wrapped_key, realm_id, registered_by
     FROM attachment"
  let items ← Db.rows ItemRow db
    "SELECT sha256, description, qty, minor, commodity FROM attachment_item
     ORDER BY sha256, idx"
  let bySha := groupBy items (·.sha256)
  return rows.foldl (fun m r =>
    m.insert r.sha256
      { file := { sha256 := r.sha256, mime := r.mime, bytes := r.bytes.toInt.toNat
                  origName := r.origName, createdAt := r.createdAt
                  cipherHash := r.cipherHash, wrappedKey := r.wrappedKey }
        extracted :=
          { merchant := r.merchant
            date := r.docDate.bind Date.ofIso?
            total := match r.commodity with
              | some c => some ⟨Commodity.ofCode c, (r.totalMinor.map (·.toInt)).getD 0⟩
              | none => none
            rawText := r.rawText.getD ""
            extractor := r.extractor.getD "" }
        items := (bySha.getD r.sha256 #[]).toList.map fun i =>
          { description := i.description, qty := i.qty.map (·.toInt)
            amount := ⟨Commodity.ofCode i.commodity, i.minor.toInt⟩ }
        registeredBy := ⟨r.registeredBy⟩
        realm := ⟨r.realmId⟩ }) {}

/-! ## The whole state -/

/--
Reads the whole database into one state.

The fingerprints are not read from a table of their own: an import fingerprint
is spoken for exactly when some transaction carries it in its provenance, so
deriving it is the only description that cannot drift from the entries.
-/
def fromDb (db : SQLite) : IO State := do
  let labelRows ← Db.rows LabelRow db "SELECT id, name, colour, realm_id FROM label"
  let partyRows ← Db.rows PartyRow db
    "SELECT id, name, iban, email, note, kind, realm_id FROM party"
  let groupRows ← Db.rows TripleRow db "SELECT name, members, realm_id FROM party_group"
  let tripRows ← Db.rows TripRow db
    "SELECT id, name, starts, ends, payer, note, realm_id FROM trip"
  let ruleRows ← Db.rows RuleRow db
    "SELECT id, name, filter, set_account, add_labels, set_party, priority, realm_id
     FROM rule"
  let batchRows ← Db.rows BatchRow db
    "SELECT id, profile, filename, account_id, at, total, duplicates, realm_id
     FROM import_batch"
  let counterRows ← Db.rows CounterRow db "SELECT name, value FROM counter"
  let everyTxn ← txns db
  let fingerprints := (sortedValues everyTxn).foldl (fun (fps : Std.HashSet String) t =>
    match t.source with
    | .imported _ fp => fps.insert fp
    | _ => fps) {}
  let everyRealm ← realms db
  let everyMember ← members db
  let everyAccount ← accounts db
  let everyBudget ← budgets db
  let everyInvoice ← invoices db
  let everyBlob ← blobs db
  return {
    realms := everyRealm
    members := everyMember
    accounts := everyAccount
    labels := labelRows.foldl (fun m r =>
      m.insert r.id { id := ⟨r.id⟩, name := r.name, colour := r.colour
                      realm := ⟨r.realmId⟩ }) {}
    parties := partyRows.foldl (fun m r =>
      m.insert r.id { id := ⟨r.id⟩, name := r.name, iban := r.iban, email := r.email,
                      note := r.note, kind := r.kind, realm := ⟨r.realmId⟩ }) {}
    groups := groupRows.foldl (fun m r =>
      m.insert r.a { name := r.a, members := splitList (some r.b), realm := ⟨r.c⟩ }) {}
    trips := tripRows.foldl (fun m r =>
      m.insert r.name
        { id := r.id, name := r.name
          starts := (Date.ofIso? r.starts).getD default
          ends := (Date.ofIso? r.ends).getD default
          payer := r.payer, note := r.note, realm := ⟨r.realmId⟩ }) {}
    rules := ruleRows.foldl (fun m r =>
      m.insert r.id
        { id := ⟨r.id⟩, name := r.name, filterSrc := r.filter
          filter := (Filter.parse r.filter).toOption.getD .all
          setAccount := r.setAccount, addLabels := splitList r.addLabels
          setParty := r.setParty, priority := r.priority.toInt, realm := ⟨r.realmId⟩ }) {}
    txns := everyTxn
    budgets := everyBudget
    invoices := everyInvoice
    blobs := everyBlob
    batches := batchRows.foldl (fun m r =>
      m.insert r.id
        { id := ⟨r.id⟩, profile := r.profile, filename := r.filename
          account := r.accountId.map (⟨·⟩), stamp := r.stamp
          total := r.total.toInt.toNat, duplicates := r.duplicates.toInt.toNat
          realm := ⟨r.realmId⟩ }) {}
    counters := counterRows.foldl (fun m r => m.insert r.name r.value.toInt) {}
    fingerprints }

end Load

/-! ## Opening the store -/

namespace Ctx

/--
Starts the log off from whatever is already in the tables.

A store whose log has entries is left alone. One with none gets exactly one
event, at sequence 1, whose single operation is a snapshot of the state that was
just read — so from the first entry onwards the log and the tables say the same
thing, and replaying gives back what was there rather than an empty ledger.

The two cases differ only in what the snapshot contains. An existing database
carries its whole ledger into the first event, which is what makes the log
adoptable without an export: nothing has to be re-entered, and the history that
predates the log is one entry saying "this is where we came in". A database
created a moment ago carries `State.init` and the party that is you, which is all
the migrations put there.
-/
private def genesis (db : SQLite) (s : State) : IO Unit := do
  if (← Db.scalarInt db "SELECT COUNT(*) FROM event") > 0 then return
  let e : Event :=
    { id := ← freshId
      author := Member.selfId
      composedAt := ← nowStamp
      basedOn := 0
      parts := [{ realm := Realm.selfId, op := .snapshot s }] }
  SQLite.transaction db (discard <| EventLog.append db e) .immediate

/--
Opens (creating if needed) the store at `cfg`, running any pending migrations
and reading the tables into the state they are a projection of.

The chain is checked first, every time. `Replay.chainError?` hashes the stored
rows and asks the three questions an append already asks — that the sequence
numbers run, that each row's hash is its own bytes, that each row follows the one
before — and the one an append cannot ask of itself, which is whether
`ledger_head` still names the last row. It does not replay: nothing is decoded
and `step` is not called, so the cost of opening a store grows with the bytes in
its log and not with what those bytes mean.

It is checked on the way *in* because the head is what the next append chains
onto. A store opened with a head that has drifted writes its next event onto a
fork of its own history, and the first thing anybody notices is a sequencer
refusing an entry for a `prevHash` nobody can explain. Refusing here costs one
pass over the log and turns that into a sentence.

`verifyChain := false` exists for `resources rebuild`, which is the one command
whose job is to look at a log this refused to open.
-/
def «open» (cfg : Config) (verifyChain : Bool := true) : IO Ctx := do
  Files.privateDir cfg.dataDir
  Files.privateDir cfg.blobDir
  let db ← SQLite.open cfg.dbPath (busyTimeoutMs := 5000)
  Db.exec db "PRAGMA journal_mode = WAL"
  Db.exec db "PRAGMA foreign_keys = ON"
  Db.exec db "PRAGMA synchronous = NORMAL"
  discard <| Schema.migrate db
  if verifyChain then
    if let some complaint ← Replay.chainError? db then
      throw <| IO.userError s!"the event log in {cfg.dbPath} is not whole: {complaint}. \
        The log is the ledger and the tables are a cache of it, so nothing is opened until \
        somebody has looked: run 'resources rebuild', which computes the tables from the \
        events again and puts the head back on the last of them. If an event's own bytes are \
        what changed, then the ledger is what changed, and no rebuild will put that back."
  let loaded ← Load.fromDb db
  genesis db loaded
  let state ← IO.mkRef loaded
  -- Last, because SQLite's journal files only exist once it has opened them.
  Files.harden cfg
  return { db, cfg, state }

end Ctx

end Resources
