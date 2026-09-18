import Resources.Core.Apply
import Resources.Store.Db

/-!
# Projecting changes into tables

A `Change` is the full new value of something an operation touched, or the id of
something it removed. Projecting one is therefore an upsert or a delete, and
nothing here decides anything: every question of what an operation *meant* was
answered in `Core/Apply.lean`, and a projector that thought for itself would be
a second implementation of the ledger, free to disagree with the first.

That is why this is the only module in the system allowed to write a ledger
table. Everything else composes operations and hands the changes here, so
"could this write have skipped a rule?" is a question about one file.

The tables that are not projections of state are left alone: `event` and
`ledger_head` (the log itself, written by `Store/Replay.lean`), `staged_entry`
(bank lines awaiting review), `revision` (the audit trail, written by `commit`),
and `token` (credentials, which are not ledger data).
-/

open Lean SQLite

namespace Resources

namespace Project

/-! ## Transactions -/

/--
Writes a transaction and its postings, labels and attachments.

The child rows are replaced wholesale rather than diffed: a posting has no
identity of its own beyond its position, so "the legs are now these" is the only
statement that cannot go stale.
-/
def writeTxn (db : SQLite) (t : Transaction) : IO Unit := do
  let now ← nowStamp
  Db.exec db
    s!"INSERT INTO txn (id, date, payee, narration, state, source, created_at, updated_at)
    VALUES ({Db.lit t.id.val}, {Db.lit t.date.toIso}, {Db.litOpt t.payee},
            {Db.lit t.narration}, {Db.lit t.state.toString}, {Db.lit t.source.encode},
            {Db.lit now}, {Db.lit now})
    ON CONFLICT(id) DO UPDATE SET date = excluded.date, payee = excluded.payee,
      narration = excluded.narration, state = excluded.state, source = excluded.source,
      updated_at = excluded.updated_at"
  Db.exec db s!"DELETE FROM posting_all WHERE txn_id = {Db.lit t.id.val}"
  Db.exec db s!"DELETE FROM txn_label WHERE txn_id = {Db.lit t.id.val}"
  Db.exec db s!"DELETE FROM txn_attachment WHERE txn_id = {Db.lit t.id.val}"
  for (p, i) in t.postings.zipIdx do
    Db.exec db s!"INSERT INTO posting_all
      (txn_id, idx, account_id, minor, commodity, party_id, note, origin, tag)
      VALUES ({Db.lit t.id.val}, {i}, {Db.lit p.account.val}, {p.amount.minor},
              {Db.lit p.amount.commodity.code}, {Db.litOpt (p.party.map (·.val))},
              {Db.litOpt p.note}, {Db.litOpt p.origin}, {Db.litOpt p.tag})"
  for (l, i) in t.labels.zipIdx do
    Db.exec db s!"INSERT OR IGNORE INTO txn_label (txn_id, label_id, idx)
                  VALUES ({Db.lit t.id.val}, {Db.lit l.val}, {i})"
  for (a, i) in t.attachments.zipIdx do
    Db.exec db s!"INSERT OR IGNORE INTO txn_attachment (txn_id, sha256, idx)
                  VALUES ({Db.lit t.id.val}, {Db.lit a}, {i})"

/-! ## The rest of the entities -/

/-- Writes a realm and who may see it. -/
private def writeRealm (db : SQLite) (r : Realm) : IO Unit := do
  Db.exec db s!"INSERT INTO realm (id, name, generation)
    VALUES ({Db.lit r.id.val}, {Db.lit r.name}, {r.generation})
    ON CONFLICT(id) DO UPDATE SET name = excluded.name, generation = excluded.generation"
  Db.exec db s!"DELETE FROM realm_member WHERE realm_id = {Db.lit r.id.val}"
  for (m, role) in r.members do
    Db.exec db s!"INSERT INTO realm_member (realm_id, member_id, role)
      VALUES ({Db.lit r.id.val}, {Db.lit m.val}, {Db.lit role.toString})"

/-- Writes an account, rights included. -/
private def writeAccount (db : SQLite) (a : Account) : IO Unit :=
  Db.exec db s!"INSERT INTO account
    (id, name, kind, owner_id, commodity, iban, note, closed_on, realm_id, bridge_of, posters)
    VALUES ({Db.lit a.id.val}, {Db.lit a.name}, {Db.lit a.kind.toString},
            {Db.lit a.owner.val}, {Db.litOpt (a.commodity.map (·.code))}, {Db.litOpt a.iban},
            {Db.litOpt a.note}, {Db.litOpt (a.closedOn.map (·.toIso))},
            {Db.lit a.realm.val}, {Db.litOpt (a.bridgeOf.map (·.val))},
            {Db.lit (String.intercalate "," (a.posters.map (·.val)))})
    ON CONFLICT(id) DO UPDATE SET name = excluded.name, kind = excluded.kind,
      owner_id = excluded.owner_id, commodity = excluded.commodity, iban = excluded.iban,
      note = excluded.note, closed_on = excluded.closed_on, realm_id = excluded.realm_id,
      bridge_of = excluded.bridge_of, posters = excluded.posters"

/-- Writes a budget and the people it is divided among. -/
private def writeBudget (db : SQLite) (b : BudgetState) : IO Unit := do
  let now ← nowStamp
  Db.exec db s!"INSERT INTO budget
    (id, name, note, created_at, closed_at, realm_id, account_id, label_id)
    VALUES ({Db.lit b.budget.id.val}, {Db.lit b.budget.name}, {Db.litOpt b.budget.note},
            {Db.lit now}, {if b.budget.closed then Db.lit now else "NULL"},
            {Db.lit b.realm.val}, {Db.lit b.account.val}, {Db.lit b.label.val})
    ON CONFLICT(id) DO UPDATE SET name = excluded.name, note = excluded.note,
      closed_at = excluded.closed_at, realm_id = excluded.realm_id,
      account_id = excluded.account_id, label_id = excluded.label_id"
  Db.exec db s!"DELETE FROM budget_participant WHERE budget_id = {Db.lit b.budget.id.val}"
  for (p, i) in b.participants.zipIdx do
    Db.exec db s!"INSERT INTO budget_participant (budget_id, idx, owner_id, account, weight)
      VALUES ({Db.lit b.budget.id.val}, {i}, {Db.lit p.owner.val}, {Db.lit p.account},
              {max p.weight 1})"

/-- Writes an invoice, its lines and the outlays it bills for. -/
private def writeInvoice (db : SQLite) (i : InvoiceState) : IO Unit := do
  let now ← nowStamp
  let inv := i.invoice
  let (kind, data) := inv.payment.encode
  Db.exec db s!"INSERT INTO invoice
    (id, number, issued, due, payer_id, payer_name, commodity, reference, status,
     note, settled_txn, created_at, payment_kind, payment_data, source_account,
     budget_id, pending_txn, realm_id)
    VALUES ({Db.lit inv.id.val}, {Db.lit inv.number}, {Db.lit inv.issued.toIso},
            {Db.lit inv.due.toIso}, {Db.litOpt (inv.payerId.map (·.val))},
            {Db.lit inv.payerName}, {Db.lit inv.commodity.code}, {Db.lit inv.reference},
            {Db.lit inv.status.toString}, {Db.litOpt inv.note},
            {Db.litOpt (inv.settledTxn.map (·.val))}, {Db.lit now}, {Db.lit kind},
            {Db.lit data}, {Db.litOpt inv.sourceAccount},
            {Db.litOpt (inv.budgetId.map (·.val))}, {Db.litOpt (inv.pendingTxn.map (·.val))},
            {Db.lit i.realm.val})
    ON CONFLICT(id) DO UPDATE SET number = excluded.number, issued = excluded.issued,
      due = excluded.due, payer_id = excluded.payer_id, payer_name = excluded.payer_name,
      commodity = excluded.commodity, reference = excluded.reference, status = excluded.status,
      note = excluded.note, settled_txn = excluded.settled_txn,
      payment_kind = excluded.payment_kind, payment_data = excluded.payment_data,
      source_account = excluded.source_account, budget_id = excluded.budget_id,
      pending_txn = excluded.pending_txn, realm_id = excluded.realm_id"
  Db.exec db s!"DELETE FROM invoice_line WHERE invoice_id = {Db.lit inv.id.val}"
  for (l, n) in inv.lines.zipIdx do
    Db.exec db s!"INSERT INTO invoice_line
      (invoice_id, idx, description, qty_milli, unit_minor, tax_bp)
      VALUES ({Db.lit inv.id.val}, {n}, {Db.lit l.description}, {l.qtyMilli},
              {l.unitPrice.minor}, {l.taxBp})"
  Db.exec db s!"DELETE FROM invoice_source WHERE invoice_id = {Db.lit inv.id.val}"
  for (t, n) in i.sources.zipIdx do
    Db.exec db s!"INSERT OR IGNORE INTO invoice_source (invoice_id, txn_id, idx)
                  VALUES ({Db.lit inv.id.val}, {Db.lit t.val}, {n})"

/-- Writes a stored file, what was read off it and the lines it prints. -/
private def writeBlob (db : SQLite) (b : BlobState) : IO Unit := do
  let e := b.extracted
  Db.exec db s!"INSERT INTO attachment
    (sha256, mime, bytes, orig_name, created_at, merchant, doc_date, total_minor,
     commodity, raw_text, extractor, cipher_hash, wrapped_key, realm_id, registered_by)
    VALUES ({Db.lit b.file.sha256}, {Db.lit b.file.mime}, {b.file.bytes},
            {Db.litOpt b.file.origName}, {Db.lit b.file.createdAt}, {Db.litOpt e.merchant},
            {Db.litOpt (e.date.map (·.toIso))}, {(e.total.map (·.minor)).getD 0},
            {Db.litOpt (e.total.map (·.commodity.code))}, {Db.lit e.rawText},
            {Db.lit e.extractor}, {Db.litOpt b.file.cipherHash},
            {Db.litOpt b.file.wrappedKey}, {Db.lit b.realm.val}, {Db.lit b.registeredBy.val})
    ON CONFLICT(sha256) DO UPDATE SET mime = excluded.mime, bytes = excluded.bytes,
      orig_name = excluded.orig_name, merchant = excluded.merchant,
      doc_date = excluded.doc_date, total_minor = excluded.total_minor,
      commodity = excluded.commodity, raw_text = excluded.raw_text,
      extractor = excluded.extractor, cipher_hash = excluded.cipher_hash,
      wrapped_key = excluded.wrapped_key, realm_id = excluded.realm_id,
      registered_by = excluded.registered_by"
  Db.exec db s!"DELETE FROM attachment_item WHERE sha256 = {Db.lit b.file.sha256}"
  for (item, i) in b.items.zipIdx do
    Db.exec db s!"INSERT INTO attachment_item
      (sha256, idx, description, qty, minor, commodity)
      VALUES ({Db.lit b.file.sha256}, {i}, {Db.lit item.description},
              {(item.qty.map toString).getD "NULL"}, {item.amount.minor},
              {Db.lit item.amount.commodity.code})"

/-! ## One change -/

/--
Projects one change into the tables.

An upsert or a delete, and never a question: the change already says what the
new value is.
-/
def apply (db : SQLite) (c : Change) : IO Unit := do
  match c with
  | .realm r => writeRealm db r
  | .member m =>
    Db.exec db s!"INSERT INTO member (id, name, party_id)
      VALUES ({Db.lit m.id.val}, {Db.lit m.name}, {Db.lit m.party.val})
      ON CONFLICT(id) DO UPDATE SET name = excluded.name, party_id = excluded.party_id"
  | .memberDeleted id =>
    Db.exec db s!"DELETE FROM member WHERE id = {Db.lit id.val}"
  | .account a => writeAccount db a
  | .accountDeleted id =>
    Db.exec db s!"DELETE FROM account WHERE id = {Db.lit id.val}"
  | .label l =>
    Db.exec db s!"INSERT INTO label (id, name, colour, realm_id)
      VALUES ({Db.lit l.id.val}, {Db.lit l.name}, {Db.litOpt l.colour}, {Db.lit l.realm.val})
      ON CONFLICT(id) DO UPDATE SET name = excluded.name, colour = excluded.colour,
        realm_id = excluded.realm_id"
  | .labelDeleted id =>
    Db.exec db s!"DELETE FROM label WHERE id = {Db.lit id.val}"
  | .party p =>
    Db.exec db s!"INSERT INTO party (id, name, iban, email, note, kind, realm_id)
      VALUES ({Db.lit p.id.val}, {Db.lit p.name}, {Db.litOpt p.iban}, {Db.litOpt p.email},
              {Db.litOpt p.note}, {Db.lit p.kind}, {Db.lit p.realm.val})
      ON CONFLICT(id) DO UPDATE SET name = excluded.name, iban = excluded.iban,
        email = excluded.email, note = excluded.note, kind = excluded.kind,
        realm_id = excluded.realm_id"
  | .group g =>
    let now ← nowStamp
    Db.exec db s!"INSERT INTO party_group (name, members, created_at, realm_id)
      VALUES ({Db.lit g.name}, {Db.lit (String.intercalate "," g.members)}, {Db.lit now},
              {Db.lit g.realm.val})
      ON CONFLICT(name) DO UPDATE SET members = excluded.members,
        realm_id = excluded.realm_id"
  | .groupDeleted name =>
    Db.exec db s!"DELETE FROM party_group WHERE name = {Db.lit name}"
  | .trip t =>
    let now ← nowStamp
    Db.exec db s!"INSERT INTO trip (id, name, starts, ends, payer, note, created_at, realm_id)
      VALUES ({Db.lit t.id}, {Db.lit t.name}, {Db.lit t.starts.toIso}, {Db.lit t.ends.toIso},
              {Db.lit t.payer}, {Db.litOpt t.note}, {Db.lit now}, {Db.lit t.realm.val})
      ON CONFLICT(id) DO UPDATE SET name = excluded.name, starts = excluded.starts,
        ends = excluded.ends, payer = excluded.payer, note = excluded.note,
        realm_id = excluded.realm_id"
  | .tripDeleted name =>
    Db.exec db s!"DELETE FROM trip WHERE name = {Db.lit name}"
  | .rule r =>
    Db.exec db s!"INSERT INTO rule
      (id, name, filter, set_account, add_labels, set_party, priority, realm_id)
      VALUES ({Db.lit r.id.val}, {Db.lit r.name}, {Db.lit r.filterSrc},
              {Db.litOpt r.setAccount}, {Db.lit (String.intercalate "," r.addLabels)},
              {Db.litOpt r.setParty}, {r.priority}, {Db.lit r.realm.val})
      ON CONFLICT(id) DO UPDATE SET name = excluded.name, filter = excluded.filter,
        set_account = excluded.set_account, add_labels = excluded.add_labels,
        set_party = excluded.set_party, priority = excluded.priority,
        realm_id = excluded.realm_id"
  | .ruleDeleted id =>
    Db.exec db s!"DELETE FROM rule WHERE id = {Db.lit id.val}"
  | .txn t => writeTxn db t
  | .txnDeleted id =>
    Db.exec db s!"DELETE FROM txn WHERE id = {Db.lit id.val}"
    -- Otherwise the staged rows stay marked promoted, pointing at nothing, and
    -- the entry can never be brought back without re-importing.
    Db.exec db s!"UPDATE staged_entry SET state = 'new', txn_id = NULL
                  WHERE txn_id = {Db.lit id.val}"
  | .budget b => writeBudget db b
  | .budgetDeleted id =>
    Db.exec db s!"DELETE FROM budget WHERE id = {Db.lit id.val}"
  | .invoice i => writeInvoice db i
  | .invoiceDeleted id =>
    Db.exec db s!"DELETE FROM invoice WHERE id = {Db.lit id.val}"
  | .blob b => writeBlob db b
  | .blobDeleted sha =>
    Db.exec db s!"DELETE FROM attachment WHERE sha256 = {Db.lit sha}"
  | .batch b =>
    Db.exec db s!"INSERT INTO import_batch
      (id, profile, filename, account_id, at, total, duplicates, realm_id)
      VALUES ({Db.lit b.id.val}, {Db.lit b.profile}, {Db.litOpt b.filename},
              {Db.litOpt (b.account.map (·.val))}, {Db.lit b.stamp}, {b.total}, {b.duplicates},
              {Db.lit b.realm.val})
      ON CONFLICT(id) DO UPDATE SET profile = excluded.profile, filename = excluded.filename,
        account_id = excluded.account_id, total = excluded.total,
        duplicates = excluded.duplicates, realm_id = excluded.realm_id"
  | .counter name value =>
    Db.exec db s!"INSERT INTO counter (name, value) VALUES ({Db.lit name}, {value})
      ON CONFLICT(name) DO UPDATE SET value = excluded.value"
  | .fingerprint _ =>
    -- Nothing to write: a fingerprint is read back off the provenance of the
    -- transaction that claimed it, so storing it again would be a second copy
    -- free to disagree with the first.
    pure ()

/-! ## A whole state -/

/--
The tables that are a projection of state, and nothing else.

`event` and `ledger_head` are the ledger itself; `revision` is the audit trail
and `token` is credentials, neither of which the log carries; `staged_entry` is
bank lines waiting to be reviewed, which are not part of the books either, and
`import_batch` stays with it because a staged row hangs off its batch with
`ON DELETE CASCADE`. Batches are upserted by a re-projection instead, which is
the same result for a table nothing ever deletes from.

Two callers need this list and they need the same one: `resources rebuild`,
which throws the projection away and computes it again, and the pull path, which
does the same thing when an event carries a whole state.
-/
def projected : List String :=
  ["txn_label", "txn_attachment", "posting_all", "txn", "invoice_line", "invoice_source",
   "invoice", "budget_participant", "budget", "attachment_item", "attachment",
   "realm_member", "member", "rule", "trip", "party_group", "label", "account", "party",
   "realm", "counter"]

/--
Empties every projected table, inside the caller's transaction.

The tables reference each other in both directions, so what has to hold is that
they are consistent once the caller's transaction commits, not at every step of
emptying and filling them.
-/
def reset (db : SQLite) : IO Unit := do
  Db.exec db "PRAGMA defer_foreign_keys = ON"
  for t in projected do
    Db.exec db s!"DELETE FROM {t}"


/--
Writes an entire state into empty tables: what `resources rebuild` does with what
the log replayed to.

A state is written as `Core.snapshotChanges`, because that list is already the
one thing that cannot leave an entity out — it is what a log's genesis event
amounts to, and a rebuild is the same statement made to the tables instead of to
the state.

Foreign keys are deferred to the end of the caller's transaction. The changes
arrive in sorted order rather than topological order — an account naming its
owner is written before the party it names — and every row those references need
is present by the time the transaction commits.
-/
def all (db : SQLite) (s : State) : IO Unit := do
  Db.exec db "PRAGMA defer_foreign_keys = ON"
  for c in snapshotChanges s do apply db c

end Project

end Resources
