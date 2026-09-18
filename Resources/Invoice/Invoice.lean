import Resources.Invoice.Epc
import Resources.Store.Budgets

/-!
# Invoices and payment requests

Invoice numbers must be gapless, so the number is allocated by the operation
that writes the document down rather than by whoever asked for it: a gap is a
question an auditor asks, and one nobody can answer afterwards. Every invoice
carries an ISO 11649 reference which the QR code puts into the payer's transfer,
which the importer finds again in the next bank export — closing the loop
between requirement (g) and requirement (b) with no manual reconciliation step.

Reading an invoice is SQL; writing one is an operation, like everything else
that reaches the ledger. What is left in this file is the part `Core` cannot do:
mint an identifier and make sure the payer exists.
-/

open Lean SQLite

namespace Resources

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
  deriving Row

private structure LineRow where
  invoiceId : String
  description : String
  qtyMilli : Int64
  unitMinor : Int64
  taxBp : Int64
  deriving Row

namespace Invoices

private def cols : String :=
  "SELECT id, number, issued, due, payer_id, payer_name, commodity, reference, status,
          note, settled_txn, payment_kind, payment_data, source_account,
          budget_id, pending_txn FROM invoice"

private def hydrate (ctx : Ctx) (rows : Array InvoiceRow) : IO (Array Invoice) := do
  if rows.isEmpty then return #[]
  let ids := "(" ++ String.intercalate ", " (rows.toList.map (fun r => Db.lit r.id)) ++ ")"
  let lines ← Db.rows LineRow ctx.db
    s!"SELECT invoice_id, description, qty_milli, unit_minor, tax_bp FROM invoice_line
       WHERE invoice_id IN {ids} ORDER BY invoice_id, idx"
  return rows.map fun r =>
    let commodity := Commodity.ofCode r.commodity
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
      lines := lines.toList.filterMap fun l =>
        if l.invoiceId == r.id then
          some { description := l.description, qtyMilli := l.qtyMilli.toInt,
                 unitPrice := ⟨commodity, l.unitMinor.toInt⟩, taxBp := l.taxBp.toInt }
        else none }

/--
The lines of the invoice for one person: what they bear, less what they put in.

Both halves are read off the ledger's own legs rather than recomputed, so the
document and the entries cannot disagree. Leaving the second half out would ask
somebody who paid for the taxi to pay for their share of it a second time.
-/
def linesFor (ctx : Ctx) (b : Budget) (owner : PartyId) : IO (List InvoiceLine) := do
  return Budget.linesFor b (← ctx.state.get) owner

/-- The transactions an invoice covers. -/
def sourcesOf (ctx : Ctx) (id : InvoiceId) : IO (Array TxId) := do
  let rows ← Db.rows String ctx.db
    s!"SELECT txn_id FROM invoice_source WHERE invoice_id = {Db.lit id.val}"
  return rows.map (⟨·⟩)

/-- Every transaction that appears on some invoice, with that invoice's number. -/
def invoicedTransactions (ctx : Ctx) : IO (Array (TxId × String)) := do
  let rows ← Db.rows (String × String) ctx.db
    "SELECT s.txn_id, i.number FROM invoice_source s JOIN invoice i ON i.id = s.invoice_id"
  return rows.map fun (t, n) => (⟨t⟩, n)

/-- Every invoice, newest first. -/
def list (ctx : Ctx) (status : Option InvoiceStatus := none) : IO (Array Invoice) := do
  let cond := match status with
    | some s => s!" WHERE status = {Db.lit s.toString}"
    | none => ""
  hydrate ctx (← Db.rows InvoiceRow ctx.db (cols ++ cond ++ " ORDER BY number DESC"))

/-- Looks up an invoice by id or by number. -/
def get? (ctx : Ctx) (idOrNumber : String) : IO (Option Invoice) := do
  let rows ← Db.rows InvoiceRow ctx.db
    (cols ++ s!" WHERE id = {Db.lit idOrNumber} OR number = {Db.lit idOrNumber}")
  return (← hydrate ctx rows)[0]?

/--
Creates an invoice, allocating its number and reference.

The number comes from the counters inside `Op.issueInvoice` rather than from
here, so it is decided at the moment the document is written down and the
sequence stays gapless. What is left for the store is the payer: a document
addressed to somebody this ledger has never heard of would otherwise become a
second record of a person, and `Core` has no way to mint them an id.
-/
def create (ctx : Ctx) (payerName : String) (lines : List InvoiceLine)
    (payment : PaymentRequest) (issued due : Date) (commodity : Commodity := Commodity.eur)
    (note : Option String := none) (sourceAccount : Option String := none)
    (budget : Option BudgetId := none) (pending : Option TxId := none)
    (status : InvoiceStatus := .draft) : IO Invoice := do
  let id : InvoiceId := ⟨← freshId⟩
  let party ← Parties.ensure ctx payerName
  let draft : Invoice :=
    { id, number := "", issued, due, payerId := some party.id, payerName, commodity
      reference := "", status, note, settledTxn := none, payment, sourceAccount
      budgetId := budget, pendingTxn := pending, lines }
  discard <| ctx.commit "system" [.issueInvoice draft []]
  let some raised := (← ctx.state.get).invoice? id
    | throw <| IO.userError s!"the invoice for {payerName} was not written"
  return raised.invoice

/-- Moves an invoice to a new status. -/
def setStatus (ctx : Ctx) (id : InvoiceId) (status : InvoiceStatus) : IO Unit :=
  discard <| ctx.commit "system" [.setInvoiceStatus id status]

/-- Marks an invoice paid and records which transaction settled it. -/
def settle (ctx : Ctx) (id : InvoiceId) (txn : TxId) : IO Unit :=
  discard <| ctx.commit "system" [.settleInvoice id txn]

/--
Deletes an invoice, its lines and the record of what it billed.

When it held the year's highest number the counter is wound back, so removing an
invoice raised by mistake leaves no hole in the sequence — a gap in invoice
numbers is a question an auditor asks, and one nobody can answer afterwards.
Only a draft may go: once a number has been sent to somebody it has to be voided
instead, because they have seen it.
-/
def delete (ctx : Ctx) (id : InvoiceId) : IO Unit :=
  discard <| ctx.commit "system" [.deleteInvoice id]

/--
Settles invoices whose ISO 11649 reference turns up in a transaction's payee or
narration. This is the payoff of putting the reference in the QR code: the
payer's banking app carries it into the transfer, the bank export carries it
back, and the invoice closes itself.

The claim closes with it. The reference is the one match in this system that is
not a guess — everything else about pairing a payment to a request is amount and
timing and hope — so it is the one place a claim may be met automatically.
-/
def reconcile (ctx : Ctx) (actor : String := "reconcile") : IO (Array (String × TxId)) := do
  let open' ← list ctx (some .sent)
  let mut settled : Array (String × TxId) := #[]
  for inv in open' do
    let hits ← Txns.list ctx (.text inv.reference) {} 5
    match hits[0]? with
    | none => pure ()
    | some t =>
      if let some claim := inv.pendingTxn then
        discard <| Pendings.resolve ctx claim t.id actor
      settle ctx inv.id t.id
      settled := settled.push (inv.number, t.id)
  return settled

/--
Raises the invoices for a budget: one per claim addressed to you.

Nothing is computed here. The allocation decided whose the spending was and the
settlement decided who owes whom; this writes one of those claims up as a
document, with the lines read straight off that person's allocation legs.

Only claims that end in an account of yours get an invoice, because an invoice
is a request *you* are making. A settlement plan may well ask two other people
to square up between themselves, and that is not yours to bill.

There is no invoice for your own share. Your share is not a claim — you paid it
at the hut in August, and the allocation recorded it as your expense. What used
to be an invoice "born paid" was a document about nothing outstanding.
-/
def forBudget (ctx : Ctx) (b : Budget) (payment : PaymentRequest) (issued due : Date)
    (commodity : Commodity := Commodity.eur) (note : Option String := none)
    (only : Option (List String) := none) : IO (Array Invoice) := do
  let before ← ctx.state.get
  -- One identifier per claim the budget has raised, which is as many documents
  -- as this can possibly write.
  let mut ids : List InvoiceId := []
  for _ in [0 : (Budget.claims b before).length] do
    ids := ids ++ [⟨← freshId⟩]
  let drafts ← IO.ofExcept
    (Budget.invoicesFor b before payment issued due commodity note only ids)
  if drafts.isEmpty then return #[]
  -- Every payer is made sure of before the documents are written: an invoice
  -- can be addressed to somebody, and it cannot invent them.
  for (inv, _) in drafts do
    discard <| Parties.ensure ctx inv.payerName
  discard <| ctx.commit "system" (drafts.map fun (inv, sources) => Op.issueInvoice inv sources)
  let after ← ctx.state.get
  return (drafts.filterMap fun (inv, _) => (after.invoice? inv.id).map (·.invoice)).toArray

end Invoices

end Resources
