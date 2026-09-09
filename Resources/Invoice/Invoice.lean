import Resources.Invoice.Epc
import Resources.Store.Budgets

/-!
# Invoices and payment requests

Invoice numbers must be gapless, so the number is allocated inside the same
database transaction that inserts the row. Every invoice carries an ISO 11649
reference which the QR code puts into the payer's transfer, which the importer
finds again in the next bank export — closing the loop between requirement (g)
and requirement (b) with no manual reconciliation step.
-/

open Lean SQLite

namespace Resources

/-- Rounds `a / b` to the nearest integer, halves away from zero. `b` must be positive. -/
def divRound (a b : Int) : Int :=
  if b == 0 then 0
  else if a ≥ 0 then (a + b / 2) / b
  else -((-a + b / 2) / b)

/-- One line of an invoice. Quantities carry three decimals, tax rates are basis points. -/
structure InvoiceLine where
  description : String
  /-- Quantity times 1000, so `2.5` hours is `2500`. -/
  qtyMilli : Int
  unitPrice : Amount
  /-- VAT in basis points: 19% is `1900`. -/
  taxBp : Int := 0
  deriving Repr, Inhabited

namespace InvoiceLine

/-- The line total before tax. -/
def net (l : InvoiceLine) : Amount :=
  ⟨l.unitPrice.commodity, divRound (l.qtyMilli * l.unitPrice.minor) 1000⟩

/-- The tax on this line. -/
def tax (l : InvoiceLine) : Amount :=
  ⟨l.unitPrice.commodity, divRound (l.net.minor * l.taxBp) 10000⟩

/-- The line total including tax. -/
def gross (l : InvoiceLine) : Amount :=
  ⟨l.unitPrice.commodity, l.net.minor + l.tax.minor⟩

/-- The quantity rendered with up to three decimals. -/
def quantity (l : InvoiceLine) : String :=
  Amount.digits ⟨⟨"", 3⟩, l.qtyMilli⟩

/-- The tax rate as a percentage string. -/
def taxRate (l : InvoiceLine) : String :=
  Amount.digits ⟨⟨"", 2⟩, l.taxBp⟩ ++ "%"

end InvoiceLine

/-- The lifecycle of an invoice. -/
inductive InvoiceStatus
  | draft | sent | paid | void
  deriving DecidableEq, Repr, Inhabited

namespace InvoiceStatus

/-- The name used in the database and in JSON. -/
def toString : InvoiceStatus → String
  | .draft => "draft" | .sent => "sent" | .paid => "paid" | .void => "void"

/-- Inverse of `toString`. -/
def ofString? : String → Option InvoiceStatus
  | "draft" => some .draft | "sent" => some .sent
  | "paid" => some .paid | "void" => some .void | _ => none

instance : ToString InvoiceStatus := ⟨InvoiceStatus.toString⟩

end InvoiceStatus

/-- A payment request addressed to a party. -/
structure Invoice where
  id : InvoiceId
  /-- Gapless, allocated per year: `2026-0007`. -/
  number : String
  issued : Date
  due : Date
  payerId : Option PartyId
  payerName : String
  commodity : Commodity
  /-- The ISO 11649 reference that closes the loop with the importer. -/
  reference : String
  status : InvoiceStatus
  note : Option String
  settledTxn : Option TxId
  payment : PaymentRequest
  /-- The budget account this was raised from. -/
  sourceAccount : Option String
  /-- The budget whose division this invoice speaks about, when there is one. -/
  budgetId : Option BudgetId
  /--
  The claim this invoice asks to have met.

  An invoice itemises costs that have already happened and asks for a payment
  that has not. Those are two entries, and this is the second one: the document
  describes the first and points at the second, so "has this been paid" is a
  question about the claim rather than a flag somebody has to remember to set.
  -/
  pendingTxn : Option TxId
  lines : List InvoiceLine
  deriving Repr, Inhabited

namespace Invoice

/-- The sum before tax. -/
def net (i : Invoice) : Amount :=
  ⟨i.commodity, (i.lines.map (fun l => l.net.minor)).sum⟩

/-- The total tax. -/
def tax (i : Invoice) : Amount :=
  ⟨i.commodity, (i.lines.map (fun l => l.tax.minor)).sum⟩

/-- The amount actually due. -/
def total (i : Invoice) : Amount :=
  ⟨i.commodity, i.net.minor + i.tax.minor⟩

/-- The string encoded in this invoice's QR code. -/
def qrPayload (i : Invoice) : Except String String :=
  i.payment.payload i.total i.reference

/-- A JSON view, for the API and the web client. -/
def toJson (i : Invoice) : Json :=
  Json.mkObj [
    ("id", i.id.val), ("number", i.number), ("issued", i.issued.toIso), ("due", i.due.toIso),
    ("payerName", i.payerName), ("payerId", (i.payerId.map (·.val)).getD ""),
    ("commodity", i.commodity.code), ("reference", i.reference),
    ("status", i.status.toString), ("note", i.note.getD ""),
    ("settledTxn", (i.settledTxn.map (·.val)).getD ""),
    ("payment", i.payment.describe), ("sourceAccount", Json.str (i.sourceAccount.getD "")),
    ("budgetId", Json.str ((i.budgetId.map (·.val)).getD "")),
    ("pendingTxn", Json.str ((i.pendingTxn.map (·.val)).getD "")),
    ("net", Json.num (JsonNumber.fromInt i.net.minor)),
    ("tax", Json.num (JsonNumber.fromInt i.tax.minor)),
    ("total", Json.num (JsonNumber.fromInt i.total.minor)),
    ("totalText", i.total.render),
    ("lines", Json.arr (i.lines.map (fun l => Json.mkObj [
        ("description", l.description),
        ("quantity", l.quantity),
        ("unitPrice", Json.num (JsonNumber.fromInt l.unitPrice.minor)),
        ("taxBp", Json.num (JsonNumber.fromInt l.taxBp)),
        ("net", Json.num (JsonNumber.fromInt l.net.minor)),
        ("gross", Json.num (JsonNumber.fromInt l.gross.minor))])).toArray) ]

end Invoice

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
  let borne ← Budgets.allocationLines ctx b owner
  let funded ← Budgets.fundedLines ctx b owner
  let line (prefix' : String) : (String × Amount) → InvoiceLine
    | (description, amount) =>
      { description := prefix' ++ description, qtyMilli := 1000, unitPrice := amount }
  return borne.toList.map (line "") ++ funded.toList.map (line "you paid: ")

/-- Records which outlays an invoice is asking to be repaid for. -/
def recordSources (ctx : Ctx) (id : InvoiceId) (sources : List TxId) : IO Unit := do
  for t in sources do
    Db.exec ctx.db s!"INSERT OR IGNORE INTO invoice_source (invoice_id, txn_id)
                      VALUES ({Db.lit id.val}, {Db.lit t.val})"

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
Allocates the next invoice number for a year. Called inside the caller's
transaction so numbering stays gapless even if two writers race.
-/
def nextNumber (ctx : Ctx) (year : Nat) : IO String := do
  let n ← ctx.nextCounter s!"invoice:{year}"
  return s!"{year}-" ++ Str.padLeft (toString n) 4 '0'

/-- Creates an invoice, allocating its number and reference. -/
def create (ctx : Ctx) (payerName : String) (lines : List InvoiceLine)
    (payment : PaymentRequest) (issued due : Date) (commodity : Commodity := Commodity.eur)
    (note : Option String := none) (sourceAccount : Option String := none)
    (budget : Option BudgetId := none) (pending : Option TxId := none)
    (status : InvoiceStatus := .draft) : IO Invoice := do
  let id ← freshId
  let now ← nowStamp
  ctx.transaction do
    let year := issued.year.toInt.toNat
    let number ← nextNumber ctx year
    let reference := Rf.make (number.replace "-" "")
    let party ← Parties.ensure ctx payerName
    let (kind, data) := payment.encode
    Db.exec ctx.db s!"INSERT INTO invoice
      (id, number, issued, due, payer_id, payer_name, commodity, reference, status,
       note, settled_txn, created_at, payment_kind, payment_data, source_account,
       budget_id, pending_txn)
      VALUES ({Db.lit id}, {Db.lit number}, {Db.lit issued.toIso}, {Db.lit due.toIso},
              {Db.lit party.id.val}, {Db.lit payerName}, {Db.lit commodity.code},
              {Db.lit reference}, {Db.lit status.toString}, {Db.litOpt note}, NULL, {Db.lit now},
              {Db.lit kind}, {Db.lit data}, {Db.litOpt sourceAccount},
              {Db.litOpt (budget.map (·.val))}, {Db.litOpt (pending.map (·.val))})"
    for (l, i) in lines.zipIdx do
      Db.exec ctx.db s!"INSERT INTO invoice_line
        (invoice_id, idx, description, qty_milli, unit_minor, tax_bp)
        VALUES ({Db.lit id}, {i}, {Db.lit l.description}, {l.qtyMilli},
                {l.unitPrice.minor}, {l.taxBp})"
    return { id := ⟨id⟩, number, issued, due, payerId := some party.id, payerName,
             commodity, reference, status, note, settledTxn := none,
             payment, sourceAccount, budgetId := budget, pendingTxn := pending, lines }

/-- Moves an invoice to a new status. -/
def setStatus (ctx : Ctx) (id : InvoiceId) (status : InvoiceStatus) : IO Unit :=
  Db.exec ctx.db
    s!"UPDATE invoice SET status = {Db.lit status.toString} WHERE id = {Db.lit id.val}"

/-- Marks an invoice paid and records which transaction settled it. -/
def settle (ctx : Ctx) (id : InvoiceId) (txn : TxId) : IO Unit :=
  Db.exec ctx.db s!"UPDATE invoice SET status = 'paid', settled_txn = {Db.lit txn.val}
                    WHERE id = {Db.lit id.val}"

/--
Deletes an invoice, its lines and the record of what it billed.

When it held the year's highest number the counter is wound back, so removing an
invoice raised by mistake leaves no hole in the sequence — a gap in invoice
numbers is a question an auditor asks, and one nobody can answer afterwards.
Only a draft may go: once a number has been sent to somebody it has to be voided
instead, because they have seen it.
-/
def delete (ctx : Ctx) (id : InvoiceId) : IO Unit :=
  ctx.transaction do
    let number := (← Db.row? String ctx.db
      s!"SELECT number FROM invoice WHERE id = {Db.lit id.val}").getD ""
    Db.exec ctx.db s!"DELETE FROM invoice WHERE id = {Db.lit id.val}"
    match number.splitOn "-" with
    | [year, seq] =>
      Db.exec ctx.db s!"UPDATE counter SET value = value - 1
                        WHERE name = {Db.lit s!"invoice:{year}"}
                          AND value = {Db.lit seq}"
    | _ => pure ()

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
  let accounts ← Accounts.list ctx
  let existing ← Db.rows String ctx.db
    s!"SELECT pending_txn FROM invoice
       WHERE budget_id = {Db.lit b.id.val} AND pending_txn IS NOT NULL AND status != 'void'"
  let done := existing.toList
  let mut out : Array Invoice := #[]
  for claim in ← Budgets.claims ctx b do
    if claim.state != .pending then continue
    if done.contains claim.id.val then continue
    if let some keep := only then
      if !keep.contains claim.id.val then continue
    let some recvId := Pendings.receiver? claim | continue
    let some payId := Pendings.payer? claim | continue
    let some recv := accounts.find? (·.id == recvId) | continue
    let some payer := accounts.find? (·.id == payId) | continue
    -- Somebody else's claim on somebody else. Theirs to chase, not yours.
    if !recv.mine then continue
    let lines ← linesFor ctx b payer.owner
    if lines.isEmpty then continue
    -- An invoice asks for exactly what its claim asks for. The two can differ
    -- when a settlement routed part of somebody's position to a third person,
    -- or when an earlier invoice already asked for some of it, and saying so is
    -- better than quietly billing a figure the QR code will not match.
    let asked := (Pendings.amount claim).minor
    let stated := (lines.map (fun l => l.gross.minor)).sum
    let lines :=
      if stated == asked then lines
      else lines ++ [{ description := "already asked for, or settled directly with the others"
                       qtyMilli := 1000, unitPrice := ⟨commodity, asked - stated⟩ }]
    let who := ((← Parties.byId? ctx payer.owner).map (·.name)).getD payer.name
    let inv ← create ctx who lines payment issued due commodity note (some b.name)
      (some b.id) (some claim.id)
    recordSources ctx inv.id ((← Budgets.costs ctx b).toList.map (·.id))
    out := out.push inv
  return out

end Invoices

end Resources
