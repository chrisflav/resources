import Resources.Core.Ledger
import Resources.Core.Payment

/-!
# Invoices, as values

An invoice is a document about money: lines, a total, a reference and the claim
it asks to have met. Everything here is arithmetic over that document, which is
why it sits in the core — `Op.issueInvoice` carries one, and the pure apply
function has to be able to talk about it without a database.

Writing one down, numbering it and rendering it stay in `Invoice/`. What moved
is the shape.
-/

open Lean

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

end Resources
