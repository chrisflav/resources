import Resources.Core.Invoice

/-!
# EPC069-12 payloads

The Girocode payload is twelve LF-separated fields in a fixed order, at most 331
bytes, scanned at error-correction level M. The important field is the
structured creditor reference: banking apps copy it into the transfer's
remittance information, so it comes back in the next bank export and the
importer can settle the invoice without anyone typing anything.

What a payment request *is*, and how a reference is built and recognised, are in
`Core/Payment.lean`. What is here is only the encoding: the core has to be able
to carry a payment request without knowing that a QR code exists.
-/

namespace Resources

namespace PaymentRequest

/--
The EPC069-12 payload: twelve fields, one per line, LF-separated.

Field 3 is the character set, where `1` means UTF-8. Exactly one of the two
remittance fields may be filled; this always uses the structured one.
-/
def epcPayload (name iban : String) (bic : Option String) (amount : Amount)
    (reference : String) : Except String String := do
  if amount.commodity.code != "EUR" then
    throw "EPC QR codes carry euro amounts only; use a payment link instead"
  if amount.minor < 1 then
    throw "EPC QR codes need a positive amount"
  if amount.minor > 99999999999 then
    throw "amount exceeds the EPC maximum of 999999999.99"
  let fields : List String :=
    [ "BCD"                                   -- service tag
    , "002"                                   -- version
    , "1"                                     -- character set: 1 = UTF-8
    , "SCT"                                   -- SEPA credit transfer
    , bic.getD ""                             -- BIC, optional in version 002
    , Str.clamp name 70                       -- beneficiary name
    , normIban iban                           -- beneficiary IBAN
    , "EUR" ++ amount.digits                  -- amount
    , ""                                      -- purpose code
    , Str.clamp reference 25                  -- structured creditor reference
    , ""                                      -- unstructured remittance (mutually exclusive)
    , "" ]                                    -- note to beneficiary
  let payload := String.intercalate "\n" fields
  if payload.utf8ByteSize > 331 then
    throw s!"EPC payload is {payload.utf8ByteSize} bytes, over the 331-byte limit"
  return payload

/-- The string to encode in the QR code for this payment request. -/
def payload (p : PaymentRequest) (amount : Amount) (reference : String) :
    Except String String :=
  match p with
  | .epc name iban bic => epcPayload name iban bic amount reference
  | .link url =>
    let sep := if url.contains '?' then "&" else "?"
    .ok (url ++ sep ++ "amount=" ++ amount.digits ++ "&ref=" ++ reference)

end PaymentRequest

/-- The string encoded in this invoice's QR code. -/
def Invoice.qrPayload (i : Invoice) : Except String String :=
  i.payment.payload i.total i.reference

-- The worked example from the EPC guidelines round-trips through the check digits.
example : Rf.isValid (Rf.make "539007547034") = true := by native_decide
example : Rf.isValid "RF18539007547034" = true := by native_decide
example : Rf.isValid "RF19539007547034" = false := by native_decide
example : Rf.find? "SEPA-UEBERWEISUNG RF18539007547034 RECHNUNG" = some "RF18539007547034" := by
  native_decide

end Resources
