import Resources.Core.Ledger

/-!
# EPC069-12 payloads and ISO 11649 references

The Girocode payload is twelve LF-separated fields in a fixed order, at most 331
bytes, scanned at error-correction level M. The important field is the
structured creditor reference: banking apps copy it into the transfer's
remittance information, so it comes back in the next bank export and the
importer can settle the invoice without anyone typing anything.
-/

namespace Resources

/-! ## ISO 11649 creditor references -/

namespace Rf

/-- Maps a character to its ISO 7064 numeric value: digits as themselves, `A`–`Z` as 10–35. -/
private def charValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if c.isUpper then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Computes `n mod 97` over the ISO 7064 expansion of a string. -/
private def mod97 (s : String) : Option Nat := Id.run do
  let mut acc : Nat := 0
  for c in s.toList do
    match charValue c with
    | none => return none
    | some v => acc := (acc * (if v < 10 then 10 else 100) + v) % 97
  return some acc

/-- Strips a reference down to the characters ISO 11649 allows. -/
def sanitise (s : String) : String :=
  String.ofList (s.toUpper.toList.filter (fun c => c.isAlphanum)) |>.take 21 |>.toString

/-- Builds an ISO 11649 creditor reference, `RF` + two check digits + the base. -/
def make (base : String) : String :=
  let b := sanitise base
  match mod97 (b ++ "RF00") with
  | none => "RF00" ++ b
  | some m =>
    let check := 98 - m
    "RF" ++ Str.padLeft (toString check) 2 '0' ++ b

/-- Whether a string is a well-formed ISO 11649 reference. -/
def isValid (s : String) : Bool :=
  let t := String.ofList (s.toUpper.toList.filter (fun c => !c.isWhitespace))
  t.startsWith "RF" && t.length ≥ 5 &&
    (match mod97 ((t.drop 4).toString ++ (t.take 4).toString) with
     | some 1 => true
     | _ => false)

/-- Finds the first ISO 11649 reference inside a free-text remittance field. -/
def find? (text : String) : Option String :=
  let words := (text.replace "\n" " ").replace "\t" " " |>.splitOn " "
  words.map (fun w => String.ofList (w.toUpper.toList.filter Char.isAlphanum))
    |>.find? isValid

end Rf

/-! ## Payment requests -/

/-- How an invoice asks to be paid. -/
inductive PaymentRequest
  /-- A SEPA credit transfer, rendered as an EPC069-12 Girocode. -/
  | epc (name : String) (iban : String) (bic : Option String)
  /-- Any payment URL — PayPal.me, Wise, a bank deep link — rendered as a plain QR. -/
  | link (url : String)
  deriving Repr, Inhabited, DecidableEq

namespace PaymentRequest

/-- Compact encoding, stored in two columns. -/
def encode : PaymentRequest → String × String
  | .epc name iban bic => ("epc", String.intercalate "|" [name, iban, bic.getD ""])
  | .link url => ("link", url)

/-- Inverse of `encode`. -/
def decode (kind data : String) : PaymentRequest :=
  match kind with
  | "epc" =>
    match data.splitOn "|" with
    | [name, iban, bic] => .epc name iban (if bic.isEmpty then none else some bic)
    | [name, iban] => .epc name iban none
    | _ => .link data
  | _ => .link data

/-- Normalises an IBAN: upper case, no spaces. -/
def normIban (s : String) : String :=
  String.ofList (s.toUpper.toList.filter (fun c => !c.isWhitespace))

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

/-- A one-line human description, for the invoice footer. -/
def describe : PaymentRequest → String
  | .epc name iban _ => s!"{name} · {normIban iban}"
  | .link url => url

end PaymentRequest

-- The worked example from the EPC guidelines round-trips through the check digits.
example : Rf.isValid (Rf.make "539007547034") = true := by native_decide
example : Rf.isValid "RF18539007547034" = true := by native_decide
example : Rf.isValid "RF19539007547034" = false := by native_decide
example : Rf.find? "SEPA-UEBERWEISUNG RF18539007547034 RECHNUNG" = some "RF18539007547034" := by
  native_decide

end Resources
