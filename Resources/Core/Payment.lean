import Resources.Util

/-!
# References and payment requests

Two things a document about money needs before anything renders it: the way it
asks to be paid, and the reference that will come back with the payment.

The ISO 11649 creditor reference is the part that closes the loop. A banking app
copies it into the transfer's remittance information, the bank export carries it
back, and the importer finds it again — so an invoice can settle itself without
anybody typing an amount into a form twice. Everything here is arithmetic over
strings, which is why it sits in the core rather than beside the QR encoder that
happens to be its first reader.
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

/-- A one-line human description, for the invoice footer. -/
def describe : PaymentRequest → String
  | .epc name iban _ => s!"{name} · {normIban iban}"
  | .link url => url

end PaymentRequest

end Resources
