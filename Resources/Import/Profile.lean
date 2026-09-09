import Resources.Import.Csv
import Lean.Data.Json

/-!
# Bank profiles

Most bank exports are the same CSV wearing different hats, so adding a bank is a
JSON file rather than a Lean module. Columns are matched against a list of
candidate header names, and a profile only *applies* to a file if its date and
amount columns actually resolve — which is what makes `--profile auto` safe.
-/

open Lean

namespace Resources

/-- One line of a bank export, before any interpretation. -/
structure RawRecord where
  date : Date
  amount : Amount
  payee : Option String := none
  purpose : Option String := none
  counterIban : Option String := none
  bankRef : Option String := none
  deriving Repr, Inhabited, ToJson, FromJson

/-- Candidate header names for each field a profile needs to find. -/
structure ColumnMap where
  date : List String := []
  amount : List String := []
  debit : List String := []
  credit : List String := []
  payee : List String := []
  /-- Counterparty column used when money leaves the account. -/
  payeeOut : List String := []
  /-- Counterparty column used when money arrives. -/
  payeeIn : List String := []
  purpose : List String := []
  iban : List String := []
  ref : List String := []
  currency : List String := []
  deriving Repr, Inhabited, ToJson, FromJson

/-- How to read one bank's CSV export. -/
structure CsvProfile where
  name : String
  /-- Field separator; only the first character is used. -/
  delimiter : String := ";"
  /-- `utf8` or `latin1`. -/
  encoding : String := "latin1"
  /-- Lines to skip before looking for the header. -/
  skipLines : Nat := 0
  /-- `dd.MM.yyyy`, `yyyy-MM-dd`, `dd/MM/yyyy`, … -/
  dateFormat : String := "dd.MM.yyyy"
  /-- `,` for German exports, `.` for Anglo ones. -/
  decimalSep : String := ","
  /-- Default commodity when the file has no currency column. -/
  commodity : String := "EUR"
  /-- Flip the sign of every amount, for exports that report outflows as positive. -/
  negate : Bool := false
  /-- Cell values that mean "empty", such as Consorsbank's `n/a`. -/
  nullValues : List String := []
  /-- Column whose value marks a row as not yet booked. -/
  pendingColumn : List String := []
  /-- Values of `pendingColumn` that mean the row is still pending. -/
  pendingValues : List String := []
  /-- Words marking a row as a fee posted alongside another row. -/
  feeWords : List String := []
  /-- The fee as basis points of its parent, for corroborating a pairing. -/
  feeRateBp : Int := 0
  /-- Where fee rows are booked, so they stay visible instead of vanishing into
  `Unclassified`. -/
  feeAccount : String := ""
  columns : ColumnMap
  deriving Repr, Inhabited, ToJson, FromJson

namespace CsvProfile

/-- The profiles that ship with the binary. User profiles override these by name. -/
def builtins : List CsvProfile := [
  { name := "generic", delimiter := ",", encoding := "utf8", dateFormat := "yyyy-MM-dd",
    decimalSep := ".",
    columns := { date := ["date", "datum"], amount := ["amount", "betrag"],
                 payee := ["payee", "counterparty", "name", "description"],
                 purpose := ["description", "purpose", "reference", "note"],
                 iban := ["iban", "account"], ref := ["id", "reference", "transaction id"],
                 currency := ["currency", "waehrung", "währung"] } },
  { name := "dkb",
    columns := { date := ["buchungsdatum", "buchungstag", "wertstellung"],
                 amount := ["betrag (€)", "betrag", "betrag (eur)"],
                 payee := ["auftraggeber / begünstigter", "name zahlungsbeteiligter"],
                 payeeOut := ["zahlungsempfänger*in", "zahlungsempfaenger*in"],
                 payeeIn := ["zahlungspflichtige*r", "zahlungspflichtiger"],
                 purpose := ["verwendungszweck", "buchungstext"],
                 iban := ["iban zahlungsbeteiligter", "iban", "kontonummer / iban"],
                 ref := ["kundenreferenz", "mandatsreferenz"] } },
  { name := "sparkasse",
    columns := { date := ["buchungstag", "valutadatum"],
                 amount := ["betrag"],
                 payee := ["beguenstigter/zahlungspflichtiger", "begünstigter/zahlungspflichtiger",
                           "name zahlungsbeteiligter"],
                 purpose := ["verwendungszweck", "buchungstext"],
                 iban := ["kontonummer/iban", "iban zahlungsbeteiligter"],
                 ref := ["kundenreferenz (end-to-end)", "mandatsreferenz"],
                 currency := ["waehrung", "währung"] } },
  { name := "consorsbank", encoding := "utf8",
    nullValues := ["n/a"],
    pendingColumn := ["valuta"], pendingValues := ["vorgemerkt"],
    feeWords := ["auslandseinsatzentgelt"], feeRateBp := 210,
    feeAccount := "Expenses.Fees.Foreign",
    columns := { date := ["buchung", "buchungstag"],
                 amount := ["betrag"],
                 payee := ["sender / empfänger", "sender / empfaenger", "sender/empfänger"],
                 purpose := ["verwendungszweck", "buchungstext"],
                 iban := ["iban"],
                 currency := ["währung", "waehrung"] } },
  { name := "ing",
    columns := { date := ["buchung", "buchungsdatum", "valuta"],
                 amount := ["betrag"],
                 payee := ["auftraggeber/empfänger", "auftraggeber/empfaenger"],
                 purpose := ["verwendungszweck", "buchungstext"],
                 currency := ["währung", "waehrung"] } },
  { name := "n26", delimiter := ",", encoding := "utf8", dateFormat := "yyyy-MM-dd",
    decimalSep := ".",
    columns := { date := ["booking date", "date", "datum"],
                 amount := ["amount (eur)", "amount", "betrag (eur)"],
                 payee := ["partner name", "payee", "empfänger"],
                 purpose := ["payment reference", "verwendungszweck", "reference"],
                 iban := ["partner iban", "iban"],
                 currency := ["currency", "original currency"] } },
  { name := "revolut", delimiter := ",", encoding := "utf8", dateFormat := "yyyy-MM-dd",
    decimalSep := ".",
    columns := { date := ["completed date", "started date", "date"],
                 amount := ["amount"], payee := ["description"],
                 purpose := ["description", "type"], currency := ["currency"] } },
  { name := "wise", delimiter := ",", encoding := "utf8", dateFormat := "dd-MM-yyyy",
    decimalSep := ".",
    columns := { date := ["date"], amount := ["amount"],
                 payee := ["merchant", "payee name", "description"],
                 purpose := ["description", "payer message", "note"],
                 iban := ["payee account number"], ref := ["transferwise id", "id"],
                 currency := ["currency"] } },
  { name := "paypal", delimiter := ",", encoding := "utf8", dateFormat := "dd.MM.yyyy",
    columns := { date := ["datum", "date"], amount := ["netto", "net", "brutto", "gross"],
                 payee := ["name", "empfänger e-mail-adresse"],
                 purpose := ["betreff", "hinweis", "subject", "note"],
                 ref := ["transaktionscode", "transaction id"],
                 currency := ["währung", "currency"] } },
  { name := "camt-csv",
    columns := { date := ["buchungstag", "valutadatum"], amount := ["betrag"],
                 payee := ["beguenstigter/zahlungspflichtiger", "name zahlungsbeteiligter"],
                 purpose := ["verwendungszweck"], iban := ["kontonummer/iban"],
                 currency := ["waehrung", "währung"] } }
]

/-- The delimiter character. -/
def delim (p : CsvProfile) : Char := p.delimiter.toList.head?.getD ';'

/-- The text encoding. -/
def enc (p : CsvProfile) : Encoding := (Encoding.ofString? p.encoding).getD .latin1

/-- Finds the index of the first header cell matching one of `candidates`. -/
def findColumn (headers : Array String) (candidates : List String) : Option Nat := Id.run do
  let norm := headers.map normHeader
  for c in candidates do
    let cn := c.toLower
    for i in [0:norm.size] do
      if norm[i]! == cn then return some i
  -- fall back to a substring match, for headers with units or footnotes appended
  for c in candidates do
    let cn := c.toLower
    for i in [0:norm.size] do
      if Str.containsCI norm[i]! cn then return some i
  return none

/-- The resolved column indices for a header row. -/
structure Resolved where
  date : Nat
  amount : Option Nat
  debit : Option Nat
  credit : Option Nat
  payee : Option Nat
  payeeOut : Option Nat
  payeeIn : Option Nat
  purpose : Option Nat
  iban : Option Nat
  ref : Option Nat
  currency : Option Nat
  pending : Option Nat

/-- Resolves a profile against a header row, or fails if the essentials are missing. -/
def resolve (p : CsvProfile) (headers : Array String) : Option Resolved :=
  match findColumn headers p.columns.date with
  | none => none
  | some date =>
    let amount := findColumn headers p.columns.amount
    let debit := findColumn headers p.columns.debit
    let credit := findColumn headers p.columns.credit
    if amount.isNone && debit.isNone && credit.isNone then none
    else some ({ date, amount, debit, credit,
                 payee := findColumn headers p.columns.payee,
                 payeeOut := findColumn headers p.columns.payeeOut,
                 payeeIn := findColumn headers p.columns.payeeIn,
                 purpose := findColumn headers p.columns.purpose,
                 iban := findColumn headers p.columns.iban,
                 ref := findColumn headers p.columns.ref,
                 currency := findColumn headers p.columns.currency,
                 pending := findColumn headers p.pendingColumn } : Resolved)

/-- How many columns a profile managed to place: a proxy for how well it fits. -/
def Resolved.fit (r : Resolved) : Nat :=
  [r.amount, r.debit, r.credit, r.payee, r.payeeOut, r.payeeIn, r.purpose, r.iban, r.ref,
   r.currency].countP Option.isSome

private def cell (nulls : List String) (row : Array String) (i : Option Nat) :
    Option String := do
  let idx ← i
  let v ← row[idx]?
  let t := v.trimAscii.toString
  if t.isEmpty || nulls.any (fun n => n.toLower == t.toLower) then none else some t

/-- Normalises a decimal string to a dot-separated one, per the profile's convention. -/
def normNumber (p : CsvProfile) (s : String) : String :=
  if p.decimalSep == "," then (s.replace "." "").replace "," "."
  else s.replace "," ""

/-- Parses the data rows of a CSV file into raw records. -/
def parseRows (p : CsvProfile) (text : String) :
    Except String (Array RawRecord × Array String) := do
  let rows := parseCsv p.delim text
  let rows := rows.extract p.skipLines rows.size
  -- The header is the first row against which this profile resolves.
  let mut headerIdx : Option Nat := none
  let mut res : Option Resolved := none
  for i in [0:min rows.size 20] do
    if res.isNone then
      match resolve p rows[i]! with
      | some r => headerIdx := some i; res := some r
      | none => pure ()
  let some hi := headerIdx | throw s!"profile '{p.name}' does not match this file's columns"
  let some r := res | throw s!"profile '{p.name}' does not match this file's columns"
  let mut out : Array RawRecord := #[]
  let mut problems : Array String := #[]
  let mut pending := 0
  for i in [hi + 1 : rows.size] do
    let row := rows[i]!
    -- Pending authorisations reappear as booked rows later, with different text
    -- and sometimes a different amount, so importing them double-counts.
    let isPending :=
      match cell p.nullValues row r.pending with
      | some v => p.pendingValues.any (fun x => x.toLower == v.toLower)
      | none => false
    if isPending then
      pending := pending + 1
      continue
    match cell p.nullValues row (some r.date) with
    | none => pure ()
    | some dateStr =>
      match parseDateWith p.dateFormat dateStr with
      | none => problems := problems.push s!"line {i + 1}: bad date {dateStr}"
      | some date =>
        let commodity :=
          Commodity.ofCode ((cell p.nullValues row r.currency).getD p.commodity)
        let amountStr : Option String :=
          match cell p.nullValues row r.amount with
          | some a => some a
          | none =>
            match cell p.nullValues row r.debit, cell p.nullValues row r.credit with
            | some d, _ => some ("-" ++ d)
            | _, some c => some c
            | _, _ => none
        match amountStr with
        | none => problems := problems.push s!"line {i + 1}: no amount"
        | some a =>
          match Amount.parseDigits commodity (normNumber p a) with
          | .error e => problems := problems.push s!"line {i + 1}: {e}"
          | .ok amt =>
            let amt := if p.negate then -amt else amt
            let payee :=
              let fallback := cell p.nullValues row r.payee
              if amt.minor < 0 then (cell p.nullValues row r.payeeOut) <|> fallback
              else (cell p.nullValues row r.payeeIn) <|> fallback
            out := out.push
              { date, amount := amt, payee,
                purpose := cell p.nullValues row r.purpose,
                counterIban := cell p.nullValues row r.iban,
                bankRef := cell p.nullValues row r.ref }
  if pending > 0 then
    problems := problems.push s!"skipped {pending} row(s) the bank has not booked yet"
  return (out, problems)

/--
Picks the profile that actually parses the file best, rather than the first one
whose headers superficially match. A profile that resolves its columns but then
fails on every row — the wrong delimiter, the wrong decimal separator — scores
zero and loses to one that reads real records.
-/
def detect (profiles : List CsvProfile) (bytes : ByteArray) : Option CsvProfile :=
  let scored : List (CsvProfile × Nat × Nat) := profiles.filterMap fun p =>
    match p.parseRows (p.enc.decode bytes) with
    | .ok (records, _) =>
      if records.isEmpty then none
      else
        -- How many columns the profile placed, which is what separates a
        -- profile written for this bank from one that merely happens to find a
        -- date and an amount.
        let rows := parseCsv p.delim (p.enc.decode bytes)
        let fit := (List.range (min rows.size 20)).foldl
          (fun best i => max best (((resolve p rows[i]!).map Resolved.fit).getD 0)) 0
        some (p, fit, records.size)
    | .error _ => none
  let better (a b : CsvProfile × Nat × Nat) : Bool :=
    if a.2.1 != b.2.1 then a.2.1 > b.2.1 else a.2.2 > b.2.2
  match scored with
  | [] => none
  | first :: rest => some (rest.foldl (fun best c => if better c best then c else best) first).1

/-- Loads user profiles from a directory of JSON files, then appends the built-ins. -/
def loadAll (dir : System.FilePath) : IO (List CsvProfile) := do
  let mut user : List CsvProfile := []
  if ← dir.pathExists then
    for entry in ← dir.readDir do
      if entry.fileName.endsWith ".json" then
        let text ← IO.FS.readFile entry.path
        match Json.parse text >>= fromJson? (α := CsvProfile) with
        | .ok p => user := p :: user
        | .error e => IO.eprintln s!"warning: bad profile {entry.fileName}: {e}"
  let userNames := user.map (·.name)
  return user ++ builtins.filter (fun b => !userNames.contains b.name)

end CsvProfile

end Resources
