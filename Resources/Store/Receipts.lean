import Resources.Store.Blob
import Resources.Import.Link

/-!
# Reading receipts

A photographed bill becomes useful once three things are read off it: who it was
from, when, and how much. Those are exactly the fields needed to match it to a
transaction — or, when there is no transaction, to create the cash one it stands
for.

Extraction is two configured commands rather than a built-in vendor:

* `textCommand` turns a file into text. `tesseract` by default, which runs
  offline — the hut with no internet in the story is the normal case, not the
  degraded one.
* `parseCommand` optionally turns that text into JSON. Point it at an AI if you
  want one; leave it unset and the built-in reader has a go with heuristics.

Nothing is applied automatically. Extraction proposes, a person confirms — the
same rule the import pairing follows, for the same reason: a wrong attribution
is far more annoying to unpick than a missed one.
-/

open Lean

namespace Resources

/-- What was read off a scanned receipt. -/
structure Extracted where
  merchant : Option String := none
  date : Option Date := none
  total : Option Amount := none
  rawText : String := ""
  extractor : String := ""
  deriving Repr, Inhabited

/-- How to turn a file into text, and text into fields. -/
structure ExtractorConfig where
  /-- Argv template; `{file}` is replaced with the path. -/
  textCommand : List String := ["tesseract", "{file}", "stdout"]
  /-- Optional; receives the text on stdin and must print JSON. -/
  parseCommand : List String := []
  /-- Commodity to assume when the receipt does not say. -/
  commodity : String := "EUR"
  deriving Repr, Inhabited, ToJson, FromJson

namespace Receipts

/-- Reads the extractor configuration, or the offline defaults. -/
def config (ctx : Ctx) : IO ExtractorConfig := do
  let p := ctx.cfg.dataDir / "extractor.json"
  if !(← p.pathExists) then return {}
  match Json.parse (← IO.FS.readFile p) >>= fromJson? (α := ExtractorConfig) with
  | .ok c => return c
  | .error e => do IO.eprintln s!"warning: bad extractor.json: {e}"; return {}

private def runArgv (argv : List String) (stdinText : Option String) :
    IO (Option String) := do
  match argv with
  | [] => return none
  | cmd :: args =>
    try
      let child ← IO.Process.spawn
        { cmd, args := args.toArray, stdin := .piped, stdout := .piped, stderr := .piped }
      let (stdin, child) ← child.takeStdin
      match stdinText with
      | some text => stdin.putStr text
      | none => pure ()
      stdin.flush
      let out ← child.stdout.readToEnd
      let code ← child.wait
      if code != 0 then return none
      return some out
    catch _ => return none

/-! ## Reading fields out of text

Without an AI to call, these are the two things worth finding on a receipt: the
largest money-looking number, which is almost always the total, and the first
date. Both are reported as guesses for a person to confirm.
-/

/-- Whether a token could be a money amount, in either decimal convention. -/
private def moneyToken? (commodity : Commodity) (tok : String) : Option Int := Id.run do
  let cleaned := String.ofList (tok.toList.filter fun c =>
    c.isDigit || c == ',' || c == '.')
  if cleaned.length < 3 then return none
  let hasSep := cleaned.any (fun c => c == ',' || c == '.')
  if !hasSep then return none
  match Amount.parseDigits commodity cleaned with
  | .ok a => if a.minor > 0 then some a.minor else none
  | .error _ => none

/-- The largest money-looking amount on the page: on a bill, that is the total. -/
def guessTotal (commodity : Commodity) (text : String) : Option Amount := Id.run do
  let mut best : Option Int := none
  for line in text.splitOn "\n" do
    for tok in line.splitOn " " do
      match moneyToken? commodity tok with
      | none => pure ()
      | some v => if best.all (fun b => v > b) then best := some v
  return best.map fun v => ⟨commodity, v⟩

/-- The first date on the page, in any of the usual layouts. -/
def guessDate (text : String) : Option Date := Id.run do
  let formats := ["dd.MM.yyyy", "yyyy-MM-dd", "dd/MM/yyyy", "dd.MM.yy"]
  for line in text.splitOn "\n" do
    for tok in line.splitOn " " do
      let cleaned := tok.trimAscii.toString
      for f in formats do
        match parseDateWith f cleaned with
        | some d => return some d
        | none => pure ()
  return none

/-- The first line with letters in it, which on most receipts names the shop. -/
def guessMerchant (text : String) : Option String := Id.run do
  for line in text.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.length ≥ 3 && l.length ≤ 60 && (l.toList.filter Char.isAlpha).length ≥ 3 then
      return some l
  return none

/-- Reads whatever the configured JSON parser returned. -/
private def ofJson (commodity : Commodity) (j : Json) : Extracted :=
  { merchant := (j.getObjValAs? String "merchant").toOption
    date := ((j.getObjValAs? String "date").toOption).bind Date.ofIso?
    total :=
      match (j.getObjValAs? Int "totalMinor").toOption with
      | some m => some ⟨commodity, m⟩
      | none => ((j.getObjValAs? String "total").toOption).bind fun t =>
          (Amount.parseDigits commodity t).toOption }

/-- Runs extraction over one stored file. -/
def extract (ctx : Ctx) (sha : String) : IO Extracted := do
  let cfg ← config ctx
  let commodity := Commodity.ofCode cfg.commodity
  let path := Blobs.path ctx sha
  if !(← path.pathExists) then throw <| IO.userError s!"no such receipt: {sha}"
  let argv := cfg.textCommand.map fun a => a.replace "{file}" path.toString
  let some text ← runArgv argv none
    | throw <| IO.userError
        s!"could not read the receipt; is {argv.head?.getD "the text command"} installed?"
  -- With a parser configured, believe it; otherwise fall back to the heuristics.
  match ← runArgv cfg.parseCommand (some text) with
  | some out =>
    match Json.parse out with
    | .ok j =>
      let e := ofJson commodity j
      return { e with rawText := text, extractor := cfg.parseCommand.head?.getD "parse" }
    | .error _ => pure ()
  | none => pure ()
  return { merchant := guessMerchant text, date := guessDate text
           total := guessTotal commodity text, rawText := text
           extractor := "builtin" }

/-- Stores what was read off a receipt. -/
def record (ctx : Ctx) (sha : String) (e : Extracted) : IO Unit :=
  Db.exec ctx.db s!"UPDATE attachment SET
      merchant = {Db.litOpt e.merchant},
      doc_date = {Db.litOpt (e.date.map (·.toIso))},
      total_minor = {(e.total.map (·.minor)).getD 0},
      commodity = {Db.litOpt (e.total.map (·.commodity.code))},
      raw_text = {Db.lit (Str.clamp e.rawText 20000)},
      extractor = {Db.lit e.extractor}
    WHERE sha256 = {Db.lit sha}"

/-! ## Matching a receipt to spending -/

private structure ScannedRow where
  sha256 : String
  mime : String
  origName : Option String
  merchant : Option String
  docDate : Option String
  totalMinor : Option Int64
  commodity : Option String
  deriving SQLite.Row

/-- A receipt that has been read but not yet attached to anything. -/
structure Scanned where
  sha256 : String
  mime : String
  origName : Option String
  merchant : Option String
  date : Option Date
  total : Option Amount
  deriving Repr, Inhabited

/-- Receipts not attached to any transaction. -/
def unattached (ctx : Ctx) : IO (Array Scanned) := do
  let rows ← Db.rows ScannedRow ctx.db
    "SELECT sha256, mime, orig_name, merchant, doc_date, total_minor, commodity
     FROM attachment
     WHERE sha256 NOT IN (SELECT sha256 FROM txn_attachment)
     ORDER BY created_at DESC"
  return rows.map fun r =>
    { sha256 := r.sha256, mime := r.mime, origName := r.origName
      merchant := r.merchant, date := r.docDate.bind Date.ofIso?
      total := match r.totalMinor with
        | some m => if m.toInt == 0 then none
            else some ⟨Commodity.ofCode (r.commodity.getD "EUR"), m.toInt⟩
        | none => none }

/-- A suggestion that a receipt is evidence for a transaction. -/
structure ReceiptMatch where
  sha256 : String
  txn : Transaction
  reason : String
  confidence : String
  deriving Repr

/--
Proposes which transaction each unattached receipt belongs to.

The amount has to agree exactly — it is the one field both the bill and the bank
know precisely — and the date has to be close, because a card payment settles a
day or two after the meal. A merchant name that also matches raises it from a
guess to a near certainty.
-/
def proposals (ctx : Ctx) (window : Int := 4) : IO (Array ReceiptMatch) := do
  let scans ← unattached ctx
  let accounts ← Accounts.list ctx
  -- Your own money accounts: a receipt in your pocket was paid for out of one
  -- of them, never out of somebody else's.
  let funding := (accounts.filter fun a => a.holdsMoney && a.mine).map (·.id)
  let mut out : Array ReceiptMatch := #[]
  for scan in scans do
    let some total := scan.total | continue
    let some date := scan.date | continue
    let candidates ← Txns.list ctx
      (.and (.dateFrom (date.plusDays (-window))) (.dateTo (date.plusDays window))) {} 10000
    let paid (t : Transaction) : Int :=
      -(funding.map (fun a => t.netIn a total.commodity.code)).foldl (· + ·) 0
    let sameAmount := candidates.filter fun t =>
      paid t == total.minor && !t.attachments.contains scan.sha256
    if sameAmount.isEmpty then continue
    let named := sameAmount.filter fun t =>
      match scan.merchant with
      | some m => Str.containsCI (t.payee.getD "" ++ " " ++ t.narration) (Str.clamp m 12)
      | none => false
    match named[0]?, sameAmount[0]? with
    | some t, _ =>
      out := out.push { sha256 := scan.sha256, txn := t, confidence := "high"
                        reason := s!"{total.render} on {t.date.toIso}, and the name matches" }
    | none, some t =>
      if sameAmount.size == 1 then
        out := out.push { sha256 := scan.sha256, txn := t, confidence := "medium"
                          reason := s!"{total.render}, the only payment of that amount nearby" }
    | _, _ => pure ()
  return out

/--
Creates the cash transaction a receipt stands for, when nothing on the statement
matches — the mountain hut with no card terminal.
-/
def toCashTransaction (ctx : Ctx) (sha : String) (from_ into : String) (actor : String) :
    IO Transaction := do
  let scans ← unattached ctx
  let some scan := scans.find? (·.sha256 == sha)
    | throw <| IO.userError "that receipt is already attached to something"
  let some total := scan.total
    | throw <| IO.userError "no total was read off this receipt; give it one by hand"
  let source ← Accounts.ensure ctx from_
  let target ← Accounts.ensure ctx into
  let date ← match scan.date with
    | some d => pure d
    | none => Date.today
  let id ← freshId
  let t : Transaction :=
    { id := ⟨id⟩, date, payee := scan.merchant
      narration := s!"cash receipt {Str.clamp sha 12}"
      postings := [{ account := source.id, amount := ⟨total.commodity, -total.minor⟩ },
                   { account := target.id, amount := total }]
      source := .manual actor
      attachments := [sha] }
  match t.validate with
  | .error e => throw <| IO.userError e
  | .ok bt =>
    Txns.put ctx bt actor "cash-receipt"
    return bt.val

end Receipts

end Resources
