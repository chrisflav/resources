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

/--
A token that could be a money amount, keeping the sign that `moneyToken?` throws
away. A total is never negative; a single line often is.
-/
private def signedMoney? (commodity : Commodity) (tok : String) : Option Amount := Id.run do
  let cleaned := String.ofList (tok.toList.filter fun c =>
    c.isDigit || c == ',' || c == '.')
  if cleaned.length < 3 then return none
  if !cleaned.any (fun c => c == ',' || c == '.') then return none
  match Amount.parseDigits commodity cleaned with
  | .ok a => return some ⟨commodity, if tok.any (· == '-') then -a.minor else a.minor⟩
  | .error _ => return none

/-- A leading count, as tills print it: `2 Haslikuchen`, or `-1` for a correction. -/
private def qtyToken? (tok : String) : Option Int :=
  let negative := tok.startsWith "-"
  let digits := if negative then (tok.drop 1).toString else tok
  -- Four digits is already an implausible count, and rules out the years and
  -- postcodes that otherwise open a line.
  if digits.isEmpty || digits.length > 4 || !digits.all Char.isDigit then none
  else some (if negative then -(digits.toNat!) else digits.toNat!)

/-- Trailing punctuation a till leaves where the unit price was cut away. -/
private def tidyDescription (s : String) : String :=
  let loose (c : Char) : Bool :=
    c == 'à' || c == '@' || c == '*' || c == ':' || c == 'x' || c == ' '
  String.ofList (s.trimAscii.toString.toList.reverse.dropWhile loose).reverse

/--
The priced lines on a page.

A line counts as an item when it opens with a count and carries a money amount.
The amount furthest right is what the line cost; an amount just before it is
dropped when the count multiplies it into the total, because that one is the
unit price and repeating it would double the line.
-/
def guessItems (commodity : Commodity) (text : String) : List LineItem := Id.run do
  let mut out : Array LineItem := #[]
  for line in text.splitOn "\n" do
    let toks := (((line.splitOn " ").map (fun t => t.trimAscii.toString)).filter
      (· != "")).toArray
    if toks.size < 2 then continue
    let some qty := qtyToken? toks[0]! | continue
    let rest := toks.extract 1 toks.size
    let mut priced : Option (Nat × Amount) := none
    for i in [0:rest.size] do
      match signedMoney? commodity rest[i]! with
      | some a => priced := some (i, a)
      | none => pure ()
    let some (ti, total) := priced | continue
    let mut descEnd := ti
    if ti > 0 then
      match signedMoney? commodity rest[ti - 1]! with
      | some unit => if qty * unit.minor == total.minor then descEnd := ti - 1
      | none => pure ()
    let desc := tidyDescription (String.intercalate " " (rest.extract 0 descEnd).toList)
    if desc.isEmpty then continue
    out := out.push { description := desc, qty := some qty, amount := total }
  return out.toList

/-- The first line with letters in it, which on most receipts names the shop. -/
def guessMerchant (text : String) : Option String := Id.run do
  for line in text.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.length ≥ 3 && l.length ≤ 60 && (l.toList.filter Char.isAlpha).length ≥ 3 then
      return some l
  return none

/-- An amount a configured parser may state either exactly or as printed text. -/
private def jsonAmount? (commodity : Commodity) (j : Json) (minorKey textKey : String) :
    Option Amount :=
  match (j.getObjValAs? Int minorKey).toOption with
  | some m => some ⟨commodity, m⟩
  | none => ((j.getObjValAs? String textKey).toOption).bind fun t =>
      (Amount.parseDigits commodity t).toOption

/-- One line of an `items` array, as a configured parser reports it. -/
private def itemOfJson (commodity : Commodity) (j : Json) : Option LineItem := do
  let description ← (j.getObjValAs? String "description").toOption
  let amount ← jsonAmount? commodity j "totalMinor" "total"
  some { description, qty := (j.getObjValAs? Int "qty").toOption, amount }

/-- Reads whatever the configured JSON parser returned. -/
private def ofJson (commodity : Commodity) (j : Json) : Extracted :=
  { merchant := (j.getObjValAs? String "merchant").toOption
    date := ((j.getObjValAs? String "date").toOption).bind Date.ofIso?
    total := jsonAmount? commodity j "totalMinor" "total"
    items :=
      match (j.getObjVal? "items").toOption with
      | some (.arr xs) => xs.toList.filterMap (itemOfJson commodity)
      | _ => [] }

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
           total := guessTotal commodity text, items := guessItems commodity text
           rawText := text, extractor := "builtin" }

private structure ItemRow where
  lineId : String
  description : String
  qty : Option Int64
  minor : Int64
  commodity : String
  deriving SQLite.Row

/-- The lines read off a receipt, in the order they were printed. -/
def items (ctx : Ctx) (sha : String) : IO (Array LineItem) := do
  let rows ← Db.rows ItemRow ctx.db
    s!"SELECT line_id, description, qty, minor, commodity FROM attachment_item
       WHERE sha256 = {Db.lit sha} ORDER BY idx"
  return rows.map fun r =>
    { id := r.lineId, description := r.description, qty := r.qty.map (·.toInt)
      amount := ⟨Commodity.ofCode r.commodity, r.minor.toInt⟩ }

/-! ## What a receipt says

Reading is SQL, because the rows are indexed and a query is the right tool for a
question. Writing is not: what was read off a receipt, and the lines somebody
edits afterwards, are state like anything else, so each of them is an operation
and the tables follow.
-/

private structure TotalRow where
  totalMinor : Option Int64
  commodity : Option String
  deriving SQLite.Row

/-- What a receipt says it came to, when a total was read off it. -/
def total? (ctx : Ctx) (sha : String) : IO (Option Amount) := do
  let rows ← Db.rows TotalRow ctx.db
    s!"SELECT total_minor, commodity FROM attachment WHERE sha256 = {Db.lit sha}"
  match rows[0]? with
  | none => return none
  | some r =>
    match r.totalMinor, r.commodity with
    | some m, some c => return if m.toInt == 0 then none else some ⟨Commodity.ofCode c, m.toInt⟩
    | _, _ => return none

/--
What the lines may still take up.

Lines are allowed to fall short of the total -- paper folds, and a service
charge is nobody's line -- but never to overrun it, because then they would be
describing a payment that did not happen. `none` when no total was read, which
is the only case where there is nothing to overrun.
-/
def headroom (ctx : Ctx) (sha : String) : IO (Option Amount) := do
  match ← total? ctx sha with
  | none => return none
  | some stated =>
    let used := ((← items ctx sha).toList.map (·.amount.minor)).sum
    return some ⟨stated.commodity, stated.minor - used⟩

/-- Adds a line by hand, for the ones a scan could not read. -/
def addItem (ctx : Ctx) (sha : String) (description : String) (qty : Option Int)
    (amountText : String) : IO LineItem := do
  let description := description.trimAscii.toString
  if description.isEmpty then throw <| IO.userError "a line needs a description"
  let its ← items ctx sha
  let stated ← total? ctx sha
  let commodity ← match stated, its[0]? with
    | some t, _ => pure t.commodity
    | none, some i => pure i.amount.commodity
    | none, none =>
      throw <| IO.userError
        "this receipt has no currency yet; read it with 'resources receipt scan' first"
  let amount ← match Amount.parseDigits commodity amountText with
    | .ok a => pure a
    | .error e => throw <| IO.userError s!"{amountText}: {e}"
  -- The operation refuses an overrun too; what it cannot say is how much room
  -- is left, which is the part somebody correcting a typo actually needs.
  match stated with
  | some t =>
    let used := (its.toList.map (·.amount.minor)).sum
    if (used + amount.minor).natAbs > t.minor.natAbs then
      throw <| IO.userError
        s!"that would take the lines past the {t.render} on this receipt; \
           {(Amount.mk commodity (t.minor - used)).render} is left"
  | none => pure ()
  let lineId ← freshId
  let item : LineItem := { id := lineId, description, qty, amount }
  discard <| ctx.commit "system" [.setReceiptLines sha (its.toList ++ [item])]
  return item

/-- Removes a line by its position, as `receipt items` numbers them. -/
def removeItem (ctx : Ctx) (sha : String) (n : Nat) : IO LineItem := do
  let its ← items ctx sha
  if n < 1 || n > its.size then
    throw <| IO.userError s!"there is no line {n}; this receipt has {its.size}"
  discard <| ctx.commit "system" [.setReceiptLines sha (its.toList.eraseIdx (n - 1))]
  return its[n - 1]!

/--
Stores what was read off a receipt, replacing whatever was read before.

The raw text is clamped here rather than in the operation: what it is for is
showing somebody the page a figure came from, and a scan of a long bill would
otherwise put a novel in every row of the table.
-/
def record (ctx : Ctx) (sha : String) (e : Extracted) : IO Unit := do
  -- Every line gets an id here, where there is an `IO` to mint one in: what a
  -- claim on a line names is the id, and the core has no way to invent one.
  let mut lines : List LineItem := []
  for l in e.items do
    if l.id.isEmpty then
      let fresh ← freshId
      lines := lines ++ [{ l with id := fresh }]
    else
      lines := lines ++ [l]
  let read := { e with items := lines, rawText := Str.clamp e.rawText 20000 }
  discard <| ctx.commit "system" [.recordExtraction sha read]

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

/-! ## Dividing a payment by its printed lines -/

/--
Divides a payment into the things it paid for.

One bill is rarely one thing, but only the payment reaches the bank, so the
parts have to come from the receipt. Each group becomes its own transaction
against the account the money left; whatever no group claimed stays behind in a
remainder, which is the normal ending rather than a failure -- lines are read
off paper, and paper folds. Fees and any other legs ride along with the
remainder, because they belong to the payment and not to any one thing bought.

Each part is left holding the lines it claimed, and the remainder the units they
left, so dividing one of them again divides its own list rather than the page
its siblings have already been paid out of. The receipt keeps every line it was
read with: what it says is a fact about the paper.
-/
def divideByItems (ctx : Ctx) (id : TxId) (groups : List ItemGroup) (actor : String) :
    IO (Array Transaction) := do
  if groups.isEmpty then throw <| IO.userError "say which lines go together: --group 1+2=Account"
  -- The realm the payment is in, which is not always yours: a cost shared into a
  -- realm of a budget's own is divided there, and the parts stay where the
  -- people who can see them are. Read off the transaction's own accounts rather
  -- than assumed, because a part may only speak about one realm and this one has
  -- to speak about the payment's.
  let st ← ctx.state.get
  let some t := st.txn? id | throw <| IO.userError s!"no such transaction: {id.val}"
  let realm := ((t.postings.head?).bind (fun p => st.realmOf p.account)).getD Realm.selfId
  -- The accounts the parts will be booked into, and one identifier per part
  -- plus one for the remainder: the three things the operation cannot mint for
  -- itself. Everything else about the division — which line covers how many
  -- units, what is left over, whether the lines overrun the payment — is
  -- arithmetic, and it is `Op.divideByItems` that does it.
  let mut resolved : List ItemGroup := []
  for g in groups do
    let target ← Accounts.ensure ctx g.into (realm := realm)
    resolved := resolved ++ [{ g with into := target.id.val }]
  let mut newIds : List TxId := []
  for _ in [0 : groups.length + 1] do
    newIds := newIds ++ [⟨← freshId⟩]
  -- Read before the commit: retiring a transaction resets the staged row that
  -- points at it, and it has to be pointed at the first part instead so the
  -- bank line stays promoted rather than reverting to unimported.
  let staged ← Db.rows String ctx.db
    s!"SELECT id FROM staged_entry WHERE txn_id = {Db.lit id.val}"
  let changes ← ctx.commit actor [.divideByItems id resolved newIds] (kind := "divide")
    (kinds := fun x => if x == id then some "divide-away" else none) (realm := realm)
  let written := Change.written changes
  if let some first := written[0]? then
    for row in staged do
      Db.exec ctx.db s!"UPDATE staged_entry SET state = 'promoted',
                        txn_id = {Db.lit first.id.val} WHERE id = {Db.lit row}"
  return written

end Receipts

end Resources
