import Resources.Api.Routes
import Resources.Api.Vectors
import Resources.Core.Apply
import Test.Sync
import Test.Crypto
import Test.Encode
import Test.Node
import Test.NodeHardening

/-!
# Tests

The interesting one is `filterAgreement`: `Filter.eval` is the reference
semantics over in-memory transactions and `Filter.toSql` is the fast path, and
proving the compiler sound against SQLite's semantics is out of reach. Checking
that the two agree on a generated corpus is not, and it catches every bug you
would actually write.
-/

open Lean Resources

/-! ## Pure tests -/

private def moneyTests (r : Report) : Report := Id.run do
  let mut r := r
  let eur := Commodity.eur
  let cases : List (String × Int) :=
    [("49.90", 4990), ("-49,90", -4990), ("1.234,56", 123456), ("1,234.56", 123456),
     ("0", 0), ("+7", 700), ("1234.5", 123450), ("-0,01", -1)]
  for (input, expected) in cases do
    match Amount.parseDigits eur input with
    | .ok a => r := checkEq r s!"parse {input}" a.minor expected
    | .error e => r := check r s!"parse {input} ({e})" false
  r := checkEq r "render" (Amount.mk eur (-4990)).render "-49.90 EUR"
  r := checkEq r "render zero-exponent" (Amount.mk (Commodity.ofCode "JPY") 1234).render "1234 JPY"
  r := checkEq r "parse with commodity"
    ((Amount.parse "-49.90EUR").toOption.map (·.minor)) (some (-4990))
  -- Splitting never loses a minor unit, for any of these shapes.
  for total in [100, 101, 7, -100, -7, 0, 999999] do
    for n in [1, 2, 3, 7, 13] do
      let parts := splitParts total n
      r := checkEq r s!"split {total}/{n} sums" parts.sum total
      r := checkEq r s!"split {total}/{n} count" parts.length n
  return r

private def rfTests (r : Report) : Report := Id.run do
  let mut r := r
  -- The worked example from the EPC guidelines.
  r := check r "RF check digits" (Rf.make "539007547034" == "RF18539007547034")
  r := check r "RF validates" (Rf.isValid "RF18539007547034")
  r := check r "RF rejects a wrong check digit" (!Rf.isValid "RF19539007547034")
  r := checkEq r "RF found in remittance text"
    (Rf.find? "SEPA UEBERWEISUNG RF18539007547034 RECHNUNG") (some "RF18539007547034")
  let payload := PaymentRequest.epcPayload "Christian Merten" "DE02120300000000202051"
    (some "GENODEF1XXX") ⟨Commodity.eur, 250000⟩ "RF18539007547034"
  match payload with
  | .error e => r := check r s!"EPC payload ({e})" false
  | .ok p =>
    let lines := p.splitOn "\n"
    r := checkEq r "EPC has 12 fields" lines.length 12
    r := checkEq r "EPC service tag" (lines[0]!) "BCD"
    r := checkEq r "EPC version" (lines[1]!) "002"
    r := checkEq r "EPC charset is UTF-8" (lines[2]!) "1"
    r := checkEq r "EPC function" (lines[3]!) "SCT"
    r := checkEq r "EPC amount" (lines[7]!) "EUR2500.00"
    r := checkEq r "EPC structured reference" (lines[9]!) "RF18539007547034"
    r := checkEq r "EPC unstructured field is empty" (lines[10]!) ""
    r := check r "EPC fits in 331 bytes" (p.utf8ByteSize ≤ 331)
  r := check r "EPC refuses non-euro"
    (PaymentRequest.epcPayload "X" "DE00" none ⟨Commodity.ofCode "USD", 100⟩ "RF00").toOption.isNone
  return r

private def invoiceTests (r : Report) : Report := Id.run do
  let mut r := r
  let eur := Commodity.eur
  let line : InvoiceLine :=
    { description := "Consulting", qtyMilli := 10000, unitPrice := ⟨eur, 12000⟩, taxBp := 1900 }
  r := checkEq r "line net" line.net.minor 120000
  r := checkEq r "line tax at 19%" line.tax.minor 22800
  r := checkEq r "line gross" line.gross.minor 142800
  r := checkEq r "quantity renders" line.quantity "10.000"
  -- A third of a cent must round, not truncate silently.
  let odd : InvoiceLine :=
    { description := "x", qtyMilli := 1, unitPrice := ⟨eur, 100⟩, taxBp := 0 }
  r := checkEq r "sub-cent quantity rounds" odd.net.minor 0
  r := checkEq r "divRound rounds half away from zero" (divRound 5 10) 1
  r := checkEq r "divRound is symmetric" (divRound (-5) 10) (-1)
  return r

private def filterParseTests (r : Report) : Report := Id.run do
  let mut r := r
  let cases :=
    ["account:Assets.Bank", "date>=2026-01-01", "-label:private", "text:\"weekly shop\"",
     "(account:A OR account:B) label:x", "amount<=-50EUR", "*"]
  for src in cases do
    match Filter.parse src with
    | .ok f =>
      -- Rendering and reparsing must land on the same predicate.
      match Filter.parse f.render with
      | .ok g => r := checkEq r s!"filter round-trip {src}" g.render f.render
      | .error e => r := check r s!"reparse {src} ({e})" false
    | .error e => r := check r s!"parse {src} ({e})" false
  for (src, key, desc) in [("date", Filter.SortKey.date, false), ("-date", .date, true),
                           ("amount", .amount, false), ("-amount", .amount, true),
                           ("payee", .payee, false), ("narration", .narration, false),
                           ("created", .created, false)] do
    let parsed := Filter.SortSpec.parse src
    r := check r s!"sort '{src}' parses" (parsed.key == key && parsed.descending == desc)
  r := check r "an unknown sort key falls back to date"
    ((Filter.SortSpec.parse "nonsense").key == Filter.SortKey.date)
  r := check r "the amount sort orders by the signed balance-sheet movement"
    (Str.containsCI (Filter.SortSpec.toSql { key := .amount }) "SUM(p.minor)")
  r := check r "and restricts that sum to balance-sheet accounts"
    (Str.containsCI (Filter.SortSpec.toSql { key := .amount }) "a.kind IN")
  r := check r "filter rejects an unbalanced parenthesis"
    (Filter.parse "(account:A").toOption.isNone
  return r

private def ledgerTests (r : Report) : Report := Id.run do
  let mut r := r
  let eur := Commodity.eur
  let a : AccountId := ⟨"a"⟩
  let b : AccountId := ⟨"b"⟩
  let t : Transaction :=
    { id := ⟨"t"⟩, date := (Date.ofIso? "2026-01-01").getD default,
      postings := [{ account := a, amount := ⟨eur, -100⟩ },
                   { account := b, amount := ⟨eur, 100⟩ }] }
  r := check r "balanced transaction validates" t.validate.toOption.isSome
  let bad := { t with postings := [{ account := a, amount := ⟨eur, -100⟩ }] }
  r := check r "unbalanced transaction is rejected" bad.validate.toOption.isNone
  r := checkEq r "auto-balance fixes it"
    ((bad.autoBalance b).validate.toOption.isSome) true
  r := checkEq r "balance of a" (Ledger.balance [t] a "EUR") (-100)
  r := checkEq r "balance of b" (Ledger.balance [t] b "EUR") 100
  r := checkEq r "trial balance" (Ledger.totalNet [t] "EUR") 0
  r := checkEq r "net in another commodity" (t.net "USD") 0
  return r

/-! ## Store-backed tests -/

/--
The database says exactly what the state says.

Every write now applies an operation to the state in memory and projects what
came back into SQL, so the two are two renderings of one thing and must agree
entry for entry. `Load.fromDb` reads the tables back into a state and
`State.canonical` sorts both, which is what makes the comparison independent of
how anything was stored.

The log is checked against the same state and in the same breath. A commit
appends the operations and projects what they changed in one transaction, so
after every group there are three renderings of one ledger — the tables, the
state in memory, and the events replayed from nothing — and all three have to
say the same thing. Replaying after every group rather than once at the end is
what makes a divergence point at the group that caused it.

On a mismatch the first differing entry of the two renderings is printed. "Two
states differ" is not a diagnosis; "the database has this transaction with two
postings and the state has three" is.
-/
private def agree (ctx : Ctx) (r : Report) : IO Report := do
  let stored ← Load.fromDb ctx.db
  let held ← ctx.state.get
  let replayed ← Replay.state ctx.db
  let r := check r "the log replays to the state" (replayed == held)
  if stored == held then return { r with passed := r.passed + 1 }
  -- A `Repr` runs to several lines, and a failure is read one line at a time.
  let entries (s : State) : List String :=
    s.canonical.flatMap fun (section', rows) =>
      rows.map fun (key, value) =>
        s!"{section'}/{key} = " ++ " ".intercalate (value.splitOn "\n")
  let a := entries stored
  let b := entries held
  let detail := match (a.zip b).find? (fun (x, y) => x != y) with
    | some (x, y) => s!"stored {Str.clamp x 300}; state has {Str.clamp y 300}"
    | none => s!"the database has {a.length} entries and the state {b.length}"
  return check r s!"the database agrees with the state ({detail})" false

/-- A tiny deterministic generator, so a failure is always reproducible. -/
private def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

private def corpusAccounts : List String :=
  ["Assets.Bank.Main", "Assets.Cash", "Expenses.Food.Groceries", "Expenses.Travel.Trains",
   "Expenses.Home.Utilities", "Income.Consulting", "Liabilities.CreditCard"]

private def corpusPayees : List String :=
  ["REWE", "Deutsche Bahn", "Stadtwerke", "ACME GmbH", "Cafe Central"]

/-- Fills a store with a varied corpus and returns the transactions written. -/
private def seedCorpus (ctx : Ctx) (n : Nat) : IO (Array Transaction) := do
  let labels ← #["food", "travel", "private"].mapM fun l => do return (← Labels.ensure ctx l)
  let accounts ← corpusAccounts.toArray.mapM fun a => Accounts.ensure ctx a
  let mut seed := 42
  let mut out : Array Transaction := #[]
  for i in [0:n] do
    seed := lcg seed
    let fromIdx := seed % accounts.size
    seed := lcg seed
    let toIdx := seed % accounts.size
    seed := lcg seed
    let minor : Int := Int.ofNat (seed % 200000) - 100000
    seed := lcg seed
    let payee := corpusPayees[seed % corpusPayees.length]!
    seed := lcg seed
    let day := 1 + seed % 28
    seed := lcg seed
    let month := 1 + seed % 12
    let mm := Str.padLeft (toString month) 2 '0'
    let dd := Str.padLeft (toString day) 2 '0'
    let date := (Date.ofIso? s!"2026-{mm}-{dd}").getD default
    seed := lcg seed
    let labelSet := if seed % 3 == 0 then [labels[seed % labels.size]!.id] else []
    if fromIdx == toIdx || minor == 0 then continue
    let t : Transaction :=
      { id := ⟨s!"tx{Str.padLeft (toString i) 4 '0'}"⟩
        date
        payee := some payee
        narration := s!"entry {i} weekly shop"
        postings := [{ account := accounts[fromIdx]!.id, amount := ⟨Commodity.eur, minor⟩ },
                     { account := accounts[toIdx]!.id, amount := ⟨Commodity.eur, -minor⟩ }]
        labels := labelSet }
    match t.validate with
    | .error e => throw <| IO.userError s!"seed produced an unbalanced transaction: {e}"
    | .ok bt =>
      Txns.put ctx bt "test"
      out := out.push t
  return out

/--
The agreement test. Every filter must select exactly the same transactions
through SQL as the reference semantics selects in memory.
-/
private def filterAgreement (ctx : Ctx) (corpus : Array Transaction) (r : Report) :
    IO Report := do
  let env := Filter.Env.ofLists (← Accounts.list ctx).toList (← Labels.list ctx).toList
    (← Parties.list ctx).toList
  let exprs :=
    ["*", "account:Assets", "account:Assets.Bank.Main", "account:Expenses.Food",
     "date>=2026-06-01", "date<=2026-03-31", "date>=2026-04-01 date<=2026-09-30",
     "label:food", "-label:food", "label:food OR label:travel",
     "payee:REWE", "-payee:REWE", "text:weekly", "text:\"entry 1\"",
     "commodity:EUR", "commodity:USD",
     "payee:\"\"", "-payee:\"\"", "text:\"\"", "tag:fee", "-tag:fee",
     "amount>=50000EUR", "amount<=-50000EUR",
     "account:Expenses -label:private", "(account:Assets OR account:Income) date>=2026-07-01",
     "account:Assets.Cash label:travel", "-(account:Assets)"]
  let mut r := r
  for src in exprs do
    match Filter.parse src with
    | .error e => r := check r s!"parse {src} ({e})" false
    | .ok f =>
      let viaSql ← Txns.list ctx f {} 10000
      let sqlIds := (viaSql.map (fun t => t.id.val)).qsort (· < ·)
      let refIds := ((corpus.filter (fun t => f.eval env t)).map (fun t => t.id.val)).qsort (· < ·)
      if sqlIds == refIds then
        r := { r with passed := r.passed + 1 }
      else
        let onlySql := sqlIds.filter (fun x => !refIds.contains x)
        let onlyRef := refIds.filter (fun x => !sqlIds.contains x)
        let detail := s!"filter '{src}': SQL returned {sqlIds.size}, reference {refIds.size}; " ++
          s!"only-SQL {onlySql.take 3}, only-reference {onlyRef.take 3}"
        r := check r detail false
  return r

/-- Sorting must order the whole result set, not just look plausible. -/
private def sortOrdering (ctx : Ctx) (r : Report) : IO Report := do
  let mut r := r
  for (spec, name) in [({ key := .date, descending := false : Filter.SortSpec }, "date ascending"),
                       ({ key := .date, descending := true }, "date descending")] do
    let rows ← Txns.list ctx .all spec 10000
    let dates := (rows.map (fun t => t.date.toIso)).toList
    let ordered := dates.zip (dates.drop 1) |>.all fun (a, b) =>
      if spec.descending then b ≤ a else a ≤ b
    r := check r s!"{name} is monotonic" ordered
  -- The amount sort must follow the signed figure the ledger displays.
  let asc ← Txns.list ctx .all { key := .amount, descending := false } 10000
  let accounts ← Accounts.list ctx
  let sheet := (accounts.filter (fun a => a.kind == .asset || a.kind == .liability)).map (·.id)
  let signed (t : Transaction) : Int :=
    (sheet.map (fun a => t.netIn a "EUR")).foldl (· + ·) 0
  let values := (asc.map signed).toList
  r := check r "the amount sort is monotonic in the signed balance-sheet movement"
    (values.zip (values.drop 1) |>.all (fun (a, b) => a ≤ b))
  return r

/-- Re-staging the same records must be a no-op. -/
private def importIdempotence (ctx : Ctx) (r : Report) : IO Report := do
  let account ← Accounts.ensure ctx "Assets.Bank.Import"
  let records : Array RawRecord := #[
    { date := (Date.ofIso? "2026-05-01").getD default, amount := ⟨Commodity.eur, -1299⟩,
      payee := some "Cafe", purpose := some "coffee" },
    { date := (Date.ofIso? "2026-05-02").getD default, amount := ⟨Commodity.eur, -4990⟩,
      payee := some "REWE", purpose := some "shop", bankRef := some "REF-1" }]
  -- A statement legitimately repeats an identical transfer; both must survive.
  let twins : Array RawRecord := #[
    { date := (Date.ofIso? "2026-06-01").getD default, amount := ⟨Commodity.eur, -100000⟩,
      payee := some "Christian Merten", purpose := some "Transfer" },
    { date := (Date.ofIso? "2026-06-01").getD default, amount := ⟨Commodity.eur, -100000⟩,
      payee := some "Christian Merten", purpose := some "Transfer" }]
  let twinAccount ← Accounts.ensure ctx "Assets.Bank.Twins"
  let (_, twinsFirst) ← Imports.stage ctx twinAccount.id "test" none twins
  let (twinBatch, twinsAgain) ← Imports.stage ctx twinAccount.id "test" none twins
  let r := checkEq r "identical rows in one file both stage" twinsFirst.size 2
  let r := checkEq r "re-importing the identical pair stages nothing" twinsAgain.size 0
  let r := checkEq r "and counts both as duplicates" twinBatch.duplicates 2
  let (_, first) ← Imports.stage ctx account.id "test" none records
  let (batch2, second) ← Imports.stage ctx account.id "test" none records
  let mut r := checkEq r "first import stages every row" first.size 2
  r := checkEq r "second import stages nothing" second.size 0
  r := checkEq r "second import counts the duplicates" batch2.duplicates 2
  -- Promoting is likewise idempotent: an entry leaves the `new` state for good.
  let some firstEntry := first[0]? | return check r "first import produced an entry" false
  let created ← Imports.promoteBatch ctx firstEntry.batch "test"
  let again ← Imports.promoteBatch ctx firstEntry.batch "test"
  r := checkEq r "promote creates one transaction per row" created.size 2
  r := checkEq r "re-promoting creates nothing" again.size 0
  return r

/-- The invariant that has to hold over any store: everything sums to zero. -/
private def trialBalance (ctx : Ctx) (r : Report) : IO Report := do
  let entries ← Balances.trial ctx
  let bad := entries.filter (fun e => e.minor != 0)
  return check r s!"trial balance is zero (offenders: {bad.map (·.commodity)})" bad.isEmpty

/-- End-to-end through the route table, the way the CLI and server both call it. -/
private def routeSmoke (ctx : Ctx) (r : Report) : IO Report := do
  let caller := Api.bootstrapCaller
  let health ← Api.handleSafe ctx caller (Api.Req.simple "GET" ["health"])
  let mut r := checkEq r "health responds 200" health.code 200
  let missing ← Api.handleSafe ctx caller (Api.Req.simple "GET" ["nope"])
  r := checkEq r "unknown route is a 404" missing.code 404
  let unbalanced ← Api.handleSafe ctx caller
    ((Api.Req.simple "POST" ["transactions"]).withJson (Json.mkObj [
      ("date", "2026-01-01"),
      ("postings", Json.arr #[Json.mkObj [("account", "Assets.Cash"), ("amount", "10.00")]])]))
  r := checkEq r "the API refuses an unbalanced transaction" unbalanced.code 400
  -- A partial edit must merge. Sending only labels once left the transaction
  -- with no postings at all, which balances vacuously and so passed validation.
  let account ← Accounts.ensure ctx "Assets.Bank.PatchTest"
  let counter ← Accounts.ensure ctx "Expenses.PatchTest"
  let txId ← freshId
  let t : Transaction :=
    { id := ⟨txId⟩, date := (Date.ofIso? "2026-03-03").getD default, payee := some "Shop"
      narration := "before"
      postings := [{ account := account.id, amount := ⟨Commodity.eur, -500⟩ },
                   { account := counter.id, amount := ⟨Commodity.eur, 500⟩ }]
      source := .imported ⟨"batch"⟩ "fp" }
  match t.validate with
  | .error _ => r := check r "patch fixture is balanced" false
  | .ok bt => Txns.put ctx bt "test"
  let patched ← Api.handleSafe ctx caller
    ((Api.Req.simple "PATCH" ["transactions", txId]).withJson
      (Json.mkObj [("labels", Json.arr #[Json.str "groceries"])]))
  r := checkEq r "a labels-only patch succeeds" patched.code 200
  match ← Txns.get? ctx ⟨txId⟩ with
  | none => r := check r "the patched transaction still exists" false
  | some after =>
    r := checkEq r "a labels-only patch keeps the postings" after.postings.length 2
    r := checkEq r "it keeps the narration" after.narration "before"
    r := checkEq r "it keeps the payee" after.payee (some "Shop")
    r := checkEq r "it keeps import provenance" after.source.encode "import:batch:fp"
    r := checkEq r "and it applied the labels" after.labels.length 1
  -- Moving a posting to another account keeps it balanced.
  let moved ← Api.handleSafe ctx caller
    ((Api.Req.simple "PATCH" ["transactions", txId]).withJson
      (Json.mkObj [("postings", Json.arr #[
        Json.mkObj [("account", "Assets.Bank.PatchTest"), ("minor", Json.num (-500)),
                    ("commodity", "EUR")],
        Json.mkObj [("account", "Expenses.Moved"), ("minor", Json.num (500)),
                    ("commodity", "EUR")]])]))
  r := checkEq r "a posting can be rebooked" moved.code 200
  let readOnly : Api.Caller := { actor := "ro", scopes := Scopes.ofList [.read] }
  let denied ← Api.handleSafe ctx readOnly
    ((Api.Req.simple "POST" ["labels"]).withJson (Json.mkObj [("name", "x")]))
  r := checkEq r "a read-only token cannot write" denied.code 400
  /- ## Body caps
  The same defence the sequencer makes, and the same shape: one number read off
  the method and the path before anything expensive is reached. The transport
  uses it to stop reading and the route table checks it again, because the CLI in
  local mode reaches this table without a socket — which is also what lets the
  refusal be tested here, with no HTTP anywhere. -/
  r := checkEq r "the default body cap is 64 KiB" (Api.bodyLimit "POST" ["labels"]) (64 * 1024)
  r := checkEq r "reading asks for nothing more"
    (Api.bodyLimit "GET" ["transactions"]) (64 * 1024)
  r := checkEq r "writing a transaction is a megabyte"
    (Api.bodyLimit "POST" ["transactions"]) (1024 * 1024)
  r := checkEq r "and so is dividing one"
    (Api.bodyLimit "POST" ["transactions", "t1", "divide"]) (1024 * 1024)
  r := checkEq r "a receipt being uploaded is sixteen"
    (Api.bodyLimit "PUT" ["attachments"]) (16 * 1024 * 1024)
  r := checkEq r "and so is a bank's export" (Api.bodyLimit "POST" ["imports"]) (16 * 1024 * 1024)
  let bodyOf (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0 : UInt8))
  let tooBig ← Api.handleSafe ctx caller
    ((Api.Req.simple "POST" ["labels"]).withBody (bodyOf (64 * 1024 + 1)))
  r := checkEq r "a body one byte past the cap is a 413" tooBig.code 413
  let atCap ← Api.handleSafe ctx caller
    ((Api.Req.simple "POST" ["labels"]).withBody (bodyOf (64 * 1024)))
  r := check r "and a body exactly at it is refused for some other reason, or not at all"
    (atCap.code != 413)
  let bigUpload ← Api.handleSafe ctx caller
    ((Api.Req.simple "PUT" ["attachments"]).withBody (bodyOf (64 * 1024 + 1)))
  r := check r "the routes that carry a file are not held to the small cap"
    (bigUpload.code != 413)
  return r

/-- Merging, unmerging, and the signature extraction they rest on. -/
private def mergeTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let bank ← Accounts.ensure ctx "Assets.Bank.Merge"
  let shop ← Accounts.ensure ctx "Expenses.Merge.Shop"
  let fees ← Accounts.ensure ctx "Expenses.Merge.Fees"
  let mk (id : String) (origin : String) (counter : AccountId) (minor : Int) : Transaction :=
    { id := ⟨id⟩, date := (Date.ofIso? "2026-02-17").getD default, payee := some "NAMECHEAP"
      narration := s!"purchase {id}"
      postings := [{ account := bank.id, amount := ⟨eur, -minor⟩, origin := some origin },
                   { account := counter, amount := ⟨eur, minor⟩, origin := some origin }] }
  let purchase := mk "mrg-a" "fp-a" shop.id 1788
  let fee := mk "mrg-b" "fp-b" fees.id 38
  let mut r := r
  for t in [purchase, fee] do
    match t.validate with
    | .error _ => r := check r "merge fixture balances" false
    | .ok bt => Txns.put ctx bt "test"
  let merged ← Txns.merge ctx #[⟨"mrg-a"⟩, ⟨"mrg-b"⟩] "test"
  r := checkEq r "merging keeps every posting" merged.postings.length 4
  r := checkEq r "the merge is balanced" (decide merged.Balanced) true
  r := checkEq r "both origins survive" merged.origins.length 2
  r := checkEq r "the narration comes from the larger leg" merged.narration "purchase mrg-a"
  r := checkEq r "the net on the bank account is the sum of both legs"
    (merged.netIn bank.id "EUR") (-1826)
  r := checkEq r "the sources are gone" (← Txns.get? ctx ⟨"mrg-a"⟩).isNone true
  -- and back again
  let parts ← Txns.unmerge ctx merged.id "test"
  r := checkEq r "unmerging restores both entries" parts.size 2
  r := checkEq r "each part balances"
    (parts.all (fun p => decide p.Balanced)) true
  r := checkEq r "the merged transaction is gone" (← Txns.get? ctx merged.id).isNone true
  r := checkEq r "and the amounts survived the round trip"
    ((parts.map (fun p => p.netIn bank.id "EUR")).foldl (· + ·) 0) (-1826)
  -- unmerging something that never was merged is refused rather than destructive
  let single := parts[0]!
  let failed ← (do discard <| Txns.unmerge ctx single.id "test"; pure false) <|> pure true
  r := check r "unmerging a single-origin transaction is refused" failed
  return r

/-- The displayed figure must be the money leaving, even between two own accounts. -/
private def headlineTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let from_ ← Accounts.ensure ctx "Assets.Bank.HeadA"
  let to_ ← Accounts.ensure ctx "Assets.Bank.HeadB"
  let shop ← Accounts.ensure ctx "Expenses.Head.Shop"
  let env ← Wire.NameEnv.load ctx
  let mk (a b : AccountId) (minor : Int) : Transaction :=
    { id := ⟨"head"⟩, date := (Date.ofIso? "2026-08-31").getD default
      postings := [{ account := a, amount := ⟨eur, -minor⟩ },
                   { account := b, amount := ⟨eur, minor⟩ }] }
  let mut r := r
  -- Both legs are assets, so the tie must break towards the outgoing side.
  match Wire.headline env (mk from_.id to_.id 100000) with
  | some (account, amount) =>
    r := checkEq r "a transfer shows the account the money left" account "Assets.Bank.HeadA"
    r := checkEq r "and shows it as an outgoing amount" amount.minor (-100000)
  | none => r := check r "a transfer has a headline" false
  -- Ordinary spending is unaffected, whichever way round the postings sit.
  match Wire.headline env (mk from_.id shop.id 4990) with
  | some (account, amount) =>
    r := checkEq r "spending shows the bank account" account "Assets.Bank.HeadA"
    r := checkEq r "with the amount that left it" amount.minor (-4990)
  | none => r := check r "spending has a headline" false
  match Wire.headline env (mk shop.id from_.id 4990) with
  | some (account, _) =>
    r := checkEq r "posting order does not change which account is shown"
      account "Assets.Bank.HeadA"
  | none => r := check r "reversed spending has a headline" false
  return r

/-- The card signature is what makes fee pairing exact rather than fuzzy. -/
private def signatureTests (r : Report) : Report := Id.run do
  let mut r := r
  let feeLine := "VISA 63371014 KINGS X (N) 50,00 GBP           20.08.             12874112"
  let buyLine := "VISA 63371014 KINGS X (N) 50,00 GBP 1,1711700 19.08.       58,56 10354112"
  match CardSignature.parse? feeLine, CardSignature.parse? buyLine with
  | some a, some b =>
    r := checkEq r "the fee and its purchase share a signature" a b
    r := checkEq r "the card is read" a.card "63371014"
    r := checkEq r "the merchant is read" a.merchant "KINGS X (N)"
    r := checkEq r "the foreign amount is read" a.amount "50,00"
    r := checkEq r "the currency is read" a.currency "GBP"
  | _, _ => r := check r "both lines yield a signature" false
  r := check r "a line without a foreign amount has no signature"
    (CardSignature.parse? "Monatlicher Beitrag Christian").isNone
  -- the exchange rate must not leak into the key, or nothing would ever match
  r := check r "the exchange rate is excluded from the key"
    ((CardSignature.parse? buyLine).all (fun s => s.amount != "1,1711700"))
  return r

/--
Upgrading a store that already has data in it.

The migrations that introduce owners and claims are the only ones in this system
that change what an existing row *means*, so they are the only ones worth
rehearsing against rows written the old way. Two things must survive: a
receivable has to come out as an account belonging to the person it was named
after, with its balance unchanged, and no posting may go missing behind the view
that now hides the unposted ones.

Migration 25 is the third, and it changes no meaning — it rebuilds `account`
under live foreign keys to make a name unique inside a realm instead of across
the ledger. What has to survive that is every account, the realm each was in, and
every posting's reference to one, so a store one version short of it is migrated
here as well.
-/
private def migrationTests (r : Report) : IO Report := do
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-migrate-{← freshId}"
  IO.FS.createDirAll root
  try
    let db ← SQLite.open (root / "old.db") (busyTimeoutMs := 5000)
    -- A store as it stood before any of this: receivables, no owners, no states.
    for (v, sql) in Schema.migrations do
      if v ≤ 10 then
        SQLite.transaction db do
          Db.exec db sql
          Db.exec db s!"PRAGMA user_version = {v}"
    Db.exec db "INSERT INTO account (id, name, kind, commodity, iban, note, closed_on) VALUES
      ('acc-recv', 'Assets.Receivable.Bo', 'asset', NULL, NULL, NULL, NULL),
      ('acc-bank', 'Assets.Bank.Old', 'asset', NULL, NULL, NULL, NULL)"
    Db.exec db "INSERT INTO txn (id, date, payee, narration, source, created_at, updated_at)
      VALUES ('old-1', '2026-01-01', 'Hut', 'beds', 'manual:old', 'x', 'x')"
    Db.exec db "INSERT INTO posting (txn_id, idx, account_id, minor, commodity, party_id, note)
      VALUES ('old-1', 0, 'acc-bank', -5000, 'EUR', NULL, NULL),
             ('old-1', 1, 'acc-recv', 5000, 'EUR', NULL, NULL)"
    let ran ← Schema.migrate db
    let mut r := check r "the pending migrations run" (ran > 0)
    r := checkEq r "and leave the store at the version this binary expects"
      (← Schema.currentVersion db) Schema.targetVersion
    r := checkEq r "a receivable becomes an account under the person's own name"
      ((← Db.row? String db "SELECT name FROM account WHERE id = 'acc-recv'").getD "")
      "Assets.Purse.Bo"
    r := checkEq r "belonging to them"
      ((← Db.row? String db
        "SELECT p.name FROM account a JOIN party p ON p.id = a.owner_id
         WHERE a.id = 'acc-recv'").getD "") "Bo"
    r := check r "while your own accounts stay yours"
      ((← Db.row? String db "SELECT owner_id FROM account WHERE id = 'acc-bank'").getD ""
        == Party.selfId.val)
    r := checkEq r "its balance is exactly what it was"
      (← Db.scalarInt db "SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = 'acc-recv'")
      5000
    r := checkEq r "every posting is still visible through the view"
      (← Db.scalarInt db "SELECT COUNT(*) FROM posting") 2
    r := checkEq r "and none was lost from the table beneath it"
      (← Db.scalarInt db "SELECT COUNT(*) FROM posting_all") 2
    r := checkEq r "rows written before states existed are posted"
      (← Db.scalarInt db "SELECT COUNT(*) FROM txn WHERE state = 'posted'") 1
    -- The property the view exists for: an unposted row reaches no balance.
    Db.exec db "INSERT INTO txn (id, date, payee, narration, state, source, created_at, updated_at)
      VALUES ('claim-1', '2026-02-01', NULL, 'a claim', 'pending', 'manual:old', 'x', 'x')"
    Db.exec db "INSERT INTO posting_all (txn_id, idx, account_id, minor, commodity, party_id, note)
      VALUES ('claim-1', 0, 'acc-bank', 5000, 'EUR', NULL, NULL),
             ('claim-1', 1, 'acc-recv', -5000, 'EUR', NULL, NULL)"
    r := checkEq r "a claim changes no balance"
      (← Db.scalarInt db "SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = 'acc-recv'")
      5000
    r := checkEq r "though it is there to be read"
      (← Db.scalarInt db
        "SELECT IFNULL(SUM(minor), 0) FROM posting_all WHERE account_id = 'acc-recv'") 0
    -- A store one version behind, with accounts in two realms and postings
    -- against them. Migration 25 cannot alter `account`'s constraint, so it
    -- rebuilds the table underneath live foreign keys — and what has to survive
    -- that is every account, the realm each was in, and every posting's
    -- reference to one. Foreign keys are on here exactly as a real store has
    -- them, because a rebuild under them is the whole difficulty.
    let old ← SQLite.open (root / "pre25.db") (busyTimeoutMs := 5000)
    Db.exec old "PRAGMA foreign_keys = ON"
    for (v, sql) in Schema.migrations do
      if v ≤ 24 then
        SQLite.transaction old do
          Db.exec old sql
          Db.exec old s!"PRAGMA user_version = {v}"
    Db.exec old "INSERT INTO realm (id, name, generation) VALUES ('r-sicily', 'Sicily', 0)"
    Db.exec old "INSERT INTO account (id, name, kind, owner_id, realm_id) VALUES
      ('acc-mine', 'Budget.Hut', 'equity', '0000000000000000000000SELF',
       '0000000000000000000000SELF'),
      ('acc-theirs', 'Budget.Sicily', 'equity', '0000000000000000000000SELF', 'r-sicily')"
    Db.exec old "INSERT INTO txn (id, date, payee, narration, source, created_at, updated_at)
      VALUES ('pre-1', '2026-03-01', NULL, 'a cost', 'manual:old', 'x', 'x')"
    Db.exec old "INSERT INTO posting_all (txn_id, idx, account_id, minor, commodity)
      VALUES ('pre-1', 0, 'acc-mine', 2500, 'EUR'), ('pre-1', 1, 'acc-theirs', -2500, 'EUR')"
    r := checkEq r "a store written before the rebuild stops one short of it"
      (← Schema.currentVersion old) 24
    r := check r "and the rebuild runs when it is opened" ((← Schema.migrate old) > 0)
    r := checkEq r "leaving it at the version this binary expects"
      (← Schema.currentVersion old) Schema.targetVersion
    r := checkEq r "every account came through the rebuild"
      (← Db.scalarInt old "SELECT COUNT(*) FROM account") 2
    r := checkEq r "in the realm it was in"
      ((← Db.row? String old "SELECT realm_id FROM account WHERE id = 'acc-theirs'").getD "")
      "r-sicily"
    r := checkEq r "every posting still names an account that is there"
      (← Db.scalarInt old
        "SELECT COUNT(*) FROM posting_all p JOIN account a ON a.id = p.account_id") 2
    r := checkEq r "and the rebuild left no reference dangling"
      (← Db.scalarInt old "SELECT COUNT(*) FROM pragma_foreign_key_check") 0
    let orphan := "INSERT INTO posting_all (txn_id, idx, account_id, minor, commodity)
      VALUES ('pre-1', 2, 'nobody', 0, 'EUR')"
    r := check r "a posting to an account that is not there is still refused"
      (← (do Db.exec old orphan; pure false) <|> pure true)
    -- The constraint the rebuild exists to replace, read from both sides.
    Db.exec old "INSERT INTO account (id, name, kind, owner_id, realm_id) VALUES
      ('acc-same', 'Budget.Hut', 'equity', '0000000000000000000000SELF', 'r-sicily')"
    r := checkEq r "a name taken in another realm can be taken here"
      (← Db.scalarInt old "SELECT COUNT(*) FROM account WHERE name = 'Budget.Hut'") 2
    let twice := "INSERT INTO account (id, name, kind, owner_id, realm_id) VALUES
      ('acc-again', 'Budget.Hut', 'equity', '0000000000000000000000SELF', 'r-sicily')"
    r := check r "and taking it twice in one realm is still refused"
      (← (do Db.exec old twice; pure false) <|> pure true)
    return r
  finally
    IO.FS.removeDirAll root <|> pure ()

/--
Settlement plans, over positions made up rather than read out of a store.

Two properties, and only one of them is about being short. A plan has to leave
everybody at zero — that is the contract `validate` enforces before a claim is
written — and it must not be longer than one transfer per person.
-/
private def settleTests (r : Report) : Report := Id.run do
  let mut r := r
  let cases : List (String × List Settle.Position) :=
    [("two people", [⟨"a", 500⟩, ⟨"b", -500⟩]),
     ("one creditor, several debtors", [⟨"a", 300⟩, ⟨"b", 700⟩, ⟨"c", -1000⟩]),
     ("crossing both ways", [⟨"a", 250⟩, ⟨"b", -100⟩, ⟨"c", 40⟩, ⟨"d", -190⟩]),
     ("somebody already square", [⟨"a", 0⟩, ⟨"b", 120⟩, ⟨"c", -120⟩]),
     ("nobody owes anybody", [⟨"a", 0⟩, ⟨"b", 0⟩])]
  for (name, ps) in cases do
    let plan := Settle.greedy ps
    r := check r s!"greedy settles {name}" (decide (Settle.Settles ps plan))
    r := check r s!"greedy is short for {name}" (plan.length + 1 ≤ ps.length + 1)
    r := check r s!"greedy never asks for nothing in {name}" (plan.all fun t => t.minor > 0)
    let hub := Settle.star "c" ps
    r := check r s!"a hub settles {name} too"
      (decide (Settle.Settles ps hub) || (ps.find? (·.who == "c")).isNone)
  -- Positions that do not sum to zero cannot be settled by anything, and saying
  -- so is the whole reason `validate` exists.
  let broken : List Settle.Position := [⟨"a", 100⟩, ⟨"b", -40⟩]
  r := check r "a plan for positions that do not net out is refused"
    (Settle.validate broken (Settle.greedy broken)).toOption.isNone
  r := check r "and the refusal names the total that is unaccounted for"
    (Settle.total broken == 60)
  return r

/--
What a realm is, through the routes that make one.

A realm is the unit of sharing: one key, one set of members, one thing somebody
can be let into. Sharing a budget is therefore making a realm and inviting
somebody to it — and the two things that used to stand in for that, a guest
route table and a token that speaks for one person on one budget, are gone.
Checking that they answer 404 and that `budget` is no longer a field of a token
is the other half of this.
-/
private def realmTests (ctx : Ctx) (r : Report) : IO Report := do
  let mut r := r
  let caller := Api.bootstrapCaller
  let reply (m : String) (segs : List String) (body : Json := Json.mkObj []) : IO Api.Reply :=
    Api.handleSafe ctx caller ((Api.Req.simple m segs).withJson body)
  -- Making a realm, and a budget inside it in the same breath.
  let made ← reply "POST" ["realms"] (Json.mkObj [("name", "Sicily"), ("budget", "Sicily")])
  r := checkEq r "a realm can be made" made.code 201
  let some realmJson := made.json? | return check r "the new realm comes back as JSON" false
  let realmId := (realmJson.getObjValAs? String "id").toOption.getD ""
  r := check r "and it has an id" (!realmId.isEmpty)
  r := checkEq r "and it names the budget it was made for"
    ((realmJson.getObjValAs? String "budget").toOption.getD "") "Sicily"
  match ← Budgets.get? ctx "Sicily" with
  | none => r := check r "the budget reached the ledger" false
  | some b =>
    let st ← ctx.state.get
    r := check r "and its account sits in the realm it was opened in"
      (st.accountByNameIn? ⟨realmId⟩ b.name).isSome
  -- Listing says the same thing back.
  let listed ← reply "GET" ["realms"]
  r := checkEq r "realms can be listed" listed.code 200
  match listed.json? with
  | some (.arr rows) =>
    let mine := rows.filter fun x => (x.getObjValAs? String "id").toOption == some realmId
    r := checkEq r "and the new one is in the list" mine.size 1
    r := check r "with you as its admin"
      (mine.any fun x => (x.getObjValAs? Bool "admin").toOption == some true)
    r := check r "and no key, because this store syncs with nothing"
      (mine.any fun x => (x.getObjValAs? Bool "hasKey").toOption == some false)
  | _ => r := check r "the realm list is an array" false
  let members ← reply "GET" ["realms", realmId, "members"]
  r := checkEq r "a realm's members can be read" members.code 200
  r := checkEq r "a realm that is not there is a 404"
    (← reply "GET" ["realms", "nope", "members"]).code 404
  -- An invite is a pending grant on a sequencer, and this store has none.
  let invited ← reply "POST" ["realms", realmId, "invites"] (Json.mkObj [("for", "carla")])
  r := checkEq r "an invite without a sequencer is refused" invited.code 400
  r := check r "and the refusal says what is missing"
    (Str.containsCI (invited.json?.getD Json.null).compress "sequencer")
  -- Sync answers for a store that syncs with nothing, rather than failing.
  let status ← reply "GET" ["sync", "status"]
  r := checkEq r "sync status answers anyway" status.code 200
  r := check r "and says this store syncs with nothing"
    (((status.json?.getD Json.null).getObjValAs? Bool "configured").toOption == some false)
  r := checkEq r "and a round of it is refused" (← reply "POST" ["sync"]).code 400
  -- A token is a credential of your own again: `budget` is not a field it reads.
  let minted ← reply "POST" ["tokens"]
    (Json.mkObj [("name", "not-a-share-link"), ("scopes", "read"), ("budget", "Sicily"),
                 ("for", "carla")])
  r := checkEq r "a token can still be minted" minted.code 201
  match minted.json? with
  | none => r := check r "the minted token is JSON" false
  | some j =>
    r := check r "and nothing about it is a link" ((j.getObjVal? "link").toOption.isNone)
    let tok := (j.getObjVal? "token").toOption.getD Json.null
    r := checkEq r "and its scopes are the ones asked for"
      ((tok.getObjValAs? String "scopes").toOption.getD "") "read"
    r := check r "and it says nothing about a budget"
      ((tok.getObjVal? "budget").toOption.isNone && (tok.getObjVal? "guest").toOption.isNone)
  -- A pot's name is taken inside a realm and not across the store. An account of
  -- a budget's name in a realm of somebody else's is their account, written under
  -- a key this one knows nothing about, and `Core` has always read it that way;
  -- the projection kept `account.name` unique over the whole table until
  -- migration 25, so the realm that reused a name was the realm that could not be
  -- written down — a 500 about a ledger nothing is wrong with.
  let elba ← reply "POST" ["realms"] (Json.mkObj [("name", "Elba")])
  r := checkEq r "a second realm can be made" elba.code 201
  let elbaId := ((elba.json?.getD Json.null).getObjValAs? String "id").toOption.getD ""
  let pot := Budget.accountName "Ischia"
  discard <| ctx.commit "test"
    [.putAccount { id := ⟨"0000000000squatter"⟩, name := pot,
                   kind := .equity, realm := ⟨elbaId⟩ }]
    (realm := ⟨elbaId⟩)
  let ischia ← reply "POST" ["realms"] (Json.mkObj [("name", "Ischia"), ("budget", "Ischia")])
  r := checkEq r "a budget whose account name is taken in another realm is made anyway"
    ischia.code 201
  let ischiaId := ((ischia.json?.getD Json.null).getObjValAs? String "id").toOption.getD ""
  r := check r "and it reached the ledger" ((← Budgets.get? ctx "Ischia").isSome)
  let both ← ctx.state.get
  r := check r "its pot is in the realm it was opened in"
    (both.accountByNameIn? ⟨ischiaId⟩ pot).isSome
  r := checkEq r "and the account of that name in the other realm is untouched"
    ((both.accountByNameIn? ⟨elbaId⟩ pot).map (·.id.val)) (some "0000000000squatter")
  r := checkEq r "so two accounts of one name stand, one to a realm"
    (both.accountsSorted.filter (·.name == pot)).length 2
  -- The tables are where this used to come apart, so they are asked separately.
  r := checkEq r "and the projection holds both rows"
    (← Db.scalarInt ctx.db s!"SELECT COUNT(*) FROM account WHERE name = {Db.lit pot}") 2
  -- The route table a share link used to be dispatched to is not there at all.
  for (m, segs) in [("GET", ["guest"]), ("POST", ["guest", "expenses"]),
                    ("DELETE", ["guest", "expenses", "anything"])] do
    r := checkEq r s!"the retired {m} /{String.intercalate "/" segs} is gone"
      (← reply m segs).code 404
  return r

/-- A participant, resolved the way the API resolves one. -/
private def person (ctx : Ctx) (name account : String) (weight : Nat := 1) : IO Participant := do
  if name.isEmpty then
    return { owner := Party.selfId, name := "me", account, weight }
  let who ← Parties.contact ctx name
  let acc ←
    if account.isEmpty then Accounts.purse ctx who
    else Accounts.ensure ctx account none (some who.id)
  return { owner := who.id, name := who.name, account := acc.name, weight }

/-- Both the rows and the columns of a two-dimensional split have to come out exact. -/
private def biproportionalTests (r : Report) : Report := Id.run do
  let mut r := r
  let cases : List (String × List Int × List Int) :=
    [("even", [200, 200], [400]),
     ("awkward total", [3334, 3333, 3334], [6000, 4001]),
     ("one row takes it all", [0, 40750], [39912, 838]),
     ("more people than costs", [100, 100, 100, 100], [250, 150]),
     ("a single cent", [1, 0], [1])]
  for (name, rows, cols) in cases do
    let grid := biproportional rows cols
    r := checkEq r s!"{name}: every person gets exactly their share"
      (grid.map (fun row => row.sum)) rows
    r := checkEq r s!"{name}: every cost is exactly divided"
      ((List.range cols.length).map fun j => (grid.map (fun row => row[j]!)).sum) cols
    r := check r s!"{name}: nobody is given a negative share"
      (grid.all fun row => row.all (· ≥ 0))
  return r

/--
Dividing a budget that was already divided in part.

`allocate` used to split whatever was left by the weights, which is right only
if every earlier division covered everybody in proportion. A budget divided one
person at a time — which is what the old invoice workflow produced — breaks that,
and so does deleting a division. Topping each person up to the share the weights
say is right either way.
-/
private def topUpTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let giro ← Accounts.ensure ctx "Assets.Bank.TopUp" (kind := some .asset)
  let holding ← Accounts.ensure ctx "Expenses.TopUp.Unsorted"
  let mut r := r
  let budget ← Budgets.open ctx "TopUp"
  let mine := "Expenses.TopUp.Mine"
  let cost (id : String) (minor : Int) : Transaction :=
    { id := ⟨id⟩, date := (Date.ofIso? "2026-07-01").getD default, payee := some id
      narration := "beds"
      postings := [{ account := giro.id, amount := ⟨eur, -minor⟩ },
                   { account := holding.id, amount := ⟨eur, minor⟩ }] }
  for t in [cost "top-1" 20000, cost "top-2" 20000] do
    match t.validate with
    | .error _ => r := check r "top-up fixture balances" false
    | .ok bt => Txns.put ctx bt "test"
  -- One person is given a whole cost, the way a per-person division does it.
  discard <| Budgets.lend ctx budget #[⟨"top-1"⟩] "test"
  discard <| Budgets.allocate ctx budget [← person ctx "zoeT" ""] "test" eur
  let zoe ← Parties.contact ctx "zoeT"
  let zoePurse ← Accounts.purse ctx zoe
  let balanceOf (a : Account) : IO Int := do
    return Ledger.balance (← Txns.list ctx .all {} 10000).toList a.id "EUR"
  r := checkEq r "the first cost went entirely to them" (← balanceOf zoePurse) 20000

  -- Now the second cost, divided between the two of them. Half of everything is
  -- 200 apiece, and they already have 200 — so the whole of it is yours.
  discard <| Budgets.lend ctx budget #[⟨"top-2"⟩] "test"
  discard <| Budgets.allocate ctx budget
    [← person ctx "zoeT" "", ← person ctx "" mine] "test" eur
  r := checkEq r "the remainder is not split down the middle"
    (← balanceOf zoePurse) 20000
  r := checkEq r "it tops up whoever is behind" (← balanceOf (← Accounts.ensure ctx mine)) 20000
  r := checkEq r "and the budget is empty" (← Budgets.balance ctx budget).minor 0

  -- Somebody already given more than the weights leave them cannot be topped
  -- up: the correction is a withdrawal, which dividing costs cannot express.
  let over ← Budgets.open ctx "TopUpOver"
  let cost2 (id : String) (minor : Int) : Transaction := { cost id minor with id := ⟨id⟩ }
  for t in [cost2 "ovr-1" 20000, cost2 "ovr-2" 10000] do
    match t.validate with
    | .error _ => r := check r "over fixture balances" false
    | .ok bt => Txns.put ctx bt "test"
  discard <| Budgets.lend ctx over #[⟨"ovr-1"⟩] "test"
  discard <| Budgets.allocate ctx over [← person ctx "zoeT" ""] "test" eur
  discard <| Budgets.lend ctx over #[⟨"ovr-2"⟩] "test"
  r := check r "dividing further is refused rather than guessed"
    (← (do
      discard <| Budgets.allocate ctx over
        [← person ctx "zoeT" "", ← person ctx "" "Expenses.TopUpOver.Mine"] "test" eur
      pure false) <|> pure true)
  return r

/--
Closing a budget, and closing it again.

Costs accumulate in the account while it is open; closing is the moment somebody
decides, and it is the only thing that divides. Reopening and closing again
writes a *second* division covering only what came in since — the first one is
not touched, because somebody was told what they owed on the strength of it.
-/
private def closeTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let giro ← Accounts.ensure ctx "Assets.Bank.Closing" (kind := some .asset)
  let holding ← Accounts.ensure ctx "Expenses.Closing.Unsorted"
  let mut r := r
  let budget ← Budgets.open ctx "Closing"
  let mine := "Expenses.Closing.Mine"
  Budgets.setParticipants ctx budget [← person ctx "kimS" "", ← person ctx "" mine]
  let kim ← Parties.contact ctx "kimS"
  let kimPurse ← Accounts.purse ctx kim
  let t : Transaction :=
    { id := ⟨"cls-1"⟩, date := (Date.ofIso? "2026-07-01").getD default, payee := some "Hut"
      narration := "beds"
      postings := [{ account := giro.id, amount := ⟨eur, -40000⟩ },
                   { account := holding.id, amount := ⟨eur, 40000⟩ }] }
  match t.validate with
  | .error _ => r := check r "closing fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  discard <| Budgets.lend ctx budget #[⟨"cls-1"⟩] "test"
  discard <| Budgets.contribute ctx budget kimPurse ⟨eur, 6000⟩
    ((Date.ofIso? "2026-07-02").getD default) "the taxi" "test" (some "Taxi")

  -- Open: naming the participants decides nothing on its own.
  r := checkEq r "everything waits in the account while it is open"
    (← Budgets.balance ctx budget).minor 46000
  r := checkEq r "nothing has been divided" (← Budgets.allocated ctx budget).minor 0
  let outstanding : IO (Array Transaction) := do
    return (← Budgets.claims ctx budget).filter fun x => x.state == .pending
  r := checkEq r "and nobody has been asked for anything" (← outstanding).size 0

  -- Closing divides, once, and asks.
  let before ← Db.scalarInt ctx.db "SELECT COUNT(*) FROM txn WHERE state = 'posted'"
  let (divided, raised) ← Budgets.close ctx budget "test" eur
  r := check r "closing writes a division" divided.isSome
  r := checkEq r "exactly one entry"
    (← Db.scalarInt ctx.db "SELECT COUNT(*) FROM txn WHERE state = 'posted'") (before + 1)
  r := checkEq r "the account is empty afterwards" (← Budgets.balance ctx budget).minor 0
  r := checkEq r "one claim was raised" raised.size 1
  -- 460 between two, less the 60 they put in.
  r := checkEq r "for what they bear less what they put in"
    (Pendings.amount (← outstanding)[0]!).minor 17000

  -- Closed: nobody adds anything, whoever they are.
  let closed ← Budgets.get? ctx "Closing"
  r := check r "the budget reads back closed" ((closed.map (·.closed)).getD false)
  let refused ← (do
    discard <| Budgets.contribute ctx closed.get! kimPurse ⟨eur, 100⟩
      ((Date.ofIso? "2026-07-03").getD default) "late" "test" none
    pure false) <|> pure true
  r := check r "a closed budget refuses a cost" refused
  r := check r "and refuses to be lent one"
    (← (do discard <| Budgets.lend ctx closed.get! #[⟨"cls-1"⟩] "test"; pure false) <|> pure true)

  -- Reopen, add a late receipt, close again: a second division, not a rewrite.
  Budgets.reopen ctx closed.get! "test"
  let reopened := (← Budgets.get? ctx "Closing").get!
  discard <| Budgets.contribute ctx reopened kimPurse ⟨eur, 10000⟩
    ((Date.ofIso? "2026-07-04").getD default) "the cable car" "test" (some "Bahn")
  r := checkEq r "only the new cost is waiting" (← Budgets.balance ctx reopened).minor 10000
  r := check r "the first division still stands"
    ((← Budgets.allocated ctx reopened).minor == 46000)
  let (again, _) ← Budgets.close ctx reopened "test" eur
  r := check r "closing again writes another division" again.isSome
  r := check r "a different one" (again.map (·.id) != divided.map (·.id))
  let budgetAcc ← Budgets.account ctx reopened
  r := checkEq r "covering only what came in since"
    ((again.map (fun x => x.netIn budgetAcc.id "EUR")).getD 0) (-10000)
  r := checkEq r "everything is divided now" (← Budgets.balance ctx reopened).minor 0
  -- The claim is revised rather than joined by a contradicting one.
  r := checkEq r "still one claim" (← outstanding).size 1
  r := checkEq r "revised to what is actually owed"
    (Pendings.amount (← outstanding)[0]!).minor 12000
  r := checkEq r "and everybody nets to nothing"
    (Settle.total ((← Budgets.standings ctx reopened).toList.map Standing.position)) 0
  return r

/--
Re-settling after the facts change.

A claim that is merely outstanding is a request, and a request made before a
late receipt turned up was made on facts that have since changed. Revising it is
the only answer that reads: raising a second claim in the other direction nets
to the same figure and tells somebody to pay 200 and take 25 back.

The exception is a claim an invoice speaks for. That is in somebody's hands
already, so it is netted off rather than rewritten, and the difference has to go
somewhere — which is the one case where the contradictory-looking pair is right.
-/
private def resettleTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let giro ← Accounts.ensure ctx "Assets.Bank.Resettle" (kind := some .asset)
  let holding ← Accounts.ensure ctx "Expenses.Resettle.Unsorted"
  let mut r := r
  let t : Transaction :=
    { id := ⟨"res-1"⟩, date := (Date.ofIso? "2026-07-01").getD default, payee := some "Hut"
      narration := "beds"
      postings := [{ account := giro.id, amount := ⟨eur, -40000⟩ },
                   { account := holding.id, amount := ⟨eur, 40000⟩ }] }
  match t.validate with
  | .error _ => r := check r "resettle fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  let budget ← Budgets.open ctx "Resettle"
  discard <| Budgets.lend ctx budget #[⟨"res-1"⟩] "test"
  let mine := "Expenses.Resettle.Mine"
  discard <| Budgets.allocate ctx budget
    [← person ctx "maxR" "", ← person ctx "" mine] "test" eur
  let outstanding : IO (Array Transaction) := do
    return (← Budgets.claims ctx budget).filter fun x => x.state == .pending
  r := checkEq r "one claim to start with" (← outstanding).size 1
  r := checkEq r "for half of it" (Pendings.amount (← outstanding)[0]!).minor 20000
  let first := (← outstanding)[0]!.id

  -- He pays for something himself, and it is divided in a second pass.
  let maxR ← Parties.contact ctx "maxR"
  discard <| Budgets.contribute ctx budget (← Accounts.purse ctx maxR) ⟨eur, 5000⟩
    ((Date.ofIso? "2026-07-02").getD default) "the taxi" "test" (some "Taxi")
  -- Nothing can be settled while part of the budget belongs to nobody yet.
  r := check r "settling is refused while something is undivided"
    (← (do discard <| Budgets.settle ctx budget "test"; pure false) <|> pure true)
  discard <| Budgets.allocate ctx budget
    [← person ctx "maxR" "", ← person ctx "" mine] "test" eur
  r := checkEq r "there is still exactly one claim, not a contradicting pair"
    (← outstanding).size 1
  r := checkEq r "and it is the same request, revised" (← outstanding)[0]!.id first
  r := checkEq r "down by half of what he put in"
    (Pendings.amount (← outstanding)[0]!).minor 17500
  r := checkEq r "settling again changes nothing"
    (← Budgets.settle ctx budget "test").size 0

  -- Once a claim has been written up and sent, it is not ours to rewrite.
  let inv ← Invoices.forBudget ctx budget (.link "https://example.org")
    ((Date.ofIso? "2026-07-03").getD default) ((Date.ofIso? "2026-08-03").getD default) eur
  r := checkEq r "the claim gets an invoice" inv.size 1
  discard <| Budgets.contribute ctx budget (← Accounts.purse ctx maxR) ⟨eur, 6000⟩
    ((Date.ofIso? "2026-07-04").getD default) "the cable car" "test" (some "Bahn")
  discard <| Budgets.allocate ctx budget
    [← person ctx "maxR" "", ← person ctx "" mine] "test" eur
  r := checkEq r "an invoiced claim is left alone, and the difference is its own claim"
    (← outstanding).size 2
  r := check r "with the invoiced one untouched"
    ((← outstanding).any fun x => x.id == first && (Pendings.amount x).minor == 17500)
  -- Voiding the document hands the claim back, and the pair collapses again.
  Invoices.setStatus ctx inv[0]!.id .void
  discard <| Budgets.settle ctx budget "test"
  r := checkEq r "voiding the invoice lets the pair collapse" (← outstanding).size 1
  r := checkEq r "to the one figure that is actually owed"
    (Pendings.amount (← outstanding)[0]!).minor 14500
  return r

/-- Claiming, tags that survive the move, and whose the account turns out to be. -/
private def purseTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let bank ← Accounts.ensure ctx "Assets.Bank.Claim"
  let spend ← Accounts.ensure ctx "Expenses.Claim.Food"
  let fees ← Accounts.ensure ctx "Expenses.Claim.Fees"
  -- An outlay with a fee beside it, exactly as a merged foreign purchase looks.
  let outlay : Transaction :=
    { id := ⟨"clm-1"⟩, date := (Date.ofIso? "2026-03-01").getD default, payee := some "Pizza"
      narration := "team dinner"
      postings := [{ account := bank.id, amount := ⟨eur, -10000⟩ },
                   { account := spend.id, amount := ⟨eur, 10000⟩ },
                   { account := bank.id, amount := ⟨eur, -210⟩ },
                   { account := fees.id, amount := ⟨eur, 210⟩, tag := some "fee" }] }
  let repaid : Transaction :=
    { id := ⟨"clm-2"⟩, date := (Date.ofIso? "2026-04-01").getD default, payee := some "Uni"
      narration := "Declaratie"
      postings := [{ account := bank.id, amount := ⟨eur, 6000⟩ },
                   { account := (← Accounts.ensure ctx "Income.Claim.Misc").id,
                     amount := ⟨eur, -6000⟩ }] }
  let mut r := r
  for t in [outlay, repaid] do
    match t.validate with
    | .error _ => r := check r "claim fixture balances" false
    | .ok bt => Txns.put ctx bt "test"
  let uni ← Parties.contact ctx "ClaimTest"
  let purse ← Accounts.purse ctx uni
  let claimed ← Txns.claim ctx #[⟨"clm-1"⟩, ⟨"clm-2"⟩] purse.name "test"
  r := checkEq r "both directions are claimable in one verb" claimed.size 2
  match ← Txns.get? ctx ⟨"clm-1"⟩ with
  | none => r := check r "the claimed outlay survives" false
  | some t =>
    r := checkEq r "the bank leg stays put"
      ((t.postings.filter (fun p => p.account == bank.id)).length) 2
    r := checkEq r "the fee moved into their purse with the purchase"
      ((t.postings.filter (fun p => p.tag == some "fee")).all
        (fun p => p.account != fees.id)) true
    r := checkEq r "and it is still a fee"
      ((t.postings.filter (fun p => p.tag == some "fee")).length) 1
  -- The purse is an ordinary asset that happens to belong to somebody else, and
  -- its balance is the claim between you: laid out, less what came back.
  r := checkEq r "the purse is an asset" purse.kind AccountKind.asset
  r := check r "and it is not yours" (!purse.mine)
  r := checkEq r "its balance is what is still outstanding"
    (Ledger.balance (← Txns.list ctx .all {} 10000).toList purse.id "EUR") 4210
  -- A tag filter finds the fee wherever it now sits.
  let tagged ← Txns.list ctx (.tag "fee") {} 10000
  r := check r "the tag filter finds a fee inside a purse"
    (tagged.any (fun t => t.id.val == "clm-1"))
  -- And the owner filter finds everything that touches them.
  let theirs ← Txns.list ctx (.owner "ClaimTest") {} 10000
  r := check r "the owner filter finds what passes between you"
    (theirs.any (fun t => t.id.val == "clm-1") && theirs.any (fun t => t.id.val == "clm-2"))
  return r

/-- Invoicing from spending: the bill must equal what actually went out. -/
private def invoiceFromTxnTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let bank ← Accounts.ensure ctx "Assets.Bank.Bill"
  let mk (id : String) (minor fee : Int) : Transaction :=
    { id := ⟨id⟩, date := (Date.ofIso? "2026-05-05").getD default, payee := some "Hut"
      narration := "stay"
      postings := [{ account := bank.id, amount := ⟨eur, -minor⟩ },
                   { account := (⟨"unset"⟩ : AccountId), amount := ⟨eur, minor⟩ },
                   { account := bank.id, amount := ⟨eur, -fee⟩ },
                   { account := (⟨"unset"⟩ : AccountId), amount := ⟨eur, fee⟩,
                     tag := some "fee" }] }
  let holding ← Accounts.ensure ctx "Expenses.Bill.Unsorted"
  let fix (t : Transaction) : Transaction :=
    { t with postings := t.postings.map fun p =>
        if p.account.val == "unset" then { p with account := holding.id } else p }
  let a := fix (mk "bill-1" 100000 2100)
  let b := fix (mk "bill-2" 5000 105)
  let mut r := r
  for t in [a, b] do
    match t.validate with
    | .error _ => r := check r "billing fixture balances" false
    | .ok bt => Txns.put ctx bt "test"
  let budget ← Budgets.open ctx "Bill"
  discard <| Budgets.lend ctx budget #[⟨"bill-1"⟩, ⟨"bill-2"⟩] "test"
  let uni ← Parties.contact ctx "Uni"
  discard <| Budgets.allocate ctx budget [← person ctx "Uni" ""] "test" eur
  let some after ← Budgets.get? ctx "Bill" | return (check r "the budget reads back" false)
  let standings ← Budgets.standings ctx after
  r := checkEq r "two positions when one person bears it all" standings.size 2
  match standings.find? (·.owner == uni.id) with
  | none => r := check r "their position exists" false
  | some standing =>
    -- The card fee rides along with the purchase: both are being borne.
    r := checkEq r "their share is the whole outlay, fee included" standing.amount.minor 107205
    let lines ← Invoices.linesFor ctx after uni.id
    -- Two costs, each with a card fee beside it, and the fee is divided in the
    -- same proportion rather than smeared into the purchase.
    r := checkEq r "one line per cost, and one per fee" lines.length 4
    r := checkEq r "and the lines add back to the share exactly"
      ((lines.map (fun l => l.net.minor)).sum) standing.amount.minor
    r := check r "identical payees on one day get distinguishable descriptions"
      (((lines.map (·.description)).eraseDups).length == lines.length)
  -- The positions sum to what the budget still holds, which is the invariant
  -- that makes a settlement plannable at all.
  r := checkEq r "the positions sum to nothing once everything is divided"
    (Settle.total (standings.toList.map Standing.position)) 0
  return r

/-- Splitting a shared bill, and the trip machinery built on top of it. -/
private def splitAndTripTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let cash ← Accounts.ensure ctx "Assets.Cash.Split"
  let hut ← Accounts.ensure ctx "Expenses.Split.Huts"
  let mk (id : String) (minor fee : Int) (date : String) : Transaction :=
    { id := ⟨id⟩, date := (Date.ofIso? date).getD default, payee := some "Hut"
      narration := "half board"
      postings := [{ account := cash.id, amount := ⟨eur, -minor⟩ },
                   { account := hut.id, amount := ⟨eur, minor - fee⟩ },
                   { account := hut.id, amount := ⟨eur, fee⟩, tag := some "fee" }] }
  let mut r := r
  match (mk "spl-1" 10000 0 "2026-07-07").validate with
  | .error _ => r := check r "split fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  -- 100.00 three ways cannot come to 99.99.
  let divided ← Txns.split ctx ⟨"spl-1"⟩ ["anna", "ben"] true "test"
  r := checkEq r "the split stays balanced" (decide divided.Balanced) true
  let shares := (divided.postings.filter (fun p => p.account != cash.id)).map (·.amount.minor)
  r := checkEq r "the shares add back to the bill" (shares.sum) 10000
  r := checkEq r "three people, three shares" shares.length 3
  r := check r "and they differ by at most a cent"
    (shares.all (fun x => x == 3333 || x == 3334))
  -- Fronting the whole bill leaves you nothing.
  match (mk "spl-2" 9000 0 "2026-07-08").validate with
  | .error _ => r := check r "second split fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  let allTheirs ← Txns.split ctx ⟨"spl-2"⟩ ["anna", "ben"] false "test"
  r := checkEq r "fronting the whole bill leaves you no share"
    (allTheirs.netIn hut.id "EUR") 0
  -- A fee keeps its tag inside every share rather than being smeared away.
  match (mk "spl-3" 10000 210 "2026-07-09").validate with
  | .error _ => r := check r "fee split fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  let withFee ← Txns.split ctx ⟨"spl-3"⟩ ["anna"] true "test"
  r := checkEq r "the fee survives splitting as a fee"
    ((withFee.postings.filter (fun p => p.tag == some "fee")).map (·.amount.minor)).sum 210

  -- Splitting many at once, with a saved group, must match splitting each.
  discard <| Groups.save ctx "test-crew" ["anna", "ben"]
  match ← Groups.byName? ctx "test-crew" with
  | none => r := check r "the group was saved" false
  | some g => r := checkEq r "with its members" g.members.length 2
  for (id, amount) in [("spl-4", 6000), ("spl-5", 4500)] do
    match (mk id amount 0 "2026-07-07").validate with
    | .error _ => r := check r "bulk fixture balances" false
    | .ok bt => Txns.put ctx bt "test"
  let bulk ← Txns.splitAll ctx #[⟨"spl-4"⟩, ⟨"spl-5"⟩] ["anna", "ben"] true "test"
  r := checkEq r "both were split" bulk.size 2
  r := check r "and both still balance" (bulk.all (fun t => decide t.Balanced))
  let owed := bulk.foldl (fun acc t =>
    acc + (t.postings.filter (fun p => p.account.val != cash.id.val)).foldl
      (fun a p => a + p.amount.minor) 0) 0
  r := checkEq r "nothing was lost across the batch" owed 10500

  -- Trips: suggest inside the window, exclude what is already claimed.
  let trip ← Trips.create ctx "test-trip" ((Date.ofIso? "2026-07-06").getD default)
    ((Date.ofIso? "2026-07-10").getD default) "Uni"
  let suggested ← Trips.suggest ctx trip
  r := check r "a trip suggests spending inside its window" (!suggested.isEmpty)
  let outside ← Txns.list ctx (.dateFrom ((Date.ofIso? "2026-07-11").getD default)) {} 10000
  r := check r "and nothing outside it"
    (suggested.all fun x => !outside.any (fun y => y.id == x.id))
  discard <| Trips.add ctx trip (suggested.map (·.id)) "test"
  let members ← Trips.members ctx trip
  r := checkEq r "adding labels them all" members.size suggested.size
  r := check r "and claims them against the payer"
    (members.all fun x => x.postings.any fun p =>
      (p.account.val != cash.id.val) && x.postings.length > 1)
  let after ← Trips.suggest ctx trip
  r := check r "so they stop being suggested" after.isEmpty
  return r

/-- Reading a receipt, and vCard contacts. -/
private def receiptTests (r : Report) : Report := Id.run do
  let mut r := r
  let text := "Cabane du Trient CAS\nCol de Balme\nDatum 07.07.2026\n" ++
    "2x Halbpension 180,00\nTotal 204,50\n"
  r := checkEq r "the total is the largest amount on the page"
    ((Receipts.guessTotal Commodity.eur text).map (·.minor)) (some 20450)
  r := checkEq r "the date is read"
    ((Receipts.guessDate text).map (·.toIso)) (some "2026-07-07")
  r := checkEq r "the merchant is the first line with words in it"
    (Receipts.guessMerchant text) (some "Cabane du Trient CAS")
  r := check r "a page with no amounts yields no total"
    (Receipts.guessTotal Commodity.eur "nothing here").isNone
  -- Line items, over the shapes Swiss and French tills actually print. The
  -- summary block underneath must not read as items, or a bill would appear to
  -- contain its own total.
  let chf := Commodity.ofCode "CHF"
  let hut := " 2 Haslikuchen             6.00     12.00 A\n" ++
    " 1 Panaché 0,5                       7.00 A\n" ++
    "-1 Panaché 0,5                      -7.00 A\n" ++
    " 1 Tegernseer Hell 5 dl               8,00 C\n" ++
    "18 FORFAIT 1/2 PENSION à 68.00    1224.00\n" ++
    "Gesamt: 642.00 CHF\n" ++
    " 0.00% A   642.00    0.00   642.00\n" ++
    "Barzahlung 642.00   Kurs 1.00   Gesamt 642.00\n"
  let its := Receipts.guessItems chf hut
  r := checkEq r "only the priced lines are items" its.length 5
  r := checkEq r "a unit price the count implies is dropped"
    ((its[0]?).map (·.description)) (some "Haslikuchen")
  r := checkEq r "the line total wins over the unit price"
    ((its[0]?).map (·.amount.minor)) (some 1200)
  r := checkEq r "a size in the name is not a unit price"
    ((its[1]?).map (·.description)) (some "Panaché 0,5")
  r := checkEq r "a correction keeps its sign"
    ((its[2]?).map (·.amount.minor)) (some (-700))
  r := checkEq r "a correction keeps its count"
    ((its[2]?).bind (·.qty)) (some (-1))
  r := checkEq r "a bare line total is read"
    ((its[3]?).map (·.amount.minor)) (some 800)
  r := checkEq r "the multiplier mark is trimmed off the name"
    ((its[4]?).map (·.description)) (some "FORFAIT 1/2 PENSION")
  r := checkEq r "the count is kept" ((its[4]?).bind (·.qty)) (some 18)
  -- The lines are not obliged to reach the total, and must not be padded to it.
  r := checkEq r "lines stand for themselves, not for the total"
    ((its.map (·.amount.minor)).sum) (1200 + 700 - 700 + 800 + 122400)
  -- vCards, including the folded lines real address books emit.
  -- (Kind handling is checked against the store below.)
  let vcf := "BEGIN:VCARD\nVERSION:3.0\nFN:Ada Lovelace\n" ++
    "EMAIL;TYPE=INTERNET:ada@example.org\nX-IBAN:DE02 1203 0000 0000 2020 51\nEND:VCARD\n" ++
    "BEGIN:VCARD\nN:Klein;Marius;;;\nEMAIL:m@example.org\nEND:VCARD\n"
  let contacts := Contacts.parse vcf
  r := checkEq r "both cards are read" contacts.size 2
  r := checkEq r "the formatted name wins" (contacts[0]!).name "Ada Lovelace"
  r := checkEq r "the email is read" (contacts[0]!).email (some "ada@example.org")
  r := checkEq r "spaces are stripped from the IBAN"
    (contacts[0]!).iban (some "DE02120300000000202051")
  r := checkEq r "a card without FN falls back to N" (contacts[1]!).name "Marius Klein"
  return r

/--
Dividing a payment by the lines on its receipt.

The property that matters is that dividing cannot invent money: whatever the
parts book, and wherever they book it, together they must still take exactly
what the original took out of the account the money left. The remainder is the
normal ending, because the lines on a scanned receipt hardly ever reach the
total -- a fold in the paper is enough.
-/
private def divideTests (ctx : Ctx) (r : Report) : IO Report := do
  let mut r := r
  let chf := Commodity.ofCode "CHF"
  let sha := "00feed00feed00feed00feed00feed00feed00feed00feed00feed00feed0000"
  let cash ← Accounts.ensure ctx "Assets.Cash.Hut" (kind := some .asset)
  let rest ← Accounts.ensure ctx "Expenses.Hut.Unclassified" (kind := some .expense)
  -- A stored file, registered the way storing one does: the bytes are not the
  -- point here, and the row is a projection of state like any other.
  discard <| ctx.commit "test" [.registerBlob
    { sha256 := sha, mime := "application/pdf", bytes := 1, origName := none,
      createdAt := "2026-08-06T00:00:00" }]
  Receipts.record ctx sha
    { merchant := some "Bächlitalhütte SAC", date := Date.ofIso? "2026-08-06"
      total := some ⟨chf, 64200⟩
      items := [{ description := "Haslikuchen", qty := some 2, amount := ⟨chf, 1200⟩ },
                { description := "Panaché 0,5", qty := some 1, amount := ⟨chf, 700⟩ },
                { description := "Hüttewurst mit Brot", qty := some 1, amount := ⟨chf, 900⟩ }]
      extractor := "test" }
  let stored ← Receipts.items ctx sha
  r := checkEq r "the lines come back in order" (stored.map (·.amount.minor)) #[1200, 700, 900]
  r := checkEq r "the count survives the round trip" ((stored[0]?).bind (·.qty)) (some 2)
  let id ← freshId
  let fixture : Transaction :=
    { id := ⟨id⟩, date := (Date.ofIso? "2026-08-06").get!
      payee := some "Bächlitalhütte SAC", narration := "cash receipt"
      postings := [{ account := cash.id, amount := ⟨chf, -64200⟩ },
                   { account := rest.id, amount := ⟨chf, 64200⟩ }]
      attachments := [sha] }
  match fixture.validate with
  | .error e => return check r s!"the fixture balances ({e})" false
  | .ok bt => Txns.put ctx bt "test" "fixture"
  let parts ← Receipts.divideByItems ctx ⟨id⟩
    [{ items := [{ line := 1 }, { line := 3 }], into := "Expenses.Hut.Food" }] "test"
  r := checkEq r "a claimed group and a remainder come back" parts.size 2
  let food ← Accounts.ensure ctx "Expenses.Hut.Food" (kind := some .expense)
  let netIn (t : Transaction) (a : AccountId) : Int := t.netIn a "CHF"
  r := checkEq r "the group is worth exactly the lines it claimed"
    ((parts[0]?).map (fun t => netIn t food.id)) (some 2100)
  r := checkEq r "the group takes its share from the account the money left"
    ((parts[0]?).map (fun t => netIn t cash.id)) (some (-2100))
  r := checkEq r "the remainder keeps what no line claimed"
    ((parts[1]?).map (fun t => netIn t rest.id)) (some 62100)
  r := checkEq r "dividing takes the same money out in total"
    ((parts.map (fun t => netIn t cash.id)).foldl (· + ·) 0) (-64200)
  r := check r "the receipt rides along on every part"
    (parts.all (fun t => t.attachments == [sha]))
  -- The page is one page and each part is only some of it, so each says which
  -- lines it paid for rather than repeating the whole bill.
  r := checkEq r "a part lists the lines it claimed and no others"
    ((parts[0]?).bind (·.items) |>.map (fun its => its.map (·.description)))
    (some ["Haslikuchen", "Hüttewurst mit Brot"])
  r := checkEq r "a part's lines come to what the part books"
    ((parts[0]?).bind (·.items) |>.map (fun its => (its.map (·.amount.minor)).sum))
    (some 2100)
  r := checkEq r "the remainder lists only what the parts left"
    ((parts[1]?).bind (·.items) |>.map (fun its => its.map (·.description)))
    (some ["Panaché 0,5"])
  r := checkEq r "a whole line is kept as the till printed it"
    ((parts[0]?).bind (·.items) |>.bind (fun its => (its[0]?).bind (·.qty))) (some 2)
  r := check r "the payment it was divided from is gone"
    ((← Txns.get? ctx ⟨id⟩)).isNone
  -- Read the parts back rather than trusting what came out of the call: a part
  -- that is returned but never lands leaves the money it was carrying nowhere,
  -- and the returned value looks perfectly correct either way.
  let mut landed := 0
  for part in parts do
    if (← Txns.get? ctx part.id).isSome then landed := landed + 1
  r := checkEq r "every part is in the store afterwards" landed parts.size
  let cashAfter ← Db.scalarInt ctx.db
    s!"SELECT COALESCE(SUM(minor), 0) FROM posting
       WHERE account_id = {Db.lit cash.id.val} AND commodity = 'CHF'"
  r := checkEq r "dividing leaves the account the money left untouched" cashAfter (-64200)
  -- The two ways of asking for the impossible.
  let twice ← try
    let _ ← Receipts.divideByItems ctx (parts[0]!).id
      [{ items := [{ line := 1 }, { line := 1 }], into := "Expenses.Hut.Food" }] "test"
    pure false
  catch _ => pure true
  r := check r "a single-unit line cannot be claimed twice" twice
  -- The part took lines 1 and 3 of the receipt and holds two lines of its own,
  -- so dividing it again is a division of those two: the third line is the
  -- remainder's, and offering it here would book the same money twice.
  let beyond ← try
    let _ ← Receipts.divideByItems ctx (parts[0]!).id
      [{ items := [{ line := 3 }], into := "Expenses.Hut.Food" }] "test"
    pure false
  catch _ => pure true
  r := check r "a part cannot be divided by a line that went to its sibling" beyond
  let again ← Receipts.divideByItems ctx (parts[0]!).id
    [{ items := [{ line := 2 }], into := "Expenses.Hut.Beer" }] "test"
  let beer ← Accounts.ensure ctx "Expenses.Hut.Beer" (kind := some .expense)
  r := checkEq r "dividing a part again divides its own lines"
    ((again[0]?).map (fun t => netIn t beer.id)) (some 900)
  r := checkEq r "what that part is left with is its other line"
    ((again[1]?).bind (·.items) |>.map (fun its => its.map (·.description)))
    (some ["Haslikuchen"])
  -- ...and it is called that, rather than keeping a list its sibling has since
  -- taken half of.
  r := checkEq r "the remainder of a part is named by the lines it keeps"
    ((again[1]?).map (·.narration)) (some "Haslikuchen")
  r := checkEq r "the remainder of a payment keeps the payment's own words"
    ((parts[1]?).map (·.narration)) (some "cash receipt")
  let tooMuch ← try
    let _ ← Receipts.divideByItems ctx (parts[1]!).id
      [{ items := [{ line := 9 }], into := "Expenses.Hut.Food" }] "test"
    pure false
  catch _ => pure true
  r := check r "a line that is not on the receipt is refused" tooMuch
  -- Editing the lines by hand, for the ones a scan could not read. The lines
  -- may fall short of the total, but never overrun it.
  r := checkEq r "headroom is what the lines leave of the total"
    ((← Receipts.headroom ctx sha).map (·.minor)) (some 61400)
  let _ ← Receipts.addItem ctx sha "Suppe" (some 1) "9.50"
  r := checkEq r "an added line takes up headroom"
    ((← Receipts.headroom ctx sha).map (·.minor)) (some 60450)
  let overrun ← try
    let _ ← Receipts.addItem ctx sha "Zu teuer" none "9999.00"
    pure false
  catch _ => pure true
  r := check r "a line that would overrun the total is refused" overrun
  r := checkEq r "the refused line was not stored" (← Receipts.items ctx sha).size 4
  let _ ← Receipts.removeItem ctx sha 2
  let after ← Receipts.items ctx sha
  r := checkEq r "removing a line renumbers the rest"
    ((after[1]?).map (·.description)) (some "Hüttewurst mit Brot")
  r := checkEq r "removing a line gives its money back to the headroom"
    ((← Receipts.headroom ctx sha).map (·.minor)) (some 61150)
  let gone ← try
    let _ ← Receipts.removeItem ctx sha 99
    pure false
  catch _ => pure true
  r := check r "removing a line that is not there is refused" gone

  -- A line covering several units is divisible too: eighteen half-boards on one
  -- printed line may belong to several people. The awkward case is a line whose
  -- total does not divide evenly, where the units must still add back exactly.
  let sha2 := "00beef0000beef0000beef0000beef0000beef0000beef0000beef0000beef00"
  let bunk ← Accounts.ensure ctx "Assets.Cash.Bunk" (kind := some .asset)
  let pot ← Accounts.ensure ctx "Expenses.Bunk.Unclassified" (kind := some .expense)
  discard <| ctx.commit "test" [.registerBlob
    { sha256 := sha2, mime := "application/pdf", bytes := 1, origName := none,
      createdAt := "2026-08-01T00:00:00" }]
  Receipts.record ctx sha2
    { total := some ⟨chf, 132400⟩
      items := [{ description := "FORFAIT 1/2 PENSION", qty := some 18, amount := ⟨chf, 122400⟩ },
                { description := "TAXE DE SEJOUR", qty := some 3, amount := ⟨chf, 10000⟩ }]
      extractor := "test" }
  let id2 ← freshId
  let fixture2 : Transaction :=
    { id := ⟨id2⟩, date := (Date.ofIso? "2026-08-01").get!
      payee := some "Cabane", narration := "hut bill"
      postings := [{ account := bunk.id, amount := ⟨chf, -132400⟩ },
                   { account := pot.id, amount := ⟨chf, 132400⟩ }]
      attachments := [sha2] }
  match fixture2.validate with
  | .error e => return check r s!"the second fixture balances ({e})" false
  | .ok bt => Txns.put ctx bt "test" "fixture"
  let split ← Receipts.divideByItems ctx ⟨id2⟩
    [{ items := [{ line := 1, qty := some 10 }, { line := 2, qty := some 1 }]
       into := "Expenses.Bunk.Mine" },
     { items := [{ line := 1, qty := some 8 }, { line := 2, qty := some 2 }]
       into := "Expenses.Bunk.Theirs" }] "test"
  let mine ← Accounts.ensure ctx "Expenses.Bunk.Mine" (kind := some .expense)
  let theirs ← Accounts.ensure ctx "Expenses.Bunk.Theirs" (kind := some .expense)
  let net (t : Transaction) (a : AccountId) : Int := t.netIn a "CHF"
  -- 10 of 18 nights at 68.00, plus a third of a 100.00 tax that does not divide
  -- evenly. `splitParts` puts the odd cent on the last unit, so one third is
  -- 33.33 and the other two are 33.33 + 33.34: 680.00 + 33.33 here.
  r := checkEq r "ten units of a line, plus a share of one that divides unevenly"
    ((split[0]?).map (fun t => net t mine.id)) (some 71333)
  r := checkEq r "the other eight units, and the odd cent with them"
    ((split[1]?).map (fun t => net t theirs.id)) (some 61067)
  r := checkEq r "the units of a line add back to the line"
    (((split[0]?).map (fun t => net t mine.id)).getD 0 +
     ((split[1]?).map (fun t => net t theirs.id)).getD 0) 132400
  r := checkEq r "claiming every unit leaves no remainder" split.size 2
  r := checkEq r "the narration says how many units it took"
    ((split[0]?).map (·.narration)) (some "10 × FORFAIT 1/2 PENSION, 1 × TAXE DE SEJOUR")
  -- A line taken in part is listed as the units taken, priced at what they cost,
  -- so the lines of a part still add up to the part.
  r := checkEq r "a part of a line is listed as the units it took"
    ((split[0]?).bind (·.items) |>.map (fun its => its.map (fun i => (i.qty, i.amount.minor))))
    (some [(some 10, 68000), (some 1, 3333)])
  r := checkEq r "the other part is listed as the units it was left"
    ((split[1]?).bind (·.items) |>.map (fun its => its.map (fun i => (i.qty, i.amount.minor))))
    (some [(some 8, 54400), (some 2, 6667)])
  let overclaim ← try
    let _ ← Receipts.divideByItems ctx (split[0]!).id
      [{ items := [{ line := 1, qty := some 99 }], into := "Expenses.Bunk.Mine" }] "test"
    pure false
  catch _ => pure true
  r := check r "claiming more units than a line covers is refused" overclaim
  return r

/--
Sharing a budget, and the people in it saying which costs were theirs.

Three properties. A budget moved into a realm of its own leaves your books
saying exactly what they said before -- the payment is untouched and the mirror
holds what it bought, so nothing is created or destroyed by moving it. A cost
somebody takes is borne by whoever took it, split equally when several do. And
what nobody takes is divided by the weights, which is what a budget did before
anybody could take anything.
-/
private def sharedBudgetTests (ctx : Ctx) (r : Report) : IO Report := do
  let mut r := r
  let eur := Commodity.eur
  let cash ← Accounts.ensure ctx "Assets.Cash.Trip" (kind := some .asset)
  let spent ← Accounts.ensure ctx "Expenses.Trip.Things" (kind := some .expense)
  -- Three costs, paid by you, lent into a pot.
  let mut ids : Array TxId := #[]
  for (what, minor) in [("hut", 6420), ("taxi", 3000), ("breakfast", 1200)] do
    let id ← freshId
    let t : Transaction :=
      { id := ⟨id⟩, date := (Date.ofIso? "2026-08-06").get!, payee := some what
        narration := what
        postings := [{ account := cash.id, amount := ⟨eur, -minor⟩ },
                     { account := spent.id, amount := ⟨eur, minor⟩ }] }
    match t.validate with
    | .error e => return check r s!"the {what} fixture balances ({e})" false
    | .ok bt => Txns.put ctx bt "test" "fixture"
    ids := ids.push ⟨id⟩
  let b ← Budgets.open ctx "Trip" "test"
  discard <| Budgets.lend ctx b ids "test"
  let worthBefore ← Balances.netWorth ctx "EUR"
  -- Into a realm of its own, with a purse there to fund it from.
  let realm : RealmId := ⟨← freshId⟩
  let bridge : Account :=
    { id := ⟨← freshId⟩, name := "Assets.Purse.me.Trip", kind := .asset, realm
      bridgeOf := some ctx.member }
  discard <| ctx.commit "test"
    [.addMember { id := ctx.member, name := "me", party := Party.selfId },
     .createRealm { id := realm, name := "Shared.Trip", members := [(ctx.member, .admin)] },
     .grant realm ctx.member .admin bridge] "realm" (fun _ => none) realm
  let (shared, moved) ← Budgets.shareInto ctx b realm bridge "test"
  r := checkEq r "every cost moved into the shared realm" moved 3
  r := checkEq r "and the pot there holds what they came to"
    ((← Budgets.balance ctx shared eur).minor) 10620
  r := checkEq r "moving a budget leaves your net worth exactly where it was"
    (← Balances.netWorth ctx "EUR") worthBefore
  let st ← ctx.state.get
  let some mirror := (sortedValues st.accounts).find? (fun a => a.mirrorOf == some bridge.id)
    | return check r "a mirror account was written" false
  r := checkEq r "the mirror holds what the payments bought"
    (st.txnsSorted.foldl (fun n t => n + t.netIn mirror.id "EUR") 0) 10620
  r := checkEq r "and the bridge holds the same, the other way about"
    (st.txnsSorted.foldl (fun n t => n + t.netIn bridge.id "EUR") 0) (-10620)
  -- What was a cost of the old budget is a cost of the shared one now.
  let costs := (Budget.remaining shared st eur).map (fun (t, _) => t.narration)
  r := checkEq r "the shared budget holds the three costs" costs.length 3
  let some taxi := (Budget.remaining shared st eur).find? (fun (t, _) => t.narration == "taxi")
    | return check r "the taxi is in the shared budget" false
  -- Taking one, giving it back, taking it again.
  let took ← Budgets.claimCost ctx shared taxi.1.id "test"
  r := checkEq r "taking a cost records who took it" took.claims.length 1
  let twice ← try
    let _ ← Budgets.claimCost ctx shared taxi.1.id "test"
    pure false
  catch _ => pure true
  r := check r "the same person cannot take one twice" twice
  let gave ← Budgets.releaseCost ctx shared taxi.1.id ctx.member "test"
  r := checkEq r "giving it back takes it off the list" gave.claims.length 0
  let back ← Budgets.claimCost ctx shared taxi.1.id "test"
  r := checkEq r "and it can be taken again" back.claims.length 1
  let notACost ← try
    let _ ← Budgets.claimCost ctx shared (ids[0]!) "test"
    pure false
  catch _ => pure true
  r := check r "a transaction that is not a cost of the budget is refused" notACost
  -- Closing: the taxi is yours alone, the rest divides between the two of you.
  let anna ← Parties.ensure ctx "Anna" "contact"
  let annaPurse ← Accounts.ensure ctx "Assets.Purse.Anna" (kind := some .asset)
    (owner := some anna.id) (realm := realm)
  let among : List Participant :=
    [{ owner := Party.selfId, name := "me", account := "Expenses.Trip.Mine" },
     { owner := anna.id, name := "Anna", account := annaPurse.name }]
  discard <| Budgets.close ctx shared "test" eur (some among)
  let after ← ctx.state.get
  -- 106.20 in all, of which the taxi's 30.00 is yours alone because you took it;
  -- the 76.20 nobody took halves, so Anna bears 38.10 and owes it.
  let standings ← Budgets.standings ctx shared eur
  r := checkEq r "what nobody took divides by the weights"
    ((standings.find? (·.name == "Anna")).map (·.amount.minor)) (some 3810)
  r := checkEq r "and you bear the rest: your half, and all of what you took"
    ((standings.find? (·.name == "me")).map (·.amount.minor)) (some (-3810))
  r := checkEq r "a cost somebody took leaves the pot entirely"
    (Budget.remaining shared after eur).length 0
  return r

/--
The workflow, end to end: lend costs into a budget, let somebody else pay for
part of it, divide it, write the claims up as invoices, and let the money
arrive.

Three properties matter. Net worth must state something true at every step, not
only at the end — which is what makes the budget account equity rather than an
asset, and what makes an owner rather than a kind decide whose money is whose.
Your own share must survive as a real expense in an account you chose. And
deciding whose the spending was must not depend on anybody having paid.
-/
private def workflowTests (ctx : Ctx) (r : Report) : IO Report := do
  let eur := Commodity.eur
  let giro ← Accounts.ensure ctx "Assets.Bank.Flow" (kind := some .asset)
  let holding ← Accounts.ensure ctx "Expenses.Flow.Unsorted"
  let mut r := r
  let worth : IO Int := Balances.netWorth ctx
  -- Captured before the costs exist, so every step below can be stated against
  -- what you were worth before the weekend.
  let before ← worth
  -- 10001 is deliberately awkward: it does not divide by three.
  for (id, amount) in [("flow-1", 6000), ("flow-2", 4001)] do
    let t : Transaction :=
      { id := ⟨id⟩, date := (Date.ofIso? "2026-07-07").getD default, payee := some "Hut"
        narration := "beds"
        postings := [{ account := giro.id, amount := ⟨eur, -amount⟩ },
                     { account := holding.id, amount := ⟨eur, amount⟩ }] }
    match t.validate with
    | .error _ => r := check r "workflow fixture balances" false
    | .ok bt => Txns.put ctx bt "test"

  r := checkEq r "paying for it costs you the whole amount, for now"
    (← worth) (before - 10001)

  -- 1. lend: rewrites the costs in place, so no entry is invented
  let budget ← Budgets.open ctx "Flow"
  let txnsBefore ← Db.scalarInt ctx.db "SELECT COUNT(*) FROM txn"
  discard <| Budgets.lend ctx budget #[⟨"flow-1"⟩, ⟨"flow-2"⟩] "test"
  r := checkEq r "lending adds no transaction"
    (← Db.scalarInt ctx.db "SELECT COUNT(*) FROM txn") txnsBefore
  r := checkEq r "the budget holds everything undivided" (← Budgets.balance ctx budget).minor 10001
  -- Lending is a reclassification, not a movement: the money already left.
  r := checkEq r "lending moves nothing" (← worth) (before - 10001)

  -- 2. somebody else pays for part of it, out of an account of their own
  let anna ← Parties.contact ctx "annaF"
  let ben ← Parties.contact ctx "benF"
  let annaPurse ← Accounts.purse ctx anna
  discard <| Budgets.contribute ctx budget annaPurse ⟨eur, 3000⟩
    ((Date.ofIso? "2026-07-08").getD default) "the taxi" "test" (some "Taxi")
  r := checkEq r "their money fills the budget too" (← Budgets.balance ctx budget).minor 13001
  -- Her outlay is not yours to keep: until the budget is divided, every cent of
  -- it is money you owe her, and her own account is what says so.
  r := checkEq r "what she fronted is money you owe her" (← worth) (before - 13001)

  -- 3. allocate: one entry, one share each, yours to an expense you name
  let mine := "Expenses.Flow.MyShare"
  let some (alloc, raised) ← Budgets.allocate ctx budget
      [← person ctx "annaF" "", ← person ctx "benF" "", ← person ctx "" mine] "test" eur
    | return (check r "allocation happens" false)
  let budgetAcc ← Budgets.account ctx budget
  r := check r "the budget's own legs are tagged as a reclassification"
    ((alloc.postings.filter fun p => p.account == budgetAcc.id).all
      fun p => p.tag == some "allocation")
  r := checkEq r "the budget is empty once divided" (← Budgets.balance ctx budget).minor 0
  let standings ← Budgets.standings ctx budget
  r := checkEq r "one position per participant" standings.size 3
  r := checkEq r "and they sum to nothing, because the budget holds nothing"
    (Settle.total (standings.toList.map Standing.position)) 0
  let mineAcc ← Accounts.ensure ctx mine
  r := checkEq r "your share is a real expense in the account you chose"
    (← Db.scalarInt ctx.db
      s!"SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = {Db.lit mineAcc.id.val}")
    4334
  -- Nothing was consumed by allocating, so net worth only moves by your share —
  -- and what she put in above her own share is now money you owe her.
  r := checkEq r "net worth is down by your share alone" (← worth) (before - 4334)
  -- Her contribution is netted against her share by the ledger, with nothing
  -- doing the netting: her own account carries both.
  match standings.find? (·.owner == anna.id) with
  | none => r := check r "she has a position" false
  | some st =>
    r := checkEq r "what she put in is set against what she bears"
      st.amount.minor ((4333 : Int) - 3000)

  -- 4. the claims that would square it, checked before any of them is written
  r := checkEq r "one claim per person who is not square" raised.size 2
  r := check r "and every one of them is a transaction that has not happened"
    (raised.all fun t => t.state == .pending)
  r := checkEq r "claims reach no balance at all" (← worth) (before - 4334)
  r := checkEq r "the budget is untouched by them" (← Budgets.balance ctx budget).minor 0
  let plan := (← Budgets.claims ctx budget).filterMap
    (Pendings.transferOf (← Accounts.list ctx))
  r := check r "the plan settles every position"
    (decide (Settle.Settles (standings.toList.map Standing.position) plan.toList))
  r := check r "and it is no longer than one transfer per person"
    (plan.size + 1 ≤ standings.size + 1)
  -- Settling again asks for nothing more: what has already been asked for is
  -- netted off before anything new is raised.
  r := checkEq r "settling twice raises nothing" (← Budgets.settle ctx budget "test").size 0

  -- 5. invoices: documents about claims addressed to you. They move no money.
  let some divided ← Budgets.get? ctx "Flow" | return (check r "the budget reads back" false)
  let issued ← Invoices.forBudget ctx divided (.link "https://example.org")
    ((Date.ofIso? "2026-07-10").getD default) ((Date.ofIso? "2026-08-01").getD default) eur
  r := checkEq r "one invoice per claim you are owed" issued.size 2
  r := checkEq r "raising invoices moves no money" (← worth) (before - 4334)
  r := check r "and none of them is addressed to you"
    (issued.all fun i => i.payerName != "me")
  r := check r "each goes to exactly one person"
    (((issued.map (·.payerName)).toList.eraseDups).length == 2)
  r := check r "and each points at the claim it is asking to have met"
    (issued.all fun i => i.pendingTxn.isSome)
  let again ← Invoices.forBudget ctx divided (.link "https://example.org")
    ((Date.ofIso? "2026-07-10").getD default) ((Date.ofIso? "2026-08-01").getD default) eur
  r := checkEq r "a claim is only ever invoiced once" again.size 0

  -- 6. the money arrives, and it meets a *named* claim rather than the oldest
  -- thing outstanding.
  let bensPurse ← Accounts.purse ctx ben
  let some bensClaim := raised.find? fun t =>
    (Pendings.payer? t).map (fun a => a == bensPurse.id) |>.getD false
    | return (check r "there is a claim against him" false)
  let owed := (Pendings.amount bensClaim).minor
  let part := owed - 500
  let paid : Transaction :=
    { id := ⟨"flow-pay"⟩, date := (Date.ofIso? "2026-07-20").getD default
      payee := some "benF", narration := "most of my share"
      postings := [{ account := giro.id, amount := ⟨eur, part⟩ },
                   { account := (← Accounts.ensure ctx "Income.Flow.Unsorted").id,
                     amount := ⟨eur, -part⟩ }] }
  match paid.validate with
  | .error _ => r := check r "settlement fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  let after ← Pendings.resolve ctx bensClaim.id ⟨"flow-pay"⟩ "test"
  r := check r "a part payment leaves the claim open" (after.state == .pending)
  r := checkEq r "and what is left of it is the difference, not a guess"
    (Pendings.amount after).minor 500
  r := checkEq r "the money landed against him and nobody else"
    (← Db.scalarInt ctx.db
      s!"SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = {Db.lit bensPurse.id.val}")
    500
  -- Being paid what you were already owed changes nothing: the claim was
  -- already part of what you are worth, and now it is cash instead.
  r := checkEq r "being paid what you were owed leaves you no better off"
    (← worth) (before - 4334)
  r := checkEq r "and the part that was met is a record of its own"
    ((← Budgets.claims ctx budget).filter (fun t => t.state == .settled)).size 1

  -- A late receipt: lent into the same budget, and dividing again must divide
  -- only the new cost. The old one has already been decided.
  let late : Transaction :=
    { id := ⟨"flow-late"⟩, date := (Date.ofIso? "2026-07-09").getD default
      payee := some "Hut", narration := "the receipt that turned up later"
      postings := [{ account := giro.id, amount := ⟨eur, -3000⟩ },
                   { account := holding.id, amount := ⟨eur, 3000⟩ }] }
  match late.validate with
  | .error _ => r := check r "late fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  discard <| Budgets.lend ctx budget #[⟨"flow-late"⟩] "test"
  r := checkEq r "only the late cost is undivided"
    (((← Budgets.remaining ctx budget eur).map (fun (_, n) => n)).foldl (· + ·) 0) (3000 : Int)
  let some (_, more) ← Budgets.allocate ctx budget
      [← person ctx "annaF" "", ← person ctx "" mine] "test" eur
    | return (check r "the second allocation happens" false)
  r := checkEq r "and the budget is empty again" (← Budgets.balance ctx budget).minor 0
  r := check r "the new claims only ask for what the second division added"
    ((more.map (fun t => (Pendings.amount t).minor)).foldl (· + ·) 0 ≤ 3000)
  let stillOwed ← Budgets.standings ctx budget
  r := checkEq r "and everybody still nets to nothing"
    (Settle.total (stillOwed.toList.map Standing.position)) 0

  -- Voiding a claim writes off the money without re-attributing the spending:
  -- somebody consumed it, and not paying does not make it yours.
  let expenseBefore ← Db.scalarInt ctx.db
    s!"SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = {Db.lit mineAcc.id.val}"
  discard <| Pendings.void ctx after.id "test"
  r := checkEq r "writing off a claim leaves your own expenses alone"
    (← Db.scalarInt ctx.db
      s!"SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = {Db.lit mineAcc.id.val}")
    expenseBefore

  -- A budget nobody else shares: one participant, no share of yours, and the
  -- whole cost becomes theirs.
  let solo ← Budgets.open ctx "Solo"
  let t : Transaction :=
    { id := ⟨"solo-1"⟩, date := (Date.ofIso? "2026-07-07").getD default, payee := some "DAV"
      narration := "club"
      postings := [{ account := giro.id, amount := ⟨eur, -9000⟩ },
                   { account := holding.id, amount := ⟨eur, 9000⟩ }] }
  match t.validate with
  | .error _ => r := check r "solo fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  discard <| Budgets.lend ctx solo #[⟨"solo-1"⟩] "test"
  discard <| Budgets.allocate ctx solo [← person ctx "DAV" ""] "test" eur
  let davPurse ← Accounts.purse ctx (← Parties.contact ctx "DAV")
  r := checkEq r "bearing none of it makes the whole cost theirs"
    (← Db.scalarInt ctx.db
      s!"SELECT IFNULL(SUM(minor), 0) FROM posting WHERE account_id = {Db.lit davPurse.id.val}")
    9000

  let eur := Commodity.eur
  -- Deleting a draft winds the number back, so the sequence has no hole in it.
  let year := 2026
  -- The counter is keyed by realm: one sequence for the whole ledger meant an
  -- admin of any realm a reader could open moved the ledger owner's numbering.
  let counterName := s!"{Realm.selfId.val}:invoice:{year}"
  let before ← Db.scalarInt ctx.db
    s!"SELECT value FROM counter WHERE name = {Db.lit counterName}"
  let scratch ← Invoices.create ctx "typo" [{ description := "x", qtyMilli := 1000, unitPrice := ⟨eur, 100⟩ }]
    (.link "https://example.org") ((Date.ofIso? "2026-07-10").getD default)
    ((Date.ofIso? "2026-08-01").getD default) eur
  Invoices.delete ctx scratch.id
  let after ← Db.scalarInt ctx.db
    s!"SELECT value FROM counter WHERE name = {Db.lit counterName}"
  r := checkEq r "deleting a draft leaves no gap in the numbering" after before
  r := check r "and the invoice itself is gone" (← Invoices.get? ctx scratch.number).isNone
  -- Only the newest may be wound back; an older hole would renumber a live one.
  let keep ← Invoices.create ctx "kept" [{ description := "y", qtyMilli := 1000, unitPrice := ⟨eur, 100⟩ }]
    (.link "https://example.org") ((Date.ofIso? "2026-07-10").getD default)
    ((Date.ofIso? "2026-08-01").getD default) eur
  let newer ← Invoices.create ctx "newer" [{ description := "z", qtyMilli := 1000, unitPrice := ⟨eur, 100⟩ }]
    (.link "https://example.org") ((Date.ofIso? "2026-07-10").getD default)
    ((Date.ofIso? "2026-08-01").getD default) eur
  Invoices.delete ctx keep.id
  r := checkEq r "removing an older draft does not renumber the counter"
    (← Db.scalarInt ctx.db s!"SELECT value FROM counter WHERE name = {Db.lit counterName}")
    ((newer.number.splitOn "-")[1]!.toNat!)
  return r

/-- Contacts are read from an address book, never stored here. -/
private def contactTests (ctx : Ctx) (r : Report) : IO Report := do
  let mut r := r
  -- Detection prefers the desktop contact store, and says so; on a machine
  -- without one it reports that rather than failing.
  let detected ← Contacts.source ctx
  let described := Contacts.describe detected
  r := check r "a source is either found or honestly absent"
    (described == "none found" || Str.containsCI described "desktop")
  -- A chosen source is recorded rather than hand-written, and read back.
  Contacts.saveSource ctx (.files "/nonexistent")
  match ← Contacts.source ctx with
  | .files p => r := checkEq r "the chosen source round-trips" p "/nonexistent"
  | _ => r := check r "the chosen source round-trips" false
  -- A directory of vCards, the shape vdirsyncer and khard keep.
  let book := ctx.cfg.dataDir / "addressbook"
  IO.FS.createDirAll book
  IO.FS.writeFile (book / "anna.vcf")
    "BEGIN:VCARD\nVERSION:3.0\nFN:Anna Beispiel\nEMAIL:anna@example.org\n\
     X-IBAN:DE02 1203 0000 0000 2020 51\nEND:VCARD\n"
  IO.FS.writeFile (book / "marius.vcf")
    "BEGIN:VCARD\nN:Klein;Marius;;;\nEMAIL:m@example.org\nEND:VCARD\n"
  Contacts.saveSource ctx (.files book.toString)
  let people ← Contacts.all ctx
  r := checkEq r "both cards are read" people.size 2
  match ← Contacts.byName? ctx "Anna Beispiel" with
  | none => r := check r "a contact is found by name" false
  | some c =>
    r := checkEq r "with her email" c.email (some "anna@example.org")
    r := checkEq r "and spaces stripped from the IBAN" c.iban (some "DE02120300000000202051")
  r := check r "a card without FN falls back to N"
    (people.any fun c => c.name == "Marius Klein")
  -- Nothing was written into the ledger's own tables.
  r := check r "reading contacts does not create parties"
    ((← Parties.byName? ctx "Anna Beispiel").isNone)
  return r

/-! ## The pure core -/

/-- The day the core fixtures happen on. Nothing in `Core` knows today's date. -/
private def coreDate : Date := (Date.ofIso? "2026-03-01").getD default

/-- An account for the core fixtures. -/
private def coreAccount (id name : String) (kind : AccountKind)
    (owner : PartyId := Party.selfId) : Account :=
  { id := ⟨id⟩, name, kind, owner }

/-- A euro posting, by account id. -/
private def cents (acc : String) (minor : Int) : Posting :=
  { account := ⟨acc⟩, amount := ⟨Commodity.eur, minor⟩ }

/-- A dated transaction for the core fixtures. -/
private def coreTxn (id : String) (postings : List Posting)
    (narration : String := "dinner") : Transaction :=
  { id := ⟨id⟩, date := coreDate, narration, postings }

/-- One event by the self member, one part per operation, all in the self realm. -/
private def coreEvent (id : String) (ops : List Op) : Event :=
  { id, author := Member.selfId, composedAt := "2026-03-01T00:00:00Z"
    parts := ops.map (fun op => { realm := Realm.selfId, op }) }

/-- Applies an operation as the self member, or leaves the state alone if it fails. -/
private def coreStep (s : State) (op : Op) : State :=
  match applyOp s Member.selfId Realm.selfId op with
  | .ok (s', _) => s'
  | .error _ => s

/-- What an operation refused with, or the empty string when it went through. -/
private def coreError (s : State) (op : Op) : String :=
  match applyOp s Member.selfId Realm.selfId op with
  | .ok _ => ""
  | .error e => e

/-- The same, for an operation written by somebody else, in a realm of its own. -/
private def coreErrorAs (who : String) (realm : RealmId) (s : State) (op : Op) : String :=
  match applyOp s ⟨who⟩ realm op with
  | .ok _ => ""
  | .error e => e

/-- Whether an operation written by somebody else, in a realm of its own, was taken. -/
private def coreAllows (who : String) (realm : RealmId) (s : State) (op : Op) : Bool :=
  (applyOp s ⟨who⟩ realm op).toOption.isSome

/-- The accounts every core test starts from. -/
private def coreBase : State := Id.run do
  let ops : List Op :=
    [ .putAccount (coreAccount "acc-bank" "Assets.Bank" .asset)
    , .putAccount (coreAccount "acc-food" "Expenses.Food" .expense)
    , .putAccount (coreAccount "acc-unc" "Income.Unclassified" .income)
    , .putAccount (coreAccount "acc-anna" "Assets.Purse.Anna" .asset ⟨"party-anna"⟩)
    , .putAccount (coreAccount "acc-bob" "Assets.Purse.Bob" .asset ⟨"party-bob"⟩)
    , .putAccount { coreAccount "acc-old" "Assets.Shoebox" .asset with closedOn := some coreDate } ]
  let mut s := State.init
  for op in ops do
    s := coreStep s op
  return s

/-! ## Budgets and invoices in the pure core -/

/-- The budget the fixtures divide. Opened as `Hut`, which makes `Budget.Hut`. -/
private def coreHut : Budget := { id := ⟨"b-hut"⟩, name := "Hut", note := none, closed := false }

/-- Who the hut is shared between: you and Anna, equally. -/
private def coreAmong : List Participant :=
  [ { owner := Party.selfId, name := "me", account := "Expenses.Food" }
  , { owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna" } ]

/-- Applies a list of operations in order, skipping any that fails. -/
private def coreSteps (s : State) (ops : List Op) : State := ops.foldl coreStep s

/-- A cost somebody paid for, straight into the budget. -/
private def coreCost (id from_ : String) (minor : Int) (narration : String) : Transaction :=
  coreTxn id [cents from_ (-minor), cents "acc-hut" minor] narration

/-- The budget as the state has it, so its name is the one it was opened under. -/
private def coreBudget (s : State) : Budget :=
  ((s.budget? ⟨"b-hut"⟩).map (·.budget)).getD coreHut

/-- The ledger with people, a label and an open budget: what the budget tests start from. -/
private def coreOpened : State :=
  coreSteps coreBase
    [ .putParty { id := Party.selfId, name := "me", kind := "self" }
    , .putParty { id := ⟨"party-anna"⟩, name := "Anna", kind := "contact" }
    , .putParty { id := ⟨"party-bob"⟩, name := "Bob", kind := "contact" }
    , .putLabel { id := ⟨"lbl-hut"⟩, name := "budget:Hut" }
    , .openBudget coreHut (coreAccount "acc-hut" "Hut" .expense)
    , .setParticipants ⟨"b-hut"⟩ coreAmong ]

/-- Two costs, hers and yours, divided between the two of you. -/
private def coreDivided : State :=
  coreSteps coreOpened
    [ .contribute ⟨"b-hut"⟩ (coreCost "t-hut1" "acc-bank" 10000 "the hut")
    , .contribute ⟨"b-hut"⟩ (coreCost "t-hut2" "acc-anna" 6000 "groceries")
    , .allocate ⟨"b-hut"⟩ coreAmong Commodity.eur coreDate none ⟨"t-alloc1"⟩
        [⟨"t-claim1"⟩] ⟨"lbl-hut"⟩ ]

/-- A receipt that turns up afterwards, and a claim from a plan that is out of date. -/
private def coreLate : State :=
  coreSteps coreDivided
    [ .raiseClaim { id := ⟨"t-claim-bob"⟩, date := coreDate, narration := "an older plan"
                    state := .pending, labels := [⟨"lbl-hut"⟩]
                    postings := [cents "acc-bank" 1500, cents "acc-bob" (-1500)] }
    , .contribute ⟨"b-hut"⟩ (coreCost "t-hut3" "acc-bank" 2000 "a late ticket") ]

/-- The late receipt, divided. -/
private def coreToppedUp : State :=
  coreStep coreLate (.allocate ⟨"b-hut"⟩ coreAmong Commodity.eur coreDate none ⟨"t-alloc2"⟩
    [⟨"t-claim2"⟩] ⟨"lbl-hut"⟩)

/-- An invoice to Anna, as it arrives at `issueInvoice`: unnumbered and unreferenced. -/
private def coreDraft (id : String) : Invoice :=
  { id := ⟨id⟩, number := "", issued := coreDate, due := coreDate
    payerId := some ⟨"party-anna"⟩, payerName := "Anna", commodity := Commodity.eur
    reference := "", status := .draft, note := none, settledTxn := none
    payment := .link "https://example.org/pay", sourceAccount := none, budgetId := none
    pendingTxn := none
    lines := [{ description := "her share", qtyMilli := 1000
                unitPrice := ⟨Commodity.eur, 5000⟩ }] }

/--
Dividing a budget, squaring it up, and writing the result down.

The arithmetic is `Core/Budgets.lean` and the writing is `applyOp`; what is
checked here is that the two together do what the store used to do in SQL —
including the awkward parts: a second division tops up rather than dividing
twice, a claim between the same two people is revised rather than duplicated,
and a number that is deleted is handed out again.
-/
private def coreBudgetTests (r : Report) : Report := Id.run do
  let mut r := r
  let eur := Commodity.eur
  -- Which realm a budget was made for is read off the budget's own realm and the
  -- account it holds inside it. Asked by name across the ledger, an equity
  -- account of that name in a realm of somebody else's — the first of the name
  -- in id order — answered for the budget instead, and named that realm as the
  -- one the budget was made for.
  let squatted : State :=
    { coreOpened with
      realms := coreOpened.realms.insert "r-elsewhere"
        { id := ⟨"r-elsewhere"⟩, name := "Elsewhere" }
      accounts := coreOpened.accounts.insert "acc-aaa"
        { coreAccount "acc-aaa" "Budget.Hut" .equity with realm := ⟨"r-elsewhere"⟩ } }
  r := checkEq r "a realm is named for the budget opened in it"
    (Wire.budgetOfRealm squatted { id := Realm.selfId, name := "me" }) (some "Hut")
  r := checkEq r "and not for one that only holds an account of that budget's name"
    (Wire.budgetOfRealm squatted { id := ⟨"r-elsewhere"⟩, name := "Elsewhere" }) none
  -- Opening a budget makes the equity account that holds it.
  match coreOpened.accountByNameIn? Realm.selfId "Budget.Hut" with
  | none => r := check r "opening a budget makes the account that holds it" false
  | some a =>
    r := check r "a budget account is equity, not an asset" (a.kind == .equity)
    r := checkEq r "and a bare name is placed under Budget" a.name "Budget.Hut"
  r := checkEq r "the budget itself is recorded under that name"
    (coreBudget coreOpened).name "Budget.Hut"
  -- Dividing two costs between two people, to the cent.
  match coreDivided.txn? ⟨"t-alloc1"⟩ with
  | none => r := check r "dividing a budget writes one transaction" false
  | some t =>
    r := check r "a division balances" (decide t.Balanced)
    r := checkEq r "your share of the weekend" (t.netIn ⟨"acc-food"⟩ "EUR") 8000
    r := checkEq r "hers" (t.netIn ⟨"acc-anna"⟩ "EUR") 8000
    r := checkEq r "and the budget is emptied by exactly the two costs"
      (t.netIn ⟨"acc-hut"⟩ "EUR") (-16000)
  r := checkEq r "so nothing is left undivided"
    (Budget.balance (coreBudget coreDivided) coreDivided eur).minor 0
  -- The claims it raises are the ones that leave everybody at zero.
  let hut := coreBudget coreDivided
  let plan := (Budget.claims hut coreDivided).filterMap
    (Pendings.transferOf coreDivided.accountsSorted.toArray)
  r := checkEq r "one claim squares the weekend up" plan.length 1
  r := check r "and performing it leaves everybody at zero"
    ((Settle.residual ((Budget.standings hut coreDivided eur).map Standing.position) plan).all
      fun p => p.minor == 0)
  match coreDivided.txn? ⟨"t-claim1"⟩ with
  | none => r := check r "dividing raises the claim that settles it" false
  | some c =>
    r := checkEq r "for what she owes once her groceries are netted off"
      (Pendings.amount c).minor 2000
    r := check r "and it has not happened yet" (c.state == .pending)
  -- A late receipt is divided on its own; what was decided stays decided.
  match coreToppedUp.txn? ⟨"t-alloc2"⟩, coreToppedUp.txn? ⟨"t-alloc1"⟩ with
  | some second, some first =>
    r := checkEq r "a second division tops each person up" (second.netIn ⟨"acc-food"⟩ "EUR") 1000
    r := checkEq r "both of them" (second.netIn ⟨"acc-anna"⟩ "EUR") 1000
    r := checkEq r "over only what came in since" (second.netIn ⟨"acc-hut"⟩ "EUR") (-2000)
    r := checkEq r "and the first division is untouched" (first.netIn ⟨"acc-food"⟩ "EUR") 8000
  | _, _ => r := check r "a late cost is divided on its own" false
  -- Settling revises the request it has already made, and withdraws the rest.
  match coreToppedUp.txn? ⟨"t-claim1"⟩, coreToppedUp.txn? ⟨"t-claim-bob"⟩ with
  | some revised, some stale =>
    r := checkEq r "a claim between the same two people is revised in place"
      (Pendings.amount revised).minor 3000
    r := check r "and stays outstanding" (revised.state == .pending)
    r := check r "a claim the facts have overtaken is withdrawn" (stale.state == .void)
  | _, _ => r := check r "settling revises rather than duplicates" false
  -- Where a settlement lands, when the budget has never moved anything of theirs.
  r := checkEq r "somebody with no leg in a budget settles through their purse"
    (((Budget.settlementAccount (coreBudget coreOpened) coreOpened ⟨"party-bob"⟩ eur).toOption.map
      (·.val)).getD "") "acc-bob"
  r := check r "and somebody with no account at all cannot be settled with"
    (Budget.settlementAccount (coreBudget coreOpened) coreOpened ⟨"party-nobody"⟩
      eur).toOption.isNone
  r := check r "a share of hers may not land in an account of yours"
    (Str.containsCI
      (coreError coreLate (.allocate ⟨"b-hut"⟩
        [{ owner := ⟨"party-anna"⟩, name := "Anna", account := "Expenses.Food" }]
        eur coreDate none ⟨"t-nowhere"⟩ [] ⟨"lbl-hut"⟩))
      "belongs to somebody else")
  r := check r "a budget still holding money cannot be settled"
    (Str.containsCI (coreError coreLate (.settle ⟨"b-hut"⟩ eur none coreDate [] ⟨"lbl-hut"⟩))
      "still holds")
  -- Closing, reopening, and closing again.
  let closed := coreStep coreToppedUp
    (.closeBudget ⟨"b-hut"⟩ none eur none coreDate ⟨"t-alloc3"⟩ [⟨"t-claim3"⟩] ⟨"lbl-hut"⟩)
  r := check r "closing a budget with nothing left to divide closes it"
    (coreBudget closed).closed
  r := check r "and writes no division it has no use for" (closed.txn? ⟨"t-alloc3"⟩).isNone
  r := check r "a closed budget takes no more costs"
    (Str.containsCI (coreError closed
      (.contribute ⟨"b-hut"⟩ (coreCost "t-hut9" "acc-bank" 100 "one more"))) "is closed")
  let again := coreSteps closed
    [ .reopenBudget ⟨"b-hut"⟩
    , .contribute ⟨"b-hut"⟩ (coreCost "t-hut4" "acc-bank" 4000 "an extra night")
    , .closeBudget ⟨"b-hut"⟩ none eur none coreDate ⟨"t-alloc4"⟩ [⟨"t-claim4"⟩] ⟨"lbl-hut"⟩ ]
  r := check r "closing it again closes it again" (coreBudget again).closed
  match again.txn? ⟨"t-alloc4"⟩ with
  | none => r := check r "a second close writes a second division" false
  | some t =>
    r := checkEq r "the second division covers only what came in since"
      (t.netIn ⟨"acc-hut"⟩ "EUR") (-4000)
    r := checkEq r "half of it to each of you" (t.netIn ⟨"acc-anna"⟩ "EUR") 2000
  r := checkEq r "and what was decided before it stands"
    (((again.txn? ⟨"t-alloc1"⟩).map fun t => t.netIn ⟨"acc-food"⟩ "EUR").getD 0) 8000
  -- Invoice numbers are gapless, and a deleted draft gives its number back.
  let numberOf (s : State) (id : String) : String :=
    ((s.invoice? ⟨id⟩).map (·.invoice.number)).getD ""
  let numbered := coreSteps coreOpened
    [ .issueInvoice (coreDraft "i1") [], .issueInvoice (coreDraft "i2") []
    , .issueInvoice (coreDraft "i3") [] ]
  r := checkEq r "invoices are numbered from one" (numberOf numbered "i1") "2026-0001"
  r := checkEq r "gaplessly" (numberOf numbered "i2") "2026-0002"
  r := checkEq r "and in the order they were written" (numberOf numbered "i3") "2026-0003"
  r := check r "each with a reference the importer can find again"
    (Rf.isValid (((numbered.invoice? ⟨"i1"⟩).map (·.invoice.reference)).getD ""))
  let rewound := coreSteps numbered [.deleteInvoice ⟨"i3"⟩, .issueInvoice (coreDraft "i4") []]
  r := check r "a deleted draft is gone" (rewound.invoice? ⟨"i3"⟩).isNone
  r := checkEq r "and the number it held is handed out again" (numberOf rewound "i4") "2026-0003"
  r := check r "an invoice somebody has seen is voided rather than deleted"
    (Str.containsCI
      (coreError (coreStep numbered (.setInvoiceStatus ⟨"i1"⟩ .sent)) (.deleteInvoice ⟨"i1"⟩))
      "void it")
  -- One invoice per claim addressed to you, and none for your own share.
  match Budget.invoicesFor (coreBudget coreToppedUp) coreToppedUp
      (.link "https://example.org/pay") coreDate coreDate eur none none
      [⟨"i-anna"⟩, ⟨"i-spare"⟩] with
  | .error e => r := check r s!"a budget raises the invoices for its claims ({e})" false
  | .ok out =>
    r := checkEq r "one invoice per claim addressed to an account of yours" out.length 1
    r := check r "and none for your own share" (out.all fun x => x.1.payerName != "me")
    match out.head? with
    | none => r := check r "the invoice to her is raised" false
    | some (inv, sources) =>
      r := checkEq r "addressed to the person who owes" inv.payerName "Anna"
      r := checkEq r "for exactly what her claim asks" inv.total.minor 3000
      r := check r "saying what she already paid for herself"
        (inv.lines.any fun l => l.description.startsWith "you paid: ")
      r := checkEq r "and billing the costs it was raised from" sources.length 3
  return r

/--
The pure core: what `applyOp` refuses, and what it does when it agrees.

Every case here is decided without a database, which is the point of the
exercise — the store will apply these same operations and only project what
comes back.
-/
private def coreTests (r : Report) : Report := Id.run do
  let mut r := r
  let s0 := coreBase
  let dinner := coreTxn "t-dinner" [cents "acc-bank" (-10000), cents "acc-food" 10000]
  -- A part that does not balance is not a part.
  r := check r "an unbalanced transaction is refused"
    (Str.containsCI (coreError s0 (.putTransaction
      (coreTxn "t-bad" [cents "acc-bank" (-10000), cents "acc-food" 9000]))) "does not balance")
  -- A closed account takes nothing further.
  r := check r "a closed account takes no more postings"
    (Str.containsCI (coreError s0 (.putTransaction
      (coreTxn "t-old" [cents "acc-old" (-10000), cents "acc-food" 10000]))) "is closed")
  -- Rights: a second member may not post until she is told she may.
  let withMara := coreSteps s0
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .grant Realm.selfId ⟨"mara"⟩ .viewer
        (coreAccount "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩) ]
  let asMara (s : State) : String :=
    match applyOp s ⟨"mara"⟩ Realm.selfId (.putTransaction dinner) with
    | .ok _ => ""
    | .error e => e
  r := check r "a member with no rights may not post"
    (Str.containsCI (asMara withMara) "you may not post to")
  r := check r "and somebody who is not in the realm at all may not even try"
    (Str.containsCI
      (match applyOp s0 ⟨"zoe"⟩ Realm.selfId (.putTransaction dinner) with
       | .ok _ => "" | .error e => e)
      "not in that realm")
  let told := coreStep (coreStep withMara (.setAccountRights ⟨"acc-bank"⟩ [⟨"mara"⟩]))
    (.setAccountRights ⟨"acc-food"⟩ [⟨"mara"⟩])
  r := checkEq r "a member named as a poster may" (asMara told) ""
  -- Handing an account over is a separate decision from putting one.
  let handed := coreStep s0 (.setAccountOwner ⟨"acc-food"⟩ ⟨"party-anna"⟩)
  r := checkEq r "an account can be handed to somebody else"
    (((handed.account? ⟨"acc-food"⟩).map (·.owner.val)).getD "") "party-anna"
  r := check r "and putting it again does not take it back"
    (((coreStep handed (.putAccount (coreAccount "acc-food" "Expenses.Food" .expense))).account?
      ⟨"acc-food"⟩).map (·.owner.val) == some "party-anna")
  -- Splitting: the shares add back to exactly what was paid.
  let s1 := coreStep s0 (.putTransaction dinner)
  let s2 := coreStep s1 (.splitTransaction ⟨"t-dinner"⟩ [⟨"acc-anna"⟩, ⟨"acc-bob"⟩] true)
  match s2.txn? ⟨"t-dinner"⟩ with
  | none => r := check r "the split transaction is still there" false
  | some t =>
    r := checkEq r "splitting leaves the funding leg alone" (t.netIn ⟨"acc-bank"⟩ "EUR") (-10000)
    r := checkEq r "the shares add back to the whole"
      (t.netIn ⟨"acc-food"⟩ "EUR" + t.netIn ⟨"acc-anna"⟩ "EUR" + t.netIn ⟨"acc-bob"⟩ "EUR")
      10000
    r := check r "and no two shares differ by more than a cent"
      ((t.netIn ⟨"acc-anna"⟩ "EUR" - t.netIn ⟨"acc-food"⟩ "EUR").natAbs ≤ 1)
    r := check r "a split transaction balances" (decide t.Balanced)
  -- Merging and unmerging are inverses, leg for leg.
  let sA := coreStep (coreStep s0 (.putTransaction
      (coreTxn "t-a" [cents "acc-bank" (-10000), cents "acc-food" 10000])))
    (.putTransaction (coreTxn "t-b" [cents "acc-bank" (-250), cents "acc-food" 250] "card fee"))
  let sM := coreStep sA (.mergeTransactions [⟨"t-a"⟩, ⟨"t-b"⟩] ⟨"t-m"⟩ none none [])
  let sU := coreStep sM (.unmergeTransaction ⟨"t-m"⟩ [⟨"t-a2"⟩, ⟨"t-b2"⟩])
  let legs (s : State) (ids : List String) : String :=
    String.intercalate ", "
      ((((ids.filterMap (fun i => s.txn? ⟨i⟩)).flatMap (fun t =>
        t.postings.map (fun p => s!"{p.account.val} {p.amount.minor}")))).mergeSort (· ≤ ·))
  r := check r "merging retires its sources"
    ((sM.txn? ⟨"t-a"⟩).isNone && (sM.txn? ⟨"t-b"⟩).isNone && (sM.txn? ⟨"t-m"⟩).isSome)
  r := check r "unmerging retires the merged transaction" (sU.txn? ⟨"t-m"⟩).isNone
  r := checkEq r "merging and unmerging round-trips the postings"
    (legs sU ["t-a2", "t-b2"]) (legs sA ["t-a", "t-b"])
  -- A division may book its spending anywhere; it may not invent money.
  r := check r "parts that take different money out of the funding account are refused"
    (Str.containsCI
      (coreError s1 (.replaceTransaction ⟨"t-dinner"⟩
        [ coreTxn "t-p1" [cents "acc-bank" (-6000), cents "acc-food" 6000]
        , coreTxn "t-p2" [cents "acc-bank" (-3000), cents "acc-food" 3000] ] "divide"))
      "do not take the same money out of")
  let sR := coreStep s1 (.replaceTransaction ⟨"t-dinner"⟩
    [ coreTxn "t-p1" [cents "acc-bank" (-6000), cents "acc-food" 6000]
    , coreTxn "t-p2" [cents "acc-bank" (-4000), cents "acc-anna" 4000] ] "divide")
  r := check r "parts that take the same money are written"
    ((sR.txn? ⟨"t-dinner"⟩).isNone && (sR.txn? ⟨"t-p1"⟩).isSome && (sR.txn? ⟨"t-p2"⟩).isSome)
  -- A part payment splits the claim rather than quietly shrinking it.
  let sC := coreStep s0 (.raiseClaim
    { id := ⟨"t-claim"⟩, date := coreDate, narration := "her share", state := .pending
      postings := [cents "acc-bank" 5000, cents "acc-anna" (-5000)] })
  let sP := coreStep sC (.putTransaction
    (coreTxn "t-paid" [cents "acc-bank" 2000, cents "acc-unc" (-2000)] "on account"))
  let sV := coreStep sP (.resolveClaim ⟨"t-claim"⟩ ⟨"t-paid"⟩ ⟨"t-claim-part"⟩)
  match sV.txn? ⟨"t-claim-part"⟩, sV.txn? ⟨"t-claim"⟩ with
  | some met, some rest =>
    r := check r "the part that was met is settled" (met.state == .settled)
    r := checkEq r "for exactly what arrived" (Pendings.amount met).minor 2000
    r := check r "and what is left is still pending" (rest.state == .pending)
    r := checkEq r "reduced by what was paid" (Pendings.amount rest).minor 3000
  | _, _ => r := check r "a part payment splits the claim" false
  r := checkEq r "meeting a claim tells the payment who the money was from"
    (((sV.txn? ⟨"t-paid"⟩).map (fun t => t.netIn ⟨"acc-anna"⟩ "EUR")).getD 0) (-2000)
  -- A claim is exactly two legs, whichever door it comes through.
  r := check r "a claim with three legs is refused"
    (Str.containsCI (coreError s0 (.raiseClaim
      { id := ⟨"t-three"⟩, date := coreDate, narration := "three ways", state := .pending
        postings := [cents "acc-bank" 6000, cents "acc-anna" (-3000),
                     cents "acc-bob" (-3000)] })) "exactly two legs")
  -- Paying a claim: the person who would have seen the money arrive, and nobody
  -- else. The payer saying so is a receipt they wrote themselves.
  let purses := coreSteps s0
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ }
    , .addMember { id := ⟨"otto"⟩, name := "Otto", party := ⟨"party-otto"⟩ }
    , .grant Realm.selfId ⟨"mara"⟩ .viewer
        (coreAccount "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩)
    , .grant Realm.selfId ⟨"nils"⟩ .viewer
        (coreAccount "acc-nils" "Assets.Purse.Nils" .asset ⟨"party-nils"⟩)
    , .grant Realm.selfId ⟨"otto"⟩ .viewer
        (coreAccount "acc-otto" "Assets.Purse.Otto" .asset ⟨"party-otto"⟩)
    , .raiseClaim
        { id := ⟨"t-claim-m"⟩, date := coreDate, narration := "her share", state := .pending
          postings := [cents "acc-nils" 5000, cents "acc-mara" (-5000)] } ]
  let payAs (who : String) (s : State) (pid : String) : Except String State :=
    (applyOp s ⟨who⟩ Realm.selfId (.payClaim ⟨"t-claim-m"⟩ ⟨pid⟩ coreDate)).map (·.1)
  match payAs "nils" purses "t-pay" with
  | .error e => r := check r s!"the receiver's member may pay a claim: {e}" false
  | .ok paid =>
    match paid.txn? ⟨"t-pay"⟩, paid.txn? ⟨"t-claim-m"⟩ with
    | some entry, some met =>
      r := checkEq r "paying a claim moves exactly what it asked for"
        (entry.netIn ⟨"acc-nils"⟩ "EUR") 5000
      r := checkEq r "out of the account that owed it" (entry.netIn ⟨"acc-mara"⟩ "EUR") (-5000)
      r := checkEq r "and says what it is for" entry.narration "payment of her share"
      r := check r "both legs are tagged as the claim's"
        (entry.postings.all (fun p => p.tag == some Pendings.tag))
      r := check r "the payment is posted" (entry.state == .posted)
      r := check r "and the claim it met is settled" (met.state == .settled)
    | _, _ => r := check r "paying a claim writes the payment and settles the claim" false
  r := check r "the member who owes it may not say it was paid"
    (Str.containsCI
      (match payAs "mara" purses "t-pay" with | .ok _ => "" | .error e => e)
      "only the receiver or an admin")
  r := check r "and neither may a third member"
    (Str.containsCI
      (match payAs "otto" purses "t-pay" with | .ok _ => "" | .error e => e)
      "only the receiver or an admin")
  r := check r "an admin of the realm may"
    (payAs Member.selfId.val purses "t-pay").toOption.isSome
  match payAs "nils" purses "t-pay" with
  | .error _ => r := check r "a claim can be paid once" false
  | .ok paid =>
    r := check r "and a claim that is already settled cannot be paid again"
      (Str.containsCI
        (match payAs "nils" paid "t-pay-again" with | .ok _ => "" | .error e => e)
        "already settled")
  r := check r "a claim between accounts that cannot hold money is not paid at all"
    (Str.containsCI
      (coreError
        (coreSteps coreOpened
          [ .raiseClaim
              { id := ⟨"t-claim-e"⟩, date := coreDate, narration := "into the pot"
                state := .pending
                postings := [cents "acc-hut" 1000, cents "acc-anna" (-1000)] } ])
        (.payClaim ⟨"t-claim-e"⟩ ⟨"t-pay-e"⟩ coreDate))
      "accounts that can hold money")
  -- A budget is an account anybody in the realm may put a cost into, while it is open.
  let shared := coreSteps coreOpened
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .grant Realm.selfId ⟨"mara"⟩ .viewer
        (coreAccount "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩) ]
  let contribution := coreTxn "t-her-cost" [cents "acc-mara" (-2500), cents "acc-hut" 2500] "food"
  let asMaraIn (s : State) : String :=
    match applyOp s ⟨"mara"⟩ Realm.selfId (.putTransaction contribution) with
    | .ok _ => ""
    | .error e => e
  r := checkEq r "a participant may post into a budget of their realm while it is open"
    (asMaraIn shared) ""
  let shut := coreStep shared (.closeBudget ⟨"b-hut"⟩ none Commodity.eur none coreDate
    ⟨"t-alloc-c"⟩ [⟨"t-claim-c"⟩] ⟨"lbl-hut"⟩)
  r := check r "the budget really is closed"
    (((shut.budget? ⟨"b-hut"⟩).map (·.budget.closed)) == some true)
  r := check r "and a closed budget takes nothing further from them"
    (Str.containsCI (asMaraIn shut) "you may not post to")
  -- A grant hands out a purse; it never moves an account that is already elsewhere.
  let twoRealms := coreSteps s0
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                     members := [(Member.selfId, .admin)], generation := 0 } ]
  r := check r "a grant naming an account of another realm is refused"
    (Str.containsCI (coreErrorAs Member.selfId.val ⟨"realm-flat"⟩ twoRealms
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer
        (coreAccount "acc-bank" "Assets.Bank" .asset))) "another realm")
  r := check r "and a grant written in a realm other than the one it names is refused too"
    (Str.containsCI (coreError twoRealms (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer
      (coreAccount "acc-mara" "Assets.Purse.Mara" .asset))) "only change the realm it names")
  let regranted := coreStep twoRealms (.grant Realm.selfId ⟨"mara"⟩ .viewer
    (coreAccount "acc-bank" "Assets.Bank" .asset))
  r := check r "and a grant naming one of this realm's own accounts leaves it alone"
    (((regranted.account? ⟨"acc-bank"⟩).map (fun a => (a.realm, a.bridgeOf))) ==
      some (Realm.selfId, none))
  r := check r "while still letting the member in"
    (((regranted.realm? Realm.selfId).map (fun x => x.isMember ⟨"mara"⟩)) == some true)
  -- Joining a realm through an invite: the admin's node was not there, so the
  -- only person who can write the newcomer into the log is the newcomer.
  let nils : Member := { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ }
  let asNils (s : State) (op : Op) : Except String State :=
    (applyOp s ⟨"nils"⟩ Realm.selfId op).map (·.1)
  let said (e : Except String State) : String :=
    match e with | .ok _ => "" | .error msg => msg
  match asNils s0 (.addMember nils) with
  | .error e => r := check r s!"a member may introduce themselves: {e}" false
  | .ok introduced =>
    r := check r "a member may introduce themselves"
      (((introduced.member? ⟨"nils"⟩).map (·.name)) == some "Nils")
    r := check r "and the party their spending lands on is written with them"
      (((introduced.party? ⟨"party-nils"⟩).map (fun p => (p.name, p.kind))) ==
        some ("Nils", "contact"))
  r := check r "but a member may not write somebody else in"
    (Str.containsCI
      (said (asNils s0 (.addMember { id := ⟨"otto"⟩, name := "Otto"
                                     party := ⟨"party-otto"⟩ })))
      "only an admin")
  let namedAlready := coreSteps s0
    [ .putParty { id := ⟨"party-nils"⟩, name := "Nils Andersson", kind := "contact" }
    , .addMember nils ]
  r := check r "a party the ledger already knows is left exactly as it was"
    (((namedAlready.party? ⟨"party-nils"⟩).map (·.name)) == some "Nils Andersson")
  -- And the grant: a view of the realm, self-attested, and nothing beyond it.
  let joined := coreStep s0 (.addMember nils)
  let nilsPurse := coreAccount "acc-nils" "Assets.Purse.Nils" .asset
  match asNils joined (.grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse) with
  | .error e => r := check r s!"a member may grant themselves a view: {e}" false
  | .ok viewing =>
    r := check r "a member may grant themselves a view of a realm"
      (((viewing.realm? Realm.selfId).map (fun x => x.roleOf ⟨"nils"⟩)) == some (some .viewer))
    r := check r "and the purse it opens is theirs, not the author's"
      (((viewing.account? ⟨"acc-nils"⟩).map (fun a => (a.owner, a.bridgeOf))) ==
        some (⟨"party-nils"⟩, some ⟨"nils"⟩))
  r := check r "a self-grant buys a view and nothing more"
    (Str.containsCI (said (asNils joined (.grant Realm.selfId ⟨"nils"⟩ .admin nilsPurse)))
      "only an admin")
  let alsoOtto := coreStep joined
    (.addMember { id := ⟨"otto"⟩, name := "Otto", party := ⟨"party-otto"⟩ })
  r := check r "and lets nobody else in"
    (Str.containsCI
      (said (asNils alsoOtto (.grant Realm.selfId ⟨"otto"⟩ .viewer
        (coreAccount "acc-otto" "Assets.Purse.Otto" .asset))))
      "only an admin")
  r := check r "a bridge an admin opens belongs to the member's party too"
    ((((coreStep joined (.grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse)).account?
      ⟨"acc-nils"⟩).map (·.owner)) == some ⟨"party-nils"⟩)
  r := check r "a grant naming somebody the ledger has never heard of is refused"
    (Str.containsCI (coreError s0 (.grant Realm.selfId ⟨"zoe"⟩ .viewer
      (coreAccount "acc-zoe" "Assets.Purse.Zoe" .asset))) "add zoe first")
  -- What an account mirrors is set when it is made, and never afterwards.
  let mirrored := coreStep s0 (.putAccount
    { coreAccount "acc-mine" "Assets.Purse.Mine" .asset with mirrorOf := some ⟨"acc-bridge"⟩ })
  r := check r "an account can be made as the mirror of a bridge"
    (((mirrored.account? ⟨"acc-mine"⟩).bind (·.mirrorOf)) == some ⟨"acc-bridge"⟩)
  let reput := coreStep mirrored
    (.putAccount (coreAccount "acc-mine" "Assets.Purse.Mine" .asset))
  r := check r "and putting it again does not forget what it mirrors"
    (((reput.account? ⟨"acc-mine"⟩).bind (·.mirrorOf)) == some ⟨"acc-bridge"⟩)
  let repointed := coreStep mirrored (.putAccount
    { coreAccount "acc-mine" "Assets.Purse.Mine" .asset with mirrorOf := some ⟨"acc-other"⟩ })
  r := check r "nor lets it be repointed at another bridge"
    (((repointed.account? ⟨"acc-mine"⟩).bind (·.mirrorOf)) == some ⟨"acc-bridge"⟩)
  -- ## One rule per operation
  --
  -- Every case below is an operation this core used to take from somebody who
  -- had no business writing it. They are grouped the way `Op.rights` is.
  let viewer := coreSteps s0
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .grant Realm.selfId ⟨"mara"⟩ .viewer
        (coreAccount "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩) ]
  let refusedMara (name : String) (op : Op) (words : String) : Report → Report := fun r =>
    check r name (Str.containsCI (coreErrorAs "mara" Realm.selfId viewer op) words)
  -- Genesis. It is a position in the log, not an operation, so no part may carry
  -- one at all — "fresh" used to be a question about the state a reader had
  -- managed to fold, and a client holding one generation's key folds nothing
  -- written under any other.
  r := check r "a snapshot is refused wherever a part carries one"
    (Str.containsCI (coreError s0 (.snapshot coreOpened)) "where a log starts")
  r := check r "and refused on an empty ledger too, where it used to be taken"
    (Str.containsCI (coreError State.init (.snapshot coreOpened)) "where a log starts")
  -- Where it *is* read: position 1 of a replay, and nowhere else.
  let genesisEvent := coreEvent "genesis" [.snapshot coreOpened]
  let later := coreEvent "later" [.putLabel { id := ⟨"lbl-late"⟩, name := "late" }]
  r := check r "a log that opens with one snapshot replays from it"
    (replay [genesisEvent] == coreOpened)
  r := check r "and the events after it are folded onto it"
    ((replay [genesisEvent, later]).label? ⟨"lbl-late"⟩).isSome
  r := check r "the same snapshot at position two changes nothing"
    (replay [later, genesisEvent] == replay [later])
  -- Exactly one part, and that part a snapshot, is the whole test. An event
  -- with a snapshot beside something else is an ordinary event whose snapshot
  -- part is refused and whose neighbour applies.
  let mixed := replay [coreEvent "both"
    [.snapshot coreOpened, .putLabel { id := ⟨"lbl-x"⟩, name := "x" }]]
  r := check r "an event of a snapshot beside something else is not a beginning"
    (mixed.accounts.isEmpty && (mixed.label? ⟨"lbl-x"⟩).isSome)
  -- Structure. A viewer writes none of it.
  r := refusedMara "a viewer may not write an account"
    (.putAccount (coreAccount "acc-new" "Expenses.Books" .expense)) "only an admin" r
  r := refusedMara "nor rename one onto a budget's name"
    (.putAccount (coreAccount "acc-bank" "Budget.Hut" .asset)) "only an admin" r
  r := refusedMara "nor merge accounts" (.mergeAccounts ⟨"acc-food"⟩ ⟨"acc-mara"⟩)
    "only an admin" r
  r := refusedMara "nor delete one" (.deleteAccount ⟨"acc-bob"⟩) "only an admin" r
  r := refusedMara "nor say who posts where" (.setAccountRights ⟨"acc-bank"⟩ [⟨"mara"⟩])
    "only an admin" r
  r := refusedMara "nor hand an account over" (.setAccountOwner ⟨"acc-bank"⟩ ⟨"party-mara"⟩)
    "only an admin" r
  r := refusedMara "nor write a label" (.putLabel { id := ⟨"0000"⟩, name := "budget:Hut" })
    "only an admin" r
  r := refusedMara "nor delete one" (.deleteLabel ⟨"lbl-hut"⟩) "only an admin" r
  r := refusedMara "nor rewrite a party"
    (.putParty { id := Party.selfId, name := "not you", kind := "contact" }) "only an admin" r
  r := refusedMara "nor save a group"
    (.putGroup { name := "flat", members := ["Anna"] }) "only an admin" r
  r := refusedMara "nor a trip"
    (.putTrip { id := "t", name := "t", starts := coreDate, ends := coreDate
                payer := "party-anna", note := none }) "only an admin" r
  r := refusedMara "nor a rule"
    (.putRule { id := ⟨"rul"⟩, name := "r", filterSrc := "", filter := .all
                setAccount := none, addLabels := [], setParty := none, priority := 0 })
    "only an admin" r
  r := refusedMara "nor record an import batch"
    (.recordImportBatch { id := ⟨"bat"⟩, profile := "p", filename := none, account := none
                          stamp := "", total := 0, duplicates := 0 }) "only an admin" r
  -- A merge asks about the account being emptied, not only the one being filled.
  let twoPurses := coreSteps viewer
    [ .addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ }
    , .grant Realm.selfId ⟨"nils"⟩ .viewer
        (coreAccount "acc-nils" "Assets.Purse.Nils" .asset ⟨"party-nils"⟩) ]
  r := check r "a merge is not a way to take somebody else's purse"
    (Str.containsCI
      (coreErrorAs "mara" Realm.selfId twoPurses (.mergeAccounts ⟨"acc-nils"⟩ ⟨"acc-mara"⟩))
      "only an admin")
  -- Realms. A realm is created with its author as its only admin.
  r := check r "a realm cannot be created with somebody else already inside it"
    (Str.containsCI (coreError viewer
      (.createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                      members := [(⟨"mara"⟩, .admin)], generation := 0 }))
      "its only admin")
  r := check r "nor at a generation that says its keys have been rotated"
    (Str.containsCI (coreError viewer
      (.createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                      members := [(Member.selfId, .admin)], generation := 3 }))
      "generation 0")
  r := check r "a role is only changed in the realm the part names"
    (Str.containsCI (coreError viewer (.setRole ⟨"realm-other"⟩ ⟨"mara"⟩ .admin))
      "only change the realm it names")
  r := check r "and so is a revoke"
    (Str.containsCI (coreError viewer (.revoke ⟨"realm-other"⟩ ⟨"mara"⟩))
      "only change the realm it names")
  r := check r "and a rotation"
    (Str.containsCI (coreError viewer (.rotateRealmKey ⟨"realm-other"⟩))
      "only change the realm it names")
  -- A self-introduction is about who you are, and the party is part of that.
  r := check r "a newcomer may not introduce themselves as the ledger's own party"
    (Str.containsCI
      (coreErrorAs "zoe" Realm.selfId s0
        (.addMember { id := ⟨"zoe"⟩, name := "Zoe", party := Party.selfId }))
      "ledger's own party")
  r := check r "nor as somebody else's"
    (Str.containsCI
      (coreErrorAs "zoe" Realm.selfId viewer
        (.addMember { id := ⟨"zoe"⟩, name := "Zoe", party := ⟨"party-mara"⟩ }))
      "already somebody else's")
  r := check r "nor may they change the party they were recorded under"
    (Str.containsCI
      (coreErrorAs "mara" Realm.selfId viewer
        (.addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-zoe"⟩ }))
      "cannot change the party")
  -- Removing a member puts them out of this realm; the identity goes last.
  let inTwo := coreSteps viewer
    [ .createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                     members := [(Member.selfId, .admin)], generation := 0 } ]
  let outOfSelf := coreStep inTwo (.removeMember ⟨"mara"⟩)
  r := check r "removing a member puts them out of the realm the part names"
    (((outOfSelf.realm? Realm.selfId).map (fun x => x.isMember ⟨"mara"⟩)) == some false)
  r := check r "and takes the identity with them when no realm is left holding it"
    (outOfSelf.member? ⟨"mara"⟩).isNone
  -- Transactions. A viewer of the realm may write their own legs and no others.
  r := refusedMara "a transaction needs postings"
    (.putTransaction (coreTxn "t-empty" [])) "needs postings" r
  r := refusedMara "a transaction is written as posted"
    (.putTransaction { coreTxn "t-void" [cents "acc-mara" (-1), cents "acc-food" 1] with
                       state := .void }) "written as posted" r
  r := check r "and a rewrite of a transaction with no leg in this realm is refused"
    (Str.containsCI
      (coreErrorAs "mara" ⟨"realm-flat"⟩
        (coreSteps inTwo [.putTransaction dinner]) (.putTransaction dinner))
      "not in that realm")
  r := refusedMara "a viewer may not retire somebody else's transaction"
    (.deleteTransaction ⟨"t-dinner"⟩) "no such transaction" r
  let spent := coreStep s0 (.putTransaction dinner)
  let spentSeen := coreSteps spent
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .grant Realm.selfId ⟨"mara"⟩ .viewer
        (coreAccount "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩) ]
  r := check r "a viewer may not delete a transaction whose legs are not theirs"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId spentSeen (.deleteTransaction ⟨"t-dinner"⟩))
      "you may not post to")
  r := check r "nor split it"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId spentSeen
      (.splitTransaction ⟨"t-dinner"⟩ [⟨"acc-mara"⟩] true)) "you may not post to")
  r := check r "nor hang a receipt on it"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId spentSeen (.attach ⟨"t-dinner"⟩ "rcpt"))
      "you may not post to")
  r := check r "nor take one off it"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId spentSeen (.detach ⟨"t-dinner"⟩ "rcpt"))
      "you may not post to")
  -- Claims. Raising is an admin's; meeting and withdrawing are the creditor's.
  r := refusedMara "a viewer may not raise a claim"
    (.raiseClaim { id := ⟨"t-c"⟩, date := coreDate, narration := "mine", state := .pending
                   postings := [cents "acc-mara" 100, cents "acc-bank" (-100)] })
    "only an admin" r
  let owed := coreSteps s0
    [ .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
    , .addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ }
    , .grant Realm.selfId ⟨"mara"⟩ .viewer
        (coreAccount "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩)
    , .grant Realm.selfId ⟨"nils"⟩ .viewer
        (coreAccount "acc-nils" "Assets.Purse.Nils" .asset ⟨"party-nils"⟩)
    , .raiseClaim
        { id := ⟨"t-owed"⟩, date := coreDate, narration := "her share", state := .pending
          postings := [cents "acc-nils" 5000, cents "acc-mara" (-5000)] } ]
  r := check r "the debtor may not withdraw the claim against them"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId owed (.voidClaim ⟨"t-owed"⟩ none))
      "may withdraw this claim")
  r := check r "the creditor may"
    (coreAllows "nils" Realm.selfId owed (.voidClaim ⟨"t-owed"⟩ none))
  r := check r "a claim that has been met is not withdrawn afterwards"
    (Str.containsCI
      (coreError (coreStep owed (.payClaim ⟨"t-owed"⟩ ⟨"t-p"⟩ coreDate))
        (.voidClaim ⟨"t-owed"⟩ none))
      "outstanding claim")
  r := check r "and the debtor does not get to say a claim was met either"
    (Str.containsCI
      (coreErrorAs "mara" Realm.selfId
        (coreStep owed (.putTransaction
          (coreTxn "t-arrived" [cents "acc-nils" 5000, cents "acc-unc" (-5000)] "paid")))
        (.resolveClaim ⟨"t-owed"⟩ ⟨"t-arrived"⟩ ⟨"t-part"⟩))
      "may meet this claim")
  -- Budgets. Every verb is an admin's, and the pot is keyed by its account id.
  r := check r "a viewer may not open a budget"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId viewer
      (.openBudget coreHut (coreAccount "acc-hut" "Hut" .equity))) "only an admin")
  r := check r "nor name who a budget is divided among"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId shared
      (.setParticipants ⟨"b-hut"⟩ coreAmong)) "only an admin")
  r := check r "nor allocate it"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId shared
      (.allocate ⟨"b-hut"⟩ coreAmong Commodity.eur coreDate none ⟨"t-a"⟩ [] ⟨"lbl-hut"⟩))
      "only an admin")
  r := check r "nor close it"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId shared
      (.closeBudget ⟨"b-hut"⟩ none Commodity.eur none coreDate ⟨"t-a"⟩ [] ⟨"lbl-hut"⟩))
      "only an admin")
  r := check r "a budget is decided in the realm it lives in"
    (Str.containsCI (coreErrorAs Member.selfId.val ⟨"realm-other"⟩ shared
      (.reopenBudget ⟨"b-hut"⟩)) "only an admin")
  r := check r "the budget's own account is the one its record names"
    (((shared.budget? ⟨"b-hut"⟩).map (·.account)) == some ⟨"acc-hut"⟩)
  r := check r "and an account that merely shares its name is not it"
    (let shadowed := coreStep shared
      (.putAccount { coreAccount "0000" "Budget.Hut" .equity with realm := Realm.selfId })
     (Budget.account? (coreBudget shadowed) shadowed).map (·.id) == some ⟨"acc-hut"⟩)
  r := check r "a participant may put money into the pot"
    (coreAllows "mara" Realm.selfId shared
      (.putTransaction (coreTxn "t-in" [cents "acc-mara" (-2500), cents "acc-hut" 2500] "food")))
  r := check r "and may not take it out again"
    (Str.containsCI
      (coreErrorAs "mara" Realm.selfId shared
        (.putTransaction (coreTxn "t-out" [cents "acc-hut" (-2500), cents "acc-mara" 2500] "mine")))
      "you may not post to")
  -- Invoices. The numbering is one sequence and only an admin moves it.
  r := refusedMara "a viewer may not issue an invoice"
    (.issueInvoice (coreDraft "i-v") []) "only an admin" r
  r := refusedMara "nor move one to a new status" (.setInvoiceStatus ⟨"i-v"⟩ .sent)
    "only an admin" r
  -- Receipts. What a receipt says is what a division divides by.
  let filed := coreStep viewer (.registerBlob
    { sha256 := "rcpt", mime := "image/jpeg", bytes := 8, origName := none, createdAt := "" })
  r := check r "the member who filed a receipt may say what it contains"
    (coreAllows Member.selfId.val Realm.selfId filed
      (.setReceiptLines "rcpt" [{ description := "bread", amount := ⟨Commodity.eur, 500⟩ }]))
  r := check r "and somebody who did not may not"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId filed
      (.setReceiptLines "rcpt" [{ description := "wine", amount := ⟨Commodity.eur, 500⟩ }]))
      "may say what it contains")
  r := check r "nor re-seal it under another key"
    (Str.containsCI (coreErrorAs "mara" Realm.selfId filed
      (.registerBlob { sha256 := "rcpt", mime := "image/jpeg", bytes := 8, origName := none
                       createdAt := "", cipherHash := some "ff" }))
      "register it again")
  r := refusedMara "nor forget it" (.forgetBlob "rcpt") "only an admin" r
  -- Bounds. What an event carries is bounded, because a reader applies it.
  r := check r "a receipt line cannot claim a quantity nobody printed"
    (Str.containsCI
      (coreError filed
        (.setReceiptLines "rcpt"
          [{ description := "x", qty := some 1000000000000, amount := ⟨Commodity.eur, 1⟩ }]))
      "covers at most")
  r := check r "a transaction cannot carry more postings than a person writes"
    (Str.containsCI
      (coreError s0 (.putTransaction (coreTxn "t-many"
        ((List.replicate 201 (cents "acc-bank" 0))))))
      "at most 200")
  r := check r "a budget cannot be divided among a crowd"
    (Str.containsCI
      (coreError coreOpened (.setParticipants ⟨"b-hut"⟩
        (List.replicate 101 { owner := ⟨"party-anna"⟩, name := "Anna"
                              account := "Assets.Purse.Anna" })))
      "at most 100")
  r := check r "a share's weight is bounded"
    (Str.containsCI
      (coreError coreOpened (.setParticipants ⟨"b-hut"⟩
        [{ owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna"
           weight := 10001 }]))
      "weight has to be between")
  r := check r "and an identifier is not a megabyte"
    (Str.containsCI
      (coreError s0 (.putLabel { id := ⟨String.ofList (List.replicate 201 'x')⟩, name := "x" }))
      "longer than 200")
  -- ## The realm every entity is in
  --
  -- Eight kinds of entry used to have none, so "an admin of the part's realm"
  -- reached across every realm a reader could open — and creating a realm you
  -- administer and handing somebody a key to it is something any member may do.
  let other : RealmId := ⟨"realm-other"⟩
  let twoRealms := coreSteps viewer
    [ .createRealm { id := other, name := "flat", members := [(Member.selfId, .admin)] } ]
  let inOther (ops : List Op) : State :=
    ops.foldl (fun st op =>
      match applyOp st Member.selfId other op with
      | .ok (st', _) => st'
      | .error _ => st) twoRealms
  let theirs := inOther
    [ .putLabel { id := ⟨"lbl-theirs"⟩, name := "theirs" }
    , .putParty { id := ⟨"party-theirs"⟩, name := "Landlord", kind := "contact" }
    , .putGroup { name := "flatmates", members := ["Anna"] }
    , .putTrip { id := "trp-t", name := "Flat", starts := coreDate, ends := coreDate
                 payer := "party-anna", note := none }
    , .putRule { id := ⟨"rul-t"⟩, name := "rent", filterSrc := "", filter := .all
                 setAccount := none, addLabels := [], setParty := none, priority := 0 }
    , .registerBlob { sha256 := "theirs", mime := "image/jpeg", bytes := 8, origName := none
                      createdAt := "" } ]
  r := check r "an entity is created in the realm the part names"
    (((theirs.label? ⟨"lbl-theirs"⟩).map (·.realm)) == some other)
  let elsewhere (name : String) (op : Op) : Report → Report := fun r =>
    check r name (Str.containsCI (coreError theirs op) "not in this realm")
  r := elsewhere "a label of another realm is not this part's to rewrite"
    (.putLabel { id := ⟨"lbl-theirs"⟩, name := "mine now" }) r
  r := elsewhere "nor to delete" (.deleteLabel ⟨"lbl-theirs"⟩) r
  r := elsewhere "nor a party of one"
    (.putParty { id := ⟨"party-theirs"⟩, name := "not them", kind := "contact" }) r
  r := elsewhere "nor a group" (.putGroup { name := "flatmates", members := ["Bob"] }) r
  r := elsewhere "nor a trip"
    (.putTrip { id := "trp-t", name := "Flat", starts := coreDate, ends := coreDate
                payer := "party-bob", note := none }) r
  r := elsewhere "nor a rule"
    (.putRule { id := ⟨"rul-t"⟩, name := "mine", filterSrc := "", filter := .all
                setAccount := none, addLabels := [], setParty := none, priority := 1 }) r
  r := elsewhere "nor a receipt filed in one"
    (.setReceiptLines "theirs" [{ description := "x", amount := ⟨Commodity.eur, 1⟩ }]) r
  r := elsewhere "nor forget it" (.forgetBlob "theirs") r
  r := check r "a member may revise their own party from any realm they are in"
    (coreAllows "mara" other
      (coreSteps theirs [.grant other ⟨"mara"⟩ .viewer
        (coreAccount "acc-m2" "Members.Mara" .asset ⟨"party-mara"⟩)])
      (.putParty { id := ⟨"party-mara"⟩, name := "Mara Neumann", kind := "contact" }))
  r := check r "and the record keeps the realm it was introduced in"
    (((theirs.party? ⟨"party-mara"⟩).map (·.realm)) == some Realm.selfId)
  -- A label is stripped from this realm's transactions and no others.
  let crossed := coreSteps
    (inOther [.putAccount (coreAccount "acc-t" "Expenses.Theirs" .expense)])
    [ .putLabel { id := ⟨"lbl-here"⟩, name := "here" }
    , .putTransaction { coreTxn "t-here"
        [cents "acc-bank" (-100), cents "acc-food" 100] "dinner" with
          labels := [⟨"lbl-here"⟩] } ]
  r := check r "deleting a label strips it from this realm's transactions"
    ((((coreStep crossed (.deleteLabel ⟨"lbl-here"⟩)).txn? ⟨"t-here"⟩).map (·.labels))
      == some [])
  -- A label of theirs, on a transaction of yours: deleting it would have to
  -- rewrite a transaction with no leg in their realm, so it is refused and the
  -- label stays rather than leaving an id nothing resolves.
  let borrowed := coreSteps
    (inOther [.putLabel { id := ⟨"lbl-there"⟩, name := "there" }])
    [ .putTransaction { coreTxn "t-mine"
        [cents "acc-bank" (-100), cents "acc-food" 100] "dinner" with
          labels := [⟨"lbl-there"⟩] } ]
  r := check r "and is refused when it would have to rewrite another realm's"
    (Str.containsCI (coreErrorAs Member.selfId.val other borrowed (.deleteLabel ⟨"lbl-there"⟩))
      "no leg in this realm")
  -- Invoice numbering is one sequence per realm, not one for the ledger.
  let year := coreDate.year.toInt.toNat
  let numbered := coreStep (inOther [.issueInvoice (coreDraft "i-1") []])
    (.issueInvoice (coreDraft "i-2") [])
  r := check r "the invoice counter is one sequence per realm"
    (numbered.counters.contains s!"{Realm.selfId.val}:invoice:{year}" &&
      numbered.counters.contains s!"{other.val}:invoice:{year}")
  r := check r "so an admin of another realm cannot move your numbering"
    (numbered.counters[s!"{Realm.selfId.val}:invoice:{year}"]? == some 1)
  -- ## The invoice record's own realm
  --
  -- The counter being keyed by realm made the missing one worse rather than
  -- better: an admin of any realm a reader could open deleted a draft issued
  -- somewhere else and wound back their own realm's sequence, so the issuing
  -- realm kept the burnt number and the next invoice in the other realm
  -- duplicated one already sent. The same door marked any invoice paid or void.
  let stepIn (st : State) (realm : RealmId) (op : Op) : State :=
    match applyOp st Member.selfId realm op with
    | .ok (st', _) => st'
    | .error _ => st
  let issuedThere := inOther [.issueInvoice (coreDraft "i-there") []]
  r := check r "an invoice carries the realm it was issued in"
    (((issuedThere.invoice? ⟨"i-there"⟩).map (·.realm)) == some other)
  let fromHere (name : String) (op : Op) : Report → Report := fun r =>
    check r name (Str.containsCI (coreError issuedThere op) "not in this realm")
  r := fromHere "an invoice of another realm is not this part's to delete"
    (.deleteInvoice ⟨"i-there"⟩) r
  r := fromHere "nor to move to a new status" (.setInvoiceStatus ⟨"i-there"⟩ .void) r
  r := fromHere "nor to record a settlement against"
    (.settleInvoice ⟨"i-there"⟩ ⟨"t-nothing"⟩) r
  r := check r "so a counter is only ever wound back by the realm that moved it"
    ((coreStep issuedThere (.deleteInvoice ⟨"i-there"⟩)).counters[s!"{other.val}:invoice:{year}"]?
      == some 1)
  -- The payer is resolved by name in the part's realm. A member may set the name
  -- of their own party to anything at all from any realm they are in, so the
  -- lookup across every realm handed an invoice to whichever record sorted first.
  let annaHere := coreStep twoRealms
    (.putParty { id := ⟨"party-anna"⟩, name := "Anna", kind := "contact" })
  let twoAnnas := stepIn annaHere other
    (.putParty { id := ⟨"party-anna-there"⟩, name := "Anna", kind := "contact" })
  let payerThere := stepIn twoAnnas other (.issueInvoice (coreDraft "i-payer") [])
  r := check r "an invoice's payer is the person of that name in the part's realm"
    (((payerThere.invoice? ⟨"i-payer"⟩).bind (·.invoice.payerId)) == some ⟨"party-anna-there"⟩)
  let newPayer := stepIn twoRealms other
    (.issueInvoice { coreDraft "i-new" with
                     payerName := "Dora", payerId := some ⟨"party-dora"⟩ } [])
  r := check r "and a payer nobody knows yet is introduced in that realm"
    (((newPayer.party? ⟨"party-dora"⟩).map (·.realm)) == some other)
  -- A grant looks for the bridge by name in the realm it is granting, so a name
  -- somebody took in another realm no longer blocks it. `Members.<name>` is a
  -- name any member can mint about themselves through the attest door.
  let nameTakenHere := coreSteps twoRealms
    [ .addMember { id := ⟨"zoe"⟩, name := "Zoe", party := ⟨"party-zoe"⟩ }
    , .putAccount (coreAccount "acc-here" "Members.Zoe" .asset) ]
  r := check r "a grant is not blocked by an account of that name in another realm"
    (coreAllows Member.selfId.val other nameTakenHere
      (.grant other ⟨"zoe"⟩ .viewer (coreAccount "acc-zoe-there" "Members.Zoe" .asset)))
  -- A settlement lands in an account of theirs in the budget's own realm. An
  -- account of theirs anywhere else used to outrank it and then be refused by
  -- the posting rules, which stopped every settlement of the budget until an
  -- admin closed or renamed an account in a realm that had nothing to do with it.
  let bobAbroad := stepIn
    (coreStep coreOpened
      (.createRealm { id := other, name := "flat", members := [(Member.selfId, .admin)] }))
    other (.putAccount (coreAccount "acc-b0" "Assets.Purse.Bob" .asset ⟨"party-bob"⟩))
  r := checkEq r "a settlement account is looked for in the budget's own realm"
    (((Budget.settlementAccount (coreBudget bobAbroad) bobAbroad ⟨"party-bob"⟩
        Commodity.eur).toOption.map (·.val)).getD "") "acc-bob"
  -- ## The attest door makes one purse and adopts nothing
  let joiner := coreSteps twoRealms
    [.addMember { id := ⟨"zoe"⟩, name := "Zoe", party := ⟨"party-zoe"⟩ }]
  let selfGranted := (applyOp joiner ⟨"zoe"⟩ other
    (.grant other ⟨"zoe"⟩ .viewer
      { coreAccount "acc-zoe" "Budget.Hut" .equity with posters := [⟨"zoe"⟩] })).toOption
  r := check r "a self-grant opens the purse named after the member, and nothing else"
    (match selfGranted with
     | some (st, _) =>
       match st.account? ⟨"acc-zoe"⟩ with
       | some a => a.name == "Members.Zoe" && a.kind == .asset && a.posters.isEmpty &&
                   a.bridgeOf == some ⟨"zoe"⟩ && a.mirrorOf.isNone
       | none => false
     | none => false)
  r := check r "and refuses a name that is already an account in that realm"
    (Str.containsCI
      (coreErrorAs "zoe" other
        (inOther [.putAccount (coreAccount "acc-taken" "Members.Zoe" .asset)] |>
          coreSteps <| [.addMember { id := ⟨"zoe"⟩, name := "Zoe", party := ⟨"party-zoe"⟩ }])
        (.grant other ⟨"zoe"⟩ .viewer (coreAccount "acc-zoe" "Members.Zoe" .asset)))
      "already an account")
  -- ## A budget is held in a pot, and a pot is not somebody's purse
  let squatted := coreSteps joiner
    [.grant Realm.selfId ⟨"zoe"⟩ .viewer
      (coreAccount "acc-squat" "Budget.Camp" .equity ⟨"party-zoe"⟩)]
  r := check r "a budget refuses to be opened over somebody's purse"
    (Str.containsCI
      (coreError squatted (.openBudget { id := ⟨"b-camp"⟩, name := "Camp", note := none
                                         closed := false }
        (coreAccount "acc-camp" "Camp" .equity)))
      "purse")
  -- ## Claims
  r := check r "a stored claim is not overwritten by a plain transaction"
    (Str.containsCI
      (coreError (coreSteps coreBase
        [.raiseClaim { id := ⟨"t-c"⟩, date := coreDate, narration := "owed", state := .pending
                       postings := [cents "acc-bank" 500, cents "acc-anna" (-500)] }])
        (.putTransaction (coreTxn "t-c" [cents "acc-bank" 500, cents "acc-anna" (-500)] "no")))
      "not overwritten")
  -- Replaying a log is a function of the log, and of nothing else.
  let accountsPart : List Op :=
    [ .putAccount (coreAccount "acc-x" "Assets.X" .asset)
    , .putAccount (coreAccount "acc-y" "Expenses.Y" .expense) ]
  let namesPart : List Op :=
    [ .putParty { id := ⟨"party-anna"⟩, name := "Anna", kind := "contact" }
    , .putLabel { id := ⟨"lbl-hut"⟩, name := "trip:hut" } ]
  let spend : List Op :=
    [ .putTransaction (coreTxn "t-x" [cents "acc-x" (-500), cents "acc-y" 500] "coffee") ]
  let broken : List Op :=
    [ .putTransaction (coreTxn "t-lost" [cents "acc-x" (-500)] "half an entry") ]
  let log : List Event :=
    [ coreEvent "e1" accountsPart, coreEvent "e2" namesPart
    , coreEvent "e3" spend, coreEvent "e4" broken ]
  let reordered : List Event :=
    [ coreEvent "e2" namesPart.reverse, coreEvent "e1" accountsPart.reverse
    , coreEvent "e3" spend, coreEvent "e4" broken ]
  r := check r "replaying a log twice gives the same state" (state log == state log)
  r := check r "and the order of independent parts does not show" (state log == state reordered)
  r := check r "an invalid part is skipped rather than failing its event"
    (((state log).txn? ⟨"t-lost"⟩).isNone && ((state log).txn? ⟨"t-x"⟩).isSome)
  return coreBudgetTests r

/--
The log, and what it is worth.

The tables are a cache from here on, so the question these ask is whether the
cache could be thrown away: does the log, replayed from nothing, give back the
ledger the suite has just spent a second building? Then the three things that
have to be true for that answer to mean anything — the chain verifies, a byte
changed under it stops verifying, and the first event carries the state the store
opened with, which is what makes a database that predates the log replayable at
all.
-/
private def logTests (ctx : Ctx) (r : Report) : IO Report := do
  let held ← ctx.state.get
  let log ← Replay.events ctx.db
  let replayed ← Replay.state ctx.db
  let (seq, hash) ← EventLog.head ctx.db
  let mut r := check r "replaying the log gives back the state in memory" (replayed == held)
  r := checkEq r "every event in the chain verified" log.size seq
  r := checkEq r "and the head names the last of them" hash.length 64
  r := checkEq r "the replayed state hashes as the one in memory does"
    (Encode.hashState replayed) (Encode.hashState held)
  r := checkEq r "the log starts at sequence 1"
    (← Db.scalarInt ctx.db "SELECT IFNULL(MIN(seq), 0) FROM event") 1
  match log[0]? with
  | none => r := check r "the log starts with a genesis event" false
  | some e =>
    r := checkEq r "genesis is one part" e.parts.length 1
    r := check r "and it is the snapshot the store opened with"
      (match e.parts.head? with | some { op := .snapshot _, .. } => true | _ => false)
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-log-{← freshId}"
  try
    let fresh ← Ctx.open (Config.atDir root)
    -- What a rebuild does: a whole state written onto tables that hold nothing.
    fresh.transaction (Project.all fresh.db replayed)
    r := check r "a replayed state projected onto an empty store reads back as itself"
      ((← Load.fromDb fresh.db) == replayed)
    -- One name, an account of it in each of two realms. `account.name` was
    -- unique over the whole table until migration 25, so this is the write that
    -- a realm arriving from a sequencer used to come apart on: `Core` holds both
    -- accounts — a name is only a name inside a realm — and the store could not
    -- hold what `Core` held.
    let twin ← Ctx.open (Config.atDir (root / "twin"))
    let other : RealmId := ⟨"0000000000000000000000TWIN"⟩
    discard <| twin.commit "test"
      [.createRealm { id := other, name := "Twin", members := [(twin.member, .admin)] }]
    discard <| twin.commit "test"
      [.putAccount { id := ⟨"acc-twin-here"⟩, name := "Budget.Twin", kind := .equity }]
    discard <| twin.commit "test"
      [.putAccount { id := ⟨"acc-twin-there"⟩, name := "Budget.Twin", kind := .equity,
                     realm := other }]
      (realm := other)
    r := checkEq r "one name is an account in each of two realms"
      (← Db.scalarInt twin.db "SELECT COUNT(*) FROM account WHERE name = 'Budget.Twin'") 2
    let back ← Load.fromDb twin.db
    r := checkEq r "and the one written here reads back as itself"
      ((back.accountByNameIn? Realm.selfId "Budget.Twin").map (·.id.val))
      (some "acc-twin-here")
    r := checkEq r "as does the one written in the other realm"
      ((back.accountByNameIn? other "Budget.Twin").map (·.id.val)) (some "acc-twin-there")
    r := check r "and the store reads back as the state it is a projection of"
      (back == (← twin.state.get))
    -- The head is what the next append chains onto, so a head that has drifted
    -- is a store whose next event forks its own history. `Ctx.open` hashes the
    -- rows and asks, every time, and refuses rather than writing onto the fork.
    let reopens : IO Bool := do
      (do discard <| Ctx.open (Config.atDir root); pure true) <|> pure false
    r := check r "a store whose chain is whole opens" (← reopens)
    Db.exec fresh.db
      s!"UPDATE ledger_head SET hash = {Db.lit EventLog.zeroHash} WHERE id = 1"
    r := check r "one whose head names an event that is not the last does not" !(← reopens)
    Db.exec fresh.db
      "UPDATE ledger_head SET hash = (SELECT hash FROM event ORDER BY seq DESC LIMIT 1)
       WHERE id = 1"
    r := check r "and putting the head back on the last event opens it again" (← reopens)
    Db.exec fresh.db "UPDATE ledger_head SET seq = seq + 1 WHERE id = 1"
    r := check r "a head that has run ahead of the log is refused too" !(← reopens)
    Db.exec fresh.db "UPDATE ledger_head SET seq = seq - 1 WHERE id = 1"
    -- The hash covers the stored bytes, so editing them is not a quiet edit.
    Db.exec fresh.db "UPDATE event SET bytes = X'00' WHERE seq = 1"
    let refused ← (do discard <| Replay.events fresh.db; pure false) <|> pure true
    r := check r "a byte changed under the log stops it verifying" refused
    r := check r "and stops the store opening at all" !(← reopens)
    return r
  finally
    IO.FS.removeDirAll root <|> pure ()

/-! ## The conformance vectors -/

/--
The vectors a port is checked against, checked against the core that wrote them.

`resources gen-vectors` hands an unverified implementation the only thing that
can hold it to these semantics: a state, an event, and the bytes the answer comes
to. That is worth nothing unless the vectors are true here first — so every one
is taken apart the way a port would take it apart, stepped, and hashed, and the
hash has to be the one the vector carries.

Decoding is not the identity on a `State`: the maps come back rebuilt from their
sorted entries, which is exactly what `State.ofBytes_toBytes` says and no more.
So this also says that stepping a rebuilt state lands on the same bytes as
stepping the state it was rebuilt from — the property the whole file rests on,
and the one a port cannot check for us.
-/
private def vectorTests (r : Report) : Report := Id.run do
  let mut r := r
  let vs := Api.Vectors.vectors
  r := check r "there are at least sixty conformance vectors" (vs.length ≥ 60)
  r := checkEq r "every state a vector starts from was reached by applying operations"
    (String.intercalate "; " Api.Vectors.setupErrors) ""
  r := checkEq r "and every scenario is refused exactly where it says it is"
    (String.intercalate "; " Api.Vectors.misfits) ""
  r := checkEq r "the vectors are named uniquely" (vs.map (·.name)).eraseDups.length vs.length
  -- The other half of what the shared artefacts pin. Every vector above is a
  -- well-formed input, so a third implementation could reproduce all of them
  -- while accepting bytes no writer produces — and a checkpoint is a name for
  -- bytes, so a decoder that takes two spellings of one state is a decoder two
  -- honest peers disagree through. `conformance/rejects.json` is generated from
  -- this same list, so a port and this core are held to one set of refusals.
  let rjs := Api.Vectors.rejects
  r := check r "there are rejections for every shape the decoder has to refuse" (rjs.length ≥ 15)
  r := checkEq r "the rejections are named uniquely"
    (rjs.map (·.name)).eraseDups.length rjs.length
  r := checkEq r "and this core refuses every one of them"
    (String.intercalate "; " Api.Vectors.rejectMisfits) ""
  for v in vs do
    match Api.Vectors.ofHex? v.stateHex, Api.Vectors.ofHex? v.eventHex with
    | some stateBytes, some eventBytes =>
      match Codec.decode (α := State) stateBytes, Codec.decode (α := Event) eventBytes with
      | some s, some e =>
        let (out, _) := step s e
        r := checkEq r s!"vector {v.name} steps to the bytes it says it does"
          (toHex (Codec.encode out)) v.expectedHex
        r := checkEq r s!"vector {v.name} steps to the hash it says it does"
          (Encode.hashState out) v.expectedHash
      | _, _ => r := check r s!"vector {v.name} decodes" false
    | _, _ => r := check r s!"vector {v.name} is written in hex" false
  return r

/-! ## Entry point -/

def main : IO UInt32 := do
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-test-{← freshId}"
  try
    let ctx ← Ctx.open (Config.atDir root)
    let mut r : Report := {}
    r := moneyTests r
    r := rfTests r
    r := invoiceTests r
    r := filterParseTests r
    r := ledgerTests r
    r := coreTests r
    r := encodeTests r
    r := vectorTests r
    let corpus ← seedCorpus ctx 200
    IO.println s!"seeded {corpus.size} transactions"
    r ← filterAgreement ctx corpus r
    r ← sortOrdering ctx r
    r ← importIdempotence ctx r
    r ← agree ctx r
    r ← trialBalance ctx r
    r ← routeSmoke ctx r
    r ← agree ctx r
    r ← syncTests r
    r ← cryptoTests r
    r ← nodeTests r
    r ← nodeHardeningTests r
    r ← headlineTests ctx r
    r ← agree ctx r
    r := signatureTests r
    r ← mergeTests ctx r
    r ← agree ctx r
    r ← migrationTests r
    r := settleTests r
    r ← purseTests ctx r
    r ← agree ctx r
    r ← realmTests ctx r
    r ← agree ctx r
    r ← resettleTests ctx r
    r ← agree ctx r
    r := biproportionalTests r
    r ← closeTests ctx r
    r ← agree ctx r
    r ← topUpTests ctx r
    r ← agree ctx r
    r ← invoiceFromTxnTests ctx r
    r ← agree ctx r
    r ← splitAndTripTests ctx r
    r ← agree ctx r
    r := receiptTests r
    r ← divideTests ctx r
    r ← agree ctx r
    r ← sharedBudgetTests ctx r
    r ← agree ctx r
    r ← workflowTests ctx r
    r ← agree ctx r
    r ← contactTests ctx r
    r ← agree ctx r
    r ← logTests ctx r
    for failure in r.failed do
      IO.eprintln s!"FAIL  {failure}"
    IO.println s!"{r.passed} passed, {r.failed.size} failed"
    return if r.failed.isEmpty then 0 else 1
  finally
    IO.FS.removeDirAll root <|> pure ()
