import Resources.Api.Routes

/-!
# Tests

The interesting one is `filterAgreement`: `Filter.eval` is the reference
semantics over in-memory transactions and `Filter.toSql` is the fast path, and
proving the compiler sound against SQLite's semantics is out of reach. Checking
that the two agree on a generated corpus is not, and it catches every bug you
would actually write.
-/

open Lean Resources

/-! ## Harness -/

private structure Report where
  passed : Nat := 0
  failed : Array String := #[]

private def check (r : Report) (name : String) (ok : Bool) : Report :=
  if ok then { r with passed := r.passed + 1 }
  else { r with failed := r.failed.push name }

private def checkEq [BEq α] [ToString α] (r : Report) (name : String) (actual expected : α) :
    Report :=
  if actual == expected then { r with passed := r.passed + 1 }
  else { r with failed := r.failed.push s!"{name}: got {actual}, expected {expected}" }

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
What a share link can reach.

The property worth testing is not that some particular route is refused — it is
that the reachable set is small and fixed. A guest sees one budget, posts to one
account of their own, and everything else is a 404, including routes that exist
for you.
-/
private def guestTests (ctx : Ctx) (r : Report) : IO Report := do
  let mut r := r
  let budget ← Budgets.open ctx "Shared"
  let guestParty ← Parties.contact ctx "carla"
  let g : Guest := { owner := guestParty.id, budget := budget.id }
  let caller : Api.Caller := { actor := "tok-guest", scopes := Scopes.none, guest := some g }
  let reply (m : String) (segs : List String) (body : Json := Json.mkObj []) : IO Api.Reply :=
    Api.handleSafe ctx caller ((Api.Req.simple m segs).withJson body)
  -- Everything the ordinary table offers is simply not there.
  for (m, segs) in [("GET", ["accounts"]), ("GET", ["transactions"]), ("GET", ["budgets"]),
                    ("GET", ["reports", "people"]), ("GET", ["tokens"]),
                    ("GET", ["contacts"]), ("GET", ["invoices"])] do
    r := checkEq r s!"a guest cannot {m} /{String.intercalate "/" segs}"
      (← reply m segs).code 404
  -- What they can do: see the budget, and add what they paid for.
  let seen ← reply "GET" ["guest"]
  r := checkEq r "a guest can see the budget the link names" seen.code 200
  match seen.json? with
  | none => r := check r "the guest view is JSON" false
  | some j =>
    r := checkEq r "and is told who they are"
      ((j.getObjValAs? String "you").toOption.getD "") "carla"
    r := check r "and nothing in it names an account of yours"
      (!Str.containsCI j.compress "Assets.Bank")
  let added ← reply "POST" ["guest", "expenses"]
    (Json.mkObj [("amount", "42.50"), ("narration", "the taxi"), ("payee", "Taxi"),
                 ("date", "2026-07-08")])
  r := checkEq r "a guest can add what they paid for" added.code 201
  r := checkEq r "and it reaches the budget" (← Budgets.balance ctx budget).minor 4250
  -- It reached the budget without any of it being yours.
  let carlaPurse ← Accounts.purse ctx guestParty
  r := checkEq r "out of their own account and nobody else's"
    (Ledger.balance (← Txns.list ctx .all {} 10000).toList carlaPurse.id "EUR") (-4250)
  -- Withdrawing their own is allowed; withdrawing anybody else's is a 404,
  -- which is the same answer as for a transaction that does not exist.
  let mineToo : Transaction :=
    { id := ⟨"guest-mine"⟩, date := (Date.ofIso? "2026-07-08").getD default
      narration := "yours"
      postings := [{ account := (← Accounts.ensure ctx "Assets.Bank.Guest").id,
                     amount := ⟨Commodity.eur, -100⟩ },
                   { account := (← Budgets.account ctx budget).id,
                     amount := ⟨Commodity.eur, 100⟩ }] }
  match mineToo.validate with
  | .error _ => r := check r "guest fixture balances" false
  | .ok bt => Txns.put ctx bt "test"
  r := checkEq r "a guest cannot withdraw a cost of yours"
    (← reply "DELETE" ["guest", "expenses", "guest-mine"]).code 404
  r := checkEq r "and it is still there" (← Budgets.balance ctx budget).minor 4350
  -- Inviting somebody to one budget must not be read as "authentication is set
  -- up now". It would lock you out of your own client as a side effect, and it
  -- closes nothing that having no tokens at all had left open.
  let (_, _) ← Tokens.create ctx "share" (Scopes.ofList [.read, .write]) none (some g)
  r := check r "a share link is a token" (← Tokens.any ctx)
  r := check r "but not one of your own, so the API stays as open as it was"
    (!(← Tokens.anyOwn ctx))
  let (_, _) ← Tokens.create ctx "mine" (Scopes.ofList [.admin])
  r := check r "minting one of your own is what locks it down" (← Tokens.anyOwn ctx)
  -- The order the server reads these in is the whole of the guarantee. A token
  -- that was presented has to decide who the caller is *before* the
  -- open-by-default rule is consulted, or a share link handed over while the
  -- API is still open would come back as the bootstrap caller — full access,
  -- from the one credential that exists to grant almost none.
  let stillGuest : Api.Caller := { actor := "tok", scopes := Scopes.none, guest := some g }
  r := checkEq r "a share link is confined however open the API is"
    (← Api.handleSafe ctx stillGuest (Api.Req.simple "GET" ["accounts"])).code 404
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
  Db.exec ctx.db s!"INSERT OR IGNORE INTO attachment (sha256, mime, bytes, created_at)
                    VALUES ({Db.lit sha}, 'application/pdf', 1, '2026-08-06T00:00:00')"
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
  Db.exec ctx.db s!"INSERT OR IGNORE INTO attachment (sha256, mime, bytes, created_at)
                    VALUES ({Db.lit sha2}, 'application/pdf', 1, '2026-08-01T00:00:00')"
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
  let overclaim ← try
    let _ ← Receipts.divideByItems ctx (split[0]!).id
      [{ items := [{ line := 1, qty := some 99 }], into := "Expenses.Bunk.Mine" }] "test"
    pure false
  catch _ => pure true
  r := check r "claiming more units than a line covers is refused" overclaim
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
  let before ← Db.scalarInt ctx.db
    s!"SELECT value FROM counter WHERE name = {Db.lit s!"invoice:{year}"}"
  let scratch ← Invoices.create ctx "typo" [{ description := "x", qtyMilli := 1000, unitPrice := ⟨eur, 100⟩ }]
    (.link "https://example.org") ((Date.ofIso? "2026-07-10").getD default)
    ((Date.ofIso? "2026-08-01").getD default) eur
  Invoices.delete ctx scratch.id
  let after ← Db.scalarInt ctx.db
    s!"SELECT value FROM counter WHERE name = {Db.lit s!"invoice:{year}"}"
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
    (← Db.scalarInt ctx.db s!"SELECT value FROM counter WHERE name = {Db.lit s!"invoice:{year}"}")
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
    let corpus ← seedCorpus ctx 200
    IO.println s!"seeded {corpus.size} transactions"
    r ← filterAgreement ctx corpus r
    r ← sortOrdering ctx r
    r ← importIdempotence ctx r
    r ← trialBalance ctx r
    r ← routeSmoke ctx r
    r ← headlineTests ctx r
    r := signatureTests r
    r ← mergeTests ctx r
    r ← migrationTests r
    r := settleTests r
    r ← purseTests ctx r
    r ← guestTests ctx r
    r ← resettleTests ctx r
    r := biproportionalTests r
    r ← closeTests ctx r
    r ← topUpTests ctx r
    r ← invoiceFromTxnTests ctx r
    r ← splitAndTripTests ctx r
    r := receiptTests r
    r ← divideTests ctx r
    r ← workflowTests ctx r
    r ← contactTests ctx r
    for failure in r.failed do
      IO.eprintln s!"FAIL  {failure}"
    IO.println s!"{r.passed} passed, {r.failed.size} failed"
    return if r.failed.isEmpty then 0 else 1
  finally
    IO.FS.removeDirAll root <|> pure ()
