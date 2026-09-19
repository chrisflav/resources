import Cli
import Resources.Cli.Client
import Resources.Api.Server
import Resources.Api.TsGen
import Resources.Api.Vectors
import Resources.Sync.Server
import Resources.Node.Realms
import Resources.Node.Rekey
import Resources.Node.Blobs
import Resources.Crypto.Sodium

/-!
# Command line

Every command is a thin shell over `Backend.call`, so `resources tx list` does
exactly what `GET /api/v1/transactions` does, whether it is talking to the local
database or to a server over HTTP.
-/

open Lean Cli

namespace Resources
namespace Cli

/-! ## Output helpers -/

/-- A flag's string value, if it was given. -/
def flagStr? (p : Parsed) (name : String) : Option String :=
  (p.flag? name).map (fun f => f.as! String)

/-- A flag's string value, or a default. -/
def flagStr (p : Parsed) (name : String) (dflt : String) : String :=
  (flagStr? p name).getD dflt

/-- A repeated flag's values. -/
def flagList (p : Parsed) (name : String) : List String :=
  match p.flag? name with
  | some f => (f.as! (Array String)).toList
  | none => []

/-- A required positional argument. -/
def argStr (p : Parsed) (name : String) : String :=
  p.positionalArg! name |>.as! String

/-- A field of a JSON object rendered as text; numbers and booleans included. -/
def jstr (j : Json) (key : String) : String :=
  match j.getObjVal? key with
  | .ok (.str s) => s
  | .ok (.num n) => toString n
  | .ok (.bool b) => toString b
  | _ => ""

/-- A nested field. -/
def jobj (j : Json) (key : String) : Json :=
  (j.getObjVal? key).toOption.getD Json.null

/-- A JSON array as a list. -/
def jarr (j : Json) : Array Json :=
  match j with
  | .arr a => a
  | _ => #[]

/-- Prints a table with aligned columns. -/
def printTable (headers : Array String) (rows : Array (Array String))
    (rightAlign : Array Nat := #[]) : IO Unit := do
  if rows.isEmpty then
    IO.println "(nothing)"
    return
  let n := headers.size
  let mut widths := headers.map (·.length)
  for row in rows do
    for i in [0:n] do
      let w := (row[i]?.getD "").length
      if w > widths[i]! then widths := widths.set! i w
  let pad (i : Nat) (s : String) : String :=
    if rightAlign.contains i then Str.padLeft s widths[i]! else Str.padRight s widths[i]!
  let line (cells : Array String) : String :=
    String.intercalate "  " ((List.range n).map (fun i => pad i (cells[i]?.getD "")))
  IO.println (line headers)
  IO.println (String.ofList (List.replicate
    ((widths.foldl (· + ·) 0) + 2 * (n - 1)) '-'))
  for row in rows do
    IO.println (line row)

/-- Opens the configured backend and runs an action, reporting errors on stderr. -/
def withBackend (f : Backend → IO Unit) : IO UInt32 := do
  try
    let cfg ← ClientConfig.load
    let b ← Backend.open? cfg
    -- A local store writes as whoever `sync.json` says this node is, so that the
    -- events it composes are authored by the key that will sign them.
    let b ← match b with
      | .direct ctx => pure (Backend.direct (← Node.adopt ctx))
      | remote => pure remote
    f b
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

/-- Opens the local store directly; used by commands that cannot go over HTTP. -/
def withLocal (f : Ctx → IO Unit) (verifyChain : Bool := true) : IO UInt32 := do
  try
    let cfg ← ClientConfig.load
    let storeCfg ←
      match cfg.dataDir with
      | some d => pure (Config.atDir (System.FilePath.mk d))
      | none => Config.default
    f (← Node.adopt (← Ctx.open storeCfg verifyChain))
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

/--
The figure a person recognises. The server nets the postings per account, so a
purchase merged with its fee shows one combined amount rather than either leg.
-/
private def headlineAmount (t : Json) : String :=
  let amt := jobj (jobj t "headline") "amount"
  let text := jstr amt "text"
  if text.isEmpty then "" else text ++ " " ++ jstr amt "commodity"

private def accountsOf (t : Json) : String :=
  String.intercalate " / " ((jarr (jobj t "postings")).toList.map (fun p => jstr p "account"))

/-! ## Transactions -/

/-- Handler for `tx list`. -/
def runTxList (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["transactions"]
    [("filter", flagStr p "filter" ""), ("sort", flagStr p "sort" "-date"),
     ("limit", flagStr p "limit" "50"), ("offset", flagStr p "offset" "0")])
  if p.hasFlag "json" then
    IO.println j.pretty
    return
  let items := jarr (jobj j "items")
  printTable #["date", "payee", "narration", "amount", "accounts", "id"]
    (items.map fun t => #[
      jstr t "date", Str.clamp (jstr t "payee") 24, Str.clamp (jstr t "narration") 34,
      headlineAmount t, Str.clamp (accountsOf t) 46, jstr t "id"])
    (rightAlign := #[3])
  let total := ((j.getObjValAs? Int "total").toOption).getD 0
  IO.println s!"\n{items.size} of {total} matching {jstr j "filter"}"

/-- Handler for `tx add`. -/
def runTxAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let amountStr := flagStr p "amount" ""
  if amountStr.isEmpty then throw <| IO.userError "--amount is required"
  let amount ← IO.ofExcept (Amount.parse amountStr)
  let from_ := flagStr p "from" ""
  if from_.isEmpty then throw <| IO.userError "--from is required"
  let to_ := flagStr? p "to"
  let today ← Date.today
  let date :=
    match flagStr? p "date" with
    | some "today" => today.toIso
    | some d => d
    | none => today.toIso
  let posting (account : String) (a : Amount) : Json :=
    Json.mkObj [("account", account), ("minor", Json.num (JsonNumber.fromInt a.minor)),
                ("commodity", a.commodity.code)]
  let postings :=
    match to_ with
    | some t => #[posting from_ (-amount), posting t amount]
    | none => #[posting from_ (-amount)]
  let mut body := Json.mkObj [
    ("date", date), ("payee", flagStr p "payee" ""), ("narration", flagStr p "narration" ""),
    ("labels", Json.arr ((flagList p "label").map Json.str).toArray),
    ("postings", Json.arr postings)]
  if to_.isNone then
    body := body.setObjVal! "balanceInto" (Json.str (flagStr p "into" "Expenses.Unclassified"))
  let j ← b.json (Call.post ["transactions"] body)
  IO.println s!"{jstr j "id"}  {jstr j "date"}  {headlineAmount j}"

/-- Handler for `tx show`. -/
def runTxShow (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["transactions", argStr p "id"])
  if p.hasFlag "json" then IO.println j.pretty; return
  IO.println s!"{jstr j "date"}  {jstr j "payee"}"
  IO.println s!"  {jstr j "narration"}"
  IO.println s!"  source: {jstr j "source"}"
  for post in jarr (jobj j "postings") do
    let amt := jobj post "amount"
    let acc := Str.padRight (jstr post "account") 34
    let text := Str.padLeft (jstr amt "text") 12
    IO.println s!"  {acc} {text} {jstr amt "commodity"}"
  let labels := (jarr (jobj j "labels")).map (fun l => l.getStr?.toOption.getD "")
  if !labels.isEmpty then IO.println s!"  labels: {String.intercalate ", " labels.toList}"
  let atts := (jarr (jobj j "attachments")).map (fun l => l.getStr?.toOption.getD "")
  for a in atts do
    IO.println s!"  receipt: {a}"
  -- What this one paid for, when it is a part of a division and so paid for only
  -- some of the page it hangs on. These are the numbers `tx divide` counts by:
  -- a part is divided again by its own lines, not by the whole receipt.
  for (it, i) in (jarr (jobj j "items")).zipIdx do
    let what := Str.clamp (jstr it "description") 40
    let qty := jstr it "qty"
    let count := if qty.isEmpty || qty == "1" then "" else s!"{qty} × "
    IO.println s!"  line {i + 1}: {count}{what}  {jstr (jobj it "amount") "text"}"

/-- Handler for `tx edit`: changes the date, payee or narration in place. -/
def runTxEdit (p : Parsed) : IO UInt32 := withBackend fun b => do
  let id := argStr p "id"
  let fields := [("date", "date"), ("payee", "payee"), ("narration", "narration")].filterMap
    fun (flag, key) => (flagStr? p flag).map (fun v => (key, Json.str v))
  if fields.isEmpty then
    throw <| IO.userError "give at least one of --date, --payee or --narration"
  let body := Json.mkObj fields
  let j ← b.json (Call.patch ["transactions", id] body)
  IO.println s!"{jstr j "date"}  {jstr j "payee"}  {jstr j "narration"}"

/--
Handler for `tx move`: rebooks a posting from one account to another. This is
how a transaction gets recategorised — the amounts do not change, only which
account the leg lands in, so the transaction stays balanced by construction.
-/
def runTxMove (p : Parsed) : IO UInt32 := withBackend fun b => do
  let id := argStr p "id"
  let target := argStr p "to"
  let current ← b.json (Call.get ["transactions", id])
  let postings := jarr (jobj current "postings")
  let source := flagStr? p "from"
  -- Without --from, move the leg that is not on a balance-sheet account: the
  -- category side, which is the one anybody actually wants to change.
  let onSourceLeg (post : Json) : Bool :=
    match source with
    | some acc => jstr post "account" == acc
    | none => jstr post "kind" != "asset" && jstr post "kind" != "liability"
  let hits := postings.filter onSourceLeg
  if hits.isEmpty then
    throw <| IO.userError <|
      match source with
      | some acc => s!"no posting in {acc}; this transaction touches " ++
          String.intercalate ", " (postings.toList.map (fun x => jstr x "account"))
      | none => "every posting is on a balance-sheet account; say which with --from"
  if hits.size > 1 && source.isNone then
    throw <| IO.userError "more than one posting could move; say which with --from"
  let rewritten := postings.map fun post =>
    if onSourceLeg post then
      Json.mkObj [("account", target),
                  ("minor", Json.num (JsonNumber.fromInt
                    (((jobj post "amount").getObjValAs? Int "minor").toOption.getD 0))),
                  ("commodity", jstr (jobj post "amount") "commodity"),
                  ("note", Json.str (jstr post "note"))]
    else
      Json.mkObj [("account", jstr post "account"),
                  ("minor", Json.num (JsonNumber.fromInt
                    (((jobj post "amount").getObjValAs? Int "minor").toOption.getD 0))),
                  ("commodity", jstr (jobj post "amount") "commodity"),
                  ("note", Json.str (jstr post "note"))]
  let j ← b.json (Call.patch ["transactions", id]
    (Json.mkObj [("postings", Json.arr rewritten)]))
  for post in jarr (jobj j "postings") do
    IO.println s!"  {jstr post "account"}  {jstr (jobj post "amount") "text"}"

/-- Handler for `tx label`: adds or removes labels, leaving the rest alone. -/
def runTxLabel (p : Parsed) : IO UInt32 := withBackend fun b => do
  let id := argStr p "id"
  let add := flagList p "add"
  let remove := flagList p "rm"
  if add.isEmpty && remove.isEmpty then
    throw <| IO.userError "give at least one --add or --rm"
  let current ← b.json (Call.get ["transactions", id])
  let existing := (jarr (jobj current "labels")).toList.map (fun l => l.getStr?.toOption.getD "")
  let kept := existing.filter (fun l => !remove.contains l)
  let final := kept ++ add.filter (fun l => !kept.contains l)
  let j ← b.json (Call.patch ["transactions", id]
    (Json.mkObj [("labels", Json.arr (final.map Json.str).toArray)]))
  let now := (jarr (jobj j "labels")).toList.map (fun l => l.getStr?.toOption.getD "")
  IO.println (if now.isEmpty then "(no labels)" else String.intercalate ", " now)

/--
Handler for `tx merge`: combines several transactions into one.

Balance is preserved by construction — the result's postings are the sources'
postings concatenated — so this can never leave the ledger inconsistent.
-/
def runTxMerge (p : Parsed) : IO UInt32 := withBackend fun b => do
  let ids := p.variableArgsAs! String
  if ids.size < 2 then throw <| IO.userError "give at least two transaction ids"
  let mut body := Json.mkObj [("ids", Json.arr (ids.map Json.str))]
  match flagStr? p "narration" with
  | some n => body := body.setObjVal! "narration" (Json.str n)
  | none => pure ()
  match flagStr? p "payee" with
  | some n => body := body.setObjVal! "payee" (Json.str n)
  | none => pure ()
  let cancel := flagList p "cancel"
  if !cancel.isEmpty then
    body := body.setObjVal! "cancelIn" (Json.arr (cancel.map Json.str).toArray)
  let j ← b.json (Call.post ["transactions", "merge"] body)
  IO.println s!"{jstr j "id"}  {jstr j "date"}  {headlineAmount j}"
  for post in jarr (jobj j "postings") do
    let amount := Str.padLeft (jstr (jobj post "amount") "text") 12
    IO.println s!"  {Str.padRight (jstr post "account") 34} {amount}"

/-- Handler for `tx unmerge`: splits a merged transaction back into its sources. -/
def runTxUnmerge (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["transactions", argStr p "id", "unmerge"] (Json.mkObj []))
  for t in jarr j do
    IO.println s!"{jstr t "id"}  {jstr t "date"}  {headlineAmount t}"

/--
Handler for `tx link`: finds fee transactions already in the ledger that belong
with a purchase, and combines them. Prints what it would do unless `--apply`.
-/
def runTxLink (p : Parsed) : IO UInt32 := withBackend fun b => do
  let proposals ← b.json (Call.get ["transactions", "link-proposals"])
  let items := jarr proposals
  if items.isEmpty then
    IO.println "nothing looks like a split event"
    return
  printTable #["confidence", "date", "purchase", "amount", "fee", "why"]
    (items.map fun x =>
      let parent := jobj x "parent"
      let child := jobj x "child"
      #[jstr x "confidence", jstr parent "date",
        Str.clamp (jstr parent "payee") 26,
        jstr (jobj (jobj parent "headline") "amount") "text",
        jstr (jobj (jobj child "headline") "amount") "text",
        Str.clamp (jstr x "reason") 46])
    (rightAlign := #[3, 4])
  if !p.hasFlag "apply" then
    IO.println s!"\n{items.size} pair(s) would be combined. Re-run with --apply to do it."
    return
  let body := match flagStr? p "confidence" with
    | some c => Json.mkObj [("confidence", Json.str c)]
    | none => Json.mkObj []
  let j ← b.json (Call.post ["transactions", "link"] body)
  let n := jstr j "merged"
  IO.println s!"\ncombined {n} pair(s); undo any of them with resources tx unmerge <id>"

/--
Handler for `claim`: books transactions as somebody else's spending.

The same verb covers both directions. An outlay's expense leg moves into their
purse, raising what they owe; a reimbursement's income leg moves into the same
purse, reducing it. When the two balance you are square — and because the purse
belongs to them, none of it was ever counted as yours.
-/
def runClaim (p : Parsed) : IO UInt32 := withBackend fun b => do
  let who := argStr p "who"
  let ids := p.variableArgsAs! String
  let body :=
    if ids.isEmpty then
      match flagStr? p "filter" with
      | some f => Json.mkObj [("who", Json.str who), ("filter", Json.str f)]
      | none => panic! "unreachable"
    else Json.mkObj [("who", Json.str who), ("ids", Json.arr (ids.map Json.str))]
  if ids.isEmpty && (flagStr? p "filter").isNone then
    throw <| IO.userError "give transaction ids, or a --filter selecting them"
  let j ← b.json (Call.post ["transactions", "claim"] body)
  IO.println s!"moved {jstr j "count"} transactions into {jstr j "into"}"

/-- Handler for `invoice mail`: hands a cost overview to whoever owes it. -/
def runInvoiceMail (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["invoices", argStr p "id", "mailto"])
  let url := jstr j "mailto"
  if p.hasFlag "open" then
    discard <| IO.Process.output { cmd := "xdg-open", args := #[url] }
    IO.println "opened in your mail client"
  else
    IO.println url

/-- Handler for `party import`: reads contacts out of a vCard file. -/
def runPartyImport (p : Parsed) : IO UInt32 := withBackend fun b => do
  let bytes ← IO.FS.readBinFile (argStr p "file")
  let j ← b.json
    { method := "POST", path := ["parties", "import"], body := bytes
      headers := [("content-type", "text/vcard")] }
  IO.println s!"read {jstr j "read"} contact(s): {jstr j "created"} new, {jstr j "updated"} updated"

/--
Handler for `report people`.

What passes between you and everybody else. Their own accounts carry the figure
and its sign says which way it runs; what is outstanding is the claims, each of
which names one specific thing rather than being aged against the oldest outlay.
-/
def runReportPeople (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["reports", "people"])
  let rows := jarr j
  let rows := if p.hasFlag "open" then rows.filter (fun x => jstr x "net" != "0") else rows
  if rows.isEmpty then
    IO.println "nothing passes between you and anybody"
    return
  printTable #["person", "net", "outstanding claims"]
    (rows.map fun x => #[
      jstr x "name", jstr x "netText",
      toString (jarr (jobj x "claims")).size])
    (rightAlign := #[1, 2])
  IO.println "\na positive net is money they owe you; negative is money you owe them"
  if p.hasFlag "items" then
    for x in rows do
      let claims := jarr (jobj x "claims")
      if claims.isEmpty then continue
      IO.println s!"\n{jstr x "name"} — outstanding:"
      printTable #["due", "from", "to", "amount", "what"]
        (claims.map fun c => #[
          jstr c "due", jstr c "from", jstr c "to",
          jstr (jobj c "amount") "text", Str.clamp (jstr c "narration") 40])
        (rightAlign := #[3])

/-- Handler for `tag fees`. -/
def runTagFees (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["postings", "tag-fees"] (Json.mkObj []))
  IO.println s!"tagged {jstr j "tagged"} postings as fees"

/--
Handler for `split`: shares costs across a group of people.

Takes transaction ids or a filter, so a weekend's worth of receipts is one
command rather than one per receipt.
-/
def runSplit (p : Parsed) : IO UInt32 := withBackend fun b => do
  let among := flagList p "among"
  let group := flagStr? p "group"
  if among.isEmpty && group.isNone then
    throw <| IO.userError "say who to split with: --among anna,ben or --group hut-crew"
  let ids := p.variableArgsAs! String
  let filter := flagStr? p "filter"
  if ids.isEmpty && filter.isNone then
    throw <| IO.userError "give transaction ids, or a --filter selecting them"
  let mut body := Json.mkObj [("keepShare", Json.bool (!p.hasFlag "all-theirs"))]
  match group with
  | some g => body := body.setObjVal! "group" (Json.str g)
  | none => body := body.setObjVal! "among" (Json.arr (among.map Json.str).toArray)
  if ids.isEmpty then
    body := body.setObjVal! "filter" (Json.str (filter.getD ""))
  else
    body := body.setObjVal! "ids" (Json.arr (ids.map Json.str))
  let j ← b.json (Call.post ["transactions", "split"] body)
  let people := (jarr (jobj j "among")).toList.map (fun x => x.getStr?.toOption.getD "")
  IO.println s!"split {jstr j "count"} transaction(s) with {String.intercalate ", " people}"
  IO.println ""
  printTable #["date", "payee", "each share goes to", "amount"]
    ((jarr (jobj j "items")).flatMap fun t =>
      ((jarr (jobj t "postings")).filter fun post =>
        jstr post "mine" != "true").map fun post =>
          #[jstr t "date", Str.clamp (jstr t "payee") 26,
            jstr post "owner", jstr (jobj post "amount") "text"])
    (rightAlign := #[3])

/-- Handler for `move`: gathers selected spending into one account. -/
def runMove (p : Parsed) : IO UInt32 := withBackend fun b => do
  let ids := p.variableArgsAs! String
  let filter := flagStr? p "filter"
  if ids.isEmpty && filter.isNone then
    throw <| IO.userError "give transaction ids, or a --filter selecting them"
  let mut body := Json.mkObj [("into", Json.str (argStr p "into")),
                              ("funding", Json.bool (p.hasFlag "fund"))]
  if ids.isEmpty then body := body.setObjVal! "filter" (Json.str (filter.getD ""))
  else body := body.setObjVal! "ids" (Json.arr (ids.map Json.str))
  let j ← b.json (Call.post ["transactions", "move"] body)
  IO.println s!"moved {jstr j "count"} transaction(s) into {jstr j "into"}"

/-- Reads one `name=account` or `name=account*weight` spec. -/
private def bearerSpec (spec : String) : Json :=
  let (who, rest) :=
    match spec.splitOn "=" with
    | [one] => ("", one)
    | who :: more => (who, String.intercalate "=" more)
    | [] => ("", "")
  let (account, weight) :=
    match rest.splitOn "*" with
    | [a, w] => (a, (w.toNat?).getD 1)
    | _ => (rest, 1)
  Json.mkObj [("name", Json.str who.trimAscii.toString),
              ("account", Json.str account.trimAscii.toString),
              ("weight", Json.num (JsonNumber.fromNat weight))]

/-- Handler for `budget new`. -/
def runBudgetNew (p : Parsed) : IO UInt32 := withBackend fun b => do
  let ids := flagList p "txn"
  let among := (flagList p "among").map bearerSpec
  let mut body := Json.mkObj [("name", Json.str (argStr p "name"))]
  if !among.isEmpty then
    body := body.setObjVal! "among" (Json.arr among.toArray)
  match flagStr? p "note" with
  | some n => body := body.setObjVal! "note" (Json.str n)
  | none => pure ()
  if !ids.isEmpty then
    body := body.setObjVal! "transactions" (Json.arr (ids.map Json.str).toArray)
  let j ← b.json (Call.post ["budgets"] body)
  IO.println s!"{jstr j "name"} — lent {jstr j "lent"} cost(s)"

/-- Handler for `budget list`. -/
def runBudgetList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["budgets"])
  printTable #["budget", "state", "costs", "undivided", "divided", "outstanding"]
    ((jarr j).map fun g => #[jstr g "shortName",
      (if jstr g "closed" == "true" then "closed" else "open"), jstr g "costs",
      jstr (jobj g "outstanding") "text", jstr (jobj g "allocated") "text",
      toString ((jarr (jobj g "claims")).filter (fun c => jstr c "state" == "pending")).size])
    (rightAlign := #[2, 3, 4, 5])

/-- Prints where everybody stands and what has been asked of them. -/
private def printDivision (g : Json) : IO Unit := do
  let standings := jarr (jobj g "standings")
  if !standings.isEmpty then
    -- Positive is what they still have to find; negative is what they fronted
    -- above their own share, which is what the group owes them.
    printTable #["person", "borne less put in", "position"]
      (standings.map fun st => #[
        jstr st "name", jstr (jobj st "amount") "text",
        if jstr (jobj st "amount") "minor" == "0" then "square"
        else if jstr st "owes" == "true" then "owes the others"
        else "is owed"])
      (rightAlign := #[1])
  let claims := (jarr (jobj g "claims")).filter fun c => jstr c "state" == "pending"
  if claims.isEmpty then
    IO.println "\nnothing outstanding"
  else
    IO.println ""
    printTable #["due", "from", "to", "amount", "claim"]
      (claims.map fun c => #[
        jstr c "due", jstr c "from", jstr c "to", jstr (jobj c "amount") "text", jstr c "id"])
      (rightAlign := #[3])

/-- Handler for `budget show`. -/
def runBudgetShow (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["budgets", argStr p "name"])
  let g := jobj j "budget"
  IO.println s!"{jstr g "name"}  ({if jstr g "closed" == "true" then "closed" else "open"})"
  IO.println s!"  undivided  {jstr (jobj g "outstanding") "text"}"
  IO.println s!"  divided    {jstr (jobj g "allocated") "text"}"
  IO.println ""
  printTable #["date", "what", "paid from", "amount"]
    ((jarr (jobj j "items")).map fun t => #[
      jstr t "date", Str.clamp (if (jstr t "payee").isEmpty then jstr t "narration"
                                else jstr t "payee") 34,
      jstr (jobj t "headline") "account", jstr (jobj (jobj t "headline") "amount") "text"])
    (rightAlign := #[3])
  IO.println ""
  printDivision g

/--
Handler for `budget among`: records once who a budget is divided among.

Nothing is divided here. Dividing is what closing does, and closing is
deliberate — until then costs simply accumulate in the account, which is the
whole reason the account exists.
-/
def runBudgetAmong (p : Parsed) : IO UInt32 := withBackend fun b => do
  let among := (p.variableArgsAs! String).toList.map bearerSpec
  if among.isEmpty then
    throw <| IO.userError "say who shares it, as name=account"
  let j ← b.json (Call.post ["budgets", argStr p "name", "among"]
    (Json.mkObj [("among", Json.arr among.toArray)]))
  let who := (jarr (jobj j "among")).toList.map fun x =>
    (if jstr x "mine" == "true" then "me" else jstr x "name") ++
      (if jstr x "weight" == "1" then "" else "×" ++ jstr x "weight")
  IO.println s!"{jstr j "budget"} is shared between {String.intercalate ", " who}"
  let waiting := jstr (jobj j "undivided") "text"
  IO.println s!"{waiting} is waiting; `budget close {argStr p "name"}` divides it"

/--
Handler for `budget close`: divides everything waiting and asks for the rest.

Closing again after reopening writes a new division covering only what came in
since; the earlier ones stand, because somebody was told what they owed on the
strength of them.
-/
def runBudgetClose (p : Parsed) : IO UInt32 := withBackend fun b => do
  let among := (p.variableArgsAs! String).toList.map bearerSpec
  let mut body := Json.mkObj [("commodity", Json.str (flagStr p "commodity" "EUR"))]
  if !among.isEmpty then body := body.setObjVal! "among" (Json.arr among.toArray)
  match flagStr? p "through" with
  | some h => body := body.setObjVal! "through" (Json.str h)
  | none => pure ()
  let j ← b.json (Call.post ["budgets", argStr p "name", "close"] body)
  if (jstr j "division").isEmpty then
    IO.println s!"{jstr j "budget"} closed; there was nothing left to divide"
  else
    IO.println s!"{jstr j "budget"} closed and divided"
  IO.println ""
  printDivision (jobj (← b.json (Call.get ["budgets", argStr p "name"])) "budget")

/-- Prints what people have said was theirs. -/
private def showClaims (j : Json) : IO Unit := do
  let costs := jarr (jobj j "costs")
  if costs.isEmpty then
    IO.println "nobody has taken a cost yet"
    return
  printTable #["date", "cost", "taken by"]
    (costs.map fun c => #[
      jstr c "date", Str.clamp (jstr c "narration") 40,
      String.intercalate ", " ((jarr (jobj c "who")).toList.map (·.getStr?.toOption.getD ""))])

/--
Handler for `budget share`: puts a budget's costs where other people can see
them, and sends each of them a link.
-/
def runBudgetShare (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj []
  let guests := flagList p "with"
  unless guests.isEmpty do
    body := body.setObjVal! "with" (Json.arr (guests.map Json.str).toArray)
  match flagStr? p "realm" with
  | some n => body := body.setObjVal! "realm" (Json.str n)
  | none => pure ()
  let j ← b.json (Call.post ["budgets", argStr p "name", "share"] body)
  IO.println s!"{jstr j "budget"} is in realm {jstr j "realm"}; {jstr j "moved"} cost(s) moved"
  let invites := jarr (jobj j "invites")
  if invites.isEmpty then
    IO.println "no links yet; 'resources realm invite' makes one"
  else
    IO.println ""
    for i in invites do
      IO.println s!"{Str.padRight (jstr i "for") 16} {jstr i "link"}"

/-- Handler for `budget claim`: says a cost was yours. -/
def runBudgetClaim (p : Parsed) : IO UInt32 := withBackend fun b => do
  for txn in (p.variableArgsAs! String) do
    let j ← b.json (Call.post ["budgets", argStr p "name", "claims"]
      (Json.mkObj [("txn", Json.str txn)]))
    if txn == (p.variableArgsAs! String).back! then showClaims j

/-- Handler for `budget release`: takes one back. -/
def runBudgetRelease (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut last : Option Json := none
  for txn in (p.variableArgsAs! String) do
    let mut body := Json.mkObj [("txn", Json.str txn)]
    match flagStr? p "member" with
    | some m => body := body.setObjVal! "member" (Json.str m)
    | none => pure ()
    last := some (← b.json (Call.post ["budgets", argStr p "name", "releases"] body))
  match last with
  | some j => showClaims j
  | none => throw <| IO.userError "say which cost to give back"

/-- Handler for `budget reopen`. -/
def runBudgetReopen (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["budgets", argStr p "name", "reopen"] (Json.mkObj []))
  IO.println s!"{jstr j "budget"} is open again; every division already made still stands"

/-- Handler for `budget lend`. -/
def runBudgetLend (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj []
  let ids := flagList p "txn"
  if !ids.isEmpty then
    body := body.setObjVal! "transactions" (Json.arr (ids.map Json.str).toArray)
  match flagStr? p "filter" with
  | some f => body := body.setObjVal! "filter" (Json.str f)
  | none => pure ()
  let j ← b.json (Call.post ["budgets", argStr p "name", "lend"] body)
  IO.println s!"lent {jstr j "lent"} cost(s) into {jstr j "budget"}"

/--
Handler for `budget contribute`: records a cost somebody else paid for.

Their money account is credited and the budget is debited, exactly as `lend`
does for one of yours. Nothing of yours moves, and nothing of theirs is counted
as yours: the account belongs to them.
-/
def runBudgetContribute (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj [
    ("who", Json.str (flagStr p "who" "")),
    ("amount", Json.str (flagStr p "amount" "")),
    ("narration", Json.str (flagStr p "for" ""))]
  for (k, v) in [("account", flagStr? p "account"), ("date", flagStr? p "date"),
                 ("commodity", flagStr? p "commodity"), ("payee", flagStr? p "payee")] do
    match v with
    | some x => body := body.setObjVal! k (Json.str x)
    | none => pure ()
  discard <| b.json (Call.post ["budgets", argStr p "name", "contribute"] body)
  IO.println s!"recorded {flagStr p "amount" ""} paid by {flagStr p "who" ""}"

/--
Handler for `budget allocate`.

A participant is written `name=account`, or `name=account*weight` when the
shares are not equal. A bare `=account` is your own share, and the account you
give is where money you actually consumed goes — which is the whole reason your
share is a posting rather than an implicit subtraction. Everybody else's share
lands in an account of their own, their purse unless you name another.
-/
def runBudgetAllocate (p : Parsed) : IO UInt32 := withBackend fun b => do
  let among := (p.variableArgsAs! String).toList.map bearerSpec
  let mut body := Json.mkObj [("among", Json.arr among.toArray),
                              ("commodity", Json.str (flagStr p "commodity" "EUR"))]
  match flagStr? p "through" with
  | some h => body := body.setObjVal! "through" (Json.str h)
  | none => pure ()
  let j ← b.json (Call.post ["budgets", argStr p "name", "allocate"] body)
  IO.println s!"divided up; {(jarr (jobj j "claims")).size} payment(s) raised"
  IO.println ""
  printDivision (jobj (← b.json (Call.get ["budgets", argStr p "name"])) "budget")

/-- Handler for `budget settle`: raises the claims that would square a budget. -/
def runBudgetSettle (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj [("commodity", Json.str (flagStr p "commodity" "EUR"))]
  match flagStr? p "through" with
  | some h => body := body.setObjVal! "through" (Json.str h)
  | none => pure ()
  let j ← b.json (Call.post ["budgets", argStr p "name", "settle"] body)
  let raised := (jarr (jobj j "claims")).size
  IO.println (if raised == 0 then "nothing more to ask for" else s!"{raised} payment(s) raised")
  IO.println ""
  printDivision (jobj (← b.json (Call.get ["budgets", argStr p "name"])) "budget")

/-! ## Claims -/

/-- Handler for `claims list`. -/
def runClaimList (p : Parsed) : IO UInt32 := withBackend fun b => do
  let query :=
    (match flagStr? p "filter" with | some f => [("filter", f)] | none => [])
      ++ (if p.hasFlag "all" then [("all", "1")] else [])
  let j ← b.json (Call.get ["claims"] query)
  let rows := jarr j
  if rows.isEmpty then
    IO.println "nothing outstanding"
    return
  printTable #["due", "from", "to", "amount", "state", "what", "id"]
    (rows.map fun c => #[
      jstr c "due", jstr c "from", jstr c "to", jstr (jobj c "amount") "text",
      jstr c "state", Str.clamp (jstr c "narration") 34, jstr c "id"])
    (rightAlign := #[3])

/-- Handler for `claims candidates`: what in the ledger could have met a claim. -/
def runClaimCandidates (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["claims", argStr p "id", "candidates"])
  let rows := jarr j
  if rows.isEmpty then
    IO.println "nothing in the ledger looks like it met this claim"
    return
  printTable #["date", "payee", "amount", "id"]
    (rows.map fun t => #[
      jstr t "date", Str.clamp (jstr t "payee") 34,
      jstr (jobj (jobj t "headline") "amount") "text", jstr t "id"])
    (rightAlign := #[2])

/--
Handler for `claims resolve`: meets a claim against the entry that performed it.

The claim does not become that entry. The bank line already exists, with the
fingerprint that reconciles it against the statement; what the claim adds is the
counterparty, which the importer could only guess at.
-/
def runClaimResolve (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["claims", argStr p "id", "resolve"]
    (Json.mkObj [("transaction", Json.str (argStr p "transaction"))]))
  if jstr j "state" == "settled" then
    IO.println s!"settled — {jstr j "from"} → {jstr j "to"}"
  else
    IO.println s!"part paid; {jstr (jobj j "amount") "text"} still outstanding"

/-- Handler for `claims void`: retires a claim that will never be performed. -/
def runClaimVoid (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj []
  match flagStr? p "write-off" with
  | some a => body := body.setObjVal! "writeOffTo" (Json.str a)
  | none => pure ()
  let j ← b.json (Call.post ["claims", argStr p "id", "void"] body)
  IO.println s!"voided {jstr (jobj j "amount") "text"} from {jstr j "from"}"
  match flagStr? p "write-off" with
  | some a => IO.println s!"and booked the loss to {a}"
  | none => IO.println "their account still says they owe it; --write-off records the loss"

/-- Handler for `group new`. -/
def runGroupNew (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["groups"] (Json.mkObj [
    ("name", Json.str (argStr p "name")),
    ("members", Json.arr ((flagList p "members").map Json.str).toArray)]))
  let members := (jarr (jobj j "members")).toList.map (fun x => x.getStr?.toOption.getD "")
  IO.println s!"{jstr j "name"}: {String.intercalate ", " members}"

/-- Handler for `group list`. -/
def runGroupList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["groups"])
  printTable #["group", "members"]
    ((jarr j).map fun g => #[jstr g "name",
      String.intercalate ", " ((jarr (jobj g "members")).toList.map
        (fun x => x.getStr?.toOption.getD ""))])

/-- Handler for `group rm`. -/
def runGroupRm (p : Parsed) : IO UInt32 := withBackend fun b => do
  discard <| b.json (Call.delete ["groups", argStr p "name"])
  IO.println "deleted"

/-- Handler for `trip new`. -/
def runTripNew (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["trips"] (Json.mkObj [
    ("name", argStr p "name"), ("starts", flagStr p "from" ""),
    ("ends", flagStr p "to" ""), ("payer", flagStr p "payer" "")]))
  IO.println s!"{jstr j "name"}  labelled {jstr j "label"}  spent from {jstr j "purse"}"

/-- Handler for `trip list`. -/
def runTripList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["trips"])
  printTable #["trip", "from", "to", "payer", "items", "cost so far"]
    ((jarr j).map fun t => #[jstr t "name", jstr t "starts", jstr t "ends", jstr t "payer",
                            jstr t "members", jstr (jobj t "total") "text"])
    (rightAlign := #[4, 5])

/-- Handler for `trip suggest`: what else in the window looks like part of it. -/
def runTripSuggest (p : Parsed) : IO UInt32 := withBackend fun b => do
  let name := argStr p "name"
  let j ← b.json (Call.get ["trips", name, "suggest"])
  let items := jarr j
  if items.isEmpty then
    IO.println "nothing else in that window looks like part of this trip"
    return
  printTable #["date", "payee", "amount", "account", "id"]
    (items.map fun t => #[
      jstr t "date", Str.clamp (jstr t "payee") 30,
      jstr (jobj (jobj t "headline") "amount") "text",
      Str.clamp (String.intercalate "/" ((jarr (jobj t "postings")).toList.map
        (fun x => jstr x "account"))) 40,
      jstr t "id"])
    (rightAlign := #[2])
  if p.hasFlag "all" then
    let ids := items.map (fun t => Json.str (jstr t "id"))
    let r ← b.json (Call.post ["trips", name, "add"] (Json.mkObj [("ids", Json.arr ids)]))
    IO.println s!"\nadded {jstr r "added"} to {name}"
  else
    IO.println s!"\nadd the ones that belong: resources trip add {name} <ids>   (or --all)"

/-- Handler for `trip add`. -/
def runTripAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let ids := (p.variableArgsAs! String).map Json.str
  let j ← b.json (Call.post ["trips", argStr p "name", "add"]
    (Json.mkObj [("ids", Json.arr ids)]))
  IO.println s!"added {jstr j "added"} transactions"

/-- Handler for `trip drop`. -/
def runTripDrop (p : Parsed) : IO UInt32 := withBackend fun b => do
  let ids := (p.variableArgsAs! String).map Json.str
  let j ← b.json (Call.post ["trips", argStr p "name", "drop"]
    (Json.mkObj [("ids", Json.arr ids)]))
  IO.println s!"dropped {jstr j "dropped"} transactions"

/-- Handler for `receipt scan`: reads a stored receipt. -/
def runReceiptScan (p : Parsed) : IO UInt32 := withBackend fun b => do
  let explicit := p.variableArgsAs! String
  let shas ←
    if explicit.isEmpty then do
      let inbox ← b.json (Call.get ["receipts"])
      pure ((jarr inbox).map (fun s => jstr s "sha256"))
    else pure explicit
  if shas.isEmpty then
    IO.println "no unattached receipts to read"
    return
  for sha in shas do
    try
      let j ← b.json (Call.post ["receipts", sha, "extract"] (Json.mkObj []))
      let total := Str.padLeft (jstr (jobj j "total") "text") 10
      let who := Str.clamp (jstr j "merchant") 34
      IO.println s!"  {Str.clamp sha 12}  {jstr j "date"}  {total}  {who}  [{jstr j "extractor"}]"
    catch e =>
      IO.eprintln s!"  {Str.clamp sha 12}  {e}"

/-- Handler for `receipt inbox`: receipts not attached to anything. -/
def runReceiptInbox (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["receipts"])
  printTable #["sha256", "date", "total", "merchant", "file"]
    ((jarr j).map fun s => #[
      Str.clamp (jstr s "sha256") 12, jstr s "date",
      jstr (jobj s "total") "text", Str.clamp (jstr s "merchant") 30, jstr s "origName"])
    (rightAlign := #[2])

/-- Handler for `receipt match`: which transaction each scanned receipt belongs to. -/
def runReceiptMatch (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["receipts", "proposals"])
  let items := jarr j
  if items.isEmpty then
    IO.println "no receipt matches a transaction yet; try 'resources receipt scan' first"
    return
  printTable #["confidence", "receipt", "goes with", "amount", "why"]
    (items.map fun m => #[
      jstr m "confidence", Str.clamp (jstr m "sha256") 12,
      Str.clamp (jstr (jobj m "txn") "payee") 26,
      jstr (jobj (jobj (jobj m "txn") "headline") "amount") "text",
      Str.clamp (jstr m "reason") 44])
    (rightAlign := #[3])
  if !p.hasFlag "apply" then
    IO.println s!"\n{items.size} proposal(s). Re-run with --apply to attach them."
    return
  for m in items do
    discard <| b.json (Call.post ["transactions", jstr (jobj m "txn") "id", "attachments"]
      (Json.mkObj [("sha256", Json.str (jstr m "sha256"))]))
  IO.println s!"\nattached {items.size} receipt(s)"

/-- Prints a receipt's lines, and what the total still leaves room for. -/
private def showItems (b : Backend) (sha : String) : IO Unit := do
  let j ← b.json (Call.get ["receipts", sha])
  let items := jarr (jobj j "items")
  printTable #["#", "qty", "line", "amount"]
    ((Array.range items.size).map fun i =>
      let it := items[i]!
      #[toString (i + 1), jstr it "qty", Str.clamp (jstr it "description") 44,
        jstr (jobj it "amount") "text"])
    (rightAlign := #[0, 1, 3])
  let left := jstr (jobj j "headroom") "text"
  if !left.isEmpty then
    IO.println s!"\n{left} of {jstr (jobj j "total") "text"} is not on any line."

/-- Handler for `receipt items`: shows the priced lines read off a receipt. -/
def runReceiptItems (p : Parsed) : IO UInt32 := withBackend fun b => do
  let sha := argStr p "sha"
  let j ← b.json (Call.get ["receipts", sha, "items"])
  if (jarr j).isEmpty then
    IO.println "no lines were read off this receipt; run 'resources receipt scan' on it first"
    return
  showItems b sha

/-- Handler for `receipt item-add`: adds a line a scan could not read. -/
def runReceiptItemAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let sha := argStr p "sha"
  let body := Json.mkObj [
    ("description", Json.str (argStr p "description")),
    ("total", Json.str (argStr p "amount"))]
  let body := match (flagStr? p "qty").bind (·.toInt?) with
    | some q => body.setObjVal! "qty" (Json.num (JsonNumber.fromInt q))
    | none => body
  let _ ← b.json (Call.post ["receipts", sha, "items"] body)
  showItems b sha

/-- Handler for `receipt item-rm`: drops a line by its position. -/
def runReceiptItemRm (p : Parsed) : IO UInt32 := withBackend fun b => do
  let sha := argStr p "sha"
  let _ ← b.json (Call.delete ["receipts", sha, "items", argStr p "line"])
  showItems b sha

/--
Handler for `tx divide`: divides a payment into the things it paid for.

The groups are written as `1+2=Account` rather than with commas, because the
flag itself is comma separated and a line list inside one would be ambiguous.
-/
def runTxDivide (p : Parsed) : IO UInt32 := withBackend fun b => do
  let specs := flagList p "group"
  if specs.isEmpty then
    throw <| IO.userError
      "say which lines go together, e.g. --group 1+2=Expenses.Food.EatingOut"
  let mut groups : Array Json := #[]
  for spec in specs do
    match spec.splitOn "=" with
    | [lhs, into] =>
      -- `3` is all of line 3; `3:10` is ten of what line 3 covers.
      let shares := (lhs.splitOn "+").filterMap fun tok =>
        match tok.trimAscii.toString.splitOn ":" with
        | [n] => n.toNat?.map fun i =>
            Json.mkObj [("line", Json.num (JsonNumber.fromInt (Int.ofNat i)))]
        | [n, q] => do
            let i ← n.toNat?
            let k ← q.toNat?
            some (Json.mkObj [("line", Json.num (JsonNumber.fromInt (Int.ofNat i))),
                              ("qty", Json.num (JsonNumber.fromInt (Int.ofNat k)))])
        | _ => none
      if shares.isEmpty then throw <| IO.userError s!"no line numbers in '{spec}'"
      if into.trimAscii.toString.isEmpty then
        throw <| IO.userError s!"no account in '{spec}'"
      groups := groups.push (Json.mkObj [
        ("items", Json.arr shares.toArray),
        ("into", Json.str into.trimAscii.toString)])
    | _ => throw <| IO.userError s!"expected lines=account, got '{spec}'"
  let j ← b.json (Call.post ["transactions", argStr p "id", "divide"]
    (Json.mkObj [("groups", Json.arr groups)]))
  for t in jarr j do
    IO.println s!"{jstr t "id"}  {jstr t "date"}  {headlineAmount t}  {jstr t "narration"}"

/-- Handler for `receipt cash`: turns a receipt into the cash transaction it stands for. -/
def runReceiptCash (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["receipts", argStr p "sha", "cash"] (Json.mkObj [
    ("from", Json.str (flagStr p "from" "Assets.Cash")),
    ("into", Json.str (flagStr p "into" "Expenses.Unclassified"))]))
  let amount := jstr (jobj (jobj j "headline") "amount") "text"
  IO.println s!"{jstr j "id"}  {jstr j "date"}  {amount}  {jstr j "payee"}"

/-- Handler for `contacts books`: what the desktop contact store holds. -/
def runContactBooks (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["contacts", "books"])
  if (jarr j).isEmpty then
    IO.println "no desktop address books found"
    return
  printTable #["address book", "contacts"]
    ((jarr j).map fun x => #[jstr x "name", jstr x "contacts"]) (rightAlign := #[1])

/-- Handler for `contacts use`: chooses where contacts come from. -/
def runContactsUse (p : Parsed) : IO UInt32 := withBackend fun b => do
  let kind := argStr p "kind"
  let rest := p.variableArgsAs! String
  let mut body := Json.mkObj [("kind", Json.str kind)]
  match kind with
  | "eds" => pure ()
  | "files" =>
    let some path := rest[0]? | throw <| IO.userError "give the directory of vCards"
    body := body.setObjVal! "path" (Json.str path)
  | "carddav" =>
    let some url := rest[0]? | throw <| IO.userError "give the collection URL"
    let some user := rest[1]? | throw <| IO.userError "give the username"
    body := body.setObjVal! "url" (Json.str url)
    body := body.setObjVal! "user" (Json.str user)
    let cmd := (flagStr p "password-command" "").splitOn " " |>.filter (!·.isEmpty)
    body := body.setObjVal! "passwordCommand" (Json.arr (cmd.map Json.str).toArray)
  | other => throw <| IO.userError s!"unknown source: {other} (eds, files or carddav)"
  let j ← b.json (Call.post ["contacts", "source"] body)
  IO.println s!"contacts now come from {jstr j "source"}"

/-- Handler for `tx rm`. -/
def runTxRm (p : Parsed) : IO UInt32 := withBackend fun b => do
  discard <| b.json (Call.delete ["transactions", argStr p "id"])
  IO.println "deleted"

/-- Handler for `tx history`. -/
def runTxHistory (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["transactions", argStr p "id", "revisions"])
  printTable #["seq", "at", "actor", "kind"]
    ((jarr j).map fun r => #[toString (((r.getObjValAs? Int "seq").toOption).getD 0),
                            jstr r "at", jstr r "actor", jstr r "kind"])

/-! ## Accounts, labels, parties -/

/-- Handler for `acc list`. -/
def runAccList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["accounts"])
  printTable #["name", "kind", "owner", "commodity", "iban", "id"]
    ((jarr j).map fun a => #[jstr a "name", jstr a "kind",
                            (if jstr a "mine" == "true" then "" else jstr a "ownerName"),
                            jstr a "commodity", jstr a "iban", jstr a "id"])

/-- Handler for `acc add`. -/
def runAccAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj [("name", argStr p "name")]
  for (k, v) in [("kind", flagStr? p "kind"), ("iban", flagStr? p "iban"),
                 ("commodity", flagStr? p "commodity"), ("note", flagStr? p "note"),
                 ("owner", flagStr? p "owner")] do
    match v with
    | some x => body := body.setObjVal! k (Json.str x)
    | none => pure ()
  let j ← b.json (Call.post ["accounts"] body)
  let whose := if jstr j "mine" == "true" then "" else s!"  owned by {jstr j "ownerName"}"
  IO.println s!"{jstr j "name"}  ({jstr j "kind"}){whose}  {jstr j "id"}"

/-- Handler for `acc merge`: folds one account into another. -/
def runAccMerge (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["accounts", "merge"]
    (Json.mkObj [("from", argStr p "from"), ("into", argStr p "into")]))
  IO.println s!"moved {jstr j "moved"} transactions from {jstr j "from"} into {jstr j "into"}"

/-- Handler for `acc balance`. -/
def runAccBalance (p : Parsed) : IO UInt32 := withBackend fun b => do
  let query := match flagStr? p "at" with | some d => [("at", d)] | none => []
  match (p.variableArgsAs! String)[0]? with
  | some name =>
    let j ← b.json (Call.get ["accounts", name, "balance"] query)
    printTable #["account", "balance", "commodity"]
      ((jarr j).map fun e => #[jstr e "account", jstr e "text", jstr e "commodity"])
      (rightAlign := #[1])
  | none =>
    let j ← b.json (Call.get ["reports", "balances"] query)
    printTable #["account", "balance", "commodity"]
      ((jarr j).map fun e => #[jstr e "account", jstr e "text", jstr e "commodity"])
      (rightAlign := #[1])

/-- Handler for `label list`. -/
def runLabelList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["labels"])
  printTable #["name", "id"] ((jarr j).map fun l => #[jstr l "name", jstr l "id"])

/-- Handler for `label add`. -/
def runLabelAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["labels"] (Json.mkObj [("name", argStr p "name")]))
  IO.println s!"{jstr j "name"}  {jstr j "id"}"

/-- Handler for `party list`. -/
def runPartyList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["parties"])
  printTable #["counterparty", "iban", "email"]
    ((jarr j).map fun x => #[jstr x "name", jstr x "iban", jstr x "email"])
  IO.println "\n(counterparties seen in the ledger; people live in your address book —"
  IO.println " see resources contacts)"

/-- Handler for `contacts`: what your address book offers. -/
def runContacts (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["contacts"])
  IO.println s!"source: {jstr j "source"}"
  let items := jarr (jobj j "items")
  if jstr j "configured" != "true" then
    IO.println ""
    IO.println ""
    IO.println "No address book was found. This machine has no desktop contact store,"
    IO.println "so point it somewhere with one of:"
    IO.println ""
    IO.println "  resources contacts use files <directory of vCards>"
    IO.println "  resources contacts use carddav <url> <user> --password-command 'pass show dav'"
    IO.println ""
    IO.println "Nothing is copied here; your address book stays the only copy."
    return
  IO.println ""
  let shown :=
    match flagStr? p "search" with
    | some needle => items.filter fun c => Str.containsCI (jstr c "name") needle
    | none => items
  printTable #["name", "email", "iban"]
    (shown.map fun c => #[jstr c "name", jstr c "email", jstr c "iban"])

/-! ## Imports -/

/-- Handler for `import file`. -/
def runImportFile (p : Parsed) : IO UInt32 := withBackend fun b => do
  let file := argStr p "file"
  let account := flagStr p "account" ""
  if account.isEmpty then throw <| IO.userError "--account names the bank account to import into"
  let bytes ← IO.FS.readBinFile file
  let j ← b.json
    { method := "POST", path := ["imports"], body := bytes
      query := [("account", account), ("profile", flagStr p "profile" "auto"),
                ("filename", (System.FilePath.mk file).fileName.getD file)]
      headers := [("content-type", "text/csv")] }
  let batch := jobj j "batch"
  let staged := jarr (jobj j "staged")
  IO.println s!"profile {jstr j "profile"}, batch {jstr batch "id"}"
  let dups := jstr batch "duplicates"
  IO.println s!"  {jstr batch "total"} rows read, {staged.size} new, {dups} already known"
  for prob in jarr (jobj j "problems") do
    IO.eprintln s!"  warning: {prob.getStr?.toOption.getD ""}"
  if p.hasFlag "promote" || p.hasFlag "auto-merge" then
    let promoteBody :=
      if p.hasFlag "auto-merge" then Json.mkObj [("merge", Json.str "auto")] else Json.mkObj []
    let r ← b.json (Call.post ["imports", jstr batch "id", "promote"] promoteBody)
    IO.println s!"  promoted {(jarr (jobj r "created")).size} transactions"
    for inv in jarr (jobj r "settledInvoices") do
      IO.println s!"  invoice {inv.getStr?.toOption.getD ""} settled"
  else
    printTable #["date", "payee", "purpose", "amount", "id"]
      (staged.map fun e => #[
        jstr e "date", Str.clamp (jstr e "payee") 24, Str.clamp (jstr e "purpose") 40,
        jstr (jobj e "amount") "text", jstr e "id"])
      (rightAlign := #[3])
    IO.println s!"\nreview, then: resources import promote {jstr batch "id"}"

/-- Handler for `import proposals`: shows rows that look like one event. -/
def runImportProposals (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["imports", argStr p "batch", "proposals"])
  printTable #["confidence", "date", "main", "with", "why"]
    ((jarr j).map fun x =>
      let parent := jobj x "parent"
      let child := jobj x "child"
      #[jstr x "confidence", jstr parent "date",
        Str.clamp (jstr (jobj parent "payee") "" ++ jstr parent "payee") 24
          ++ " " ++ jstr (jobj parent "amount") "text",
        jstr (jobj child "amount") "text",
        Str.clamp (jstr x "reason") 52])
  IO.println "\npromote them as single transactions with:"
  IO.println "  resources import promote <batch> --auto-merge"

/-- Handler for `import list`. -/
def runImportList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["imports"])
  printTable #["at", "profile", "file", "rows", "dups", "id"]
    ((jarr j).map fun x => #[jstr x "at", jstr x "profile", jstr x "filename",
                            toString (((x.getObjValAs? Int "total").toOption).getD 0),
                            toString (((x.getObjValAs? Int "duplicates").toOption).getD 0),
                            jstr x "id"])

/-- Handler for `import staged`. -/
def runImportStaged (p : Parsed) : IO UInt32 := withBackend fun b => do
  let batch := argStr p "batch"
  let query := match flagStr? p "state" with | some s => [("state", s)] | none => []
  let j ← b.json (Call.get ["imports", batch, "staged"] query)
  printTable #["date", "payee", "purpose", "amount", "state", "id"]
    ((jarr j).map fun e => #[
      jstr e "date", Str.clamp (jstr e "payee") 22, Str.clamp (jstr e "purpose") 36,
      jstr (jobj e "amount") "text", jstr e "state", jstr e "id"])
    (rightAlign := #[3])

/-- Handler for `import suggest`: routes a staged row before it is promoted. -/
def runImportSuggest (p : Parsed) : IO UInt32 := withBackend fun b => do
  discard <| b.json (Call.post ["staged", argStr p "id", "suggest"]
    (Json.mkObj [("account", argStr p "account")]))
  IO.println s!"{argStr p "id"} will be booked into {argStr p "account"}"

/-- Handler for `import promote`. -/
def runImportPromote (p : Parsed) : IO UInt32 := withBackend fun b => do
  let batch := argStr p "batch"
  let ids := flagList p "id"
  let mut body :=
    if ids.isEmpty then Json.mkObj []
    else Json.mkObj [("ids", Json.arr (ids.map Json.str).toArray)]
  if p.hasFlag "auto-merge" then body := body.setObjVal! "merge" (Json.str "auto")
  else if p.hasFlag "as-one" then body := body.setObjVal! "merge" (Json.str "true")
  let j ← b.json (Call.post ["imports", batch, "promote"] body)
  let merged := ((j.getObjValAs? Int "merged").toOption).getD 0
  let note := if merged > 0 then s!" ({merged} of them merged from several rows)" else ""
  IO.println (s!"promoted {(jarr (jobj j "created")).size} transactions" ++ note)
  for inv in jarr (jobj j "settledInvoices") do
    IO.println s!"invoice {inv.getStr?.toOption.getD ""} settled"

/-- Handler for `import ignore`. -/
def runImportIgnore (p : Parsed) : IO UInt32 := withBackend fun b => do
  let ids := p.variableArgsAs! String
  discard <| b.json (Call.post ["staged", "ignore"]
    (Json.mkObj [("ids", Json.arr (ids.map Json.str))]))
  IO.println s!"ignored {ids.size}"

/-! ## Rules -/

/-- Handler for `rule list`. -/
def runRuleList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["rules"])
  printTable #["priority", "name", "filter", "account", "labels", "id"]
    ((jarr j).map fun r => #[
      toString (((r.getObjValAs? Int "priority").toOption).getD 0), jstr r "name",
      jstr r "filter", jstr r "setAccount",
      String.intercalate "," ((jarr (jobj r "addLabels")).toList.map
        (fun l => l.getStr?.toOption.getD "")),
      jstr r "id"])

/-- Handler for `rule add`. -/
def runRuleAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let body := Json.mkObj [
    ("name", argStr p "name"), ("filter", argStr p "filter"),
    ("setAccount", Json.str (flagStr p "account" "")),
    ("addLabels", Json.arr ((flagList p "label").map Json.str).toArray),
    ("priority", Json.num (JsonNumber.fromNat ((flagStr p "priority" "0").toNat?.getD 0)))]
  let j ← b.json (Call.post ["rules"] body)
  IO.println s!"{jstr j "name"}  {jstr j "id"}"

/--
Handler for `rule apply`: runs the rules over transactions already in the
ledger. Shows what would change unless `--apply` is given.
-/
def runRuleApply (p : Parsed) : IO UInt32 := withBackend fun b => do
  let commit := p.hasFlag "apply"
  let j ← b.json (Call.post ["rules", "apply"] (Json.mkObj [("commit", Json.bool commit)]))
  let items := jarr (jobj j "items")
  if items.isEmpty then
    IO.println "no uncategorised transaction matches a rule"
    return
  let byRule := items.foldl (init := ([] : List (String × Nat))) fun acc x =>
    let key := jstr x "rule" ++ "  ->  " ++ jstr x "account"
    match acc.lookup key with
    | some n => acc.filter (fun kv => kv.1 != key) ++ [(key, n + 1)]
    | none => acc ++ [(key, 1)]
  printTable #["rule", "matched"]
    (byRule.toArray.map fun (k, n) => #[k, toString n]) (rightAlign := #[1])
  if commit then
    IO.println s!"\ncategorised {items.size} transactions"
  else
    IO.println s!"\n{items.size} transactions would be categorised. Re-run with --apply."

/-- Handler for `rule rm`. -/
def runRuleRm (p : Parsed) : IO UInt32 := withBackend fun b => do
  discard <| b.json (Call.delete ["rules", argStr p "id"])
  IO.println "deleted"

/-! ## Receipts -/

/-- Handler for `receipt add`. -/
def runReceiptAdd (p : Parsed) : IO UInt32 := withBackend fun b => do
  let file := argStr p "file"
  let bytes ← IO.FS.readBinFile file
  let name := (System.FilePath.mk file).fileName.getD "receipt"
  let j ← b.json
    { method := "PUT", path := ["attachments"], body := bytes
      query := [("filename", name)]
      headers := [("content-type", Blobs.mimeOfExtension name)] }
  let sha := jstr j "sha256"
  IO.println s!"{sha}  {jstr j "bytes"} bytes"
  match flagStr? p "txn" with
  | some id =>
    discard <| b.json (Call.post ["transactions", id, "attachments"]
      (Json.mkObj [("sha256", sha)]))
    IO.println s!"attached to {id}"
  | none => pure ()

/-- Handler for `receipt list`. -/
def runReceiptList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["attachments"])
  printTable #["sha256", "mime", "bytes", "name"]
    ((jarr j).map fun a => #[Str.clamp (jstr a "sha256") 16, jstr a "mime",
                            toString (((a.getObjValAs? Int "bytes").toOption).getD 0),
                            jstr a "origName"])
    (rightAlign := #[2])

/-- Handler for `receipt gc`. -/
def runReceiptGc (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["attachments", "gc"] (Json.mkObj []))
  IO.println s!"removed {jstr j "removed"} unreferenced receipts"

/-! ## Invoices -/

/-- Handler for `invoice new`. -/
def runInvoiceNew (p : Parsed) : IO UInt32 := withBackend fun b => do
  let today ← Date.today
  let issued := flagStr p "issued" today.toIso
  let due := flagStr p "due" ((today.plusDays 14).toIso)
  let mut body := Json.mkObj [
    ("budget", Json.str (argStr p "budget")), ("issued", issued), ("due", due),
    ("commodity", flagStr p "commodity" "EUR")]
  match flagStr? p "link" with
  | some url => body := body.setObjVal! "paymentLink" (Json.str url)
  | none =>
    body := body.setObjVal! "beneficiary" (Json.str (flagStr p "beneficiary" ""))
    body := body.setObjVal! "iban" (Json.str (flagStr p "iban" ""))
    match flagStr? p "bic" with
    | some bic => body := body.setObjVal! "bic" (Json.str bic)
    | none => pure ()
  match flagStr? p "note" with
  | some n => body := body.setObjVal! "note" (Json.str n)
  | none => pure ()
  let j ← b.json (Call.post ["invoices"] body)
  IO.println s!"raised from {jstr j "budget"}"
  IO.println ""
  printTable #["number", "to", "total", "reference"]
    ((jarr (jobj j "items")).map fun i =>
      #[jstr i "number", Str.clamp (jstr i "payerName") 28, jstr i "totalText",
        jstr i "reference"])
    (rightAlign := #[2])

/-- Handler for `invoice list`. -/
def runInvoiceList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["invoices"])
  printTable #["number", "issued", "due", "payer", "total", "status", "reference"]
    ((jarr j).map fun i => #[jstr i "number", jstr i "issued", jstr i "due",
                            Str.clamp (jstr i "payerName") 24, jstr i "totalText",
                            jstr i "status", jstr i "reference"])
    (rightAlign := #[4])

/-- Handler for `invoice show`. -/
def runInvoiceShow (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["invoices", argStr p "id"])
  if p.hasFlag "json" then IO.println j.pretty; return
  IO.println s!"invoice {jstr j "number"}  ({jstr j "status"})"
  IO.println s!"  to        {jstr j "payerName"}"
  IO.println s!"  issued    {jstr j "issued"}   due {jstr j "due"}"
  IO.println s!"  reference {jstr j "reference"}"
  IO.println s!"  payable   {jstr j "payment"}"
  for l in jarr (jobj j "lines") do
    IO.println s!"    {Str.padRight (jstr l "description") 34} {Str.padLeft (jstr l "quantity") 8}"
  IO.println s!"  total     {jstr j "totalText"}"

/-- Handler for `invoice status`. -/
def runInvoiceStatus (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["invoices", argStr p "id", "status"]
    (Json.mkObj [("status", argStr p "status")]))
  IO.println s!"{jstr j "invoice"} is now {jstr j "status"}"

/-- Handler for `invoice delete`. -/
def runInvoiceDelete (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.delete ["invoices", argStr p "id"])
  IO.println s!"deleted {jstr j "deleted"}"

/-- Handler for `invoice qr`. -/
def runInvoiceQr (p : Parsed) : IO UInt32 := withBackend fun b => do
  let art ← b.bytes (Call.get ["invoices", argStr p "id", "qr.txt"])
  IO.print ((String.fromUTF8? art).getD "")

/-- Handler for `invoice pdf`. -/
def runInvoicePdf (p : Parsed) : IO UInt32 := withBackend fun b => do
  let id := argStr p "id"
  let bytes ← b.bytes (Call.get ["invoices", id, "pdf"])
  let out := flagStr p "out" s!"invoice-{id}.pdf"
  IO.FS.writeBinFile out bytes
  IO.println s!"wrote {out} ({bytes.size} bytes)"

/-- Handler for `invoice html`. -/
def runInvoiceHtml (p : Parsed) : IO UInt32 := withBackend fun b => do
  let id := argStr p "id"
  let bytes ← b.bytes (Call.get ["invoices", id, "html"])
  match flagStr? p "out" with
  | some out => do IO.FS.writeBinFile out bytes; IO.println s!"wrote {out}"
  | none => IO.print ((String.fromUTF8? bytes).getD "")

/-- Handler for `invoice reconcile`. -/
def runInvoiceReconcile (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.post ["invoices", "reconcile"] (Json.mkObj []))
  if (jarr j).isEmpty then IO.println "nothing to settle"
  else
    for x in jarr j do
      IO.println s!"invoice {jstr x "invoice"} settled by {jstr x "txn"}"

/-! ## Reports and tokens -/

/-- Handler for `report trial`. -/
def runReportTrial (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["reports", "trial"])
  let rows := (jarr j).map fun e => #[jstr e "commodity", jstr e "text"]
  printTable #["commodity", "total"] rows (rightAlign := #[1])
  let bad := (jarr j).filter fun e => (((e.getObjValAs? Int "minor").toOption).getD 0) != 0
  if bad.isEmpty then IO.println "\ntrial balance is zero in every commodity"
  else IO.eprintln "\nTRIAL BALANCE IS NOT ZERO — the store is inconsistent"

/-- Handler for `report monthly`. -/
def runReportMonthly (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["reports", "monthly"]
    [("account", flagStr p "account" "Expenses"), ("commodity", flagStr p "commodity" "EUR")])
  let commodity := Commodity.ofCode (flagStr p "commodity" "EUR")
  printTable #["month", "total"]
    ((jarr j).map fun r => #[jstr r "month",
      (Amount.mk commodity (((r.getObjValAs? Int "minor").toOption).getD 0)).digits])
    (rightAlign := #[1])

/--
Handler for `token create`.

A token is a credential of your own. Letting somebody else in is an invite to a
realm — `resources realm invite` — which hands them a key rather than a narrower
version of yours.
-/
def runTokenCreate (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj [("name", argStr p "name"), ("scopes", flagStr p "scopes" "read")]
  match flagStr? p "expires" with
  | some x => body := body.setObjVal! "expires" (Json.str x)
  | none => pure ()
  let j ← b.json (Call.post ["tokens"] body)
  let tok := jobj j "token"
  IO.println s!"token {jstr tok "name"} created with scopes {jstr tok "scopes"}"
  IO.println ""
  IO.println (jstr j "secret")
  IO.println ""
  IO.println "This is the only time the secret is shown. Store it now."

/-- Handler for `token list`. -/
def runTokenList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["tokens"])
  printTable #["name", "scopes", "created", "last used", "id"]
    ((jarr j).map fun t => #[jstr t "name", jstr t "scopes", jstr t "createdAt",
                            jstr t "lastUsedAt", jstr t "id"])

/-- Handler for `token revoke`. -/
def runTokenRevoke (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.delete ["tokens", argStr p "id"])
  IO.println (if jstr j "revoked" == "true" then "revoked" else "revoked")

/-! ## Server, status and the escape hatch -/

/--
Notes `--insecure-dev`, the second half of asking for the test suite.

`RESOURCES_INSECURE_CRYPTO=1` on its own is no longer enough, and the reason is
the shape of the two things rather than a belt and braces: an environment
variable is inherited — by a service manager's children, by a container, by
every shell started from a profile that once set it for an afternoon — and a
flag on this command line is not. Something that can arrive without anybody
deciding it cannot be the thing that decides this, so the decision is taken
twice, in two kinds of place, and `Node.CryptoSuite.forNode` refuses unless both
are there.

It is set before anything opens a key, because the routes underneath build a
suite of their own (`Node/Realms.lean`) and have no command line to read.
-/
def noteInsecureDev (p : Parsed) : IO Unit := do
  if p.hasFlag "insecure-dev" then Node.CryptoSuite.allowInsecureDev

/-- Handler for `serve`. -/
def runServe (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  Api.serve ctx
    { host := flagStr p "host" "127.0.0.1"
      port := ((flagStr p "port" "8087").toNat?.getD 8087).toUInt16
      webRoot := (flagStr? p "web").map System.FilePath.mk
      cors := flagStr? p "cors" }
    Node.Realms.api

/--
The keys allowed to create a ledger: `--creator`, then `$RESOURCES_SEQ_CREATORS`,
both comma-separated lists of member ids.

An empty list is a real answer, not a missing one: membership of this service is
self-serve, so a sequencer that let any key that could authenticate make ledgers
would let any key on the internet make unlimited ledgers and fill the disk
through them. A deployment that wants none says so by listing none.
-/
private def sequencerCreators (p : Parsed) : IO (Array String) := do
  let listed := (flagStr p "creator" "").splitOn ","
  let fromEnv := match ← IO.getEnv "RESOURCES_SEQ_CREATORS" with
    | some s => s.splitOn ","
    | none => []
  return ((listed ++ fromEnv).map (fun s => s.trimAscii.toString.toLower)).toArray.filter
    (fun s => !s.isEmpty)

/--
The verifier `resources sequencer` checks signatures with.

`Verifier.ofSuite` over `CryptoSuite.sodium`: Ed25519, checked at the exact
width the suite declares. This was `Verifier.rejectAll` while no scheme was
bound, and the line above is the whole of what changed when one was — the
sequencer is written against `Verifier`, so order, membership, grants and
checkpoints were all enforced already and none of those routes was opened.

What it can no longer be is the test suite. That used to be reachable with
`RESOURCES_INSECURE_CRYPTO=1` *and* `--insecure-dev`, plus a check that the bind
address was loopback — and this project's documented topology is nginx in front
of a loopback socket, so the one check that was about the network passed in
exactly the configuration it was written to prevent. Under that suite a
signature is recomputed from the public key, so anybody who can verify one can
forge one, and a service whose entire job is to say who appended what cannot
have a mode where that depends on an inherited environment variable.

So the sequencer binary has no spelling for it at all, and `Sync.Node.make`
refuses to build one with a verifier that proves nothing unless the caller is a
test saying so in Lean. The node commands keep `--insecure-dev`, because a node
running the test suite lies only to itself and to whoever it syncs with.
-/
def sequencerVerifier : Sync.Verifier := Sync.Verifier.ofSuite Node.CryptoSuite.sodium

/--
Handler for `sequencer`.

`--origin` is the URL clients reach this sequencer at, and it is bound into every
challenge. Getting it wrong does not weaken anything — a client that signs for
one origin cannot authenticate at another — but it does mean nobody can log in,
so it is printed at startup.

`--blob-quota` is how many bytes of receipts one ledger may hold, written either
plainly or with a unit. Nothing collects blobs — the sequencer cannot read an
entry, so it cannot know which ones the order still points at — so this number
is what turns "the disk is full" into "this ledger is full", which is a sentence
somebody can be told and act on. A size this command cannot read is refused
rather than rounded or ignored: a quota typed with a zero missing is a service
that stops taking receipts three months later, and one silently dropped is a
disk that fills.

`--max-part` and `--max-append` are the two sizes a genesis is measured against:
how many bytes of ciphertext one part of an entry may carry, and how many bytes
of body an append or a checkpoint may. The first entry of a shared order is a
whole store as one snapshot, so for a ledger somebody has kept for years these
are what decide whether it can be put on a sequencer at all, and the refusal
when they are too small names bytes. Both default to what `Sync.Limits` says —
8MiB and 16MiB — and both are read with the same reader as the quota, so a size
this command cannot make sense of is refused rather than rounded.
-/
def runSequencer (p : Parsed) : IO UInt32 := do
  try
    let dataDir ←
      match flagStr? p "data" with
      | some d => pure (System.FilePath.mk d)
      | none => do pure (← Config.default).dataDir
    let host := flagStr p "host" "127.0.0.1"
    let port := ((flagStr p "port" "8088").toNat?.getD 8088).toUInt16
    let origin := flagStr p "origin" s!"http://{host}:{port}"
    let log ← Sync.Log.open (Sync.Config.atDir dataDir)
    let verifier := sequencerVerifier
    let size? (flag : String) : IO (Option Nat) := do
      let some given := flagStr? p flag | return none
      let some bytes := Sync.byteSize? given
        | throw <| IO.userError s!"--{flag} is a size in bytes, written plainly or with a \
                                   unit: 268435456, 256MiB, 512K. '{given}' is not one."
      return some bytes
    let fallback : Sync.Limits := {}
    let limits : Sync.Limits :=
      { fallback with
        blobQuotaBytes := (← size? "blob-quota").getD fallback.blobQuotaBytes,
        maxPartBytes := (← size? "max-part").getD fallback.maxPartBytes,
        maxAppendBytes := (← size? "max-append").getD fallback.maxAppendBytes }
    let creators ← sequencerCreators p
    -- `testOnly` is not passed and has no spelling here. `make` refuses to build
    -- a sequencer over a verifier that proves nothing, and the one way past that
    -- refusal is a test asking for it in Lean.
    Sync.serve (← Sync.Node.make log verifier limits origin (some creators))
      { host, port, webRoot := (flagStr? p "web").map System.FilePath.mk }
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1

/-! ## The node: identity, keys and sync -/

/-- Runs `stty` with one flag, and says whether the terminal took it. -/
private def stty (flag : String) : IO Bool := do
  try
    let child ← IO.Process.spawn
      { cmd := "stty", args := #[flag], stdout := .null, stderr := .null }
    return (← child.wait) == 0
  catch _ =>
    return false

/--
The passphrase that opens this node's identity and its keys.

`$RESOURCES_PASSPHRASE` for a service and a prompt for a person, and there is no
third way. `--passphrase` was the third, and it put the one secret that opens
every realm key this node holds into argv — where `ps` and `/proc/<pid>/cmdline`
show it to every other user on the machine, and where a shell writes it into a
history file.

The prompt turns the terminal's echo off around the read by shelling out to
`stty`, because Lean binds no `tcsetattr`, and turns it back on afterwards
whatever happened, including when the read threw. A terminal `stty` cannot
quieten is one the passphrase would be typed into in the clear, and that is said
out loud rather than pretended about.
-/
private def promptPassphrase (label : String) : IO String := do
  IO.print label
  (← IO.getStdout).flush
  let quiet ← stty "-echo"
  unless quiet do
    IO.eprintln "warning: this terminal will echo the passphrase as you type it"
  try
    return (← (← IO.getStdin).getLine).trimAscii.toString
  finally
    if quiet then
      discard <| stty "echo"
      IO.println ""

def nodePassphrase (_p : Parsed) : IO String := do
  match ← IO.getEnv "RESOURCES_PASSPHRASE" with
  | some given => return given
  | none => promptPassphrase "passphrase: "

/--
The passphrase for a file that does not exist yet, typed twice.

Everywhere else a typo costs one refusal and another go, because the file is
already there and either opens or does not. Here the file is about to be
*written* under whatever was typed, and nothing else in the world knows the
secret keys inside it: a slip at this prompt is a member id this machine can
never sign as again, an identity nobody can revoke because revoking it needs the
key, and a keyring full of realm keys that open nothing. So it is asked for
twice and the two are compared.

`$RESOURCES_PASSPHRASE` is asked for once. It was not typed at this prompt, a
second read of the same variable would compare a string with itself, and there
is nobody at the terminal to ask in any case.
-/
def newPassphrase (p : Parsed) : IO String := do
  if (← IO.getEnv "RESOURCES_PASSPHRASE").isSome then return ← nodePassphrase p
  let first ← promptPassphrase "passphrase: "
  let again ← promptPassphrase "passphrase (again): "
  unless first == again do
    throw <| IO.userError "the two passphrases are not the same, so nothing was written; \
                           run 'resources identity init' again"
  if first.isEmpty then
    throw <| IO.userError "an empty passphrase encrypts nothing; nothing was written"
  return first

/-- Everything a sync command needs, or `none` when this store syncs with nothing. -/
def openSession (ctx : Ctx) (p : Parsed) : IO (Option Node.Session) := do
  let settings ← Node.Settings.load ctx.cfg
  unless settings.configured do return none
  let suite ← Node.CryptoSuite.forNode
  let pass ← nodePassphrase p
  let identity ← Node.Identity.load suite (Node.Identity.pathIn ctx.cfg) pass
  let keys ← Node.Keys.open suite (Node.Keys.pathIn ctx.cfg) pass identity
  let transport ← Node.Transport.overCurl suite identity settings.sequencer
  return some { ctx, suite, keys, transport, ledger := settings.ledger }

/--
Prints what a round of sync came to, and says so loudly when it stopped early.

A checkpoint this node disagrees with is printed on the error stream and is not
fatal. Two honest nodes cannot disagree — the projection is a pure fold of the
same parts in the same order — so a mismatch means somebody is running different
code or telling a different story, and the useful thing is to say which realm
and which entry rather than to stop syncing.
-/
def reportRound (ctx : Ctx) (pulled : Node.Pulled) (pushed : Node.Pushed)
    (checkpoints : Array (String × Node.Checkpoint.Outcome) := #[]) : IO Unit := do
  IO.println s!"pulled    {pulled.applied} applied, {pulled.unreadable} unreadable, \
                {pulled.rejected.size} rejected"
  IO.println s!"pushed    {pushed.pushed} appended, {pushed.conflicts} conflicts"
  if pulled.rekeyed > 0 then
    IO.println s!"re-keyed  {pulled.rekeyed} realm keys fetched again"
  IO.println s!"checked   {pulled.checkpointsAgreed} checkpoints agreed"
  for (realm, outcome) in checkpoints do
    IO.println s!"published {outcome.describe realm}"
  IO.println s!"remote    entry {(← Node.remoteHead ctx).seq}"
  for (seq, why) in pulled.rejected do
    IO.eprintln s!"rejected  entry {seq}: {why}"
  for (realm, seq, why) in pulled.checkpointMismatch do
    IO.eprintln s!"MISMATCH  realm {realm} at entry {seq}: {why}"
  match pulled.refused with
  | some (seq, why) => throw <| IO.userError s!"the fetch stopped at entry {seq}: {why}"
  | none => pure ()
  match pushed.blocked with
  | some why => throw <| IO.userError why
  | none => pure ()

/--
Handler for `identity init`.

Idempotent in both halves, and the second half is the one worth stating: an
identity file that exists is opened rather than replaced, and a member the
ledger already knows is *adopted* rather than added again — `Identity.install`
asks the state before it writes, and returns the context unchanged when the key
is already a member. Appending a second `addMember` and a second `grant` for a
key that has both would open a second bridge account for one person, hand out
the admin role again over an event somebody else's node has to apply, and put a
duplicate into every projection downstream. So running it twice costs a
passphrase and writes nothing.
-/
def runIdentityInit (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  let suite ← Node.CryptoSuite.forNode
  let path := Node.Identity.pathIn ctx.cfg
  let existed ← path.pathExists
  -- Which prompt depends on which half of "idempotent in both halves" this run
  -- is. An identity that is already there is being opened, and a wrong
  -- passphrase is one refusal; one that is not is being created, and a wrong
  -- passphrase is unrecoverable, so it is typed twice.
  let pass ← if existed then nodePassphrase p else newPassphrase p
  let identity ←
    if existed then Node.Identity.load suite path pass else Node.Identity.create suite path pass
  let adopted ← Node.Identity.install ctx identity (flagStr p "name" "me")
  Node.Settings.setMember ctx.cfg identity.id
  IO.println s!"identity  {identity.id}{if existed then "  (already there)" else ""}"
  IO.println s!"agreement {identity.boxPkHex}"
  IO.println s!"file      {path}"
  IO.println s!"member    {adopted.member.val} of realm {Realm.selfId.val}"
  IO.println "the log's first author stays 'self': the core will not remove the member a \
              ledger belongs to, and genesis was written before there was a key to sign it"

/-- Handler for `identity show`. -/
def runIdentityShow (_p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let path := Node.Identity.pathIn ctx.cfg
  match ← Node.Identity.publicKeys? path with
  | none => IO.println s!"no identity at {path}; run 'resources identity init'"
  | some (signPk, boxPk) =>
    let st ← ctx.state.get
    IO.println s!"identity  {signPk}"
    IO.println s!"agreement {boxPk}"
    IO.println s!"file      {path}"
    match st.member? ⟨signPk⟩ with
    | none => IO.println "member    not a member of this ledger yet"
    | some m =>
      let role := match (st.realm? Realm.selfId).bind (fun r => r.roleOf m.id) with
        | some r => toString r
        | none => "no role"
      IO.println s!"member    {m.name} ({role} of realm {Realm.selfId.val})"

/-- Handler for `sync init`. -/
def runSyncInit (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  let url := flagStr p "sequencer" ""
  if url.isEmpty then
    throw <| IO.userError "a sequencer to sync with: --sequencer https://host"
  let suite ← Node.CryptoSuite.forNode
  let pass ← nodePassphrase p
  let identity ← Node.Identity.load suite (Node.Identity.pathIn ctx.cfg) pass
  if ((← ctx.state.get).member? identity.memberId).isNone then
    throw <| IO.userError "this identity is not a member of this ledger; run \
                           'resources identity init' first"
  let keys ← Node.Keys.open suite (Node.Keys.pathIn ctx.cfg) pass identity
  let ledger := flagStr p "ledger" "home"
  let transport ← Node.Transport.overCurl suite identity url
  let session ← Node.initAsAdmin { ctx with member := identity.memberId } suite keys transport
    url ledger
  IO.println s!"sequencer {url}"
  IO.println s!"ledger    {ledger}"
  IO.println s!"member    {session.member}"
  IO.println s!"realm     {Realm.selfId.val} created, and its key is yours"
  IO.println s!"pending   {← Node.pendingCount ctx} entries to push"

/--
An invite link's fragment, read back and checked against what an id may be.

`readInvite?` recovers six fields from one string by splitting it on `:`, which
is unambiguous exactly as long as no field can contain one. The ledger id is the
field at risk: it is a name somebody chose, and while it was any string at all,
`(ledger = "a", realm = "b:c")` and `(ledger = "a:b", realm = "c")` wrote the
identical fragment and the parser always read the first. An invite that named
one realm and redeemed another is a key handed to the wrong room.

The sequencer now holds both to `Sync.isPlainId` — `[A-Za-z0-9._-]`, at most 64
— so a fragment whose ids fall outside that set names nothing that exists there,
and reading it as an invite could only ever be reading it as the wrong one. This
refuses instead. It is the client half of the same rule and it is checked here,
where the string a person pasted turns into a request.
-/
def invitation? (fragment : String) : Option Node.Invitation := do
  let inv ← Node.readInvite? fragment
  guard (Sync.isPlainId inv.ledger)
  guard (Sync.isPlainId inv.realm)
  return inv

/--
Handler for `sync join`: spends an invite somebody sent.

The link's fragment is never sent to a server, so everything needed to redeem it
is in the string the user pastes: which ledger, which realm, and the secret that
seeds the key pair the proof is signed with. The sequencer is read off the link
too — it is the host serving `/join/` — and `--sequencer` overrides that for a
node reached by another name.
-/
def runSyncJoin (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  let link := (argStr p "link").trimAscii.toString
  let fragment := match Str.splitOnce link '#' with
    | some (_, after) => after
    | none => link
  let some inv := invitation? fragment
    | throw <| IO.userError "that is not an invite link: it has to carry the ledger, the realm, \
                             the secret, the inviter's signing key, the digest of the realm key \
                             and the digest of the order's first entry, all of them named the \
                             way this protocol names things, and this one does not"
  let url := flagStr p "sequencer" (((link.splitOn "/join/")[0]?).getD "")
  if url.isEmpty then
    throw <| IO.userError "the link does not say which sequencer to join on: --sequencer URL"
  let suite ← Node.CryptoSuite.forNode
  let pass ← nodePassphrase p
  let identity ← Node.Identity.load suite (Node.Identity.pathIn ctx.cfg) pass
  let keys ← Node.Keys.open suite (Node.Keys.pathIn ctx.cfg) pass identity
  let transport ← Node.Transport.overCurl suite identity url
  let session ← Node.join { ctx with member := identity.memberId } suite keys transport url inv
  IO.println s!"sequencer {url}"
  IO.println s!"ledger    {inv.ledger}"
  IO.println s!"realm     {inv.realm}, read and written into as a viewer"
  IO.println s!"member    {session.member}"
  IO.println s!"inviter   {inv.inviter}, pinned as an admin of that realm until its \
                membership says otherwise"
  IO.println s!"genesis   {inv.genesisHash}, which is what this ledger does begin with"
  IO.println s!"remote    entry {(← Node.remoteHead ctx).seq}"
  IO.println "what this store already held is its own prehistory and is never offered; \
the ledger has been told who has arrived, and an admin can widen what you may do"

/-- Handler for `sync`: one round. -/
def runSync (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  match ← openSession ctx p with
  | none =>
    IO.println "this store syncs with nothing; run 'resources sync init --sequencer URL'"
  | some session =>
    let r ← Node.round session
    discard <| Node.Realms.record r
    reportRound ctx r.pulled r.pushed r.checkpoints

/--
Handler for `sync status`.

Three groups of lines are about things nothing else here would show. What each
*pin* is still worth: a pin is a bootstrap, so it stops counting the moment this
node's replayed state names an admin of that realm, and a line that still said
"pinned as an admin" about somebody the ledger has since demoted would be
describing a rule this node no longer follows. What this node could *not* read:
a realm some entry carried an unreadable part in is a realm whose projection is
a fold around a hole, so it is marked `unverified` — it cannot be committed to
and nobody else's commitment can be checked against it. And where the order
*begins*, which is what an invite link pins and what every commitment is
ultimately anchored to.

Two more lines are about what the cryptography here actually is, because
neither of them is visible from anything else this command prints. `suite` is
what *this* binary signs and seals with — `resources` ships with no scheme bound,
so the honest answer is usually that it has none, and the loud one is the test
suite somebody asked for with an environment variable. `verifier` is what the
sequencer says it checks signatures with, read off its own `GET health`: a
deployment running `reject-all` accepts nothing and one running `insecure`
accepts anything, and neither is something a node can work out by syncing
successfully.
-/
def runSyncStatus (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  let settings ← Node.Settings.load ctx.cfg
  if !settings.configured then
    IO.println s!"local-only; no {Node.Settings.pathIn ctx.cfg}"
    return
  let head ← Node.remoteHead ctx
  -- Both of these are asked for without stopping the command: a sequencer that
  -- is down, and a build with no scheme bound, are things this is for saying.
  let suiteName ←
    try pure (← Node.CryptoSuite.forNode).name
    catch _ => pure "none bound in this build"
  let verifier ←
    try
      let (code, j) ← Node.Transport.result (Node.Transport.unauthenticated settings.sequencer)
        (Node.Transport.get ["health"])
      pure (if code ≥ 400 then s!"unknown; the sequencer answered {code}"
            else Sync.strField? j "verifier" "unknown; it did not say")
    catch _ => pure "unknown; the sequencer did not answer"
  IO.println s!"sequencer {settings.sequencer}"
  IO.println s!"ledger    {settings.ledger}"
  IO.println s!"member    {settings.member}"
  IO.println s!"suite     {suiteName}"
  IO.println s!"verifier  {verifier}"
  IO.println s!"remote    entry {head.seq} {head.hash}"
  IO.println s!"pending   {← Node.pendingCount ctx} entries to push"
  IO.println s!"local     {(← EventLog.head ctx.db).1} events"
  if settings.genesisHash.isEmpty then
    IO.println "genesis   not known here yet"
  else
    IO.println s!"genesis   {settings.genesisHash}"
  unless settings.genesisSeen do
    IO.println "genesis   never seen here: this store began from a checkpoint rather than \
                from entry 1"
  let st ← ctx.state.get
  for pin in settings.pinned do
    -- Three answers, and the middle one is the one worth printing at all: a pin
    -- that has been overtaken is still written down and no longer consulted.
    let realm := st.realm? ⟨pin.realm⟩
    let stillAdmin := st.canAdminister ⟨pin.member⟩ ⟨pin.realm⟩
    let hasAdmins : Bool := match realm with
      | some r => r.members.any (fun (m, role) => role == .admin && m != Member.selfId)
      | none => false
    let standing :=
      if stillAdmin then "still an admin of it"
      else if hasAdmins then "no longer an admin of it, so this pin no longer counts"
      else "the only anchor this node has: it has not read that realm's membership yet"
    IO.println s!"pinned    {pin.member} on realm {pin.realm} — {standing}"
  for realm in ← Node.Checkpoint.gappedRealms ctx head.seq do
    IO.println s!"unverified realm {realm}: some part written in it never opened here, so what \
                  this node shows of it is a fold around a hole"
  for stored in ← Checkpoints.all ctx.db do
    if stored.realm.isEmpty then
      IO.println s!"snapshot  event {stored.seq}, {stored.stateHash}"
    else
      IO.println s!"committed {stored.realm} at entry {stored.seq}, {stored.stateHash}"

/-! ## Realms

Four thin wrappers, like every other command here: the route table is where a
realm is made, and `resources realm create` is `POST realms` with a nicer table
at the end of it.
-/

/-- Handler for `realm list`. -/
def runRealmList (_p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["realms"])
  printTable #["realm", "gen", "key", "budget", "members", "id"]
    ((jarr j).map fun r => #[
      jstr r "name", jstr r "generation",
      (if jstr r "hasKey" == "true" then "held" else "-"),
      jstr r "budget", toString (jarr (jobj r "members")).size, jstr r "id"])
    (rightAlign := #[1, 4])

/-- Handler for `realm create`. -/
def runRealmCreate (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj [("name", argStr p "name")]
  match flagStr? p "budget" with
  | some bn => body := body.setObjVal! "budget" (Json.str bn)
  | none => pure ()
  let j ← b.json (Call.post ["realms"] body)
  IO.println s!"realm     {jstr j "name"}  ({jstr j "id"})"
  IO.println s!"key       {if jstr j "hasKey" == "true" then "held here" else "not held here"}"
  let budget := jstr j "budget"
  unless budget.isEmpty do
    IO.println s!"budget    {budget}"

/-- Handler for `realm invite`. -/
def runRealmInvite (p : Parsed) : IO UInt32 := withBackend fun b => do
  let mut body := Json.mkObj [("for", argStr p "who")]
  for (k, v) in [("role", flagStr? p "role"), ("expires", flagStr? p "expires")] do
    match v with
    | some x => body := body.setObjVal! k (Json.str x)
    | none => pure ()
  let j ← b.json (Call.post ["realms", argStr p "realm", "invites"] body)
  IO.println s!"invite    {jstr j "for"} as {jstr j "role"} of {jstr j "name"}, \
                until {jstr j "expires"}"
  IO.println ""
  IO.println s!"  {jstr j "link"}"
  IO.println ""
  IO.println "Send that once. The secret lives in the fragment, so it never reaches a server \
log or a Referer header, and redeeming it is what makes them a member with a key of their own."

/-- Handler for `realm members`. -/
def runRealmMembers (p : Parsed) : IO UInt32 := withBackend fun b => do
  let j ← b.json (Call.get ["realms", argStr p "realm", "members"])
  let granted := jobj j "granted"
  let holders := (jarr granted).map (fun x => (x.getStr?.toOption).getD "")
  printTable #["member", "role", "key", "id"]
    ((jarr (jobj j "members")).map fun m => #[
      jstr m "name", jstr m "role",
      (if granted == Json.null then "?"
       else if holders.contains (jstr m "id") then "held" else "-"),
      jstr m "id"])

/-! ## Re-keying a realm, and what this node has committed to -/

/-- Prints what a revoke or a rotation came to. -/
def reportRekey (out : Node.Rekey.Outcome) : IO Unit := do
  IO.println s!"realm     {out.realm}"
  IO.println s!"generation {out.generation} on the sequencer, in the keyring and in the log"
  match out.revoked with
  | some who => IO.println s!"revoked   {who}"
  | none => pure ()
  IO.println s!"granted   {String.intercalate ", " out.granted.toList}"
  IO.println s!"pushed    {out.pushed} entries under the new key"
  for (who, why) in out.stranded do
    IO.eprintln s!"stranded  {who}: {why}; they will read nothing written from now on"

/-- The session a command that needs a sequencer works through, or a refusal. -/
def needSession (ctx : Ctx) (p : Parsed) (what : String) : IO Node.Session := do
  match ← openSession ctx p with
  | some session => return session
  | none =>
    throw <| IO.userError s!"{what} needs a sequencer, and this store syncs with nothing; \
                             run 'resources sync init --sequencer URL'"

/--
Handler for `realm revoke`.

The member keeps what they have already read — nobody can take that back — and
reads nothing written from here on. See `Node/Rekey.lean` for the order the
three records are moved in and what an interrupted run leaves behind.
-/
def runRealmRevoke (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let member := flagStr p "member" ""
  if member.isEmpty then
    throw <| IO.userError "who is being put out: --member <id>"
  let session ← needSession ctx p "revoking a grant"
  reportRekey (← Node.Rekey.revoke session (flagStr p "realm" Realm.selfId.val) member)

/-- Handler for `realm rotate`: a new key for everybody who is already here. -/
def runRealmRotate (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let session ← needSession ctx p "rotating a realm key"
  reportRekey (← Node.Rekey.rotate session (flagStr p "realm" Realm.selfId.val))

/--
Handler for `checkpoint`.

One signed sentence per realm this node holds a key for, plus the local snapshot
`resources rebuild --from-checkpoint` starts from. A round of sync does this
too; the command exists for the times you want it now.
-/
def runCheckpoint (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let session ← needSession ctx p "publishing a checkpoint"
  let outcomes ← Node.checkpoint session (flagStr? p "realm")
  if outcomes.isEmpty then
    IO.println "this node holds no realm keys, so there is nothing it can commit to"
  for (realm, outcome) in outcomes do
    IO.println (outcome.describe realm)
  match ← Checkpoints.get? ctx.db "" with
  | some local' => IO.println s!"local     event {local'.seq}, {local'.stateHash}"
  | none => pure ()

/-! ## Receipts on the sequencer -/

/-- Handler for `blob push`: stores a file, encrypts it and uploads the ciphertext. -/
def runBlobPush (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let session ← needSession ctx p "uploading a receipt"
  let file : System.FilePath := argStr p "file"
  let sha ← Node.Blobs.putFile session file
  match ← Blobs.meta? ctx sha with
  | some stored =>
    IO.println s!"stored    {sha}"
    IO.println s!"uploaded  {stored.cipherHash.getD "nothing"}"
  | none => IO.println s!"stored    {sha}"

/--
Handler for `blob get`: fetches a receipt this node has the metadata for.

Everything that comes back is checked against a hash that arrived in the order,
so a sequencer that hands back the wrong bytes is caught here rather than
believed.
-/
def runBlobGet (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let session ← needSession ctx p "fetching a receipt"
  let sha := argStr p "sha"
  match ← Node.Blobs.get? session sha with
  | none => throw <| IO.userError s!"no receipt {sha} here, and the sequencer has none to give"
  | some bytes =>
    match flagStr? p "out" with
    | some out =>
      IO.FS.writeBinFile out bytes
      IO.println s!"wrote {bytes.size} bytes to {out}"
    | none => IO.println s!"{bytes.size} bytes, cached in {Blobs.path ctx sha}"

/--
Handler for `node`: the UI server, and a round of sync every half minute.

The loop shares the store with the server, as the server's own request handlers
share it with each other: one connection, one state in memory, and SQLite's
locking underneath. It only runs when there is a sequencer to talk to, so a
local-only node is `resources serve` with a longer name.
-/
partial def syncLoop (session : Node.Session) : IO Unit := do
  IO.sleep 30000
  try
    -- Recorded as well as printed, so that a status read between rounds says when
    -- the last one ran rather than "never".
    let r ← Node.Realms.record (← Node.round session)
    if r.applied > 0 || r.pushed > 0 || !r.trouble.isEmpty then
      IO.eprintln s!"sync: {r.applied} in, {r.pushed} out, at entry {r.seq}"
    unless r.trouble.isEmpty do
      IO.eprintln s!"sync: {r.trouble}"
  catch e =>
    IO.eprintln s!"sync: {e}"
  syncLoop session

/-- Handler for `node`. -/
def runNode (p : Parsed) : IO UInt32 := withLocal fun ctx => do
  noteInsecureDev p
  match ← openSession ctx p with
  | none => IO.eprintln "no sync.json: serving without syncing"
  | some session =>
    IO.eprintln s!"syncing with {(← Node.Settings.load ctx.cfg).sequencer} every 30s"
    -- The routes underneath need the same keys this loop opened, and there is no
    -- second way to get them: the passphrase was typed once.
    Node.Realms.hold session
    discard <| IO.asTask (syncLoop session) Task.Priority.dedicated
  Api.serve ctx
    { host := flagStr p "host" "127.0.0.1"
      port := ((flagStr p "port" "8087").toNat?.getD 8087).toUInt16
      webRoot := (flagStr? p "web").map System.FilePath.mk
      cors := flagStr? p "cors" }
    Node.Realms.api

/-- Handler for `status`. -/
def runStatus (_p : Parsed) : IO UInt32 := withBackend fun b => do
  IO.println s!"backend   {b.describe}"
  let j ← b.json (Call.get ["health"])
  IO.println s!"schema    {jstr j "schema"}"
  IO.println s!"actor     {jstr j "actor"}  (scopes {jstr j "scopes"})"
  let accounts ← b.json (Call.get ["accounts"])
  let txns ← b.json (Call.get ["transactions"] [("limit", "1")])
  IO.println s!"accounts  {(jarr accounts).size}"
  IO.println s!"txns      {jstr txns "total"}"
  IO.println s!"qrencode  {if ← Qr.available then "available" else "NOT FOUND"}"

/-- Handler for `api`, the escape hatch onto any route. -/
def runApi (p : Parsed) : IO UInt32 := withBackend fun b => do
  let method := (argStr p "method").toUpper
  let path := ((argStr p "path").splitOn "/").filter (fun s => !s.isEmpty)
  let query := (flagList p "query").filterMap fun kv =>
    (Str.splitOnce kv '=')
  let body := match flagStr? p "data" with
    | some d => d.toUTF8
    | none => ByteArray.empty
  match ← b.call { method, path, query, body,
                   headers := [("content-type", "application/json")] } with
  | .json _ payload => IO.println payload.pretty
  | .bytes _ _ data _ => IO.println ((String.fromUTF8? data).getD s!"<{data.size} bytes>")

/-- Handler for `gen-types`. -/
def runGenTypes (p : Parsed) : IO UInt32 := do
  match flagStr? p "out" with
  | some out => do
    IO.FS.writeFile out Api.TsGen.module
    IO.println s!"wrote {out}"
  | none => IO.print Api.TsGen.module
  return 0

/-- Handler for `gen-vectors`. -/
def runGenVectors (p : Parsed) : IO UInt32 := do
  let dir : System.FilePath := flagStr p "out" "conformance"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "README.md") Api.Vectors.readme
  IO.FS.writeFile (dir / "format-version") s!"{Api.Vectors.formatVersion}\n"
  IO.FS.writeFile (dir / "vectors.json") Api.Vectors.vectorsJson
  IO.FS.writeFile (dir / "rejects.json") Api.Vectors.rejectsJson
  IO.println s!"wrote {Api.Vectors.vectors.length} vectors and \
                {Api.Vectors.rejects.length} rejections to {dir}"
  return 0

/-- Handler for `migrate`. -/
def runMigrate (_p : Parsed) : IO UInt32 := withLocal fun ctx => do
  let v ← Schema.currentVersion ctx.db
  IO.println s!"schema version {v} at {ctx.cfg.dbPath}"

/--
Handler for `upgrade-format`: makes this store readable by a binary whose format
has moved past the one its log was written at.

Nothing is rewritten and nothing is thrown away. The log keeps every byte it
had, still chained, still hashing to what it says; what is added beside it is a
state to start folding from, written at the format this binary speaks. That is
the same bargain a newcomer already makes with a checkpoint, and it is why a
format change does not have to mean a new ledger: the identity, the order, the
members and the links all stay exactly as they were.

The state it writes down is the one in the tables, which is the projection the
*old* binary maintained -- the only reading of those entries anybody still has.
So this is run once, with the new binary, before anything asks the log to fold.
-/
def runUpgradeFormat (_p : Parsed) : IO UInt32 := withLocal (verifyChain := true) fun ctx => do
  let boundary ← Replay.formatBoundary ctx.db
  let (seq, _) ← EventLog.head ctx.db
  if seq == 0 then
    IO.println "this log is empty; there is nothing to upgrade"
    return
  if boundary == 0 then
    IO.println s!"every entry in this log was written at format {Encode.formatVersion}, \
                  which is the one this binary speaks; there is nothing to upgrade"
    return
  Node.Checkpoint.recordLocal ctx
  IO.println s!"entries 1 to {boundary} were written before format {Encode.formatVersion}"
  IO.println s!"wrote a checkpoint at entry {seq}, from the state the tables hold"
  IO.println "the log is untouched: every entry is still there and still verifies"
  -- The other half is for everybody else. A member joining, or replaying from
  -- the order rather than from these tables, needs a checkpoint of their realm
  -- published on the sequencer -- and this node cannot compute one, because
  -- computing it means reading the very entries it has grown past.
  match ← Node.Realms.session? ctx with
  | none => pure ()
  | some _ =>
    IO.println ""
    IO.println "this store syncs with a sequencer, and everybody else reading that ledger has"
    IO.println "to upgrade too — each of them runs this against their own tables. A published"
    IO.println "checkpoint cannot stand in for that yet."

/--
Handler for `rebuild`: computes the tables again from the log.

This is the phase-2 claim made executable. If the events are the ledger and the
tables are a cache of what they add up to, then deleting the cache and writing it
again from the replayed state has to be a no-op — so the last line printed is the
interesting one, and any answer but "the tables agreed with the log" is a bug in
a projection, now fixed.

It is also the one command that opens a store without checking the chain first,
because it is the command `Ctx.open`'s refusal names. What it can repair is a
cache: the ledger tables, and `ledger_head`, which is a cache of the end of the
chain. What it cannot repair is an event, and it does not pretend to — a row
whose bytes have changed still stops `Replay.events` here, with the same sentence
`Ctx.open` would have given.
-/
def runRebuild (p : Parsed) : IO UInt32 := withLocal (verifyChain := false) fun ctx => do
  let stored ← Load.fromDb ctx.db
  -- Folding from the beginning is what a rebuild means, and it is possible
  -- exactly while nothing in the log was written before this binary's format.
  -- Past that line the checkpoint is not a shortcut but the only reading there
  -- is, so it is taken without having to be asked for.
  let boundary ← Replay.formatBoundary ctx.db
  let (replayed, from') : State × Nat ←
    if p.hasFlag "from-checkpoint" || boundary > 0 then Replay.stateFrom ctx.db
    else do pure (← Replay.state ctx.db, 0)
  ctx.transaction do
    Project.reset ctx.db
    Project.all ctx.db replayed
    -- The head is a cache of the end of the chain, like every other table here,
    -- and this is the command that writes the caches again. `Ctx.open` refuses a
    -- store whose head has drifted and names this command; that would be an
    -- empty instruction if this did not put it back.
    Db.exec ctx.db "DELETE FROM ledger_head"
    Db.exec ctx.db "INSERT INTO ledger_head (id, seq, hash)
      SELECT 1, seq, hash FROM event ORDER BY seq DESC LIMIT 1"
  ctx.state.set replayed
  -- Read after the repair, so that what is printed is where the log now says it
  -- has got to rather than what the head claimed on the way in.
  let (seq, hash) ← EventLog.head ctx.db
  if from' == 0 then
    IO.println s!"replayed {seq} events, head {hash}"
  else
    IO.println s!"replayed {seq - from'} events after the snapshot at event {from'}, head {hash}"
    IO.println s!"the {from'} events it covers are still in the log; this phase archives nothing"
  IO.println (if stored == replayed then "the tables agreed with the log"
              else "the tables disagreed with the log and have been rebuilt from it")

end Cli
end Resources
