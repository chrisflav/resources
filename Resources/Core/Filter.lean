import Resources.Core.Ledger

/-!
# The filter language

One datatype, three consumers: the CLI parses it from argv, the web client puts
it in the URL, and the API parses it from a query parameter. It has two
interpretations — a reference semantics over in-memory transactions, and a
compiler to a SQL `WHERE` fragment — which are checked against each other in the
test suite. That is the honest version of "verified queries": proving `toSql`
sound against SQLite's semantics is out of reach, agreement testing is not.

Syntax, roughly `account:Assets.Bank date>=2026-01-01 -label:private (a OR b)`:
space means AND, `-` negates, `OR` is a keyword, parentheses group.
-/

open Lean

namespace Resources

/-- A predicate over transactions. -/
inductive Filter
  /-- Matches everything. -/
  | all
  /-- Some posting lands in this account or one of its descendants. -/
  | account (under : String)
  /-- On or after this date. -/
  | dateFrom (d : Date)
  /-- On or before this date. -/
  | dateTo (d : Date)
  /-- Some posting is at least this amount. -/
  | amountFrom (a : Amount)
  /-- Some posting is at most this amount. -/
  | amountTo (a : Amount)
  /-- Carries this label. -/
  | label (name : String)
  /-- Some posting names this party. -/
  | party (name : String)
  /-- Some posting lands in an account owned by this person. -/
  | owner (name : String)
  /-- The payee contains this text. -/
  | payee (needle : String)
  /-- The payee or narration contains this text. -/
  | text (needle : String)
  /-- Some posting is in this commodity. -/
  | commodity (code : String)
  /-- Some posting carries this tag, wherever it currently sits. -/
  | tag (name : String)
  /-- Conjunction. -/
  | and (a b : Filter)
  /-- Disjunction. -/
  | or (a b : Filter)
  /-- Negation. -/
  | not (a : Filter)
  deriving Repr, Inhabited

namespace Filter

/-- Name lookups needed to evaluate a filter against in-memory transactions. -/
structure Env where
  accountName : AccountId → Option String
  labelName : LabelId → Option String
  partyName : PartyId → Option String
  /-- The name of the person an account belongs to. -/
  accountOwner : AccountId → Option String

/-- Builds an `Env` from the entities currently in the store. -/
def Env.ofLists (accounts : List Account) (labels : List Label) (parties : List Party) : Env where
  accountName id := (accounts.find? (·.id == id)).map (·.name)
  labelName id := (labels.find? (·.id == id)).map (·.name)
  partyName id := (parties.find? (·.id == id)).map (·.name)
  accountOwner id := do
    let a ← accounts.find? (·.id == id)
    let p ← parties.find? (·.id == a.owner)
    pure p.name

/-- The reference semantics. -/
def eval (env : Env) : Filter → Transaction → Bool
  | .all, _ => true
  | .account under, t =>
    t.postings.any fun p =>
      match env.accountName p.account with
      | some n => Account.isUnder n under
      | none => false
  | .dateFrom d, t => Date.le d t.date
  | .dateTo d, t => Date.le t.date d
  | .amountFrom a, t =>
    t.postings.any fun p => p.amount.commodity == a.commodity && p.amount.minor >= a.minor
  | .amountTo a, t =>
    t.postings.any fun p => p.amount.commodity == a.commodity && p.amount.minor <= a.minor
  | .label name, t =>
    t.labels.any fun l => (env.labelName l).map (· == name) |>.getD false
  | .party name, t =>
    t.postings.any fun p =>
      match p.party with
      | some pid => (env.partyName pid).map (· == name) |>.getD false
      | none => false
  | .owner name, t =>
    t.postings.any fun p => (env.accountOwner p.account).map (· == name) |>.getD false
  -- An empty needle means "this field is empty", not "match everything": a rule
  -- written as `payee:""` should find the rows with no payee, not sweep up the
  -- whole ledger.
  | .payee needle, t =>
    if needle.isEmpty then (t.payee.getD "").isEmpty
    else Str.containsCI (t.payee.getD "") needle
  | .text needle, t =>
    let hay := t.payee.getD "" ++ " " ++ t.narration
    if needle.isEmpty then hay.trimAscii.isEmpty else Str.containsCI hay needle
  | .commodity code, t => t.postings.any fun p => p.amount.commodity.code == code.toUpper
  | .tag name, t => t.postings.any fun p => p.tag == some name
  | .and a b, t => eval env a t && eval env b t
  | .or a b, t => eval env a t || eval env b t
  | .not a, t => !eval env a t

/-! ## Compilation to SQL -/

/-- Escapes a SQL string literal by doubling embedded quotes. -/
def sqlLit (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

/-- Escapes a `LIKE` pattern operand, then wraps it in `%` on both sides. -/
private def likeLit (s : String) : String :=
  sqlLit ("%" ++ (s.replace "\\" "\\\\" |>.replace "%" "\\%" |>.replace "_" "\\_") ++ "%")

/--
Compiles to a boolean SQL expression over a transaction row aliased `t`.
Posting-level conditions become `EXISTS` subqueries, which is what makes
`account:` mean "some posting is in this account".
-/
def toSql : Filter → String
  | .all => "1"
  | .account under =>
    "EXISTS (SELECT 1 FROM posting_all p JOIN account a ON a.id = p.account_id " ++
    "WHERE p.txn_id = t.id AND (a.name = " ++ sqlLit under ++
    " OR a.name LIKE " ++ sqlLit (under ++ ".%") ++ "))"
  | .dateFrom d => "t.date >= " ++ sqlLit d.toIso
  | .dateTo d => "t.date <= " ++ sqlLit d.toIso
  | .amountFrom a =>
    "EXISTS (SELECT 1 FROM posting_all p WHERE p.txn_id = t.id AND p.commodity = " ++
    sqlLit a.commodity.code ++ " AND p.minor >= " ++ toString a.minor ++ ")"
  | .amountTo a =>
    "EXISTS (SELECT 1 FROM posting_all p WHERE p.txn_id = t.id AND p.commodity = " ++
    sqlLit a.commodity.code ++ " AND p.minor <= " ++ toString a.minor ++ ")"
  | .label name =>
    "EXISTS (SELECT 1 FROM txn_label tl JOIN label l ON l.id = tl.label_id " ++
    "WHERE tl.txn_id = t.id AND l.name = " ++ sqlLit name ++ ")"
  | .party name =>
    "EXISTS (SELECT 1 FROM posting_all p JOIN party pa ON pa.id = p.party_id " ++
    "WHERE p.txn_id = t.id AND pa.name = " ++ sqlLit name ++ ")"
  | .owner name =>
    "EXISTS (SELECT 1 FROM posting_all p JOIN account a ON a.id = p.account_id " ++
    "JOIN party pa ON pa.id = a.owner_id " ++
    "WHERE p.txn_id = t.id AND pa.name = " ++ sqlLit name ++ ")"
  | .payee needle =>
    if needle.isEmpty then "IFNULL(t.payee,'') = ''"
    else "(IFNULL(t.payee,'') LIKE " ++ likeLit needle ++ " ESCAPE '\\')"
  | .text needle =>
    if needle.isEmpty then "TRIM(IFNULL(t.payee,'') || ' ' || t.narration) = ''"
    else "((IFNULL(t.payee,'') || ' ' || t.narration) LIKE " ++ likeLit needle ++ " ESCAPE '\\')"
  | .commodity code =>
    "EXISTS (SELECT 1 FROM posting_all p WHERE p.txn_id = t.id AND p.commodity = " ++
    sqlLit code.toUpper ++ ")"
  | .tag name =>
    "EXISTS (SELECT 1 FROM posting_all p WHERE p.txn_id = t.id AND p.tag = " ++ sqlLit name ++ ")"
  | .and a b => "(" ++ toSql a ++ " AND " ++ toSql b ++ ")"
  | .or a b => "(" ++ toSql a ++ " OR " ++ toSql b ++ ")"
  | .not a => "(NOT " ++ toSql a ++ ")"

/-! ## Parsing -/

private structure Tok where
  text : String
  deriving Repr

/-- Splits a filter expression into tokens, respecting double quotes and parentheses. -/
private def tokenize (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur := ""
  let mut inQuote := false
  for ch in s.toList do
    if inQuote then
      if ch == '"' then inQuote := false else cur := cur.push ch
    else if ch == '"' then inQuote := true
    else if ch == ' ' then
      if !cur.isEmpty then out := cur :: out; cur := ""
    else if ch == '(' || ch == ')' then
      if !cur.isEmpty then out := cur :: out; cur := ""
      out := String.singleton ch :: out
    else cur := cur.push ch
  if !cur.isEmpty then out := cur :: out
  return out.reverse

private def parseAtomWord (w : String) : Except String Filter := do
  let mkDate (v : String) : Except String Date :=
    match Date.ofIso? v with
    | some d => .ok d
    | none => .error s!"not an ISO date: {v}"
  if w == "*" then return .all
  match Str.splitOnce w ':' with
  | some ("account", v) => return .account v
  | some ("acc", v) => return .account v
  | some ("label", v) => return .label v
  | some ("party", v) => return .party v
  | some ("owner", v) => return .owner v
  | some ("payee", v) => return .payee v
  | some ("text", v) => return .text v
  | some ("commodity", v) => return .commodity v
  | some ("tag", v) => return .tag v
  | some ("cur", v) => return .commodity v
  | some ("date", v) => return .and (.dateFrom (← mkDate v)) (.dateTo (← mkDate v))
  | _ =>
    if let some v := Str.dropPrefix? w "date>=" then return .dateFrom (← mkDate v)
    else if let some v := Str.dropPrefix? w "date<=" then return .dateTo (← mkDate v)
    else if let some v := Str.dropPrefix? w "amount>=" then
      return .amountFrom (← Amount.parse v)
    else if let some v := Str.dropPrefix? w "amount<=" then
      return .amountTo (← Amount.parse v)
    else return .text w

mutual

private partial def parseOr (ts : List String) : Except String (Filter × List String) := do
  let (lhs, rest) ← parseAnd ts
  match rest with
  | "OR" :: more | "or" :: more =>
    let (rhs, rest') ← parseOr more
    return (.or lhs rhs, rest')
  | _ => return (lhs, rest)

private partial def parseAnd (ts : List String) : Except String (Filter × List String) := do
  let (lhs, rest) ← parseUnary ts
  match rest with
  | [] => return (lhs, [])
  | ")" :: _ => return (lhs, rest)
  | "OR" :: _ | "or" :: _ => return (lhs, rest)
  | "AND" :: more | "and" :: more =>
    let (rhs, rest') ← parseAnd more
    return (.and lhs rhs, rest')
  | _ =>
    let (rhs, rest') ← parseAnd rest
    return (.and lhs rhs, rest')

private partial def parseUnary : List String → Except String (Filter × List String)
  | [] => .error "unexpected end of filter"
  | "(" :: rest => do
    let (inner, rest') ← parseOr rest
    match rest' with
    | ")" :: more => return (inner, more)
    | _ => .error "unbalanced parenthesis in filter"
  | w :: rest =>
    if w.startsWith "-" && w.length > 1 then do
      let f ← parseAtomWord (w.drop 1).toString
      return (.not f, rest)
    else do
      let f ← parseAtomWord w
      return (f, rest)

end

/-- Parses a filter expression. An empty string matches everything. -/
def parse (s : String) : Except String Filter := do
  let ts := tokenize s
  if ts.isEmpty then return .all
  let (f, rest) ← parseOr ts
  if !rest.isEmpty then .error s!"trailing input in filter: {String.intercalate " " rest}"
  return f

/-- Renders a filter back to its source syntax, for round-tripping through URLs. -/
partial def render : Filter → String
  | .all => "*"
  | .account u => "account:" ++ u
  | .dateFrom d => "date>=" ++ d.toIso
  | .dateTo d => "date<=" ++ d.toIso
  | .amountFrom a => "amount>=" ++ a.digits ++ a.commodity.code
  | .amountTo a => "amount<=" ++ a.digits ++ a.commodity.code
  | .label n => "label:" ++ n
  | .party n => "party:" ++ n
  | .owner n => "owner:" ++ n
  | .payee n => "payee:\"" ++ n ++ "\""
  | .text n => "text:\"" ++ n ++ "\""
  | .commodity c => "commodity:" ++ c
  | .tag n => "tag:" ++ n
  | .and a b => "(" ++ render a ++ " " ++ render b ++ ")"
  | .or a b => "(" ++ render a ++ " OR " ++ render b ++ ")"
  | .not a => "-" ++ render a

/-- How a result set is ordered. -/
inductive SortKey
  | date | amount | payee | narration | created
  deriving Repr, Inhabited, DecidableEq

/-- Sort direction and key. -/
structure SortSpec where
  key : SortKey := .date
  descending : Bool := true
  deriving Repr, Inhabited

namespace SortSpec

/-- The `ORDER BY` clause, always tie-broken by id so paging is stable. -/
def toSql (s : SortSpec) : String :=
  let dir := if s.descending then "DESC" else "ASC"
  let col :=
    match s.key with
    | .date => "t.date"
    -- The signed movement on the balance-sheet accounts: the same figure the
    -- ledger displays, so ordering matches what the reader sees. Summing also
    -- makes a merged purchase-plus-fee sort by its combined total.
    | .amount =>
      "(SELECT IFNULL(SUM(p.minor), 0) FROM posting_all p JOIN account a ON a.id = p.account_id
        WHERE p.txn_id = t.id AND a.kind IN ('asset', 'liability'))"
    | .payee => "IFNULL(t.payee,'')"
    | .narration => "t.narration"
    | .created => "t.created_at"
  s!"ORDER BY {col} {dir}, t.id {dir}"

/-- Parses `date`, `-date`, `amount`, `-amount`, … -/
def parse (s : String) : SortSpec :=
  let (desc, name) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let key :=
    match name with
    | "amount" => SortKey.amount
    | "payee" => SortKey.payee
    | "narration" => SortKey.narration
    | "created" => SortKey.created
    | _ => SortKey.date
  { key, descending := desc }

end SortSpec

end Filter

end Resources
