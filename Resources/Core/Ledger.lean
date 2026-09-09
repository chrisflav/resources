import Resources.Core.Money
import Resources.Core.Ids

/-!
# The ledger

A transaction is a list of postings whose amounts sum to zero per commodity.
Everything else in this system — categories, budgets, envelopes, reimbursements,
"accounts that aren't bank accounts" — is a consequence of that one rule rather
than a separate feature.

Postings are a `List` rather than an `Array` so the balance lemmas below are
provable by ordinary structural induction. A transaction has a handful of
postings; nothing here is on a hot path.
-/

open Lean

namespace Resources

instance : ToJson Date := ⟨fun d => Json.str d.toIso⟩
instance : FromJson Date := ⟨fun j => do
  let s ← j.getStr?
  match Date.ofIso? s with
  | some d => pure d
  | none => throw s!"not an ISO date: {s}"⟩

/-! ## Accounts -/

/-- The five classical account kinds. Sign conventions follow from this. -/
inductive AccountKind
  | asset | liability | equity | income | expense
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace AccountKind

/-- The lowercase name used in JSON and in the database. -/
def toString : AccountKind → String
  | .asset => "asset" | .liability => "liability" | .equity => "equity"
  | .income => "income" | .expense => "expense"

/-- Inverse of `toString`. -/
def ofString? : String → Option AccountKind
  | "asset" => some .asset | "liability" => some .liability | "equity" => some .equity
  | "income" => some .income | "expense" => some .expense | _ => none

instance : ToString AccountKind := ⟨AccountKind.toString⟩
instance : ToJson AccountKind := ⟨fun k => Json.str k.toString⟩
instance : FromJson AccountKind := ⟨fun j => do
  let s ← j.getStr?
  match ofString? s with
  | some k => pure k
  | none => throw s!"not an account kind: {s}"⟩

/-- Whether a positive posting increases the everyday reading of this account. -/
def isDebitNormal : AccountKind → Bool
  | .asset | .expense => true
  | _ => false

end AccountKind

/--
The fixed id of the ledger's own owner.

Every account has an owner and the overwhelming majority have this one, so it is
a constant rather than something looked up: a migration can backfill the column
in a single statement, and no code path has to bootstrap "who am I" before it
can read a balance.
-/
def Party.selfId : PartyId := ⟨"0000000000000000000000SELF"⟩

/--
An account. Names are dot-separated paths — `Assets.Bank.DKB.Giro`,
`Expenses.Travel.Trains`, `Budget.Rent` — and the hierarchy is what subtree
balances are computed over. Only some accounts correspond to a real bank
account; those carry an `iban`.
-/
structure Account where
  id : AccountId
  /-- Dot-separated path, e.g. `Assets.Bank.DKB.Giro`. -/
  name : String
  kind : AccountKind
  /--
  Whose account this is.

  The kind says what an account *is*; it has never said whose it is, and
  `asset` has spent this system's whole life standing in for `mine`. They are
  different questions: a friend's bank account is a real-money account, which is
  how it can fund a shared cost, and it is not yours, which is why it must never
  reach your net worth. Only the owner answers the second.
  -/
  owner : PartyId := Party.selfId
  /-- Restricts the account to a single commodity, when set. -/
  commodity : Option Commodity := none
  /-- Set when this account mirrors a real bank account. -/
  iban : Option String := none
  /-- Free-form note. -/
  note : Option String := none
  /-- Closed accounts are hidden by default and reject new postings. -/
  closedOn : Option Date := none
  deriving Repr, Inhabited, ToJson, FromJson

namespace Account

/-- The path components of an account name. -/
def components (name : String) : List String := name.splitOn "."

/-- Whether `name` is `under` itself or one of its descendants. -/
def isUnder (name under : String) : Bool :=
  name == under || name.startsWith (under ++ ".")

/-- The parent path, or `none` for a top-level account. -/
def parent (name : String) : Option String :=
  let cs := components name
  if cs.length ≤ 1 then none else some (String.intercalate "." cs.dropLast)

/-- The last path component. -/
def leaf (name : String) : String := (components name).getLastD name

/-- Whether this account is your own, as opposed to a participant's. -/
def mine (a : Account) : Bool := a.owner == Party.selfId

/--
Whether this account holds real money — for whoever owns it.

This is the funding-leg test, and it is deliberately blind to the owner: a
friend's bank account funds a cost exactly the way yours does. Whether the money
is *yours* is `mine`, and the two must not be run together.
-/
def holdsMoney (a : Account) : Bool := a.kind == .asset || a.kind == .liability

end Account

/-! ## People and labels -/

/-- A counterparty: an employer, a shop, a friend you split dinner with. -/
structure Party where
  id : PartyId
  name : String
  iban : Option String := none
  email : Option String := none
  note : Option String := none
  /--
  `contact` for someone you deal with deliberately, `merchant` for a name an
  importer produced. Only contacts are offered when there is a person to choose.
  -/
  kind : String := "merchant"
  deriving Repr, Inhabited, ToJson, FromJson

/-- A free-form tag on a transaction. -/
structure Label where
  id : LabelId
  name : String
  colour : Option String := none
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Postings and transactions -/

/-- One side of a transaction: an amount moving into an account. -/
structure Posting where
  account : AccountId
  amount : Amount
  /-- Who this leg involves, when it differs from the transaction's payee. -/
  party : Option PartyId := none
  note : Option String := none
  /--
  Which source entry this posting came from: an import fingerprint, or the id of
  a transaction that was merged into this one. All postings created from one
  bank line share it, which is what makes a merge reversible.
  -/
  origin : Option String := none
  /--
  What this posting is, as opposed to where it sits: `fee` for a card charge,
  say. An account can only hold a posting in one place, so anything that has to
  survive the posting being moved belongs here.
  -/
  tag : Option String := none
  deriving Repr, Inhabited, DecidableEq, ToJson, FromJson

/-- Where a transaction came from, so every row can be traced to its origin. -/
inductive Provenance
  /-- Entered by hand through the CLI or the web client, by the given token. -/
  | manual (actor : String)
  /-- Promoted from an import batch, carrying the fingerprint that dedupes it. -/
  | imported (batch : BatchId) (fingerprint : String)
  /-- Produced by a rule. -/
  | derived (rule : RuleId)
  deriving Repr, Inhabited, DecidableEq

namespace Provenance

/-- Compact textual encoding, stored in one column. -/
def encode : Provenance → String
  | .manual a => "manual:" ++ a
  | .imported b f => "import:" ++ b.val ++ ":" ++ f
  | .derived r => "rule:" ++ r.val

/-- Inverse of `encode`; unrecognised input degrades to a manual entry. -/
def decode (s : String) : Provenance :=
  match s.splitOn ":" with
  | ["manual", a] => .manual a
  | ["import", b, f] => .imported (BatchId.mk b) f
  | ["rule", r] => .derived (RuleId.mk r)
  | _ => .manual s

instance : ToJson Provenance := ⟨fun p => Json.str p.encode⟩
instance : FromJson Provenance := ⟨fun j => decode <$> j.getStr?⟩

end Provenance

/--
Whether a transaction has happened.

A `pending` transaction is a claim: a specific, dated, balanced movement that is
expected and may still fail to occur — the payment an invoice asks for, or the
transfer that squares a budget. It is a transaction because a promise that does
not balance is not a promise about money, and it is not `posted` because nothing
has moved.

A claim that is met becomes `settled`: the money did arrive, but it arrived as
its own transaction with its own bank leg, and the claim's job was only to say
what was expected. `void` is a claim that will never be performed — cancelled,
or written off — kept rather than deleted so the loss has something to point at.
Only `posted` reaches a balance.
-/
inductive TxnState
  | posted | pending | settled | void
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace TxnState

/-- The name used in JSON and in the database. -/
def toString : TxnState → String
  | .posted => "posted" | .pending => "pending"
  | .settled => "settled" | .void => "void"

/-- Inverse of `toString`. -/
def ofString? : String → Option TxnState
  | "posted" => some .posted | "pending" => some .pending
  | "settled" => some .settled | "void" => some .void | _ => none

/-- Whether a claim is still outstanding. -/
def open' : TxnState → Bool
  | .pending => true
  | _ => false

instance : ToString TxnState := ⟨TxnState.toString⟩
instance : ToJson TxnState := ⟨fun s => Json.str s.toString⟩
instance : FromJson TxnState := ⟨fun j => do
  let s ← j.getStr?
  match ofString? s with
  | some k => pure k
  | none => throw s!"not a transaction state: {s}"⟩

end TxnState

/-- A dated, balanced set of postings. -/
structure Transaction where
  id : TxId
  date : Date
  /-- Who the money went to or came from, as the bank reported it. -/
  payee : Option String := none
  /-- What it was for. -/
  narration : String := ""
  /--
  Whether this has happened. A pending transaction is excluded from every
  balance by the `posting` view, so it can be stored beside the ledger without
  being part of it.
  -/
  state : TxnState := .posted
  postings : List Posting
  labels : List LabelId := []
  source : Provenance := .manual "system"
  /-- Attached receipts, by content hash. -/
  attachments : List String := []
  deriving Repr, Inhabited, ToJson, FromJson

/-! ## Balance -/

namespace Posting

/-- This posting's contribution to the total of commodity `c`. -/
def net (c : String) (p : Posting) : Int :=
  if p.amount.commodity.code = c then p.amount.minor else 0

/-- This posting's contribution to account `a`'s balance in commodity `c`. -/
def netIn (a : AccountId) (c : String) (p : Posting) : Int :=
  if p.account = a then p.net c else 0

end Posting

namespace Transaction

/-- The commodities mentioned by this transaction, with duplicates. -/
def commodityCodes (t : Transaction) : List String :=
  t.postings.map (fun p => p.amount.commodity.code)

/-- The signed total of commodity `c` across all postings. Zero for a balanced transaction. -/
def net (t : Transaction) (c : String) : Int :=
  (t.postings.map (Posting.net c)).sum

/-- The signed total of commodity `c` landing in account `a`. -/
def netIn (t : Transaction) (a : AccountId) (c : String) : Int :=
  (t.postings.map (Posting.netIn a c)).sum

/-- The postings sum to zero in every commodity they mention. -/
def Balanced (t : Transaction) : Prop := ∀ c ∈ t.commodityCodes, t.net c = 0

instance (t : Transaction) : Decidable t.Balanced :=
  inferInstanceAs (Decidable (∀ c ∈ t.commodityCodes, t.net c = 0))

private theorem sum_net_eq_zero_of_not_mem (c : String) :
    ∀ ps : List Posting, c ∉ ps.map (fun p => p.amount.commodity.code) →
      (ps.map (Posting.net c)).sum = 0
  | [], _ => rfl
  | p :: ps, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.map_cons, List.sum_cons, Posting.net]
    rw [if_neg (fun hc => h.1 hc.symm), sum_net_eq_zero_of_not_mem c ps h.2]
    simp

/-- A balanced transaction nets to zero in *every* commodity, not only the ones it mentions. -/
theorem net_of_balanced {t : Transaction} (h : t.Balanced) (c : String) : t.net c = 0 := by
  by_cases hc : c ∈ t.commodityCodes
  · exact h c hc
  · exact sum_net_eq_zero_of_not_mem c t.postings hc

/-- The non-zero residuals, per commodity — what an unbalanced transaction is missing. -/
def residuals (t : Transaction) : List (String × Int) := Id.run do
  let mut seen : List String := []
  let mut out : List (String × Int) := []
  for c in t.commodityCodes do
    if !seen.contains c then
      seen := c :: seen
      let n := t.net c
      if n != 0 then out := (c, n) :: out
  return out.reverse

/-- Appends whatever postings are needed to make `t` balance, all into `account`. -/
def autoBalance (t : Transaction) (account : AccountId) : Transaction :=
  let extra := t.residuals.map fun (code, n) =>
    { account, amount := ⟨Commodity.ofCode code, -n⟩ : Posting }
  { t with postings := t.postings ++ extra }

/-- The only way into the store: rejects anything that does not balance. -/
def validate (t : Transaction) : Except String { t : Transaction // t.Balanced } :=
  if h : t.Balanced then .ok ⟨t, h⟩
  else
    let detail := String.intercalate ", " (t.residuals.map fun (c, n) => s!"{c} {n}")
    .error s!"transaction does not balance: {detail}"

/-- Total of the postings that land in `a`, as an `Amount`. -/
def amountIn (t : Transaction) (a : AccountId) (c : Commodity) : Amount :=
  ⟨c, t.netIn a c.code⟩

/-- Every account this transaction touches. -/
def accounts (t : Transaction) : List AccountId := t.postings.map (·.account)

/-! ### Merging

Two bank lines are often one economic event: a card purchase and the foreign-use
fee the bank posts beside it, or a transfer that appears in both accounts'
statements. Such lines belong in one transaction, and the postings union is
exactly that transaction.
-/

/-- Stamps every posting that has no origin yet, so a merge stays reversible. -/
def withOrigin (t : Transaction) (origin : String) : Transaction :=
  { t with postings := t.postings.map fun p =>
      { p with origin := p.origin <|> some origin } }

/-- Combines two transactions into one by concatenating their postings. -/
def mergeWith (t u : Transaction) : Transaction :=
  { t with
    postings := t.postings ++ u.postings
    labels := t.labels ++ u.labels.filter (fun l => !t.labels.contains l)
    attachments := t.attachments ++ u.attachments.filter (fun a => !t.attachments.contains a) }

@[simp] theorem net_mergeWith (t u : Transaction) (c : String) :
    (t.mergeWith u).net c = t.net c + u.net c := by
  simp [mergeWith, net, List.map_append, List.sum_append]

/--
Merging cannot unbalance the ledger. The postings of the result are the two
lists concatenated, and a sum over a concatenation is the sum of the sums.
-/
theorem balanced_mergeWith {t u : Transaction} (ht : t.Balanced) (hu : u.Balanced) :
    (t.mergeWith u).Balanced := by
  intro c _
  rw [net_mergeWith, net_of_balanced ht, net_of_balanced hu]
  simp

/-- Merges a whole list of transactions into `base`. -/
def mergeAll (base : Transaction) (rest : List Transaction) : Transaction :=
  rest.foldl mergeWith base

theorem balanced_mergeAll : ∀ (rest : List Transaction) (base : Transaction),
    base.Balanced → (∀ u ∈ rest, u.Balanced) → (base.mergeAll rest).Balanced
  | [], _, hb, _ => hb
  | u :: us, base, hb, h =>
    balanced_mergeAll us (base.mergeWith u)
      (balanced_mergeWith hb (h u (by simp)))
      (fun x hx => h x (by simp [hx]))

/-- The distinct origins present, in the order they first appear. -/
def origins (t : Transaction) : List String := Id.run do
  let mut seen : List String := []
  for p in t.postings do
    match p.origin with
    | some o => if !seen.contains o then seen := seen ++ [o]
    | none => pure ()
  return seen

/-- The postings belonging to one origin. -/
def postingsOf (t : Transaction) (origin : String) : List Posting :=
  t.postings.filter (fun p => p.origin == some origin)

/--
Splits a merged transaction back into one transaction per origin. Each part
balances exactly when the entry it came from did, which is guaranteed for
anything `mergeWith` built.
-/
def unmerge (t : Transaction) (freshIds : List TxId) : List Transaction :=
  (t.origins.zip freshIds).map fun (o, id) =>
    { t with id, postings := t.postingsOf o }

/-- Removes every posting on `account`; used to cancel counter-legs that a merge
made redundant. The result is re-validated by the caller rather than proved
balanced here, because it only balances when those postings summed to zero. -/
def dropAccount (t : Transaction) (a : AccountId) : Transaction :=
  { t with postings := t.postings.filter (fun p => p.account != a) }

/-- The net movement on one account, as an amount. -/
def netOn (t : Transaction) (a : AccountId) (c : Commodity) : Amount :=
  ⟨c, t.netIn a c.code⟩

/--
The leg that carries the transaction: the largest net movement, preferring an
account that holds a real balance, and on a tie the side the money left.

This is the figure a person recognises — a purchase merged with its fee reads as
one combined amount — and it is what both the ledger display and invoicing bill
from, so the two cannot disagree. `onSheet` says which accounts hold balances,
which the ledger core has no opinion about.
-/
def principal (t : Transaction) (onSheet : AccountId → Bool) : Option (AccountId × Amount) :=
  Id.run do
    let mut best : Option (AccountId × Amount × Int) := none
    let mut seen : List String := []
    for p in t.postings do
      let key := p.account.val ++ "|" ++ p.amount.commodity.code
      if seen.contains key then continue
      seen := key :: seen
      let net := t.netOn p.account p.amount.commodity
      if net.minor == 0 then continue
      let magnitude := if net.minor < 0 then -net.minor else net.minor
      let rank := if onSheet p.account then magnitude + 1000000000000 else magnitude
      let better :=
        match best with
        | none => true
        | some (_, bestAmount, bestRank) =>
          rank > bestRank || (rank == bestRank && net.minor < bestAmount.minor)
      if better then best := some (p.account, net, rank)
    return best.map fun (account, amount, _) => (account, amount)

end Transaction

/-! ## Ledgers -/

/-- A ledger is just a list of transactions; the store is a cache of one. -/
abbrev Ledger := List Transaction

namespace Ledger

/-- The balance of account `a` in commodity `c`. -/
def balance (l : Ledger) (a : AccountId) (c : String) : Int :=
  (l.map (fun t => t.netIn a c)).sum

/-- The total of commodity `c` across every account. -/
def totalNet (l : Ledger) (c : String) : Int :=
  (l.map (fun t => t.net c)).sum

/-- Adding a transaction shifts the balance by exactly that transaction's contribution. -/
@[simp] theorem balance_cons (t : Transaction) (l : Ledger) (a : AccountId) (c : String) :
    balance (t :: l) a c = t.netIn a c + balance l a c := by
  simp [balance]

/-- The trial balance: over balanced transactions, everything sums to zero. -/
theorem totalNet_eq_zero : ∀ (l : Ledger), (∀ t ∈ l, t.Balanced) → ∀ c, totalNet l c = 0
  | [], _, _ => rfl
  | t :: l, h, c => by
    have ih := totalNet_eq_zero l (fun t' ht' => h t' (by simp [ht'])) c
    simp only [totalNet, List.map_cons, List.sum_cons]
    simp only [totalNet] at ih
    rw [Transaction.net_of_balanced (h t (by simp)) c, ih]
    simp

/-- The balance of a whole subtree of accounts. -/
def subtreeBalance (l : Ledger) (accounts : List Account) (under : String) (c : String) : Int :=
  let ids := (accounts.filter (fun a => Account.isUnder a.name under)).map (·.id)
  (l.map (fun t => (ids.map (fun a => t.netIn a c)).sum)).sum

end Ledger

end Resources
