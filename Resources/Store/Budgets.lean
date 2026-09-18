import Resources.Store.Pendings

/-!
# Auxiliary budgets

A payment several people will bear leaves an account before anybody knows whose
it was. That gap — between paying and knowing — is what a budget names.

A shared payment is a loan from the paying account to an auxiliary budget. The
budget holds the money while it is unattributed; discharging it means deciding,
for each share, whose spending that money actually was. When every share is
decided the budget is empty, and a budget that is not empty is a worklist entry.

The budget account is **equity**, not an asset. A budget balance is not wealth
you hold: you have already parted with it, and the part that turns out to be
your own share is never coming back. Equity is the residual — the honest home
for "not attributed yet" — so assets minus liabilities states something true at
every step.

## Who paid, and whose it was

Those are different axes, and keeping them apart is what lets other people share
a budget at all. A cost can be funded by *anybody's* money account: your bank,
or a friend's, because a friend's bank account is a real-money account owned by
somebody else, and the owner is what keeps it out of your net worth. Allocation
then divides the whole pot regardless of who fronted which part.

Nothing has to net contributions against shares, because the ledger already
does. Somebody who put in more than their share ends up with their own account
carrying the difference, and the sign says which way it runs.

## Deciding is not paying

Allocation is a classification: whose consumption the money was. It becomes true
the moment it is decided, and no payment is outstanding for it. What may still
be outstanding is the transfer that squares everybody up, and that is a claim —
a transaction that has not happened (`Pendings`).

Collapsing the two would make your own expense contingent on somebody else's
bank transfer, and would leave a write-off with nothing to write off: voiding an
unpaid share would silently re-attribute their consumption to you. So `allocate`
posts the division and raises the claims, and they are separate entries because
they are separate facts.

Four operations, and none of them is "pay your own invoice":

* `lend` redirects a cost's non-funding leg into the budget. It rewrites the
  transaction in place, so no entry is invented and the funding leg — whoever's
  it is — still reconciles against a statement.
* `contribute` records a cost somebody else paid for directly.
* `allocate` divides what the budget holds among the participants, in one
  transaction, and raises the claims that would square it.
* settling is `Pendings.resolve` when the money arrives.

## What is left here

The arithmetic moved. Every question a budget can be asked — what it still
holds, what each person stands at, what a division would come to, which claims
would square it — is a function of the ledger, and so it lives in
`Core/Budgets.lean` as a function of `State`; the reads below call it rather
than asking the same question in SQL, because a query and a re-derivation are
two implementations and two implementations drift.

The writes are operations. What is left in each of them is the part `Core`
cannot do: mint an identifier, ask what day it is, and make sure the accounts an
operation will name already exist.
-/

open Lean SQLite

namespace Resources

private structure BudgetRow where
  id : String
  name : String
  note : Option String
  closedAt : Option String
  deriving Row

private structure ParticipantRow where
  ownerId : String
  ownerName : String
  account : String
  weight : Int64
  deriving Row

namespace Budgets

/-- How one cost is described on an allocation leg and on an invoice line. -/
def describe (t : Transaction) : String := Budget.describe t

/-- The account name a budget lives in. A bare name is placed under `Budget`. -/
def accountName (name : String) : String := Budget.accountName name

private def ofRow (r : BudgetRow) : Budget :=
  { id := ⟨r.id⟩, name := r.name, note := r.note, closed := r.closedAt.isSome }

private def cols : String :=
  "SELECT id, name, note, closed_at FROM budget"

/-- Every budget, newest first. -/
def list (ctx : Ctx) : IO (Array Budget) := do
  return (← Db.rows BudgetRow ctx.db (cols ++ " ORDER BY created_at DESC")).map ofRow

/-- Looks up a budget by id, by account name, or by its short name. -/
def get? (ctx : Ctx) (idOrName : String) : IO (Option Budget) := do
  let full := accountName idOrName
  let rows ← Db.rows BudgetRow ctx.db
    (cols ++ s!" WHERE id = {Db.lit idOrName} OR name = {Db.lit full}")
  return (rows.map ofRow)[0]?

/--
Creates a budget and its equity account, or returns the one already there.

One operation for both, because a budget without the account that holds it is
not half a budget: it is a name with nowhere for the money to wait.
-/
def «open» (ctx : Ctx) (name : String) (note : Option String := none) : IO Budget := do
  let full := accountName name
  match ← get? ctx full with
  | some b => return b
  | none =>
    let opening : Budget := { id := ⟨← freshId⟩, name := full, note, closed := false }
    -- Equity, deliberately: see the note at the top of this file.
    let acc : Account := { id := ⟨← freshId⟩, name := full, kind := .equity }
    let changes ← ctx.commit "system" [.openBudget opening acc]
    return (changes.findSome? fun
      | .budget bs => some bs.budget
      | _ => none).getD opening

/--
The realm a budget lives in: the one whose admins decide about it.

Written once by `openBudget` and read back here, because every operation on a
budget has to be written under that realm's key — `Core.checkBudget` refuses one
that is not — and so does every label and account those operations create.
-/
def realmOf (ctx : Ctx) (b : Budget) : IO RealmId := do
  let st ← ctx.state.get
  return ((st.budget? b.id).map (·.realm)).getD Realm.selfId

/-- The budget's own account. -/
def account (ctx : Ctx) (b : Budget) : IO Account := do
  Accounts.ensure ctx b.name (kind := some .equity) (realm := ← realmOf ctx b)

/-- The budget's label, ensured, so its costs can be found as a group. -/
def labelOf (ctx : Ctx) (b : Budget) : IO Label := do
  Labels.ensure ctx b.label (← realmOf ctx b)

/--
Who this budget is divided among, if that has been said.

Saying it is what turns the budget from a pot into a standing rule. An empty
list means it has not been said, and costs go on waiting in the account to be
divided by hand — which is what a budget is for when you genuinely do not know
yet.
-/
def participants (ctx : Ctx) (b : Budget) : IO (List Participant) := do
  let rows ← Db.rows ParticipantRow ctx.db
    s!"SELECT p.owner_id, pa.name, p.account, p.weight
       FROM budget_participant p JOIN party pa ON pa.id = p.owner_id
       WHERE p.budget_id = {Db.lit b.id.val} ORDER BY p.idx"
  return rows.toList.map fun r =>
    { owner := ⟨r.ownerId⟩, name := r.ownerName, account := r.account
      weight := r.weight.toInt.toNat }

/--
Records who a budget is divided among, replacing whatever was there.

Costs already booked keep the division they were booked under. That is not
laziness: they were divided under the rule in force at the time, and rewriting
them would change what somebody was told they owed for a weekend that is over.
-/
def setParticipants (ctx : Ctx) (b : Budget) (among : List Participant) : IO Unit := do
  discard <| ctx.commit "system" [.setParticipants b.id among] (realm := ← realmOf ctx b)

/-! ## Reading a budget

Every question below is arithmetic over the ledger, so every one of them is a
call into `Core/Budgets.lean` against the state the tables project. They used to
be SQL, and the SQL was right; what it could not be is the *same* right as the
operations, which compute from the state.
-/

/-- What the budget still holds, and so what is still undecided. -/
def balance (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) : IO Amount := do
  return Budget.balance b (← ctx.state.get) commodity

/-- Everything already handed to somebody, yourself included. -/
def allocated (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) : IO Amount := do
  return Budget.allocated b (← ctx.state.get) commodity

/-- What this budget has already given one person, whatever account it landed in. -/
def dividedTo (ctx : Ctx) (b : Budget) (owner : PartyId)
    (commodity : Commodity := Commodity.eur) : IO Int := do
  return Budget.dividedTo b (← ctx.state.get) owner commodity

/-- Where each person stands: what they bear, less what they put in. -/
def standings (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) :
    IO (Array Standing) := do
  return (Budget.standings b (← ctx.state.get) commodity).toArray

/-- The claims raised for this budget: outstanding and already met, but not voided. -/
def claims (ctx : Ctx) (b : Budget) : IO (Array Transaction) := do
  return (Budget.claims b (← ctx.state.get)).toArray

/-- Whether a claim has been written up as an invoice that still stands. -/
def spokenFor (ctx : Ctx) (t : Transaction) : IO Bool := do
  return Budget.spokenFor (← ctx.state.get) t

/--
The account a person settles through: the one of theirs this budget already
moved the most money across.

Whoever fronted a cost gets paid back into the account they fronted it from,
which is both what a person expects and the only choice that needs no
configuring. Somebody who only owes has no such leg, so it falls back to the
account of theirs this ledger sees most, and then to their purse — which is the
one case that may have to be created, because a purse nobody has used yet does
not exist.
-/
def settlementAccount (ctx : Ctx) (b : Budget) (owner : PartyId)
    (commodity : Commodity := Commodity.eur) : IO Account := do
  let s ← ctx.state.get
  match Budget.settlementAccount b s owner commodity with
  | .ok id =>
    let some acc := s.account? id | throw <| IO.userError s!"no such account: {id.val}"
    return acc
  | .error e =>
    let some p ← Parties.byId? ctx owner | throw <| IO.userError e
    Accounts.purse ctx p

/-- Everything a budget is made of: its costs and the divisions of them. -/
def entries (ctx : Ctx) (b : Budget) : IO (Array Transaction) := do
  return (Budget.entries b (← ctx.state.get)).toArray

/-- The costs a budget was lent, as opposed to the entries that divided them. -/
def costs (ctx : Ctx) (b : Budget) : IO (Array Transaction) := do
  return (Budget.costs b (← ctx.state.get)).toArray

/-- What each cost still has undivided, so allocating twice divides only the rest. -/
def remaining (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) :
    IO (Array (Transaction × Int)) := do
  return (Budget.remaining b (← ctx.state.get) commodity).toArray

/-- The lines an invoice for one person's share is made of: what landed on them. -/
def allocationLines (ctx : Ctx) (b : Budget) (owner : PartyId) :
    IO (Array (String × Amount)) := do
  return (Budget.allocationLines b (← ctx.state.get) owner).toArray

/-- What one person put into a budget, cost by cost. -/
def fundedLines (ctx : Ctx) (b : Budget) (owner : PartyId) : IO (Array (String × Amount)) := do
  return (Budget.fundedLines b (← ctx.state.get) owner).toArray

/-- Each participant's part of an amount, to the cent. -/
def shareOut (minor : Int) (among : List Participant) : List Int :=
  Budget.shareOut minor among

/--
Each participant's account, created if it is not there and checked for
ownership, so a typo fails before anything is written.

That check is the whole arrangement in one line: a share of somebody else's must
land in an account of theirs, or the division has quietly made it yours.
`Core` asks the same question of the state; what it cannot do is create the
account, which is why this runs first.
-/
def targetsOf (ctx : Ctx) (b : Budget) (among : List Participant) : IO (List AccountId) := do
  let realm ← realmOf ctx b
  -- One row per person. Two rows for the same owner would each be topped up
  -- against that owner's whole total, and both would be wrong.
  let owners := among.map (·.owner)
  if owners.eraseDups.length != owners.length then
    throw <| IO.userError "somebody appears twice; give each person one share"
  let mut out : List AccountId := []
  for p in among do
    if p.account.isEmpty then
      throw <| IO.userError s!"{p.name} has no account for their share"
    let target ← Accounts.ensure ctx p.account (owner := some p.owner) (realm := realm)
    if target.owner != p.owner then
      throw <| IO.userError
        s!"{p.account} belongs to somebody else, so {p.name} cannot have a share there"
    out := out ++ [target.id]
  return out

/-! ## Squaring up

Three things have to be true before a settlement can be an operation: the label
exists, everybody it could name has an account to be paid into, and there are
enough identifiers for the claims it may raise. None of them is a decision, and
all three are things `Core` cannot do for itself.
-/

/--
Makes sure a settlement has somewhere to land for everybody it could name.

`Core` picks the account each person settles through and can only pick one that
exists, while the people a division is about may have none yet. Asking it first
and creating a purse only where it has no answer is what keeps this from minting
accounts nobody needed.
-/
private def ensureSettlementAccounts (ctx : Ctx) (b : Budget) (commodity : Commodity)
    (among : List Participant) : IO Unit := do
  let s ← ctx.state.get
  let owners := ((Budget.standings b s commodity).map (·.owner) ++ among.map (·.owner)).eraseDups
  for owner in owners do
    if (Budget.settlementAccount b s owner commodity).toOption.isNone then
      match ← Parties.byId? ctx owner with
      | some p => discard <| Accounts.purse ctx p
      | none => pure ()

/--
Fresh identifiers for the claims a settlement may raise, with room to spare.

A plan asks at most one person per position, and `Core` refuses loudly rather
than quietly when it runs out — so the list is deliberately longer than any plan
can use, and what goes unused is simply never written.
-/
private def freshClaimIds (ctx : Ctx) (b : Budget) (commodity : Commodity)
    (among : List Participant) : IO (List TxId) := do
  let s ← ctx.state.get
  let mut out : List TxId := []
  for _ in [0 : (Budget.standings b s commodity).length + among.length + 4] do
    out := out ++ [⟨← freshId⟩]
  return out

/--
What each transaction a squaring-up wrote was written for.

Three kinds, told apart by what the id was beforehand: the division itself, an
id minted for this plan, which is a new claim, and an id that was already a
claim, which is one the facts have overtaken.
-/
private def settlementKinds (before : State) (ids : List TxId) (division : Option TxId) :
    TxId → Option String := fun x =>
  if division == some x then some "allocate"
  else if ids.contains x then some "claim"
  else if (before.txn? x).isSome then some "resettle"
  else none

/--
Raises the claims that would square the budget, and revises the ones already
raised.

Two kinds of claim are treated differently, because they are different things. A
claim that has been *met* is money that moved, so it is netted off: asking again
would ask twice. A claim that is merely outstanding is a request, and a request
made before a late receipt turned up was made on facts that have since changed —
so it is revised, or withdrawn, rather than left standing beside a contradicting
one. Nobody wants to be told to pay 200 and then handed 25 back.

The exception is a claim an invoice speaks for. That has been sent to somebody,
and a document already in their hands is not something to quietly rewrite; it is
netted off like a settled one, and the difference goes into a new claim. Voiding
the invoice makes its claim revisable again.

`hub`, when given, routes everything through one person instead of taking the
shortest plan. The shortest plan will cheerfully tell two people who never dealt
with each other to pay one another; a group usually wants the other thing.

Returns only what changed, so running this twice returns nothing the second
time.
-/
def settle (ctx : Ctx) (b : Budget) (actor : String) (commodity : Commodity := Commodity.eur)
    (hub : Option PartyId := none) (due : Option Date := none) : IO (Array Transaction) := do
  -- Refused before anything is created: a budget with money still in it has a
  -- residue belonging to nobody, and no set of transfers can settle that.
  let held ← balance ctx b commodity
  if held.minor != 0 then
    throw <| IO.userError
      s!"{Budget.shortName b} still holds {held.render} undivided; allocate it before settling"
  if (← standings ctx b commodity).isEmpty then return #[]
  let byDate ← match due with
    | some d => pure d
    | none => Date.today
  let lbl ← labelOf ctx b
  ensureSettlementAccounts ctx b commodity []
  let ids ← freshClaimIds ctx b commodity []
  let before ← ctx.state.get
  let changes ← ctx.commit actor [.settle b.id commodity hub byDate ids lbl.id]
    (kind := "resettle") (kinds := settlementKinds before ids none) (realm := ← realmOf ctx b)
  return Change.written changes

/--
Brings the claims up to date, when there is anything they could be up to date
with.

A budget still holding money nobody has been made responsible for cannot be
settled, and that is not a failure worth reporting every time somebody adds a
receipt — it is the ordinary state of a budget you have not divided yet. So this
is the version to call after a cost goes in: it settles when settling means
something, and otherwise leaves the claims where they are.
-/
def resettle (ctx : Ctx) (b : Budget) (actor : String)
    (commodity : Commodity := Commodity.eur) : IO (Array Transaction) := do
  if (← balance ctx b commodity).minor != 0 then return #[]
  settle ctx b actor commodity

/-! ## Adding to a budget -/

/--
Lends costs into a budget: the non-funding leg of each transaction is redirected
into it, to wait there until the budget is closed.

This rewrites the transactions rather than adding entries, so the funding leg is
untouched and reconciliation against a statement still holds. It is
`Txns.moveMany`, named for what it means here — and because "funding" is a
question about the kind of account rather than whose it is, a cost a friend paid
for is lent exactly the way one of yours is.
-/
def lend (ctx : Ctx) (b : Budget) (ids : Array TxId) (actor : String) :
    IO (Array Transaction) := do
  if b.closed then
    throw <| IO.userError s!"{Budget.shortName b} is closed; reopen it to add costs"
  Txns.moveMany ctx ids b.name actor

/--
Records a cost somebody else paid for, straight into the budget.

Their money account is credited and the budget is debited, which is the same
entry `lend` produces for one of yours. Nothing of yours moves: the accounts this
touches are the budget and one belonging to them.
-/
def contribute (ctx : Ctx) (b : Budget) (from_ : Account) (amount : Amount) (date : Date)
    (narration : String) (actor : String) (payee : Option String := none) :
    IO Transaction := do
  let acc ← account ctx b
  let t : Transaction :=
    { id := ⟨← freshId⟩, date, payee, narration
      postings :=
        [{ account := acc.id, amount },
         { account := from_.id, amount := ⟨amount.commodity, -amount.minor⟩ }]
      source := .manual actor }
  let changes ← ctx.commit actor [.contribute b.id t] (kind := "contribute")
    (realm := ← realmOf ctx b)
  match (Change.written changes)[0]? with
  | some added => return added
  | none => throw <| IO.userError "a contribution has to be an amount that was spent"

/-! ## Dividing -/

/--
Divides what the budget holds among the participants, in one transaction, and
raises the claims that would square it.

Each cost is divided separately so the entry says which part of which purchase
each person bears, and an invoice can be rendered from the legs without dividing
anything a second time. `splitParts` guarantees the parts of each cost add back
to it exactly, so the participants' totals add back to the budget exactly too.

Allocating twice is allowed and normal: a receipt turns up after the weekend, it
is lent into the same budget, and a second allocation divides just what is left.
Every leg is tagged `allocation`, because none of this is money moving — it is
money already spent being told whose it was.
-/
def allocate (ctx : Ctx) (b : Budget) (among : List Participant) (actor : String)
    (commodity : Commodity := Commodity.eur) (date : Option Date := none)
    (hub : Option PartyId := none) :
    IO (Option (Transaction × Array Transaction)) := do
  if among.isEmpty then throw <| IO.userError "say who to divide this among"
  -- Nothing left to divide is not a failure, and it is answered before anything
  -- is created: a division that was never going to happen should not leave
  -- accounts and labels behind it.
  if (← remaining ctx b commodity).isEmpty then return none
  discard <| targetsOf ctx b among
  let lbl ← labelOf ctx b
  ensureSettlementAccounts ctx b commodity among
  let today ← match date with
    | some d => pure d
    | none => Date.today
  let txnId : TxId := ⟨← freshId⟩
  let ids ← freshClaimIds ctx b commodity among
  let before ← ctx.state.get
  let changes ← ctx.commit actor [.allocate b.id among commodity today hub txnId ids lbl.id]
    (kind := "allocate") (kinds := settlementKinds before ids (some txnId))
    (realm := ← realmOf ctx b)
  let written := Change.written changes
  match written.find? (·.id == txnId) with
  | none => return none
  | some divided => return some (divided, written.filter (·.id != txnId))

/--
Closes a budget: divides everything still waiting, and asks for what that leaves
people owing.

Closing is the moment of decision, and it is deliberate. Until it happens costs
simply accumulate in the account, which is what the account is for; afterwards
nobody can add to it, including everybody else in its realm.

Reopening it and closing again writes a *new* division covering only what came
in since. The first one is not touched: it recorded a decision about a set of
costs on a particular day, and somebody was told what they owed on the strength
of it. `remaining` is what keeps the second from dividing the first again.

The budget is marked closed last, inside the same operation. A failure between
dividing and closing leaves it open, and closing again then divides only
whatever is still waiting — where a half-applied close that had already flipped
the flag would be a budget nobody could finish dividing.
-/
def close (ctx : Ctx) (b : Budget) (actor : String) (commodity : Commodity := Commodity.eur)
    (among : Option (List Participant) := none) (hub : Option PartyId := none)
    (date : Option Date := none) : IO (Option Transaction × Array Transaction) := do
  if b.closed then
    throw <| IO.userError s!"{Budget.shortName b} is already closed"
  let people ← match among with
    | some ps => pure ps
    | none => participants ctx b
  if people.isEmpty then
    throw <| IO.userError
      s!"say who shares {Budget.shortName b} first: budget among {Budget.shortName b} anna= …"
  if !(← remaining ctx b commodity).isEmpty then
    discard <| targetsOf ctx b people
  let lbl ← labelOf ctx b
  ensureSettlementAccounts ctx b commodity people
  let today ← match date with
    | some d => pure d
    | none => Date.today
  let txnId : TxId := ⟨← freshId⟩
  let ids ← freshClaimIds ctx b commodity people
  let before ← ctx.state.get
  let changes ← ctx.commit actor
    [.closeBudget b.id (some people) commodity hub today txnId ids lbl.id]
    (kind := "allocate") (kinds := settlementKinds before ids (some txnId))
    (realm := ← realmOf ctx b)
  let written := Change.written changes
  return (written.find? (·.id == txnId), written.filter (·.id != txnId))

/--
Reopens a closed budget so more costs can go in.

Nothing that was decided is undone: every division stands, and so does every
claim raised from one. What changes is only that the budget can be added to
again — and until it is closed once more, what everybody was last told remains
what they were last told.
-/
def reopen (ctx : Ctx) (b : Budget) (_actor : String) : IO Unit := do
  discard <| ctx.commit "system" [.reopenBudget b.id] (realm := ← realmOf ctx b)

/-- Deletes a budget's bookkeeping. The transactions it touched are left alone. -/
def delete (ctx : Ctx) (b : Budget) : IO Unit := do
  discard <| ctx.commit "system" [.deleteBudget b.id] (realm := ← realmOf ctx b)

end Budgets

end Resources
