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
-/

open Lean SQLite

namespace Resources

/-- Someone a budget is divided among. -/
structure Participant where
  /-- Whose share this is. -/
  owner : PartyId
  /-- Their name, for messages and for the allocation's own legs. -/
  name : String
  /--
  Where their share lands.

  For you, the expense account it belongs to — which is the whole reason your
  share is a posting and not an implicit subtraction. For somebody else, an
  account of *theirs*: their purse by default, or one of their expense accounts
  if you are keeping that much of their books.
  -/
  account : String
  /-- Relative size of the share. Equal shares are all `1`. -/
  weight : Nat := 1
  deriving Repr, Inhabited

namespace Participant

/-- Whether this share is your own. -/
def mine (p : Participant) : Bool := p.owner == Party.selfId

end Participant

/-- Money paid out and not yet attributed. -/
structure Budget where
  id : BudgetId
  /-- The equity account holding it, e.g. `Budget.Zinalrothorn2026`. -/
  name : String
  note : Option String
  closed : Bool
  deriving Repr, Inhabited

namespace Budget

/-- The short name, without the `Budget.` prefix. -/
def shortName (b : Budget) : String :=
  if b.name.startsWith "Budget." then (b.name.drop 7).toString else b.name

/-- The label the claims raised for this budget carry. -/
def label (b : Budget) : String := "budget:" ++ b.shortName

end Budget

/--
One person's net position in a budget: what they were allocated, less what they
put in. Positive means they owe the group.
-/
structure Standing where
  owner : PartyId
  name : String
  amount : Amount
  deriving Repr, Inhabited

namespace Standing

/-- The position, as the settlement arithmetic sees it. -/
def position (s : Standing) : Settle.Position := { who := s.owner.val, minor := s.amount.minor }

end Standing

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

private structure StandingRow where
  ownerId : String
  ownerName : String
  minor : Int64
  deriving Row

namespace Budgets

/-- How one cost is described on an allocation leg and on an invoice line. -/
def describe (t : Transaction) : String :=
  let what := (t.payee.getD "").trimAscii.toString
  if what.isEmpty then s!"{t.date.toIso} — {Str.clamp t.narration 60}"
  else s!"{t.date.toIso} — {Str.clamp what 60}"

/-- The account name a budget lives in. A bare name is placed under `Budget`. -/
def accountName (name : String) : String :=
  if name.startsWith "Budget." then name else "Budget." ++ name

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

/-- Creates a budget and its equity account, or returns the one already there. -/
def «open» (ctx : Ctx) (name : String) (note : Option String := none) : IO Budget := do
  let full := accountName name
  match ← get? ctx full with
  | some b => return b
  | none =>
    let id ← freshId
    let now ← nowStamp
    -- Equity, deliberately: see the note at the top of this file.
    discard <| Accounts.ensure ctx full (kind := some .equity)
    Db.exec ctx.db s!"INSERT INTO budget (id, name, note, created_at, closed_at)
                      VALUES ({Db.lit id}, {Db.lit full}, {Db.litOpt note}, {Db.lit now}, NULL)"
    return { id := ⟨id⟩, name := full, note, closed := false }

/-- The budget's own account. -/
def account (ctx : Ctx) (b : Budget) : IO Account :=
  Accounts.ensure ctx b.name (kind := some .equity)

/-- The budget's label, ensured, so its costs can be found as a group. -/
def labelOf (ctx : Ctx) (b : Budget) : IO Label :=
  Labels.ensure ctx b.label

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
  ctx.transaction do
    Db.exec ctx.db s!"DELETE FROM budget_participant WHERE budget_id = {Db.lit b.id.val}"
    for (p, i) in among.zipIdx do
      Db.exec ctx.db s!"INSERT INTO budget_participant (budget_id, idx, owner_id, account, weight)
        VALUES ({Db.lit b.id.val}, {i}, {Db.lit p.owner.val}, {Db.lit p.account},
                {max p.weight 1})"

/-- What the budget still holds, and so what is still undecided. -/
def balance (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) : IO Amount := do
  let acc ← account ctx b
  let n ← Db.scalarInt ctx.db
    s!"SELECT IFNULL(SUM(minor), 0) FROM posting
       WHERE account_id = {Db.lit acc.id.val} AND commodity = {Db.lit commodity.code}"
  return ⟨commodity, n⟩

/--
Everything already handed to somebody, yourself included.

Read as "what landed on somebody" rather than "what carries the allocation tag",
because a cost booked already divided has no allocation entry to tag: its shares
are legs of the cost itself. A share is a positive movement onto an account that
is not the budget's; a funding leg is negative, and the budget's own leg is
excluded, so the two cannot be confused.
-/
def allocated (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) : IO Amount := do
  let acc ← account ctx b
  let n ← Db.scalarInt ctx.db
    s!"SELECT IFNULL(SUM(p.minor), 0) FROM posting p
       WHERE p.minor > 0
         AND p.commodity = {Db.lit commodity.code}
         AND p.account_id != {Db.lit acc.id.val}
         AND p.txn_id IN (SELECT txn_id FROM posting WHERE account_id = {Db.lit acc.id.val})
"
  return ⟨commodity, n⟩

/--
What this budget has already given one person, whatever account it landed in.

Read per owner rather than per account, because a share booked to somebody's
expense category once and their purse the next time is still the same person's
share — and because that is the figure a further division has to top up rather
than start from.
-/
def dividedTo (ctx : Ctx) (b : Budget) (owner : PartyId)
    (commodity : Commodity := Commodity.eur) : IO Int := do
  let acc ← account ctx b
  Db.scalarInt ctx.db
    s!"SELECT IFNULL(SUM(p.minor), 0) FROM posting p
       JOIN account a ON a.id = p.account_id
       WHERE p.minor > 0
         AND p.commodity = {Db.lit commodity.code}
         AND a.owner_id = {Db.lit owner.val}
         AND a.id != {Db.lit acc.id.val}
         AND p.txn_id IN (SELECT txn_id FROM posting WHERE account_id = {Db.lit acc.id.val})"

/-! ## Standing and settlement -/

/--
Where each person stands: everything the budget's transactions moved across
their accounts, the budget's own account excluded.

That exclusion is what makes the figure mean something. Include the budget and
you are asking "how much money went through this pot", which is a fact about the
pot; exclude it and you are asking "how much of it was this person's, less what
they put in", which is a fact about the person. The second is the settlement.

The positions sum to minus what the budget still holds, so they sum to zero
exactly when everything has been divided — which is why `settle` refuses to plan
against a budget with money still in it. There would be a residue belonging to
nobody, and no set of transfers can settle that.
-/
def standings (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) :
    IO (Array Standing) := do
  let acc ← account ctx b
  let rows ← Db.rows StandingRow ctx.db
    s!"SELECT pa.id, pa.name, IFNULL(SUM(p.minor), 0)
       FROM posting p
       JOIN account a ON a.id = p.account_id
       JOIN party pa ON pa.id = a.owner_id
       WHERE p.commodity = {Db.lit commodity.code}
         AND a.id != {Db.lit acc.id.val}
         AND p.txn_id IN (SELECT txn_id FROM posting WHERE account_id = {Db.lit acc.id.val})

       GROUP BY pa.id, pa.name
       HAVING SUM(p.minor) != 0
       ORDER BY pa.name"
  return rows.map fun r =>
    { owner := ⟨r.ownerId⟩, name := r.ownerName, amount := ⟨commodity, r.minor.toInt⟩ }

/--
The claims raised for this budget: outstanding and already met, but not voided.

Netting depends on that distinction. A claim that was met is money somebody has
already moved, so asking again would ask twice; a claim that was voided is money
that will never move, so the position it was raised against still stands.
-/
def claims (ctx : Ctx) (b : Budget) : IO (Array Transaction) := do
  return (← Pendings.history ctx (.label b.label)).filter fun t => t.state != .void

/--
The account a person settles through: the one of theirs this budget already
moved the most money across.

Whoever fronted a cost gets paid back into the account they fronted it from,
which is both what a person expects and the only choice that needs no
configuring. Somebody who only owes has no such leg, so it falls back to the
account of theirs this ledger sees most, and then to their purse.
-/
def settlementAccount (ctx : Ctx) (b : Budget) (owner : PartyId)
    (commodity : Commodity := Commodity.eur) : IO Account := do
  let acc ← account ctx b
  let inBudget ← Db.row? String ctx.db
    s!"SELECT a.name FROM posting p JOIN account a ON a.id = p.account_id
       WHERE a.owner_id = {Db.lit owner.val} AND a.kind IN ('asset', 'liability')
         AND p.commodity = {Db.lit commodity.code}
         AND p.txn_id IN (SELECT txn_id FROM posting WHERE account_id = {Db.lit acc.id.val})

       GROUP BY a.id ORDER BY ABS(SUM(p.minor)) DESC LIMIT 1"
  match inBudget with
  | some name => Accounts.ensure ctx name
  | none =>
    let anywhere ← Db.row? String ctx.db
      s!"SELECT a.name FROM posting p JOIN account a ON a.id = p.account_id
         WHERE a.owner_id = {Db.lit owner.val} AND a.kind = 'asset'
         GROUP BY a.id ORDER BY COUNT(*) DESC LIMIT 1"
    match anywhere with
    | some name => Accounts.ensure ctx name
    | none =>
      match ← Parties.byId? ctx owner with
      | some p => Accounts.purse ctx p
      | none => throw <| IO.userError s!"no such person: {owner.val}"

/-- Whether a claim has been written up as an invoice that still stands. -/
def spokenFor (ctx : Ctx) (t : Transaction) : IO Bool := do
  return (← Db.scalarInt ctx.db
    s!"SELECT COUNT(*) FROM invoice
       WHERE pending_txn = {Db.lit t.id.val} AND status != 'void'") > 0

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

The plan is checked before anything is written: `Settle.validate` says whether
performing it leaves everybody at zero, and refuses otherwise. That is the same
contract `Transaction.validate` has, and it is why a settlement and the ledger
cannot drift apart.

`hub`, when given, routes everything through one person instead of taking the
shortest plan. The shortest plan will cheerfully tell two people who never dealt
with each other to pay one another; a group usually wants the other thing.

Returns only what changed, so running this twice returns nothing the second
time.
-/
def settle (ctx : Ctx) (b : Budget) (actor : String) (commodity : Commodity := Commodity.eur)
    (hub : Option PartyId := none) (due : Option Date := none) : IO (Array Transaction) := do
  let held ← balance ctx b commodity
  if held.minor != 0 then
    throw <| IO.userError
      s!"{Budget.shortName b} still holds {held.render} undivided; allocate it before settling"
  let stand ← standings ctx b commodity
  if stand.isEmpty then return #[]
  let accounts ← Accounts.list ctx
  -- What is already true, and what is merely still being asked.
  let mut fixed : Array Transaction := #[]
  let mut open' : Array Transaction := #[]
  for t in ← claims ctx b do
    if t.state != .pending || (← spokenFor ctx t) then fixed := fixed.push t
    else open' := open'.push t
  let toPlan := Settle.residual (stand.toList.map Standing.position)
    (fixed.filterMap (Pendings.transferOf accounts)).toList
  let plan :=
    match hub with
    | some h => Settle.star h.val toPlan
    | none => Settle.greedy toPlan
  let checked ← IO.ofExcept (Settle.validate toPlan plan)
  let byDate ← match due with
    | some d => pure d
    | none => Date.today
  let lbl ← Labels.ensure ctx b.label
  let nameOf (id : String) : String :=
    ((stand.find? (fun s => s.owner.val == id)).map (·.name)).getD id
  let ownerOf (a : AccountId) : Option String :=
    (accounts.find? (·.id == a)).map (·.owner.val)
  -- A claim between the same two people is the same request, so it keeps its
  -- id: an invoice raised against it later, and the audit trail behind it, go
  -- on pointing at the thing they were about.
  let mut spare := open'
  let mut out : Array Transaction := #[]
  for t in checked.val do
    if t.minor == 0 then continue
    let samePair (x : Transaction) : Bool :=
      (Pendings.payer? x).bind ownerOf == some t.from_ &&
        (Pendings.receiver? x).bind ownerOf == some t.to
    match spare.findIdx? samePair with
    | some i =>
      let existing := spare[i]!
      spare := spare.filter (fun x => x.id != existing.id)
      if (Pendings.amount existing).minor == t.minor then continue
      let revised : Transaction :=
        { existing with postings := existing.postings.map fun p =>
            { p with amount := (⟨commodity, if p.amount.minor > 0 then t.minor else -t.minor⟩
                                 : Amount) } }
      match revised.validate with
      | .error e => throw <| IO.userError s!"revising a claim would not balance: {e}"
      | .ok bt =>
        Txns.put ctx bt actor "resettle"
        out := out.push bt.val
    | none =>
      let payer ← settlementAccount ctx b ⟨t.from_⟩ commodity
      let receiver ← settlementAccount ctx b ⟨t.to⟩ commodity
      out := out.push (← Pendings.create ctx payer.id receiver.id ⟨commodity, t.minor⟩ byDate
        s!"{nameOf t.from_} → {nameOf t.to} for {Budget.shortName b}" actor [lbl.id])
  -- Whatever the new plan has no use for was a request the facts have overtaken.
  for x in spare do
    out := out.push (← Pendings.void ctx x.id actor)
  return out

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

/--
Each participant's part of an amount, to the cent.

`splitParts` guarantees the parts add back to exactly what was paid, and a
participant's weight is simply a run of consecutive parts — so unequal shares
cost nothing extra in accuracy.
-/
def shareOut (minor : Int) (among : List Participant) : List Int :=
  let weights := among.map (fun p => max p.weight 1)
  let parts := splitParts minor weights.sum
  (weights.zipIdx).map fun (w, i) => ((parts.drop (weights.take i).sum).take w).sum

/--
Each participant's account, resolved up front so a typo fails before anything is
written, and checked for ownership.

That check is the whole arrangement in one line: a share of somebody else's must
land in an account of theirs, or the division has quietly made it yours.
-/
def targetsOf (ctx : Ctx) (among : List Participant) : IO (List AccountId) := do
  -- One row per person. Two rows for the same owner would each be topped up
  -- against that owner's whole total, and both would be wrong.
  let owners := among.map (·.owner)
  if owners.eraseDups.length != owners.length then
    throw <| IO.userError "somebody appears twice; give each person one share"
  let mut out : List AccountId := []
  for p in among do
    if p.account.isEmpty then
      throw <| IO.userError s!"{p.name} has no account for their share"
    let target ← Accounts.ensure ctx p.account (owner := some p.owner)
    if target.owner != p.owner then
      throw <| IO.userError
        s!"{p.account} belongs to somebody else, so {p.name} cannot have a share there"
    out := out ++ [target.id]
  return out

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
  if b.closed then
    throw <| IO.userError s!"{Budget.shortName b} is closed; reopen it to add costs"
  if amount.minor ≤ 0 then
    throw <| IO.userError "a contribution has to be an amount that was spent"
  let acc ← account ctx b
  let t : Transaction :=
    { id := ⟨← freshId⟩, date, payee, narration
      postings :=
        [{ account := acc.id, amount },
         { account := from_.id, amount := ⟨amount.commodity, -amount.minor⟩ }]
      source := .manual actor }
  match t.validate with
  | .error e => throw <| IO.userError e
  | .ok bt =>
    Txns.put ctx bt actor "contribute"
    return bt.val

/-- Everything a budget is made of: its costs and the divisions of them. -/
def entries (ctx : Ctx) (b : Budget) : IO (Array Transaction) :=
  Txns.list ctx (.account b.name) { key := .date, descending := false } 10000

/--
The costs a budget was lent, as opposed to the entries that divided them.

A transaction counts as a cost when it has a posting in the budget account that
is not itself part of a division — a division's own legs live in the same
account and would otherwise be read back as costs. The `allocation` tag is what
tells them apart.
-/
def costs (ctx : Ctx) (b : Budget) : IO (Array Transaction) := do
  let acc ← account ctx b
  return (← entries ctx b).filter fun t =>
    t.postings.any fun p => p.account == acc.id && p.tag != some "allocation"

/--
What each cost still has undivided, so allocating twice divides only the rest.

A cost's contribution to the budget does not shrink when part of it is
allocated: the allocation posts against the budget, not against the cost. So the
allocation legs carry the id of the cost they discharge, and the remainder is
the difference.

Legs from before that was recorded carry no such id. They still discharged
*something*, so they are applied oldest cost first: the only convention left in
this file, and it applies to nothing raised since.
-/
def remaining (ctx : Ctx) (b : Budget) (commodity : Commodity := Commodity.eur) :
    IO (Array (Transaction × Int)) := do
  let acc ← account ctx b
  let cs ← costs ctx b
  let everything ← Txns.list ctx (.account b.name) { key := .date, descending := false } 10000
  let takenAgainst (id : TxId) : Int :=
    (everything.map fun t =>
      (t.postings.filterMap fun p =>
        if p.account == acc.id && p.tag == some "allocation"
            && p.origin == some id.val && p.amount.commodity.code == commodity.code
        then some p.amount.minor else none).sum).foldl (· + ·) 0
  let mut rows : Array (Transaction × Int) :=
    cs.map fun t => (t, t.netIn acc.id commodity.code + takenAgainst t.id)
  -- Whatever the per-cost figures do not account for is spread oldest first.
  let attributed := (rows.map (fun (_, n) => n)).foldl (· + ·) 0
  let held := (← balance ctx b commodity).minor
  let mut slack := attributed - held
  if slack != 0 then
    let mut out : Array (Transaction × Int) := #[]
    for (t, n) in rows do
      -- Only ever take from a cost in the direction it actually points, and
      -- never past zero: a cost cannot be more than fully divided.
      let cut :=
        if slack > 0 then (if n > 0 then min slack n else 0)
        else (if n < 0 then max slack n else 0)
      slack := slack - cut
      out := out.push (t, n - cut)
    rows := out
  return rows.filter fun (_, n) => n != 0

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
  let acc ← account ctx b
  let pending ← remaining ctx b commodity
  if pending.isEmpty then
    return none
  let targets ← targetsOf ctx among
  -- What each person is *supposed* to end up with, less what they have already
  -- been given. Dividing the remainder by the weights would be right only if
  -- every earlier division had covered everybody in proportion — which is false
  -- for a budget divided one person at a time, and false after any division is
  -- deleted. Topping up to the target is right either way, and in the ordinary
  -- case the two agree exactly.
  let mut already : List Int := []
  for p in among do
    already := already ++ [← dividedTo ctx b p.owner commodity]
  let toDivide := (pending.map (fun (_, n) => n)).foldl (· + ·) 0
  let owed := shareOut (already.sum + toDivide) among
  let topUps : List Int := (owed.zip already).map fun (target, had) => target - had
  match (topUps.zipIdx).find? (fun (n, _) => n < 0) with
  | some (over, i) =>
    let who := (among[i]!).name
    throw <| IO.userError
      s!"{who} has already been given {(Amount.mk commodity (-over)).render} more than \
this division leaves them; withdraw a division before dividing again"
  | none => pure ()
  -- Every cost, split into the kinds of leg it is made of, so a card fee is
  -- borne in the same proportion as the purchase beside it and stays
  -- recognisable as a fee inside everybody's share.
  let mut pieces : List (String × Option String × Int) := []
  let mut seen : List String := []
  for (t, held) in pending do
    -- Two costs from the same shop on the same day would otherwise read as one
    -- line repeated, which is exactly the kind of thing a payer queries.
    let base := describe t
    let clash := seen.countP fun d => d == base
    seen := seen ++ [base]
    let label := if clash == 0 then base else s!"{base} ({clash + 1})"
    let mut kinds : List (Option String × Int) := []
    for p in t.postings do
      if p.account == acc.id && p.amount.commodity.code == commodity.code then
        kinds := match kinds.find? (fun (g, _) => g == p.tag) with
          | some _ => kinds.map fun (g, n) =>
              if g == p.tag then (g, n + p.amount.minor) else (g, n)
          | none => kinds ++ [(p.tag, p.amount.minor)]
    -- Where the legs do not add up to what is left of the cost — one the old
    -- pot machinery divided in part, with nothing recording against what —
    -- there is nothing to line up with, so it goes in as one piece.
    let split := if (kinds.map (·.2)).sum == held then kinds else [((none : Option String), held)]
    for (kind, piece) in split do
      let line := match kind with
        | some k => s!"{label} ({k})"
        | none => label
      pieces := pieces ++ [(line, kind, piece)]
  -- Each person gets their top-up exactly, and each piece is fully divided.
  -- Rounding either one on its own would drift on the other.
  let grid := biproportional topUps (pieces.map (fun (_, _, n) => n))
  let mut postings : List Posting := []
  let mut totals : List Int := among.map (fun _ => 0)
  for ((row, target), i) in (grid.zip targets).zipIdx do
    for (share, (line, kind, _)) in row.zip pieces do
      if share != 0 then
        postings := postings ++
          [{ account := target, amount := ⟨commodity, share⟩
             note := some line, tag := kind }]
        totals := totals.set i (totals[i]! + share)
  -- One budget leg per cost, carrying that cost's id, so a later division can
  -- tell what is left of it.
  for (t, held) in pending do
    if held != 0 then
      postings := postings ++
        [{ account := acc.id, amount := ⟨commodity, -held⟩
           note := some (describe t), tag := some "allocation", origin := some t.id.val }]
  let discharged := (totals.foldl (· + ·) 0)
  if discharged == 0 then return none
  let today ← match date with
    | some d => pure d
    | none => Date.today
  let t : Transaction :=
    { id := ⟨← freshId⟩, date := today, payee := none
      narration := s!"allocation of {Budget.shortName b}"
      postings, source := .manual actor }
  match t.validate with
  | .error e => throw <| IO.userError s!"allocation would not balance: {e}"
  | .ok bt =>
    Txns.put ctx bt actor "allocate"
    -- Deciding and paying are two facts, so they are two entries. The claims
    -- are raised here rather than by a second verb because the moment the
    -- division is known is the moment the arithmetic behind them is cheapest to
    -- get right, and because a division nobody has been asked to settle is a
    -- worklist entry that looks finished.
    let raised ← settle ctx b actor commodity hub (some today)
    return some (bt.val, raised)

/--
The lines an invoice for one person's share is made of: what landed on them.

Nothing is divided here. The division already decided who bears what, cost by
cost, and this reads those legs back — which is what makes an invoice and the
ledger incapable of disagreeing, because there is only ever one division and
both are looking at it.

A share is a positive movement onto an account of theirs. That holds whether it
was posted by an allocation entry or is a leg of the cost itself, which is why
this does not go looking for a tag that only one of those two has.
-/
def allocationLines (ctx : Ctx) (b : Budget) (owner : PartyId) :
    IO (Array (String × Amount)) := do
  let acc ← account ctx b
  let theirs := ((← Accounts.list ctx).filter (·.owner == owner)).map (·.id)
  let mut out : Array (String × Amount) := #[]
  for t in ← entries ctx b do
    for p in t.postings do
      if theirs.contains p.account && p.account != acc.id && p.amount.minor > 0 then
        out := out.push (p.note.getD (describe t), p.amount)
  return out

/--
What one person put into a budget, cost by cost.

The mirror of `allocationLines`, and needed for the same reason: a document
asking somebody for money has to say what they already paid for, or it asks for
their whole share as though they had contributed nothing. Amounts come back
negative, because that is the direction they run on the invoice.
-/
def fundedLines (ctx : Ctx) (b : Budget) (owner : PartyId) : IO (Array (String × Amount)) := do
  let theirs := ((← Accounts.list ctx).filter fun a => a.owner == owner && a.holdsMoney).map (·.id)
  let mut out : Array (String × Amount) := #[]
  for t in ← costs ctx b do
    for c in (t.commodityCodes.eraseDups) do
      -- Only the negative side. A cost somebody paid for out of their own purse,
      -- and booked already divided, has their share on that same purse — and
      -- their share is not something they put in.
      let funded := (t.postings.filterMap fun p =>
        if theirs.contains p.account && p.amount.commodity.code == c && p.amount.minor < 0
        then some p.amount.minor else none).sum
      if funded < 0 then
        out := out.push (describe t, ⟨Commodity.ofCode c, funded⟩)
  return out

/-- Marks a budget closed, or reopens it. -/
def setClosed (ctx : Ctx) (b : Budget) (closed : Bool) : IO Unit := do
  let now ← nowStamp
  Db.exec ctx.db s!"UPDATE budget SET closed_at = {if closed then Db.lit now else "NULL"}
                    WHERE id = {Db.lit b.id.val}"

/--
Closes a budget: divides everything still waiting, and asks for what that leaves
people owing.

Closing is the moment of decision, and it is deliberate. Until it happens costs
simply accumulate in the account, which is what the account is for; afterwards
nobody can add to it, including whoever holds a share link.

Reopening it and closing again writes a *new* division covering only what came
in since. The first one is not touched: it recorded a decision about a set of
costs on a particular day, and somebody was told what they owed on the strength
of it. `remaining` is what keeps the second from dividing the first again.

`closed_at` is set last on purpose. A crash between dividing and closing leaves
the budget open, and closing again then divides only whatever is still waiting —
which is right, where a half-applied close that had already flipped the flag
would be a budget nobody could finish dividing.
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
  let divided ← allocate ctx b people actor commodity date hub
  -- Dividing settles as it goes; with nothing left to divide there is still the
  -- chance that a claim was written off or an invoice voided since.
  let raised ← match divided with
    | some (_, cs) => pure cs
    | none => resettle ctx b actor commodity
  setClosed ctx b true
  return (divided.map (·.1), raised)

/--
Reopens a closed budget so more costs can go in.

Nothing that was decided is undone: every division stands, and so does every
claim raised from one. What changes is only that the budget can be added to
again — and until it is closed once more, what everybody was last told remains
what they were last told.
-/
def reopen (ctx : Ctx) (b : Budget) (_actor : String) : IO Unit := do
  if !b.closed then
    throw <| IO.userError s!"{Budget.shortName b} is already open"
  setClosed ctx b false

/-- Deletes a budget's bookkeeping. The transactions it touched are left alone. -/
def delete (ctx : Ctx) (b : Budget) : IO Unit :=
  Db.exec ctx.db s!"DELETE FROM budget WHERE id = {Db.lit b.id.val}"

end Budgets

end Resources
