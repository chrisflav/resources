import Resources.Core.Claim
import Resources.Core.State

/-!
# Reading a budget

A payment several people will bear leaves an account before anybody knows whose
it was. That gap — between paying and knowing — is what a budget names, and
everything in this file is a question about the gap: what is still undivided,
what has already been handed to whom, where each person stands, and what would
square them up.

The store asked these questions in SQL. They are arithmetic over the ledger, so
they are here instead, as functions of a `State`: one implementation that the
store projects and the pure operations in `Core/Apply.lean` compute from, rather
than a query and a re-derivation that can drift apart.

Two things the SQL said implicitly and this file has to say out loud.

*Only what happened counts.* Every balance in the store went through the
`posting` view, which shows posted rows alone, so a claim — a transaction that
has not happened — never reached a figure. Here that is `State.ledger`, and
every query below is taken over it.

*Order is chosen, not inherited.* A hash map has no order and `ORDER BY name`
had one, so the tie-breaks are written down: entries run oldest first and then
by id, claims newest first and then by id, standings by the person's name and
then by their id.
-/

namespace Resources
namespace Budget

/-! ## Naming -/

/-- How one cost is described on an allocation leg and on an invoice line. -/
def describe (t : Transaction) : String :=
  let what := (t.payee.getD "").trimAscii.toString
  if what.isEmpty then s!"{t.date.toIso} — {Str.clamp t.narration 60}"
  else s!"{t.date.toIso} — {Str.clamp what 60}"

/-- The account name a budget lives in. A bare name is placed under `Budget`. -/
def accountName (name : String) : String :=
  if name.startsWith "Budget." then name else "Budget." ++ name

/-- The account name a person's own money lives in. -/
def purseName (person : String) : String :=
  if person.startsWith "Assets." then person else "Assets.Purse." ++ person

/--
The budget's own equity account, when the state still has it.

By id, out of the budget's own record. It used to be by name, and the first
account in id order won: anybody who could write an account could create one
called `Budget.Hut` with a lower id and become the pot for every reader —
the balance read zero, settling found nothing to do, and every member of the
realm acquired post rights on the impostor.
-/
def account? (b : Budget) (s : State) : Option Account :=
  match s.budget? b.id with
  | some bs => s.account? bs.account
  | none => none

/-! ## Order -/

/-- Oldest first, ties broken by id: the order the entries of a budget are read in. -/
private def olderFirst (a b : Transaction) : Bool :=
  match compare a.date b.date with
  | .lt => true
  | .gt => false
  | .eq => a.id.val ≤ b.id.val

/-- Newest first, ties broken by id: the order claims are read in. -/
private def newerFirst (a b : Transaction) : Bool :=
  match compare a.date b.date with
  | .gt => true
  | .lt => false
  | .eq => b.id.val ≤ a.id.val

/-- The first element with the largest score, in the order given. -/
private def pickMax {α : Type} (xs : List α) (score : α → Nat) : Option α :=
  xs.foldl (fun best x =>
    match best with
    | some b => if score x > score b then some x else some b
    | none => some x) none

/-! ## What a budget is made of -/

/-- Everything a budget is made of: its costs and the divisions of them. -/
def entries (b : Budget) (s : State) : List Transaction :=
  (s.ledger.filter fun t => t.postings.any fun p =>
    match s.account? p.account with
    | some a => Account.isUnder a.name b.name
    | none => false).mergeSort olderFirst

/--
The posted transactions with a leg in the budget's own account.

Narrower than `entries`, which takes the subtree: a figure about this pot is
about this pot, and a sub-budget is a different one.
-/
private def touching (s : State) (acc : AccountId) : List Transaction :=
  s.ledger.filter fun t => t.postings.any fun p => p.account == acc

/-- What the budget still holds, and so what is still undecided. -/
def balance (b : Budget) (s : State) (c : Commodity := Commodity.eur) : Amount :=
  match b.account? s with
  | none => ⟨c, 0⟩
  | some acc => ⟨c, s.balance acc.id c.code⟩

/--
Everything already handed to somebody, yourself included.

Read as "what landed on somebody" rather than "what carries the allocation tag",
because a cost booked already divided has no allocation entry to tag: its shares
are legs of the cost itself. A share is a positive movement onto an account that
is not the budget's; a funding leg is negative, and the budget's own leg is
excluded, so the two cannot be confused.
-/
def allocated (b : Budget) (s : State) (c : Commodity := Commodity.eur) : Amount :=
  match b.account? s with
  | none => ⟨c, 0⟩
  | some acc =>
    ⟨c, ((touching s acc.id).map fun t =>
      (t.postings.filterMap fun p =>
        if p.account != acc.id && p.amount.minor > 0 && p.amount.commodity.code == c.code
        then some p.amount.minor else none).sum).sum⟩

/--
What this budget has already given one person, whatever account it landed in.

Read per owner rather than per account, because a share booked to somebody's
expense category once and their purse the next time is still the same person's
share — and because that is the figure a further division has to top up rather
than start from.
-/
def dividedTo (b : Budget) (s : State) (owner : PartyId)
    (c : Commodity := Commodity.eur) : Int :=
  match b.account? s with
  | none => 0
  | some acc =>
    ((touching s acc.id).map fun t =>
      (t.postings.filterMap fun p =>
        if p.account != acc.id && p.amount.minor > 0 && p.amount.commodity.code == c.code
            && (s.account? p.account).map (·.owner) == some owner
        then some p.amount.minor else none).sum).sum

/--
The costs a budget was lent, as opposed to the entries that divided them.

A transaction counts as a cost when it has a posting in the budget account that
is not itself part of a division — a division's own legs live in the same
account and would otherwise be read back as costs. The `allocation` tag is what
tells them apart.
-/
def costs (b : Budget) (s : State) : List Transaction :=
  match b.account? s with
  | none => []
  | some acc =>
    (entries b s).filter fun t =>
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
def remaining (b : Budget) (s : State) (c : Commodity := Commodity.eur) :
    List (Transaction × Int) :=
  match b.account? s with
  | none => []
  | some acc => Id.run do
    let everything := entries b s
    let takenAgainst (id : TxId) : Int :=
      (everything.map fun t =>
        (t.postings.filterMap fun p =>
          if p.account == acc.id && p.tag == some "allocation"
              && p.origin == some id.val && p.amount.commodity.code == c.code
          then some p.amount.minor else none).sum).sum
    let mut rows : List (Transaction × Int) :=
      (costs b s).map fun t => (t, t.netIn acc.id c.code + takenAgainst t.id)
    -- Whatever the per-cost figures do not account for is spread oldest first.
    let attributed := (rows.map (fun (_, n) => n)).sum
    let mut slack := attributed - (balance b s c).minor
    if slack != 0 then
      let mut out : List (Transaction × Int) := []
      for (t, n) in rows do
        -- Only ever take from a cost in the direction it actually points, and
        -- never past zero: a cost cannot be more than fully divided.
        let cut :=
          if slack > 0 then (if n > 0 then min slack n else 0)
          else (if n < 0 then max slack n else 0)
        slack := slack - cut
        out := out ++ [(t, n - cut)]
      rows := out
    return rows.filter fun (_, n) => n != 0

/--
The lines an invoice for one person's share is made of: what landed on them.

Nothing is divided here. The division already decided who bears what, cost by
cost, and this reads those legs back — which is what makes an invoice and the
ledger incapable of disagreeing, because there is only ever one division and
both are looking at it.

A share is a positive movement onto an account of theirs. That holds whether it
was posted by a division entry or is a leg of the cost itself, which is why this
does not go looking for a tag that only one of those two has.
-/
def allocationLines (b : Budget) (s : State) (owner : PartyId) : List (String × Amount) :=
  match b.account? s with
  | none => []
  | some acc =>
    let theirs := (s.accountsSorted.filter fun a => a.owner == owner).map (·.id)
    (entries b s).flatMap fun t =>
      t.postings.filterMap fun p =>
        if theirs.contains p.account && p.account != acc.id && p.amount.minor > 0
        then some (p.note.getD (describe t), p.amount) else none

/--
What one person put into a budget, cost by cost.

The mirror of `allocationLines`, and needed for the same reason: a document
asking somebody for money has to say what they already paid for, or it asks for
their whole share as though they had contributed nothing. Amounts come back
negative, because that is the direction they run on the invoice.
-/
def fundedLines (b : Budget) (s : State) (owner : PartyId) : List (String × Amount) :=
  let theirs := (s.accountsSorted.filter fun a => a.owner == owner && a.holdsMoney).map (·.id)
  (costs b s).flatMap fun t =>
    t.commodityCodes.eraseDups.filterMap fun code =>
      -- Only the negative side. A cost somebody paid for out of their own purse,
      -- and booked already divided, has their share on that same purse — and
      -- their share is not something they put in.
      let funded := (t.postings.filterMap fun p =>
        if theirs.contains p.account && p.amount.commodity.code == code && p.amount.minor < 0
        then some p.amount.minor else none).sum
      if funded < 0 then some (describe t, (⟨Commodity.ofCode code, funded⟩ : Amount)) else none

/-! ## Standing and settlement -/

/--
Where each person stands: everything the budget's transactions moved across
their accounts, the budget's own account excluded.

That exclusion is what makes the figure mean something. Include the budget and
you are asking "how much money went through this pot", which is a fact about the
pot; exclude it and you are asking "how much of it was this person's, less what
they put in", which is a fact about the person. The second is the settlement.

The positions sum to minus what the budget still holds, so they sum to zero
exactly when everything has been divided — which is why settling refuses to plan
against a budget with money still in it. There would be a residue belonging to
nobody, and no set of transfers can settle that.
-/
def standings (b : Budget) (s : State) (c : Commodity := Commodity.eur) : List Standing :=
  match b.account? s with
  | none => []
  | some acc => Id.run do
    let mut rows : List (PartyId × Int) := []
    for t in touching s acc.id do
      for p in t.postings do
        if p.account != acc.id && p.amount.commodity.code == c.code then
          if let some a := s.account? p.account then
            rows := match rows.find? (fun x => x.1 == a.owner) with
              | some _ =>
                rows.map fun x => if x.1 == a.owner then (x.1, x.2 + p.amount.minor) else x
              | none => rows ++ [(a.owner, p.amount.minor)]
    let named : List Standing := rows.filterMap fun (owner, minor) =>
      if minor == 0 then none
      else some { owner, name := ((s.party? owner).map (·.name)).getD owner.val
                  amount := ⟨c, minor⟩ }
    return named.mergeSort fun x y =>
      if x.name == y.name then x.owner.val ≤ y.owner.val else x.name ≤ y.name

/-- The claims carrying one label: outstanding and already met, but not voided. -/
def claimsLabelled (s : State) (label : LabelId) : List Transaction :=
  (s.txnsSorted.filter fun t =>
    t.labels.contains label && (t.state == .pending || t.state == .settled)).mergeSort newerFirst

/--
The claims raised for this budget.

By the label id pinned on the budget, not by a label of the budget's name: a
label is another entry anybody could write, and the first one of that name in
id order used to decide which claims a budget could see.

Netting depends on the distinction this leaves in. A claim that was met is money
somebody has already moved, so asking again would ask twice; a claim that was
voided is money that will never move, so the position it was raised against
still stands.
-/
def claims (b : Budget) (s : State) : List Transaction :=
  match s.budget? b.id with
  | some bs => if bs.label.val.isEmpty then [] else claimsLabelled s bs.label
  | none => []

/-- Whether a claim has been written up as an invoice that still stands. -/
def spokenFor (s : State) (t : Transaction) : Bool :=
  (sortedValues s.invoices).any fun i =>
    i.invoice.pendingTxn == some t.id && i.invoice.status != .void

/--
The account a person settles through: the one of theirs this budget already
moved the most money across.

Whoever fronted a cost gets paid back into the account they fronted it from,
which is both what a person expects and the only choice that needs no
configuring. Somebody who only owes has no such leg, so it falls back to the
account of theirs this ledger sees most, and then to their purse.

All three readings are taken inside the budget's own realm. Without that filter
the candidates were every account of theirs anywhere, and a settlement is written
by `checkPostings`, which refuses a leg outside the part's realm — so somebody
who held an asset account of their own in any other realm this reader could see
made every settlement of this budget fail with "is not in this realm", and
getting it back needed an admin to close or rename an account in a realm that had
nothing to do with the budget.
-/
def settlementAccount (b : Budget) (s : State) (owner : PartyId)
    (c : Commodity := Commodity.eur) : Except String AccountId := do
  let some bs := s.budget? b.id | throw s!"no such budget: {b.id.val}"
  let theirs := s.accountsSorted.filter fun a => a.owner == owner && a.realm == bs.realm
  let inBudget : List (AccountId × Int) :=
    match b.account? s with
    | none => []
    | some acc =>
      (theirs.filter (·.holdsMoney)).filterMap fun a =>
        let moved := (touching s acc.id).flatMap fun t =>
          t.postings.filter fun p => p.account == a.id && p.amount.commodity.code == c.code
        if moved.isEmpty then none else some (a.id, (moved.map (·.amount.minor)).sum)
  match pickMax inBudget (fun x => x.2.natAbs) with
  | some (id, _) => return id
  | none =>
    let anywhere : List (AccountId × Nat) :=
      (theirs.filter (fun a => a.kind == .asset)).filterMap fun a =>
        let n := (s.ledger.map fun t => (t.postings.filter (·.account == a.id)).length).sum
        if n == 0 then none else some (a.id, n)
    match pickMax anywhere (fun x => x.2) with
    | some (id, _) => return id
    | none =>
      let some party := s.party? owner | throw s!"no such person: {owner.val}"
      -- Their purse: the bridge they hold in this realm, or the account named
      -- for them. Without one there is nowhere for a settlement to land.
      match (theirs.find? (·.bridgeOf.isSome)) <|>
            (theirs.find? (fun a => a.name == purseName party.name)) with
      | some a => return a.id
      | none => throw s!"{party.name} has no account to settle through"

/-! ## Dividing -/

/--
Each participant's part of an amount, to the cent.

`splitParts` guarantees the parts add back to exactly what was paid, and a
participant's weight is simply a run of consecutive parts — so unequal shares
cost nothing extra in accuracy.
-/
def shareOut (minor : Int) (among : List Participant) : List Int :=
  let weights := among.map fun p => max p.weight 1
  let parts := splitParts minor weights.sum
  (weights.zipIdx).map fun (w, i) => ((parts.drop (weights.take i).sum).take w).sum

/--
Each participant's account, resolved up front so a typo fails before anything is
written, and checked for ownership.

That check is the whole arrangement in one line: a share of somebody else's must
land in an account of theirs, or the division has quietly made it yours.

Nothing is created here. A participant account that does not exist yet is the
caller's to make — the store ensures the accounts before it composes the
operation — because `Core` has no way to mint an id.
-/
def targetsOf (s : State) (realm : RealmId) (among : List Participant) :
    Except String (List AccountId) := do
  -- One row per person. Two rows for the same owner would each be topped up
  -- against that owner's whole total, and both would be wrong.
  let owners := among.map (·.owner)
  if owners.eraseDups.length != owners.length then
    throw "somebody appears twice; give each person one share"
  let mut out : List AccountId := []
  for p in among do
    if p.account.isEmpty then
      throw s!"{p.name} has no account for their share"
    -- In this realm. The lookup used to be the first account of that name in id
    -- order across every realm, and an account of any name can be minted by
    -- anybody about themselves — so a share could be pointed at a stranger's
    -- account, and while the ownership check below stopped the money going
    -- there, it stopped the division for ever instead.
    let some target := s.accountByNameIn? realm p.account
      | throw s!"no such account in this realm: {p.account}"
    -- Theirs, or the purse they hold here. A bridge belongs to the member it is
    -- for, and a member's spending lands on their party, so a share may go to
    -- either reading of "an account of theirs" and to nothing else.
    let bridgeParty := target.bridgeOf.bind (fun m => (s.member? m).map (·.party))
    if target.owner != p.owner && bridgeParty != some p.owner then
      throw s!"{p.account} belongs to somebody else, so {p.name} cannot have a share there"
    out := out ++ [target.id]
  return out

/--
The transaction that divides what the budget holds among the participants, or
nothing when there is nothing left to divide.

Each cost is divided separately so the entry says which part of which purchase
each person bears, and an invoice can be rendered from the legs without dividing
anything a second time. `splitParts` guarantees the parts of each cost add back
to it exactly, so the participants' totals add back to the budget exactly too.

Dividing twice is allowed and normal: a receipt turns up after the weekend, it
is lent into the same budget, and a second division covers just what is left.
Every leg is tagged `allocation`, because none of this is money moving — it is
money already spent being told whose it was.
-/
def divisionOf (b : Budget) (s : State) (realm : RealmId) (among : List Participant)
    (c : Commodity) (date : Date) (id : TxId) (actor : String) :
    Except String (Option Transaction) := do
  if among.isEmpty then throw "say who to divide this among"
  let some acc := b.account? s | throw s!"{b.shortName} has no account of its own"
  let pending := remaining b s c
  if pending.isEmpty then return none
  let targets ← targetsOf s realm among
  -- What each person is *supposed* to end up with, less what they have already
  -- been given. Dividing the remainder by the weights would be right only if
  -- every earlier division had covered everybody in proportion — which is false
  -- for a budget divided one person at a time, and false after any division is
  -- deleted. Topping up to the target is right either way, and in the ordinary
  -- case the two agree exactly.
  let already := among.map fun p => dividedTo b s p.owner c
  let toDivide := (pending.map (fun (_, n) => n)).sum
  let owed := shareOut (already.sum + toDivide) among
  let topUps : List Int := (owed.zip already).map fun (target, had) => target - had
  match (topUps.zipIdx).find? (fun (n, _) => n < 0) with
  | some (over, i) =>
    throw s!"{(among[i]!).name} has already been given \
             {(Amount.mk c (-over)).render} more than this division leaves them; \
             withdraw a division before dividing again"
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
    let line := if clash == 0 then base else s!"{base} ({clash + 1})"
    let mut kinds : List (Option String × Int) := []
    for p in t.postings do
      if p.account == acc.id && p.amount.commodity.code == c.code then
        kinds := match kinds.find? (fun (g, _) => g == p.tag) with
          | some _ => kinds.map fun (g, n) => if g == p.tag then (g, n + p.amount.minor) else (g, n)
          | none => kinds ++ [(p.tag, p.amount.minor)]
    -- Where the legs do not add up to what is left of the cost — one divided in
    -- part, with nothing recording against what — there is nothing to line up
    -- with, so it goes in as one piece.
    let split := if (kinds.map (·.2)).sum == held then kinds else [((none : Option String), held)]
    for (kind, piece) in split do
      let named := match kind with
        | some k => s!"{line} ({k})"
        | none => line
      pieces := pieces ++ [(named, kind, piece)]
  -- Each person gets their top-up exactly, and each piece is fully divided.
  -- Rounding either one on its own would drift on the other.
  let grid := biproportional topUps (pieces.map fun (_, _, n) => n)
  let mut postings : List Posting := []
  let mut totals : List Int := among.map fun _ => 0
  for ((row, target), i) in (grid.zip targets).zipIdx do
    for (share, (named, kind, _)) in row.zip pieces do
      if share != 0 then
        postings := postings ++
          [{ account := target, amount := ⟨c, share⟩, note := some named, tag := kind }]
        totals := totals.set i (totals[i]! + share)
  -- One budget leg per cost, carrying that cost's id, so a later division can
  -- tell what is left of it.
  for (t, held) in pending do
    if held != 0 then
      postings := postings ++
        [{ account := acc.id, amount := ⟨c, -held⟩, note := some (describe t)
           tag := some "allocation", origin := some t.id.val }]
  if totals.sum == 0 then return none
  let divided : Transaction :=
    { id, date, payee := none, narration := s!"allocation of {b.shortName}"
      postings, source := .manual actor }
  match divided.validate with
  | .error e => throw s!"allocation would not balance: {e}"
  | .ok bt => return some bt.val

/--
The claims that would square the budget: the ones to raise, the ones to revise,
and the ones the facts have overtaken.

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

Returns only what changed, so running it twice returns nothing the second time.
-/
def settlementOf (b : Budget) (s : State) (c : Commodity) (hub : Option PartyId) (due : Date)
    (claimIds : List TxId) (label : LabelId) (actor : String) :
    Except String (List Transaction) := do
  let held := balance b s c
  if held.minor != 0 then
    throw s!"{b.shortName} still holds {held.render} undivided; allocate it before settling"
  let stand := standings b s c
  if stand.isEmpty then return []
  let accounts := s.accountsSorted.toArray
  -- What is already true, and what is merely still being asked.
  let mut fixed : List Transaction := []
  let mut asking : List Transaction := []
  for t in claimsLabelled s label do
    if t.state != .pending || spokenFor s t then fixed := fixed ++ [t]
    else asking := asking ++ [t]
  let toPlan := Settle.residual (stand.map Standing.position)
    (fixed.filterMap (Pendings.transferOf accounts))
  let plan := match hub with
    | some h => Settle.star h.val toPlan
    | none => Settle.greedy toPlan
  let checked ← Settle.validate toPlan plan
  let nameOf (id : String) : String :=
    ((stand.find? fun x => x.owner.val == id).map (·.name)).getD id
  let ownerOf (a : AccountId) : Option String := (s.account? a).map (·.owner.val)
  -- A claim between the same two people is the same request, so it keeps its
  -- id: an invoice raised against it later, and the audit trail behind it, go
  -- on pointing at the thing they were about.
  let mut spare := asking
  let mut ids := claimIds
  let mut out : List Transaction := []
  for t in checked.val do
    if t.minor == 0 then continue
    let samePair (x : Transaction) : Bool :=
      (Pendings.payer? x).bind ownerOf == some t.from_ &&
        (Pendings.receiver? x).bind ownerOf == some t.to
    match spare.findIdx? samePair with
    | some i =>
      let existing := spare[i]!
      spare := spare.filter fun x => x.id != existing.id
      if (Pendings.amount existing).minor == t.minor then continue
      let revised : Transaction :=
        { existing with postings := existing.postings.map fun p =>
            { p with amount := (⟨c, if p.amount.minor > 0 then t.minor else -t.minor⟩ : Amount) } }
      match revised.validate with
      | .error e => throw s!"revising a claim would not balance: {e}"
      | .ok bt => out := out ++ [bt.val]
    | none =>
      let payer ← settlementAccount b s ⟨t.from_⟩ c
      let receiver ← settlementAccount b s ⟨t.to⟩ c
      if payer == receiver then
        throw "a claim between one account and itself asks for nothing"
      let some id := ids.head?
        | throw s!"squaring up {b.shortName} needs more claim ids than the \
                   {claimIds.length} given"
      ids := ids.drop 1
      let claim : Transaction :=
        { id, date := due, narration := s!"{nameOf t.from_} → {nameOf t.to} for {b.shortName}"
          state := .pending
          postings :=
            [{ account := receiver, amount := ⟨c, t.minor⟩, tag := some Pendings.tag },
             { account := payer, amount := ⟨c, -t.minor⟩, tag := some Pendings.tag }]
          labels := [label], source := .manual actor }
      match claim.validate with
      | .error e => throw s!"the claim would not balance: {e}"
      | .ok bt => out := out ++ [bt.val]
  -- Whatever the new plan has no use for was a request the facts have overtaken.
  for x in spare do
    out := out ++ [{ x with state := .void }]
  return out

/-! ## Invoicing what was divided -/

/--
The lines of the invoice for one person: what they bear, less what they put in.

Both halves are read off the ledger's own legs rather than recomputed, so the
document and the entries cannot disagree. Leaving the second half out would ask
somebody who paid for the taxi to pay for their share of it a second time.
-/
def linesFor (b : Budget) (s : State) (owner : PartyId) : List InvoiceLine :=
  let line (prefix' : String) : (String × Amount) → InvoiceLine
    | (description, amount) =>
      { description := prefix' ++ description, qtyMilli := 1000, unitPrice := amount }
  (allocationLines b s owner).map (line "") ++ (fundedLines b s owner).map (line "you paid: ")

/--
The invoices a budget still has to raise: one per claim addressed to you, with
the transactions each of them bills for.

Nothing is computed here. The division decided whose the spending was and the
settlement decided who owes whom; this writes one of those claims up as a
document, with the lines read straight off that person's own legs.

Only claims that end in an account of yours get an invoice, because an invoice
is a request *you* are making. A settlement plan may well ask two other people
to square up between themselves, and that is not yours to bill. There is no
invoice for your own share either: you paid it at the hut in August, and the
division recorded it as your expense.

The numbers are not allocated here — `Op.issueInvoice` does that, from the
counters, so that a document's number is decided at the moment it is written
down and the sequence stays gapless.
-/
def invoicesFor (b : Budget) (s : State) (payment : PaymentRequest) (issued due : Date)
    (c : Commodity := Commodity.eur) (note : Option String := none)
    (only : Option (List String) := none) (ids : List InvoiceId := []) :
    Except String (List (Invoice × List TxId)) := do
  let done := (sortedValues s.invoices).filterMap fun i =>
    if i.invoice.budgetId == some b.id && i.invoice.status != .void then
      i.invoice.pendingTxn.map (·.val)
    else none
  let sources := (costs b s).map (·.id)
  let mut left := ids
  let mut out : List (Invoice × List TxId) := []
  for claim in claims b s do
    if claim.state != .pending then continue
    if done.contains claim.id.val then continue
    if let some keep := only then
      if !keep.contains claim.id.val then continue
    let some recvId := Pendings.receiver? claim | continue
    let some payId := Pendings.payer? claim | continue
    let some recv := s.account? recvId | continue
    let some payer := s.account? payId | continue
    -- Somebody else's claim on somebody else. Theirs to chase, not yours.
    if !recv.mine then continue
    let lines := linesFor b s payer.owner
    if lines.isEmpty then continue
    -- An invoice asks for exactly what its claim asks for. The two can differ
    -- when a settlement routed part of somebody's position to a third person,
    -- or when an earlier invoice already asked for some of it, and saying so is
    -- better than quietly billing a figure the QR code will not match.
    let asked := (Pendings.amount claim).minor
    let stated := (lines.map fun l => l.gross.minor).sum
    let lines := if stated == asked then lines
      else lines ++ [{ description := "already asked for, or settled directly with the others"
                       qtyMilli := 1000, unitPrice := ⟨c, asked - stated⟩ }]
    let some id := left.head?
      | throw s!"invoicing {b.shortName} needs more invoice ids than the {ids.length} given"
    left := left.drop 1
    out := out ++
      [({ id, number := "", issued, due, payerId := some payer.owner
          payerName := ((s.party? payer.owner).map (·.name)).getD payer.name
          commodity := c, reference := "", status := .draft, note, settledTxn := none
          payment, sourceAccount := some b.name, budgetId := some b.id
          pendingTxn := some claim.id, lines }, sources)]
  return out

end Budget
end Resources
