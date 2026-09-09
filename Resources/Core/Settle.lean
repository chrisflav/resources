import Resources.Core.Money

/-!
# Settling up

Once a shared budget has been divided, every participant stands at some net
position: what they were allocated, less what they put in. Positive means they
owe the group, negative means the group owes them, and — because every cost was
funded by somebody and every share was given to somebody — the positions sum to
what the budget still holds undivided. When the budget is empty they sum to
zero, and only then is there a settlement to plan at all.

A *plan* is a list of transfers. Its one obligation is that performing it leaves
everybody at zero, which is decidable and is checked before a single claim is
written: `validate` is the same shape as `Transaction.validate`, and for the
same reason. Nothing here decides who *should* pay whom — that is a social
question with several defensible answers, and `greedy` and `star` are two of
them.

Everything in this file is over plain integers in one commodity. Netting across
commodities is not arithmetic, it is a guess about an exchange rate, so a
settlement is planned per commodity and never mixes them.
-/

namespace Resources
namespace Settle

/-- One party's net position. Positive means they owe the group. -/
structure Position where
  /-- Who this is: an owner's party id. -/
  who : String
  minor : Int
  deriving Repr, Inhabited, DecidableEq

/-- One payment in a plan: `minor` moves from `from_` to `to`. -/
structure Transfer where
  from_ : String
  to : String
  minor : Int
  deriving Repr, Inhabited, DecidableEq

/-- The total of a list of positions. Zero exactly when there is nothing left over. -/
def total (ps : List Position) : Int := (ps.map (·.minor)).sum

/--
One transfer's effect on a position: the payer owes that much less, the receiver
is owed that much less.
-/
def applyOne (t : Transfer) (p : Position) : Position :=
  if p.who == t.from_ then { p with minor := p.minor - t.minor }
  else if p.who == t.to then { p with minor := p.minor + t.minor }
  else p

/-- What the positions become once every transfer has been performed. -/
def residual (ps : List Position) : List Transfer → List Position
  | [] => ps
  | t :: ts => residual (ps.map (applyOne t)) ts

/-- A plan settles these positions when it leaves every one of them at zero. -/
def Settles (ps : List Position) (ts : List Transfer) : Prop :=
  ∀ p ∈ residual ps ts, p.minor = 0

instance (ps : List Position) (ts : List Transfer) : Decidable (Settles ps ts) :=
  inferInstanceAs (Decidable (∀ p ∈ residual ps ts, p.minor = 0))

/-- Applying no transfers changes nothing. -/
@[simp] theorem residual_nil (ps : List Position) : residual ps [] = ps := rfl

/--
Nobody drops out of a plan.

A transfer only ever changes the figure attached to a participant, so the same
people come out as went in — which is why `Settles` can be checked by looking at
the residual alone, with no separate "and everybody is still accounted for".
-/
theorem residual_length : ∀ (ts : List Transfer) (ps : List Position),
    (residual ps ts).length = ps.length
  | [], _ => rfl
  | t :: ts, ps => by
    show (residual (ps.map (applyOne t)) ts).length = ps.length
    simpa using residual_length ts (ps.map (applyOne t))

/--
The largest debtor and the largest creditor, and the most that can pass between
them without overshooting either.

Matching the extremes is what makes the plan short: whichever side is smaller is
zeroed outright, so each transfer retires at least one participant.
-/
def step (ps : List Position) : Option Transfer :=
  let debtor := ps.foldl (fun best p =>
    match best with
    | some b => if p.minor > b.minor then some p else some b
    | none => if p.minor > 0 then some p else none) none
  let creditor := ps.foldl (fun best p =>
    match best with
    | some b => if p.minor < b.minor then some p else some b
    | none => if p.minor < 0 then some p else none) none
  match debtor, creditor with
  | some d, some c =>
    if d.minor > 0 && c.minor < 0 then
      some { from_ := d.who, to := c.who, minor := min d.minor (-c.minor) }
    else none
  | _, _ => none

/-- `greedy`, with an explicit bound on how many transfers may be produced. -/
def greedyFuel : Nat → List Position → List Transfer
  | 0, _ => []
  | n + 1, ps =>
    match step ps with
    | none => []
    | some t => t :: greedyFuel n (ps.map (applyOne t))

/-- The fuel is a hard ceiling on the plan's length. -/
theorem greedyFuel_length_le : ∀ (n : Nat) (ps : List Position),
    (greedyFuel n ps).length ≤ n
  | 0, _ => by simp [greedyFuel]
  | n + 1, ps => by
    simp only [greedyFuel]
    split
    · simp
    · simpa using greedyFuel_length_le n _

/--
The shortest plan this file will look for: repeatedly settle the largest debtor
against the largest creditor.

Every transfer zeroes at least one participant, so `n` people need at most
`n - 1` transfers, and the last of them is always the one that closes the books.
That bound is worst-case optimal; the true minimum is `n` less the largest number
of disjoint subgroups that already sum to zero among themselves, which is
subset-sum and not worth chasing for a hut weekend.

Being shortest is not the same as being sensible: this will cheerfully tell
somebody to pay a person they never dealt with. `star` is the other answer.
-/
def greedy (ps : List Position) : List Transfer := greedyFuel ps.length ps

/-- A greedy plan never has more transfers than there are participants. -/
theorem greedy_length_le (ps : List Position) : (greedy ps).length ≤ ps.length :=
  greedyFuel_length_le ps.length ps

/--
Everybody settles with one person: whoever holds the budget.

The same `n - 1` transfers in the worst case, and no payment between two people
who never dealt with each other — which is usually what a group actually wants,
even when a cleverer plan exists.
-/
def star (hub : String) (ps : List Position) : List Transfer :=
  ps.filterMap fun p =>
    if p.who == hub || p.minor == 0 then none
    else if p.minor > 0 then some { from_ := p.who, to := hub, minor := p.minor }
    else some { from_ := hub, to := p.who, minor := -p.minor }

/--
Checks a plan before anything is written down.

The positions must sum to zero — otherwise there is money nobody has been made
responsible for, and no plan can settle them — and performing the plan must
leave every position at zero. Both are decidable, so the claims that get raised
are exactly the ones that square the budget.
-/
def validate (ps : List Position) (ts : List Transfer) :
    Except String { ts : List Transfer // Settles ps ts } :=
  if h : Settles ps ts then .ok ⟨ts, h⟩
  else
    let left := (residual ps ts).filter (fun p => p.minor != 0)
    let detail := String.intercalate ", " (left.map fun p => s!"{p.who} {p.minor}")
    if total ps != 0 then
      .error s!"these positions do not sum to zero, so nothing can settle them: {detail}"
    else .error s!"the plan would leave: {detail}"

end Settle
end Resources
