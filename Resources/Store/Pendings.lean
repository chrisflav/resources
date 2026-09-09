import Resources.Core.Settle
import Resources.Store.Repo

/-!
# Claims

A claim is a transaction that has not happened: money that is expected to pass
from one account to another, by a date, because a budget was divided or an
invoice was sent. It balances, it is dated, it names two accounts — everything a
transaction is — and the one thing it is not is *true yet*.

That distinction is the whole point, and it is enforced by the schema rather
than by discipline: claims live in `posting_all` alongside everything else, and
the `posting` view every balance goes through shows only posted rows. Imaginary
money cannot reach a balance because no query has to remember to exclude it.

What this replaces is a convention. Aging outlays oldest-first gave a defensible
answer to "what is still outstanding" without knowing which specific outlay a
lump payment repaid — but it was a guess, and it was wrong whenever somebody
paid for one thing and not another. A claim is the specific thing. A part
payment reduces *it*, and there is nothing left to guess about.

Three verbs:

* `create` raises a claim.
* `resolve` meets one against the transaction that actually performed it. The
  claim does not turn into that transaction — the bank line already exists, with
  the fingerprint that reconciles it against the statement. What the claim
  contributes is the counterparty: the leg the importer could only guess at.
* `void` retires one that will never be performed, which is what a write-off is.
-/

open Lean

namespace Resources
namespace Pendings

/-- The tag both legs of a claim carry, so a claim is recognisable leg by leg. -/
def tag : String := "claim"

/-- The account a claim expects money to arrive in. -/
def receiver? (t : Transaction) : Option AccountId :=
  (t.postings.find? (·.amount.minor > 0)).map (·.account)

/-- The account a claim expects money to leave. -/
def payer? (t : Transaction) : Option AccountId :=
  (t.postings.find? (·.amount.minor < 0)).map (·.account)

/-- What a claim still asks for. -/
def amount (t : Transaction) : Amount :=
  match t.postings.find? (·.amount.minor > 0) with
  | some p => p.amount
  | none => ⟨Commodity.eur, 0⟩

/--
Raises a claim for `amount` passing from `payer` to `receiver` by `due`.

Two legs, both tagged, and validated like anything else that reaches the store:
a promise that does not balance is not a promise about money.
-/
def create (ctx : Ctx) (payer receiver : AccountId) (amount : Amount) (due : Date)
    (narration : String) (actor : String) (labels : List LabelId := [])
    (payee : Option String := none) : IO Transaction := do
  if amount.minor ≤ 0 then
    throw <| IO.userError "a claim has to ask for something"
  if payer == receiver then
    throw <| IO.userError "a claim between one account and itself asks for nothing"
  let t : Transaction :=
    { id := ⟨← freshId⟩, date := due, payee, narration, state := .pending
      postings :=
        [{ account := receiver, amount, tag := some tag },
         { account := payer, amount := ⟨amount.commodity, -amount.minor⟩, tag := some tag }]
      labels, source := .manual actor }
  match t.validate with
  | .error e => throw <| IO.userError e
  | .ok bt =>
    Txns.put ctx bt actor "claim"
    return bt.val

/-- Outstanding claims matching a filter, soonest due first. -/
def list (ctx : Ctx) (f : Filter := .all) (limit : Nat := 500) : IO (Array Transaction) :=
  Txns.list ctx f { key := .date, descending := false } limit 0 (some .pending)

/-- Claims in any state, for a history view. -/
def history (ctx : Ctx) (f : Filter := .all) (limit : Nat := 500) : IO (Array Transaction) := do
  let all ← Txns.list ctx f { key := .date, descending := true } limit 0 none
  return all.filter fun t => t.state != .posted

/--
Meets a claim against the transaction that performed it.

The counter legs of the real transaction are moved into the paying account,
which is the one thing the claim knew and the importer did not. The bank leg is
untouched, so what reconciles against the statement goes on reconciling.

A part payment splits the claim: the part that was met becomes a settled claim
of its own, pointing at the entry that met it, and the original is reduced to
what is still outstanding. This is where aging oldest-first used to be needed,
and is not — there is no question which outlay was paid, because the claim *is*
the outlay.

Splitting rather than merely shrinking matters for more than the audit trail. A
settlement nets off what has already been asked for before it asks for anything
more, and a claim that had quietly shrunk would let the difference be asked for
a second time.
-/
def resolve (ctx : Ctx) (id : TxId) (actual : TxId) (actor : String) : IO Transaction := do
  let some claim ← Txns.get? ctx id
    | throw <| IO.userError s!"no such claim: {id.val}"
  if claim.state != .pending then
    throw <| IO.userError s!"that claim is already {claim.state}"
  let some act ← Txns.get? ctx actual
    | throw <| IO.userError s!"no such transaction: {actual.val}"
  if act.state != .posted then
    throw <| IO.userError "a claim can only be met by a transaction that actually happened"
  let some recv := receiver? claim
    | throw <| IO.userError "this claim has no receiving leg"
  let some payAcc := payer? claim
    | throw <| IO.userError "this claim has no paying leg"
  let asked := amount claim
  let arrived := act.netIn recv asked.commodity.code
  if arrived ≤ 0 then
    let some acc ← Accounts.byId? ctx recv | throw <| IO.userError "the receiving account is gone"
    throw <| IO.userError s!"{actual.val} brings nothing into {acc.name}"
  let some payer ← Accounts.byId? ctx payAcc
    | throw <| IO.userError "the paying account is gone"
  let matched := min arrived asked.minor
  -- What the claim contributes to the real transaction: who the money was from.
  -- Anything it overpays goes to the same place, which is right — an
  -- overpayment leaves their purse owing them the difference.
  discard <| Txns.claim ctx #[actual] payer.name actor
  let left := asked.minor - matched
  -- A met claim is stamped the way a merge stamps its sources, so it points at
  -- the entry that discharged it.
  let resize (n : Int) (t : Transaction) : Transaction :=
    { t with postings := t.postings.map fun p =>
        { p with amount := (⟨p.amount.commodity, if p.amount.minor > 0 then n else -n⟩ : Amount) } }
  let stamp (t : Transaction) : Transaction :=
    { t with postings := t.postings.map fun p => { p with origin := p.origin <|> some actual.val } }
  let write (t : Transaction) (kind : String) : IO Transaction := do
    match t.validate with
    | .error e => throw <| IO.userError s!"the claim would not balance: {e}"
    | .ok bt =>
      Txns.put ctx bt actor kind
      return bt.val
  if left == 0 then
    return ← write (stamp { claim with state := .settled }) "resolve"
  -- The part that was met becomes a record in its own right, so what has been
  -- asked for stays the sum of both halves.
  discard <| write
    (stamp (resize matched { claim with id := ⟨← freshId⟩, date := act.date, state := .settled }))
    "resolve"
  write (resize left claim) "part-resolve"

/--
Retires a claim that will never be performed.

`writeOffTo`, when given, records the loss: what they still owe leaves their
account and lands in one of yours. Without it the claim simply stops being
outstanding and their account goes on saying they owe you, which is the right
state while you have given up asking but not given up hope.

Either way the spending stays where the division put it. Somebody consumed it,
and their not paying does not turn it into your consumption — it turns it into
your loss, which is a different account and a different sentence.
-/
def void (ctx : Ctx) (id : TxId) (actor : String)
    (writeOffTo : Option String := none) : IO Transaction := do
  let some claim ← Txns.get? ctx id
    | throw <| IO.userError s!"no such claim: {id.val}"
  if claim.state == .posted then
    throw <| IO.userError "that is a transaction, not a claim"
  if let some name := writeOffTo then
    let some payAcc := payer? claim
      | throw <| IO.userError "this claim has no paying leg to write off"
    let loss ← Accounts.ensure ctx name
    if !loss.mine then
      throw <| IO.userError s!"{loss.name} is not yours, so the loss cannot land there"
    let amount := amount claim
    let today ← Date.today
    let entry : Transaction :=
      { id := ⟨← freshId⟩, date := today, payee := claim.payee
        narration := s!"written off: {claim.narration}"
        postings :=
          [{ account := loss.id, amount },
           { account := payAcc, amount := ⟨amount.commodity, -amount.minor⟩ }]
        labels := claim.labels, source := .manual actor }
    match entry.validate with
    | .error e => throw <| IO.userError s!"the write-off would not balance: {e}"
    | .ok bt => Txns.put ctx bt actor "write-off"
  match ({ claim with state := .void } : Transaction).validate with
  | .error e => throw <| IO.userError e
  | .ok bt =>
    Txns.put ctx bt actor "void"
    return bt.val

/--
Posted transactions that could meet this claim: money arriving in the account it
names, on or after the day it was raised, in the right commodity.

Deliberately a suggestion and not an action. Matching by amount and direction is
a guess, and the one mechanism that is not a guess — the ISO 11649 reference an
invoice puts in the payer's transfer — belongs to the invoice, which knows it.
-/
def candidates (ctx : Ctx) (t : Transaction) (limit : Nat := 10) : IO (Array Transaction) := do
  let some recv := receiver? t | return #[]
  let some acc ← Accounts.byId? ctx recv | return #[]
  let asked := amount t
  let hits ← Txns.list ctx (.account acc.name) { key := .date, descending := true } 200
  return (hits.filter fun x => x.netIn recv asked.commodity.code > 0).take limit

/--
A claim, read as the movement it would make between two owners.

This is the bridge to `Settle`: a plan is arithmetic over positions, and a claim
already outstanding is a movement somebody has already been asked to make, so it
has to be netted off before any more are raised.
-/
def transferOf (accounts : Array Account) (t : Transaction) : Option Settle.Transfer := do
  let recv ← receiver? t
  let pay ← payer? t
  let to ← accounts.find? (·.id == recv)
  let from_ ← accounts.find? (·.id == pay)
  pure { from_ := from_.owner.val, to := to.owner.val, minor := (amount t).minor }

end Pendings
end Resources
