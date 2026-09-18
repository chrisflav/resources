import Resources.Core.Claim
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

/--
Raises a claim for `amount` passing from `payer` to `receiver` by `due`.

Two legs, both tagged, and validated like anything else that reaches the store:
a promise that does not balance is not a promise about money. The tagging, the
checks and the validation all live in `Op.raiseClaim`; what is left here is the
one thing `Core` cannot do, which is to mint the id.
-/
def create (ctx : Ctx) (payer receiver : AccountId) (amount : Amount) (due : Date)
    (narration : String) (actor : String) (labels : List LabelId := [])
    (payee : Option String := none) : IO Transaction := do
  let t : Transaction :=
    { id := ⟨← freshId⟩, date := due, payee, narration, state := .pending
      postings :=
        [{ account := receiver, amount, tag := some tag },
         { account := payer, amount := ⟨amount.commodity, -amount.minor⟩, tag := some tag }]
      labels, source := .manual actor }
  let changes ← ctx.commit actor [.raiseClaim t] (kind := "claim")
  match (Change.written changes)[0]? with
  | some raised => return raised
  | none => throw <| IO.userError "a claim has to ask for something"

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
  -- Read once, before anything is written, to name the revisions: a part
  -- payment records the half that was met as `resolve` and the claim it reduced
  -- as `part-resolve`, and the kind has to be chosen per id in advance.
  let before ← ctx.state.get
  let partly : Bool :=
    match before.txn? id, before.txn? actual with
    | some claim, some act =>
      match receiver? claim with
      | some recv =>
        let asked := amount claim
        let arrived := act.netIn recv asked.commodity.code
        0 < arrived && arrived < asked.minor
      | none => false
    | _, _ => false
  let splitId : TxId := ⟨← freshId⟩
  discard <| ctx.commit actor [.resolveClaim id actual splitId] (kind := "resolve")
    (kinds := fun x =>
      if x == actual then some "claim"
      else if x == id && partly then some "part-resolve"
      else none)
  let some met := (← ctx.state.get).txn? id
    | throw <| IO.userError s!"no such claim: {id.val}"
  return met

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
  let before ← ctx.state.get
  let some claim := before.txn? id
    | throw <| IO.userError s!"no such claim: {id.val}"
  if claim.state == .posted then
    throw <| IO.userError "that is a transaction, not a claim"
  -- The account the loss lands in has to exist before the operation can name
  -- it, and the entry needs an id and a date: the three things `Core` has no
  -- way to produce for itself.
  let writeOff ← match writeOffTo with
    | some name => do
      let loss ← Accounts.ensure ctx name
      pure (some (loss.id, (⟨← freshId⟩ : TxId), ← Date.today))
    | none => pure none
  discard <| ctx.commit actor [.voidClaim id writeOff] (kind := "void")
    (kinds := fun x => if some x == writeOff.map (·.2.1) then some "write-off" else none)
  let some voided := (← ctx.state.get).txn? id
    | throw <| IO.userError s!"no such claim: {id.val}"
  return voided

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

end Pendings
end Resources
