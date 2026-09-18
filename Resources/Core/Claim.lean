import Resources.Core.Entities

/-!
# Reading a claim

A claim is a transaction that has not happened: money expected to pass from one
account to another by a date. Everything about it is readable off the
transaction itself — which account is owed, which owes, and how much — so these
are functions of a `Transaction` and nothing else.

The verbs that raise, meet and retire claims are operations (`Core/Apply.lean`);
what lives here is the arithmetic they and the store both need.
-/

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
