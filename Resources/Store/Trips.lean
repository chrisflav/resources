import Resources.Store.Repo

/-!
# Trips

A trip is a named window of spending that somebody else pays for: a conference,
a hut weekend, a business flight.

It is deliberately thin. The grouping is a label, what is owed is the payer's
own purse, and the cost overview is an invoice — all of which already exist. A
trip adds only the two facts none of them carry: the dates it covers, and who is
paying. That is what lets it *suggest* the hotel and the restaurants alongside
the flight, instead of making you find them.
-/

open Lean

namespace Resources

private structure TripRow where
  id : String
  name : String
  starts : String
  ends : String
  payer : String
  note : Option String
  realmId : String
  deriving SQLite.Row

namespace Trips

private def ofRow (r : TripRow) : Trip :=
  { id := r.id, name := r.name
    starts := (Date.ofIso? r.starts).getD default
    ends := (Date.ofIso? r.ends).getD default
    payer := r.payer, note := r.note, realm := ⟨r.realmId⟩ }

private def cols : String := "SELECT id, name, starts, ends, payer, note, realm_id FROM trip"

/-- Every trip, newest first. -/
def list (ctx : Ctx) : IO (Array Trip) := do
  return (← Db.rows TripRow ctx.db (cols ++ " ORDER BY starts DESC")).map ofRow

/-- Looks a trip up by name. -/
def byName? (ctx : Ctx) (name : String) : IO (Option Trip) := do
  return (← Db.row? TripRow ctx.db (cols ++ s!" WHERE name = {Db.lit name}")).map ofRow

/-- The label that groups a trip's transactions. -/
def label (t : Trip) : String := "trip:" ++ t.name

/-- Whose spending a trip's costs are: the payer's own purse. -/
def purse (t : Trip) : String := Accounts.purseName t.payer

/-- Creates a trip, its label and the payer's purse. -/
def create (ctx : Ctx) (name : String) (starts ends : Date) (payer : String)
    (note : Option String := none) : IO Trip := do
  if (← byName? ctx name).isSome then
    throw <| IO.userError s!"a trip called {name} already exists"
  let id ← freshId
  let trip : Trip := { id, name, starts, ends, payer, note }
  discard <| ctx.commit "system" [.putTrip trip]
  discard <| Labels.ensure ctx (label trip)
  discard <| Accounts.purse ctx (← Parties.contact ctx payer)
  return trip

/-- Deletes a trip. The label and the transactions it grouped are left alone. -/
def delete (ctx : Ctx) (name : String) : IO Unit :=
  discard <| ctx.commit "system" [.deleteTrip name]

/-- The transactions already assigned to a trip. -/
def members (ctx : Ctx) (t : Trip) : IO (Array Transaction) :=
  Txns.list ctx (.label (label t)) { key := .date, descending := false } 10000

/--
Spending inside the trip's dates that is not yet part of it.

Money arriving is excluded, and so is anything already claimed against someone:
the point is to surface the hotel and the restaurants you have not thought
about, not to re-propose what is already settled.
-/
def suggest (ctx : Ctx) (t : Trip) : IO (Array Transaction) := do
  let inWindow ← Txns.list ctx
    (.and (.dateFrom t.starts) (.dateTo t.ends)) { key := .date, descending := false } 10000
  let accounts ← Accounts.list ctx
  -- Already somebody else's, so already answered for.
  let claimed := (accounts.filter fun a => !a.mine).map (·.id)
  let funding := (accounts.filter fun a => a.holdsMoney && a.mine).map (·.id)
  let mine ← members ctx t
  let already := mine.map (·.id)
  return inWindow.filter fun x =>
    !already.contains x.id &&
      !x.postings.any (fun p => claimed.contains p.account) &&
      (funding.map (fun a => x.netIn a "EUR")).foldl (· + ·) 0 < 0

/-- Adds transactions to a trip: labels them and claims them against the payer. -/
def add (ctx : Ctx) (t : Trip) (ids : Array TxId) (actor : String) : IO Nat := do
  let lbl ← Labels.ensure ctx (label t)
  -- Made sure of before the claim, because `claim` creates a missing target
  -- account and would have no way to know whose it is.
  discard <| Accounts.purse ctx (← Parties.contact ctx t.payer)
  let mut n := 0
  for id in ids do
    let some x ← Txns.get? ctx id | continue
    let extra := if x.labels.contains lbl.id then [] else [lbl.id]
    let labelled := { x with labels := x.labels ++ extra }
    match labelled.validate with
    | .error _ => continue
    | .ok bt =>
      Txns.put ctx bt actor "trip"
      n := n + 1
  discard <| Txns.claim ctx ids (purse t) actor
  return n

/-- Removes transactions from a trip's label. The claim is left in place. -/
def drop (ctx : Ctx) (t : Trip) (ids : Array TxId) (actor : String) : IO Nat := do
  let some lbl ← Labels.byName? ctx (label t) | return 0
  let mut n := 0
  for id in ids do
    let some x ← Txns.get? ctx id | continue
    let stripped := { x with labels := x.labels.filter (· != lbl.id) }
    match stripped.validate with
    | .error _ => continue
    | .ok bt =>
      Txns.put ctx bt actor "trip"
      n := n + 1
  return n

/-- What a trip has cost so far, across its members. -/
def total (ctx : Ctx) (t : Trip) : IO Amount := do
  let mine ← members ctx t
  let accounts ← Accounts.list ctx
  let funding := (accounts.filter fun a => a.holdsMoney && a.mine).map (·.id)
  let sum := mine.foldl (fun acc x =>
    acc + (funding.map (fun a => x.netIn a "EUR")).foldl (· + ·) 0) 0
  return ⟨Commodity.eur, -sum⟩

end Trips

end Resources
