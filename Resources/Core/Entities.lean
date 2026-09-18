import Resources.Core.Filter
import Resources.Core.Settle

/-!
# The records the ledger keeps beside its transactions

Groups, trips, rules, import batches and budgets are plain values: they say what
was decided, and nothing about them needs a database or a clock. They lived in
the store only because the store was the first thing that had to read them back,
so they are here now, where the pure core can apply an operation to them without
touching SQL.

The store keeps its own namespaces (`Groups`, `Trips`, `Rules`, `Budgets`) and
goes on projecting these into tables; what moved is the shape, not the storage.
-/

namespace Resources

/-! ## Groups -/

/-- A named set of people to split costs with. -/
structure PartyGroup where
  name : String
  members : List String
  /-- Which realm this group belongs to: the one whose admins decide about it. -/
  realm : RealmId := Realm.selfId
  deriving Repr, Inhabited

/-! ## Trips -/

/-- A named window of spending someone else pays for. -/
structure Trip where
  id : String
  name : String
  starts : Date
  ends : Date
  payer : String
  note : Option String
  /-- Which realm this trip belongs to. -/
  realm : RealmId := Realm.selfId
  deriving Repr, Inhabited

/-! ## Rules -/

/-- A categorisation rule: a filter plus what to do when it matches. -/
structure Rule where
  id : RuleId
  name : String
  /-- Source text of the filter, so it round-trips through the database. -/
  filterSrc : String
  filter : Filter
  setAccount : Option String
  addLabels : List String
  setParty : Option String
  priority : Int
  /-- Which realm this rule belongs to: rules drive what an import files where. -/
  realm : RealmId := Realm.selfId
  deriving Repr, Inhabited

/-! ## Imports -/

/-- One run of an importer over one file. -/
structure ImportBatch where
  id : BatchId
  profile : String
  filename : Option String
  account : Option AccountId
  stamp : String
  total : Nat
  duplicates : Nat
  /-- Which realm this import was recorded in. -/
  realm : RealmId := Realm.selfId
  deriving Repr, Inhabited, Lean.ToJson

/-! ## Budgets -/

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

end Resources
