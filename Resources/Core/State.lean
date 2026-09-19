import Resources.Core.Entities
import Resources.Core.Receipt
import Resources.Core.Invoice

/-!
# The state of the ledger

Everything the store keeps, as one value. `State` is what an operation is
applied to and what a log of events replays into; the SQLite database is a
projection of it, not the thing itself.

Two rules hold throughout, and the rest of `Core` depends on both.

*Nothing here knows the time or the world.* There is no `IO`, no clock and no
identifier generator: an operation that needs a date or a fresh id carries it,
so replaying a log tomorrow produces exactly the state it produced today.

*Iteration is sorted.* The maps are hashed, so their order is an implementation
detail of the hash function, and folding over one would make the result depend
on it. Every fold in `Core` goes through `sortedPairs` or one of the `…Sorted`
helpers below, which order by id — and `canonical` is the same idea applied to
the whole state, so two replays can be compared without caring how anything was
stored.

## Realms, members and rights

A *realm* is a set of accounts with one viewer set and one key. A *member* is an
identity that may read and write inside the realms it belongs to. A ledger with
one of each — you, in your own realm — passes every check below, which is why
they went untested for so long; what they are for is the ledger with a second
person in it, where every one of them is the difference between a viewer and an
owner.

Three questions are asked of a member, and they are asked here rather than at
each caller. `isMemberOf` is whether they may see a realm at all; `canAdminister`
is whether they decide things about it; and `canPostLeg` is whether they may
write one particular posting into one particular account — a leg rather than an
account, because the right a budget hands its participants is a right to put
money *in*.
-/

namespace Resources

/-! ## Members and realms -/

/-- What a member may do inside a realm. -/
inductive RealmRole
  | viewer | admin
  deriving DecidableEq, Repr, Inhabited

namespace RealmRole

/-- The name used in JSON and in the database. -/
def toString : RealmRole → String
  | .viewer => "viewer" | .admin => "admin"

/-- Inverse of `toString`. -/
def ofString? : String → Option RealmRole
  | "viewer" => some .viewer | "admin" => some .admin | _ => none

instance : ToString RealmRole := ⟨RealmRole.toString⟩

end RealmRole

/--
A member of the ledger: an identity.

Later a public key; for now the one member is `Member.selfId`, and `party` is
the counterparty they are, so a member's own spending has somewhere to land.
-/
structure Member where
  id : MemberId
  name : String
  party : PartyId := Party.selfId
  deriving Repr, Inhabited

/-- A set of accounts with one viewer set and one key. -/
structure Realm where
  id : RealmId
  name : String
  /-- Who may see this realm, sorted by member id. -/
  members : List (MemberId × RealmRole) := []
  /-- The key generation, bumped whenever a revoke or a rotation invalidates it. -/
  generation : Nat := 0
  deriving Repr, Inhabited

namespace Realm

/-- The role a member holds here, if any. -/
def roleOf (r : Realm) (m : MemberId) : Option RealmRole :=
  (r.members.find? (fun x => x.1 == m)).map (·.2)

/-- Whether a member may administer this realm. -/
def isAdmin (r : Realm) (m : MemberId) : Bool := r.roleOf m == some .admin

/-- Whether a member may see this realm at all. -/
def isMember (r : Realm) (m : MemberId) : Bool := (r.roleOf m).isSome

/-- Records a member's role, replacing any role they held, keeping members sorted by id. -/
def withMember (r : Realm) (m : MemberId) (role : RealmRole) : Realm :=
  let rest := r.members.filter (fun x => x.1 != m)
  { r with members := (rest ++ [(m, role)]).mergeSort (fun a b => a.1.val ≤ b.1.val) }

/-- Drops a member from this realm. -/
def withoutMember (r : Realm) (m : MemberId) : Realm :=
  { r with members := r.members.filter (fun x => x.1 != m) }

end Realm

/-! ## What a budget, an invoice and a receipt look like in state -/

/--
One cost of a budget, taken by one member: "that one was mine".

A claim is not money and moves none: it is a statement, in the shared order, by
the person it is about. What it is *for* is the moment the budget is divided --
a cost somebody has taken is borne by whoever took it, and only what nobody took
is divided among everybody by weight.

It says nothing about who paid, which the postings already say. A cost you paid
for and claim is one you bore yourself; a cost somebody else paid for and you
claim is one you owe them.
-/
structure CostClaim where
  txn : TxId
  member : MemberId
  deriving Repr, Inhabited, DecidableEq

/--
A budget, the people it is divided among, and the three entries it is keyed to.

`realm`, `account` and `label` are written once, by `openBudget`, and every
question about the budget goes through them. They are ids rather than names on
purpose: a budget used to be found by the name of its equity account and its
claims by the name of its label, and a name is something anybody who may write
an account or a label can take — an account called `Budget.Hut` with a lower id
became *the* budget account for every reader. An id cannot be squatted.

`label` is empty until something pins it: `openBudget` takes the label of the
budget's own name when the ledger already has one, and `allocate`, `settle` and
`closeBudget` write the label they were told to raise their claims under.
-/
structure BudgetState where
  budget : Budget
  /-- Who it is divided among, in the order they were named. -/
  participants : List Participant := []
  /--
  The costs people have said were theirs, in the order they said so.

  One entry per person per cost: several people on one cost is that cost split
  equally between them, which is the whole of the arithmetic. A cost nobody has
  taken is not here at all.
  -/
  claims : List CostClaim := []
  /-- The realm the budget lives in: the one whose admins decide about it. -/
  realm : RealmId := Realm.selfId
  /-- The equity account that holds it. -/
  account : AccountId := ⟨""⟩
  /-- The label the claims raised for it carry, when one has been pinned. -/
  label : LabelId := ⟨""⟩
  deriving Repr, Inhabited

namespace BudgetState

/-- Who has taken a cost, in the order they took it. -/
def claimantsOf (b : BudgetState) (txn : TxId) : List MemberId :=
  (b.claims.filter (·.txn == txn)).map (·.member)

/-- The costs anybody has taken, in the order they were first taken. -/
def claimed (b : BudgetState) : List TxId := Id.run do
  let mut seen : List TxId := []
  for c in b.claims do
    if !seen.contains c.txn then seen := seen ++ [c.txn]
  return seen

end BudgetState

/-- An invoice and the outlays it bills for. -/
structure InvoiceState where
  invoice : Invoice
  sources : List TxId := []
  /--
  The realm the invoice was issued in: the one whose admins decide about it.

  An invoice record used to have no realm at all, which the per-realm numbering
  made worse rather than better. The counter is keyed by realm, so an admin of
  any realm a reader could open could delete a draft issued somewhere else and
  wind back *their own* realm's counter: the issuing realm kept the burnt number
  while an unrelated sequence went backwards, and the next invoice there
  duplicated a number somebody had already been sent. The same door marked any
  invoice in the ledger `paid` or `void`.

  Written once, at `issueInvoice`, from the part's realm; every later word about
  the invoice has to be said in it, and the counter is only ever wound back by
  the realm that handed the number out.
  -/
  realm : RealmId := Realm.selfId
  deriving Repr, Inhabited

/--
A stored file, what was read off it, and the lines it prints.

`extracted.items` is always empty: the lines are `items`, because they are
edited by hand after extraction and the fields are not.
-/
structure BlobState where
  /-- The stored file's metadata. Named `file` because `meta` is a Lean keyword. -/
  file : Attachment
  extracted : Extracted := {}
  items : List LineItem := []
  /-- Who registered these bytes: the member who may say what they contain. -/
  registeredBy : MemberId := Member.selfId
  /--
  The realm these bytes were filed in.

  `registeredBy` used to be realm-blind: whoever first filed a set of bytes kept
  the right to rewrite what they said from a part in *any* realm they held a key
  for, including after the receipt had been attached to a transaction in a realm
  they could not otherwise touch. The realm is written once, at registration,
  and every later word about the file has to be said in it.
  -/
  realm : RealmId := Realm.selfId
  deriving Repr, Inhabited

namespace BlobState

/-- What this receipt says it came to, when a total was read off it. -/
def total? (b : BlobState) : Option Amount :=
  match b.extracted.total with
  | some t => if t.minor == 0 then none else some t
  | none => none

end BlobState

/-! ## The state -/

/--
Everything the ledger knows.

Keyed by id throughout, except groups and trips, which are named rather than
identified — the store keys them by name too, and a name is what the CLI and the
web client pass.
-/
structure State where
  realms : Std.HashMap String Realm := {}
  members : Std.HashMap String Member := {}
  accounts : Std.HashMap String Account := {}
  labels : Std.HashMap String Label := {}
  parties : Std.HashMap String Party := {}
  /-- Keyed by name. -/
  groups : Std.HashMap String PartyGroup := {}
  /-- Keyed by name. -/
  trips : Std.HashMap String Trip := {}
  rules : Std.HashMap String Rule := {}
  /-- Every transaction, in every state: posted, pending, settled and void. -/
  txns : Std.HashMap String Transaction := {}
  budgets : Std.HashMap String BudgetState := {}
  invoices : Std.HashMap String InvoiceState := {}
  /-- Keyed by content hash. -/
  blobs : Std.HashMap String BlobState := {}
  batches : Std.HashMap String ImportBatch := {}
  /-- Monotonic counters, which is how invoice numbering stays gapless. -/
  counters : Std.HashMap String Int := {}
  /-- Import fingerprints already seen, which is what makes re-importing a no-op. -/
  fingerprints : Std.HashSet String := {}

instance : Inhabited State := ⟨{}⟩

/-- The entries of a map, ordered by key: the only way `Core` iterates over one. -/
def sortedPairs {α : Type} (m : Std.HashMap String α) : List (String × α) :=
  m.toList.mergeSort (fun a b => a.1 ≤ b.1)

/-- The values of a map, ordered by key. -/
def sortedValues {α : Type} (m : Std.HashMap String α) : List α :=
  (sortedPairs m).map (·.2)

namespace State

/-- The ledger as it starts: your realm and you, and nothing else. -/
def init : State :=
  { realms := ({} : Std.HashMap String Realm).insert Realm.selfId.val
      { id := Realm.selfId, name := "me", members := [(Member.selfId, .admin)] }
    members := ({} : Std.HashMap String Member).insert Member.selfId.val
      { id := Member.selfId, name := "me", party := Party.selfId } }

/-- Your own realm, if it is still there. -/
def selfRealm (s : State) : Option Realm := s.realms[Realm.selfId.val]?

/-- A realm by id. -/
def realm? (s : State) (id : RealmId) : Option Realm := s.realms[id.val]?

/-- A member by id. -/
def member? (s : State) (id : MemberId) : Option Member := s.members[id.val]?

/-- An account by id. -/
def account? (s : State) (id : AccountId) : Option Account := s.accounts[id.val]?

/-- A transaction by id, whatever state it is in. -/
def txn? (s : State) (id : TxId) : Option Transaction := s.txns[id.val]?

/-- A label by id. -/
def label? (s : State) (id : LabelId) : Option Label := s.labels[id.val]?

/-- A party by id. -/
def party? (s : State) (id : PartyId) : Option Party := s.parties[id.val]?

/-- A rule by id. -/
def rule? (s : State) (id : RuleId) : Option Rule := s.rules[id.val]?

/-- A stored receipt by content hash. -/
def blob? (s : State) (sha : String) : Option BlobState := s.blobs[sha]?

/-- A budget by id. -/
def budget? (s : State) (id : BudgetId) : Option BudgetState := s.budgets[id.val]?

/-- An invoice by id. -/
def invoice? (s : State) (id : InvoiceId) : Option InvoiceState := s.invoices[id.val]?

/-- Every account, ordered by id. -/
def accountsSorted (s : State) : List Account := sortedValues s.accounts

/-- Every transaction, ordered by id. -/
def txnsSorted (s : State) : List Transaction := sortedValues s.txns

/-- Every rule, ordered by id. -/
def rulesSorted (s : State) : List Rule := sortedValues s.rules

/-- Every realm, ordered by id. -/
def realmsSorted (s : State) : List Realm := sortedValues s.realms

/--
An account by name inside one realm: the only way to find one by name.

A name across the whole ledger is not a question with an answer. A name is
something anybody who may write an account can take, so a viewer who
self-granted a purse called `Assets.Purse.Anna` with a low id used to decide, for
every reader, which account that name meant — and the ledger holding one account
of a name was never a fact about the books either, only about the tables, which
kept `account.name` unique until migration 25 taught them to keep it unique per
realm. Every lookup that goes by name (a budget's pot, a participant's share)
goes through this one, and a realm is a set of accounts one group of people may
write.
-/
def accountByNameIn? (s : State) (realm : RealmId) (name : String) : Option Account :=
  s.accountsSorted.find? (fun a => a.name == name && a.realm == realm)

/-- The posted transactions, ordered by id: the ledger every balance is taken over. -/
def ledger (s : State) : Ledger := s.txnsSorted.filter (fun t => t.state == .posted)

/-- The balance of an account in one commodity, over posted transactions only. -/
def balance (s : State) (a : AccountId) (c : String) : Int := s.ledger.balance a c

/--
The accounts money is held in, ordered by id.

Deliberately blind to the owner: a friend's bank account funds a shared cost
exactly the way yours does, which is what makes the funding leg recognisable
without asking whose it is.
-/
def fundingAccounts (s : State) : List AccountId :=
  (s.accountsSorted.filter Account.holdsMoney).map (·.id)

/-- Which realm an account sits in. -/
def realmOf (s : State) (a : AccountId) : Option RealmId := (s.account? a).map (·.realm)

/-- How many postings, in any transaction, still land in this account. -/
def postingCount (s : State) (a : AccountId) : Nat :=
  (s.txnsSorted.map (fun t => (t.postings.filter (fun p => p.account == a)).length)).sum

/-- Whether an open budget is held in the account with this id. -/
def openBudgetAccount (s : State) (id : AccountId) : Bool :=
  (sortedValues s.budgets).any (fun b => !b.budget.closed && b.account == id)

/--
Whether a member may write a posting of this size into an account.

Four ways, and they are the whole rule: it is their own purse in this realm,
they were named as a poster on it, they administer the realm it belongs to, or
it is the equity account of a budget that is still open, they are in the realm
that budget lives in, and the leg they are writing puts money *into* the pot.

The fourth is what makes a contribution an ordinary transaction. Somebody the
budget is divided among has to be able to say "I paid for this too", and the
only account they need for it besides their own purse is the budget's. Two
things bound it, and both were missing. It is keyed on the budget's own account
id, not on a name anybody could give an account of their own; and it is a right
to contribute rather than a right to write, because a pot that everybody may
take out of is not a pot. A closed budget is a decided one, so the right ends
with it either way.
-/
def canPostLeg (s : State) (m : MemberId) (a : Account) (minor : Int) : Bool :=
  a.bridgeOf == some m || a.posters.contains m ||
    (match s.realm? a.realm with
     | some r => r.isAdmin m || (r.isMember m && s.openBudgetAccount a.id && minor > 0)
     | none => false)

/--
Whether a member may write into an account at all.

`canPostLeg` with the most generous leg there is, which is what the operations
that move a whole account rather than a posting — a merge, a deletion — ask.
-/
def canPost (s : State) (m : MemberId) (a : Account) : Bool := s.canPostLeg m a 1

/-- Whether a member administers a realm. -/
def canAdminister (s : State) (m : MemberId) (realm : RealmId) : Bool :=
  match s.realm? realm with
  | some r => r.isAdmin m
  | none => false

/-- Whether a member may see a realm at all. -/
def isMemberOf (s : State) (m : MemberId) (realm : RealmId) : Bool :=
  match s.realm? realm with
  | some r => r.isMember m
  | none => false

/-! ## Comparing two states

Replaying a log must give the same state twice, and "the same" cannot be read
off a hash map: the buckets depend on insertion order. `canonical` sorts every
map by key and prints each value, so equality is decidable, order-independent
and — when a test fails — legible.
-/

/-- One section of the canonical form: a map's entries, sorted by key and printed. -/
private def section' {α : Type} [Repr α] (name : String) (m : Std.HashMap String α) :
    String × List (String × String) :=
  (name, (sortedPairs m).map (fun (k, v) => (k, reprStr v)))

/-- The whole state as sorted, printed entries: what two replays are compared by. -/
def canonical (s : State) : List (String × List (String × String)) :=
  [ section' "realms" s.realms
  , section' "members" s.members
  , section' "accounts" s.accounts
  , section' "labels" s.labels
  , section' "parties" s.parties
  , section' "groups" s.groups
  , section' "trips" s.trips
  , section' "rules" s.rules
  , section' "txns" s.txns
  , section' "budgets" s.budgets
  , section' "invoices" s.invoices
  , section' "blobs" s.blobs
  , section' "batches" s.batches
  , section' "counters" s.counters
  , ("fingerprints", (s.fingerprints.toList.mergeSort (· ≤ ·)).map (fun f => (f, ""))) ]

instance : BEq State := ⟨fun a b => a.canonical == b.canonical⟩

end State

end Resources
