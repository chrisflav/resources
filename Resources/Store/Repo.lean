import Resources.Store.Commit

/-!
# Repository

Every read and write of ledger data goes through here. Reads are SQL, because
the tables are indexed and a query is the right tool for a question. Writes are
not: every one of them composes the operations it means and hands them to
`Ctx.commit`, which applies them to the state and projects what came back.

Two things follow, and they are the reason the writes look the way they do.
Nothing in this file writes a ledger table — `Store/Project.lean` does, from a
change it was given. And the rules an operation enforces are enforced once, in
`Core/Apply.lean`, so `Txns.put` still cannot persist an unbalanced transaction
and no longer has to know why.
-/

open Lean SQLite

namespace Resources

/-! ## Row shapes -/

private structure AccountRow where
  id : String
  name : String
  kind : String
  ownerId : Option String
  commodity : Option String
  iban : Option String
  note : Option String
  closedOn : Option String
  realmId : Option String
  deriving Row

private structure PartyRow where
  id : String
  name : String
  iban : Option String
  email : Option String
  note : Option String
  kind : String
  realmId : String
  deriving Row

private structure LabelRow where
  id : String
  name : String
  colour : Option String
  realmId : String
  deriving Row

private structure TxnRow where
  id : String
  date : String
  payee : Option String
  narration : String
  state : String
  source : String
  deriving Row

private structure PostingRow where
  txnId : String
  accountId : String
  minor : Int64
  commodity : String
  partyId : Option String
  note : Option String
  origin : Option String
  tag : Option String
  deriving Row

private structure PairRow where
  a : String
  b : String
  deriving Row

private structure BalanceRow where
  account : String
  commodity : String
  minor : Int64
  deriving Row

/-- Renders a list of ids as a SQL `IN (...)` list, or `(NULL)` when empty. -/
private def inList (xs : Array String) : String :=
  if xs.isEmpty then "(NULL)"
  else "(" ++ String.intercalate ", " (xs.toList.map Db.lit) ++ ")"

/-! ## Accounts -/

namespace Accounts

private def ofRow (r : AccountRow) : Account :=
  { id := ⟨r.id⟩
    name := r.name
    kind := (AccountKind.ofString? r.kind).getD .expense
    owner := ⟨r.ownerId.getD Party.selfId.val⟩
    commodity := r.commodity.map Commodity.ofCode
    iban := r.iban
    note := r.note
    closedOn := r.closedOn.bind Date.ofIso?
    realm := ⟨r.realmId.getD Realm.selfId.val⟩ }

private def selectCols : String :=
  "SELECT id, name, kind, owner_id, commodity, iban, note, closed_on, realm_id FROM account"

/-- Every account, ordered by name. -/
def list (ctx : Ctx) (includeClosed : Bool := true) : IO (Array Account) := do
  let whereClause := if includeClosed then "" else " WHERE closed_on IS NULL"
  let rs ← Db.rows AccountRow ctx.db (selectCols ++ whereClause ++ " ORDER BY name")
  return rs.map ofRow

/--
Looks up an account by its exact dotted name, inside one realm.

A realm is a set of accounts one group of people may write, and a name is
something any of them may take — so which account a name means is a question
that only has an answer inside a realm.
-/
def byName? (ctx : Ctx) (name : String) (realm : RealmId := Realm.selfId) :
    IO (Option Account) := do
  let r ← Db.row? AccountRow ctx.db (selectCols ++
    s!" WHERE name = {Db.lit name} AND realm_id = {Db.lit realm.val} ORDER BY id")
  return r.map ofRow

/-- Looks up an account by id. -/
def byId? (ctx : Ctx) (id : AccountId) : IO (Option Account) := do
  let r ← Db.row? AccountRow ctx.db (selectCols ++ s!" WHERE id = {Db.lit id.val}")
  return r.map ofRow

/-- Guesses the kind from the top-level path component, the way ledger tools do. -/
def kindOfName (name : String) : AccountKind :=
  match (Account.components name).head? with
  | some "Assets" => .asset
  | some "Liabilities" => .liability
  | some "Equity" => .equity
  | some "Budget" => .equity
  | some "Income" => .income
  | _ => .expense

/-- Inserts an account. -/
def insert (ctx : Ctx) (a : Account) : IO Unit :=
  discard <| ctx.commit "system" [.putAccount a]

/--
Updates the mutable fields of an account.

The owner is said twice on purpose. Putting an account keeps the owner it has —
retagging somebody's account by mentioning its name in passing is exactly the
confusion an owner exists to prevent — so an edit that really does hand it over
has to say so out loud, which is the second operation.
-/
def update (ctx : Ctx) (a : Account) : IO Unit :=
  discard <| ctx.commit "system" [.putAccount a, .setAccountOwner a.id a.owner]

/--
Returns the account with this name, creating it (and its kind) if absent.

A new account belongs to you unless told otherwise. An account that already
exists keeps the owner it has: retagging somebody's account by mentioning its
name in passing is exactly the confusion an owner exists to prevent.
-/
def ensure (ctx : Ctx) (name : String) (kind : Option AccountKind := none)
    (owner : Option PartyId := none) (realm : RealmId := Realm.selfId) : IO Account := do
  match ← byName? ctx name realm with
  | some a => return a
  | none =>
    let a : Account :=
      { id := ⟨← freshId⟩, name, kind := kind.getD (kindOfName name)
        owner := owner.getD Party.selfId, realm }
    discard <| ctx.commit "system" [.putAccount a] (realm := realm)
    return a

/-- The account name a person's own money lives in. -/
def purseName (person : String) : String :=
  if person.startsWith "Assets." then person else "Assets.Purse." ++ person

/--
Somebody's purse: the one account of theirs this ledger keeps.

It is an ordinary asset, and it is theirs, which is the whole arrangement. Its
balance is what passes between you: positive, they owe you; negative, you owe
them. Nothing about it belongs in your net worth, and nothing has to remember to
exclude it, because the owner already says so.
-/
def purse (ctx : Ctx) (p : Party) : IO Account :=
  ensure ctx (purseName p.name) (some .asset) (some p.id)

/-- Hands an account to somebody else, or takes it back. -/
def setOwner (ctx : Ctx) (id : AccountId) (owner : PartyId) : IO Unit :=
  discard <| ctx.commit "system" [.setAccountOwner id owner]

/--
Rebooks every posting from one account into another and removes the emptied
account. Balance is untouched: each posting keeps its amount and only changes
which account it lands in.
-/
def mergeInto (ctx : Ctx) (from_ into : AccountId) (actor : String) : IO Nat := do
  -- Counted before the commit, because afterwards there is no account to count
  -- the postings of. A rule that filed things into the emptied account is
  -- repointed by the operation itself, and arrives here as a change like any
  -- other.
  let before ← ctx.state.get
  let moved := (before.txnsSorted.filter (fun t => t.postings.any (·.account == from_))).length
  discard <| ctx.commit actor [.mergeAccounts from_ into] (kind := "move")
  return moved

/-- Deletes an account. Fails if postings still reference it. -/
def delete (ctx : Ctx) (id : AccountId) : IO Unit :=
  discard <| ctx.commit "system" [.deleteAccount id]

end Accounts

/-! ## Labels and parties -/

namespace Labels

private def ofRow (r : LabelRow) : Label :=
  { id := ⟨r.id⟩, name := r.name, colour := r.colour, realm := ⟨r.realmId⟩ }

/-- Every label. -/
def list (ctx : Ctx) : IO (Array Label) := do
  let rs ← Db.rows LabelRow ctx.db "SELECT id, name, colour, realm_id FROM label ORDER BY name"
  return rs.map ofRow

/--
Looks up a label by name inside one realm.

A name is shared vocabulary and a realm is who shares it. Two realms may both
have a label called `groceries` and they are not the same label — `deleteLabel`
strips one from the transactions of its own realm, and a lookup that crossed
realms would find the other realm's and hand it to a part that may not name it.
-/
def byName? (ctx : Ctx) (name : String) (realm : RealmId := Realm.selfId) :
    IO (Option Label) := do
  let r ← Db.row? LabelRow ctx.db
    s!"SELECT id, name, colour, realm_id FROM label
       WHERE name = {Db.lit name} AND realm_id = {Db.lit realm.val} ORDER BY id"
  return r.map ofRow

/-- Returns the label of this name in this realm, creating it there if absent. -/
def ensure (ctx : Ctx) (name : String) (realm : RealmId := Realm.selfId) : IO Label := do
  match ← byName? ctx name realm with
  | some l => return l
  | none =>
    let l : Label := { id := ⟨← freshId⟩, name, realm }
    discard <| ctx.commit "system" [.putLabel l] (realm := realm)
    return l

/-- Deletes a label, and strips it from every transaction of its realm carrying it. -/
def delete (ctx : Ctx) (id : LabelId) : IO Unit := do
  let st ← ctx.state.get
  let realm := ((st.label? id).map (·.realm)).getD Realm.selfId
  discard <| ctx.commit "system" [.deleteLabel id] (kind := "categorise") (realm := realm)

end Labels

namespace Parties

private def ofRow (r : PartyRow) : Party :=
  { id := ⟨r.id⟩, name := r.name, iban := r.iban, email := r.email, note := r.note
    kind := r.kind, realm := ⟨r.realmId⟩ }

/-- Every party. -/
def list (ctx : Ctx) : IO (Array Party) := do
  let rs ← Db.rows PartyRow ctx.db
    "SELECT id, name, iban, email, note, kind, realm_id FROM party ORDER BY name"
  return rs.map ofRow

/-- Looks up a party by name inside one realm: two realms may know two Annas. -/
def byName? (ctx : Ctx) (name : String) (realm : RealmId := Realm.selfId) :
    IO (Option Party) := do
  let r ← Db.row? PartyRow ctx.db
    s!"SELECT id, name, iban, email, note, kind, realm_id FROM party
       WHERE name = {Db.lit name} AND realm_id = {Db.lit realm.val} ORDER BY id"
  return r.map ofRow

/-- Looks up a party by id. -/
def byId? (ctx : Ctx) (id : PartyId) : IO (Option Party) := do
  let r ← Db.row? PartyRow ctx.db
    s!"SELECT id, name, iban, email, note, kind, realm_id FROM party
       WHERE id = {Db.lit id.val}"
  return r.map ofRow

/--
Returns the party with this name, creating it if absent.

New parties default to `merchant`, because the overwhelming caller is an
importer turning a payee string into a party. Anything you create on purpose
should say `contact`.
-/
def ensure (ctx : Ctx) (name : String) (kind : String := "merchant")
    (realm : RealmId := Realm.selfId) : IO Party := do
  match ← byName? ctx name realm with
  | some p => return p
  | none =>
    let p : Party := { id := ⟨← freshId⟩, name, kind, realm }
    discard <| ctx.commit "system" [.putParty p] (realm := realm)
    return p

/--
You: the party every account belongs to unless it says otherwise.

Created if it is somehow missing, at the fixed id the migration backfilled with,
so the invariant "every account has an owner and most of them have this one"
holds even against a database that has been edited by hand.
-/
def self (ctx : Ctx) : IO Party := do
  match ← byId? ctx Party.selfId with
  | some p => return p
  | none =>
    let p : Party := { id := Party.selfId, name := "me", kind := "self" }
    discard <| ctx.commit "system" [.putParty p]
    return p

/-- Updates a party. -/
def update (ctx : Ctx) (p : Party) : IO Unit :=
  discard <| ctx.commit "system" [.putParty p]

/--
The person of this name, as somebody you deal with on purpose.

`ensure` defaults to `merchant` because its overwhelming caller is an importer
turning a payee string into a party. Anybody who can own an account, be sent a
realm invite, or owe you money is a contact, and saying so here keeps them out of
the thousand names a bank export produces.
-/
def contact (ctx : Ctx) (name : String) : IO Party := do
  let trimmed := name.trimAscii.toString
  if trimmed.isEmpty then return ← self ctx
  let p ← ensure ctx trimmed "contact"
  if p.kind == "merchant" then
    update ctx { p with kind := "contact" }
    return { p with kind := "contact" }
  return p

end Parties

/-! ## Groups

The set of people a cost gets shared with, saved under a name. Nothing here is
clever; it exists so that splitting a weekend's worth of receipts is one command
per weekend rather than one per receipt.
-/

private structure GroupRow where
  name : String
  members : String
  realmId : String
  deriving Row

namespace Groups

private def ofRow (r : GroupRow) : PartyGroup :=
  { name := r.name, members := (r.members.splitOn ",").filter (fun m => !m.isEmpty)
    realm := ⟨r.realmId⟩ }

/-- Every saved group. -/
def list (ctx : Ctx) : IO (Array PartyGroup) := do
  return (← Db.rows GroupRow ctx.db
    "SELECT name, members, realm_id FROM party_group ORDER BY name").map ofRow

/-- Looks a group up by name. -/
def byName? (ctx : Ctx) (name : String) : IO (Option PartyGroup) := do
  return (← Db.row? GroupRow ctx.db
    s!"SELECT name, members, realm_id FROM party_group WHERE name = {Db.lit name}").map ofRow

/-- Saves a group, replacing any existing one of that name. -/
def save (ctx : Ctx) (name : String) (members : List String) : IO PartyGroup := do
  if members.isEmpty then throw <| IO.userError "a group needs at least one member"
  for m in members do
    discard <| Parties.ensure ctx m
  let g : PartyGroup := { name, members }
  discard <| ctx.commit "system" [.putGroup g]
  return g

/-- Deletes a group. The people and what they owe are untouched. -/
def delete (ctx : Ctx) (name : String) : IO Unit :=
  discard <| ctx.commit "system" [.deleteGroup name]

end Groups


/-! ## Transactions -/

namespace Txns

/-- Loads the postings, labels and attachments for a set of transaction ids. -/
private def hydrate (ctx : Ctx) (heads : Array TxnRow) : IO (Array Transaction) := do
  if heads.isEmpty then return #[]
  let ids := heads.map (·.id)
  -- `posting_all` deliberately: loading a transaction must show what it says,
  -- including a pending one. It is *summing* that has to exclude pendings, and
  -- the `posting` view is what every balance goes through.
  let postings ← Db.rows PostingRow ctx.db
    s!"SELECT txn_id, account_id, minor, commodity, party_id, note, origin, tag FROM posting_all
       WHERE txn_id IN {inList ids} ORDER BY txn_id, idx"
  let labels ← Db.rows PairRow ctx.db
    s!"SELECT txn_id, label_id FROM txn_label WHERE txn_id IN {inList ids} ORDER BY txn_id, idx"
  let attachments ← Db.rows PairRow ctx.db
    s!"SELECT txn_id, sha256 FROM txn_attachment WHERE txn_id IN {inList ids} ORDER BY txn_id, idx"
  return heads.map fun h =>
    { id := ⟨h.id⟩
      date := (Date.ofIso? h.date).getD default
      payee := h.payee
      narration := h.narration
      state := (TxnState.ofString? h.state).getD .posted
      source := Provenance.decode h.source
      postings := postings.toList.filterMap fun p =>
        if p.txnId == h.id then
          some { account := ⟨p.accountId⟩
                 amount := ⟨Commodity.ofCode p.commodity, p.minor.toInt⟩
                 party := p.partyId.map (⟨·⟩)
                 note := p.note
                 origin := p.origin
                 tag := p.tag }
        else none
      labels := labels.toList.filterMap fun l => if l.a == h.id then some ⟨l.b⟩ else none
      attachments := attachments.toList.filterMap fun a => if a.a == h.id then some a.b else none }

private def headCols : String :=
  "SELECT t.id, t.date, t.payee, t.narration, t.state, t.source FROM txn t"

/-- The `WHERE` fragment restricting a query to one state, or to all of them. -/
private def stateCond : Option TxnState → String
  | some st => s!"t.state = {Db.lit st.toString} AND "
  | none => ""

/-- Fetches one transaction. -/
def get? (ctx : Ctx) (id : TxId) : IO (Option Transaction) := do
  let heads ← Db.rows TxnRow ctx.db (headCols ++ s!" WHERE t.id = {Db.lit id.val}")
  return (← hydrate ctx heads)[0]?

/--
Fetches transactions matching a filter, in the requested order.

Only posted transactions, unless another state is asked for by name. A claim
that has not been performed is not part of the ledger, and every caller that
wants one wants *only* those, so the default is the safe one and the interesting
case has to say what it means.
-/
def list (ctx : Ctx) (f : Filter) (s : Filter.SortSpec := {}) (limit : Nat := 100)
    (offset : Nat := 0) (state : Option TxnState := some .posted) : IO (Array Transaction) := do
  let sql := headCols ++ " WHERE " ++ stateCond state ++ f.toSql ++ " " ++ s.toSql ++
    s!" LIMIT {limit} OFFSET {offset}"
  let heads ← Db.rows TxnRow ctx.db sql
  hydrate ctx heads

/-- Counts transactions matching a filter. -/
def count (ctx : Ctx) (f : Filter) (state : Option TxnState := some .posted) : IO Int :=
  Db.scalarInt ctx.db s!"SELECT COUNT(*) FROM txn t WHERE {stateCond state}{f.toSql}"

/--
Writes a transaction, inserting or replacing, and records a revision.

The `Balanced` proof carried by the argument is the reason no unbalanced
transaction can reach the database, and it is checked a second time by the
operation this becomes: the proof travels with the value, the check travels with
the write, and neither is trusted on the other's behalf.
-/
def put (ctx : Ctx) (t : { t : Transaction // t.Balanced }) (actor : String)
    (kind : String := "write") : IO Unit :=
  discard <| ctx.commit actor [.putTransaction t.val] (kind := kind)

/-- Deletes a transaction, leaving its revision history behind. -/
def delete (ctx : Ctx) (id : TxId) (actor : String) : IO Unit :=
  discard <| ctx.commit actor [.deleteTransaction id] (kind := "delete")

/-!
### Claiming

An outlay somebody else will bear is not an expense of yours — it is their
spending, which happened to leave your account. Moving it into their purse says
exactly that, and because the purse belongs to them the balance is what passes
between you: positive, they owe you; negative, you owe them.

The same operation handles the repayment: an incoming reimbursement has its
counter leg moved to the same purse, which brings the balance back towards zero.
So laying out and being repaid are one verb.
-/

/--
Moves the counter legs of several transactions into one account, creating it if
it does not exist.

This is the general operation; `claim` is the same thing aimed at a receivable.
Gathering spending into an account of its own is what makes it billable as a
unit: the account is the container, the invoice is the document about it.
-/
def moveMany (ctx : Ctx) (ids : Array TxId) (into : String) (actor : String)
    (funding : Bool := false) : IO (Array Transaction) := do
  let target ← Accounts.ensure ctx into
  let accounts ← Accounts.list ctx
  -- Which leg the money came out of, for whoever paid. Deliberately blind to
  -- the owner: a friend's bank account funds a shared cost exactly the way
  -- yours does, and redirecting *their* bank leg into your budget would be
  -- rewriting a payment that was never yours to rewrite.
  let onSheet := (accounts.filter Account.holdsMoney).map (·.id)
  let mut out : Array Transaction := #[]
  for id in ids do
    let some t ← get? ctx id | continue
    -- `funding` moves the side the money came *from* instead of what it was
    -- spent on. That turns the target into a pot the costs were drawn against:
    -- its balance is what is still to be settled, and paying into it clears it.
    let moved : Transaction :=
      { t with postings := t.postings.map fun p =>
          if onSheet.contains p.account == funding then { p with account := target.id } else p }
    if moved.postings == t.postings then continue
    match moved.validate with
    | .error e => throw <| IO.userError s!"moving {id.val} would not balance: {e}"
    | .ok bt =>
      put ctx bt actor "move"
      out := out.push bt.val
  return out

/-- Moves every leg that is not on a money-holding account into `into`. -/
def claim (ctx : Ctx) (ids : Array TxId) (into : String) (actor : String) :
    IO (Array Transaction) := do
  let target ← Accounts.ensure ctx into
  let accounts ← Accounts.list ctx
  let onSheet := (accounts.filter Account.holdsMoney).map (·.id)
  let mut out : Array Transaction := #[]
  for id in ids do
    let some t ← get? ctx id | continue
    -- Only the counter legs move; the bank side stays where the money was.
    let moved : Transaction :=
      { t with postings := t.postings.map fun p =>
          if onSheet.contains p.account then p else { p with account := target.id } }
    if moved.postings == t.postings then continue
    match moved.validate with
    | .error e => throw <| IO.userError s!"claiming {id.val} would not balance: {e}"
    | .ok bt =>
      put ctx bt actor "claim"
      out := out.push bt.val
  return out

/--
Splits a transaction between the people who share it.

Every leg that is not on a funding account is divided with `splitParts`, so the
shares add back to exactly what was paid — `splitParts_sum` is the reason no
cent can go missing here. Each leg is split separately, which keeps a card fee
tagged as a fee inside every share rather than smearing it into the principal.

`keepShare` says whether you bear a share yourself, or fronted the whole thing
for other people.
-/
def split (ctx : Ctx) (id : TxId) (among : List String) (keepShare : Bool)
    (actor : String) : IO Transaction := do
  if among.isEmpty then throw <| IO.userError "say who to split this with"
  -- The purses first: the operation divides between accounts, and it has no way
  -- to create one for somebody it has never heard of.
  let mut targets : List AccountId := []
  for who in among do
    let person ← Parties.contact ctx who
    targets := targets ++ [(← Accounts.purse ctx person).id]
  let changes ← ctx.commit actor [.splitTransaction id targets keepShare] (kind := "split")
  match (Change.written changes)[0]? with
  | some divided => return divided
  | none => throw <| IO.userError s!"no such transaction: {id.val}"

/-- Splits several transactions the same way, and reports what each became. -/
def splitAll (ctx : Ctx) (ids : Array TxId) (among : List String) (keepShare : Bool)
    (actor : String) : IO (Array Transaction) := do
  let mut out : Array Transaction := #[]
  for id in ids do
    out := out.push (← split ctx id among keepShare actor)
  return out

/-! ### Merging and unmerging -/

/--
Combines several transactions into one. Each source contributes its postings,
stamped with its own origin so the merge can be undone, and the originals are
deleted with their history recorded.

`cancelIn` names accounts whose postings should drop out afterwards — the
`Unclassified` legs that auto-balancing created on both halves of a transfer,
which cancel once the halves are in one transaction. The result is validated
either way, so a cancellation that does not actually cancel is refused rather
than silently unbalancing the ledger.
-/
def merge (ctx : Ctx) (ids : Array TxId) (actor : String) (payee : Option String := none)
    (narration : Option String := none) (cancelIn : List String := []) : IO Transaction := do
  if ids.size < 2 then
    throw <| IO.userError "merging needs at least two transactions"
  let newId ← freshId
  let mut cancel : List AccountId := []
  for name in cancelIn do
    match ← Accounts.byName? ctx name with
    | some acc => cancel := cancel ++ [acc.id]
    | none => pure ()
  -- Read before the commit: retiring a transaction resets the staged rows that
  -- point at it, and they have to be pointed at what it became instead.
  let staged ← Db.rows String ctx.db
    s!"SELECT id FROM staged_entry WHERE txn_id IN {inList (ids.map (·.val))}"
  let changes ← ctx.commit actor
    [.mergeTransactions ids.toList ⟨newId⟩ payee narration cancel]
    (kinds := fun t => if t.val == newId then some "merge" else some "merged-away")
  Db.exec ctx.db s!"UPDATE staged_entry SET state = 'promoted', txn_id = {Db.lit newId}
                    WHERE id IN {inList staged}"
  match (Change.written changes)[0]? with
  | some merged => return merged
  | none => throw <| IO.userError "merging needs at least two transactions"

/-- Splits a merged transaction back into one transaction per origin. -/
def unmerge (ctx : Ctx) (id : TxId) (actor : String) : IO (Array Transaction) := do
  let some t ← get? ctx id | throw <| IO.userError s!"no such transaction: {id.val}"
  let mut ids : List TxId := []
  for _ in t.origins do
    ids := ids ++ [⟨← freshId⟩]
  let changes ← ctx.commit actor [.unmergeTransaction id ids]
    (kinds := fun x => if x == id then some "unmerged-away" else some "unmerge")
  let parts := Change.written changes
  -- Each part takes back the bank line it came from, so the statement stays
  -- promoted rather than reverting to unimported.
  for (origin, part) in t.origins.zip parts.toList do
    Db.exec ctx.db s!"UPDATE staged_entry SET state = 'promoted', txn_id = {Db.lit part.id.val}
                      WHERE fingerprint = {Db.lit origin}"
  return parts

/--
Replaces one transaction with the parts it was divided into.

Dividing is not unmerging: the parts may book their spending wherever they
belong, which is the whole point, so what they own is allowed to differ from
what the original said. What may not differ is the funding. Together the parts
must take exactly what the original took, out of exactly the accounts it took it
from -- otherwise a division could quietly invent money, and the ledger would
still balance while being wrong.

The staged row that produced the original follows the first part, so the bank
line stays promoted rather than reverting to unimported.
-/
def replaceWith (ctx : Ctx) (id : TxId) (parts : List Transaction) (actor : String)
    (kind : String := "split") : IO (Array Transaction) := do
  let staged ← Db.rows String ctx.db
    s!"SELECT id FROM staged_entry WHERE txn_id = {Db.lit id.val}"
  let changes ← ctx.commit actor [.replaceTransaction id parts kind] (kind := kind)
    (kinds := fun x => if x == id then some s!"{kind}-away" else none)
  let written := Change.written changes
  match written[0]? with
  | some first =>
    Db.exec ctx.db s!"UPDATE staged_entry SET state = 'promoted', txn_id = {Db.lit first.id.val}
                      WHERE id IN {inList staged}"
  | none => pure ()
  return written

/-- One entry of a transaction's audit trail. -/
structure Revision where
  seq : Int
  stamp : String
  actor : String
  kind : String
  patch : String
  deriving Repr, ToJson

private structure RevisionRow where
  seq : Int64
  stamp : String
  actor : String
  kind : String
  patch : String
  deriving Row

/-- The audit trail of a transaction, oldest first. -/
def revisions (ctx : Ctx) (id : TxId) : IO (Array Revision) := do
  let rs ← Db.rows RevisionRow ctx.db
    s!"SELECT seq, at, actor, kind, patch FROM revision WHERE txn_id = {Db.lit id.val} ORDER BY seq"
  return rs.map fun r => { seq := r.seq.toInt, stamp := r.stamp, actor := r.actor, kind := r.kind,
                           patch := r.patch }

end Txns

/-! ## Balances -/

namespace Balances

/-- A balance of one commodity in one account. -/
structure Entry where
  account : String
  commodity : String
  minor : Int
  deriving Repr, ToJson

/-- Per-account balances, optionally as of a date. -/
def all (ctx : Ctx) (asOf : Option Date := none) : IO (Array Entry) := do
  let cond := match asOf with
    | some d => s!" WHERE t.date <= {Db.lit d.toIso}"
    | none => ""
  let rs ← Db.rows BalanceRow ctx.db
    s!"SELECT a.name, p.commodity, SUM(p.minor) FROM posting p
       JOIN account a ON a.id = p.account_id
       JOIN txn t ON t.id = p.txn_id{cond}
       GROUP BY a.name, p.commodity HAVING SUM(p.minor) != 0 ORDER BY a.name, p.commodity"
  return rs.map fun r => { account := r.account, commodity := r.commodity, minor := r.minor.toInt }

/-- The balance of one account subtree, per commodity. -/
def subtree (ctx : Ctx) (under : String) (asOf : Option Date := none) : IO (Array Entry) := do
  let entries ← all ctx asOf
  let inTree := entries.filter (fun e => Account.isUnder e.account under)
  let codes := inTree.map (·.commodity) |>.toList.eraseDups
  return codes.toArray.map fun c =>
    { account := under, commodity := c,
      minor := (inTree.filter (·.commodity == c)).foldl (fun acc e => acc + e.minor) 0 }

/--
What you are worth: your own money, plus what passes between you and everybody
else.

Two terms, because there are two things. Your own asset and liability accounts
are your money. Everything belonging to somebody else nets, across *all* of
their accounts, to the claim between you — their spending less what they put in
— and that claim is yours: positive, they owe you; negative, you owe them.

Summing their accounts by kind instead would be wrong the moment you keep any of
their books beyond a purse, because their expense account is not your asset and
their bank account is not your liability. It is the owner that makes the two
terms separable, and it is the reason `asset` was never able to mean `mine`.
-/
def netWorth (ctx : Ctx) (commodity : String := "EUR") : IO Int :=
  Db.scalarInt ctx.db
    s!"SELECT IFNULL(SUM(p.minor), 0) FROM posting p
       JOIN account a ON a.id = p.account_id
       WHERE p.commodity = {Db.lit commodity}
         AND (a.owner_id != {Db.lit Party.selfId.val}
              OR a.kind IN ('asset', 'liability'))"

/-- The trial balance: totals per commodity across every account. Should be all zeroes. -/
def trial (ctx : Ctx) : IO (Array Entry) := do
  let rs ← Db.rows BalanceRow ctx.db
    "SELECT 'TOTAL', p.commodity, SUM(p.minor) FROM posting p GROUP BY p.commodity"
  return rs.map fun r => { account := r.account, commodity := r.commodity, minor := r.minor.toInt }

/-- Monthly totals for an account subtree, for the cashflow report. -/
def monthly (ctx : Ctx) (under : String) (commodity : String) : IO (Array (String × Int)) := do
  let rs ← Db.rows BalanceRow ctx.db
    s!"SELECT substr(t.date, 1, 7), p.commodity, SUM(p.minor) FROM posting p
       JOIN account a ON a.id = p.account_id
       JOIN txn t ON t.id = p.txn_id
       WHERE p.commodity = {Db.lit commodity}
         AND (a.name = {Db.lit under} OR a.name LIKE {Db.lit (under ++ ".%")})
       GROUP BY substr(t.date, 1, 7) ORDER BY 1"
  return rs.map fun r => (r.account, r.minor.toInt)

end Balances

end Resources
