import Resources.Core.State

/-!
# Operations and events

An *operation* is one decision: put this account, split that payment, raise this
claim. It is data, not a procedure — which is what lets it be stored, replayed,
and later signed and sent to somebody else.

An operation carries everything it needs. The date it happens on, the
identifiers it will write under, the amounts: all of them are in the value,
because `applyOp` has no clock and no source of randomness, and replaying a log
has to give the same state every time.

An *event* is one author's set of parts, each part naming the realm it applies
in. Parts are independent: a reader who cannot decrypt one realm's part applies
the others and is not stuck, which is the whole reason the unit of sharing is a
part rather than an event. That is also why an invalid part is skipped rather
than failing its neighbours.

A *change* is what came out: the full new value of every entity an operation
touched, or the id of one it removed. The store projects changes into tables by
upsert and delete, and never has to work out what an operation implied.
-/

namespace Resources

/-- One operation, applied inside one realm. -/
inductive Op
  -- Structure
  /-- Records a realm. -/
  | createRealm (r : Realm)
  /-- Inserts or updates an account; an existing account keeps its owner and realm. -/
  | putAccount (a : Account)
  /-- Rebooks every posting from one account into another and removes the emptied one. -/
  | mergeAccounts (from_ into : AccountId)
  /-- Removes an account that no posting mentions any more. -/
  | deleteAccount (id : AccountId)
  /-- Names the members who may post into an account besides its realm's admins. -/
  | setAccountRights (id : AccountId) (posters : List MemberId)
  /-- Hands an account to somebody else, or takes it back. -/
  | setAccountOwner (id : AccountId) (owner : PartyId)
  /-- Inserts or updates a label. -/
  | putLabel (l : Label)
  /-- Removes a label, and strips it from every transaction carrying it. -/
  | deleteLabel (id : LabelId)
  /-- Inserts or updates a party. -/
  | putParty (p : Party)
  /-- Saves a named set of people to split costs with. -/
  | putGroup (g : PartyGroup)
  /-- Removes a group. The people and what they owe are untouched. -/
  | deleteGroup (name : String)
  /-- Inserts or updates a trip. -/
  | putTrip (t : Trip)
  /-- Removes a trip. Its label and the transactions it grouped are left alone. -/
  | deleteTrip (name : String)
  /-- Inserts or updates a categorisation rule. -/
  | putRule (r : Rule)
  /-- Removes a rule by id or by name. -/
  | deleteRule (idOrName : String)
  -- Transactions
  /-- Writes a transaction. The postings are this realm's legs only. -/
  | putTransaction (t : Transaction)
  /-- Removes a transaction. -/
  | deleteTransaction (id : TxId)
  -- Arithmetic intents
  /-- Divides every non-funding leg between the targets, and you if `keepShare`. -/
  | splitTransaction (id : TxId) (targets : List AccountId) (keepShare : Bool)
  /-- Combines several transactions into one, stamped so the merge can be undone. -/
  | mergeTransactions (ids : List TxId) (newId : TxId) (payee narration : Option String)
      (cancelIn : List AccountId)
  /-- Splits a merged transaction back into one transaction per origin. -/
  | unmergeTransaction (id : TxId) (newIds : List TxId)
  /-- Replaces a transaction with the parts it was divided into. -/
  | replaceTransaction (id : TxId) (parts : List Transaction) (kind : String)
  /-- Divides a payment by the lines printed on its receipt. `ItemGroup.into` is an account id. -/
  | divideByItems (id : TxId) (groups : List Receipts.ItemGroup) (newIds : List TxId)
  -- Claims
  /-- Raises a claim: a pending transaction with two tagged legs. -/
  | raiseClaim (t : Transaction)
  /-- Meets a claim against the transaction that performed it. `splitId` names a part payment. -/
  | resolveClaim (id actual : TxId) (splitId : TxId)
  /-- Retires a claim that will never be performed, optionally writing the loss off. -/
  | voidClaim (id : TxId) (writeOff : Option (AccountId × TxId × Date))
  -- Budgets
  /-- Opens a budget and the equity account that holds it. -/
  | openBudget (b : Budget) (account : Account)
  /-- Names who a budget is divided among. -/
  | setParticipants (budget : BudgetId) (among : List Participant)
  /-- Records a cost somebody paid for directly into a budget. -/
  | contribute (budget : BudgetId) (t : Transaction)
  /-- Divides what a budget holds among the participants and raises the claims. -/
  | allocate (budget : BudgetId) (among : List Participant) (commodity : Commodity) (date : Date)
      (hub : Option PartyId) (txnId : TxId) (claimIds : List TxId) (labelId : LabelId)
  /-- Raises the claims that square everybody up. -/
  | settle (budget : BudgetId) (commodity : Commodity) (hub : Option PartyId) (due : Date)
      (claimIds : List TxId) (labelId : LabelId)
  /-- Divides the remainder and closes the budget. -/
  | closeBudget (budget : BudgetId) (among : Option (List Participant)) (commodity : Commodity)
      (hub : Option PartyId) (date : Date) (txnId : TxId) (claimIds : List TxId) (labelId : LabelId)
  /-- Reopens a closed budget. -/
  | reopenBudget (budget : BudgetId)
  /-- Removes a budget. -/
  | deleteBudget (budget : BudgetId)
  /--
  Takes a cost of a budget: says that it was yours to bear.

  For yourself and nobody else -- the author of the part is who the claim is
  recorded against -- and only while the budget is open. Several people taking
  one cost is that cost split equally between them; a cost nobody takes is
  divided among the participants by weight, which is what a budget did before
  anybody could take anything.
  -/
  | claimCost (budget : BudgetId) (txn : TxId)
  /--
  Gives a cost back: your own, or -- for an admin of the budget's realm --
  anybody's, because somebody has to be able to correct a list people filled in
  themselves.
  -/
  | releaseCost (budget : BudgetId) (txn : TxId) (member : MemberId)
  -- Invoices
  /-- Issues an invoice; its number comes from the counters inside `applyOp`. -/
  | issueInvoice (inv : Invoice) (sources : List TxId)
  /-- Moves an invoice to a new status. -/
  | setInvoiceStatus (id : InvoiceId) (status : InvoiceStatus)
  /-- Marks an invoice paid and records which transaction settled it. -/
  | settleInvoice (id : InvoiceId) (txn : TxId)
  /-- Deletes an invoice, winding the year's counter back when it held the last number. -/
  | deleteInvoice (id : InvoiceId)
  -- Attachments
  /-- Records a stored file's metadata. -/
  | registerBlob (file : Attachment)
  /-- Links a receipt to a transaction. -/
  | attach (txn : TxId) (sha : String)
  /-- Unlinks a receipt from a transaction. -/
  | detach (txn : TxId) (sha : String)
  /-- Stores what was read off a receipt, replacing whatever was read before. -/
  | recordExtraction (sha : String) (e : Extracted)
  /-- Replaces the lines printed on a receipt. -/
  | setReceiptLines (sha : String) (items : List LineItem)
  /-- Forgets a stored file nothing points at any more. -/
  | forgetBlob (sha : String)
  -- Import
  /-- Records one run of an importer over one file. -/
  | recordImportBatch (b : ImportBatch)
  -- Members and realms
  /-- Records an identity. -/
  | addMember (m : Member)
  /-- Removes an identity. -/
  | removeMember (id : MemberId)
  /-- Lets a member into a realm, with the bridge account their balance lives in. -/
  | grant (realm : RealmId) (member : MemberId) (role : RealmRole) (bridge : Account)
  /-- Puts a member out of a realm and bumps its key generation. -/
  | revoke (realm : RealmId) (member : MemberId)
  /-- Changes what a member may do in a realm. -/
  | setRole (realm : RealmId) (member : MemberId) (role : RealmRole)
  /-- Bumps a realm's key generation. -/
  | rotateRealmKey (realm : RealmId)
  /--
  Shows a realm an account that is not its own, so legs on it can be written in
  parts of that realm.

  The account travels with it because the realm being shown it has never heard
  of it: a reader folding this realm's history has to come away knowing what the
  account is called, what kind it is and whose it is, or the legs that follow
  name an id and nothing more. Nothing about the account moves — it stays
  written in the realm it was written in, and its owner stays its owner.
  -/
  | showAccount (realm : RealmId) (account : Account)
  /-- Stops showing one. Sight is taken away forwards: what was read stays read. -/
  | hideAccount (realm : RealmId) (account : AccountId)
  -- Genesis
  /--
  The whole state a log starts from.

  Never applied by `applyOp`, which refuses it wherever it appears. It is read
  by `Core.replay` off the *first* event of a log and nowhere else, because
  "nothing has happened yet" is a fact about where a reader stands in the order
  and not about what it has managed to fold.
  -/
  | snapshot (s : State)
  -- Paying a claim
  /--
  Pays a claim in one step: writes the payment between the claim's own two
  accounts, for exactly what it asked, and settles the claim with it.

  Either of the two members whose purses the claim names may do this, as may an
  admin of the realm. The amount is the claim's, so none of them can invent a
  payment — only perform one that has already been asked for.
  -/
  | payClaim (claim : TxId) (payment : TxId) (date : Date)

/-! ## Who may perform an operation

Every operation has a rule, and `Op.rights` is a total function that says which,
so a constructor cannot be added without somebody deciding who may use it. The
rule is the *baseline*: it is checked by `checkRights` at the top of `applyOp`,
before any of the state is read for effect, and the operations that need more —
post rights on the legs they write, the member a claim was raised for, the
member who registered a receipt — check that in their own case, against the same
realm and the same author.
-/

/-- The baseline right an operation needs, before anything else it asks for. -/
inductive Rights
  /-- The author has to be a member of this ledger; the realm is the one being made. -/
  | known
  /--
  An admin of the part's realm, or the author speaking about themselves alone.

  Three operations have this door and all three are the same situation:
  somebody who joined through an invite, whose admin was a link in a browser
  rather than a node composing events. `addMember` writes their own record,
  `grant` attests their own viewer role, and `putParty` revises the party record
  their own spending lands on — the one entity a member owns outright, and the
  reason they may revise it from any realm they are in. Nothing else goes
  through it.
  -/
  | attest
  /-- Any member of the part's realm. -/
  | member
  /-- An admin of the part's realm. -/
  | admin
  deriving DecidableEq, Repr, Inhabited

/--
Who may perform each operation.

The shape of the table is the decision: anything that changes who may read or
write — realms, members, accounts and the rights on them — is an admin's; so is
anything realm-wide that nothing else can undo, which is why the shared
vocabulary (labels, parties, groups, trips, rules, batches) and every budget and
invoice verb are admin's too. What a member may do on their own is write
transactions, and every one of those is checked leg by leg against `canPostLeg`
afterwards.
-/
def Op.rights : Op → Rights
  -- Structure
  --
  -- `known` rather than `admin`, and deliberately not "the part's own realm":
  -- a realm is created by somebody who is not yet in it, so there is no realm to
  -- be an admin of and no key the part could have been written under but the one
  -- it names in passing. What that leaves is squatting — a member who may write
  -- in any realm you read can put a realm record naming themselves its sole admin
  -- into your state, and creation is first-write-wins, so the honest creation of
  -- that id is refused in your state afterwards.
  --
  -- It buys nothing else, and that is new. Every entity now carries the realm it
  -- was written in, and every `.admin` rule is about the *part's* realm, so a
  -- realm you were handed by a stranger reaches no entry of yours: not a label,
  -- not a party, not a receipt, not an invoice and not an invoice counter. The
  -- grant path refuses a realm your state does not already record an admin for,
  -- so one cannot be pushed at a node either. The cost of the remaining hole is a
  -- name; the cost of closing it here would be a realm nobody could create.
  | .createRealm _ => .known
  | .putAccount _ | .mergeAccounts _ _ | .deleteAccount _ | .setAccountRights _ _
  | .setAccountOwner _ _ => .admin
  | .putLabel _ | .deleteLabel _ | .putGroup _ | .deleteGroup _
  | .putTrip _ | .deleteTrip _ | .putRule _ | .deleteRule _ => .admin
  | .putParty _ => .attest
  -- Transactions
  | .putTransaction _ | .deleteTransaction _ | .splitTransaction .. | .mergeTransactions ..
  | .unmergeTransaction .. | .replaceTransaction .. | .divideByItems .. => .member
  -- Claims
  | .raiseClaim _ => .admin
  | .resolveClaim .. | .voidClaim .. | .payClaim .. => .member
  -- Budgets
  | .openBudget .. | .setParticipants .. | .contribute .. | .allocate .. | .settle ..
  | .closeBudget .. | .reopenBudget _ | .deleteBudget _ => .admin
  -- Taking a cost and giving it back are what everybody in the realm is there to
  -- do, and `applyOp` checks that they take it for themselves.
  | .claimCost .. | .releaseCost .. => .member
  -- Invoices
  | .issueInvoice .. | .setInvoiceStatus .. | .settleInvoice .. | .deleteInvoice _ => .admin
  -- Attachments
  | .registerBlob _ | .attach .. | .detach .. | .recordExtraction .. | .setReceiptLines .. =>
      .member
  | .forgetBlob _ => .admin
  -- Import
  | .recordImportBatch _ => .admin
  -- Members and realms
  | .addMember _ | .grant .. => .attest
  | .removeMember _ | .revoke .. | .setRole .. | .rotateRealmKey _ => .admin
  -- What a realm may see is the realm's own business, so an admin of it decides.
  -- Whether the account was the author's to show is a second question, asked in
  -- `applyOp` by whoever is in a position to answer it.
  | .showAccount .. | .hideAccount .. => .admin
  -- Genesis. Never consulted: `checkRights` refuses a snapshot before it reads
  -- this table, because where a snapshot may be applied is a fact about the
  -- reader's position in the log rather than about who wrote it. The strictest
  -- rule there is stands here so that the table stays total and says nothing
  -- weaker than the refusal.
  | .snapshot _ => .admin

/-! ## Bounds

Everything an operation carries is bounded, because a reader applies what an
author sends it and a list whose length the author chose is a list that can be
made to exhaust memory. The numbers are generous for anything a person does and
small enough that the worst an event can cost is bounded by its own size.
-/

/-- The most postings one transaction may carry. -/
def maxPostings : Nat := 200

/-- The most people a budget may be divided among. -/
def maxParticipants : Nat := 100

/-- The most lines one receipt may print. -/
def maxLines : Nat := 500

/-- The largest count a receipt line, or a share of one, may claim. -/
def maxQty : Nat := 100000

/-- The largest weight a participant's share may carry. -/
def maxWeight : Nat := 10000

/--
The most claims one budget may carry.

One per person per cost, and a budget holds costs and people in numbers a person
chose; this is what a long trip between a large group honestly comes to, and it
bounds the fold a division does over them.
-/
def maxClaims : Nat := 2000

/-- The longest an identifier or a name may be. -/
def maxIdLength : Nat := 200

/-- The longest a narration, a note or a description may be. -/
def maxTextLength : Nat := 2000

/-- The most parts any other list an operation carries may have. -/
def maxParts : Nat := 100000

/-! ### Bounds on the three numbers nothing else bounds

A list's length is bounded above because a reader has to allocate it. These
three are bounded because a reader has to *compute* with them, and each of them
is a number whose type says nothing at all.

`Date` is Std's `PlainDate`, whose year is an `Int`: month and day are bounded by
their own types and by the proof a `PlainDate` carries, so a year is the only
part of a date that can be absurd. Six digits either side of zero is four times
the age of the universe in one direction and long past any invoice in the other.

`Commodity.exponent` is how many decimal places its minor unit has, and
`Commodity.scale` is `10 ^ exponent`. An exponent of ten million is six bytes on
the wire and a bignum with three million digits in memory, so this is the bound
that matters most. Eighteen is the most decimal places a currency has ever had
and the most that fits in the integer widths a port will use.

`Amount.minor` is a count of those units. Below `2 ^ 63` is what a port can hold
in the signed 64-bit integer its database column is, and far above the largest
sum of money there is.

`checkBounds` refuses an operation that carries a number outside these, and
`Wellformed` refuses bytes that decode to one — the same two doors every other
bound here is behind.
-/

/-- The earliest year a date may name. -/
def minYear : Int := -999999

/-- The latest year a date may name. -/
def maxYear : Int := 999999

/-- The most decimal places a commodity's minor unit may have. -/
def maxExponent : Nat := 18

/-- The largest magnitude, exclusive, a count of minor units may have. -/
def maxMinor : Nat := 2 ^ 63

/-- Whether a date names a year the ledger will take; its month and day are its type's own. -/
def Date.inRange (d : Date) : Bool := minYear ≤ (d.year : Int) && (d.year : Int) ≤ maxYear

/-- Whether an optional date is in range. Nothing is in range. -/
def Date.inRange? (d : Option Date) : Bool := d.all Date.inRange

/-- Whether a commodity's minor unit is one arithmetic can be done in. -/
def Commodity.inRange (c : Commodity) : Bool := c.exponent ≤ maxExponent

/-- Whether an amount is one this format carries: a usable unit and a 64-bit count. -/
def Amount.inRange (a : Amount) : Bool := a.commodity.inRange && a.minor.natAbs < maxMinor

/-- Whether every date and every amount a filter compares against is in range. -/
def Filter.inRange : Filter → Bool
  | .dateFrom d | .dateTo d => d.inRange
  | .amountFrom a | .amountTo a => a.inRange
  | .and a b | .or a b => a.inRange && b.inRange
  | .not a => a.inRange
  | _ => true

/-- One realm's share of an event. -/
structure Part where
  realm : RealmId
  op : Op

/-- One author's set of parts, applied together. -/
structure Event where
  id : String
  author : MemberId
  /-- When it was composed, for display only: nothing in `Core` reads it. -/
  composedAt : String
  /-- How many events the author had seen, for ordering later. -/
  basedOn : Nat := 0
  parts : List Part

namespace Event

/--
The state this event is the genesis of, when it is one.

Genesis is a *position*, not a permission: an event whose whole content is one
snapshot is what a log starts from, and it counts as genesis only when it is the
first event of the fold — `Core.replay` is where that is decided. Anywhere else
it is an ordinary event whose one part `applyOp` refuses, which is a no-op.

"Exactly one part, and that part a snapshot" is the whole test. An event with a
snapshot beside something else is not a beginning: the something else would have
to apply either before or after a state that replaced everything, and neither
reading is one two implementations would agree on.
-/
def genesis? (e : Event) : Option State :=
  match e.parts with
  | [{ realm := _, op := .snapshot g }] => some g
  | _ => none

end Event

/-- What an op changed, for the store to project into SQL. -/
inductive Change
  /-- A realm, in full. -/
  | realm (r : Realm)
  /-- A member, in full. -/
  | member (m : Member)
  /-- A member that is gone. -/
  | memberDeleted (id : MemberId)
  /-- An account, in full. -/
  | account (a : Account)
  /-- An account that is gone. -/
  | accountDeleted (id : AccountId)
  /-- A label, in full. -/
  | label (l : Label)
  /-- A label that is gone. -/
  | labelDeleted (id : LabelId)
  /-- A party, in full. -/
  | party (p : Party)
  /-- A group, in full. -/
  | group (g : PartyGroup)
  /-- A group that is gone. -/
  | groupDeleted (name : String)
  /-- A trip, in full. -/
  | trip (t : Trip)
  /-- A trip that is gone. -/
  | tripDeleted (name : String)
  /-- A rule, in full. -/
  | rule (r : Rule)
  /-- A rule that is gone. -/
  | ruleDeleted (id : RuleId)
  /-- A transaction, in full, including every rewrite an intent implied. -/
  | txn (t : Transaction)
  /-- A transaction that is gone. -/
  | txnDeleted (id : TxId)
  /-- A budget and its participants. -/
  | budget (b : BudgetState)
  /-- A budget that is gone. -/
  | budgetDeleted (id : BudgetId)
  /-- An invoice and what it bills for. -/
  | invoice (i : InvoiceState)
  /-- An invoice that is gone. -/
  | invoiceDeleted (id : InvoiceId)
  /-- A stored file, what was read off it and the lines it prints. -/
  | blob (b : BlobState)
  /-- A stored file that is gone. -/
  | blobDeleted (sha : String)
  /-- An import batch. -/
  | batch (b : ImportBatch)
  /-- A counter's new value. -/
  | counter (name : String) (value : Int)
  /-- An import fingerprint that is now spoken for. -/
  | fingerprint (fp : String)

end Resources
