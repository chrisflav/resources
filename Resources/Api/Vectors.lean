import Resources.Core.Apply
import Resources.Core.Encode

/-!
# Conformance vectors

What an operation means is decided in one place — `applyOp` — and checked in one
place, and a port of this ledger is neither. The browser client, or any other
implementation of the same wire format, cannot be verified; what it can do is
answer the same questions this core answers, byte for byte, and be compared.

A vector is one such question: a state the ledger can actually reach, an event
applied to it, and the state `step` produced, all three in the canonical bytes of
`Core/Encode.lean`, together with the hash a checkpoint would commit to, the
changes the store projects, and the parts `applyOp` refused. A port passes when
it reproduces those bytes. This is the only bridge between the verified semantics
and an unverified port, which is why it ships with the core and is versioned with
the wire format rather than with the client.

Everything here is fixed. Identifiers are literals, dates are literals, and
nothing consults `freshId` or `Date.today`, so generating the vectors twice
writes the same bytes twice.

The input states are built by applying earlier operations with `applyOp`, never
by assembling a `State` by hand — a vector starting from a state no sequence of
operations produces would ask a port to reproduce something that cannot happen.
Two lists say whether that held: `setupErrors` is empty exactly when every
fixture applied, and `misfits` is empty exactly when every scenario was refused
where it says it is refused and nowhere else.
-/

namespace Resources
namespace Api
namespace Vectors

/-! ## What a vector is -/

/-- One scenario: a reachable state, and the event applied to it. -/
structure Scenario where
  /-- A stable name, which is also the event's id. -/
  name : String
  /-- What the scenario is for, in one sentence. -/
  description : String
  /-- Whether at least one part of the event is meant to be refused. -/
  refused : Bool := false
  /-- The state the event is applied to. -/
  state : State
  /-- The event. -/
  event : Event

/-- One vector, in the shape `vectors.json` holds it. -/
structure Case where
  /-- The scenario's name. -/
  name : String
  /-- The scenario's description. -/
  description : String
  /-- The canonical bytes of the input state, in hex. -/
  stateHex : String
  /-- The canonical bytes of the event, in hex. -/
  eventHex : String
  /-- The canonical bytes of the state `step` produced, in hex. -/
  expectedHex : String
  /-- `Encode.hashState` of that state: what a checkpoint would commit to. -/
  expectedHash : String
  /-- The constructor name and entity id of every change, in order. -/
  changes : List (String × String)
  /-- The indices of the parts `applyOp` refused, which `step` skipped. -/
  rejected : List Nat

/-! ## Reading a change

A change carries a whole entity, and a vector reports only what it is and which
entity it is about — enough for a port to say it made the same decisions, and
not so much that the summary becomes a second encoding to keep in step.
-/

/-- The constructor name of a change. -/
def changeKind : Change → String
  | .realm _ => "realm"
  | .member _ => "member"
  | .memberDeleted _ => "memberDeleted"
  | .account _ => "account"
  | .accountDeleted _ => "accountDeleted"
  | .label _ => "label"
  | .labelDeleted _ => "labelDeleted"
  | .party _ => "party"
  | .group _ => "group"
  | .groupDeleted _ => "groupDeleted"
  | .trip _ => "trip"
  | .tripDeleted _ => "tripDeleted"
  | .rule _ => "rule"
  | .ruleDeleted _ => "ruleDeleted"
  | .txn _ => "txn"
  | .txnDeleted _ => "txnDeleted"
  | .budget _ => "budget"
  | .budgetDeleted _ => "budgetDeleted"
  | .invoice _ => "invoice"
  | .invoiceDeleted _ => "invoiceDeleted"
  | .blob _ => "blob"
  | .blobDeleted _ => "blobDeleted"
  | .batch _ => "batch"
  | .counter _ _ => "counter"
  | .fingerprint _ => "fingerprint"

/--
The key the entity is held under: an id for most, a name for groups and trips,
a content hash for a stored file, and the value itself for a fingerprint.
-/
def changeId : Change → String
  | .realm r => r.id.val
  | .member m => m.id.val
  | .memberDeleted i => i.val
  | .account a => a.id.val
  | .accountDeleted i => i.val
  | .label l => l.id.val
  | .labelDeleted i => i.val
  | .party p => p.id.val
  | .group g => g.name
  | .groupDeleted n => n
  | .trip t => t.name
  | .tripDeleted n => n
  | .rule r => r.id.val
  | .ruleDeleted i => i.val
  | .txn t => t.id.val
  | .txnDeleted i => i.val
  | .budget b => b.budget.id.val
  | .budgetDeleted i => i.val
  | .invoice i => i.invoice.id.val
  | .invoiceDeleted i => i.val
  | .blob b => b.file.sha256
  | .blobDeleted sha => sha
  | .batch b => b.id.val
  | .counter name _ => name
  | .fingerprint fp => fp

/-! ## Hex

`toHex` is in `Util`; the inverse is here rather than imported, because the one
that exists lives in `Sync` and `Api` does not depend on `Sync`.
-/

/-- The nibble a hex digit stands for. -/
private def nibble? (c : Char) : Option Nat :=
  let n := c.toNat
  if n ≥ 48 && n ≤ 57 then some (n - 48)
  else if n ≥ 97 && n ≤ 102 then some (n - 97 + 10)
  else none

/-- Reads a lowercase hex string back into bytes: the inverse of `toHex`. -/
def ofHex? (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.empty
  for k in [0:cs.size / 2] do
    let some hi := nibble? cs[2 * k]! | return none
    let some lo := nibble? cs[2 * k + 1]! | return none
    out := out.push (((hi <<< 4) ||| lo).toUInt8)
  return some out

/-! ## Building a state

Every fixture is a chain of operations from `State.init`, applied as the member
the ledger belongs to. The chain is an `Except`, so an operation that would be
refused makes the whole fixture an error rather than silently leaving the state
one step short of what the vectors below assume.
-/

/-- Applies operations in order, as one member inside one realm. -/
private def afterAs (author : MemberId) (realm : RealmId) (start : Except String State)
    (ops : List Op) : Except String State := do
  let mut st ← start
  for op in ops do
    let (next, _) ← applyOp st author realm op
    st := next
  return st

/-- Applies operations in order, as the self member in the self realm. -/
private def after (start : Except String State) (ops : List Op) : Except String State :=
  afterAs Member.selfId Realm.selfId start ops

/-- Applies operations in order, as the self member inside another realm. -/
private def afterIn (realm : RealmId) (start : Except String State) (ops : List Op) :
    Except String State := afterAs Member.selfId realm start ops

/-- The state a fixture reached, or the empty ledger if it did not reach one. -/
private def stateOf (s : Except String State) : State := s.toOption.getD State.init

/-! ## The values the fixtures are made of -/

/-- The euro, which every vector counts in. -/
private def eur : Commodity := Commodity.eur

/-- A date, from its ISO form. -/
private def iso (s : String) : Date := (Date.ofIso? s).getD default

/-- The day the vectors happen on. -/
private def day : Date := iso "2026-03-01"

/-- The earliest date any vector mentions. -/
private def dayEarly : Date := iso "2000-01-01"

/-- The latest date any vector mentions. -/
private def dayLate : Date := iso "2099-12-31"

/--
A year a million years hence: one past `maxYear`, and the ISO parser will not
write it, so it is built from its three numbers instead.
-/
private def dayImpossible : Date := (Date.ofTriple (maxYear + 1, 1, 1)).getD day

/-- A commodity with one more decimal place than `maxExponent` allows. -/
private def tooManyPlaces : Commodity := { code := "XXX", exponent := maxExponent + 1 }

/-- When the events were composed. Nothing in `Core` reads it. -/
private def stamp : String := "2026-03-01T00:00:00Z"

/-- An account. -/
private def acc (id name : String) (kind : AccountKind) (owner : PartyId := Party.selfId) :
    Account := { id := ⟨id⟩, name, kind, owner }

/-- A euro posting, by account id. -/
private def cents (account : String) (minor : Int) : Posting :=
  { account := ⟨account⟩, amount := ⟨eur, minor⟩ }

/-- A dated transaction. -/
private def txn (id : String) (postings : List Posting) (narration : String := "dinner") :
    Transaction := { id := ⟨id⟩, date := day, narration, postings }

/-- One event by the member the ledger belongs to, one part per operation, all in your realm. -/
private def ev (name : String) (ops : List Op) : Event :=
  { id := "ev-" ++ name, author := Member.selfId, composedAt := stamp
    parts := ops.map fun op => { realm := Realm.selfId, op } }

/-! ## The scenario constructors -/

/-- A scenario with one part, which applies. -/
private def one (name description : String) (s : Except String State) (op : Op) : Scenario :=
  { name, description, state := stateOf s, event := ev name [op] }

/-- A scenario with one part, which is refused. -/
private def refuses (name description : String) (s : Except String State) (op : Op) : Scenario :=
  { name, description, refused := true, state := stateOf s, event := ev name [op] }

/-- A scenario with several parts. -/
private def parts (name description : String) (s : Except String State) (ops : List Op)
    (refused : Bool := false) : Scenario :=
  { name, description, refused, state := stateOf s, event := ev name ops }

/-- A scenario whose event another member composed. -/
private def asMember (name description : String) (author : MemberId) (s : Except String State)
    (op : Op) (refused : Bool := false) : Scenario :=
  { name, description, refused, state := stateOf s, event := { ev name [op] with author } }

/-- A scenario whose one part names a realm other than yours. -/
private def inRealm (name description : String) (realm : RealmId) (s : Except String State)
    (op : Op) (refused : Bool := false) : Scenario :=
  { name, description, refused, state := stateOf s
    event := { ev name [] with parts := [{ realm, op }] } }

/-- A scenario another member composed, in a realm of its own. -/
private def asMemberIn (name description : String) (author : MemberId) (realm : RealmId)
    (s : Except String State) (op : Op) (refused : Bool := false) : Scenario :=
  { name, description, refused, state := stateOf s
    event := { ev name [] with author, parts := [{ realm, op }] } }

/-! ## The fixtures

Each of these is a state the vectors below start from, and each was reached by
applying the operations of the one above it.
-/

/-- People, accounts, labels and a second member: what everything else starts from. -/
private def base : Except String State := after (.ok State.init)
  [ .putParty { id := Party.selfId, name := "me", kind := "self" }
  , .putParty { id := ⟨"party-anna"⟩, name := "Anna", kind := "contact" }
  , .putParty { id := ⟨"party-bob"⟩, name := "Bob", kind := "contact" }
  , .addMember { id := ⟨"mara"⟩, name := "Mara", party := ⟨"party-mara"⟩ }
  , .putAccount (acc "acc-bank" "Assets.Bank" .asset)
  , .putAccount (acc "acc-food" "Expenses.Food" .expense)
  , .putAccount (acc "acc-unc" "Income.Unclassified" .income)
  , .putAccount (acc "acc-loss" "Expenses.Loss" .expense)
  , .putAccount (acc "acc-spare" "Expenses.Spare" .expense)
  , .putAccount (acc "acc-anna" "Assets.Purse.Anna" .asset ⟨"party-anna"⟩)
  , .putAccount (acc "acc-bob" "Assets.Purse.Bob" .asset ⟨"party-bob"⟩)
  , .putAccount { acc "acc-old" "Assets.Shoebox" .asset with closedOn := some day }
  , .putLabel { id := ⟨"lbl-hut"⟩, name := "budget:Hut" }
  , .putLabel { id := ⟨"lbl-cabin"⟩, name := "budget:Cabin" } ]

/-- The transaction most of the transaction vectors are about. -/
private def dinner : Transaction :=
  txn "t-dinner" [cents "acc-bank" (-10000), cents "acc-food" 10000]

/-- A dinner, paid for. -/
private def spent : Except String State := after base [.putTransaction dinner]

/-- One cent, so a split of it has a share for nobody. -/
private def tiny : Except String State :=
  after base [.putTransaction (txn "t-tiny" [cents "acc-bank" (-1), cents "acc-food" 1] "a cent")]

/-- A purchase and the card fee the bank posted beside it. -/
private def twoTxns : Except String State := after base
  [ .putTransaction (txn "t-a" [cents "acc-bank" (-10000), cents "acc-food" 10000])
  , .putTransaction (txn "t-b" [cents "acc-bank" (-250), cents "acc-food" 250] "card fee") ]

/-- The two of them, combined. -/
private def merged : Except String State :=
  after twoTxns [.mergeTransactions [⟨"t-a"⟩, ⟨"t-b"⟩] ⟨"t-m"⟩ none none []]

/-- A bank line, carrying the fingerprint that dedupes it. -/
private def imported : Except String State := after base
  [.putTransaction { txn "t-imp" [cents "acc-bank" (-2500), cents "acc-food" 2500] "groceries" with
     source := .imported ⟨"bat-1"⟩ "fp-1" }]

/-- A transaction carrying a label, so deleting the label has something to strip it from. -/
private def labelled : Except String State := after base
  [.putTransaction { txn "t-lab" [cents "acc-bank" (-3000), cents "acc-food" 3000] "the hut" with
     labels := [⟨"lbl-hut"⟩] }]

/-- A saved set of people. -/
private def grouped : Except String State :=
  after base [.putGroup { name := "flat", members := ["Anna", "Bob"] }]

/-- A trip, spanning the two dates at the ends of what a `Date` can hold. -/
private def tripped : Except String State := after base
  [.putTrip { id := "trp-zin", name := "Zinalrothorn", starts := dayEarly, ends := dayLate
              payer := "party-anna", note := some "hut booked" }]

/-- A categorisation rule, with a filter that nests. -/
private def ruled : Except String State := after base
  [.putRule { id := ⟨"rul-1"⟩, name := "groceries", filterSrc := "payee:REWE"
              filter := .and (.account "Assets") (.not (.label "private"))
              setAccount := some "acc-food", addLabels := ["food", "weekly"]
              setParty := none, priority := -3 }]

/-- A claim: five thousand she has not paid yet. -/
private def claim : Transaction :=
  { id := ⟨"t-claim"⟩, date := day, narration := "her share", state := .pending
    postings := [cents "acc-bank" 5000, cents "acc-anna" (-5000)] }

/-- The claim, outstanding. -/
private def claimed : Except String State := after base [.raiseClaim claim]

/-- Two thousand of it, arrived. -/
private def partPaid : Except String State := after claimed
  [.putTransaction (txn "t-paid" [cents "acc-bank" 2000, cents "acc-unc" (-2000)] "on account")]

/-- All of it, arrived. -/
private def fullPaid : Except String State := after claimed
  [.putTransaction (txn "t-full" [cents "acc-bank" 5000, cents "acc-unc" (-5000)] "settled up")]

/-- And met: the claim is settled, stamped, and asks for nothing more. -/
private def resolved : Except String State :=
  after fullPaid [.resolveClaim ⟨"t-claim"⟩ ⟨"t-full"⟩ ⟨"t-claim-part"⟩]

/-- The receipt the divide-by-items vectors read their lines off. -/
private def receipt : Attachment :=
  { sha256 := "rcpt", mime := "image/jpeg", bytes := 8192, origName := some "till.jpg"
    createdAt := "2026-03-01T10:00:00" }

/-- What was read off it: one line, and one line covering six units. -/
private def extracted : Extracted :=
  { merchant := some "REWE", date := some day, total := some ⟨eur, 12000⟩
    items := [{ description := "bread", qty := none, amount := ⟨eur, 500⟩ }
            , { description := "rolls", qty := some 6, amount := ⟨eur, 3000⟩ }]
    rawText := "REWE\nbread 5.00\n6 rolls 30.00", extractor := "test" }

/-- The payment the receipt belongs to, and the stored file, with nothing linking them yet. -/
private def blobbed : Except String State := after base
  [ .registerBlob receipt
  , .putTransaction (txn "t-shop" [cents "acc-bank" (-12000), cents "acc-food" 12000]
      "the weekly shop") ]

/--
The same receipt, sealed again under another realm's key.

A file is registered in the realm it was scanned in and attached in whichever
realm the payment lives in, which need not be the same one. The bytes do not
move and the hash the ledger calls the file does not change; what changes is
where the ciphertext is kept and which key opens it, and those are the two
fields a second registration is allowed to speak about.
-/
private def rewrapped : Attachment :=
  { receipt with
      cipherHash := some "5f2b1c3d4e5a69788796a5b4c3d2e1f0f1e2d3c4b5a69788796a5b4c3d2e1f00"
      wrappedKey := some "realm-flat:1:AAECAwQFBgcICQoLDA0ODw==" }

/-- The receipt, attached and read. -/
private def receipted : Except String State :=
  after blobbed [.attach ⟨"t-shop"⟩ "rcpt", .recordExtraction "rcpt" extracted]

/--
The same payment, divided once: two of the six rolls are hers.

Both parts hang on the same receipt and neither paid for all of it, so each
carries the lines it took -- hers the two rolls, the remainder the bread and the
four rolls left -- and a second division reads those rather than the page.
-/
private def divided : Except String State :=
  after receipted
    [.divideByItems ⟨"t-shop"⟩ [{ items := [{ line := 2, qty := some 2 }], into := "acc-anna" }]
      [⟨"t-d1"⟩, ⟨"t-d2"⟩]]

/-- The budget two people share. -/
private def hut : Budget :=
  { id := ⟨"b-hut"⟩, name := "Hut", note := some "a weekend", closed := false }

/-- You and Anna, equally. -/
private def among : List Participant :=
  [ { owner := Party.selfId, name := "me", account := "Expenses.Food" }
  , { owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna" } ]

/-- You and Anna, in a two-to-one split. -/
private def weighted : List Participant :=
  [ { owner := Party.selfId, name := "me", account := "Expenses.Food", weight := 2 }
  , { owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna", weight := 1 } ]

/-- A cost somebody paid for, straight into a budget. -/
private def cost (id from_ into : String) (minor : Int) (narration : String) : Transaction :=
  txn id [cents from_ (-minor), cents into minor] narration

/-- The budget, open and holding nothing. -/
private def budgetOpened : Except String State :=
  after base [.openBudget hut (acc "acc-hut" "Hut" .equity)]

/-- The budget, with the two of you named as sharing it. -/
private def budgetShared : Except String State :=
  after budgetOpened [.setParticipants ⟨"b-hut"⟩ among]

/-- Two costs, hers and yours. -/
private def budgetFunded : Except String State := after budgetShared
  [ .contribute ⟨"b-hut"⟩ (cost "t-hut1" "acc-bank" "acc-hut" 10000 "the hut")
  , .contribute ⟨"b-hut"⟩ (cost "t-hut2" "acc-anna" "acc-hut" 6000 "groceries") ]

/-- One of the two costs taken by the person who was there. -/
private def budgetTaken : Except String State := after budgetFunded
  [.claimCost ⟨"b-hut"⟩ ⟨"t-hut2"⟩]

/-- Both of them, divided, and the claim that squares them up raised. -/
private def budgetDivided : Except String State := after budgetFunded
  [.allocate ⟨"b-hut"⟩ among eur day none ⟨"t-alloc1"⟩ [⟨"t-claim1"⟩] ⟨"lbl-hut"⟩]

/-- A receipt that turned up after the division. -/
private def budgetLate : Except String State := after budgetDivided
  [.contribute ⟨"b-hut"⟩ (cost "t-hut3" "acc-bank" "acc-hut" 2000 "a late ticket")]

/-- The budget, closed with nothing left in it. -/
private def budgetClosed : Except String State := after budgetDivided
  [.closeBudget ⟨"b-hut"⟩ none eur none day ⟨"t-alloc9"⟩ [⟨"t-claim9"⟩] ⟨"lbl-hut"⟩]

/-- A budget three people share, so a settlement has a shape to choose. -/
private def cabin : Budget :=
  { id := ⟨"b-cabin"⟩, name := "Cabin", note := none, closed := false }

/-- You, Anna and Bob, equally. -/
private def three : List Participant :=
  [ { owner := Party.selfId, name := "me", account := "Expenses.Food" }
  , { owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna" }
  , { owner := ⟨"party-bob"⟩, name := "Bob", account := "Assets.Purse.Bob" } ]

/--
The three-way budget, open and shared.

The dinner is there so that the ledger has seen your bank account: a settlement
lands in the account of theirs a budget already moved money across, and you
fronted none of this one, so it falls back to the account of yours the ledger
sees most — and somebody the ledger has never seen move money cannot be settled
with at all.
-/
private def cabinShared : Except String State := after base
  [ .putTransaction dinner
  , .openBudget cabin (acc "acc-cabin" "Cabin" .equity)
  , .setParticipants ⟨"b-cabin"⟩ three ]

/-- Anna and Bob paid for everything; you paid for nothing. -/
private def cabinFunded : Except String State := after cabinShared
  [ .contribute ⟨"b-cabin"⟩ (cost "t-cab1" "acc-anna" "acc-cabin" 5000 "the cabin")
  , .contribute ⟨"b-cabin"⟩ (cost "t-cab2" "acc-bob" "acc-cabin" 4000 "the food") ]

/-- Divided three ways, and squared up by the shortest plan. -/
private def cabinDivided : Except String State := after cabinFunded
  [.allocate ⟨"b-cabin"⟩ three eur day none ⟨"t-calloc"⟩ [⟨"t-cc1"⟩, ⟨"t-cc2"⟩] ⟨"lbl-cabin"⟩]

/-- An invoice as it arrives at `issueInvoice`: unnumbered and unreferenced. -/
private def draft (id : String) : Invoice :=
  { id := ⟨id⟩, number := "", issued := day, due := day
    payerId := some ⟨"party-anna"⟩, payerName := "Anna", commodity := eur
    reference := "", status := .draft, note := some "her half", settledTxn := none
    payment := .epc "Christian Merten" "DE02120300000000202051" (some "GENODEF1XXX")
    sourceAccount := some "Expenses.Food", budgetId := none, pendingTxn := none
    lines := [{ description := "her share", qtyMilli := 1000, unitPrice := ⟨eur, 5000⟩
                taxBp := 1900 }] }

/-- The invoice, raised. -/
private def invoiced : Except String State :=
  after spent [.issueInvoice (draft "i1") [⟨"t-dinner"⟩]]

/-- The invoice, sent: she has seen the number, so it can no longer be deleted. -/
private def invoiceSent : Except String State :=
  after invoiced [.setInvoiceStatus ⟨"i1"⟩ .sent]

/-- An import batch, recorded. -/
private def batched : Except String State := after base
  [.recordImportBatch { id := ⟨"bat-1"⟩, profile := "dkb", filename := some "export.csv"
                        account := some ⟨"acc-bank"⟩, stamp := "2026-03-01T10:00:00"
                        total := 42, duplicates := 3 }]

/-- A second realm, which you administer. -/
private def realmTwo : Except String State := after base
  [.createRealm { id := ⟨"realm-flat"⟩, name := "flat", members := [(Member.selfId, .admin)]
                  generation := 0 }]

/-- Mara, let into it, with the purse she holds her balance in. -/
private def granted : Except String State := afterIn ⟨"realm-flat"⟩ realmTwo
  [.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer (acc "acc-mara" "Assets.Purse.Mara" .asset
    ⟨"party-mara"⟩)]

/-- Mara's purse in your own realm: a bridge you granted her here. -/
private def maraPurse : Account := acc "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩

/-- Nils's purse in your own realm. -/
private def nilsPurse : Account := acc "acc-nils" "Assets.Purse.Nils" .asset ⟨"party-nils"⟩

/--
Two members of your realm, each with a purse, and a claim between the two of
them: what paying a claim is about.
-/
private def bridged : Except String State := after base
  [ .addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ }
  , .grant Realm.selfId ⟨"mara"⟩ .viewer maraPurse
  , .grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse
  , .raiseClaim { id := ⟨"t-claim-m"⟩, date := day, narration := "her share"
                  state := .pending
                  postings := [cents "acc-nils" 5000, cents "acc-mara" (-5000)] } ]

/-- The claim, paid: what a second payment of it runs into. -/
private def claimPaid : Except String State :=
  after bridged [.payClaim ⟨"t-claim-m"⟩ ⟨"t-pay"⟩ day]

/-- The open budget, with Mara let into your realm and holding a purse of her own. -/
private def budgetWithMember : Except String State :=
  after budgetShared [.grant Realm.selfId ⟨"mara"⟩ .viewer maraPurse]

/-- The same, after the budget has been closed. -/
private def budgetShutWithMember : Except String State :=
  after budgetClosed [.grant Realm.selfId ⟨"mara"⟩ .viewer maraPurse]

/-- A refund: money that came back, so what is divided is a negative amount. -/
private def refunded : Except String State := after base
  [.putTransaction (txn "t-refund" [cents "acc-bank" 100, cents "acc-food" (-100)] "returned")]

/--
A cost with a discount on it: one leg into the budget, and a smaller one back out.

A division splits each cost by the kinds of leg it is made of, so the discount is
divided as a piece of its own — a negative amount, three ways, which is where
Euclidean division shows.
-/
private def budgetDiscounted : Except String State := after budgetShared
  [.contribute ⟨"b-hut"⟩ (txn "t-hut1"
    [ cents "acc-bank" (-9900), cents "acc-hut" 10000
    , { cents "acc-hut" (-100) with tag := some "discount" } ] "the hut")]

/-- Mara, a viewer of your own realm, holding the purse the grant opened for her. -/
private def viewing : Except String State :=
  after base [.grant Realm.selfId ⟨"mara"⟩ .viewer maraPurse]

/-- The same, with a payment of yours already in the books. -/
private def spentSeen : Except String State := after spent
  [.grant Realm.selfId ⟨"mara"⟩ .viewer maraPurse]

/-- An account that lives in the second realm, so this one may not rewrite it. -/
private def flatAccount : Except String State :=
  afterIn ⟨"realm-flat"⟩ realmTwo [.putAccount (acc "acc-flat" "Assets.Flat" .asset)]

/-- A receipt somebody else filed: what only they, or an admin, may speak about. -/
private def filedByMara : Except String State :=
  afterAs ⟨"mara"⟩ Realm.selfId viewing [.registerBlob receipt]

/-- The claim between the two purses, met. -/
private def claimMet : Except String State :=
  afterAs ⟨"nils"⟩ Realm.selfId bridged [.payClaim ⟨"t-claim-m"⟩ ⟨"t-pay"⟩ day]

/-! ### Fixtures for the realm rules

Every entity kind carries the realm it was written in, so the fixtures below are
the same entities written *somewhere else*: what a part in your realm may not
touch, and what a part in theirs may.
-/

/-- A label, a party, a group, a trip, a rule and an import batch, all in the second realm. -/
private def flatVocabulary : Except String State := afterIn ⟨"realm-flat"⟩ realmTwo
  [ .putLabel { id := ⟨"lbl-flat"⟩, name := "flat:rent" }
  , .putParty { id := ⟨"party-flat"⟩, name := "Landlord", kind := "contact" }
  , .putGroup { name := "flatmates", members := ["Anna"] }
  , .putTrip { id := "trp-flat", name := "Flat", starts := day, ends := day
               payer := "party-anna", note := none }
  , .putRule { id := ⟨"rul-flat"⟩, name := "rent", filterSrc := "", filter := .all
               setAccount := none, addLabels := [], setParty := none, priority := 0 }
  , .recordImportBatch { id := ⟨"bat-flat"⟩, profile := "dkb", filename := none
                         account := none, stamp := "", total := 0, duplicates := 0 } ]

/-- A receipt filed in the second realm. -/
private def flatReceipt : Except String State :=
  afterIn ⟨"realm-flat"⟩ realmTwo [.registerBlob receipt]

/-- Mara, a viewer of your realm, whose party was introduced there. -/
private def maraKnown : Except String State := viewing

/-- A purse already called `Members.Mara` in the second realm, before Mara self-grants. -/
private def flatNameTaken : Except String State := afterIn ⟨"realm-flat"⟩ realmTwo
  [.putAccount (acc "acc-taken" "Members.Mara" .asset)]

/-- A bridge account of a budget's name, squatted before the budget is opened. -/
private def potSquatted : Except String State := after base
  [ .addMember { id := ⟨"zed"⟩, name := "Zed", party := ⟨"party-zed"⟩ }
  , .grant Realm.selfId ⟨"zed"⟩ .viewer (acc "acc-squat" "Budget.Hut" .equity ⟨"party-zed"⟩) ]

/-- A plain equity account of a budget's name, which a budget may be held in. -/
private def potReady : Except String State := after base
  [.putAccount (acc "acc-pot" "Budget.Hut" .equity)]

/-- Mara's purse in your realm, and a budget she has a share of through it. -/
private def bridgeShare : Except String State := after budgetWithMember
  [.contribute ⟨"b-hut"⟩ (cost "t-hut1" "acc-bank" "acc-hut" 10000 "the hut")]

/-- A payment into the receiving purse, so the receiver has something to meet the claim with. -/
private def paidIn : Except String State := after bridged
  [.putTransaction (txn "t-in" [cents "acc-nils" 5000, cents "acc-unc" (-5000)] "paid")]

/-- An invoice issued in the second realm: a number that realm handed out. -/
private def flatInvoice : Except String State :=
  afterIn ⟨"realm-flat"⟩ realmTwo [.issueInvoice (draft "i-flat") []]

/--
A second person called Anna, introduced in the second realm.

`party-anna` sorts first, so the unscoped by-name lookup found her rather than
the one the part's realm knows.
-/
private def flatPayer : Except String State := afterIn ⟨"realm-flat"⟩ realmTwo
  [.putParty { id := ⟨"party-flat-anna"⟩, name := "Anna", kind := "contact" }]

/--
The three-way budget, funded by the other two, and an account of yours in a realm
that has nothing to do with it.

You fronted none of this budget, so the account you settle through is the one of
yours the ledger sees most — and the ledger saw every account of yours in every
realm a reader could open. Two entries in the second realm are enough to outrank
the one your bank account has here.
-/
private def cabinAbroad : Except String State :=
  afterIn ⟨"realm-flat"⟩ (after cabinFunded
    [.createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                    members := [(Member.selfId, .admin)], generation := 0 }])
  [ .putAccount (acc "acc-flat-bank" "Assets.Flat" .asset)
  , .putAccount (acc "acc-flat-food" "Expenses.Flat" .expense)
  , .putTransaction (txn "t-flat1" [cents "acc-flat-bank" (-2000), cents "acc-flat-food" 2000]
      "the flat's shopping")
  , .putTransaction (txn "t-flat2" [cents "acc-flat-bank" (-3000), cents "acc-flat-food" 3000]
      "and more of it") ]

/-- Every fixture, by name: what `setupErrors` reads. -/
private def fixtures : List (String × Except String State) :=
  [ ("base", base), ("spent", spent), ("tiny", tiny), ("twoTxns", twoTxns), ("merged", merged)
  , ("imported", imported), ("labelled", labelled), ("grouped", grouped), ("tripped", tripped)
  , ("ruled", ruled), ("claimed", claimed), ("partPaid", partPaid), ("fullPaid", fullPaid)
  , ("resolved", resolved)
  , ("blobbed", blobbed), ("receipted", receipted), ("divided", divided)
  , ("budgetOpened", budgetOpened)
  , ("budgetShared", budgetShared), ("budgetFunded", budgetFunded)
  , ("budgetTaken", budgetTaken)
  , ("budgetDivided", budgetDivided), ("budgetLate", budgetLate), ("budgetClosed", budgetClosed)
  , ("cabinShared", cabinShared), ("cabinFunded", cabinFunded), ("cabinDivided", cabinDivided)
  , ("invoiced", invoiced), ("invoiceSent", invoiceSent), ("batched", batched)
  , ("realmTwo", realmTwo), ("granted", granted)
  , ("bridged", bridged), ("claimPaid", claimPaid), ("budgetWithMember", budgetWithMember)
  , ("budgetShutWithMember", budgetShutWithMember), ("refunded", refunded)
  , ("budgetDiscounted", budgetDiscounted), ("viewing", viewing), ("spentSeen", spentSeen)
  , ("flatAccount", flatAccount), ("filedByMara", filedByMara), ("claimMet", claimMet)
  , ("flatVocabulary", flatVocabulary), ("flatReceipt", flatReceipt)
  , ("maraKnown", maraKnown), ("flatNameTaken", flatNameTaken)
  , ("potSquatted", potSquatted), ("potReady", potReady), ("bridgeShare", bridgeShare)
  , ("paidIn", paidIn), ("flatInvoice", flatInvoice), ("flatPayer", flatPayer)
  , ("cabinAbroad", cabinAbroad) ]

/-- The fixtures that did not apply, and what they were refused with. -/
def setupErrors : List String :=
  fixtures.filterMap fun (name, s) =>
    match s with
    | .error e => some s!"{name}: {e}"
    | .ok _ => none

/-! ## The scenarios

Grouped the way `Op` is grouped, so every constructor can be seen to be here.
-/

/-- Realms, accounts, people, labels, groups, trips and rules. -/
private def structureScenarios : List Scenario :=
  [ one "create-realm" "Records a second realm, with you as its admin." base
      (.createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                      members := [(Member.selfId, .admin)], generation := 0 })
  , one "put-account" "Adds an account, which lands in the realm the part names." base
      (.putAccount (acc "acc-new" "Expenses.Books" .expense))
  , one "put-account-keeps-the-owner"
      "Putting an account that exists again leaves its owner and realm alone." base
      (.putAccount (acc "acc-anna" "Assets.Purse.Anna" .asset))
  , inRealm "put-account-in-another-realm" "An account created inside a realm of its own."
      ⟨"realm-flat"⟩ realmTwo (.putAccount (acc "acc-flat" "Assets.Flat" .asset))
  , one "merge-accounts" "Rebooks every posting into another account and removes the emptied one."
      spent (.mergeAccounts ⟨"acc-food"⟩ ⟨"acc-spare"⟩)
  , one "delete-account" "Removes an account no posting mentions." base
      (.deleteAccount ⟨"acc-spare"⟩)
  , one "set-account-rights" "Names a second member as a poster on an account." base
      (.setAccountRights ⟨"acc-bank"⟩ [⟨"mara"⟩])
  , one "set-account-rights-to-nobody" "An empty list: the boundary case of a list field." base
      (.setAccountRights ⟨"acc-bank"⟩ [])
  , one "set-account-owner" "Hands an account to somebody else." base
      (.setAccountOwner ⟨"acc-food"⟩ ⟨"party-anna"⟩)
  , one "put-label" "Adds a label." base
      (.putLabel { id := ⟨"lbl-food"⟩, name := "food", colour := some "#ff8800" })
  , one "put-label-with-empty-strings" "Empty strings, which encode as a zero length." base
      (.putLabel { id := ⟨"lbl-blank"⟩, name := "", colour := some "" })
  , one "delete-label" "Removes a label, and strips it from the transaction carrying it." labelled
      (.deleteLabel ⟨"lbl-hut"⟩)
  , one "put-party" "Adds a counterparty." base
      (.putParty { id := ⟨"party-carl"⟩, name := "Carl", iban := some "DE89370400440532013000"
                   email := some "carl@example.org", note := none, kind := "contact" })
  , one "put-group" "Saves a named set of people to split costs with." base
      (.putGroup { name := "flat", members := ["Anna", "Bob"] })
  , one "delete-group" "Removes a group, leaving the people alone." grouped (.deleteGroup "flat")
  , one "put-trip" "A trip spanning the two ends of what a date can hold." base
      (.putTrip { id := "trp-zin", name := "Zinalrothorn", starts := dayEarly, ends := dayLate
                  payer := "party-anna", note := some "hut booked" })
  , one "delete-trip" "Removes a trip by name." tripped (.deleteTrip "Zinalrothorn")
  , one "put-rule" "A rule whose filter nests, so the recursive encoding is exercised." base
      (.putRule { id := ⟨"rul-1"⟩, name := "groceries", filterSrc := "payee:REWE"
                  filter := .and (.account "Assets") (.not (.label "private"))
                  setAccount := some "acc-food", addLabels := ["food", "weekly"]
                  setParty := none, priority := -3 })
  , one "put-rule-with-empty-lists" "Empty strings, an empty list and a negative priority." base
      (.putRule { id := ⟨"rul-bare"⟩, name := "", filterSrc := "", filter := .all
                  setAccount := none, addLabels := [], setParty := none, priority := -1 })
  , one "delete-rule" "Removes a rule by name." ruled (.deleteRule "groceries")
  , one "add-member" "Records another identity, and the party their spending lands on." base
      (.addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ })
  , asMember "member-introduces-themselves"
      "Somebody who joined through an invite writes their own member record, and the \
       party that comes with it." ⟨"nils"⟩ base
      (.addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ })
  , one "remove-member" "Removes an identity that is not the ledger's own." base
      (.removeMember ⟨"mara"⟩)
  , inRealm "grant" "Lets a member into a realm, with the purse they hold a balance in."
      ⟨"realm-flat"⟩ realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer
        (acc "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩))
  , inRealm "bridge-owner-is-the-members-party"
      "The purse a grant opens belongs to the member it is for, whatever the operation says."
      ⟨"realm-flat"⟩ realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer (acc "acc-mara" "Assets.Purse.Mara" .asset))
  , asMemberIn "member-self-grants-as-viewer"
      "A joiner attests the viewer grant the sequencer already holds for them." ⟨"mara"⟩
      ⟨"realm-flat"⟩ realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer
        (acc "acc-mara" "Assets.Purse.Mara" .asset ⟨"party-mara"⟩))
  , inRealm "set-role" "Changes what a member may do in a realm." ⟨"realm-flat"⟩ granted
      (.setRole ⟨"realm-flat"⟩ ⟨"mara"⟩ .admin)
  , inRealm "revoke" "Puts a member out, and bumps the realm's key generation."
      ⟨"realm-flat"⟩ granted (.revoke ⟨"realm-flat"⟩ ⟨"mara"⟩)
  , inRealm "rotate-realm-key" "Bumps a realm's key generation on its own." ⟨"realm-flat"⟩
      realmTwo (.rotateRealmKey ⟨"realm-flat"⟩)
  , one "record-import-batch" "Records one run of an importer over one file." base
      (.recordImportBatch { id := ⟨"bat-1"⟩, profile := "dkb", filename := some "export.csv"
                            account := some ⟨"acc-bank"⟩, stamp := "2026-03-01T10:00:00"
                            total := 42, duplicates := 3 })
  , refuses "refuses-a-snapshot-in-a-part"
      "A snapshot is where a log starts, not something a part may say — not even on a ledger \
       nothing has happened in. Where a log starts is a fact about the reader's position in \
       the order, and a reader holding one key generation folds nothing written under any \
       other, so a state that looks untouched part way along is not a beginning."
      (.ok State.init) (.snapshot (stateOf spent)) ]

/-- Writing transactions, and the arithmetic intents over them. -/
private def transactionScenarios : List Scenario :=
  [ one "put-transaction" "Writes a balanced transaction." base (.putTransaction dinner)
  , one "put-transaction-imported"
      "A transaction off a bank line, which spends its import fingerprint." base
      (.putTransaction { txn "t-imp" [cents "acc-bank" (-2500), cents "acc-food" 2500]
        "groceries" with source := .imported ⟨"bat-1"⟩ "fp-1" })
  , one "delete-transaction" "Removes a transaction." spent (.deleteTransaction ⟨"t-dinner"⟩)
  , one "split-three-ways"
      "Ten thousand between three people: the remainder goes out a cent at a time." spent
      (.splitTransaction ⟨"t-dinner"⟩ [⟨"acc-anna"⟩, ⟨"acc-bob"⟩] true)
  , one "split-one-cent-two-ways" "One cent between two people: one of them gets nothing." tiny
      (.splitTransaction ⟨"t-tiny"⟩ [⟨"acc-anna"⟩] true)
  , one "split-without-keeping-a-share" "The whole amount goes to the two of them." spent
      (.splitTransaction ⟨"t-dinner"⟩ [⟨"acc-anna"⟩, ⟨"acc-bob"⟩] false)
  , one "merge-transactions" "Combines a purchase with the fee the bank posted beside it." twoTxns
      (.mergeTransactions [⟨"t-a"⟩, ⟨"t-b"⟩] ⟨"t-m"⟩ (some "REWE") (some "the weekly shop") [])
  , one "unmerge-transaction" "Splits the merged transaction back into what it was built from."
      merged (.unmergeTransaction ⟨"t-m"⟩ [⟨"t-a2"⟩, ⟨"t-b2"⟩])
  , one "replace-transaction"
      "Divides a payment into parts that take exactly the money the original took." spent
      (.replaceTransaction ⟨"t-dinner"⟩
        [ txn "t-p1" [cents "acc-bank" (-6000), cents "acc-food" 6000]
        , txn "t-p2" [cents "acc-bank" (-4000), cents "acc-anna" 4000] ] "divide")
  , one "split-a-refund-three-ways"
      "A hundred cents back, between three: Euclidean division makes that -34, -33, -33."
      refunded (.splitTransaction ⟨"t-refund"⟩ [⟨"acc-anna"⟩, ⟨"acc-bob"⟩] true)
  , one "divide-by-items"
      "Two of the six units a line covers go to her; the rest stays behind." receipted
      (.divideByItems ⟨"t-shop"⟩ [{ items := [{ line := 2, qty := some 2 }], into := "acc-anna" }]
        [⟨"t-d1"⟩, ⟨"t-d2"⟩])
  , one "claim-a-cost" "Says a cost of a budget was yours to bear, rather than everybody's."
      budgetFunded (.claimCost ⟨"b-hut"⟩ ⟨"t-hut2"⟩)
  , one "release-a-cost" "And gives it back." budgetTaken
      (.releaseCost ⟨"b-hut"⟩ ⟨"t-hut2"⟩ Member.selfId)
  , one "divide-a-part-again"
      "A remainder is divided by the lines it was left with, numbered from one." divided
      (.divideByItems ⟨"t-d2"⟩ [{ items := [{ line := 1 }], into := "acc-anna" }]
        [⟨"t-e1"⟩, ⟨"t-e2"⟩]) ]

/-- Raising, meeting and retiring claims. -/
private def claimScenarios : List Scenario :=
  [ one "raise-claim" "A claim: a dated movement that is expected and has not happened." base
      (.raiseClaim claim)
  , one "resolve-claim-in-full" "The money arrived in full, so the claim is settled and stamped."
      fullPaid (.resolveClaim ⟨"t-claim"⟩ ⟨"t-full"⟩ ⟨"t-claim-part"⟩)
  , one "resolve-claim-in-part"
      "Two thousand of five: the part that was met becomes a record of its own." partPaid
      (.resolveClaim ⟨"t-claim"⟩ ⟨"t-paid"⟩ ⟨"t-claim-part"⟩)
  , one "void-claim" "Retires a claim that will never be performed." claimed
      (.voidClaim ⟨"t-claim"⟩ none)
  , one "void-claim-with-a-write-off" "The same, with the loss booked where it belongs." claimed
      (.voidClaim ⟨"t-claim"⟩ (some (⟨"acc-loss"⟩, ⟨"t-writeoff"⟩, day)))
  , asMember "pay-claim"
      "The member who is owed records the payment: the payment and the settlement in one."
      ⟨"nils"⟩ bridged (.payClaim ⟨"t-claim-m"⟩ ⟨"t-pay"⟩ day)
  , one "pay-claim-by-an-admin"
      "An admin of the realm the two purses sit in may record it too." bridged
      (.payClaim ⟨"t-claim-m"⟩ ⟨"t-pay"⟩ day)
  , asMember "refuses-paying-your-own-debt"
      "The member who owes a claim cannot write the receipt for it themselves."
      ⟨"mara"⟩ bridged (.payClaim ⟨"t-claim-m"⟩ ⟨"t-pay"⟩ day) true
  , refuses "refuses-paying-a-settled-claim"
      "A claim that has already been met cannot be paid again." claimPaid
      (.payClaim ⟨"t-claim-m"⟩ ⟨"t-pay2"⟩ day)
  , refuses "refuses-a-claim-with-three-legs"
      "A claim is exactly two legs: one account owes and one is owed." base
      (.raiseClaim { id := ⟨"t-three"⟩, date := day, narration := "three ways"
                     state := .pending
                     postings := [cents "acc-bank" 6000, cents "acc-anna" (-3000),
                                  cents "acc-bob" (-3000)] }) ]

/-- Opening, funding, dividing, settling and closing a budget. -/
private def budgetScenarios : List Scenario :=
  [ one "open-budget" "Opens a budget and the equity account that holds it." base
      (.openBudget hut (acc "acc-hut" "Hut" .equity))
  , one "set-participants" "Names who a budget is divided among." budgetOpened
      (.setParticipants ⟨"b-hut"⟩ among)
  , one "set-participants-to-nobody" "An empty list of participants." budgetOpened
      (.setParticipants ⟨"b-hut"⟩ [])
  , one "contribute" "Records a cost somebody paid for directly into a budget." budgetShared
      (.contribute ⟨"b-hut"⟩ (cost "t-hut1" "acc-bank" "acc-hut" 10000 "the hut"))
  , one "allocate-equally" "Divides sixteen thousand between two people and raises the claim."
      budgetFunded (.allocate ⟨"b-hut"⟩ among eur day none ⟨"t-alloc1"⟩ [⟨"t-claim1"⟩] ⟨"lbl-hut"⟩)
  , one "allocate-by-weight" "The same money, in a two-to-one split." budgetFunded
      (.allocate ⟨"b-hut"⟩ weighted eur day none ⟨"t-alloc2"⟩ [⟨"t-claim2"⟩] ⟨"lbl-hut"⟩)
  , one "allocate-tops-up-a-late-cost"
      "A receipt that turned up afterwards is divided on its own, topping each person up."
      budgetLate (.allocate ⟨"b-hut"⟩ among eur day none ⟨"t-alloc3"⟩ [⟨"t-claim3"⟩] ⟨"lbl-hut"⟩)
  , one "allocate-through-a-hub"
      "Three people, squared up through one of them instead of by the shortest plan." cabinFunded
      (.allocate ⟨"b-cabin"⟩ three eur day (some ⟨"party-anna"⟩) ⟨"t-calloc"⟩
        [⟨"t-cc1"⟩, ⟨"t-cc2"⟩] ⟨"lbl-cabin"⟩)
  , one "settle-through-a-hub"
      "Re-planning through a hub revises one claim, raises another and withdraws a third."
      cabinDivided (.settle ⟨"b-cabin"⟩ eur (some ⟨"party-anna"⟩) day [⟨"t-cc3"⟩, ⟨"t-cc4"⟩]
        ⟨"lbl-cabin"⟩)
  , one "close-budget" "Divides what is left and closes the budget." budgetLate
      (.closeBudget ⟨"b-hut"⟩ none eur none day ⟨"t-alloc4"⟩ [⟨"t-claim4"⟩] ⟨"lbl-hut"⟩)
  , one "allocate-a-negative-cost"
      "A discount, divided three ways: a negative amount, and the remainder goes the other way."
      budgetDiscounted (.allocate ⟨"b-hut"⟩ three eur day none ⟨"t-alloc8"⟩
        [⟨"t-claim8a"⟩, ⟨"t-claim8b"⟩] ⟨"lbl-hut"⟩)
  , one "reopen-budget" "Reopens it; every division already made stands." budgetClosed
      (.reopenBudget ⟨"b-hut"⟩)
  , one "delete-budget" "Removes a budget, leaving the transactions it touched alone." budgetShared
      (.deleteBudget ⟨"b-hut"⟩) ]

/-- Invoices, which are numbered inside `applyOp` rather than by the caller. -/
private def invoiceScenarios : List Scenario :=
  [ one "issue-invoice" "Numbers an invoice gaplessly and gives it a structured reference." spent
      (.issueInvoice (draft "i1") [⟨"t-dinner"⟩])
  , one "issue-invoice-for-an-unknown-payer"
      "A payer nobody knows yet is recorded as a party by the same operation." spent
      (.issueInvoice { draft "i2" with payerName := "Dora", payerId := some ⟨"party-dora"⟩ } [])
  , one "set-invoice-status" "Moves an invoice to a new status." invoiced
      (.setInvoiceStatus ⟨"i1"⟩ .sent)
  , one "settle-invoice" "Marks it paid, and records which transaction settled it." invoiced
      (.settleInvoice ⟨"i1"⟩ ⟨"t-dinner"⟩)
  , one "delete-invoice" "Deletes a draft, winding the year's counter back." invoiced
      (.deleteInvoice ⟨"i1"⟩) ]

/-- Stored files, what was read off them, and the lines they print. -/
private def receiptScenarios : List Scenario :=
  [ one "register-blob" "Records a stored file's metadata." base (.registerBlob receipt)
  , one "re-register-blob-with-a-wrap"
      "A file the ledger already knows, re-sealed under another realm: the ciphertext's hash \
       and the wrapped key are taken, and nothing else about it is."
      blobbed (.registerBlob rewrapped)
  , one "attach" "Links a receipt to a transaction." blobbed (.attach ⟨"t-shop"⟩ "rcpt")
  , one "detach" "Unlinks it again." receipted (.detach ⟨"t-shop"⟩ "rcpt")
  , one "record-extraction" "Stores what was read off a receipt." blobbed
      (.recordExtraction "rcpt" extracted)
  , one "set-receipt-lines" "Replaces the lines printed on it, short of the total." receipted
      (.setReceiptLines "rcpt"
        [ { description := "bread", qty := none, amount := ⟨eur, 500⟩ }
        , { description := "rolls", qty := some 6, amount := ⟨eur, 3000⟩ }
        , { description := "wine", qty := none, amount := ⟨eur, 2000⟩ } ])
  , one "forget-blob" "Forgets a stored file nothing points at." blobbed (.forgetBlob "rcpt") ]

/-- What `applyOp` refuses, and what a refused part does to the parts beside it. -/
private def refusalScenarios : List Scenario :=
  [ refuses "refuses-an-unbalanced-transaction" "A transaction whose postings do not sum to zero."
      base (.putTransaction (txn "t-bad" [cents "acc-bank" (-10000), cents "acc-food" 9000]))
  , refuses "refuses-a-closed-account" "A posting into an account that is closed." base
      (.putTransaction (txn "t-old" [cents "acc-old" (-10000), cents "acc-food" 10000]))
  , asMember "refuses-a-member-without-rights"
      "A second member, who administers nothing and was named on nothing." ⟨"mara"⟩ base
      (.putTransaction dinner) true
  , refuses "refuses-a-missing-transaction" "An operation naming something that is not there." base
      (.deleteTransaction ⟨"t-nobody"⟩)
  , refuses "refuses-a-duplicate-fingerprint" "A bank line that has already been imported." imported
      (.putTransaction { txn "t-imp2" [cents "acc-bank" (-2500), cents "acc-food" 2500]
        "groceries again" with source := .imported ⟨"bat-1"⟩ "fp-1" })
  , refuses "refuses-a-cost-on-a-closed-budget" "A closed budget takes no more costs." budgetClosed
      (.contribute ⟨"b-hut"⟩ (cost "t-hut8" "acc-bank" "acc-hut" 100 "one more"))
  , refuses "refuses-too-few-fresh-ids" "Unmerging into fewer ids than there are origins." merged
      (.unmergeTransaction ⟨"t-m"⟩ [⟨"t-a2"⟩])
  , refuses "refuses-a-settled-claim" "A claim that has already been met asks for nothing." resolved
      (.resolveClaim ⟨"t-claim"⟩ ⟨"t-full"⟩ ⟨"t-claim-again"⟩)
  , refuses "refuses-deleting-a-sent-invoice" "A number somebody has seen is voided, not deleted."
      invoiceSent (.deleteInvoice ⟨"i1"⟩)
  , refuses "refuses-an-account-merged-into-itself" "A merge that would empty and fill one account."
      base (.mergeAccounts ⟨"acc-food"⟩ ⟨"acc-food"⟩)
  , refuses "refuses-an-empty-group" "A group needs at least one member." base
      (.putGroup { name := "nobody", members := [] })
  , asMemberIn "refuses-a-grant-by-a-non-admin" "Only an admin of a realm may let somebody in."
      ⟨"mara"⟩ ⟨"realm-flat"⟩ realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .admin (acc "acc-mara" "Assets.Purse.Mara" .asset)) true
  , asMember "refuses-a-self-grant-as-admin"
      "What a member may attest about themselves is a view; an admin role is a takeover."
      ⟨"mara"⟩ base (.grant Realm.selfId ⟨"mara"⟩ .admin maraPurse) true
  , asMember "refuses-a-self-grant-for-somebody-else"
      "A member may speak for themselves. Letting a third person in is still an admin's decision."
      ⟨"mara"⟩ bridged (.grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse) true
  , inRealm "refuses-a-grant-that-moves-an-account"
      "A grant hands out a purse; it never moves an account that is already elsewhere."
      ⟨"realm-flat"⟩ realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer (acc "acc-bank" "Assets.Bank" .asset)) true
  , asMember "participant-posts-to-an-open-budget"
      "Anybody in the realm may put a cost into a budget of it while the budget is open."
      ⟨"mara"⟩ budgetWithMember
      (.putTransaction (txn "t-contrib" [cents "acc-mara" (-2500), cents "acc-hut" 2500]
        "her share of the food"))
  , asMember "refuses-posting-to-a-closed-budget-account"
      "A closed budget is a decided one, so the right to put costs into it ends with it."
      ⟨"mara"⟩ budgetShutWithMember
      (.putTransaction (txn "t-contrib2" [cents "acc-mara" (-2500), cents "acc-hut" 2500]
        "one more")) true
  , refuses "refuses-a-division-that-invents-money"
      "Parts that take less out of the funding account than the original did." spent
      (.replaceTransaction ⟨"t-dinner"⟩
        [ txn "t-p1" [cents "acc-bank" (-6000), cents "acc-food" 6000]
        , txn "t-p2" [cents "acc-bank" (-3000), cents "acc-food" 3000] ] "divide")
  , parts "mixed-parts-second-refused" "A valid part beside an invalid one, which is skipped." base
      [ .putAccount (acc "acc-new" "Expenses.Books" .expense)
      , .putTransaction (txn "t-bad" [cents "acc-bank" (-10000), cents "acc-food" 9000]) ] true
  , parts "mixed-parts-first-refused" "The invalid part first: its neighbour still applies." base
      [ .putTransaction (txn "t-bad" [cents "acc-bank" (-10000), cents "acc-food" 9000])
      , .putLabel { id := ⟨"lbl-food"⟩, name := "food", colour := none } ] true
  , parts "mixed-parts-middle-refused" "Three parts, and the one in the middle is refused." base
      [ .putAccount (acc "acc-new" "Expenses.Books" .expense)
      , .deleteTransaction ⟨"t-nobody"⟩
      , .putLabel { id := ⟨"lbl-food"⟩, name := "food", colour := none } ] true ]

/--
One refusal for every operation, about what it names.

There used to be eleven that could not be refused at all: `putAccount`,
`putLabel`, `deleteLabel`, `putParty`, `deleteGroup`, `putTrip`, `deleteTrip`,
`putRule`, `registerBlob`, `recordImportBatch` and `snapshot` wrote what they
were given and had nothing to check. Every one of them has a rule now, and the
rules are exercised in `rightsScenarios`; what is here is the other half — what
each operation refuses about the thing it names rather than about who wrote it.
-/
private def perOpRefusalScenarios : List Scenario :=
  [ refuses "refuses-a-realm-that-exists" "A realm id that is already spoken for." realmTwo
      (.createRealm { id := ⟨"realm-flat"⟩, name := "flat again", members := [], generation := 0 })
  , refuses "refuses-deleting-an-account-with-postings" "An account something still lands in."
      spent (.deleteAccount ⟨"acc-bank"⟩)
  , refuses "refuses-rights-on-a-missing-account" "Rights named on an account that is not there."
      base (.setAccountRights ⟨"acc-nobody"⟩ [⟨"mara"⟩])
  , refuses "refuses-handing-over-a-missing-account" "The same, for an account's owner." base
      (.setAccountOwner ⟨"acc-nobody"⟩ ⟨"party-anna"⟩)
  , refuses "refuses-a-missing-rule" "A rule named by neither id nor name." base
      (.deleteRule "nothing of the sort")
  , refuses "refuses-a-split-with-nobody-to-split-with" "A split naming no targets." spent
      (.splitTransaction ⟨"t-dinner"⟩ [] true)
  , refuses "refuses-a-merge-of-one" "Merging needs at least two transactions." spent
      (.mergeTransactions [⟨"t-dinner"⟩] ⟨"t-m"⟩ none none [])
  , refuses "refuses-a-division-with-no-groups" "Dividing by lines that were never named."
      receipted (.divideByItems ⟨"t-shop"⟩ [] [⟨"t-d1"⟩])
  , refuses "refuses-taking-a-cost-twice" "The same person, the same cost, a second time."
      budgetTaken (.claimCost ⟨"b-hut"⟩ ⟨"t-hut2"⟩)
  , refuses "refuses-taking-what-is-not-a-cost-of-the-budget"
      "A transaction with no leg in the budget's account." budgetFunded
      (.claimCost ⟨"b-hut"⟩ ⟨"t-dinner"⟩)
  , refuses "refuses-giving-back-what-nobody-took" "A cost no claim was made on." budgetFunded
      (.releaseCost ⟨"b-hut"⟩ ⟨"t-hut2"⟩ Member.selfId)
  , asMember "refuses-giving-back-somebody-elses-cost"
      "A member of the realm who is not an admin, undoing another's claim." ⟨"mara"⟩ budgetTaken
      (.releaseCost ⟨"b-hut"⟩ ⟨"t-hut2"⟩ Member.selfId) true
  , refuses "refuses-a-line-that-went-to-a-sibling"
      "A part holds the two lines it was left with, and a third number is not one of them."
      divided (.divideByItems ⟨"t-d2"⟩ [{ items := [{ line := 3 }], into := "acc-anna" }]
        [⟨"t-e1"⟩, ⟨"t-e2"⟩])
  , refuses "refuses-a-claim-that-has-happened" "A claim is a transaction that has not happened."
      base (.raiseClaim (txn "t-not-a-claim" [cents "acc-bank" 5000, cents "acc-anna" (-5000)]))
  , refuses "refuses-voiding-a-transaction" "A posted transaction is not a claim to withdraw."
      spent (.voidClaim ⟨"t-dinner"⟩ none)
  , asMember "refuses-a-budget-opened-by-a-non-admin"
      "Only an admin of a realm may open a budget in it." ⟨"mara"⟩ base
      (.openBudget hut (acc "acc-hut" "Hut" .equity)) true
  , refuses "refuses-participants-on-a-missing-budget" "A budget nobody opened." base
      (.setParticipants ⟨"b-nobody"⟩ among)
  , refuses "refuses-a-share-in-an-account-of-yours"
      "A share of hers may not land in an account of yours." budgetFunded
      (.allocate ⟨"b-hut"⟩ [{ owner := ⟨"party-anna"⟩, name := "Anna", account := "Expenses.Food" }]
        eur day none ⟨"t-nowhere"⟩ [] ⟨"lbl-hut"⟩)
  , refuses "refuses-settling-a-budget-still-holding-money"
      "There would be a residue belonging to nobody." budgetLate
      (.settle ⟨"b-hut"⟩ eur none day [⟨"t-claim5"⟩] ⟨"lbl-hut"⟩)
  , refuses "refuses-closing-a-closed-budget" "Closing one that is already closed." budgetClosed
      (.closeBudget ⟨"b-hut"⟩ none eur none day ⟨"t-alloc5"⟩ [⟨"t-claim5"⟩] ⟨"lbl-hut"⟩)
  , refuses "refuses-reopening-an-open-budget" "Reopening one that was never closed." budgetShared
      (.reopenBudget ⟨"b-hut"⟩)
  , refuses "refuses-deleting-a-missing-budget" "A budget nobody opened." base
      (.deleteBudget ⟨"b-nobody"⟩)
  , refuses "refuses-an-invoice-id-that-exists" "An invoice id that is already spoken for."
      invoiced (.issueInvoice (draft "i1") [])
  , refuses "refuses-a-status-on-a-missing-invoice" "An invoice that was never raised." base
      (.setInvoiceStatus ⟨"i-nobody"⟩ .sent)
  , refuses "refuses-settling-an-invoice-with-a-missing-transaction"
      "The entry that is said to have paid it is not there." invoiced
      (.settleInvoice ⟨"i1"⟩ ⟨"t-nobody"⟩)
  , refuses "refuses-attaching-a-missing-receipt" "A content hash nothing is stored under." spent
      (.attach ⟨"t-dinner"⟩ "nothing")
  , refuses "refuses-detaching-from-a-missing-transaction" "A transaction that is not there." base
      (.detach ⟨"t-nobody"⟩ "rcpt")
  , refuses "refuses-an-extraction-of-a-missing-receipt" "Nothing is stored under that hash." base
      (.recordExtraction "nothing" extracted)
  , refuses "refuses-lines-past-the-total"
      "Lines may fall short of what a receipt says it came to, and never overrun it." receipted
      (.setReceiptLines "rcpt"
        [{ description := "everything", qty := none, amount := ⟨eur, 20000⟩ }])
  , refuses "refuses-forgetting-a-missing-receipt" "Nothing is stored under that hash." base
      (.forgetBlob "nothing")
  , asMember "refuses-a-member-added-by-a-non-admin"
      "A member introduces themselves; writing somebody else in is an admin's decision."
      ⟨"mara"⟩ base
      (.addMember { id := ⟨"nils"⟩, name := "Nils", party := ⟨"party-nils"⟩ }) true
  , refuses "refuses-removing-yourself" "The member this ledger belongs to cannot be removed." base
      (.removeMember Member.selfId)
  , asMemberIn "refuses-a-revoke-by-a-non-admin" "Only an admin of a realm may put somebody out."
      ⟨"mara"⟩ ⟨"realm-flat"⟩ granted (.revoke ⟨"realm-flat"⟩ ⟨"mara"⟩) true
  , inRealm "refuses-a-role-for-somebody-outside-the-realm"
      "A role can only be changed for somebody who holds one." ⟨"realm-flat"⟩ realmTwo
      (.setRole ⟨"realm-flat"⟩ ⟨"mara"⟩ .admin) true
  , inRealm "refuses-rotating-a-missing-realm"
      "A realm nobody created, and so nobody administers." ⟨"realm-nobody"⟩ base
      (.rotateRealmKey ⟨"realm-nobody"⟩) true ]

/-- The edges of the encoding: LEB128 boundaries, signs, empty things and the ends of a date. -/
private def boundaryScenarios : List Scenario :=
  [ one "boundary-leb128-127" "An amount of 127 minor units: the last one-byte LEB128." base
      (.putTransaction (txn "t-127" [cents "acc-bank" (-127), cents "acc-food" 127] "one byte"))
  , one "boundary-leb128-128" "An amount of 128: the first two-byte LEB128." base
      (.putTransaction (txn "t-128" [cents "acc-bank" (-128), cents "acc-food" 128] "two bytes"))
  , one "boundary-leb128-16383" "An amount of 16383: the last two-byte LEB128." base
      (.putTransaction (txn "t-16383" [cents "acc-bank" (-16383), cents "acc-food" 16383]
        "two bytes still"))
  , { name := "boundary-leb128-16384"
      description := "An amount of 16384 and an event based on 16384: the first three-byte LEB128."
      state := stateOf base
      event := { ev "boundary-leb128-16384"
        [.putTransaction (txn "t-16384" [cents "acc-bank" (-16384), cents "acc-food" 16384]
          "three bytes")] with basedOn := 16384 } }
  , one "boundary-negative-amounts" "A refund: the expense leg is the negative one." base
      (.putTransaction
        (txn "t-refund" [cents "acc-food" (-2500), cents "acc-bank" 2500] "returned"))
  , one "boundary-empty-strings" "An empty narration and an empty payee." base
      (.putTransaction { txn "t-empty" [cents "acc-bank" (-100), cents "acc-food" 100] "" with
        payee := some "" })
  , { name := "boundary-empty-event"
      description := "An event with no parts at all, which changes nothing."
      state := stateOf base
      event := ev "boundary-empty-event" [] }
  , one "boundary-date-2000-01-01" "A transaction on the earliest date the vectors use." base
      (.putTransaction { txn "t-early" [cents "acc-bank" (-100), cents "acc-food" 100] "long ago"
        with date := dayEarly })
  , one "boundary-date-2099-12-31" "A transaction on the latest date the vectors use." base
      (.putTransaction { txn "t-late" [cents "acc-bank" (-100), cents "acc-food" 100] "long hence"
        with date := dayLate }) ]

/--
One refusal per rule in the rights table.

`Op.rights` is a total function, so every operation has a rule and every rule is
a sentence somebody can be told. These are those sentences, one scenario each,
grouped the way the table is: what needs a realm, what needs an admin, what needs
post rights on the legs it writes, and what needs to be about you.

A port that quietly takes any of these is a port that would let a viewer of one
realm rewrite another's books, which is what every one of them used to do.
-/
private def rightsScenarios : List Scenario :=
  [ -- Global: a member of the realm, a fresh state for genesis, bounded lists.
    asMember "refuses-an-author-outside-the-realm"
      "Every operation asks first whether its author is in the realm the part names."
      ⟨"zoe"⟩ base (.putTransaction dinner) true
  , asMember "refuses-a-realm-member-without-post-rights"
      "Being in the realm is not being able to write in it." ⟨"mara"⟩ viewing
      (.putTransaction dinner) true
  , refuses "refuses-a-snapshot-once-anything-has-happened"
      "A snapshot replaces the state, so it is the first thing a log says or it is a takeover."
      spent (.snapshot (stateOf budgetClosed))
  , refuses "refuses-a-snapshot-by-an-admin-of-the-realm"
      "Not even an admin: `applyOp` refuses every snapshot, wherever it appears and whoever \
       wrote it, and `replay` reads the genesis off the first event of the log instead."
      base (.snapshot (stateOf spent))
  , refuses "refuses-a-transaction-with-no-postings"
      "An empty posting list balances vacuously, which made it a way to rewrite any \
       transaction's metadata — including voiding it." base
      (.putTransaction { txn "t-nothing" [] with payee := some "nobody" })
  , refuses "refuses-a-transaction-that-is-not-posted"
      "A transaction is written as something that happened; the other states belong to claims."
      base
      (.putTransaction { txn "t-void" [cents "acc-bank" (-100), cents "acc-food" 100] with
         state := .void })
  , refuses "refuses-too-many-postings" "A list an author chose the length of is bounded." base
      (.putTransaction (txn "t-many" (List.replicate 201 (cents "acc-bank" 0))))
  , refuses "refuses-too-many-participants" "The same, for the people a budget is divided among."
      budgetOpened
      (.setParticipants ⟨"b-hut"⟩ (List.replicate 101
        { owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna" }))
  , refuses "refuses-a-weight-out-of-range" "A share's weight is a small number." budgetOpened
      (.setParticipants ⟨"b-hut"⟩
        [{ owner := ⟨"party-anna"⟩, name := "Anna", account := "Assets.Purse.Anna"
           weight := 10001 }])
  , refuses "refuses-a-line-quantity-nobody-printed"
      "A receipt line covering a thousand million units is how one small event made every \
       reader allocate a list of that length." receipted
      (.setReceiptLines "rcpt"
        [{ description := "x", qty := some 1000000000000, amount := ⟨eur, 1⟩ }])
  , refuses "refuses-an-identifier-that-is-too-long" "An id is a name, not a document." base
      (.putLabel { id := ⟨String.ofList (List.replicate 201 'x')⟩, name := "long" })
  , refuses "refuses-a-year-out-of-range"
      "A date's year is the one part of a date no type bounds, and a ledger keeping books \
       a million years hence is a number somebody sent, not a date." base
      (.putTransaction { txn "t-year" [cents "acc-bank" (-100), cents "acc-food" 100] "far off"
         with date := dayImpossible })
  , refuses "refuses-an-exponent-out-of-range"
      "A commodity's scale is ten to the power of its exponent, so an exponent an author \
       chose is a bignum an author chose the length of." base
      (.putTransaction (txn "t-exponent"
        [ { account := ⟨"acc-bank"⟩, amount := ⟨tooManyPlaces, -100⟩ }
        , { account := ⟨"acc-food"⟩, amount := ⟨tooManyPlaces, 100⟩ } ] "too fine"))
    -- Structure: an admin writes the shared vocabulary and the accounts.
  , refuses "refuses-a-realm-with-somebody-else-inside-it"
      "A realm is created with its author as its only admin; the membership list is not \
       the author's to choose." base
      (.createRealm { id := ⟨"realm-squat"⟩, name := "squat"
                      members := [(⟨"mara"⟩, .admin)], generation := 0 })
  , refuses "refuses-a-realm-at-a-rotated-generation"
      "A new realm starts at generation 0: a history that begins after a revoke is a lie." base
      (.createRealm { id := ⟨"realm-squat"⟩, name := "squat"
                      members := [(Member.selfId, .admin)], generation := 3 })
  , asMember "refuses-an-account-written-by-a-viewer"
      "Whoever may write an account into a realm decides who posts to everything in it."
      ⟨"mara"⟩ viewing (.putAccount (acc "acc-shadow" "Budget.Hut" .equity)) true
  , inRealm "refuses-rewriting-an-account-of-another-realm"
      "An account is rewritten from the realm it sits in, and no other." Realm.selfId
      flatAccount (.putAccount (acc "acc-flat" "Assets.Theirs" .asset)) true
  , asMember "refuses-a-merge-by-a-viewer"
      "A merge empties the account it names, so it asks about that one too." ⟨"mara"⟩ viewing
      (.mergeAccounts ⟨"acc-anna"⟩ ⟨"acc-mara"⟩) true
  , asMember "refuses-an-account-deleted-by-a-viewer" "Removing an account is an admin's."
      ⟨"mara"⟩ viewing (.deleteAccount ⟨"acc-spare"⟩) true
  , asMember "refuses-rights-set-by-a-viewer" "So is saying who may post where." ⟨"mara"⟩ viewing
      (.setAccountRights ⟨"acc-bank"⟩ [⟨"mara"⟩]) true
  , asMember "refuses-an-account-handed-over-by-a-viewer" "And so is handing one to somebody."
      ⟨"mara"⟩ viewing (.setAccountOwner ⟨"acc-bank"⟩ ⟨"party-mara"⟩) true
  , asMember "refuses-a-label-written-by-a-viewer"
      "A label is shared vocabulary, and the first one of a name used to decide which claims \
       a budget could see." ⟨"mara"⟩ viewing
      (.putLabel { id := ⟨"0000"⟩, name := "budget:Hut" }) true
  , asMember "refuses-a-label-deleted-by-a-viewer"
      "Deleting a label strips it from every transaction carrying it." ⟨"mara"⟩ viewing
      (.deleteLabel ⟨"lbl-hut"⟩) true
  , asMember "refuses-a-party-rewritten-by-a-viewer"
      "A party record is what a settlement is addressed to." ⟨"mara"⟩ viewing
      (.putParty { id := Party.selfId, name := "not you", kind := "contact" }) true
  , asMember "refuses-a-group-written-by-a-viewer" "A saved set of people is the realm's."
      ⟨"mara"⟩ viewing (.putGroup { name := "flat", members := ["Anna"] }) true
  , asMember "refuses-a-trip-written-by-a-viewer" "So is a trip." ⟨"mara"⟩ viewing
      (.putTrip { id := "trp-x", name := "Anywhere", starts := day, ends := day
                  payer := "party-anna", note := none }) true
  , asMember "refuses-a-rule-written-by-a-viewer" "Rules drive what an import files where."
      ⟨"mara"⟩ viewing
      (.putRule { id := ⟨"rul-x"⟩, name := "mine", filterSrc := "", filter := .all
                  setAccount := some "acc-mara", addLabels := [], setParty := none
                  priority := 0 }) true
  , asMember "refuses-an-import-batch-by-a-viewer" "And so is the record of an import."
      ⟨"mara"⟩ viewing
      (.recordImportBatch { id := ⟨"bat-x"⟩, profile := "dkb", filename := none
                            account := none, stamp := "", total := 0, duplicates := 0 }) true
    -- Members and realms: what a newcomer may say about themselves.
  , asMember "refuses-a-newcomer-taking-the-ledgers-party"
      "A member's party is what their spending is attributed to, so it may not be yours."
      ⟨"zoe"⟩ base
      (.addMember { id := ⟨"zoe"⟩, name := "Zoe", party := Party.selfId }) true
  , asMember "refuses-a-newcomer-taking-somebody-elses-party"
      "Nor anybody else's: it would put their movements in that person's standing."
      ⟨"zoe"⟩ base
      (.addMember { id := ⟨"zoe"⟩, name := "Zoe", party := ⟨"party-mara"⟩ }) true
  , refuses "refuses-a-grant-for-another-realm"
      "The evidence a sequencer holds is a grant on the realm the part names, so that is \
       the only realm a part can speak about." realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer maraPurse)
    -- Transactions: post rights on every leg, here and already there.
  , inRealm "refuses-rewriting-a-transaction-with-no-leg-here"
      "A part with nothing of this realm's to replace has no business replacing the metadata."
      ⟨"realm-flat"⟩ (after flatAccount [.putTransaction dinner])
      (.putTransaction { dinner with state := .posted, narration := "not mine" }) true
  , asMember "refuses-deleting-somebody-elses-transaction"
      "A transaction is retired by somebody who could have written it." ⟨"mara"⟩ spentSeen
      (.deleteTransaction ⟨"t-dinner"⟩) true
  , asMember "refuses-splitting-somebody-elses-transaction"
      "The same holds of every arithmetic intent over it." ⟨"mara"⟩ spentSeen
      (.splitTransaction ⟨"t-dinner"⟩ [⟨"acc-mara"⟩] true) true
  , asMember "refuses-attaching-to-somebody-elses-transaction"
      "A receipt is hung on a transaction by somebody who may post to it." ⟨"mara"⟩ spentSeen
      (.attach ⟨"t-dinner"⟩ "rcpt") true
  , asMember "refuses-detaching-from-somebody-elses-transaction" "And taken off the same way."
      ⟨"mara"⟩ spentSeen (.detach ⟨"t-dinner"⟩ "rcpt") true
    -- Claims: raising is an admin's; meeting and withdrawing are the creditor's.
  , asMember "refuses-a-claim-raised-by-a-viewer"
      "Asking somebody for money in the realm's name is an admin's decision." ⟨"mara"⟩ viewing
      (.raiseClaim { id := ⟨"t-mine"⟩, date := day, narration := "pay me", state := .pending
                     postings := [cents "acc-mara" 5000, cents "acc-bank" (-5000)] }) true
  , asMember "refuses-voiding-a-claim-by-the-debtor"
      "Withdrawing a claim is the creditor's decision; the debtor doing it is not paying."
      ⟨"mara"⟩ bridged (.voidClaim ⟨"t-claim-m"⟩ none) true
  , refuses "refuses-voiding-a-claim-that-was-met"
      "Withdrawing a settled claim took the payment out of the settlement arithmetic, so the \
       same money was asked for twice." claimMet (.voidClaim ⟨"t-claim-m"⟩ none)
  , asMember "refuses-resolving-a-claim-by-the-debtor"
      "Saying money arrived is the decision of whoever would have seen it arrive."
      ⟨"mara"⟩ (after bridged
        [.putTransaction (txn "t-in" [cents "acc-nils" 5000, cents "acc-unc" (-5000)] "paid")])
      (.resolveClaim ⟨"t-claim-m"⟩ ⟨"t-in"⟩ ⟨"t-part"⟩) true
  , refuses "refuses-paying-a-claim-into-an-account-that-holds-no-money"
      "A payment into an equity leg was rewritten onto the paying account, so the claim came \
       out met and nothing had moved." (after budgetShared
        [.raiseClaim { id := ⟨"t-pot"⟩, date := day, narration := "into the pot"
                       state := .pending
                       postings := [cents "acc-hut" 1000, cents "acc-anna" (-1000)] }])
      (.payClaim ⟨"t-pot"⟩ ⟨"t-pot-pay"⟩ day)
    -- Budgets: an admin of the budget's own realm, and a pot you can only fill.
  , asMember "refuses-participants-named-by-a-viewer"
      "Who a budget is divided among is an admin's decision." ⟨"mara"⟩ budgetWithMember
      (.setParticipants ⟨"b-hut"⟩ among) true
  , asMember "refuses-an-allocation-by-a-viewer" "So is dividing what it holds." ⟨"mara"⟩
      budgetWithMember
      (.allocate ⟨"b-hut"⟩ among eur day none ⟨"t-alloc-v"⟩ [⟨"t-claim-v"⟩] ⟨"lbl-hut"⟩) true
  , inRealm "refuses-a-budget-decided-from-another-realm"
      "A budget belongs to one realm, and a decision about it has to be written under its key."
      ⟨"realm-flat"⟩ (after budgetShared
        [.createRealm { id := ⟨"realm-flat"⟩, name := "flat"
                        members := [(Member.selfId, .admin)], generation := 0 }])
      (.reopenBudget ⟨"b-hut"⟩) true
  , asMember "refuses-taking-money-out-of-a-budget"
      "A participant's right on the pot is a right to contribute. A pot everybody may take \
       out of is not a pot." ⟨"mara"⟩ budgetWithMember
      (.putTransaction (txn "t-take" [cents "acc-hut" (-2500), cents "acc-mara" 2500]
        "helping myself")) true
    -- Invoices: one gapless sequence, and only an admin moves it.
  , asMember "refuses-an-invoice-issued-by-a-viewer"
      "Burning a number in your sequence, or winding it back, is not a viewer's to do."
      ⟨"mara"⟩ viewing (.issueInvoice (draft "i-v") []) true
  , asMember "refuses-an-invoice-status-set-by-a-viewer" "Nor is moving one to a new status."
      ⟨"mara"⟩ (after viewing [.issueInvoice (draft "i1") []])
      (.setInvoiceStatus ⟨"i1"⟩ .void) true
    -- Receipts: what a receipt says is what a division divides by.
  , asMember "refuses-a-receipt-rewritten-by-somebody-else"
      "Only the member who filed the bytes, somebody who may post what they belong to, or an \
       admin, may say what a receipt contains." ⟨"nils"⟩
      (after filedByMara [.grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse])
      (.setReceiptLines "rcpt" [{ description := "wine", amount := ⟨eur, 2000⟩ }]) true
  , asMember "refuses-an-extraction-by-somebody-else" "The same for what was read off it."
      ⟨"nils"⟩ (after filedByMara [.grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse])
      (.recordExtraction "rcpt" extracted) true
  , asMember "refuses-re-registering-somebody-elses-file"
      "Re-sealing a file is a decision about where their bytes are kept." ⟨"nils"⟩
      (after filedByMara [.grant Realm.selfId ⟨"nils"⟩ .viewer nilsPurse])
      (.registerBlob { receipt with cipherHash := some "ff" }) true
  , asMember "refuses-forgetting-a-receipt-by-a-viewer" "Forgetting one is an admin's."
      ⟨"mara"⟩ (after viewing [.registerBlob receipt]) (.forgetBlob "rcpt") true ]

/--
One scenario per entity kind that gained a realm, and per door that used to be
open because it had none.

The rule is one sentence — a part may only speak about an entry of the realm it
names — and it is here eight times because there were eight kinds of entry it
did not hold of. An admin of any realm a reader can open could delete a label
out of every transaction in every realm that reader held, rewrite any person in
their books, install rules that drive what their imports file where, and forget
their receipts; and "admin of a realm you can read" is a right anybody can
manufacture, because anybody may create a realm and hand you a key to it.
-/
private def realmScenarios : List Scenario :=
  [ inRealm "put-label-in-another-realm"
      "A label is created in the realm the part names, and carries it."
      ⟨"realm-flat"⟩ realmTwo (.putLabel { id := ⟨"lbl-flat"⟩, name := "flat:rent" })
  , refuses "refuses-rewriting-a-label-of-another-realm"
      "Shared vocabulary belongs to the people who share it." flatVocabulary
      (.putLabel { id := ⟨"lbl-flat"⟩, name := "mine now" })
  , refuses "refuses-deleting-a-label-of-another-realm"
      "Deleting a label strips it from the transactions carrying it, and those are not this \
       part's to rewrite." flatVocabulary (.deleteLabel ⟨"lbl-flat"⟩)
  , refuses "refuses-rewriting-a-party-of-another-realm"
      "A party record is what a settlement is addressed to, and it belongs to the realm the \
       person was introduced in." flatVocabulary
      (.putParty { id := ⟨"party-flat"⟩, name := "not them", kind := "contact" })
  , asMemberIn "member-revises-their-own-party-from-any-realm"
      "The one entity a member owns outright: the party their own spending lands on. They \
       may revise it from any realm they are in, and the record keeps the realm it was \
       introduced in." ⟨"mara"⟩ ⟨"realm-flat"⟩ granted
      (.putParty { id := ⟨"party-mara"⟩, name := "Mara Neumann", kind := "contact" })
  , refuses "refuses-a-group-of-another-realm" "A saved set of people is a realm's."
      flatVocabulary (.putGroup { name := "flatmates", members := ["Bob"] })
  , refuses "refuses-deleting-a-group-of-another-realm" "And so is removing one."
      flatVocabulary (.deleteGroup "flatmates")
  , refuses "refuses-a-trip-of-another-realm" "So is a trip." flatVocabulary
      (.putTrip { id := "trp-flat", name := "Flat", starts := dayEarly, ends := dayLate
                  payer := "party-bob", note := some "mine now" })
  , refuses "refuses-deleting-a-trip-of-another-realm" "And removing one." flatVocabulary
      (.deleteTrip "Flat")
  , refuses "refuses-a-rule-of-another-realm"
      "Rules drive what an import files where, so they are the realm's they were written in."
      flatVocabulary
      (.putRule { id := ⟨"rul-flat"⟩, name := "theirs", filterSrc := "", filter := .all
                  setAccount := some "acc-food", addLabels := [], setParty := none
                  priority := 0 })
  , refuses "refuses-an-import-batch-of-another-realm" "And so is the record of an import."
      flatVocabulary
      (.recordImportBatch { id := ⟨"bat-flat"⟩, profile := "elsewhere", filename := none
                            account := none, stamp := "", total := 1, duplicates := 0 })
  , refuses "refuses-rewriting-a-receipt-filed-in-another-realm"
      "Whoever filed a receipt keeps the right to say what it contains — in the realm they \
       filed it in, and not from any other realm they hold a key for." flatReceipt
      (.setReceiptLines "rcpt" [{ description := "wine", amount := ⟨eur, 2000⟩ }])
  , refuses "refuses-forgetting-a-receipt-filed-in-another-realm"
      "Forgetting one is an admin's, of the realm the bytes were filed in." flatReceipt
      (.forgetBlob "rcpt")
  , refuses "refuses-an-invoice-touched-from-another-realm"
      "An invoice record carries the realm it was issued in, and the counter is keyed by \
       realm — so deleting a draft from anywhere else wound back a sequence that had never \
       issued it: the issuing realm kept the burnt number, and the next invoice in the \
       other realm duplicated one already sent. Setting the status and recording a \
       settlement go through the same door." flatInvoice (.deleteInvoice ⟨"i-flat"⟩)
  , inRealm "invoice-payer-resolved-in-this-realm"
      "The payer is looked up by name inside the part's realm. The lookup used to be the \
       first party of that name in id order across every realm a reader could open, and a \
       member may set the name of their own party to anything from any realm they are in — \
       so an invoice to a name you both know was addressed to whichever record sorted first."
      ⟨"realm-flat"⟩ flatPayer (.issueInvoice (draft "i-flat") [])
  , one "refuses-a-settlement-account-from-another-realm"
      "The account a person settles through is looked for in the budget's own realm. An \
       account of theirs in another realm is refused as a candidate here, rather than \
       chosen and then refused by the posting rules — which is what used to happen, and it \
       stopped every settlement of the budget until somebody closed or renamed an account \
       in a realm that had nothing to do with it." cabinAbroad
      (.allocate ⟨"b-cabin"⟩ three eur day none ⟨"t-cal2"⟩ [⟨"t-cs1"⟩, ⟨"t-cs2"⟩] ⟨"lbl-cabin"⟩)
  , inRealm "invoice-numbering-is-per-realm"
      "The year's counter is keyed by realm. One sequence for the whole ledger meant an \
       admin of any realm a reader could open moved the ledger owner's invoice numbering."
      ⟨"realm-flat"⟩ realmTwo (.issueInvoice (draft "i-flat") [])
    -- The attest door, and the one thing it may make.
  , asMemberIn "self-grant-makes-the-canonical-bridge"
      "A member attesting their own viewer grant opens one purse: named after them, of the \
       kind money is held in, with nobody else on it and mirroring nothing. Everything else \
       the operation carries is ignored, because the door is open to any member about \
       themselves and it used to write the name, the kind and the posters verbatim."
      ⟨"mara"⟩ ⟨"realm-flat"⟩ realmTwo
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer
        { acc "acc-mine" "Budget.Hut" .equity with posters := [⟨"mara"⟩] })
  , asMemberIn "refuses-a-self-grant-onto-a-name-that-exists"
      "Nothing is adopted by the attest door either: a joiner taking over an account that \
       is already there is the same hole read backwards." ⟨"mara"⟩ ⟨"realm-flat"⟩
      flatNameTaken
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer (acc "acc-mine" "Members.Mara" .asset)) true
  , asMemberIn "refuses-a-self-grant-onto-an-id-that-exists"
      "Nor by id." ⟨"mara"⟩ ⟨"realm-flat"⟩ flatAccount
      (.grant ⟨"realm-flat"⟩ ⟨"mara"⟩ .viewer (acc "acc-flat" "Members.Mara" .asset)) true
    -- Budgets: the pot is adopted only when it is a pot.
  , refuses "refuses-a-budget-held-in-somebody-s-purse"
      "A viewer who self-granted a purse called `Budget.Hut` before the budget was opened \
       had the pot adopted as their own bridge, which they may post to in either direction."
      potSquatted (.openBudget hut (acc "acc-hut" "Hut" .equity))
  , one "open-budget-adopts-a-plain-equity-account"
      "An account of the budget's name that is a pot and nobody's purse is adopted, which is \
       what makes opening a budget over one that is already there say nothing new."
      potReady (.openBudget hut (acc "acc-hut" "Hut" .equity))
  , one "allocate-to-a-participant-s-bridge"
      "A share may land in the purse a member holds in this realm: a bridge belongs to the \
       member it is for, and their spending lands on their party, so both readings of \
       \"an account of theirs\" are allowed and nothing else is." bridgeShare
      (.allocate ⟨"b-hut"⟩
        [ { owner := Party.selfId, name := "me", account := "Expenses.Food" }
        , { owner := ⟨"party-mara"⟩, name := "Mara", account := "Assets.Purse.Mara" } ]
        eur day none ⟨"t-alloc-b"⟩ [⟨"t-claim-b"⟩] ⟨"lbl-hut"⟩)
    -- Claims.
  , asMember "receiver-resolves-their-own-claim"
      "The member whose purse was owed says the money arrived, without post rights on the \
       debtor's purse. The rights table always granted this and the arithmetic never \
       allowed it: settling writes the claim back, and the claim's paying leg is the \
       debtor's." ⟨"nils"⟩ paidIn
      (.resolveClaim ⟨"t-claim-m"⟩ ⟨"t-in"⟩ ⟨"t-part"⟩)
  , refuses "refuses-overwriting-a-stored-claim"
      "A claim is met or withdrawn, never overwritten. Rewriting one as a posted \
       transaction took it out of the settlement arithmetic and put its amounts into every \
       balance, without going through either claim verb." claimed
      (.putTransaction (txn "t-claim" [cents "acc-bank" 5000, cents "acc-anna" (-5000)]
        "not a claim any more"))
  , refuses "refuses-overwriting-a-settled-claim"
      "The same door reached a claim that had already been met, and so booked money that \
       had already moved a second time." resolved
      (.putTransaction (txn "t-claim" [cents "acc-bank" 5000, cents "acc-anna" (-5000)]
        "again"))
    -- Bounds on what an intent computes, rather than on what it carries.
  , refuses "refuses-a-split-that-computes-too-many-postings"
      "`checkBounds` refuses a transaction of more than two hundred legs that an author \
       *sends*; this is one an intent computed, which nothing used to bound at all."
      spent (.splitTransaction ⟨"t-dinner"⟩
        (List.replicate 200 (⟨"acc-anna"⟩ : AccountId)) true) ]

/-- Every scenario, in the order the file writes them. -/
def scenarios : List Scenario :=
  structureScenarios ++ transactionScenarios ++ claimScenarios ++ budgetScenarios ++
    invoiceScenarios ++ receiptScenarios ++ refusalScenarios ++
    perOpRefusalScenarios ++ rightsScenarios ++ realmScenarios ++ boundaryScenarios

/-! ## Running them -/

/--
The parts `applyOp` refused, by index.

`step` skips them and says nothing about which, so this walks the same fold
again — a part is applied to what the parts before it left behind, which is why
this cannot be decided part by part in isolation.
-/
def rejectedParts (s : State) (e : Event) : List Nat := Id.run do
  let mut st := s
  let mut out : List Nat := []
  for (p, i) in e.parts.zipIdx do
    match applyPart st e.author p with
    | .ok (next, _) => st := next
    | .error _ => out := out ++ [i]
  return out

/-- A scenario, run: the bytes, the hash, the changes and the refusals. -/
def render (sc : Scenario) : Case :=
  let (expected, changes) := step sc.state sc.event
  { name := sc.name
    description := sc.description
    stateHex := toHex (Codec.encode sc.state)
    eventHex := toHex (Codec.encode sc.event)
    expectedHex := toHex (Codec.encode expected)
    expectedHash := Encode.hashState expected
    changes := changes.map fun c => (changeKind c, changeId c)
    rejected := rejectedParts sc.state sc.event }

/-- Every vector. -/
def vectors : List Case := scenarios.map render

/-! ## Bytes a decoder has to refuse

Every vector above is a *well-formed* input, and a port could reproduce all of
them while accepting non-canonical bytes — which is exactly the property a
checkpoint rests on. A checkpoint is the hash of a state's canonical encoding,
so a reader that takes a second spelling of a state will re-encode it to
something the sender never committed to, and two honest peers then disagree
about whether a checkpoint verifies. The same goes for an event: two spellings
mean two hashes for one decision.

So the shared artefacts carry the other half too. Each entry below is a byte
string that `Codec.decode` must refuse, and `type` says which decoder has to
refuse it — a port has all six, because they are the primitives its state and
event decoders are built from.
-/

/-- One byte string a conforming decoder has to refuse, and why. -/
structure Reject where
  /-- A stable name. -/
  name : String
  /-- What is wrong with these bytes. -/
  description : String
  /-- Which decoder refuses it: `nat`, `int`, `string`, `date`, `state` or `event`. -/
  type : String
  /-- The bytes, in hex. -/
  hex : String

/-- The state most of the crafted rejections are built by corrupting. -/
private def rejectState : State := stateOf spent

/-- Bytes, as the hex a vector carries. -/
private def hexOf {α : Type} [Codec α] (x : α) : String := toHex (Codec.encode x)

/-- A year one past the last a date may name, inside a transaction of a state. -/
private def stateWithBadYear : State :=
  { rejectState with
      txns := rejectState.txns.insert "t-dinner" { dinner with date := dayImpossible } }

/-- An amount whose count of minor units does not fit the column a port stores it in. -/
private def stateWithBadAmount : State :=
  { rejectState with
      txns := rejectState.txns.insert "t-dinner"
        { dinner with postings :=
            [ { account := ⟨"acc-bank"⟩, amount := ⟨eur, -(2 ^ 63)⟩ }
            , { account := ⟨"acc-food"⟩, amount := ⟨eur, 2 ^ 63⟩ } ] } }

/-- A commodity with more decimal places than anything can compute in. -/
private def stateWithBadExponent : State :=
  { rejectState with
      txns := rejectState.txns.insert "t-dinner"
        { dinner with postings :=
            [ { account := ⟨"acc-bank"⟩, amount := ⟨tooManyPlaces, -100⟩ }
            , { account := ⟨"acc-food"⟩, amount := ⟨tooManyPlaces, 100⟩ } ] } }

/-- An event whose one part carries a snapshot of a state no reader may believe. -/
private def eventWithBadState : Event :=
  { ev "bad-snapshot" [] with parts := [{ realm := Realm.selfId, op := .snapshot stateWithBadYear }] }

/-- The bytes a conforming decoder refuses, and what is wrong with each. -/
def rejects : List Reject :=
  [ { name := "overlong-leb128-zero", type := "nat", hex := "8000"
      description := "Zero written in two bytes. A continuation byte has to contribute \
                      something, or every natural has unboundedly many encodings." }
  , { name := "overlong-leb128-one", type := "nat", hex := "8100"
      description := "One, written in two bytes, for the same reason." }
  , { name := "doubly-overlong-leb128-zero", type := "nat", hex := "808000"
      description := "Zero in three bytes: the rule is about every continuation byte, not \
                      only the first." }
  , { name := "negative-zero", type := "int", hex := "0100"
      description := "A sign byte of 1 and a magnitude of 0. Zero has one encoding, and it \
                      is the non-negative one." }
  , { name := "trailing-byte-after-an-integer", type := "int", hex := "000000"
      description := "A valid zero followed by a byte nobody asked for. `decode` reads a \
                      whole byte string or none of it." }
  , { name := "overlong-length-prefix", type := "string", hex := "820068690000"
      description := "A string of length 2 whose length prefix is written in two bytes." }
  , { name := "thirteenth-month", type := "date"
      hex := hexOf ((2026 : Int), (13 : Int), (1 : Int))
      description := "A month no year has. A port whose date is three numbers checks all \
                      three; Lean's `PlainDate` carries the proof." }
  , { name := "thirty-first-of-february", type := "date"
      hex := hexOf ((2026 : Int), (2 : Int), (31 : Int))
      description := "Three numbers that are each in range and are not a date." }
  , { name := "year-out-of-range", type := "date"
      hex := hexOf ((maxYear + 1 : Int), (1 : Int), (1 : Int))
      description := "A year past the last one this format carries." }
  , { name := "unsorted-map", type := "state"
      hex := hexOf { rejectState.wire with labels := rejectState.wire.labels.reverse }
      description := "A state whose labels are not strictly ascending by key. The entries \
                      would be folded back in with `insert` and re-encode to other bytes, so \
                      the state would not hash to what it was read out of." }
  , { name := "duplicate-key", type := "state"
      hex := hexOf { rejectState.wire with
                       parties := rejectState.wire.parties ++ rejectState.wire.parties }
      description := "The same key twice: one entry would silently win." }
  , { name := "misfiled-entity", type := "state"
      hex := hexOf { rejectState.wire with
                       labels := rejectState.wire.labels.map
                         (fun (p : String × Label) => ("not-its-id", p.2)) }
      description := "An entity filed under a key that is not its own id, which makes \
                      \"the label with this id\" a question with two answers." }
  , { name := "trailing-byte-after-a-state", type := "state"
      hex := hexOf rejectState ++ "00"
      description := "A whole state and then a byte nobody asked for." }
  , { name := "state-with-a-year-out-of-range", type := "state"
      hex := hexOf stateWithBadYear
      description := "A state is believed rather than applied, so the numbers inside one are \
                      questioned here or nowhere." }
  , { name := "state-with-an-exponent-out-of-range", type := "state"
      hex := hexOf stateWithBadExponent
      description := "A commodity's scale is ten to the power of its exponent, so an exponent \
                      a sender chose is a bignum a sender chose the length of." }
  , { name := "state-with-an-amount-out-of-range", type := "state"
      hex := hexOf stateWithBadAmount
      description := "A count of minor units that does not fit the signed 64-bit column a \
                      port stores it in." }
  , { name := "event-carrying-a-snapshot-of-such-a-state", type := "event"
      hex := hexOf eventWithBadState
      description := "The bound travels with the value: an event carrying a state is refused \
                      for what the state says, where an event carrying an *operation* that \
                      says the same thing decodes and is refused when it is applied." } ]

/-- Whether a decoder of this type refuses these bytes: what a port has to reproduce. -/
def isRefused (rj : Reject) : Bool :=
  match ofHex? rj.hex with
  | none => false
  | some bs =>
    match rj.type with
    | "nat" => (Codec.decode (α := Nat) bs).isNone
    | "int" => (Codec.decode (α := Int) bs).isNone
    | "string" => (Codec.decode (α := String) bs).isNone
    | "date" => (Codec.decode (α := Date) bs).isNone
    | "state" => (Codec.decode (α := State) bs).isNone
    | "event" => (Codec.decode (α := Event) bs).isNone
    | _ => false

/-- The rejections this core does not in fact refuse: empty, or the file is a lie. -/
def rejectMisfits : List String := (rejects.filter (fun rj => !isRefused rj)).map (·.name)

/-- The scenarios that were not refused exactly where they say they are. -/
def misfits : List String :=
  scenarios.filterMap fun sc =>
    if (rejectedParts sc.state sc.event).isEmpty == sc.refused then some sc.name else none

/-! ## The files -/

/-- The version the format carries, which is the one the encoder stamps events with. -/
def formatVersion : Nat := Encode.formatVersion

/-- A string, escaped the way JSON escapes one. -/
private def jsonStr (s : String) : String := (Lean.Json.str s).compress

/-- One vector as a JSON object, a field to a line. -/
private def caseJson (c : Case) : String :=
  let changes := c.changes.map fun (kind, id) =>
    "      { \"kind\": " ++ jsonStr kind ++ ", \"id\": " ++ jsonStr id ++ " }"
  let changesJson :=
    if changes.isEmpty then "[]"
    else "[\n" ++ String.intercalate ",\n" changes ++ "\n    ]"
  let rejected := String.intercalate ", " (c.rejected.map toString)
  "  {\n" ++
    "    \"name\": " ++ jsonStr c.name ++ ",\n" ++
    "    \"description\": " ++ jsonStr c.description ++ ",\n" ++
    "    \"stateHex\": " ++ jsonStr c.stateHex ++ ",\n" ++
    "    \"eventHex\": " ++ jsonStr c.eventHex ++ ",\n" ++
    "    \"expectedHex\": " ++ jsonStr c.expectedHex ++ ",\n" ++
    "    \"expectedHash\": " ++ jsonStr c.expectedHash ++ ",\n" ++
    "    \"changes\": " ++ changesJson ++ ",\n" ++
    "    \"rejected\": [" ++ rejected ++ "]\n" ++
  "  }"

/-- The whole of `vectors.json`: one array, one object per vector. -/
def vectorsJson : String :=
  "[\n" ++ String.intercalate ",\n" (vectors.map caseJson) ++ "\n]\n"

/-- One rejection as a JSON object, a field to a line. -/
private def rejectJson (rj : Reject) : String :=
  "  {\n" ++
    "    \"name\": " ++ jsonStr rj.name ++ ",\n" ++
    "    \"description\": " ++ jsonStr rj.description ++ ",\n" ++
    "    \"type\": " ++ jsonStr rj.type ++ ",\n" ++
    "    \"hex\": " ++ jsonStr rj.hex ++ "\n" ++
  "  }"

/-- The whole of `rejects.json`: one array, one object per byte string that must be refused. -/
def rejectsJson : String :=
  "[\n" ++ String.intercalate ",\n" (rejects.map rejectJson) ++ "\n]\n"

/-- The whole of `README.md`: what the file is, and when its version moves. -/
def readme : String :=
  String.intercalate "\n"
    [ "# Conformance vectors"
    , ""
    , "Generated by `resources gen-vectors` from the Lean core's own `step`; do not edit."
    , ""
    , "`vectors.json` is an array of vectors, each of which is a question the core has already"
    , "answered: `name` and `description` say what the case is for, `stateHex` is the canonical"
    , "encoding of a `State` the ledger can reach, `eventHex` is the canonical encoding of an"
    , "`Event` applied to it, `expectedHex` is the canonical encoding of the state `step`"
    , "produced, `expectedHash` is the SHA-256 of those bytes in hex — what a checkpoint commits"
    , "to — `changes` lists the constructor and entity key of every `Change` the operations"
    , "returned, in order, and `rejected` lists the indices of the event's parts that `applyOp`"
    , "refused, which are skipped rather than failing their neighbours. A port passes a vector"
    , "when, from `stateHex` and `eventHex` decoded with the same wire format, its own `step`"
    , "produces a state that encodes to exactly `expectedHex` — and so hashes to"
    , "`expectedHash` — with the same changes and the same refusals; the bytes are the contract,"
    , "because two implementations that agree on every field but one byte of encoding cannot"
    , "share a checkpoint."
    , ""
    , "`rejects.json` is the other half, and it is what makes the format a *name* rather than"
    , "merely a shape. Each entry is `name`, `description`, a `type` — `nat`, `int`, `string`,"
    , "`date`, `state` or `event` — and `hex`: a byte string that a conforming decoder of that"
    , "type has to refuse. Every vector above is a well-formed input, so a port could reproduce"
    , "all of them while accepting bytes no writer produces; and a checkpoint is the hash of a"
    , "state's canonical encoding, so a reader that takes a second spelling of one state will"
    , "re-encode it to something the sender never committed to, and two honest peers then"
    , "disagree about whether a checkpoint verifies. The shapes covered are overlong LEB128,"
    , "integer negative zero, an overlong length prefix, a map whose entries are not strictly"
    , "ascending, a key appearing twice, an entity filed under a key that is not its own id,"
    , "trailing bytes after a complete value, and a year, an exponent or a count of minor units"
    , "outside what this format carries."
    , ""
    , "## Where a log starts"
    , ""
    , "A log starts from a state, the first event carries it, and that is the whole of the"
    , "rule: an event whose parts are exactly one `snapshot` part, at **position 1** of the"
    , "order, is the state the fold begins from. `applyOp` refuses a `snapshot` everywhere,"
    , "including on an empty ledger, so a snapshot anywhere else is a part that is skipped like"
    , "any other invalid one, and an event carrying a snapshot beside something else is not a"
    , "beginning at all — its snapshot part is refused and its neighbours apply."
    , ""
    , "This used to be decided by asking whether the state the reader had folded so far looked"
    , "untouched, and that is a question about the reader rather than about the log. A browser"
    , "holds one key generation while a node holds every one, so after any revoke or key"
    , "rotation a browser replaying from the beginning skips every part written before the"
    , "rotation and arrives, part way along, at a state indistinguishable from a new ledger."
    , "One snapshot by anybody still in the realm then replaced the whole of what it displayed,"
    , "and since the snapshot can name its author an admin, every checkpoint they published"
    , "afterwards was trusted too."
    , ""
    , "So a reader of this format starts a fold at position 1 of its own order, or at the state"
    , "of a checkpoint it has verified, and nowhere else. And a reader that cannot read every"
    , "part of a realm between where it started and the head refuses to display that realm —"
    , "\"cannot verify: no checkpoint covers the parts you cannot read\" — rather than folding"
    , "around the gap: what it would show is not a ledger anybody wrote."
    , ""
    , "## Which realm an entry is in"
    , ""
    , "Every entity the ledger keeps says which realm it belongs to, and a part may only speak"
    , "about an entry of the realm it names. At format-version 5 that reached the last eight"
    , "kinds that had no realm at all: `Label`, `Party`, `PartyGroup`, `Trip`, `Rule`,"
    , "`ImportBatch` and `BlobState` each gained a trailing `realm` field, and the invoice"
    , "counter is keyed `<realm>:invoice:<year>`. A new entry is created in the realm the part"
    , "names; an existing one in another realm is refused. Two exceptions, and both are stated"
    , "as rules rather than as gaps: a member may revise the party record their own spending"
    , "lands on from any realm they are in, and the record keeps the realm it was introduced in;"
    , "and a `registerBlob` that re-seals a known file moves the record into the realm the part"
    , "names, because a receipt filed in one realm and attached to a payment in another has to"
    , "be readable by the people who can read that payment."
    , ""
    , "Format-version 6 finishes the list with the one kind it missed: `InvoiceState` gained a"
    , "trailing `realm`, written after the outlays the invoice bills for. `issueInvoice` records"
    , "the part's realm, and `setInvoiceStatus`, `settleInvoice` and `deleteInvoice` refuse an"
    , "invoice belonging to any other — so a counter is only ever wound back by the realm that"
    , "handed the number out. The per-realm counter made the missing field worse rather than"
    , "better: a draft issued in one realm, deleted from another, wound back a sequence that had"
    , "never issued it, and the next invoice there duplicated a number already sent."
    , ""
    , "The same version scopes the four lookups that still went by name and *selected*"
    , "rather than refused: an invoice's payer is the party of that name in the part's realm"
    , "(and a payer nobody knows is created there), a grant's bridge is the account of that name"
    , "in the realm being granted, the label a budget pins is one of that name in the budget's"
    , "realm, and the account a person settles a budget through is looked for among their"
    , "accounts in the budget's realm. A name is something anybody who may write an entry can"
    , "take, so a lookup by name across every realm is a lookup an outsider chooses the answer"
    , "to."
    , ""
    , "`format-version` holds a single integer, starting at 1. Bump it whenever these bytes mean"
    , "something new: a tag added to or renumbered within `Op`, `Change`, `Filter`, `Provenance`"
    , "or `PaymentRequest`, a field added to, removed from or reordered inside any encoded type,"
    , "a change to the primitives in `Core/Codec.lean`, or a change to the shape of"
    , "`vectors.json` itself. Do not bump it when only the vectors move: a new scenario, a"
    , "different refusal message, or a rounding decision inside `applyOp` changes what the"
    , "ledger decides, not how it is written down, and a port that reads the version to decide"
    , "whether it understands the file would be told the wrong thing. The version is the wire"
    , "format's, so it moves in the commit that moves the format, together with the fixed byte"
    , "strings in `Test/Encode.lean`."
    , ""
    , "## What a reader has to refuse"
    , ""
    , "Three numbers in this format have no type over them, and a port that reads them as they"
    , "come will turn six bytes into a computation nobody asked for. The rules are:"
    , ""
    , "* a `Date`'s year is between -999999 and 999999, its month is 1-12, its day is 1-31, and"
    , "  the three together are a date — so the thirty-first of February is refused. Lean's"
    , "  `PlainDate` carries a proof of the last three, so only the year is checked separately;"
    , "  a port whose date is three numbers checks all four."
    , "* a `Commodity`'s exponent is at most 18. The scale is ten to that power, so an exponent"
    , "  an author chose is a bignum an author chose the length of."
    , "* an `Amount`'s count of minor units has magnitude below 2^63, which is what fits the"
    , "  signed 64-bit column a port will store it in."
    , ""
    , "These are refused *while decoding* wherever a value is read for itself: a `Date`, a"
    , "`Commodity`, an `Amount`, anything holding one — a `Transaction`, an `Account`, an"
    , "`Invoice`, a `Rule`'s filter — and above all a `State`, which is what a checkpoint"
    , "commits to and what a `snapshot` carries."
    , ""
    , "An `Op` is the exception, and the exception is the important part. An operation is an"
    , "*intent*, and an intent is refused by the bounds check `step` makes before it applies"
    , "anything — the same check that refuses a name of 300 characters or a receipt line"
    , "claiming a thousand million units. It has to be that way round, because an event is one"
    , "author's set of parts and a part that cannot be applied is skipped rather than failing"
    , "its neighbours. A reader that refused the bytes would throw away every other realm's"
    , "part in the same event because of one it did not like, and which parts those are is"
    , "chosen by whoever composed it."
    , ""
    , "So: an event carrying an absurd year or exponent **decodes**, and the part carrying it"
    , "is then refused, which is exactly what `refuses-a-year-out-of-range` and"
    , "`refuses-an-exponent-out-of-range` below say. A port that refuses such an event while"
    , "reading it will fail those two vectors, and is also dropping parts it should have"
    , "applied. Everything else an operation carries is bounded the same way: identifiers and"
    , "names at 200 characters, free text at 2000, postings at 200 per transaction, receipt"
    , "lines at 500, participants at 100, a share's weight at 10000, a line's quantity at"
    , "100000, and any other list at 100000."
    , "" ]

end Vectors
end Api
end Resources
