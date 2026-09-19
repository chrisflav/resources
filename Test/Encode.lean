import Test.Sync
import Resources.Core.Encode
import Resources.Api.Vectors

/-!
# Encoding tests

Two things are checked here, and they are checked for different reasons.

The round trips are a sanity net under the proofs. `Codec.decode_encode` already
says that a lawful codec loses nothing, so a failure here would mean the value
built in this file is not the value the proof is about — a wrong tuple in an
`ofIso`, say, or a field left out. They also cover the three types whose law is
*not* proved: `State`, `Op` and `Event` all carry a `Std.HashMap` rebuild, and
`State.RebuildsCanonically` is checked here rather than proved.

The fixed byte strings are the other half. A proof says decode inverts encode;
it says nothing about *which* bytes were written, so an innocent-looking edit
could renumber a tag or reorder a field and every proof would still go through
while every checkpoint hash in the world changed. The literals below pin the
format down. If one of them fails, the format changed: decide whether that was
meant, and if it was, change the literal in the same commit.
-/

open Lean Resources

/-! ## Helpers -/

/-- Round-trips a value and checks that what comes back prints the same. -/
private def trip {α : Type} [Codec α] [Wellformed α] [Repr α] (r : Report) (name : String)
    (x : α) : Report :=
  match Codec.decode (α := α) (Codec.encode x) with
  | some y => checkEq r s!"round trip {name}" (reprStr y) (reprStr x)
  | none => check r s!"round trip {name}: decode failed" false

/--
Round-trips a value that has no `Repr`, checking that what comes back writes the
same bytes. Weaker than `trip` on its own; the laws in `Core/Encode.lean` supply
the rest.
-/
private def tripBytes {α : Type} [Codec α] [Wellformed α] (r : Report) (name : String)
    (x : α) : Report :=
  match Codec.decode (α := α) (Codec.encode x) with
  | some y => checkEq r s!"round trip {name}" (toHex (Codec.encode y)) (toHex (Codec.encode x))
  | none => check r s!"round trip {name}: decode failed" false

/-- Pins the exact bytes a value encodes to. -/
private def bytesAre {α : Type} [Codec α] (r : Report) (name : String) (x : α) (hex : String) :
    Report := checkEq r s!"bytes {name}" (toHex (Codec.encode x)) hex

/-! ## The values being encoded -/

private def eur : Commodity := Commodity.eur

private def day : Date := (Date.ofIso? "2026-03-09").getD default

private def otherDay : Date := (Date.ofIso? "2025-12-31").getD default

/-- A date at each end of what the decoder will take, and one step past each end. -/
private def ymd (y : Int) (m d : Nat) : Date := (Date.ofTriple (y, m, d)).getD default

private def lastYear : Date := ymd maxYear 12 31

private def firstYear : Date := ymd minYear 1 1

private def pastLastYear : Date := ymd (maxYear + 1) 1 1

private def beforeFirstYear : Date := ymd (minYear - 1) 1 1

/-- The finest commodity the decoder will take, and one place finer. -/
private def finest : Commodity := { code := "XAU", exponent := maxExponent }

private def tooFine : Commodity := { code := "XAU", exponent := maxExponent + 1 }

private def account : Account :=
  { id := ⟨"acc-giro"⟩, name := "Assets.Bank.DKB.Giro", kind := .asset,
    owner := Party.selfId, commodity := some eur, iban := some "DE02120300000000202051",
    note := some "the everyday one", closedOn := some otherDay, realm := Realm.selfId,
    bridgeOf := some ⟨"self"⟩, posters := [⟨"self"⟩, ⟨"anna"⟩],
    mirrorOf := some ⟨"acc-bridge"⟩ }

private def party : Party :=
  { id := ⟨"party-anna"⟩, name := "Anna", iban := some "DE89370400440532013000",
    email := some "anna@example.org", note := none, kind := "contact" }

private def label : Label := { id := ⟨"lab-trip"⟩, name := "trip", colour := some "#ff8800" }

private def posting : Posting :=
  { account := ⟨"acc-giro"⟩, amount := ⟨eur, -4990⟩, party := some ⟨"party-anna"⟩,
    note := some "half of dinner", origin := some "csv:17", tag := some "fee" }

private def txn : Transaction :=
  { id := ⟨"tx-0001"⟩, date := day, payee := some "Ristorante", narration := "dinner",
    state := .pending,
    postings := [posting, { account := ⟨"acc-food"⟩, amount := ⟨eur, 4990⟩ }],
    labels := [⟨"lab-trip"⟩], source := .imported ⟨"batch-7"⟩ "fp-abc",
    attachments := ["sha-1", "sha-2"],
    items := some [{ description := "half of dinner", qty := some 1, amount := ⟨eur, 4990⟩ }] }

private def filter : Filter :=
  .and (.or (.account "Assets") (.not (.label "private")))
    (.and (.dateFrom day) (.amountTo ⟨eur, 10000⟩))

private def rule : Rule :=
  { id := ⟨"rule-1"⟩, name := "groceries", filterSrc := "payee:REWE", filter := filter,
    setAccount := some "Expenses.Food", addLabels := ["food", "weekly"],
    setParty := none, priority := -3 }

private def group : PartyGroup := { name := "flat", members := ["anna", "ben"] }

private def trip' : Trip :=
  { id := "trip-zin", name := "Zinalrothorn", starts := otherDay, ends := day,
    payer := "party-anna", note := some "hut booked" }

private def batch : ImportBatch :=
  { id := ⟨"batch-7"⟩, profile := "dkb", filename := some "export.csv",
    account := some ⟨"acc-giro"⟩, stamp := "2026-03-09T10:00:00", total := 42, duplicates := 3 }

private def participant : Participant :=
  { owner := Party.selfId, name := "me", account := "Expenses.Travel", weight := 2 }

private def budget : Budget :=
  { id := ⟨"bud-1"⟩, name := "Budget.Zinalrothorn2026", note := some "the hut trip",
    closed := false }

private def attachment : Attachment :=
  { sha256 := "aabbcc", mime := "image/jpeg", bytes := 91234, origName := some "till.jpg",
    createdAt := "2026-03-09T10:00:00" }

/-- The same file as a synced node knows it: uploaded, and sealed under a realm key. -/
private def uploaded : Attachment :=
  { attachment with cipherHash := some "ddeeff",
                    wrappedKey := some "0000000000000000000000SELF:1:AAEC" }

private def lineItem : LineItem :=
  { description := "18 FORFAIT 1/2 PENSION", qty := some 18, amount := ⟨eur, 122400⟩ }

private def extracted : Extracted :=
  { merchant := some "Cabane", date := some day, total := some ⟨eur, 122400⟩,
    items := [], rawText := "18 FORFAIT…", extractor := "tesseract" }

private def itemGroup : Receipts.ItemGroup :=
  { items := [{ line := 1, qty := some 6 }, { line := 2, qty := none }], into := "acc-food" }

private def invoice : Invoice :=
  { id := ⟨"inv-1"⟩, number := "2026-0007", issued := otherDay, due := day,
    payerId := some ⟨"party-anna"⟩, payerName := "Anna", commodity := eur,
    reference := "RF18539007547034", status := .sent, note := some "hut share",
    settledTxn := none, payment := .epc "Christian" "DE0212030000" (some "GENODEF1XXX"),
    sourceAccount := some "Budget.Zinalrothorn2026", budgetId := some ⟨"bud-1"⟩,
    pendingTxn := some ⟨"tx-0002"⟩,
    lines := [{ description := "nights", qtyMilli := 18000, unitPrice := ⟨eur, 6800⟩,
                taxBp := 1900 }] }

private def member : Member := { id := ⟨"anna"⟩, name := "Anna", party := ⟨"party-anna"⟩ }

private def realm : Realm :=
  { id := ⟨"realm-1"⟩, name := "flat", members := [(⟨"anna"⟩, .admin), (⟨"ben"⟩, .viewer)],
    generation := 3 }

private def blobState : BlobState :=
  { file := attachment, extracted := extracted, items := [lineItem],
    registeredBy := ⟨"anna"⟩ }

private def budgetState : BudgetState :=
  { budget := budget, participants := [participant], realm := ⟨"realm-1"⟩,
    account := ⟨"acc-budget"⟩, label := ⟨"lab-trip"⟩ }

/-- A state with something in most of its maps. -/
private def sampleState : State :=
  { State.init with
    accounts := (State.init.accounts.insert "acc-giro" account).insert "acc-food"
      { id := ⟨"acc-food"⟩, name := "Expenses.Food", kind := .expense }
    parties := State.init.parties.insert "party-anna" party
    labels := State.init.labels.insert "lab-trip" label
    groups := State.init.groups.insert "flat" group
    trips := State.init.trips.insert trip'.name trip'
    rules := State.init.rules.insert "rule-1" rule
    txns := State.init.txns.insert "tx-0001" txn
    budgets := State.init.budgets.insert "bud-1" budgetState
    invoices := State.init.invoices.insert "inv-1" { invoice := invoice, sources := [⟨"tx-0001"⟩] }
    blobs := State.init.blobs.insert "aabbcc" blobState
    batches := State.init.batches.insert "batch-7" batch
    counters := State.init.counters.insert "invoice:2026" 7
    fingerprints := (State.init.fingerprints.insert "fp-abc").insert "fp-def" }

/-- The same state, with every map filled in the opposite order. -/
private def shuffledState : State :=
  { sampleState with
    accounts := (({} : Std.HashMap String Account).insert "acc-food"
        { id := ⟨"acc-food"⟩, name := "Expenses.Food", kind := .expense }).insert
      "acc-giro" account
    fingerprints := (({} : Std.HashSet String).insert "fp-def").insert "fp-abc" }

private def ops : List (String × Op) :=
  [ ("createRealm", .createRealm realm)
  , ("putAccount", .putAccount account)
  , ("mergeAccounts", .mergeAccounts ⟨"a"⟩ ⟨"b"⟩)
  , ("setAccountRights", .setAccountRights ⟨"a"⟩ [⟨"anna"⟩])
  , ("putRule", .putRule rule)
  , ("putTransaction", .putTransaction txn)
  , ("mergeTransactions", .mergeTransactions [⟨"t1"⟩, ⟨"t2"⟩] ⟨"t3"⟩ (some "p") none [⟨"a"⟩])
  , ("divideByItems", .divideByItems ⟨"t1"⟩ [itemGroup] [⟨"t2"⟩, ⟨"t3"⟩])
  , ("voidClaim", .voidClaim ⟨"t1"⟩ (some (⟨"a"⟩, ⟨"t9"⟩, day)))
  , ("allocate", .allocate ⟨"bud-1"⟩ [participant] eur day (some Party.selfId) ⟨"t1"⟩
      [⟨"t2"⟩] ⟨"lab-trip"⟩)
  , ("closeBudget", .closeBudget ⟨"bud-1"⟩ (some [participant]) eur none day ⟨"t1"⟩ []
      ⟨"lab-trip"⟩)
  , ("issueInvoice", .issueInvoice invoice [⟨"tx-0001"⟩])
  , ("recordExtraction", .recordExtraction "aabbcc" extracted)
  , ("forgetBlob", .forgetBlob "aabbcc")
  , ("grant", .grant Realm.selfId ⟨"anna"⟩ .viewer account)
  , ("payClaim", .payClaim ⟨"tx-0001"⟩ ⟨"tx-0002"⟩ day)
  , ("rotateRealmKey", .rotateRealmKey Realm.selfId)
  , ("snapshot", .snapshot sampleState) ]

private def changes : List (String × Change) :=
  [ ("realm", .realm realm)
  , ("accountDeleted", .accountDeleted ⟨"a"⟩)
  , ("rule", .rule rule)
  , ("txn", .txn txn)
  , ("blob", .blob blobState)
  , ("counter", .counter "invoice:2026" 7)
  , ("fingerprint", .fingerprint "fp-abc") ]

private def event : Event :=
  { id := "ev-1", author := ⟨"anna"⟩, composedAt := "2026-03-09T10:00:00", basedOn := 12,
    parts := [{ realm := Realm.selfId, op := .putAccount account },
              { realm := ⟨"realm-1"⟩, op := .snapshot sampleState }] }

/-! ## The group -/

/--
Every type an event or a state holds, through its own encoding and back, plus
the byte strings that pin the format.
-/
def encodeTests (r : Report) : Report := Id.run do
  let mut r := r

  /- ## Primitives -/
  r := trip r "Nat zero" (0 : Nat)
  r := trip r "Nat one byte" (127 : Nat)
  r := trip r "Nat two bytes" (300 : Nat)
  r := trip r "Nat large" (123456789012345 : Nat)
  r := trip r "Int zero" (0 : Int)
  r := trip r "Int negative" (-300 : Int)
  r := trip r "Int positive" (1250 : Int)
  r := trip r "Bool false" false
  r := trip r "Bool true" true
  r := trip r "UInt8" (0xfe : UInt8)
  r := trip r "String empty" ""
  r := trip r "String ascii" "hello"
  r := trip r "String unicode" "Zinalrothorn · 3562 m — Wallis"
  r := tripBytes r "ByteArray" (ByteArray.mk #[0, 1, 2, 255])
  r := trip r "Option none" (none : Option String)
  r := trip r "Option some" (some "x" : Option String)
  r := trip r "List empty" ([] : List Nat)
  r := trip r "List" ([1, 2, 300] : List Nat)
  r := trip r "Prod" (("a", 1) : String × Nat)
  r := trip r "nested" ([(some 1, "a"), (none, "b")] : List (Option Int × String))

  /- ## Dates and identifiers -/
  r := trip r "Date" day
  r := trip r "Date other" otherDay
  r := trip r "Date epoch" ((Date.ofIso? "1970-01-01").getD default)
  r := trip r "Date early" ((Date.ofIso? "0001-01-01").getD default)
  r := trip r "AccountId" (⟨"acc-giro"⟩ : AccountId)
  r := trip r "TxId" (⟨"tx-0001"⟩ : TxId)
  r := trip r "MemberId" Member.selfId
  r := trip r "RealmId" Realm.selfId

  /- ## Money -/
  r := trip r "Commodity" eur
  r := trip r "Commodity zero exponent" (Commodity.ofCode "JPY")
  r := trip r "Amount" (Amount.mk eur (-4990))

  /- ## The ledger -/
  r := trip r "AccountKind" AccountKind.expense
  r := trip r "Account" account
  r := trip r "Party" party
  r := trip r "Label" label
  r := trip r "Posting" posting
  r := trip r "Provenance manual" (Provenance.manual "cli")
  r := trip r "Provenance imported" (Provenance.imported ⟨"batch-7"⟩ "fp-abc")
  r := trip r "Provenance derived" (Provenance.derived ⟨"rule-1"⟩)
  r := trip r "TxnState" TxnState.pending
  r := trip r "Transaction" txn
  -- The three answers a transaction can give about what it paid for, which the
  -- bytes have to keep apart: these lines, no printed line at all, and nothing
  -- said either way.
  r := trip r "Transaction paying for no printed line" { txn with items := some [] }
  r := trip r "Transaction that was never divided" { txn with items := none }

  /- ## Filters -/
  r := trip r "Filter all" Filter.all
  r := trip r "Filter leaf" (Filter.commodity "EUR")
  r := trip r "Filter nested" filter
  r := trip r "Filter deep"
    (Filter.not (.not (.not (.and (.all) (.or (.text "a") (.not (.tag "b")))))))

  /- ## Entities -/
  r := trip r "PartyGroup" group
  r := trip r "Trip" trip'
  r := trip r "Rule" rule
  r := trip r "ImportBatch" batch
  r := trip r "Participant" participant
  r := trip r "Budget" budget

  /- ## Receipts -/
  r := trip r "Attachment" attachment
  r := trip r "Attachment uploaded" uploaded
  r := trip r "LineItem" lineItem
  r := trip r "Extracted" extracted
  r := trip r "ItemShare" ({ line := 3, qty := some 2 } : Receipts.ItemShare)
  r := trip r "ItemGroup" itemGroup

  /- ## Invoices -/
  r := trip r "PaymentRequest epc" (PaymentRequest.epc "C" "DE02" (some "GENO"))
  r := trip r "PaymentRequest link" (PaymentRequest.link "https://example.org/pay")
  r := trip r "InvoiceLine"
    ({ description := "nights", qtyMilli := 18000, unitPrice := ⟨eur, 6800⟩,
       taxBp := 1900 } : InvoiceLine)
  r := trip r "InvoiceStatus" InvoiceStatus.paid
  r := trip r "Invoice" invoice

  /- ## Members, realms and the state's parts -/
  r := trip r "RealmRole" RealmRole.admin
  r := trip r "Member" member
  r := trip r "Realm" realm
  r := trip r "BudgetState" budgetState
  r := trip r "InvoiceState"
    ({ invoice := invoice, sources := [⟨"tx-0001"⟩] } : InvoiceState)
  r := trip r "BlobState" blobState
  r := tripBytes r "StateWire" sampleState.wire

  /- ## Operations, changes and events -/
  for (name, op) in ops do
    r := tripBytes r s!"Op.{name}" op
  for (name, change) in changes do
    r := tripBytes r s!"Change.{name}" change
  r := tripBytes r "Part" ({ realm := Realm.selfId, op := .putAccount account } : Part)
  r := tripBytes r "Event" event

  /- ## The state, and the rebuild its law is stated up to -/
  r := tripBytes r "State" sampleState
  r := check r "a decoded state is canonically the state"
    (match Codec.decode (Codec.encode sampleState) with
     | some (s : State) => s.canonical == sampleState.canonical
     | none => false)
  r := check r "State.RebuildsCanonically holds for this state"
    (sampleState.wire.state.canonical == sampleState.canonical)
  r := check r "and for the empty state"
    (State.init.wire.state.canonical == State.init.canonical)
  r := checkEq r "insertion order does not reach the bytes"
    (Encode.hashState shuffledState) (Encode.hashState sampleState)
  r := check r "two different states hash differently"
    (Encode.hashState sampleState != Encode.hashState State.init)
  r := checkEq r "hashing a state is hashing its bytes"
    (Encode.hashState sampleState) (Sha256.hexBytes (Codec.encode sampleState))
  r := checkEq r "hashing an event is hashing its bytes"
    (Encode.hashEvent event) (Sha256.hexBytes (Codec.encode event))
  r := check r "a signature over one event does not cover another"
    (Encode.hashEvent event != Encode.hashEvent { event with basedOn := 13 })

  /- ## Fixed bytes: the format itself -/
  r := bytesAre r "Nat 0" (0 : Nat) "00"
  r := bytesAre r "Nat 127" (127 : Nat) "7f"
  r := bytesAre r "Nat 128" (128 : Nat) "8001"
  r := bytesAre r "Nat 300" (300 : Nat) "ac02"
  r := bytesAre r "Int 300" (300 : Int) "00ac02"
  r := bytesAre r "Int -300" (-300 : Int) "01ac02"
  r := bytesAre r "Int 0" (0 : Int) "0000"
  r := bytesAre r "Bool false" false "00"
  r := bytesAre r "Bool true" true "01"
  r := bytesAre r "String empty" "" "00"
  r := bytesAre r "String hi" "hi" "026869"
  r := bytesAre r "String two-byte utf8" "é" "02c3a9"
  r := bytesAre r "Option none" (none : Option String) "00"
  r := bytesAre r "Option some" (some "hi" : Option String) "01026869"
  r := bytesAre r "List" ([1, 2, 300] : List Nat) "030102ac02"
  r := bytesAre r "Prod" (("hi", 7) : String × Nat) "02686907"
  r := bytesAre r "Commodity EUR" eur "0345555202"
  r := bytesAre r "Amount -12.50 EUR" (Amount.mk eur (-1250)) "034555520201e209"
  r := bytesAre r "Date 2026-03-09" day "00ea0f00030009"
  r := bytesAre r "AccountKind expense" AccountKind.expense "04"
  r := bytesAre r "TxnState pending" TxnState.pending "01"
  r := bytesAre r "InvoiceStatus paid" InvoiceStatus.paid "02"
  r := bytesAre r "RealmRole admin" RealmRole.admin "01"
  r := bytesAre r "Provenance manual" (Provenance.manual "x") "000178"
  r := bytesAre r "PaymentRequest link" (PaymentRequest.link "u") "010175"
  -- The realm is the trailing field every entity gained at format-version 5:
  -- written last, so a port that reads the old shape stops exactly where the new
  -- one carries on.
  r := bytesAre r "Label" ({ id := ⟨"l"⟩, name := "n", colour := none } : Label)
    ("016c016e00" ++ "1a3030303030303030303030303030303030303030303053454c46")
  r := bytesAre r "Account bare" ({ id := ⟨"a"⟩, name := "n", kind := .asset } : Account)
    ("0161016e001a3030303030303030303030303030303030303030303053454c4600000000" ++
      "1a3030303030303030303030303030303030303030303053454c46000000")
  -- The last two fields are the ones a synced node fills in: the hash of the
  -- ciphertext it uploaded, and the per-blob key sealed under a realm key. A
  -- local-only store writes two `none` bytes there, which is what a port that
  -- does not sync still has to write.
  r := bytesAre r "Attachment local" attachment
    ("066161626263630a696d6167652f6a706567e2c805010874696c6c2e6a7067" ++
      "13323032362d30332d30395431303a30303a30300000")
  r := bytesAre r "Attachment uploaded" uploaded
    ("066161626263630a696d6167652f6a706567e2c805010874696c6c2e6a7067" ++
      "13323032362d30332d30395431303a30303a3030010664646565666601" ++
      "213030303030303030303030303030303030303030303053454c463a313a41414543")
  r := bytesAre r "Op.deleteGroup" (Op.deleteGroup "g") "0a0167"
  r := bytesAre r "Change.fingerprint" (Change.fingerprint "f") "180166"
  r := bytesAre r "Filter all" Filter.all "00"
  r := bytesAre r "Filter not label" (Filter.not (.label "x")) "0f060178"
  r := checkEq r "the empty state's hash" (Encode.hashState {})
    "5322fecfc92a5e3248a297a3df3eddfb9bd9049504272e4f572b87fa36d4b3bd"
  -- The two records that grew at format-version 4, and the claims a budget grew
  -- at 8. New fields are written last, so a port that reads the old shape stops
  -- exactly where the new one carries on; these pin where "last" is.
  r := bytesAre r "BudgetState bare"
    ({ budget := { id := ⟨"b"⟩, name := "n", note := none, closed := false } } : BudgetState)
    ("0162016e000000" ++ "1a3030303030303030303030303030303030303030303053454c4600" ++ "0000")
  r := bytesAre r "BudgetState with a cost somebody took"
    ({ budget := { id := ⟨"b"⟩, name := "n", note := none, closed := false }
       claims := [{ txn := ⟨"t"⟩, member := ⟨"m"⟩ }] } : BudgetState)
    ("0162016e000000" ++ "1a3030303030303030303030303030303030303030303053454c4600" ++
      "00" ++ "01" ++ "0174" ++ "016d")
  -- And the record that grew at format-version 6: an invoice knows the realm it
  -- was issued in, and it is written last, after the outlays it bills for.
  r := bytesAre r "InvoiceState bare"
    ({ invoice := { id := ⟨"i"⟩, number := "n", issued := day, due := day, payerId := none
                    payerName := "", commodity := eur, reference := "", status := .draft
                    note := none, settledTxn := none, payment := .link ""
                    sourceAccount := none, budgetId := none, pendingTxn := none
                    lines := [] }
       sources := [] } : InvoiceState)
    ("0169016e" ++ "00ea0f0003000900ea0f00030009" ++ "0000" ++ "0345555202" ++
      "00000000" ++ "0100" ++ "00000000" ++ "00" ++
      "1a3030303030303030303030303030303030303030303053454c46")
  r := bytesAre r "BlobState bare"
    ({ file := { sha256 := "s", mime := "m", bytes := 0, origName := none
                 createdAt := "" } } : BlobState)
    ("0173016d0000000000" ++ "000000000000" ++ "00" ++ "0473656c66" ++
      "1a3030303030303030303030303030303030303030303053454c46")

  /- ## Bytes that must be refused
     A decoder that takes more than the writer produces is a decoder that gives
     one value two names, and a checkpoint is a name. These are the spellings
     that used to be accepted. -/
  let refuses (name : String) (hex : String) : Report → Report := fun r =>
    match Api.Vectors.ofHex? hex with
    | none => check r s!"{name}: the test's own bytes are hex" false
    | some bs => check r s!"refuses {name}" (Codec.decode (α := Nat) bs).isNone
  r := refuses "an overlong zero" "8000" r
  r := refuses "an overlong one" "8100" r
  r := refuses "a doubly overlong zero" "808000" r
  r := check r "a canonical zero is still read"
    (Codec.decode (α := Nat) (Codec.encode (0 : Nat)) == some 0)
  r := check r "negative zero is refused"
    (match Api.Vectors.ofHex? "0100" with
     | some bs => (Codec.decode (α := Int) bs).isNone
     | none => false)
  r := check r "and positive zero is not"
    (match Api.Vectors.ofHex? "0000" with
     | some bs => Codec.decode (α := Int) bs == some 0
     | none => false)
  r := check r "trailing bytes are refused"
    (match Api.Vectors.ofHex? "00007f" with
     | some bs => (Codec.decode (α := Int) bs).isNone
     | none => false)
  r := check r "an overlong length prefix is refused"
    (match Api.Vectors.ofHex? "820068690000" with
     | some bs => (Codec.decode (α := String) bs).isNone
     | none => false)
  -- A state whose entries are out of order, repeated, or filed under a key that
  -- is not the entity's own id: three shapes `State.wire` never writes.
  let shuffled : StateWire :=
    { sampleState.wire with labels := sampleState.wire.labels.reverse ++ [] }
  let doubled : StateWire :=
    { sampleState.wire with parties := sampleState.wire.parties ++ sampleState.wire.parties }
  let misfiled : StateWire :=
    { sampleState.wire with
        labels := sampleState.wire.labels.map (fun p => ("not-its-id", p.2)) }
  r := check r "a state whose entries are not sorted is refused"
    ((Codec.decode (α := State) (Codec.encode shuffled)).isNone ||
      sampleState.wire.labels.length < 2)
  r := check r "a state with a key twice is refused"
    ((Codec.decode (α := State) (Codec.encode doubled)).isNone ||
      sampleState.wire.parties.isEmpty)
  r := check r "a state filed under a key that is not the entity's id is refused"
    ((Codec.decode (α := State) (Codec.encode misfiled)).isNone ||
      sampleState.wire.labels.isEmpty)
  r := check r "and the state it was made from is not"
    (Codec.decode (α := State) (Codec.encode sampleState)).isSome

  /- ## Numbers that must be refused
     Overlong bytes are a *shape* nobody writes. These are a *size* somebody
     writes on purpose: a year, a number of decimal places or a count of minor
     units far outside anything a ledger means, which the first thing that
     renders them turns into a bignum with millions of digits. The writer can
     produce all of them, which is why the check is `Wellformed` and not the
     round-trip law — see `Core/Codec.lean`. -/
  let takes {α : Type} [Codec α] [Wellformed α] (name : String) (x : α) : Report → Report :=
    fun r => check r s!"takes {name}" (Codec.decode (α := α) (Codec.encode x)).isSome
  let refusesValue {α : Type} [Codec α] [Wellformed α] (name : String) (x : α) :
      Report → Report :=
    fun r => check r s!"refuses {name}" (Codec.decode (α := α) (Codec.encode x)).isNone
  r := takes "the last year a date may name" lastYear r
  r := takes "the first year a date may name" firstYear r
  r := refusesValue "a year past the last one" pastLastYear r
  r := refusesValue "a year before the first one" beforeFirstYear r
  r := takes "the finest commodity there may be" finest r
  r := refusesValue "a commodity with one decimal place too many" tooFine r
  r := takes "the largest count of minor units" (Amount.mk eur (2 ^ 63 - 1)) r
  r := takes "and the smallest" (Amount.mk eur (-(2 ^ 63) + 1)) r
  r := refusesValue "a count of minor units that overflows a 64-bit column"
    (Amount.mk eur (2 ^ 63)) r
  r := refusesValue "and the same going the other way" (Amount.mk eur (-(2 ^ 63))) r
  r := refusesValue "an amount in a commodity nothing can scale" (Amount.mk tooFine 1) r
  -- A bound inside a record is the record's bound: this is the rule every
  -- instance in `Core/Encode.lean` follows, checked on the three shapes a
  -- reader actually meets.
  r := refusesValue "a transaction dated outside the calendar"
    ({ txn with date := pastLastYear }) r
  r := refusesValue "a receipt line priced in a commodity nothing can scale"
    ({ lineItem with amount := ⟨tooFine, 1⟩ }) r
  r := refusesValue "a rule whose filter compares against such an amount"
    ({ rule with filter := .amountTo ⟨tooFine, 1⟩ }) r
  -- The checkpoint door. A state is believed rather than applied, so this is
  -- the only place the numbers inside one are ever questioned.
  let badState : State :=
    { sampleState with txns := sampleState.txns.insert "tx-0001" { txn with date := pastLastYear } }
  r := refusesValue "a state holding a transaction dated outside the calendar" badState r
  r := refusesValue "an event carrying a snapshot of one"
    ({ event with parts := [{ realm := Realm.selfId, op := .snapshot badState }] }) r
  -- And the door that is not this one. An operation is an intent, and an intent
  -- is refused by `checkBounds` when it is applied; `refuses-a-year-out-of-range`
  -- in `conformance/` is the vector that says so, and it could not exist if the
  -- bytes below did not decode.
  let badEvent : Event :=
    { event with parts := [{ realm := Realm.selfId,
                             op := .putTransaction { txn with date := pastLastYear } }] }
  r := takes "an event whose operation carries such a date" badEvent r
  r := check r "and applying it refuses the part rather than computing with it"
    ((step State.init badEvent).1 == State.init)
  -- Month and day. The `Date` type carries a proof that these are a date, so the
  -- refusal is `Date.ofTriple`'s rather than `Wellformed`'s — a port whose date
  -- is three numbers has to make all three checks itself.
  let refusesTriple (name : String) (y m d : Int) : Report → Report := fun r =>
    check r s!"refuses {name}"
      (Codec.decode (α := Date) (Codec.encode (y, m, d))).isNone
  r := refusesTriple "a thirteenth month" 2026 13 1 r
  r := refusesTriple "a zeroth month" 2026 0 1 r
  r := refusesTriple "a thirty-second day" 2026 1 32 r
  r := refusesTriple "the thirty-first of February" 2026 2 31 r
  r := check r "and takes the twenty-eighth"
    (Codec.decode (α := Date) (Codec.encode ((2026 : Int), (2 : Int), (28 : Int)))).isSome

  return r
