import Resources.Core.Codec
import Resources.Core.Event
import Resources.Crypto.Sha256

/-!
# The ledger's canonical bytes

An instance of `Codec` for every type an `Event` or a `State` is made of, and
the two hashes the rest of the system asks for: `Encode.hashState`, which a
checkpoint commits to, and `Encode.hashEvent`, which a signature covers.

Almost everything here is one line of structure and one line of proof. A
structure is carried into nested products by `Codec.ofIso` and its law follows
from the product law by `rfl` on the round trip, which holds definitionally
because Lean's structures have eta. An enumeration is carried into `Nat` by
`Codec.ofRetract` and its law is `cases … <;> rfl`. Only the inductives with
payloads — `Provenance`, `PaymentRequest`, `Filter`, `Op`, `Change` — are
written out, as a tag byte and a payload, and even those are proved by one
`cases … <;> simp`.

Two things do not fit that pattern, and both are documented where they appear.

`Filter` is recursive, so its reader takes fuel; the fuel handed in is the
length of the remaining input, which is always enough because a filter's nesting
depth never exceeds the number of bytes it was written as. It is also the one
place this decoder is not linear: measuring the input is one walk per filter
read, so a state holding many rules costs the product. Every other length the
reader asks about is `Codec.splitExactly`, which walks only what it consumes.

`State` holds `Std.HashMap`s. A hash map has no canonical value — its iteration
order is a fact about the hash function, not about the ledger — so it is written
as its entries in key order, which is what `sortedPairs` already gives `Core`,
and read back by inserting them again. What comes back holds exactly the same
entries, but it is not the same `Std.HashMap` value, and no `LawfulCodec State`
instance is claimed. What is proved instead is exact: `State.ofBytes_toBytes`
says the reader returns `s.wire.state`, the state rebuilt from `s`'s own sorted
entries. That the rebuild is indistinguishable — `State.canonical` cannot tell
it from `s` — is `State.RebuildsCanonically`, which is a statement about
`Std.HashMap.insert` rather than about this encoding, is not proved here, and is
checked by the tests. The same `.wire.state` appears in `Op.canon`, `Part.canon`
and `Event.canon`, because `Op.snapshot` carries a whole `State`.

Reading a state back is also the one place here that refuses bytes a writer
could produce, and it has to be. `StateWire.canonical` insists the entries are
strictly ascending by key and that every entity is filed under its own id, which
is what `State.wire` writes and what a hand-assembled `State` need not be: a
decoded state holding `accounts["A"] = { id := "B", … }` made "the account with
this id" a question with two answers, and a state whose entries arrived unsorted
or twice re-encoded to bytes its own hash was not taken over. `State.Canonical`
is the side condition that carries through `Op.Canonical`, `Part.Canonical` and
`Event.Canonical` to the round-trip theorems.

Hashes are taken over the bytes, so a checkpoint is reproducible: `State.wire`
sorts, nothing else looks at a map, and the format has no padding, no alignment
and no platform-dependent width.

Every type here also gets a `Wellformed` instance, which is what `Codec.decode`
consults before it hands a value back. The rule those instances follow is worth
stating once: **a record's bound is the bound of exactly the fields its encoding
writes, in the same order.** So each instance below mirrors the `ofIso` tuple
beside it, field for field, and a field added to an encoding without being added
here does not quietly escape the check — the tuple no longer matches and it does
not compile. Only three types answer anything but `true` of their own accord:
`Date`, `Commodity` and `Amount`, and `Core/Event.lean` says why.

`Op` is the one deliberate hole in that rule, and `Op.wf` says why: an operation
is an intent, and `Core/Apply.lean`'s `checkBounds` is where an intent is
refused. Everything a *state* holds is bounded here, because nothing checks a
state before it is believed.
-/

open Std.Time

namespace Resources

/-! ## Dates

A date is written as its three components rather than as its ISO string, and
that is a deliberate trade. The ISO form would be prettier in a hexdump, but
`Date.ofIso?` is Std's date parser and `Date.toIso` is Std's date formatter, and
that the two invert each other is not something this file can prove — it would
leave every type that holds a date, which is most of them, with an unproved law.
The components are the same information, they are canonical in the same way, and
`PlainDate.ofYearMonthDay?` inverts them in three lines.
-/

/-- A date as its year, month and day. -/
def Date.triple (d : Date) : Int × Int × Int := (d.year, d.month.val, d.day.val)

/-- Rebuilds a date, refusing a month, a day or a combination that is not one. -/
def Date.ofTriple : Int × Int × Int → Option Date
  | (y, m, dd) =>
    match (Internal.Bounded.LE.ofInt (lo := 1) (hi := 12) m : Option Month.Ordinal),
        (Internal.Bounded.LE.ofInt (lo := 1) (hi := 31) dd : Option Day.Ordinal) with
    | some mo, some da => PlainDate.ofYearMonthDay? y mo da
    | _, _ => none

instance : Codec Date := Codec.ofRetract Date.triple Date.ofTriple

instance : LawfulCodec Date :=
  Codec.lawful_ofRetract (fun d => by
    have hm : (Internal.Bounded.LE.ofInt (lo := 1) (hi := 12) d.month.val
        : Option Month.Ordinal) = some d.month := by
      rw [Internal.Bounded.LE.ofInt, dif_pos d.month.property]
      rfl
    have hd : (Internal.Bounded.LE.ofInt (lo := 1) (hi := 31) d.day.val
        : Option Day.Ordinal) = some d.day := by
      rw [Internal.Bounded.LE.ofInt, dif_pos d.day.property]
      rfl
    simp only [Date.triple, Date.ofTriple, hm, hd, PlainDate.ofYearMonthDay?]
    exact (dif_pos d.valid).trans rfl)

/--
A date the ledger will take: one whose year is between `minYear` and `maxYear`.

The month and the day are not checked here because they are already refused
while the bytes are being read: `Date.ofTriple` puts them through
`Bounded.LE.ofInt` for 1–12 and 1–31 and then through `PlainDate.ofYearMonthDay?`,
which is what rules out the thirty-first of February. A port has no type carrying
that proof and has to make all three checks itself.
-/
instance : Wellformed Date := ⟨Date.inRange⟩

/-! ## Identifiers -/

/-- Declares the codec for a string-backed identifier: the string, and nothing else. -/
macro "codec_id " id:ident : command =>
  `(instance : Codec $id := Codec.ofIso (fun x => x.val) (fun s => ⟨s⟩)
    instance : LawfulCodec $id := Codec.lawful_ofIso (fun _ => rfl)
    instance : Wellformed $id := Wellformed.ofIso (fun x => x.val))

codec_id AccountId
codec_id TxId
codec_id LabelId
codec_id PartyId
codec_id TokenId
codec_id InvoiceId
codec_id BatchId
codec_id StagedId
codec_id RuleId
codec_id BudgetId
codec_id RealmId
codec_id MemberId

/-! ## Commodities and amounts -/

instance : Codec Commodity :=
  Codec.ofIso (fun c => (c.code, c.exponent)) (fun (code, exponent) => { code, exponent })

instance : LawfulCodec Commodity := Codec.lawful_ofIso (fun _ => rfl)

/-- A commodity whose minor unit has few enough places that `10 ^ exponent` is a number. -/
instance : Wellformed Commodity := ⟨Commodity.inRange⟩

instance : Codec Amount :=
  Codec.ofIso (fun a => (a.commodity, a.minor)) (fun (commodity, minor) => { commodity, minor })

instance : LawfulCodec Amount := Codec.lawful_ofIso (fun _ => rfl)

/-- An amount in a usable commodity, counted in a number that fits a 64-bit column. -/
instance : Wellformed Amount := ⟨Amount.inRange⟩

/-! ## Accounts, parties, labels -/

/-- The tag of each account kind, in declaration order. -/
def AccountKind.tag : AccountKind → Nat
  | .asset => 0 | .liability => 1 | .equity => 2 | .income => 3 | .expense => 4

/-- Inverse of `AccountKind.tag`. -/
def AccountKind.ofTag : Nat → Option AccountKind
  | 0 => some .asset | 1 => some .liability | 2 => some .equity
  | 3 => some .income | 4 => some .expense | _ => none

instance : Codec AccountKind := Codec.ofRetract AccountKind.tag AccountKind.ofTag

instance : LawfulCodec AccountKind := Codec.lawful_ofRetract (fun k => by cases k <;> rfl)

instance : Wellformed AccountKind := Wellformed.ofIso AccountKind.tag

instance : Codec Account :=
  Codec.ofIso
    (fun a => (a.id, a.name, a.kind, a.owner, a.commodity, a.iban, a.note, a.closedOn,
      a.realm, a.bridgeOf, a.posters, a.mirrorOf))
    (fun (id, name, kind, owner, commodity, iban, note, closedOn, realm, bridgeOf, posters,
        mirrorOf) =>
      { id, name, kind, owner, commodity, iban, note, closedOn, realm, bridgeOf, posters,
        mirrorOf })

instance : LawfulCodec Account := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Account :=
  Wellformed.ofIso
    (fun a => (a.id, a.name, a.kind, a.owner, a.commodity, a.iban, a.note, a.closedOn,
      a.realm, a.bridgeOf, a.posters, a.mirrorOf))

instance : Codec Party :=
  Codec.ofIso
    (fun p => (p.id, p.name, p.iban, p.email, p.note, p.kind, p.realm))
    (fun (id, name, iban, email, note, kind, realm) =>
      { id, name, iban, email, note, kind, realm })

instance : LawfulCodec Party := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Party :=
  Wellformed.ofIso (fun p => (p.id, p.name, p.iban, p.email, p.note, p.kind, p.realm))

instance : Codec Label :=
  Codec.ofIso (fun l => (l.id, l.name, l.colour, l.realm))
    (fun (id, name, colour, realm) => { id, name, colour, realm })

instance : LawfulCodec Label := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Label := Wellformed.ofIso (fun l => (l.id, l.name, l.colour, l.realm))

/-! ## Postings and transactions -/

instance : Codec Posting :=
  Codec.ofIso
    (fun p => (p.account, p.amount, p.party, p.note, p.origin, p.tag))
    (fun (account, amount, party, note, origin, tag) =>
      { account, amount, party, note, origin, tag })

instance : LawfulCodec Posting := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Posting :=
  Wellformed.ofIso (fun p => (p.account, p.amount, p.party, p.note, p.origin, p.tag))

/-- Tag, then payload, one tag per constructor in declaration order. -/
def encProvenance : Provenance → List UInt8
  | .manual a => tagged 0 (Codec.toBytes a)
  | .imported b f => tagged 1 (Codec.toBytes (b, f))
  | .derived r => tagged 2 (Codec.toBytes r)

/-- Inverse of `encProvenance`. -/
def decProvenance (bs : List UInt8) : Option (Provenance × List UInt8) :=
  match decNat bs with
  | some (0, rest) => readAs String rest .manual
  | some (1, rest) => readAs (BatchId × String) rest (fun (b, f) => .imported b f)
  | some (2, rest) => readAs RuleId rest .derived
  | _ => none

instance : Codec Provenance where
  toBytes := encProvenance
  ofBytes := decProvenance

instance : LawfulCodec Provenance where
  ofBytes_toBytes p rest := by
    show decProvenance (encProvenance p ++ rest) = some (p, rest)
    cases p <;> simp [encProvenance, decProvenance, tagged, List.append_assoc]

/-- The bound of each constructor's payload, one line per tag above. -/
def Provenance.wf : Provenance → Bool
  | .manual a => Wellformed.wf a
  | .imported b f => Wellformed.wf (b, f)
  | .derived r => Wellformed.wf r

instance : Wellformed Provenance := ⟨Provenance.wf⟩

/-- The tag of each transaction state, in declaration order. -/
def TxnState.tag : TxnState → Nat
  | .posted => 0 | .pending => 1 | .settled => 2 | .void => 3

/-- Inverse of `TxnState.tag`. -/
def TxnState.ofTag : Nat → Option TxnState
  | 0 => some .posted | 1 => some .pending | 2 => some .settled | 3 => some .void | _ => none

instance : Codec TxnState := Codec.ofRetract TxnState.tag TxnState.ofTag

instance : LawfulCodec TxnState := Codec.lawful_ofRetract (fun s => by cases s <;> rfl)

instance : Wellformed TxnState := Wellformed.ofIso TxnState.tag

-- A receipt's priced line is encoded here, ahead of the receipts below, because
-- a transaction carries the lines it paid for and so has to be able to reach it.
instance : Codec LineItem :=
  Codec.ofIso
    (fun l => (l.description, l.qty, l.amount))
    (fun (description, qty, amount) => { description, qty, amount })

instance : LawfulCodec LineItem := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed LineItem := Wellformed.ofIso (fun l => (l.description, l.qty, l.amount))

instance : Codec Transaction :=
  Codec.ofIso
    (fun t => (t.id, t.date, t.payee, t.narration, t.state, t.postings, t.labels, t.source,
      t.attachments, t.items))
    (fun (id, date, payee, narration, state, postings, labels, source, attachments, items) =>
      { id, date, payee, narration, state, postings, labels, source, attachments, items })

instance : LawfulCodec Transaction := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Transaction :=
  Wellformed.ofIso
    (fun t => (t.id, t.date, t.payee, t.narration, t.state, t.postings, t.labels, t.source,
      t.attachments, t.items))

/-! ## Filters

The one recursive type in the ledger, and the only decoder here that takes fuel.
A filter's decoder cannot recurse on the byte list structurally — the remainder
is not a sublist in a way Lean sees — so it counts down instead, and the caller
hands it the length of the input. That is always enough: `Filter.depth_le_length`
says a filter nests less deeply than it is long, because every level costs at
least its own tag byte.
-/

/-- How deeply a filter nests: the fuel its reader needs. -/
def Filter.depth : Filter → Nat
  | .and a b => 1 + a.depth + b.depth
  | .or a b => 1 + a.depth + b.depth
  | .not a => 1 + a.depth
  | _ => 1

/-- Tag, then payload; the two connectives carry whole filters. -/
def encFilter : Filter → List UInt8
  | .all => tagged 0 []
  | .account s => tagged 1 (Codec.toBytes s)
  | .dateFrom d => tagged 2 (Codec.toBytes d)
  | .dateTo d => tagged 3 (Codec.toBytes d)
  | .amountFrom a => tagged 4 (Codec.toBytes a)
  | .amountTo a => tagged 5 (Codec.toBytes a)
  | .label s => tagged 6 (Codec.toBytes s)
  | .party s => tagged 7 (Codec.toBytes s)
  | .owner s => tagged 8 (Codec.toBytes s)
  | .payee s => tagged 9 (Codec.toBytes s)
  | .text s => tagged 10 (Codec.toBytes s)
  | .commodity s => tagged 11 (Codec.toBytes s)
  | .tag s => tagged 12 (Codec.toBytes s)
  | .and a b => tagged 13 (encFilter a ++ encFilter b)
  | .or a b => tagged 14 (encFilter a ++ encFilter b)
  | .not a => tagged 15 (encFilter a)

/-- Reads a filter. `fuel` bounds the nesting depth; `Codec Filter` passes the input length. -/
def decFilter : Nat → List UInt8 → Option (Filter × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
    match decNat bs with
    | none => none
    | some (0, rest) => some (.all, rest)
    | some (1, rest) => readAs String rest .account
    | some (2, rest) => readAs Date rest .dateFrom
    | some (3, rest) => readAs Date rest .dateTo
    | some (4, rest) => readAs Amount rest .amountFrom
    | some (5, rest) => readAs Amount rest .amountTo
    | some (6, rest) => readAs String rest .label
    | some (7, rest) => readAs String rest .party
    | some (8, rest) => readAs String rest .owner
    | some (9, rest) => readAs String rest .payee
    | some (10, rest) => readAs String rest .text
    | some (11, rest) => readAs String rest .commodity
    | some (12, rest) => readAs String rest .tag
    | some (13, rest) =>
      match decFilter fuel rest with
      | none => none
      | some (a, rest) =>
        match decFilter fuel rest with
        | none => none
        | some (b, rest) => some (.and a b, rest)
    | some (14, rest) =>
      match decFilter fuel rest with
      | none => none
      | some (a, rest) =>
        match decFilter fuel rest with
        | none => none
        | some (b, rest) => some (.or a b, rest)
    | some (15, rest) =>
      match decFilter fuel rest with
      | none => none
      | some (a, rest) => some (.not a, rest)
    | _ => none

/-- With enough fuel, a filter reads back exactly. -/
theorem decFilter_encFilter : ∀ (f : Filter) (fuel : Nat), f.depth ≤ fuel →
    ∀ rest : List UInt8, decFilter fuel (encFilter f ++ rest) = some (f, rest) := by
  intro f
  induction f with
  | all => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter]
  | account s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | dateFrom d => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | dateTo d => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | amountFrom a => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | amountTo a => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | label s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | party s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | owner s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | payee s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | text s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | commodity s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | tag s => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n => simp [encFilter, decFilter, tagged, List.append_assoc]
  | and a b iha ihb => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n =>
      have ha : a.depth ≤ n := by simp only [Filter.depth] at h; omega
      have hb : b.depth ≤ n := by simp only [Filter.depth] at h; omega
      simp [encFilter, decFilter, tagged, List.append_assoc, iha n ha, ihb n hb]
  | or a b iha ihb => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n =>
      have ha : a.depth ≤ n := by simp only [Filter.depth] at h; omega
      have hb : b.depth ≤ n := by simp only [Filter.depth] at h; omega
      simp [encFilter, decFilter, tagged, List.append_assoc, iha n ha, ihb n hb]
  | not a iha => intro fuel h rest; cases fuel with
    | zero => simp [Filter.depth] at h
    | succ n =>
      have ha : a.depth ≤ n := by simp only [Filter.depth] at h; omega
      simp [encFilter, decFilter, tagged, List.append_assoc, iha n ha]

/-- A filter nests less deeply than its encoding is long: every level costs a tag byte. -/
theorem Filter.depth_le_length : ∀ f : Filter, f.depth ≤ (encFilter f).length := by
  intro f
  induction f with
  | and a b iha ihb =>
    have := one_le_length_encNat 13
    simp only [Filter.depth, encFilter, length_tagged, List.length_append]
    omega
  | or a b iha ihb =>
    have := one_le_length_encNat 14
    simp only [Filter.depth, encFilter, length_tagged, List.length_append]
    omega
  | not a iha =>
    have := one_le_length_encNat 15
    simp only [Filter.depth, encFilter, length_tagged]
    omega
  | _ =>
    simp only [Filter.depth, encFilter]
    exact one_le_length_tagged _ _

instance : Codec Filter where
  toBytes := encFilter
  ofBytes bs := decFilter bs.length bs

/--
A filter carries dates and amounts of its own, and `Filter.inRange` is the same
walk `checkBounds` makes over a rule: the bound belongs beside the other bounds
rather than here, because both doors ask the same question of it.
-/
instance : Wellformed Filter := ⟨Filter.inRange⟩

instance : LawfulCodec Filter where
  ofBytes_toBytes f rest := by
    have h : f.depth ≤ (encFilter f ++ rest).length := by
      have := Filter.depth_le_length f
      simp only [List.length_append]
      omega
    exact decFilter_encFilter f _ h rest

/-! ## Groups, trips, rules, batches, budgets -/

instance : Codec PartyGroup :=
  Codec.ofIso (fun g => (g.name, g.members, g.realm))
    (fun (name, members, realm) => { name, members, realm })

instance : LawfulCodec PartyGroup := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed PartyGroup := Wellformed.ofIso (fun g => (g.name, g.members, g.realm))

instance : Codec Trip :=
  Codec.ofIso
    (fun t => (t.id, t.name, t.starts, t.ends, t.payer, t.note, t.realm))
    (fun (id, name, starts, ends, payer, note, realm) =>
      { id, name, starts, ends, payer, note, realm })

instance : LawfulCodec Trip := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Trip :=
  Wellformed.ofIso (fun t => (t.id, t.name, t.starts, t.ends, t.payer, t.note, t.realm))

instance : Codec Rule :=
  Codec.ofIso
    (fun r => (r.id, r.name, r.filterSrc, r.filter, r.setAccount, r.addLabels, r.setParty,
      r.priority, r.realm))
    (fun (id, name, filterSrc, filter, setAccount, addLabels, setParty, priority, realm) =>
      { id, name, filterSrc, filter, setAccount, addLabels, setParty, priority, realm })

instance : LawfulCodec Rule := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Rule :=
  Wellformed.ofIso
    (fun r => (r.id, r.name, r.filterSrc, r.filter, r.setAccount, r.addLabels, r.setParty,
      r.priority, r.realm))

instance : Codec ImportBatch :=
  Codec.ofIso
    (fun b => (b.id, b.profile, b.filename, b.account, b.stamp, b.total, b.duplicates, b.realm))
    (fun (id, profile, filename, account, stamp, total, duplicates, realm) =>
      { id, profile, filename, account, stamp, total, duplicates, realm })

instance : LawfulCodec ImportBatch := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed ImportBatch :=
  Wellformed.ofIso
    (fun b => (b.id, b.profile, b.filename, b.account, b.stamp, b.total, b.duplicates, b.realm))

instance : Codec Participant :=
  Codec.ofIso
    (fun p => (p.owner, p.name, p.account, p.weight))
    (fun (owner, name, account, weight) => { owner, name, account, weight })

instance : LawfulCodec Participant := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Participant :=
  Wellformed.ofIso (fun p => (p.owner, p.name, p.account, p.weight))

instance : Codec Budget :=
  Codec.ofIso
    (fun b => (b.id, b.name, b.note, b.closed)) (fun (id, name, note, closed) =>
      { id, name, note, closed })

instance : LawfulCodec Budget := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Budget := Wellformed.ofIso (fun b => (b.id, b.name, b.note, b.closed))

/-! ## Receipts -/

instance : Codec Attachment :=
  Codec.ofIso
    (fun a => (a.sha256, a.mime, a.bytes, a.origName, a.createdAt, a.cipherHash, a.wrappedKey))
    (fun (sha256, mime, bytes, origName, createdAt, cipherHash, wrappedKey) =>
      { sha256, mime, bytes, origName, createdAt, cipherHash, wrappedKey })

instance : LawfulCodec Attachment := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Attachment :=
  Wellformed.ofIso
    (fun a => (a.sha256, a.mime, a.bytes, a.origName, a.createdAt, a.cipherHash, a.wrappedKey))

instance : Codec Extracted :=
  Codec.ofIso
    (fun e => (e.merchant, e.date, e.total, e.items, e.rawText, e.extractor))
    (fun (merchant, date, total, items, rawText, extractor) =>
      { merchant, date, total, items, rawText, extractor })

instance : LawfulCodec Extracted := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Extracted :=
  Wellformed.ofIso (fun e => (e.merchant, e.date, e.total, e.items, e.rawText, e.extractor))

instance : Codec Receipts.ItemShare :=
  Codec.ofIso (fun s => (s.line, s.qty)) (fun (line, qty) => { line, qty })

instance : LawfulCodec Receipts.ItemShare := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Receipts.ItemShare := Wellformed.ofIso (fun s => (s.line, s.qty))

instance : Codec Receipts.ItemGroup :=
  Codec.ofIso (fun g => (g.items, g.into)) (fun (items, into) => { items, into })

instance : LawfulCodec Receipts.ItemGroup := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Receipts.ItemGroup := Wellformed.ofIso (fun g => (g.items, g.into))

/-! ## Payment requests and invoices -/

/-- Tag, then payload, one tag per constructor in declaration order. -/
def encPaymentRequest : PaymentRequest → List UInt8
  | .epc name iban bic => tagged 0 (Codec.toBytes (name, iban, bic))
  | .link url => tagged 1 (Codec.toBytes url)

/-- Inverse of `encPaymentRequest`. -/
def decPaymentRequest (bs : List UInt8) : Option (PaymentRequest × List UInt8) :=
  match decNat bs with
  | some (0, rest) =>
    readAs (String × String × Option String) rest (fun (n, i, b) => .epc n i b)
  | some (1, rest) => readAs String rest .link
  | _ => none

instance : Codec PaymentRequest where
  toBytes := encPaymentRequest
  ofBytes := decPaymentRequest

instance : LawfulCodec PaymentRequest where
  ofBytes_toBytes p rest := by
    show decPaymentRequest (encPaymentRequest p ++ rest) = some (p, rest)
    cases p <;> simp [encPaymentRequest, decPaymentRequest, tagged, List.append_assoc]

/-- The bound of each constructor's payload, one line per tag above. -/
def PaymentRequest.wf : PaymentRequest → Bool
  | .epc name iban bic => Wellformed.wf (name, iban, bic)
  | .link url => Wellformed.wf url

instance : Wellformed PaymentRequest := ⟨PaymentRequest.wf⟩

instance : Codec InvoiceLine :=
  Codec.ofIso
    (fun l => (l.description, l.qtyMilli, l.unitPrice, l.taxBp))
    (fun (description, qtyMilli, unitPrice, taxBp) =>
      { description, qtyMilli, unitPrice, taxBp })

instance : LawfulCodec InvoiceLine := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed InvoiceLine :=
  Wellformed.ofIso (fun l => (l.description, l.qtyMilli, l.unitPrice, l.taxBp))

/-- The tag of each invoice status, in declaration order. -/
def InvoiceStatus.tag : InvoiceStatus → Nat
  | .draft => 0 | .sent => 1 | .paid => 2 | .void => 3

/-- Inverse of `InvoiceStatus.tag`. -/
def InvoiceStatus.ofTag : Nat → Option InvoiceStatus
  | 0 => some .draft | 1 => some .sent | 2 => some .paid | 3 => some .void | _ => none

instance : Codec InvoiceStatus := Codec.ofRetract InvoiceStatus.tag InvoiceStatus.ofTag

instance : LawfulCodec InvoiceStatus := Codec.lawful_ofRetract (fun s => by cases s <;> rfl)

instance : Wellformed InvoiceStatus := Wellformed.ofIso InvoiceStatus.tag

instance : Codec Invoice :=
  Codec.ofIso
    (fun i => (i.id, i.number, i.issued, i.due, i.payerId, i.payerName, i.commodity, i.reference,
      i.status, i.note, i.settledTxn, i.payment, i.sourceAccount, i.budgetId, i.pendingTxn,
      i.lines))
    (fun (id, number, issued, due, payerId, payerName, commodity, reference, status, note,
        settledTxn, payment, sourceAccount, budgetId, pendingTxn, lines) =>
      { id, number, issued, due, payerId, payerName, commodity, reference, status, note,
        settledTxn, payment, sourceAccount, budgetId, pendingTxn, lines })

instance : LawfulCodec Invoice := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Invoice :=
  Wellformed.ofIso
    (fun i => (i.id, i.number, i.issued, i.due, i.payerId, i.payerName, i.commodity, i.reference,
      i.status, i.note, i.settledTxn, i.payment, i.sourceAccount, i.budgetId, i.pendingTxn,
      i.lines))

/-! ## Members and realms -/

/-- The tag of each realm role, in declaration order. -/
def RealmRole.tag : RealmRole → Nat
  | .viewer => 0 | .admin => 1

/-- Inverse of `RealmRole.tag`. -/
def RealmRole.ofTag : Nat → Option RealmRole
  | 0 => some .viewer | 1 => some .admin | _ => none

instance : Codec RealmRole := Codec.ofRetract RealmRole.tag RealmRole.ofTag

instance : LawfulCodec RealmRole := Codec.lawful_ofRetract (fun r => by cases r <;> rfl)

instance : Wellformed RealmRole := Wellformed.ofIso RealmRole.tag

instance : Codec Member :=
  Codec.ofIso (fun m => (m.id, m.name, m.party)) (fun (id, name, party) => { id, name, party })

instance : LawfulCodec Member := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Member := Wellformed.ofIso (fun m => (m.id, m.name, m.party))

instance : Codec Realm :=
  Codec.ofIso
    (fun r => (r.id, r.name, r.members, r.generation))
    (fun (id, name, members, generation) => { id, name, members, generation })

instance : LawfulCodec Realm := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed Realm :=
  Wellformed.ofIso (fun r => (r.id, r.name, r.members, r.generation))

instance : Codec BudgetState :=
  Codec.ofIso
    (fun b => (b.budget, b.participants, b.realm, b.account, b.label))
    (fun (budget, participants, realm, account, label) =>
      { budget, participants, realm, account, label })

instance : LawfulCodec BudgetState := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed BudgetState :=
  Wellformed.ofIso (fun b => (b.budget, b.participants, b.realm, b.account, b.label))

instance : Codec InvoiceState :=
  Codec.ofIso
    (fun i => (i.invoice, i.sources, i.realm))
    (fun (invoice, sources, realm) => { invoice, sources, realm })

instance : LawfulCodec InvoiceState := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed InvoiceState :=
  Wellformed.ofIso (fun i => (i.invoice, i.sources, i.realm))

instance : Codec BlobState :=
  Codec.ofIso
    (fun b => (b.file, b.extracted, b.items, b.registeredBy, b.realm))
    (fun (file, extracted, items, registeredBy, realm) =>
      { file, extracted, items, registeredBy, realm })

instance : LawfulCodec BlobState := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed BlobState :=
  Wellformed.ofIso (fun b => (b.file, b.extracted, b.items, b.registeredBy, b.realm))

/-! ## The state -/

/--
A state with every map replaced by its entries in key order, and the fingerprint
set by its members in order.

This is what the encoding sees, and it is the whole reason a checkpoint hash is
reproducible: a `Std.HashMap` iterates in bucket order, which is a fact about the
hash function rather than about the ledger, so nothing is ever written in the
order a map happens to hold it.
-/
structure StateWire where
  /-- Realms, by id. -/
  realms : List (String × Realm)
  /-- Members, by id. -/
  members : List (String × Member)
  /-- Accounts, by id. -/
  accounts : List (String × Account)
  /-- Labels, by id. -/
  labels : List (String × Label)
  /-- Parties, by id. -/
  parties : List (String × Party)
  /-- Groups, by name. -/
  groups : List (String × PartyGroup)
  /-- Trips, by name. -/
  trips : List (String × Trip)
  /-- Rules, by id. -/
  rules : List (String × Rule)
  /-- Transactions, by id. -/
  txns : List (String × Transaction)
  /-- Budgets, by id. -/
  budgets : List (String × BudgetState)
  /-- Invoices, by id. -/
  invoices : List (String × InvoiceState)
  /-- Stored files, by content hash. -/
  blobs : List (String × BlobState)
  /-- Import batches, by id. -/
  batches : List (String × ImportBatch)
  /-- Counters, by name. -/
  counters : List (String × Int)
  /-- Import fingerprints, in order. -/
  fingerprints : List String

instance : Codec StateWire :=
  Codec.ofIso
    (fun w => (w.realms, w.members, w.accounts, w.labels, w.parties, w.groups, w.trips, w.rules,
      w.txns, w.budgets, w.invoices, w.blobs, w.batches, w.counters, w.fingerprints))
    (fun (realms, members, accounts, labels, parties, groups, trips, rules, txns, budgets,
        invoices, blobs, batches, counters, fingerprints) =>
      { realms, members, accounts, labels, parties, groups, trips, rules, txns, budgets,
        invoices, blobs, batches, counters, fingerprints })

instance : LawfulCodec StateWire := Codec.lawful_ofIso (fun _ => rfl)

instance : Wellformed StateWire :=
  Wellformed.ofIso
    (fun w => (w.realms, w.members, w.accounts, w.labels, w.parties, w.groups, w.trips, w.rules,
      w.txns, w.budgets, w.invoices, w.blobs, w.batches, w.counters, w.fingerprints))

/-! ## What a state's entries have to look like

A hash map has no canonical value, so a state is written as its entries in key
order — and a reader has to insist on exactly that, or a checkpoint is not a
name for a state. Two things were accepted that the writer never produces.

*Unsorted or repeated keys.* The entries were folded back in with `insert`, so a
list in any order, with any duplicates, rebuilt a map that re-encoded to
different bytes. `ascending` is the one rule that rules both out.

*A key that is not the entity's own id.* Nothing stopped a decoded state holding
`accounts["A"] = { id := "B", … }`, which no operation can produce and which
makes "the account with this id" a question with two answers.
-/

/-- Whether entries are strictly ascending by key: sorted, with no key twice. -/
def ascending {α : Type} (ps : List (String × α)) : Bool :=
  (ps.zip (ps.drop 1)).all (fun q => decide (q.1.1 < q.2.1))

/-- Whether names are strictly ascending: the same rule for the fingerprint set. -/
def ascendingNames (ks : List String) : Bool :=
  (ks.zip (ks.drop 1)).all (fun q => decide (q.1 < q.2))

/-- Whether every entry is filed under the id the entity itself carries. -/
def keyedBy {α : Type} (f : α → String) (ps : List (String × α)) : Bool :=
  ps.all (fun p => f p.2 == p.1)

namespace StateWire

/-- Whether these are the entries a state would have been written as. -/
def canonical (w : StateWire) : Bool :=
  ascending w.realms && keyedBy (fun r => r.id.val) w.realms &&
  ascending w.members && keyedBy (fun m => m.id.val) w.members &&
  ascending w.accounts && keyedBy (fun a => a.id.val) w.accounts &&
  ascending w.labels && keyedBy (fun l => l.id.val) w.labels &&
  ascending w.parties && keyedBy (fun p => p.id.val) w.parties &&
  ascending w.groups && keyedBy (fun g => g.name) w.groups &&
  ascending w.trips && keyedBy (fun t => t.name) w.trips &&
  ascending w.rules && keyedBy (fun r => r.id.val) w.rules &&
  ascending w.txns && keyedBy (fun t => t.id.val) w.txns &&
  ascending w.budgets && keyedBy (fun b => b.budget.id.val) w.budgets &&
  ascending w.invoices && keyedBy (fun i => i.invoice.id.val) w.invoices &&
  ascending w.blobs && keyedBy (fun b => b.file.sha256) w.blobs &&
  ascending w.batches && keyedBy (fun b => b.id.val) w.batches &&
  ascending w.counters &&
  ascendingNames w.fingerprints

end StateWire

/-- Rebuilds a map by inserting its entries in the order they were written. -/
def ofPairs {α : Type} (ps : List (String × α)) : Std.HashMap String α :=
  ps.foldl (fun m p => m.insert p.1 p.2) {}

/-- Rebuilds a set the same way. -/
def ofKeys (ks : List String) : Std.HashSet String :=
  ks.foldl (fun s k => s.insert k) {}

namespace State

/-- Every map of `s`, in key order: the form the encoder writes. -/
def wire (s : State) : StateWire :=
  { realms := sortedPairs s.realms
    members := sortedPairs s.members
    accounts := sortedPairs s.accounts
    labels := sortedPairs s.labels
    parties := sortedPairs s.parties
    groups := sortedPairs s.groups
    trips := sortedPairs s.trips
    rules := sortedPairs s.rules
    txns := sortedPairs s.txns
    budgets := sortedPairs s.budgets
    invoices := sortedPairs s.invoices
    blobs := sortedPairs s.blobs
    batches := sortedPairs s.batches
    counters := sortedPairs s.counters
    fingerprints := s.fingerprints.toList.mergeSort (· ≤ ·) }

end State

namespace StateWire

/-- Puts the maps back, by inserting every entry. -/
def state (w : StateWire) : State :=
  { realms := ofPairs w.realms
    members := ofPairs w.members
    accounts := ofPairs w.accounts
    labels := ofPairs w.labels
    parties := ofPairs w.parties
    groups := ofPairs w.groups
    trips := ofPairs w.trips
    rules := ofPairs w.rules
    txns := ofPairs w.txns
    budgets := ofPairs w.budgets
    invoices := ofPairs w.invoices
    blobs := ofPairs w.blobs
    batches := ofPairs w.batches
    counters := ofPairs w.counters
    fingerprints := ofKeys w.fingerprints }

end StateWire

/--
A state, written as its sorted entries and read back only from entries that are
sorted and keyed by their own ids.

This is the one decoder in the file that refuses something the writer can
produce, and it has to be: `State.wire` sorts, so its own output always passes,
but a `State` assembled by hand can hold an account under a key that is not its
id, and that state has no canonical bytes to be read back from.
-/
instance : Codec State where
  toBytes s := Codec.toBytes s.wire
  ofBytes bs := (Codec.ofBytes (α := StateWire) bs).bind fun p =>
    if p.1.canonical then some (p.1.state, p.2) else none

/-- A state is bounded exactly as the entries it is written as are. -/
instance : Wellformed State := Wellformed.ofIso State.wire

namespace State

/--
Whether this state is one the reader would take back.

Its entries are sorted by `State.wire`, so the only thing at stake is whether
every entity is filed under its own id — which everything `applyOp` writes is,
and which a hand-assembled `State` need not be.
-/
def Canonical (s : State) : Prop := s.wire.canonical = true

instance (s : State) : Decidable s.Canonical := by
  unfold State.Canonical; infer_instance

/--
What a state reads back as: itself, rebuilt from its own sorted entries.

Not `s` — a `Std.HashMap` built by inserting the same entries in the same order
holds the same entries but is not the same value, and there is no law in `Std`
that says otherwise. Every statement below about `Op`, `Part` and `Event` carries
this through rather than pretending it away.
-/
theorem ofBytes_toBytes (s : State) (h : s.Canonical) (rest : List UInt8) :
    Codec.ofBytes (Codec.toBytes s ++ rest) = some (s.wire.state, rest) := by
  show ((Codec.ofBytes (α := StateWire) (Codec.toBytes s.wire ++ rest)).bind
      fun p => if p.1.canonical then some (StateWire.state p.1, p.2) else none)
    = some (s.wire.state, rest)
  simp only [LawfulCodec.ofBytes_toBytes, Option.bind_some]
  exact if_pos h

/--
The remaining obligation, stated and not proved here.

`State.canonical` is how `Core` compares two states, and it sorts every map by
key before looking at anything, so it cannot see the difference between a map
and the same map rebuilt. Proving it needs `Std.HashMap` lemmas relating
`insert`, `toList` and key order that `Std` does not export; the round trip is
checked instead, on real states, in `Test/Encode.lean`.
-/
def RebuildsCanonically (s : State) : Prop := s.wire.state.canonical = s.canonical

end State

/-- Reading back a state gives the state rebuilt from its sorted entries. -/
theorem readAs_state {β : Type} (s : State) (h : s.Canonical) (rest : List UInt8)
    (f : State → β) : readAs State (Codec.toBytes s ++ rest) f = some (f s.wire.state, rest) := by
  simp [readAs, State.ofBytes_toBytes s h]

/-! ## Operations -/

/-- Tag, then payload, one tag per constructor in declaration order. -/
def encOp : Op → List UInt8
  | .createRealm r => tagged 0 (Codec.toBytes r)
  | .putAccount a => tagged 1 (Codec.toBytes a)
  | .mergeAccounts f i => tagged 2 (Codec.toBytes (f, i))
  | .deleteAccount i => tagged 3 (Codec.toBytes i)
  | .setAccountRights i ps => tagged 4 (Codec.toBytes (i, ps))
  | .setAccountOwner i o => tagged 5 (Codec.toBytes (i, o))
  | .putLabel l => tagged 6 (Codec.toBytes l)
  | .deleteLabel i => tagged 7 (Codec.toBytes i)
  | .putParty p => tagged 8 (Codec.toBytes p)
  | .putGroup g => tagged 9 (Codec.toBytes g)
  | .deleteGroup n => tagged 10 (Codec.toBytes n)
  | .putTrip t => tagged 11 (Codec.toBytes t)
  | .deleteTrip n => tagged 12 (Codec.toBytes n)
  | .putRule r => tagged 13 (Codec.toBytes r)
  | .deleteRule n => tagged 14 (Codec.toBytes n)
  | .putTransaction t => tagged 15 (Codec.toBytes t)
  | .deleteTransaction i => tagged 16 (Codec.toBytes i)
  | .splitTransaction i ts k => tagged 17 (Codec.toBytes (i, ts, k))
  | .mergeTransactions is n p nr c => tagged 18 (Codec.toBytes (is, n, p, nr, c))
  | .unmergeTransaction i ns => tagged 19 (Codec.toBytes (i, ns))
  | .replaceTransaction i ps k => tagged 20 (Codec.toBytes (i, ps, k))
  | .divideByItems i gs ns => tagged 21 (Codec.toBytes (i, gs, ns))
  | .raiseClaim t => tagged 22 (Codec.toBytes t)
  | .resolveClaim i a s => tagged 23 (Codec.toBytes (i, a, s))
  | .voidClaim i w => tagged 24 (Codec.toBytes (i, w))
  | .openBudget b a => tagged 25 (Codec.toBytes (b, a))
  | .setParticipants b a => tagged 26 (Codec.toBytes (b, a))
  | .contribute b t => tagged 27 (Codec.toBytes (b, t))
  | .allocate b a c d h t cs l => tagged 28 (Codec.toBytes (b, a, c, d, h, t, cs, l))
  | .settle b c h d cs l => tagged 29 (Codec.toBytes (b, c, h, d, cs, l))
  | .closeBudget b a c h d t cs l => tagged 30 (Codec.toBytes (b, a, c, h, d, t, cs, l))
  | .reopenBudget b => tagged 31 (Codec.toBytes b)
  | .deleteBudget b => tagged 32 (Codec.toBytes b)
  | .issueInvoice i s => tagged 33 (Codec.toBytes (i, s))
  | .setInvoiceStatus i s => tagged 34 (Codec.toBytes (i, s))
  | .settleInvoice i t => tagged 35 (Codec.toBytes (i, t))
  | .deleteInvoice i => tagged 36 (Codec.toBytes i)
  | .registerBlob f => tagged 37 (Codec.toBytes f)
  | .attach t s => tagged 38 (Codec.toBytes (t, s))
  | .detach t s => tagged 39 (Codec.toBytes (t, s))
  | .recordExtraction s e => tagged 40 (Codec.toBytes (s, e))
  | .setReceiptLines s i => tagged 41 (Codec.toBytes (s, i))
  | .forgetBlob s => tagged 42 (Codec.toBytes s)
  | .recordImportBatch b => tagged 43 (Codec.toBytes b)
  | .addMember m => tagged 44 (Codec.toBytes m)
  | .removeMember i => tagged 45 (Codec.toBytes i)
  | .grant r m ro b => tagged 46 (Codec.toBytes (r, m, ro, b))
  | .revoke r m => tagged 47 (Codec.toBytes (r, m))
  | .setRole r m ro => tagged 48 (Codec.toBytes (r, m, ro))
  | .rotateRealmKey r => tagged 49 (Codec.toBytes r)
  | .snapshot s => tagged 50 (Codec.toBytes s)
  | .payClaim c p d => tagged 51 (Codec.toBytes (c, p, d))

/-- Reads one operation, by tag. -/
def decOpTag : Nat → List UInt8 → Option (Op × List UInt8)
  | 0, bs => readAs Realm bs .createRealm
  | 1, bs => readAs Account bs .putAccount
  | 2, bs => readAs (AccountId × AccountId) bs (fun (f, i) => .mergeAccounts f i)
  | 3, bs => readAs AccountId bs .deleteAccount
  | 4, bs => readAs (AccountId × List MemberId) bs (fun (i, ps) => .setAccountRights i ps)
  | 5, bs => readAs (AccountId × PartyId) bs (fun (i, o) => .setAccountOwner i o)
  | 6, bs => readAs Label bs .putLabel
  | 7, bs => readAs LabelId bs .deleteLabel
  | 8, bs => readAs Party bs .putParty
  | 9, bs => readAs PartyGroup bs .putGroup
  | 10, bs => readAs String bs .deleteGroup
  | 11, bs => readAs Trip bs .putTrip
  | 12, bs => readAs String bs .deleteTrip
  | 13, bs => readAs Rule bs .putRule
  | 14, bs => readAs String bs .deleteRule
  | 15, bs => readAs Transaction bs .putTransaction
  | 16, bs => readAs TxId bs .deleteTransaction
  | 17, bs => readAs (TxId × List AccountId × Bool) bs
      (fun (i, ts, k) => .splitTransaction i ts k)
  | 18, bs => readAs (List TxId × TxId × Option String × Option String × List AccountId) bs
      (fun (is, n, p, nr, c) => .mergeTransactions is n p nr c)
  | 19, bs => readAs (TxId × List TxId) bs (fun (i, ns) => .unmergeTransaction i ns)
  | 20, bs => readAs (TxId × List Transaction × String) bs
      (fun (i, ps, k) => .replaceTransaction i ps k)
  | 21, bs => readAs (TxId × List Receipts.ItemGroup × List TxId) bs
      (fun (i, gs, ns) => .divideByItems i gs ns)
  | 22, bs => readAs Transaction bs .raiseClaim
  | 23, bs => readAs (TxId × TxId × TxId) bs (fun (i, a, s) => .resolveClaim i a s)
  | 24, bs => readAs (TxId × Option (AccountId × TxId × Date)) bs (fun (i, w) => .voidClaim i w)
  | 25, bs => readAs (Budget × Account) bs (fun (b, a) => .openBudget b a)
  | 26, bs => readAs (BudgetId × List Participant) bs (fun (b, a) => .setParticipants b a)
  | 27, bs => readAs (BudgetId × Transaction) bs (fun (b, t) => .contribute b t)
  | 28, bs => readAs (BudgetId × List Participant × Commodity × Date × Option PartyId × TxId ×
      List TxId × LabelId) bs (fun (b, a, c, d, h, t, cs, l) => .allocate b a c d h t cs l)
  | 29, bs => readAs (BudgetId × Commodity × Option PartyId × Date × List TxId × LabelId) bs
      (fun (b, c, h, d, cs, l) => .settle b c h d cs l)
  | 30, bs => readAs (BudgetId × Option (List Participant) × Commodity × Option PartyId × Date ×
      TxId × List TxId × LabelId) bs
      (fun (b, a, c, h, d, t, cs, l) => .closeBudget b a c h d t cs l)
  | 31, bs => readAs BudgetId bs .reopenBudget
  | 32, bs => readAs BudgetId bs .deleteBudget
  | 33, bs => readAs (Invoice × List TxId) bs (fun (i, s) => .issueInvoice i s)
  | 34, bs => readAs (InvoiceId × InvoiceStatus) bs (fun (i, s) => .setInvoiceStatus i s)
  | 35, bs => readAs (InvoiceId × TxId) bs (fun (i, t) => .settleInvoice i t)
  | 36, bs => readAs InvoiceId bs .deleteInvoice
  | 37, bs => readAs Attachment bs .registerBlob
  | 38, bs => readAs (TxId × String) bs (fun (t, s) => .attach t s)
  | 39, bs => readAs (TxId × String) bs (fun (t, s) => .detach t s)
  | 40, bs => readAs (String × Extracted) bs (fun (s, e) => .recordExtraction s e)
  | 41, bs => readAs (String × List LineItem) bs (fun (s, i) => .setReceiptLines s i)
  | 42, bs => readAs String bs .forgetBlob
  | 43, bs => readAs ImportBatch bs .recordImportBatch
  | 44, bs => readAs Member bs .addMember
  | 45, bs => readAs MemberId bs .removeMember
  | 46, bs => readAs (RealmId × MemberId × RealmRole × Account) bs
      (fun (r, m, ro, b) => .grant r m ro b)
  | 47, bs => readAs (RealmId × MemberId) bs (fun (r, m) => .revoke r m)
  | 48, bs => readAs (RealmId × MemberId × RealmRole) bs (fun (r, m, ro) => .setRole r m ro)
  | 49, bs => readAs RealmId bs .rotateRealmKey
  | 50, bs => readAs State bs .snapshot
  | 51, bs => readAs (TxId × TxId × Date) bs (fun (c, p, d) => .payClaim c p d)
  | _, _ => none

/-- Reads one operation: the tag, then whatever that tag says follows. -/
def decOp (bs : List UInt8) : Option (Op × List UInt8) :=
  match decNat bs with
  | none => none
  | some (t, rest) => decOpTag t rest

/--
An operation as it comes back from its own bytes.

Only `snapshot` moves, and only in the way `State.ofBytes_toBytes` describes.
-/
def Op.canon : Op → Op
  | .snapshot s => .snapshot s.wire.state
  | o => o

/-- Whether an operation's own bytes are ones the reader takes back. -/
def Op.Canonical : Op → Prop
  | .snapshot g => g.Canonical
  | _ => True

/-- An operation round-trips, up to the state rebuild inside a snapshot. -/
theorem decOp_encOp (o : Op) (h : o.Canonical) (rest : List UInt8) :
    decOp (encOp o ++ rest) = some (o.canon, rest) := by
  cases o
  case snapshot g =>
    show decOp (tagged 50 (Codec.toBytes g) ++ rest) = some (Op.canon (.snapshot g), rest)
    simp only [decOp, decNat_tagged, decOpTag, Op.canon, readAs_state g h]
  all_goals
    simp [encOp, decOp, decOpTag, Op.canon, tagged, List.append_assoc]

/--
What a decoded operation is checked for, which is one thing: the state a
`snapshot` carries.

The other fifty-one carry an *intent* — a transaction to write, a budget to
divide, a receipt's lines — and the door an intent goes through is `checkBounds`,
which `applyOp` runs over every one of them before it reads any of it for effect.
That door is the right one, and the reason is the rule the whole file is built
around: **an invalid part is skipped rather than failing its neighbours.** An
event is one author's set of parts, each in a realm of its own, and a reader who
cannot use one applies the others. Refusing the *bytes* would throw all of them
away — one part naming a silly exponent would cost a reader every other realm's
part in the same event, decided by whoever composed it. Refusing the *part* costs
exactly the part that is wrong.

So an operation's numbers are `checkBounds`'s, and `Test/Encode.lean` pins both
halves: that an event carrying an absurd year decodes, and that stepping it
leaves the state alone.

A `snapshot` is the exception because it is the exception in `checkBounds` too:
it carries a whole `State`, `checkBounds` answers `ok` for it without looking,
and nothing applies it in the sense the other operations are applied — it
*replaces*. A state is a value the ledger holds rather than an intent, and every
value the ledger holds — every checkpoint, every entity inside one — is bounded
here.
-/
def Op.wf : Op → Bool
  | .snapshot s => Wellformed.wf s
  | _ => true

instance : Wellformed Op := ⟨Op.wf⟩

instance : Codec Op where
  toBytes := encOp
  ofBytes := decOp

/-! ## Parts and events -/

/-- The realm, then the operation. -/
def encPart (p : Part) : List UInt8 := Codec.toBytes p.realm ++ encOp p.op

/-- Inverse of `encPart`, up to the state rebuild inside a snapshot. -/
def decPart (bs : List UInt8) : Option (Part × List UInt8) :=
  match Codec.ofBytes (α := RealmId) bs with
  | none => none
  | some (r, bs) =>
    match decOp bs with
    | none => none
    | some (o, bs) => some ({ realm := r, op := o }, bs)

instance : Codec Part where
  toBytes := encPart
  ofBytes := decPart

instance : Wellformed Part := Wellformed.ofIso (fun p => (p.realm, p.op))

/-- A part as it comes back from its own bytes. -/
def Part.canon (p : Part) : Part := { p with op := p.op.canon }

/-- Whether a part's own bytes are ones the reader takes back. -/
def Part.Canonical (p : Part) : Prop := p.op.Canonical

/-- A part round-trips, up to the state rebuild inside a snapshot. -/
theorem Part.ofBytes_toBytes (p : Part) (h : p.Canonical) (rest : List UInt8) :
    Codec.ofBytes (Codec.toBytes p ++ rest) = some (p.canon, rest) := by
  show decPart (encPart p ++ rest) = some (p.canon, rest)
  simp only [encPart, decPart, List.append_assoc, LawfulCodec.ofBytes_toBytes,
    decOp_encOp p.op h, Part.canon]

/-- A list of parts round-trips element by element. -/
theorem decMany_encMany_parts : ∀ (ps : List Part), (∀ p ∈ ps, p.Canonical) →
    ∀ rest : List UInt8,
      decMany Part ps.length (encMany ps ++ rest) = some (ps.map Part.canon, rest)
  | [], _, _ => rfl
  | p :: ps, h, rest => by
    simp only [encMany, decMany, List.length_cons, List.append_assoc, List.map_cons,
      Part.ofBytes_toBytes p (h p (by simp)),
      decMany_encMany_parts ps (fun q hq => h q (by simp [hq])) rest]

/-- A list of parts round-trips, up to the state rebuild inside a snapshot. -/
theorem ofBytes_toBytes_parts (ps : List Part) (h : ∀ p ∈ ps, p.Canonical)
    (rest : List UInt8) :
    Codec.ofBytes (Codec.toBytes ps ++ rest) = some (ps.map Part.canon, rest) := by
  show (match decNat ((encNat ps.length ++ encMany ps) ++ rest) with
    | none => none
    | some (n, r) => decMany Part n r) = some (ps.map Part.canon, rest)
  simp only [List.append_assoc, decNat_encNat, decMany_encMany_parts ps h]

/-- The four scalar fields, then the parts. -/
def encEvent (e : Event) : List UInt8 :=
  Codec.toBytes (e.id, e.author, e.composedAt, e.basedOn) ++ Codec.toBytes e.parts

/-- Inverse of `encEvent`, up to the state rebuild inside a snapshot. -/
def decEvent (bs : List UInt8) : Option (Event × List UInt8) :=
  match Codec.ofBytes (α := String × MemberId × String × Nat) bs with
  | none => none
  | some ((id, author, composedAt, basedOn), bs) =>
    match Codec.ofBytes (α := List Part) bs with
    | none => none
    | some (parts, bs) => some ({ id, author, composedAt, basedOn, parts }, bs)

instance : Codec Event where
  toBytes := encEvent
  ofBytes := decEvent

instance : Wellformed Event :=
  Wellformed.ofIso (fun e => (e.id, e.author, e.composedAt, e.basedOn, e.parts))

/-- An event as it comes back from its own bytes. -/
def Event.canon (e : Event) : Event := { e with parts := e.parts.map Part.canon }

/-- Whether an event's own bytes are ones the reader takes back. -/
def Event.Canonical (e : Event) : Prop := ∀ p ∈ e.parts, p.Canonical

/-- An event round-trips, up to the state rebuild inside a snapshot. -/
theorem Event.ofBytes_toBytes (e : Event) (h : e.Canonical) (rest : List UInt8) :
    Codec.ofBytes (Codec.toBytes e ++ rest) = some (e.canon, rest) := by
  show decEvent (encEvent e ++ rest) = some (e.canon, rest)
  simp only [encEvent, decEvent, List.append_assoc, LawfulCodec.ofBytes_toBytes,
    ofBytes_toBytes_parts e.parts h, Event.canon]

/-! ## Changes -/

/-- Tag, then payload, one tag per constructor in declaration order. -/
def encChange : Change → List UInt8
  | .realm r => tagged 0 (Codec.toBytes r)
  | .member m => tagged 1 (Codec.toBytes m)
  | .memberDeleted i => tagged 2 (Codec.toBytes i)
  | .account a => tagged 3 (Codec.toBytes a)
  | .accountDeleted i => tagged 4 (Codec.toBytes i)
  | .label l => tagged 5 (Codec.toBytes l)
  | .labelDeleted i => tagged 6 (Codec.toBytes i)
  | .party p => tagged 7 (Codec.toBytes p)
  | .group g => tagged 8 (Codec.toBytes g)
  | .groupDeleted n => tagged 9 (Codec.toBytes n)
  | .trip t => tagged 10 (Codec.toBytes t)
  | .tripDeleted n => tagged 11 (Codec.toBytes n)
  | .rule r => tagged 12 (Codec.toBytes r)
  | .ruleDeleted i => tagged 13 (Codec.toBytes i)
  | .txn t => tagged 14 (Codec.toBytes t)
  | .txnDeleted i => tagged 15 (Codec.toBytes i)
  | .budget b => tagged 16 (Codec.toBytes b)
  | .budgetDeleted i => tagged 17 (Codec.toBytes i)
  | .invoice i => tagged 18 (Codec.toBytes i)
  | .invoiceDeleted i => tagged 19 (Codec.toBytes i)
  | .blob b => tagged 20 (Codec.toBytes b)
  | .blobDeleted s => tagged 21 (Codec.toBytes s)
  | .batch b => tagged 22 (Codec.toBytes b)
  | .counter n v => tagged 23 (Codec.toBytes (n, v))
  | .fingerprint f => tagged 24 (Codec.toBytes f)

/-- Reads one change, by tag. -/
def decChangeTag : Nat → List UInt8 → Option (Change × List UInt8)
  | 0, bs => readAs Realm bs .realm
  | 1, bs => readAs Member bs .member
  | 2, bs => readAs MemberId bs .memberDeleted
  | 3, bs => readAs Account bs .account
  | 4, bs => readAs AccountId bs .accountDeleted
  | 5, bs => readAs Label bs .label
  | 6, bs => readAs LabelId bs .labelDeleted
  | 7, bs => readAs Party bs .party
  | 8, bs => readAs PartyGroup bs .group
  | 9, bs => readAs String bs .groupDeleted
  | 10, bs => readAs Trip bs .trip
  | 11, bs => readAs String bs .tripDeleted
  | 12, bs => readAs Rule bs .rule
  | 13, bs => readAs RuleId bs .ruleDeleted
  | 14, bs => readAs Transaction bs .txn
  | 15, bs => readAs TxId bs .txnDeleted
  | 16, bs => readAs BudgetState bs .budget
  | 17, bs => readAs BudgetId bs .budgetDeleted
  | 18, bs => readAs InvoiceState bs .invoice
  | 19, bs => readAs InvoiceId bs .invoiceDeleted
  | 20, bs => readAs BlobState bs .blob
  | 21, bs => readAs String bs .blobDeleted
  | 22, bs => readAs ImportBatch bs .batch
  | 23, bs => readAs (String × Int) bs (fun (n, v) => .counter n v)
  | 24, bs => readAs String bs .fingerprint
  | _, _ => none

/-- Reads one change: the tag, then whatever that tag says follows. -/
def decChange (bs : List UInt8) : Option (Change × List UInt8) :=
  match decNat bs with
  | none => none
  | some (t, rest) => decChangeTag t rest

instance : Codec Change where
  toBytes := encChange
  ofBytes := decChange

instance : LawfulCodec Change where
  ofBytes_toBytes c rest := by
    show decChange (encChange c ++ rest) = some (c, rest)
    cases c <;> simp [encChange, decChange, decChangeTag, tagged, List.append_assoc]

/-- The bound of each change's payload, one line per tag in `encChange`. -/
def Change.wf : Change → Bool
  | .realm r => Wellformed.wf r
  | .member m => Wellformed.wf m
  | .memberDeleted i => Wellformed.wf i
  | .account a => Wellformed.wf a
  | .accountDeleted i => Wellformed.wf i
  | .label l => Wellformed.wf l
  | .labelDeleted i => Wellformed.wf i
  | .party p => Wellformed.wf p
  | .group g => Wellformed.wf g
  | .groupDeleted n => Wellformed.wf n
  | .trip t => Wellformed.wf t
  | .tripDeleted n => Wellformed.wf n
  | .rule r => Wellformed.wf r
  | .ruleDeleted i => Wellformed.wf i
  | .txn t => Wellformed.wf t
  | .txnDeleted i => Wellformed.wf i
  | .budget b => Wellformed.wf b
  | .budgetDeleted i => Wellformed.wf i
  | .invoice i => Wellformed.wf i
  | .invoiceDeleted i => Wellformed.wf i
  | .blob b => Wellformed.wf b
  | .blobDeleted s => Wellformed.wf s
  | .batch b => Wellformed.wf b
  | .counter n v => Wellformed.wf (n, v)
  | .fingerprint f => Wellformed.wf f

instance : Wellformed Change := ⟨Change.wf⟩

/-! ## The two hashes -/

namespace Encode

/-- The canonical bytes of a state. -/
def stateBytes (s : State) : ByteArray := Codec.encode s

/-- The canonical bytes of an event. -/
def eventBytes (e : Event) : ByteArray := Codec.encode e

/-- The SHA-256 of a state's canonical bytes, in hex: what a checkpoint commits to. -/
def hashState (s : State) : String := Sha256.hexBytes (stateBytes s)

/-- The SHA-256 of an event's canonical bytes, in hex: what a signature covers. -/
def hashEvent (e : Event) : String := Sha256.hexBytes (eventBytes e)

end Encode

end Resources
