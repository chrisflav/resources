import Std

/-!
# A canonical binary encoding

Checkpoints hash a `State` and signatures cover an `Event`, so both need one
byte-exact encoding that two machines agree on without negotiating. This file is
the machinery — a class, the primitives and the combinators — and
`Core/Encode.lean` is the instance for every type the ledger actually holds.

A codec is a writer and a reader over `List UInt8`. The reader is handed the
bytes that are left rather than an array and an index, which is what makes the
law compose:

    decode (encode x ++ rest) = some (x, rest)

says the reader stops exactly where the writer stopped. A product is then proved
from its two factors by rewriting twice, a list from its element by induction,
and no arithmetic about offsets appears anywhere. `ByteArray` is the public face,
because that is what hashing and the wire want; lists are the proof-facing form,
and the two meet at a single `Array.toList` in `Codec.encode` and `Codec.decode`.

The format. Naturals are LEB128: seven bits per byte, little-endian, high bit set
on every byte but the last, so a number below 128 is one byte. Integers are a
LEB128 sign — `0` for non-negative, `1` for negative — followed by the LEB128
magnitude. `Bool` is a LEB128 `0` or `1`. `UInt8` is itself. Strings, byte arrays
and lists carry a LEB128 length first, strings as their UTF-8 bytes. `Option` is
a `0` tag or a `1` tag and a value. A product is its two halves, in order. Every
constructor of a sum gets a LEB128 tag, which is `tagged` below. Nothing is
aligned, nothing is padded, and no length depends on the platform, so one value
has exactly one encoding on every machine.

And — since the decoder is the direction that matters for content addressing —
one encoding has exactly one value. `decNat` refuses overlong LEB128 and `decInt`
refuses negative zero, so the reader takes nothing the writer would not have
written; `CanonicalCodec` below is that statement, proved for the primitives and
for every combinator over them.

One thing more is refused, and it is about size rather than about shape: a year,
an exponent or a count of minor units far outside anything the ledger means. That
is `Wellformed`, near the bottom of this file, and the section there says why it
lives beside the decoder rather than inside it.

*What it costs.* The reader is linear in the bytes it consumes and recurses in
no proportion to them. Two things used to make that false, and both are about a
reader handed a list rather than an array and an index: reading a length-prefixed
value asked `rest.length < n`, which walks everything that is left, so a string
near the front of a megabyte cost a megabyte; and `decNat` recursed once per
continuation byte and combined on the way back out, so a crafted run of `0x80` —
one byte each to send — was a stack frame each to read. `splitExactly` and
`decNatGo` are the answers: both walk exactly what they consume, and both are
tail-recursive, so they are loops. The remaining cost that is not linear is
`Filter`'s reader, which takes the length of the input as its fuel and so pays
one walk per filter it reads; that is a fact about `Core/Encode.lean` and is
noted there.
-/

namespace Resources

/-! ## The classes -/

/--
A byte encoding for `α`, and a reader that takes one `α` off the front of a
byte list and hands back what it did not consume.
-/
class Codec (α : Type) where
  /-- The bytes `x` encodes to. -/
  toBytes : α → List UInt8
  /-- Reads one value off the front, returning it and the bytes after it. -/
  ofBytes : List UInt8 → Option (α × List UInt8)

/--
The round-trip law, in the form that composes: reading back an encoded value
returns it and stops exactly where the writer stopped, whatever follows it.

Stated with a trailing `rest` rather than as `ofBytes (toBytes x) = some (x, [])`
because that is what a product, a list and a tagged sum need from their parts —
each of those puts something after the value it is proving about.
-/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /-- Decoding an encoded value returns it and leaves everything after it untouched. -/
  ofBytes_toBytes (x : α) (rest : List UInt8) :
    Codec.ofBytes (Codec.toBytes x ++ rest) = some (x, rest)

attribute [simp] LawfulCodec.ofBytes_toBytes

/-! ## Naturals: LEB128 -/

/--
LEB128: seven bits of `n` per byte, least significant first, with the high bit
set on every byte but the last. Numbers below 128 take one byte, which is what
makes constructor tags cheap.
-/
def encNat (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 128 + 128) :: encNat (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/--
Reads a LEB128 natural, seven bits at a time, into an accumulator.

Tail-recursive on purpose. The obvious reader recurses once per continuation
byte and combines on the way back out, so a crafted run of `0x80` — which costs
a sender one byte each — is a stack frame each on every reader, and the Lean one
fell over where an index-based port merely threw. Here the recursion is the last
thing the function does, so it is a loop, and the work is one pass over the
bytes the number is written in and nothing else.

`shift` is `128 ^ k` after `k` continuation bytes and `acc` is what they have
contributed. Overlong encodings are refused: `[0x80, 0x00]` is `0` written in two
bytes, and a reader that accepted it gave every natural — every constructor tag,
every length prefix, every amount — unboundedly many encodings. That is fatal
for a format whose whole job is content addressing: two different byte strings
would decode to the same event, and a state read back from a checkpoint would
not re-encode to the bytes its hash was taken over. The rule is one line: a
continuation byte has to contribute something, so the byte that ends the number
may not be zero unless it is the only byte there is — which is the same rule as
before, read from the front instead of from the back.
-/
def decNatGo (shift acc : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then
      if b.toNat = 0 ∧ shift ≠ 1 then none else some (acc + shift * b.toNat, bs)
    else decNatGo (shift * 128) (acc + shift * (b.toNat - 128)) bs

/-- Reads a LEB128 natural off the front of a byte string. -/
def decNat (bs : List UInt8) : Option (Nat × List UInt8) := decNatGo 1 0 bs

/-- LEB128 round-trips into the accumulator, for every natural that may end a number. -/
theorem decNatGo_encNat : ∀ (n shift acc : Nat) (rest : List UInt8), (n ≠ 0 ∨ shift = 1) →
    decNatGo shift acc (encNat n ++ rest) = some (acc + shift * n, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro shift acc rest hok
    rw [encNat]
    split
    · next h =>
      have hb : (UInt8.ofNat n).toNat = n :=
        UInt8.toNat_ofNat_of_lt' (by have : UInt8.size = 256 := rfl; omega)
      have hne : ¬ (n = 0 ∧ shift ≠ 1) := by
        rcases hok with hn | hs
        · exact fun hc => hn hc.1
        · exact fun hc => hc.2 hs
      simp only [List.cons_append, List.nil_append, decNatGo, hb, if_pos h, if_neg hne]
    · next h =>
      have hm : n % 128 < 128 := Nat.mod_lt _ (by omega)
      have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 :=
        UInt8.toNat_ofNat_of_lt' (by have : UInt8.size = 256 := rfl; omega)
      have hq : n / 128 ≠ 0 := by
        have : 0 < n / 128 := Nat.div_pos (by omega) (by omega)
        omega
      have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih (n / 128) hlt (shift * 128) (acc + shift * (n % 128 + 128 - 128)) rest
        (Or.inl hq)
      have harith : acc + shift * (n % 128 + 128 - 128) + shift * 128 * (n / 128)
          = acc + shift * n := by
        have hmd : n % 128 + 128 * (n / 128) = n := Nat.mod_add_div n 128
        have hsub : n % 128 + 128 - 128 = n % 128 := by omega
        rw [hsub, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, hmd]
      simp only [List.cons_append, decNatGo, hb,
        if_neg (by omega : ¬ n % 128 + 128 < 128), hrec, harith]

/-- LEB128 round-trips, for every natural and whatever follows it. -/
@[simp] theorem decNat_encNat (n : Nat) (rest : List UInt8) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  have := decNatGo_encNat n 1 0 rest (Or.inr rfl)
  simpa [decNat] using this

instance : Codec Nat where
  toBytes := encNat
  ofBytes := decNat

instance : LawfulCodec Nat where
  ofBytes_toBytes _ _ := decNat_encNat _ _

/-! ## Tags -/

/--
A constructor tag and its payload. Tags are LEB128 naturals, so every tag below
128 — which is all of them here — costs exactly one byte, and reading one back
is the natural law rather than a new argument about bytes.
-/
def tagged (n : Nat) (body : List UInt8) : List UInt8 := encNat n ++ body

/--
Reads one `α` and wraps it with `f`, keeping the remainder. Every tagged
decoder below is a `match` on the tag whose branches are calls to this.
-/
def readAs (α : Type) [Codec α] {β : Type} (bs : List UInt8) (f : α → β) :
    Option (β × List UInt8) :=
  match Codec.ofBytes (α := α) bs with
  | some (x, rest) => some (f x, rest)
  | none => none

/-- Reading back what was written is the value, wrapped. -/
@[simp] theorem readAs_toBytes {α β : Type} [Codec α] [LawfulCodec α] (x : α)
    (rest : List UInt8) (f : α → β) :
    readAs α (Codec.toBytes x ++ rest) f = some (f x, rest) := by
  simp [readAs]

/-- A tag followed by a payload splits back into the tag and the payload. -/
@[simp] theorem decNat_tagged (n : Nat) (body rest : List UInt8) :
    decNat (tagged n body ++ rest) = some (n, body ++ rest) := by
  simp [tagged, List.append_assoc]

/-! ## The other primitives -/

/-- A byte is its own encoding. -/
instance : Codec UInt8 where
  toBytes b := [b]
  ofBytes
    | [] => none
    | b :: bs => some (b, bs)

instance : LawfulCodec UInt8 where
  ofBytes_toBytes _ _ := rfl

/-- `false` is `0`, `true` is `1`; anything else is not a boolean. -/
instance : Codec Bool where
  toBytes b := encNat (if b then 1 else 0)
  ofBytes bs :=
    match decNat bs with
    | some (0, rest) => some (false, rest)
    | some (1, rest) => some (true, rest)
    | _ => none

instance : LawfulCodec Bool where
  ofBytes_toBytes b rest := by
    cases b <;> simp [Codec.toBytes, Codec.ofBytes]

/-- A sign byte — `0` non-negative, `1` negative — and the LEB128 magnitude. -/
def encInt (i : Int) : List UInt8 :=
  if i < 0 then tagged 1 (encNat i.natAbs) else tagged 0 (encNat i.natAbs)

/--
Inverse of `encInt`.

Negative zero is refused for the reason overlong naturals are: `[0x01, 0x00]`
and `[0x00, 0x00]` both meant `0`, so an amount had two encodings and a
transaction carrying it had two hashes.
-/
def decInt (bs : List UInt8) : Option (Int × List UInt8) :=
  match decNat bs with
  | some (0, rest) => (decNat rest).map (fun p => ((p.1 : Int), p.2))
  | some (1, rest) =>
    match decNat rest with
    | some (0, _) => none
    | some (m, r) => some (-(m : Int), r)
    | none => none
  | _ => none

instance : Codec Int where
  toBytes := encInt
  ofBytes := decInt

instance : LawfulCodec Int where
  ofBytes_toBytes i rest := by
    by_cases h : i < 0
    · obtain ⟨k, hk⟩ : ∃ k, i.natAbs = k + 1 := ⟨i.natAbs - 1, by omega⟩
      have hval : -((k + 1 : Nat) : Int) = i := by omega
      simp only [Codec.toBytes, Codec.ofBytes, encInt, if_pos h, tagged, List.append_assoc,
        decInt, decNat_encNat, hk, hval]
    · simp only [Codec.toBytes, Codec.ofBytes, encInt, if_neg h, tagged, List.append_assoc,
        decInt, decNat_encNat, Option.map_some]
      have : (i.natAbs : Int) = i := by omega
      simp [this]

/-! ## Length-prefixed bytes and text -/

/-- The bytes of a `ByteArray`, as a list: the form the proofs work in. -/
def bytesToList (b : ByteArray) : List UInt8 := b.data.toList

/-- A list of bytes, as a `ByteArray`: the form the callers work in. -/
def bytesOfList (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- Listing a byte array's bytes and putting them back gives it again. -/
@[simp] theorem bytesOfList_bytesToList (b : ByteArray) : bytesOfList (bytesToList b) = b := by
  simp [bytesOfList, bytesToList]

/-- Building a byte array from a list and listing it again gives the list. -/
@[simp] theorem bytesToList_bytesOfList (l : List UInt8) : bytesToList (bytesOfList l) = l := by
  simp [bytesOfList, bytesToList]

/-- A byte array has as many list entries as it has bytes. -/
@[simp] theorem length_bytesToList (b : ByteArray) : (bytesToList b).length = b.size := by
  simp only [bytesToList, Array.length_toList]
  rfl

/-! ### Taking a fixed number of bytes

A length-prefixed reader has to say whether the bytes it was promised are there.
Asking `rest.length < n` answers it by walking everything that is left — so
reading a string near the front of a megabyte costs a megabyte, and a state with
a few thousand strings in it costs that many megabytes. The two implementations
then agree on the bytes and not on whether they can be read at all: an
index-based port opens a checkpoint in a second where this one takes minutes.

`splitExactly` walks `n` bytes and stops, and it is tail-recursive through an
accumulator, so it is a loop rather than a stack frame per byte. What it costs
is what it consumes, which is what makes the whole decoder linear in its input.
-/

/-- Splits `n` bytes off the front, reversing the accumulator at the end. -/
def splitGo : Nat → List UInt8 → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, acc, bs => some (acc.reverse, bs)
  | _ + 1, _, [] => none
  | n + 1, acc, b :: bs => splitGo n (b :: acc) bs

/-- Exactly `n` bytes, and what follows them, or nothing when there are not `n`. -/
def splitExactly (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  splitGo n [] bs

/-- Taking as many bytes as were written takes exactly those bytes. -/
theorem splitGo_append : ∀ (xs acc rest : List UInt8),
    splitGo xs.length acc (xs ++ rest) = some (acc.reverse ++ xs, rest)
  | [], acc, rest => by simp [splitGo]
  | x :: xs, acc, rest => by
    simp only [List.length_cons, List.cons_append, splitGo, splitGo_append xs (x :: acc) rest,
      List.reverse_cons]
    simp

/-- Taking as many bytes as were written takes exactly those bytes. -/
@[simp] theorem splitExactly_append (xs rest : List UInt8) :
    splitExactly xs.length (xs ++ rest) = some (xs, rest) := by
  simpa [splitExactly] using splitGo_append xs [] rest

/-- What the accumulating split accepted is `n` bytes off the front and no more. -/
theorem splitGo_spec : ∀ (n : Nat) (acc bs xs rest : List UInt8),
    splitGo n acc bs = some (xs, rest) →
      ∃ ys : List UInt8, ys.length = n ∧ bs = ys ++ rest ∧ xs = acc.reverse ++ ys
  | 0, acc, bs, xs, rest, h => by
    simp only [splitGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, by simp⟩
  | _ + 1, _, [], _, _, h => by simp [splitGo] at h
  | n + 1, acc, b :: bs, xs, rest, h => by
    simp only [splitGo] at h
    obtain ⟨ys, hlen, hbs, hxs⟩ := splitGo_spec n (b :: acc) bs xs rest h
    refine ⟨b :: ys, by simp [hlen], by simp [hbs], ?_⟩
    rw [hxs]
    simp

/-- What the split accepted is `n` bytes off the front and no more. -/
theorem splitExactly_spec {n : Nat} {bs xs rest : List UInt8}
    (h : splitExactly n bs = some (xs, rest)) : xs.length = n ∧ bs = xs ++ rest := by
  obtain ⟨ys, hlen, hbs, hxs⟩ := splitGo_spec n [] bs xs rest h
  simp only [List.reverse_nil, List.nil_append] at hxs
  subst hxs
  exact ⟨hlen, hbs⟩

/-- The byte count, then the bytes. -/
instance : Codec ByteArray where
  toBytes b := encNat b.size ++ bytesToList b
  ofBytes bs :=
    match decNat bs with
    | none => none
    | some (n, rest) =>
      match splitExactly n rest with
      | none => none
      | some (body, after) => some (bytesOfList body, after)

instance : LawfulCodec ByteArray where
  ofBytes_toBytes b rest := by
    have hsize : (bytesToList b).length = b.size := length_bytesToList b
    simp only [Codec.toBytes, Codec.ofBytes, List.append_assoc, decNat_encNat, ← hsize,
      splitExactly_append, bytesOfList_bytesToList]

/-- The UTF-8 byte count, then the UTF-8 bytes. -/
instance : Codec String where
  toBytes s := encNat s.toUTF8.size ++ bytesToList s.toUTF8
  ofBytes bs :=
    match decNat bs with
    | none => none
    | some (n, rest) =>
      match splitExactly n rest with
      | none => none
      | some (body, after) => (String.fromUTF8? (bytesOfList body)).map (fun s => (s, after))

/-- UTF-8 bytes that came from a string are valid, so they decode back to it. -/
@[simp] theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dif_pos s.isValidUTF8]
  rfl

instance : LawfulCodec String where
  ofBytes_toBytes s rest := by
    have hsize : (bytesToList s.toUTF8).length = s.toUTF8.size := length_bytesToList _
    simp only [Codec.toBytes, Codec.ofBytes, List.append_assoc, decNat_encNat, ← hsize,
      splitExactly_append, bytesOfList_bytesToList, fromUTF8?_toUTF8, Option.map_some]

/-! ## Combinators -/

/-- The first half, then the second. -/
instance {α β : Type} [Codec α] [Codec β] : Codec (α × β) where
  toBytes p := Codec.toBytes p.1 ++ Codec.toBytes p.2
  ofBytes bs :=
    match Codec.ofBytes (α := α) bs with
    | none => none
    | some (a, bs) =>
      match Codec.ofBytes (α := β) bs with
      | none => none
      | some (b, bs) => some ((a, b), bs)

instance {α β : Type} [Codec α] [Codec β] [LawfulCodec α] [LawfulCodec β] :
    LawfulCodec (α × β) where
  ofBytes_toBytes p rest := by
    simp [Codec.toBytes, Codec.ofBytes, List.append_assoc]

/-- A `0` tag for nothing, a `1` tag and the value for something. -/
instance {α : Type} [Codec α] : Codec (Option α) where
  toBytes
    | none => tagged 0 []
    | some x => tagged 1 (Codec.toBytes x)
  ofBytes bs :=
    match decNat bs with
    | some (0, rest) => some (none, rest)
    | some (1, rest) => readAs α rest some
    | _ => none

instance {α : Type} [Codec α] [LawfulCodec α] : LawfulCodec (Option α) where
  ofBytes_toBytes x rest := by
    cases x <;> simp [Codec.toBytes, Codec.ofBytes]

/-- The elements' encodings, run together; the length that precedes them is `encList`'s. -/
def encMany {α : Type} [Codec α] : List α → List UInt8
  | [] => []
  | x :: xs => Codec.toBytes x ++ encMany xs

/-- Reads exactly `n` elements. The count comes from the length prefix. -/
def decMany (α : Type) [Codec α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match Codec.ofBytes (α := α) bs with
    | none => none
    | some (x, bs) =>
      match decMany α n bs with
      | none => none
      | some (xs, bs) => some (x :: xs, bs)

/-- Reading back exactly as many elements as were written gives the list. -/
@[simp] theorem decMany_encMany {α : Type} [Codec α] [LawfulCodec α] :
    ∀ (xs : List α) (rest : List UInt8),
      decMany α xs.length (encMany xs ++ rest) = some (xs, rest)
  | [], rest => rfl
  | x :: xs, rest => by
    simp [encMany, decMany, List.append_assoc, decMany_encMany xs rest]

/-- The element count, then the elements. -/
instance {α : Type} [Codec α] : Codec (List α) where
  toBytes xs := encNat xs.length ++ encMany xs
  ofBytes bs :=
    match decNat bs with
    | none => none
    | some (n, rest) => decMany α n rest

instance {α : Type} [Codec α] [LawfulCodec α] : LawfulCodec (List α) where
  ofBytes_toBytes xs rest := by
    simp [Codec.toBytes, Codec.ofBytes, List.append_assoc]

/-! ## Canonicity

The law above says the reader accepts what the writer wrote. This one says it
accepts nothing else: whatever comes back out of a byte string is a value whose
own encoding is that byte string again.

Round-tripping is what makes a format usable; this is what makes it a *name*. A
checkpoint is the hash of these bytes, so a reader that accepts a second spelling
of a state will hash what it re-encodes to something the sender never committed
to, and honest peers disagree about whether a checkpoint verifies. The same goes
for an event: two spellings mean two hashes for one decision, and any dedupe or
replay check keyed on the hash has a hole in it.

Proved below for the primitives and for every combinator built on them. The
structures in `Core/Encode.lean` inherit it through `ofIso` exactly when the
rebuild is injective — which for `State` it is not, because a hash map is rebuilt
from its entries, so that one is checked inside the decoder instead.
-/

/-- Nothing but the canonical bytes decodes: what the reader takes, the writer wrote. -/
class CanonicalCodec (α : Type) [Codec α] : Prop where
  /-- Anything the reader accepts is exactly what the writer would have written. -/
  toBytes_ofBytes (bs : List UInt8) (x : α) (rest : List UInt8) :
    Codec.ofBytes bs = some (x, rest) → bs = Codec.toBytes x ++ rest

/-- A byte is below the size of a byte. -/
private theorem toNat_lt_256 (b : UInt8) : b.toNat < 256 := by
  have h1 : b.toNat < UInt8.size := b.toNat_lt_size
  have h2 : UInt8.size = 256 := rfl
  omega

/--
A LEB128 natural the accumulating reader accepted is one the writer would have
written, with the accumulator and the shift read off it.
-/
theorem encNat_decNatGo : ∀ (bs : List UInt8) (shift acc n : Nat) (rest : List UInt8),
    0 < shift → decNatGo shift acc bs = some (n, rest) →
      ∃ m : Nat, n = acc + shift * m ∧ bs = encNat m ++ rest ∧ (m ≠ 0 ∨ shift = 1)
  | [], _, _, _, _, _, h => by simp [decNatGo] at h
  | b :: bs, shift, acc, n, rest, hs, h => by
    simp only [decNatGo] at h
    by_cases hlt : b.toNat < 128
    · rw [if_pos hlt] at h
      by_cases hz : b.toNat = 0 ∧ shift ≠ 1
      · rw [if_pos hz] at h; simp at h
      · rw [if_neg hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨b.toNat, rfl, ?_, ?_⟩
        · rw [encNat, if_pos hlt, UInt8.ofNat_toNat]
          simp
        · by_cases hone : shift = 1
          · exact Or.inr hone
          · exact Or.inl (fun hc => hz ⟨hc, hone⟩)
    · rw [if_neg hlt] at h
      have hs' : 0 < shift * 128 := by omega
      obtain ⟨m, hn, hbs, hm⟩ := encNat_decNatGo bs (shift * 128)
        (acc + shift * (b.toNat - 128)) n rest hs' h
      have hmne : m ≠ 0 := by
        rcases hm with hm | hc
        · exact hm
        · omega
      have hb := toNat_lt_256 b
      refine ⟨b.toNat - 128 + 128 * m, ?_, ?_, Or.inl (by omega)⟩
      · rw [hn, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
      · have hmod : (b.toNat - 128 + 128 * m) % 128 = b.toNat - 128 := by omega
        have hdiv : (b.toNat - 128 + 128 * m) / 128 = m := by omega
        have hback : b.toNat - 128 + 128 = b.toNat := by omega
        rw [encNat, if_neg (by omega), hmod, hdiv, hback, UInt8.ofNat_toNat, hbs]
        simp

/-- A LEB128 natural the reader accepted is the one the writer would have written. -/
theorem encNat_decNat (bs : List UInt8) (n : Nat) (rest : List UInt8)
    (h : decNat bs = some (n, rest)) : bs = encNat n ++ rest := by
  obtain ⟨m, hn, hbs, -⟩ := encNat_decNatGo bs 1 0 n rest (by omega) h
  rw [hn]
  simpa using hbs

instance : CanonicalCodec Nat where
  toBytes_ofBytes bs n rest h := encNat_decNat bs n rest h

instance : CanonicalCodec UInt8 where
  toBytes_ofBytes bs x rest h := by
    cases bs with
    | nil => simp [Codec.ofBytes] at h
    | cons b bs =>
      simp only [Codec.ofBytes, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

instance : CanonicalCodec Bool where
  toBytes_ofBytes bs x rest h := by
    simp only [Codec.ofBytes] at h
    cases hn : decNat bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      match n with
      | 0 =>
        simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact encNat_decNat bs 0 r hn
      | 1 =>
        simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact encNat_decNat bs 1 r hn
      | (_ + 2) => simp [hn] at h

instance : CanonicalCodec Int where
  toBytes_ofBytes bs x rest h := by
    simp only [Codec.ofBytes, decInt] at h
    cases hn : decNat bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨sign, r⟩ := p
      match sign with
      | 0 =>
        simp only [hn] at h
        cases hm : decNat r with
        | none => simp [hm] at h
        | some q =>
          obtain ⟨m, r'⟩ := q
          simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hz : ¬ ((m : Int) < 0) := by omega
          have habs : (m : Int).natAbs = m := by omega
          rw [encNat_decNat bs 0 r hn, encNat_decNat r m r' hm]
          simp [Codec.toBytes, encInt, if_neg hz, habs, tagged, List.append_assoc]
      | 1 =>
        simp only [hn] at h
        cases hm : decNat r with
        | none => simp [hm] at h
        | some q =>
          obtain ⟨m, r'⟩ := q
          match m with
          | 0 => simp [hm] at h
          | (k + 1) =>
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have habs : ((k : Int) + 1).natAbs = k + 1 := by omega
            rw [encNat_decNat bs 1 r hn, encNat_decNat r (k + 1) r' hm]
            simp [Codec.toBytes, encInt, tagged, List.append_assoc, habs]
      | (_ + 2) => simp [hn] at h

instance : CanonicalCodec ByteArray where
  toBytes_ofBytes bs x rest h := by
    simp only [Codec.ofBytes] at h
    cases hn : decNat bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only [hn] at h
      cases hsp : splitExactly n r with
      | none => simp [hsp] at h
      | some q =>
        obtain ⟨body, after⟩ := q
        simp only [hsp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlen, hr⟩ := splitExactly_spec hsp
        have hsz : (bytesOfList body).size = n := by
          rw [← length_bytesToList, bytesToList_bytesOfList, hlen]
        show bs = (encNat (bytesOfList body).size ++ bytesToList (bytesOfList body)) ++ after
        rw [bytesToList_bytesOfList, hsz, encNat_decNat bs n r hn, hr, List.append_assoc]

/-- The bytes a string was read out of are the bytes it writes. -/
theorem toUTF8_of_fromUTF8? {b : ByteArray} {s : String} (h : String.fromUTF8? b = some s) :
    s.toUTF8 = b := by
  simp only [String.fromUTF8?] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ByteArray.ext rfl
  · simp at h

instance : CanonicalCodec String where
  toBytes_ofBytes bs x rest h := by
    simp only [Codec.ofBytes] at h
    cases hn : decNat bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only [hn] at h
      cases hsp : splitExactly n r with
      | none => simp [hsp] at h
      | some q =>
        obtain ⟨body, after⟩ := q
        simp only [hsp] at h
        cases hu : String.fromUTF8? (bytesOfList body) with
        | none => simp [hu] at h
        | some y =>
          simp only [hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlen, hr⟩ := splitExactly_spec hsp
          have hbytes := toUTF8_of_fromUTF8? hu
          have hsz : (bytesOfList body).size = n := by
            rw [← length_bytesToList, bytesToList_bytesOfList, hlen]
          show bs = (encNat y.toUTF8.size ++ bytesToList y.toUTF8) ++ after
          rw [hbytes, bytesToList_bytesOfList, hsz, encNat_decNat bs n r hn, hr,
            List.append_assoc]

instance {α β : Type} [Codec α] [Codec β] [CanonicalCodec α] [CanonicalCodec β] :
    CanonicalCodec (α × β) where
  toBytes_ofBytes bs x rest h := by
    simp only [Codec.ofBytes] at h
    cases ha : Codec.ofBytes (α := α) bs with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨a, r⟩ := p
      simp only [ha] at h
      cases hb : Codec.ofBytes (α := β) r with
      | none => simp [hb] at h
      | some q =>
        obtain ⟨b, r'⟩ := q
        simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [CanonicalCodec.toBytes_ofBytes bs a r ha, CanonicalCodec.toBytes_ofBytes r b r' hb]
        simp [Codec.toBytes, List.append_assoc]

instance {α : Type} [Codec α] [CanonicalCodec α] : CanonicalCodec (Option α) where
  toBytes_ofBytes bs x rest h := by
    simp only [Codec.ofBytes] at h
    cases hn : decNat bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      match n with
      | 0 =>
        simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [encNat_decNat bs 0 r hn]
        simp [Codec.toBytes, tagged]
      | 1 =>
        simp only [hn, readAs] at h
        cases hy : Codec.ofBytes (α := α) r with
        | none => simp [hy] at h
        | some q =>
          obtain ⟨y, r'⟩ := q
          simp only [hy, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [encNat_decNat bs 1 r hn, CanonicalCodec.toBytes_ofBytes r y r' hy]
          simp [Codec.toBytes, tagged, List.append_assoc]
      | (_ + 2) => simp [hn] at h

/-- Reading exactly `n` elements reads `n` of them, and reads them canonically. -/
theorem encMany_decMany {α : Type} [Codec α] [CanonicalCodec α] :
    ∀ (n : Nat) (bs : List UInt8) (xs : List α) (rest : List UInt8),
      decMany α n bs = some (xs, rest) → xs.length = n ∧ bs = encMany xs ++ rest
  | 0, bs, xs, rest, h => by
    simp only [decMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encMany]
  | n + 1, bs, xs, rest, h => by
    simp only [decMany] at h
    cases hy : Codec.ofBytes (α := α) bs with
    | none => simp [hy] at h
    | some p =>
      obtain ⟨y, r⟩ := p
      simp only [hy] at h
      cases hys : decMany α n r with
      | none => simp [hys] at h
      | some q =>
        obtain ⟨ys, r'⟩ := q
        simp only [hys, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlen, hbs⟩ := encMany_decMany n r ys r' hys
        refine ⟨by simp [hlen], ?_⟩
        rw [CanonicalCodec.toBytes_ofBytes bs y r hy, hbs]
        simp [encMany, List.append_assoc]

instance {α : Type} [Codec α] [CanonicalCodec α] : CanonicalCodec (List α) where
  toBytes_ofBytes bs xs rest h := by
    simp only [Codec.ofBytes] at h
    cases hn : decNat bs with
    | none => simp [hn] at h
    | some p =>
      obtain ⟨n, r⟩ := p
      simp only [hn] at h
      obtain ⟨hlen, hbs⟩ := encMany_decMany n r xs rest h
      rw [encNat_decNat bs n r hn, hbs]
      simp only [Codec.toBytes, ← hlen, List.append_assoc]

/-! ## Transport along a retraction -/

/--
The codec `α` inherits by being carried into a type that has one.

Every structure below is encoded this way: `f` flattens it into nested products
and `g` puts it back together. Only `g ∘ f = id` is needed — `f` may throw
information away in the other direction, and for `State` it does.
-/
@[instance_reducible]
def Codec.ofIso {α β : Type} [Codec β] (f : α → β) (g : β → α) : Codec α where
  toBytes x := Codec.toBytes (f x)
  ofBytes bs := (Codec.ofBytes (α := β) bs).map (fun p => (g p.1, p.2))

/-- The law travels with the retraction: if `g` undoes `f`, the transported codec is lawful. -/
theorem Codec.lawful_ofIso {α β : Type} [Codec β] [LawfulCodec β] {f : α → β} {g : β → α}
    (h : ∀ x, g (f x) = x) : @LawfulCodec α (Codec.ofIso f g) := by
  refine @LawfulCodec.mk α (Codec.ofIso f g) ?_
  intro x rest
  show (Codec.ofBytes (α := β) (Codec.toBytes (f x) ++ rest)).map (fun p => (g p.1, p.2))
      = some (x, rest)
  simp only [LawfulCodec.ofBytes_toBytes, Option.map_some, h]

/--
The codec `α` inherits from a type it embeds in only partially.

`f` writes; `g` reads, and may refuse bytes that `f` never produces — an
out-of-range constructor tag, or a day that no month has. The law asks only that
`g` accept everything `f` writes.
-/
@[instance_reducible]
def Codec.ofRetract {α β : Type} [Codec β] (f : α → β) (g : β → Option α) : Codec α where
  toBytes x := Codec.toBytes (f x)
  ofBytes bs := (Codec.ofBytes (α := β) bs).bind (fun p => (g p.1).map (fun x => (x, p.2)))

/-- The law travels with the retraction, as long as `g` accepts everything `f` writes. -/
theorem Codec.lawful_ofRetract {α β : Type} [Codec β] [LawfulCodec β] {f : α → β}
    {g : β → Option α} (h : ∀ x, g (f x) = some x) : @LawfulCodec α (Codec.ofRetract f g) := by
  refine @LawfulCodec.mk α (Codec.ofRetract f g) ?_
  intro x rest
  show (Codec.ofBytes (α := β) (Codec.toBytes (f x) ++ rest)).bind
      (fun p => (g p.1).map (fun y => (y, p.2))) = some (x, rest)
  simp only [LawfulCodec.ofBytes_toBytes, Option.bind_some, h, Option.map_some]

/-! ## Sizes -/

/-- Every LEB128 encoding is at least one byte, which is what bounds a tag's cost. -/
theorem one_le_length_encNat (n : Nat) : 1 ≤ (encNat n).length := by
  rw [encNat]
  split <;> simp

/-- A tagged encoding is its tag and its payload, so it is longer than the payload. -/
theorem length_tagged (n : Nat) (body : List UInt8) :
    (tagged n body).length = (encNat n).length + body.length := by
  simp [tagged]

/-- A tagged encoding is at least its tag byte long. -/
theorem one_le_length_tagged (n : Nat) (body : List UInt8) : 1 ≤ (tagged n body).length := by
  have := one_le_length_encNat n
  rw [length_tagged]
  omega

/-! ## What the reader will hand back

The two laws above are about *shape*: that the bytes a value writes read back as
that value, and that nothing else reads back at all. Neither says anything about
*size*, and size is the other thing a reader has to refuse.

Three of the ledger's own types carry a number nothing bounds. A `Date` is Std's
`PlainDate`, whose year is an `Int`; a `Commodity`'s exponent is a `Nat`, and
`Commodity.scale` is `10 ^ exponent`; an `Amount` counts minor units in an `Int`.
Six bytes of LEB128 in a stranger's event is a commodity with an exponent of ten
million, and the first thing that renders an amount in it asks for a string of
that length. The reader has to say no.

It cannot say no inside `ofBytes` without making `LawfulCodec` false, and that is
not a technicality: `toBytes` is total on a type whose values are not bounded, so
the writer really can produce those bytes, and a reader that refuses what the
writer wrote does not round-trip. The bound is therefore a predicate on the
value — `Wellformed.wf` — and `Codec.decode`, which is the whole-byte-string
entry point and the only way a value enters this system from outside, checks it
after the parse. That is the same question as refusing inside the reader:
`decode` insists on consuming every byte, so a byte string is accepted exactly
when it parses *and* what it parses to is well-formed, whichever of the two is
asked first. A port is free to ask first, and will want to.

`decode_encode` now says what is true rather than slightly more: a value this
decoder would hand back is one that round-trips. `Core/Encode.lean` gives every
ledger type an instance, and the three that carry a bound are `Date`,
`Commodity` and `Amount`.
-/

/-- Which values of `α` the decoder will hand back. -/
class Wellformed (α : Type) where
  /-- Whether `x` is inside the bounds this format carries. -/
  wf : α → Bool

/-- Nothing in this type is bounded, so every value of it is one the decoder may return. -/
@[instance_reducible]
def Wellformed.unbounded (α : Type) : Wellformed α := ⟨fun _ => true⟩

/-- The bound `α` inherits by being carried into a type that has one. -/
@[instance_reducible]
def Wellformed.ofIso {α β : Type} [Wellformed β] (f : α → β) : Wellformed α :=
  ⟨fun x => Wellformed.wf (f x)⟩

instance : Wellformed Nat := Wellformed.unbounded _
instance : Wellformed Int := Wellformed.unbounded _
instance : Wellformed Bool := Wellformed.unbounded _
instance : Wellformed UInt8 := Wellformed.unbounded _
instance : Wellformed String := Wellformed.unbounded _
instance : Wellformed ByteArray := Wellformed.unbounded _

instance {α β : Type} [Wellformed α] [Wellformed β] : Wellformed (α × β) :=
  ⟨fun p => Wellformed.wf p.1 && Wellformed.wf p.2⟩

instance {α : Type} [Wellformed α] : Wellformed (Option α) :=
  ⟨fun x => match x with | none => true | some y => Wellformed.wf y⟩

instance {α : Type} [Wellformed α] : Wellformed (List α) := ⟨fun xs => xs.all Wellformed.wf⟩

/-! ## The public API -/

namespace Codec

/-- The canonical bytes of `x`. -/
def encode {α : Type} [Codec α] (x : α) : ByteArray := bytesOfList (Codec.toBytes x)

/--
Reads a value out of a byte array, insisting that it accounts for every byte and
that what it says is inside the bounds this format carries.

The `Wellformed` check is the second half of the decoder and not an afterthought:
see the section above for why it is here rather than inside `ofBytes`, and why
asking it here and asking it while reading accept exactly the same byte strings.
-/
def decode {α : Type} [Codec α] [Wellformed α] (bs : ByteArray) : Option α :=
  match Codec.ofBytes (α := α) (bytesToList bs) with
  | some (x, []) => if Wellformed.wf x then some x else none
  | _ => none

/--
The round trip, on the public API: nothing is lost and nothing is left over.

The hypothesis is the bound. A value outside it is one the writer can write and
the reader will not take back, which is the whole point of having a bound at all.
-/
theorem decode_encode {α : Type} [Codec α] [Wellformed α] [LawfulCodec α] (x : α)
    (hwf : Wellformed.wf x = true) : decode (encode x) = some x := by
  have h : bytesToList (encode x) = Codec.toBytes x := by
    simp [encode]
  have h2 := LawfulCodec.ofBytes_toBytes x ([] : List UInt8)
  simp only [decode, h, List.append_nil] at *
  rw [h2]
  exact if_pos hwf

end Codec

end Resources
