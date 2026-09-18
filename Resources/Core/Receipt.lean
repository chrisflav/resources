import Resources.Core.Ledger

/-!
# Receipts, as values

A stored file, what was read off it, and the ways its printed lines can be
divided. None of this needs the filesystem: the bytes live in the blob store and
the rows live in SQLite, but what a receipt *says* is a value, and dividing a
payment by the lines on its receipt is arithmetic over that value.
-/

namespace Resources

/--
Metadata for a stored file.

The file is named by the SHA-256 of its *plaintext*, which is what the ledger
and every transaction that attaches it call it. The last two fields are how the
same file exists on a sequencer, which is never shown a plaintext:

* `cipherHash` is the SHA-256 of the ciphertext uploaded under it, and the name
  the sequencer stores it under;
* `wrappedKey` carries the per-blob key, sealed under a realm key, as
  `realm ++ ":" ++ generation ++ ":" ++ base64(nonce ++ sealed)`. The realm and
  the generation are in front because the key that opens it is a realm key at a
  generation, and a reader that has been re-keyed since has to know which one to
  reach for. One field rather than three because this is metadata about bytes
  that live somewhere else: a reader either has all of it or none of it.

Both are `none` on a local-only store, which uploads nothing and encrypts
nothing.
-/
structure Attachment where
  sha256 : String
  mime : String
  bytes : Nat
  origName : Option String
  createdAt : String
  /-- The SHA-256 of the ciphertext this file was uploaded as, if it was. -/
  cipherHash : Option String := none
  /-- The per-blob key sealed under a realm key; see above for its framing. -/
  wrappedKey : Option String := none
  deriving Repr, Inhabited, Lean.ToJson

/--
One priced line printed on a receipt.

Amounts are signed: a till prints a correction as a negative line, and dropping
the sign would make the lines add up to something that was never charged.
-/
structure LineItem where
  description : String
  /-- How many, when the line opens with a count. -/
  qty : Option Int := none
  amount : Amount
  deriving Repr, Inhabited

/-- What was read off a scanned receipt. -/
structure Extracted where
  merchant : Option String := none
  date : Option Date := none
  total : Option Amount := none
  /--
  The priced lines, in the order they were printed. These are not required to
  add up to `total`: a service charge, a fold in the paper or a torn corner all
  leave a remainder, and pretending otherwise would lose the part that is known.
  -/
  items : List LineItem := []
  rawText : String := ""
  extractor : String := ""
  deriving Repr, Inhabited

namespace Receipts

/--
A claim on one printed line: all of it, or a count of what it covers.

A line is not always one thing. `18 FORFAIT 1/2 PENSION à 68.00` is eighteen
nights that may belong to eighteen different people, and the bill prints them
once. Rather than storing eighteen identical lines -- which would misdescribe
the paper, and would force a rounding decision for a line whose total does not
divide evenly -- a share says how many of the units it takes, and `splitParts`
hands them out without losing a minor unit.
-/
structure ItemShare where
  /-- Position in the receipt's item list, numbered from one as `receipt items` shows. -/
  line : Nat
  /-- How many of the line's units, or all that are left of it when absent. -/
  qty : Option Nat := none
  deriving Repr, Inhabited

/-- One part of a division: which printed lines go together, and where they belong. -/
structure ItemGroup where
  /-- The lines, or parts of lines, that belong together. -/
  items : List ItemShare
  /--
  Where this part's spending belongs: an account name for the store, an account
  id for `Op.divideByItems`, which has no way to create an account.
  -/
  into : String
  deriving Repr, Inhabited

end Receipts

end Resources
