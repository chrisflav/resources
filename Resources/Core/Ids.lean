import Resources.Util
import Lean.Data.Json

/-!
# Identifiers

Every entity gets an opaque, time-sortable string id. They are wrapped in
single-field structures so an `AccountId` can never be passed where a `TxId` is
expected, while the wire and SQL representations stay plain strings.
-/

open Lean

namespace Resources

/-- Declares an opaque string-backed identifier type with the standard instances. -/
macro "declare_id " id:ident : command =>
  `(structure $id where
      val : String
    deriving DecidableEq, Repr, Inhabited, Hashable, Ord

    instance : ToString $id := ⟨fun x => x.val⟩
    instance : Lean.ToJson $id := ⟨fun x => Lean.Json.str x.val⟩
    instance : Lean.FromJson $id :=
      ⟨fun j => (fun s => ({ val := s } : $id)) <$> j.getStr?⟩)

declare_id AccountId
declare_id TxId
declare_id LabelId
declare_id PartyId
declare_id TokenId
declare_id InvoiceId
declare_id BatchId
declare_id StagedId
declare_id RuleId
declare_id BudgetId
declare_id RealmId
declare_id MemberId

/--
Generates a fresh identifier: 10 characters of millisecond timestamp followed by
16 characters of randomness, both in Crockford base32. Lexicographic order is
chronological order, which is what makes keyset pagination cheap.
-/
def freshId : IO String := do
  let ms ← nowMillis
  let rand ← IO.getRandomBytes 10
  return natToBase32 ms.toNat 10 ++ toBase32 rand

end Resources
