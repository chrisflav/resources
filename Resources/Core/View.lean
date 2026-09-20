import Resources.Core.Ledger

/-!
# What a room can see

A realm is a key, and until now it was also a wall: an account belonged to one
realm, every leg of a transaction had to be on accounts of the realm its part
named, and money that mattered in two rooms had to be *re-entered* in both —
your books keeping the payment, the shared realm holding a copy of what it
bought, the two tied together by a mirror and a bridge. Everything crossing that
wall needed a hand-written crossing, and every one of those crossings was a
place to get it wrong.

This is the other way round. A realm sees a *set of accounts*, and a transaction
is written once. What differs between readers is not what happened but how much
of it they are shown:

* every leg on an account the view sees — the room reads the transaction as it
  is, byte for byte the same as everybody else's copy;
* some legs seen and some not — the room reads a *redaction*: the legs it may
  not see are replaced by legs on a **purse**, an account standing for the
  person those legs belong to. `Assets.Cash -560, Budget.Hut +560` becomes
  `Purse.Christian -560, Budget.Hut +560`: the room learns that 560 went into
  the pot and who put it there, and not which account of yours it left;
* no legs seen at all — the room is not told about it.

The room's own purses are things it sees, so a settlement between the pot and
the people in it is in the first case and travels verbatim. Only the entries
where money arrives from outside are ever redacted, which is what keeps the
extra work proportional to the costs rather than to everything anybody does.

Redaction happens where the transaction is written, because encryption cannot
hide part of a plaintext: what a room may not see must be gone before the bytes
are sealed to that room's key. So this is a function the author runs, and what a
reader gets is its output. A reader cannot check the legs that are not there —
no design can give them that — but `redact_accounts` below says exactly what
they can be shown, and `redact_balanced` says the arithmetic they fold is sound.

Nothing here reads the state. The owner of an account is passed in, because the
author is the one who knows it, and keeping it out means every theorem below is
about lists and amounts rather than about a ledger.
-/

namespace Resources

/--
The accounts one realm may see: its whole reading of the ledger.

`accounts` is what somebody granted it. The purses are not listed, because there
is one for every person whose money ever reaches this room and they are named
rather than opened: `purse` below says what they are called, and a reader builds
each one's balance out of the legs it is shown.
-/
structure View where
  realm : RealmId
  accounts : List AccountId
  deriving Repr, Inhabited, DecidableEq

namespace View

/--
What every purse id of this view starts with.

A room's purses are its own: two rooms showing the same person's hidden legs
name two different accounts, because a balance is about what happened in one
room and adding the two together would be counting a payment twice.
-/
def pursePrefix (v : View) : String := "purse." ++ v.realm.val ++ "."

/-- The account this view shows one person's hidden legs on. -/
def purse (v : View) (p : PartyId) : AccountId := ⟨v.pursePrefix ++ p.val⟩

/-- Whether an id names one of this view's purses. -/
def isPurse (v : View) (a : AccountId) : Bool := a.val.startsWith v.pursePrefix

/--
Whether this view sees an account as itself.

Its own purses count, and that is not a special case: a purse is where this
room's reading of somebody's money lives, so a leg already written on one is a
leg about this room.
-/
def sees (v : View) (a : AccountId) : Bool := v.accounts.contains a || v.isPurse a

/-- Granting sight of an account. Granting one twice grants it once. -/
def grant (v : View) (a : AccountId) : View :=
  if v.accounts.contains a then v else { v with accounts := v.accounts ++ [a] }

end View

/-! ## How much of one entry -/

/-- How much of a transaction a view is shown. -/
inductive Sight where
  /-- Every leg is on an account the view sees: it reads the entry as written. -/
  | whole
  /-- Some legs are and some are not: it reads a redaction. -/
  | part
  /-- None are: it is not told. -/
  | nothing
  deriving Repr, Inhabited, DecidableEq

/-- Which of the three a transaction falls into, for this view. -/
def sight (v : View) (t : Transaction) : Sight :=
  if t.postings.all (fun p => v.sees p.account) then .whole
  else if t.postings.any (fun p => v.sees p.account) then .part
  else .nothing

/-! ## The redaction itself -/

namespace Posting

/--
One leg as a view is shown it: itself, or the same amount on the purse of
whoever owns the account it is really on.

Everything else the leg carries goes with the account — the note, the party, the
import fingerprint, the tag. They describe a leg in somebody's own books, they
would say more about it than the account name they replace, and none of them is
needed to fold a balance.
-/
def through (owner : AccountId → PartyId) (v : View) (p : Posting) : Posting :=
  if v.sees p.account then p
  else { account := v.purse (owner p.account), amount := p.amount }

end Posting

/--
A transaction as a view is shown it, or `none` when the view is not shown it at
all.

The id and the date are kept, deliberately. The redaction is not another
transaction that happens to look similar: it is *this* transaction, read from
one room, and a reader that later comes to see more of the ledger has to be able
to recognise the fuller reading as the same fact rather than a second one.
-/
def redact (owner : AccountId → PartyId) (v : View) (t : Transaction) : Option Transaction :=
  match sight v t with
  | .whole => some t
  | .part => some { t with postings := t.postings.map (Posting.through owner v) }
  | .nothing => none

/-! ## What a reader is promised

Two things, and they are the whole of what makes the design safe: the arithmetic
a room folds is sound, and the names it can be shown are ones it was allowed to
see.
-/

theorem Posting.net_through (owner : AccountId → PartyId) (v : View) (c : String) (p : Posting) :
    (Posting.through owner v p).net c = p.net c := by
  unfold Posting.through
  split <;> rfl

/-- A view that sees every leg is shown the transaction as it was written. -/
theorem redact_of_whole {owner : AccountId → PartyId} {v : View} {t : Transaction}
    (h : sight v t = Sight.whole) : redact owner v t = some t := by
  unfold redact; rw [h]

/-- A view that sees no leg is not shown the transaction. -/
theorem redact_of_nothing {owner : AccountId → PartyId} {v : View} {t : Transaction}
    (h : sight v t = Sight.nothing) : redact owner v t = none := by
  unfold redact; rw [h]

/-- What a redaction is made of, in the one case where it is not the entry itself. -/
theorem redact_of_part {owner : AccountId → PartyId} {v : View} {t : Transaction}
    (h : sight v t = Sight.part) :
    redact owner v t = some { t with postings := t.postings.map (Posting.through owner v) } := by
  unfold redact; rw [h]

/-- Whatever it is shown, the totals per commodity are the ones that were written. -/
theorem redact_net {owner : AccountId → PartyId} {v : View} {t r : Transaction}
    (h : redact owner v t = some r) (c : String) : r.net c = t.net c := by
  unfold redact at h
  cases hs : sight v t with
  | whole => rw [hs] at h; injection h with h; subst h; rfl
  | part =>
    rw [hs] at h
    injection h with h
    subst h
    simp only [Transaction.net, List.map_map]
    exact congrArg List.sum (List.map_congr_left (fun p _ => Posting.net_through owner v c p))
  | nothing => rw [hs] at h; exact absurd h (by simp)

/--
A redaction balances if the transaction did.

Every leg keeps its amount and only its account can change, so the totals per
commodity are the ones that were already zero. This is why the purse is a leg
rather than a footnote: a room that folds what it is shown gets a number that is
true, not one that is short by what it was not shown.
-/
theorem redact_balanced {owner : AccountId → PartyId} {v : View} {t r : Transaction}
    (hb : t.Balanced) (h : redact owner v t = some r) : r.Balanced := by
  intro c _
  rw [redact_net h c]
  exact Transaction.net_of_balanced hb c

/--
Every account named in a redaction is one the view already sees, or a purse of
that view.

This is the sentence a reader is owed: what reaches them says nothing about
where else in the ledger the money was, only that somebody put it there. It is
also what makes a redaction stable — a room shown a purse leg is shown an account
it sees, so reading it again changes nothing.
-/
theorem redact_accounts {owner : AccountId → PartyId} {v : View} {t r : Transaction}
    (h : redact owner v t = some r) :
    ∀ a ∈ r.accounts, v.sees a = true ∨ ∃ p : PartyId, a = v.purse p := by
  unfold redact at h
  cases hs : sight v t with
  | whole =>
    rw [hs] at h
    injection h with h
    subst h
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine Or.inl ?_
    unfold sight at hs
    split at hs
    · rename_i hall
      have := List.all_eq_true.mp hall p hp
      simpa using this
    · split at hs <;> simp at hs
  | part =>
    rw [hs] at h
    injection h with h
    subst h
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hq
    unfold Posting.through
    split
    · exact Or.inl (by assumption)
    · exact Or.inr ⟨owner p.account, rfl⟩
  | nothing => rw [hs] at h; exact absurd h (by simp)

/-- A redaction is the same entry: same id, same day. -/
theorem redact_same_entry {owner : AccountId → PartyId} {v : View} {t r : Transaction}
    (h : redact owner v t = some r) : r.id = t.id ∧ r.date = t.date := by
  unfold redact at h
  cases hs : sight v t with
  | whole => rw [hs] at h; injection h with h; subst h; exact ⟨rfl, rfl⟩
  | part => rw [hs] at h; injection h with h; subst h; exact ⟨rfl, rfl⟩
  | nothing => rw [hs] at h; exact absurd h (by simp)

end Resources
