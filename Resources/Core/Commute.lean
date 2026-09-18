import Resources.Core.Theorems
import Std.Data.HashSet.Lemmas

/-!
# Operations that commute, and rebasing on them

A client composes an operation against the state it has seen. By the time it
arrives, other events may have been applied in front of it. Rebasing is the
question of whether it still means what it meant: if the operations in between
cannot see the one being resubmitted, and it cannot see them, then applying it
now is applying it then, and the client may resubmit without asking anybody.

This file answers that question with three things.

*A footprint.* `Op.touches`, `Op.touchesTxns` and `Op.touchesEntities` say which
entries of the state an operation names — the accounts of its postings, the
transaction ids it reads or writes, the labels, parties, blobs and the rest.
They are syntax: reading them takes no state, which is what lets a client decide
a rebase before it has replayed anything. `Op.Independent` is disjointness of
two footprints, and it is decidable.

*A theorem.* `applyOp_comm` says that two independent operations reach the same
state either way round, and `applyOp_success_comm` — the one a rebase needs —
says that an operation that was going to succeed still succeeds after an
independent one has been applied in front of it.

*A decision procedure.* `Rebase.check` is what the node's sync calls, and
`rebase_sound` is the theorem that makes its answer worth acting on.

## What is covered, and why not everything

`Op.Rebasable` names the operations the theorems cover, and they are the common
case: `putTransaction`, `deleteTransaction`, `raiseClaim`, `putLabel`,
`putParty`, `putGroup`, `deleteGroup`, `putTrip`, `deleteTrip`, `putRule`,
`registerBlob`, `attach`, `detach`, `forgetBlob` and `recordImportBatch`. Each
has the same shape — its whole effect is one entry of one map, and what it writes
is decided by what it carries and by the entries its footprint names.

`setReceiptLines` and `recordExtraction` were on that list and are not any more.
Who may say what a receipt contains is now a question about the member who filed
it *and* about every transaction it is attached to, so the operation reads the
whole transaction table and its real footprint is not the one it names. Narrowing
`Rebasable` is the conservative answer: a client asks the user rather than
resubmitting on a reading that might have moved.

Everything else is left out, and for one of two reasons. Some cannot be covered
at all:

* `snapshot` replaces the state, so its footprint is everything;
* `mergeAccounts` and `deleteLabel` rewrite every transaction that mentions
  what they name, so their footprint is not syntactic;
* `issueInvoice` and `deleteInvoice` move a counter, and two of them racing
  would hand out one number twice;
* `allocate`, `settle` and `closeBudget` read the whole realm — every
  contribution and every outstanding claim — before they write anything;
* `createRealm`, `grant`, `revoke`, `setRole`, `rotateRealmKey`, `addMember`,
  `removeMember`, `setAccountRights`, `setAccountOwner`, `putAccount` and
  `deleteAccount` change who may write where, which is exactly what every other
  operation's success is checked against;
* `deleteRule` removes every rule of that name as well as the one of that id,
  so what it names is a question about the state rather than about the verb.

The rest are simply not done here yet. The arithmetic intents
(`splitTransaction`, `mergeTransactions`, `unmergeTransaction`,
`replaceTransaction`, `divideByItems`), the other claim verbs (`resolveClaim`,
`voidClaim`, `payClaim`) and `contribute` retire one transaction and write
several, so the single write below would have to become a list of them. None of
them is unstateable — they are more work rather than a missing idea, and until
they are done a client asks the user.

Every covered operation now reads something other than its own footprint, and it
is always the same thing: the rule `Op.rights` gives it, which is a question
about the realms. That is not a gap — `Agree` requires the realms to match, and
no rebasable operation writes one — and it is the same reading every posting is
checked under. `checkRights_congr` is the statement that a rebasable operation's
rule depends on the realms alone, which is what makes that closure hold.

`Independent` is conservative rather than complete: it implies the theorems, and
two operations it refuses may still commute. A refused rebase costs a question
to the user; a wrong one costs the ledger.

## What "the same state" means

The maps are hashed, so two states holding the same entries need not be equal as
values: the buckets remember the order things were inserted in. `State.Same`
below is entry-by-entry equality — exactly what `State.canonical` prints and
what the tests compare — and `sortedPairs_congr` carries it to the sorted
reading of every map, which is the list `canonical` is built from. The one thing
this file cannot do is rewrite `canonical` itself, because the helper that
builds one of its sections is private to `Core/State.lean`;
`State.Same.sections` is that statement in the only form available here.
-/

namespace Resources

/-! ## Reading a map in sorted order

Pointwise equality of two maps is what every statement below concludes with.
These two lemmas say it is enough: a map's sorted reading — what `canonical`
prints and what `Core` iterates over — is a function of its entries alone.
-/

/-- Two maps holding the same entry under every key list the same pairs. -/
theorem toList_perm {α : Type} {m₁ m₂ : Std.HashMap String α}
    (h : ∀ k : String, m₁[k]? = m₂[k]?) : m₁.toList.Perm m₂.toList := by
  have hnd : ∀ m : Std.HashMap String α, m.toList.Nodup := by
    intro m
    exact (Std.HashMap.distinct_keys_toList (m := m)).imp (fun hx hc => by
      subst hc; simp at hx)
  refine (List.perm_ext_iff_of_nodup (hnd m₁) (hnd m₂)).mpr ?_
  intro ⟨k, v⟩
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.mem_toList_iff_getElem?_eq_some, h k]

/--
Two maps holding the same entry under every key are read identically.

Sorting by key is what `Core` iterates by and what `canonical` prints, and the
keys of a map are distinct, so the sorted reading is unique.
-/
theorem sortedPairs_congr {α : Type} {m₁ m₂ : Std.HashMap String α}
    (h : ∀ k : String, m₁[k]? = m₂[k]?) : sortedPairs m₁ = sortedPairs m₂ := by
  have hmem : ∀ (m : Std.HashMap String α) (a : String × α),
      a ∈ sortedPairs m → m[a.1]? = some a.2 := by
    intro m a ha
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp
      ((List.mergeSort_perm m.toList (fun a b => a.1 ≤ b.1)).mem_iff.mp ha)
  have hsorted : ∀ m : Std.HashMap String α,
      (sortedPairs m).Pairwise (fun a b : String × α => decide (a.1 ≤ b.1) = true) := by
    intro m
    exact List.pairwise_mergeSort
      (le := fun a b : String × α => decide (a.1 ≤ b.1))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact Std.le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Std.le_total) _
  refine List.Perm.eq_of_pairwise
    (le := fun a b : String × α => decide (a.1 ≤ b.1) = true) ?_ (hsorted m₁) (hsorted m₂) ?_
  · intro a b ha hb hab hba
    simp only [decide_eq_true_eq] at hab hba
    have hk : a.1 = b.1 := Std.le_antisymm hab hba
    have h1 := hmem m₁ a ha
    have h2 := hmem m₂ b hb
    rw [hk, h b.1, h2] at h1
    exact Prod.ext hk (by simpa using h1.symm)
  · exact ((List.mergeSort_perm _ _).trans (toList_perm h)).trans
      (List.mergeSort_perm _ _).symm

/-- Two sets holding the same elements are listed in the same sorted order. -/
theorem sortedFingerprints_congr {s₁ s₂ : Std.HashSet String}
    (h : ∀ f : String, s₁.contains f = s₂.contains f) :
    s₁.toList.mergeSort (· ≤ ·) = s₂.toList.mergeSort (· ≤ ·) := by
  have hnd : ∀ m : Std.HashSet String, m.toList.Nodup := by
    intro m
    exact (Std.HashSet.distinct_toList (m := m)).imp (fun hx hc => by subst hc; simp at hx)
  have hperm : s₁.toList.Perm s₂.toList := by
    refine (List.perm_ext_iff_of_nodup (hnd s₁) (hnd s₂)).mpr ?_
    intro f
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_toList, ← Std.HashSet.contains_iff_mem,
      ← Std.HashSet.contains_iff_mem, h f]
  have hsorted : ∀ m : Std.HashSet String,
      (m.toList.mergeSort (· ≤ ·)).Pairwise (fun a b : String => decide (a ≤ b) = true) := by
    intro m
    exact List.pairwise_mergeSort
      (le := fun a b : String => decide (a ≤ b))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact Std.le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Std.le_total) _
  refine List.Perm.eq_of_pairwise
    (le := fun a b : String => decide (a ≤ b) = true) ?_ (hsorted s₁) (hsorted s₂) ?_
  · intro a b _ _ hab hba
    simp only [decide_eq_true_eq] at hab hba
    exact Std.le_antisymm hab hba
  · exact ((List.mergeSort_perm _ _).trans hperm).trans (List.mergeSort_perm _ _).symm

/-! ## States that hold the same entries -/

/--
Two states holding the same entry under every key.

This is what two replays are compared by: `State.canonical` sorts every map by
key and prints it, so two states that agree entry by entry print the same thing.
It is stated here rather than as an equality of maps because a hash map
remembers the order its entries arrived in, and two orders of the same writes do
not produce the same buckets.
-/
structure State.Same (s t : State) : Prop where
  /-- The realms agree. -/
  realms : ∀ k : String, s.realms[k]? = t.realms[k]?
  /-- The members agree. -/
  members : ∀ k : String, s.members[k]? = t.members[k]?
  /-- The accounts agree. -/
  accounts : ∀ k : String, s.accounts[k]? = t.accounts[k]?
  /-- The labels agree. -/
  labels : ∀ k : String, s.labels[k]? = t.labels[k]?
  /-- The parties agree. -/
  parties : ∀ k : String, s.parties[k]? = t.parties[k]?
  /-- The groups agree. -/
  groups : ∀ k : String, s.groups[k]? = t.groups[k]?
  /-- The trips agree. -/
  trips : ∀ k : String, s.trips[k]? = t.trips[k]?
  /-- The rules agree. -/
  rules : ∀ k : String, s.rules[k]? = t.rules[k]?
  /-- The transactions agree. -/
  txns : ∀ k : String, s.txns[k]? = t.txns[k]?
  /-- The budgets agree. -/
  budgets : ∀ k : String, s.budgets[k]? = t.budgets[k]?
  /-- The invoices agree. -/
  invoices : ∀ k : String, s.invoices[k]? = t.invoices[k]?
  /-- The stored receipts agree. -/
  blobs : ∀ k : String, s.blobs[k]? = t.blobs[k]?
  /-- The import batches agree. -/
  batches : ∀ k : String, s.batches[k]? = t.batches[k]?
  /-- The counters agree. -/
  counters : ∀ k : String, s.counters[k]? = t.counters[k]?
  /-- The import fingerprints agree. -/
  fingerprints : ∀ f : String, s.fingerprints.contains f = t.fingerprints.contains f

namespace State.Same

/-- Every state holds the entries it holds. -/
theorem refl (s : State) : State.Same s s :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/--
The sorted reading of every map, which is what `State.canonical` prints.

`canonical` itself cannot be rewritten from outside `Core/State.lean` — the
helper that builds one of its sections is private there — so this is the
statement in the form available here: every list it is built from is the same.
-/
theorem sections {s t : State} (h : State.Same s t) :
    sortedPairs s.realms = sortedPairs t.realms ∧
      sortedPairs s.members = sortedPairs t.members ∧
      sortedPairs s.accounts = sortedPairs t.accounts ∧
      sortedPairs s.labels = sortedPairs t.labels ∧
      sortedPairs s.parties = sortedPairs t.parties ∧
      sortedPairs s.groups = sortedPairs t.groups ∧
      sortedPairs s.trips = sortedPairs t.trips ∧
      sortedPairs s.rules = sortedPairs t.rules ∧
      sortedPairs s.txns = sortedPairs t.txns ∧
      sortedPairs s.budgets = sortedPairs t.budgets ∧
      sortedPairs s.invoices = sortedPairs t.invoices ∧
      sortedPairs s.blobs = sortedPairs t.blobs ∧
      sortedPairs s.batches = sortedPairs t.batches ∧
      sortedPairs s.counters = sortedPairs t.counters ∧
      s.fingerprints.toList.mergeSort (· ≤ ·) = t.fingerprints.toList.mergeSort (· ≤ ·) :=
  ⟨sortedPairs_congr h.realms, sortedPairs_congr h.members, sortedPairs_congr h.accounts,
   sortedPairs_congr h.labels, sortedPairs_congr h.parties, sortedPairs_congr h.groups,
   sortedPairs_congr h.trips, sortedPairs_congr h.rules, sortedPairs_congr h.txns,
   sortedPairs_congr h.budgets, sortedPairs_congr h.invoices, sortedPairs_congr h.blobs,
   sortedPairs_congr h.batches, sortedPairs_congr h.counters,
   sortedFingerprints_congr h.fingerprints⟩

end State.Same

/-! ## What an operation names -/

/--
One entry of the state: which map, and which key inside it.

A footprint is a list of these. Keys from different maps can never collide,
which is the whole reason this is a type rather than a string.
-/
inductive Key
  /-- An account. -/
  | account (id : AccountId)
  /-- A transaction. -/
  | txn (id : TxId)
  /-- A label. -/
  | label (id : LabelId)
  /-- A party. -/
  | party (id : PartyId)
  /-- A group, which is keyed by name. -/
  | group (name : String)
  /-- A trip, which is keyed by name. -/
  | trip (name : String)
  /-- A categorisation rule. -/
  | rule (id : RuleId)
  /-- A stored receipt, which is keyed by content hash. -/
  | blob (sha : String)
  /-- An import batch. -/
  | batch (id : BatchId)
  /-- A budget. -/
  | budget (id : BudgetId)
  /-- An invoice. -/
  | invoice (id : InvoiceId)
  /-- A realm. -/
  | realm (id : RealmId)
  /-- A member. -/
  | member (id : MemberId)
  /-- A counter. -/
  | counter (name : String)
  /-- An import fingerprint. -/
  | fingerprint (fp : String)
  deriving DecidableEq, Repr

namespace Op

/--
Every account an operation names, in its postings or outright.

Syntactic, and deliberately so: nothing here reads the state, because a client
deciding whether to rebase has only the operations. The operations whose real
footprint cannot be read off them — a merge rewrites every transaction that
mentions an account, an allocation reads a whole budget — are the ones
`Rebasable` leaves out.
-/
def touches : Op → List AccountId
  | .putAccount a => [a.id]
  | .mergeAccounts from_ into => [from_, into]
  | .deleteAccount id | .setAccountRights id _ | .setAccountOwner id _ => [id]
  | .putTransaction t | .raiseClaim t | .contribute _ t => t.postings.map (·.account)
  | .splitTransaction _ targets _ => targets
  | .mergeTransactions _ _ _ _ cancelIn => cancelIn
  | .replaceTransaction _ parts _ => parts.flatMap (fun p => p.postings.map (·.account))
  | .divideByItems _ groups _ => groups.map (fun g => ⟨g.into⟩)
  | .voidClaim _ (some (into, _, _)) => [into]
  | .openBudget _ account => [account.id]
  | .grant _ _ _ bridge => [bridge.id]
  | .recordImportBatch b => b.account.toList
  | _ => []

/-- Every transaction an operation reads or writes by name. -/
def touchesTxns : Op → List TxId
  | .putTransaction t | .raiseClaim t | .contribute _ t => [t.id]
  | .deleteTransaction id | .splitTransaction id _ _ | .attach id _ | .detach id _ => [id]
  | .mergeTransactions ids newId _ _ _ => newId :: ids
  | .unmergeTransaction id newIds => id :: newIds
  | .replaceTransaction id parts _ => id :: parts.map (·.id)
  | .divideByItems id _ newIds => id :: newIds
  | .resolveClaim id actual splitId => [id, actual, splitId]
  | .voidClaim id (some (_, entryId, _)) => [id, entryId]
  | .voidClaim id none => [id]
  | .allocate _ _ _ _ _ txnId claimIds _ => txnId :: claimIds
  | .settle _ _ _ _ claimIds _ => claimIds
  | .closeBudget _ _ _ _ _ txnId claimIds _ => txnId :: claimIds
  | .issueInvoice _ sources => sources
  | .settleInvoice _ txn => [txn]
  | .payClaim claim payment _ => [claim, payment]
  | _ => []

/--
Every other entry an operation names: labels, parties, groups, trips, rules,
receipts, batches, budgets, invoices, realms, members and fingerprints.

A write that carries an import fingerprint names it, because a second write
carrying the same one is refused — which is what makes re-importing a no-op, and
what makes two such writes anything but independent.
-/
def touchesEntities : Op → List Key
  | .createRealm r => [.realm r.id]
  | .putLabel l => [.label l.id]
  | .deleteLabel id => [.label id]
  | .putParty p => [.party p.id]
  | .putGroup g => [.group g.name]
  | .deleteGroup name => [.group name]
  | .putTrip t => [.trip t.name]
  | .deleteTrip name => [.trip name]
  | .putRule r => [.rule r.id]
  | .deleteRule idOrName => [.rule ⟨idOrName⟩]
  | .putTransaction t | .raiseClaim t | .contribute _ t =>
      (fingerprintOf t).toList.map Key.fingerprint
  | .registerBlob file => [.blob file.sha256]
  | .attach _ sha | .detach _ sha | .recordExtraction sha _ | .setReceiptLines sha _
  | .forgetBlob sha => [.blob sha]
  | .recordImportBatch b => [.batch b.id]
  | .openBudget b _ => [.budget b.id]
  | .setParticipants budget _ | .reopenBudget budget | .deleteBudget budget => [.budget budget]
  | .allocate budget .. | .settle budget .. | .closeBudget budget .. => [.budget budget]
  | .issueInvoice inv _ => [.invoice inv.id]
  | .setInvoiceStatus id _ | .settleInvoice id _ | .deleteInvoice id => [.invoice id]
  | .addMember m => [.member m.id]
  | .removeMember id => [.member id]
  | .grant realm member _ _ | .revoke realm member | .setRole realm member _ =>
      [.realm realm, .member member]
  | .rotateRealmKey realm => [.realm realm]
  | _ => []

/-- Every entry of the state an operation names: its whole syntactic footprint. -/
def footprint (o : Op) : List Key :=
  o.touches.map Key.account ++ o.touchesTxns.map Key.txn ++ o.touchesEntities

/-! ## Independence -/

/--
The operations the theorems below cover.

Each writes one entry of one map, and decides what to write from what it carries
and from the entries its footprint names. The module comment says why each of
the others is left out.
-/
def Rebasable : Op → Bool
  | .putTransaction _ | .deleteTransaction _ | .raiseClaim _ | .putLabel _ | .putParty _
  | .putGroup _ | .deleteGroup _ | .putTrip _ | .deleteTrip _ | .putRule _ | .registerBlob _
  | .attach _ _ | .detach _ _ | .forgetBlob _ | .recordImportBatch _ => true
  | _ => false

/-- Whether two lists of keys have nothing in common. -/
def disjointKeys (xs ys : List Key) : Bool :=
  xs.all (fun k => ys.all (fun k' => decide (k ≠ k')))

/-- Two operations that name a common entry are not independent. -/
theorem ne_of_disjointKeys {xs ys : List Key} {k k' : Key} (h : disjointKeys xs ys = true)
    (hx : k ∈ xs) (hy : k' ∈ ys) : k ≠ k' := by
  simp only [disjointKeys, List.all_eq_true, decide_eq_true_eq] at h
  exact h k hx k' hy

/--
Whether two operations can be applied in either order.

Both have to be rebasable — which is what rules out snapshots, realm and member
operations, the invoice counter and the budget intents that read a whole realm —
and their footprints have to be disjoint: no shared account, no shared
transaction, no shared label, receipt or fingerprint.
-/
def independent (a b : Op) : Bool :=
  a.Rebasable && b.Rebasable && disjointKeys a.footprint b.footprint

/-- `independent`, as a proposition to hypothesise. It is decidable. -/
def Independent (a b : Op) : Prop := Op.independent a b = true

instance (a b : Op) : Decidable (Op.Independent a b) :=
  decidable_of_iff (Op.independent a b = true) Iff.rfl

namespace Independent

/-- An independent pair is a pair of rebasable operations. -/
theorem left {a b : Op} (h : Independent a b) : a.Rebasable = true := by
  simp only [Independent, independent, Bool.and_eq_true] at h
  exact h.1.1

/-- An independent pair is a pair of rebasable operations. -/
theorem right {a b : Op} (h : Independent a b) : b.Rebasable = true := by
  simp only [Independent, independent, Bool.and_eq_true] at h
  exact h.1.2

/-- Independence is symmetric: neither operation names anything the other does. -/
theorem symm {a b : Op} (h : Independent a b) : Independent b a := by
  simp only [Independent, independent, Bool.and_eq_true] at h ⊢
  refine ⟨⟨h.1.2, h.1.1⟩, ?_⟩
  simp only [disjointKeys, List.all_eq_true, decide_eq_true_eq]
  intro k hk k' hk'
  exact (ne_of_disjointKeys h.2 hk' hk).symm

/-- No entry is named by both of an independent pair. -/
theorem not_mem {a b : Op} (h : Independent a b) {k : Key} (hka : k ∈ a.footprint)
    (hkb : k ∈ b.footprint) : False := by
  simp only [Independent, independent, Bool.and_eq_true] at h
  exact ne_of_disjointKeys h.2 hka hkb rfl

end Independent

end Op

/-! ## One write, one entry

What a rebasable operation does to the state is one write to one map, and the
algebra of those writes is the whole of why two of them commute. `Upd` is a
write; `Delta` is one per map, which is how an operation that touches a
transaction and an import fingerprint is still one value.
-/

/-- A single-entry write to one of the state's maps. -/
inductive Upd (α : Type)
  /-- Nothing is written. -/
  | skip
  /-- The entry under `k` becomes `v`. -/
  | put (k : String) (v : α)
  /-- The entry under `k` goes. -/
  | drop (k : String)

namespace Upd

/-- Carrying the write out. -/
def run {α : Type} : Upd α → Std.HashMap String α → Std.HashMap String α
  | .skip, m => m
  | .put k v, m => m.insert k v
  | .drop k, m => m.erase k

/-- The one key a write names, if it names one. -/
def key {α : Type} : Upd α → Option String
  | .skip => none
  | .put k _ => some k
  | .drop k => some k

/-- A write leaves every entry it does not name exactly as it was. -/
theorem getElem?_run_of_ne {α : Type} {u : Upd α} {m : Std.HashMap String α} {j : String}
    (h : ∀ k ∈ u.key, j ≠ k) : (u.run m)[j]? = m[j]? := by
  cases u with
  | skip => rfl
  | put k v =>
    have hne : j ≠ k := h k (by simp [key])
    simp [run, Std.HashMap.getElem?_insert, Ne.symm hne]
  | drop k =>
    have hne : j ≠ k := h k (by simp [key])
    simp [run, Std.HashMap.getElem?_erase, Ne.symm hne]

/-- What a write leaves under the entry it names does not depend on what was there. -/
theorem getElem?_run_of_mem {α : Type} {u : Upd α} {m m' : Std.HashMap String α} {j : String}
    (h : j ∈ u.key) : (u.run m)[j]? = (u.run m')[j]? := by
  cases u with
  | skip => simp [key] at h
  | put k v =>
    simp only [key, Option.mem_def, Option.some.injEq] at h
    subst h
    simp [run]
  | drop k =>
    simp only [key, Option.mem_def, Option.some.injEq] at h
    subst h
    simp [run]

/-- Two writes to one map that name different keys read back the same either way round. -/
theorem getElem?_run_comm {α : Type} {u v : Upd α} {m : Std.HashMap String α}
    (h : ∀ k ∈ u.key, ∀ k' ∈ v.key, k ≠ k') (j : String) :
    (u.run (v.run m))[j]? = (v.run (u.run m))[j]? := by
  by_cases hu : u.key = some j
  · have hmem : j ∈ u.key := hu
    rw [getElem?_run_of_mem (m' := m) hmem,
      getElem?_run_of_ne (fun k' hk' => h j hmem k' hk')]
  · have hune : ∀ k ∈ u.key, j ≠ k := by
      intro k hk hjk
      exact hu (by subst hjk; exact hk)
    rw [getElem?_run_of_ne hune]
    by_cases hv : v.key = some j
    · exact (getElem?_run_of_mem (m' := m) hv).symm
    · have hvne : ∀ k ∈ v.key, j ≠ k := by
        intro k hk hjk
        exact hv (by subst hjk; exact hk)
      rw [getElem?_run_of_ne hvne, getElem?_run_of_ne hvne, getElem?_run_of_ne hune]

end Upd

/--
The one write a rebasable operation makes.

Every field is a write to the map of that name, and `fp` is the import
fingerprint the write spoke for, when it took a fresh one. Nothing here can
touch an account, a realm, a member, a budget, an invoice or a counter, which is
the reason those maps never have to be checked for interference below.
-/
structure Delta where
  /-- The transaction written or removed. -/
  txns : Upd Transaction := .skip
  /-- The label written. -/
  labels : Upd Label := .skip
  /-- The party written. -/
  parties : Upd Party := .skip
  /-- The group written. -/
  groups : Upd PartyGroup := .skip
  /-- The trip written. -/
  trips : Upd Trip := .skip
  /-- The rule written. -/
  rules : Upd Rule := .skip
  /-- The stored receipt written. -/
  blobs : Upd BlobState := .skip
  /-- The import batch written. -/
  batches : Upd ImportBatch := .skip
  /-- The import fingerprint this write spoke for, when it took a fresh one. -/
  fp : Option String := none

namespace Delta

/-- Carrying the write out. -/
def run (d : Delta) (s : State) : State :=
  { s with
    txns := d.txns.run s.txns
    labels := d.labels.run s.labels
    parties := d.parties.run s.parties
    groups := d.groups.run s.groups
    trips := d.trips.run s.trips
    rules := d.rules.run s.rules
    blobs := d.blobs.run s.blobs
    batches := d.batches.run s.batches
    fingerprints := match d.fp with
      | none => s.fingerprints
      | some f => s.fingerprints.insert f }

/-- Every entry a write names. -/
def keys (d : Delta) : List Key :=
  d.txns.key.toList.map (fun k => Key.txn ⟨k⟩) ++
    d.labels.key.toList.map (fun k => Key.label ⟨k⟩) ++
    d.parties.key.toList.map (fun k => Key.party ⟨k⟩) ++
    d.groups.key.toList.map Key.group ++
    d.trips.key.toList.map Key.trip ++
    d.rules.key.toList.map (fun k => Key.rule ⟨k⟩) ++
    d.blobs.key.toList.map Key.blob ++
    d.batches.key.toList.map (fun k => Key.batch ⟨k⟩) ++
    d.fp.toList.map Key.fingerprint

/-- A write never touches an account. -/
@[simp] theorem accounts_run (d : Delta) (s : State) : (d.run s).accounts = s.accounts := rfl

/-- A write never touches a realm. -/
@[simp] theorem realms_run (d : Delta) (s : State) : (d.run s).realms = s.realms := rfl

/-- A write never touches a member. -/
@[simp] theorem members_run (d : Delta) (s : State) : (d.run s).members = s.members := rfl

/-- A write never touches a budget. -/
@[simp] theorem budgets_run (d : Delta) (s : State) : (d.run s).budgets = s.budgets := rfl

/-- Reading a transaction back out of a write that did not name it. -/
theorem txn?_run_of_ne {d : Delta} {s : State} {id : TxId}
    (h : ∀ k ∈ d.txns.key, id.val ≠ k) : (d.run s).txn? id = s.txn? id :=
  Upd.getElem?_run_of_ne h

/-- Reading a receipt back out of a write that did not name it. -/
theorem blob?_run_of_ne {d : Delta} {s : State} {sha : String}
    (h : ∀ k ∈ d.blobs.key, sha ≠ k) : (d.run s).blob? sha = s.blob? sha :=
  Upd.getElem?_run_of_ne h

/-- A fingerprint a write did not take is spoken for exactly as before. -/
theorem contains_run_of_ne {d : Delta} {s : State} {f : String} (h : ∀ g ∈ d.fp, f ≠ g) :
    (d.run s).fingerprints.contains f = s.fingerprints.contains f := by
  simp only [run]
  cases hfp : d.fp with
  | none => rfl
  | some g =>
    have hne : f ≠ g := h g (by simp [hfp])
    simp [Std.HashSet.contains_insert, Ne.symm hne]

/--
Two writes that name no entry in common leave the same state either way round.

This is the whole arithmetic behind commutation: the maps are separate, and
within one map two writes under different keys do not see each other.
-/
theorem run_comm {d e : Delta} {s : State} (h : ∀ k ∈ d.keys, ∀ k' ∈ e.keys, k ≠ k') :
    State.Same (d.run (e.run s)) (e.run (d.run s)) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl,
    fun _ => rfl, ?_, ?_, fun _ => rfl, ?_⟩
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.label ⟨k⟩) (by simp [keys, Option.mem_def.mp hk])
        (Key.label ⟨k'⟩) (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.party ⟨k⟩) (by simp [keys, Option.mem_def.mp hk])
        (Key.party ⟨k'⟩) (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.group k) (by simp [keys, Option.mem_def.mp hk])
        (Key.group k') (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.trip k) (by simp [keys, Option.mem_def.mp hk])
        (Key.trip k') (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.rule ⟨k⟩) (by simp [keys, Option.mem_def.mp hk])
        (Key.rule ⟨k'⟩) (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.txn ⟨k⟩) (by simp [keys, Option.mem_def.mp hk])
        (Key.txn ⟨k'⟩) (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.blob k) (by simp [keys, Option.mem_def.mp hk])
        (Key.blob k') (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · exact Upd.getElem?_run_comm (fun k hk k' hk' => by
      have := h (Key.batch ⟨k⟩) (by simp [keys, Option.mem_def.mp hk])
        (Key.batch ⟨k'⟩) (by simp [keys, Option.mem_def.mp hk'])
      simpa using this)
  · intro f
    simp only [run]
    cases hd : d.fp <;> cases he : e.fp <;>
      simp [Std.HashSet.contains_insert, Bool.or_left_comm]

end Delta

/-! ## Reading what an operation reads

A rebasable operation reads three things: the accounts, realms and budgets — in
full, because that is what `checkPostings` and `canPost` are checked against, and
no rebasable operation writes any of them — and the transactions, receipts and
fingerprints its own footprint names. `Agree` is two states that agree on all of
it, and the lemmas after it carry that agreement through the readers.
-/

/-- Two states that agree on everything a rebasable operation reads. -/
structure Agree (o : Op) (s t : State) : Prop where
  /-- The accounts are the same, because every posting is checked against them. -/
  accounts : s.accounts = t.accounts
  /-- The realms are the same, because who may post is read off them. -/
  realms : s.realms = t.realms
  /-- The members are the same, because the party a member owns is read off them. -/
  members : s.members = t.members
  /-- The budgets are the same, because an open budget is a right to post. -/
  budgets : s.budgets = t.budgets
  /-- The transactions the operation names are the same. -/
  txns : ∀ id : TxId, Key.txn id ∈ o.footprint → s.txn? id = t.txn? id
  /-- The receipts the operation names are the same. -/
  blobs : ∀ sha : String, Key.blob sha ∈ o.footprint → s.blob? sha = t.blob? sha
  /-- The labels the operation names are the same: a label says which realm it is in. -/
  labels : ∀ id : LabelId, Key.label id ∈ o.footprint → s.labels[id.val]? = t.labels[id.val]?
  /-- The people the operation names are the same, for the same reason. -/
  parties : ∀ id : PartyId, Key.party id ∈ o.footprint → s.parties[id.val]? = t.parties[id.val]?
  /-- The groups the operation names are the same. -/
  groups : ∀ n : String, Key.group n ∈ o.footprint → s.groups[n]? = t.groups[n]?
  /-- The trips the operation names are the same. -/
  trips : ∀ n : String, Key.trip n ∈ o.footprint → s.trips[n]? = t.trips[n]?
  /-- The rules the operation names are the same. -/
  rules : ∀ id : RuleId, Key.rule id ∈ o.footprint → s.rules[id.val]? = t.rules[id.val]?
  /-- The import batches the operation names are the same. -/
  batches : ∀ id : BatchId, Key.batch id ∈ o.footprint → s.batches[id.val]? = t.batches[id.val]?
  /-- The fingerprints the operation names are spoken for in the same way. -/
  fingerprints : ∀ f : String, Key.fingerprint f ∈ o.footprint →
    s.fingerprints.contains f = t.fingerprints.contains f

namespace Agree

/-- A state agrees with itself. -/
theorem refl (o : Op) (s : State) : Agree o s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Agreement is symmetric. -/
theorem symm {o : Op} {s t : State} (h : Agree o s t) : Agree o t s :=
  ⟨h.accounts.symm, h.realms.symm, h.members.symm, h.budgets.symm,
   fun id hk => (h.txns id hk).symm, fun sha hk => (h.blobs sha hk).symm,
   fun id hk => (h.labels id hk).symm, fun id hk => (h.parties id hk).symm,
   fun n hk => (h.groups n hk).symm, fun n hk => (h.trips n hk).symm,
   fun id hk => (h.rules id hk).symm, fun id hk => (h.batches id hk).symm,
   fun f hk => (h.fingerprints f hk).symm⟩

end Agree

/-- Two states with the same accounts read an account the same way. -/
theorem accountOf_congr {s t : State} (ha : s.accounts = t.accounts) (id : AccountId) :
    accountOf s id = accountOf t id := by
  simp only [accountOf, State.account?, ha]

/-- Two states with the same realms and budgets agree on who may write which leg. -/
theorem canPostLeg_congr {s t : State} (hr : s.realms = t.realms) (hb : s.budgets = t.budgets)
    (m : MemberId) (a : Account) (n : Int) : s.canPostLeg m a n = t.canPostLeg m a n := by
  simp only [State.canPostLeg, State.realm?, State.openBudgetAccount, hr, hb]

/-- Two states with the same realms and budgets agree on who may post where. -/
theorem canPost_congr {s t : State} (hr : s.realms = t.realms) (hb : s.budgets = t.budgets)
    (m : MemberId) (a : Account) : s.canPost m a = t.canPost m a :=
  canPostLeg_congr hr hb m a 1

/-- Checking a part's postings reads nothing but the accounts, the realms and the budgets. -/
theorem checkPostings_congr {s t : State} (ha : s.accounts = t.accounts)
    (hr : s.realms = t.realms) (hb : s.budgets = t.budgets) (au : MemberId) (r : RealmId)
    (allowed : List AccountId) (ps : List Posting) :
    checkPostings s au r ps allowed = checkPostings t au r ps allowed := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [checkPostings, List.forIn_cons, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, pure, Except.pure, accountOf_congr ha, canPostLeg_congr hr hb] at ih ⊢

/-- Checking legs that are already there reads the same three maps. -/
theorem checkOwnLegs_congr {s t : State} (ha : s.accounts = t.accounts)
    (hr : s.realms = t.realms) (hb : s.budgets = t.budgets) (au : MemberId) (r : RealmId)
    (ps : List Posting) : checkOwnLegs s au r ps = checkOwnLegs t au r ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [checkOwnLegs, List.forIn_cons, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, pure, Except.pure, accountOf_congr ha, canPostLeg_congr hr hb] at ih ⊢

/-- Two states with the same realms agree about who administers one. -/
theorem canAdminister_congr {s t : State} (hr : s.realms = t.realms) (m : MemberId)
    (r : RealmId) : s.canAdminister m r = t.canAdminister m r := by
  simp only [State.canAdminister, State.realm?, hr]

/-- Two states with the same realms agree about who is in one. -/
theorem isMemberOf_congr {s t : State} (hr : s.realms = t.realms) (m : MemberId)
    (r : RealmId) : s.isMemberOf m r = t.isMemberOf m r := by
  simp only [State.isMemberOf, State.realm?, hr]

/--
Every rebasable operation's rule is a question about the realms and nothing else.

That is not an accident of the table: an operation that decided who may act by
reading the ledger would be one whose success another operation could change
without naming anything it names, and `Rebasable` is exactly the set where that
cannot happen.
-/
theorem checkRights_congr {s t : State} {o : Op} (hreb : o.Rebasable = true)
    (hr : s.realms = t.realms) (hm : s.members = t.members) (au : MemberId) (r : RealmId) :
    checkRights s au r o = checkRights t au r o := by
  have hadm : s.canAdminister au r = t.canAdminister au r := canAdminister_congr hr au r
  have hmem : s.isMemberOf au r = t.isMemberOf au r := isMemberOf_congr hr au r
  have hwho : s.member? au = t.member? au := by simp only [State.member?, hm]
  cases o <;> simp_all [checkRights, Op.rights, Op.Rebasable]

/-- Two states with the same accounts agree on which realm a posting lands in. -/
theorem realmOf_congr {s t : State} (ha : s.accounts = t.accounts) :
    s.realmOf = t.realmOf := by
  funext id
  simp only [State.realmOf, State.account?, ha]

/-- The guard a rewrite makes reads the accounts, the realms, the budgets and its own entry. -/
theorem putGuard_congr {s t : State} (ha : s.accounts = t.accounts) (hr : s.realms = t.realms)
    (hb : s.budgets = t.budgets) {au : MemberId} {r : RealmId} {tx : Transaction}
    (htx : s.txn? tx.id = t.txn? tx.id) : putGuard s au r tx = putGuard t au r tx := by
  simp only [putGuard, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure, htx, realmOf_congr ha, checkOwnLegs_congr ha hr hb]

/-- The write a transaction put makes: the transaction, under its own id. -/
def Delta.txnPut (k : String) (w : Transaction) (fp : Option String) : Delta :=
  { txns := .put k w, fp }

/-- A transaction put names the transaction it writes and the fingerprint it took. -/
theorem Delta.keys_txnPut {k : String} {w : Transaction} {fp : Option String} :
    (Delta.txnPut k w fp).keys = Key.txn ⟨k⟩ :: fp.toList.map Key.fingerprint := by
  cases fp <;> rfl

/--
What `putTxn` does, read as a single write.

It writes one transaction, under the id that transaction carries, and it takes
at most one import fingerprint — the one the transaction itself carries. Any
state that agrees on the accounts, the realms, the budgets, the transaction
being replaced and that fingerprint takes the very same write.
-/
theorem putTxn_frame {s : State} {au : MemberId} {r : RealmId} {tx : Transaction}
    {allowed : List AccountId} {s' : State} {cs : List Change}
    (hok : putTxn s au r tx allowed = .ok (s', cs)) :
    ∃ (w : Transaction) (fp : Option String),
      (∀ f ∈ fp, fingerprintOf tx = some f) ∧
      s' = (Delta.txnPut tx.id.val w fp).run s ∧
      ∀ t : State, s.accounts = t.accounts → s.realms = t.realms → s.budgets = t.budgets →
        s.txn? tx.id = t.txn? tx.id →
        (∀ f, fingerprintOf tx = some f →
          s.fingerprints.contains f = t.fingerprints.contains f) →
        ∃ cs', putTxn t au r tx allowed = .ok ((Delta.txnPut tx.id.val w fp).run t, cs') := by
  simp only [putTxn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at hok
  cases hchk : checkPostings s au r tx.postings allowed with
  | error e => simp only [hchk] at hok; simp at hok
  | ok u =>
    cases hval : tx.validate with
    | error e => simp only [hchk, hval] at hok; simp at hok
    | ok v =>
      obtain ⟨hvv, hbal⟩ := validate_val hval
      simp only [hchk, hval, hvv] at hok
      by_cases hlegs : (tx.state == .pending && tx.postings.length != 2) = true
      · rw [if_pos hlegs] at hok; simp at hok
      · rw [if_neg hlegs] at hok
        by_cases hlen : ((((s.txn? tx.id).map (·.postings)).getD []).filter
            (fun p => s.realmOf p.account != some r) ++ tx.postings).length > maxPostings
        · rw [if_pos hlen] at hok; simp at hok
        rw [if_neg hlen] at hok
        cases hfing : fingerprintOf tx with
        | none =>
          simp only [hfing, Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨rfl, rfl⟩ := hok
          refine ⟨_, none, by simp, rfl, ?_⟩
          intro t ha hr hb hid _
          exact ⟨_, by
            simp only [putTxn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
              Except.pure, ← checkPostings_congr ha hr hb, hchk, hval, hvv, if_neg hlegs,
              hfing, ← hid, ← realmOf_congr ha, if_neg hlen] <;> rfl⟩
        | some f =>
          simp only [hfing] at hok
          by_cases hdup : (s.fingerprints.contains f &&
              ((s.txn? tx.id).bind fingerprintOf) != some f) = true
          · rw [if_pos hdup] at hok; simp at hok
          · rw [if_neg hdup] at hok
            by_cases hnew : (!s.fingerprints.contains f) = true
            · rw [if_pos hnew] at hok
              simp only [Except.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨_, some f, by simp, rfl, ?_⟩
              intro t ha hr hb hid hfp
              exact ⟨_, by
                simp only [putTxn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
                  Except.pure, ← checkPostings_congr ha hr hb, hchk, hval, hvv,
                  if_neg hlegs, hfing, ← hid, ← hfp f rfl, ← realmOf_congr ha, if_neg hlen,
                  if_neg hdup, if_pos hnew] <;> rfl⟩
            · rw [if_neg hnew] at hok
              simp only [Except.ok.injEq, Prod.mk.injEq] at hok
              obtain ⟨rfl, rfl⟩ := hok
              refine ⟨_, none, by simp, rfl, ?_⟩
              intro t ha hr hb hid hfp
              exact ⟨_, by
                simp only [putTxn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
                  Except.pure, ← checkPostings_congr ha hr hb, hchk, hval, hvv,
                  if_neg hlegs, hfing, ← hid, ← hfp f rfl, ← realmOf_congr ha, if_neg hlen,
                  if_neg hdup, if_neg hnew] <;> rfl⟩

/-! ## Every rebasable operation is one write -/

/-- A transaction an operation names is in its footprint. -/
theorem mem_footprint_txn {o : Op} {id : TxId} (h : id ∈ o.touchesTxns) :
    Key.txn id ∈ o.footprint := by
  simp only [Op.footprint, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨id, h, rfl⟩)

/-- An entity an operation names is in its footprint. -/
theorem mem_footprint_entity {o : Op} {k : Key} (h : k ∈ o.touchesEntities) :
    k ∈ o.footprint := by
  simp only [Op.footprint, List.mem_append]
  exact Or.inr h

/-- Two states holding the same transaction read it the same way. -/
theorem txnOf_congr {s u : State} {id : TxId} (h : s.txn? id = u.txn? id) :
    txnOf s id = txnOf u id := by
  simp only [txnOf, h]

/--
What an operation promises, read as a write.

`d` is the entry it wrote, which is one its own footprint names; and every state
that agrees with `s` on what the operation reads takes that very same write.
Quantifying over those states inside the existential is what makes the write
*the* write: the same `d` serves every state the operation could be replayed
against.
-/
def Framed (o : Op) (au : MemberId) (r : RealmId) (s s' : State) : Prop :=
  ∃ d : Delta, (∀ k ∈ d.keys, k ∈ o.footprint) ∧ s' = d.run s ∧
    ∀ u : State, Agree o s u → ∃ cs : List Change, applyChecked u au r o = .ok (d.run u, cs)

/--
Every rebasable operation writes one entry, and writes it the same way wherever
what it reads is the same.

The invariant is what `attach` and `detach` need: they write the transaction
they read back under the id it carries, and `Inv.keyed` is what says that id is
the key it was found under — without it the write could land outside the
footprint the operation names.
-/
theorem applyOp_frame {o : Op} {au : MemberId} {r : RealmId} {s s' : State} {cs : List Change}
    (hinv : Inv r s) (hreb : o.Rebasable = true) (hok : applyChecked s au r o = .ok (s', cs)) :
    Framed o au r s s' := by
  cases o
  case putTransaction tx =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    by_cases h1 : tx.postings.isEmpty = true
    · rw [if_pos h1] at hok; simp at hok
    rw [if_neg h1] at hok
    by_cases h2 : (tx.state != TxnState.posted) = true
    · rw [if_pos h2] at hok; simp at hok
    rw [if_neg h2] at hok
    cases hg : putGuard s au r tx with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
    cases gu
    simp only [hg] at hok
    obtain ⟨w, fp, hfp, hs', hall⟩ := putTxn_frame hok
    refine ⟨Delta.txnPut tx.id.val w fp, ?_, hs', ?_⟩
    · intro k hk
      rw [Delta.keys_txnPut] at hk
      simp only [List.mem_cons, List.mem_map] at hk
      rcases hk with rfl | ⟨f, hf, rfl⟩
      · exact mem_footprint_txn (by simp [Op.touchesTxns])
      · have hmem : f ∈ fp := by simpa using hf
        have hf' := hfp f hmem
        refine mem_footprint_entity ?_
        show Key.fingerprint f ∈ (fingerprintOf tx).toList.map Key.fingerprint
        rw [show fingerprintOf tx = some f from hf']
        simp
    · intro u hu
      have htx := hu.txns tx.id (mem_footprint_txn (by simp [Op.touchesTxns]))
      obtain ⟨cs', hcs'⟩ := hall u hu.accounts hu.realms hu.budgets htx
        (fun f hf => hu.fingerprints f
          (mem_footprint_entity (by simp [Op.touchesEntities, hf])))
      refine ⟨cs', ?_⟩
      have hgu : putGuard u au r tx = .ok () := by
        rw [← putGuard_congr hu.accounts hu.realms hu.budgets htx]; exact hg
      simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        if_neg h1, if_neg h2, hgu]
      exact hcs'
  case deleteTransaction id =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hget : txnOf s id with
    | error e => simp only [hget] at hok; simp at hok
    | ok tx =>
      simp only [hget] at hok
      cases hlegs : checkOwnLegs s au r tx.postings with
      | error e => simp only [hlegs] at hok; simp at hok
      | ok lu =>
        cases lu
        simp only [hlegs, Except.ok.injEq, Prod.mk.injEq] at hok
        refine ⟨{ txns := .drop id.val }, ?_, hok.1.symm, ?_⟩
        · intro k hk
          simp only [Delta.keys, Upd.key] at hk
          simp only [Option.toList_some, Option.toList_none, List.map_cons, List.map_nil,
            List.append_nil, List.mem_singleton] at hk
          subst hk
          exact mem_footprint_txn (by simp [Op.touchesTxns])
        · intro u hu
          exact ⟨_, by
            simp only [applyChecked, bind, Except.bind, pure, Except.pure,
              ← txnOf_congr (hu.txns id (mem_footprint_txn (by simp [Op.touchesTxns]))),
              hget, ← checkOwnLegs_congr hu.accounts hu.realms hu.budgets, hlegs] <;> rfl⟩
  case raiseClaim tx =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    by_cases h1 : (tx.state != TxnState.pending) = true
    · rw [if_pos h1] at hok; simp at hok
    rw [if_neg h1] at hok
    by_cases h2 : (tx.postings.length != 2) = true
    · rw [if_pos h2] at hok; simp at hok
    rw [if_neg h2] at hok
    by_cases h3 : (Pendings.amount tx).minor ≤ 0
    · rw [if_pos h3] at hok; simp at hok
    rw [if_neg h3] at hok
    cases hrecv : Pendings.receiver? tx with
    | none => simp only [hrecv] at hok; simp at hok
    | some recv =>
      simp only [hrecv] at hok
      cases hpay : Pendings.payer? tx with
      | none => simp only [hpay] at hok; simp at hok
      | some pay =>
        simp only [hpay] at hok
        by_cases h4 : (recv == pay) = true
        · rw [if_pos h4] at hok; simp at hok
        rw [if_neg h4] at hok
        obtain ⟨w, fp, hfp, hs', hall⟩ := putTxn_frame hok
        refine ⟨Delta.txnPut tx.id.val w fp, ?_, hs', ?_⟩
        · intro k hk
          rw [Delta.keys_txnPut] at hk
          simp only [List.mem_cons, List.mem_map] at hk
          rcases hk with rfl | ⟨f, hf, rfl⟩
          · exact mem_footprint_txn (by simp [Op.touchesTxns])
          · have hmem : f ∈ fp := by simpa using hf
            have hf' := hfp f hmem
            refine mem_footprint_entity ?_
            show Key.fingerprint f ∈ (fingerprintOf tx).toList.map Key.fingerprint
            rw [show fingerprintOf tx = some f from hf']
            simp
        · intro u hu
          obtain ⟨cs', hcs'⟩ := hall u hu.accounts hu.realms hu.budgets
            (hu.txns tx.id (mem_footprint_txn (by simp [Op.touchesTxns])))
            (fun f hf => hu.fingerprints f (mem_footprint_entity (by
              show Key.fingerprint f ∈ (fingerprintOf tx).toList.map Key.fingerprint
              rw [show fingerprintOf tx = some f from hf]
              simp)))
          refine ⟨cs', ?_⟩
          simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
            if_neg h1, if_neg h2, if_neg h3, hrecv, hpay, if_neg h4]
          exact hcs'
  case putLabel l =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hg : ofThisRealm? Label.name Label.realm r (s.label? l.id) with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ labels := .put l.id.val { l with realm := r } }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hl : u.label? l.id = s.label? l.id :=
          (hu.labels l.id (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hl, hg] <;> rfl⟩
  case putParty p =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    by_cases hmine : ((s.member? au).map (·.party) != some p.id) = true
    · rw [if_pos hmine] at hok
      cases hg : ofThisRealm? Party.name Party.realm r (s.party? p.id) with
      | error e => simp only [hg] at hok; simp at hok
      | ok gu =>
        cases gu
        simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
        refine ⟨{ parties := .put p.id.val { p with realm := (((s.party? p.id).map (·.realm)).getD r) } }, ?_, hok.1.symm, ?_⟩
        · intro k hk
          simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
            List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
          subst hk
          exact mem_footprint_entity (by simp [Op.touchesEntities])
        · intro u hu
          have hp : u.party? p.id = s.party? p.id :=
            (hu.parties p.id (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
          have hm : u.member? au = s.member? au := by simp only [State.member?, hu.members]
          exact ⟨_, by
            simp only [applyChecked, bind, Except.bind, pure, Except.pure, hp, hm,
              if_pos hmine, hg] <;> rfl⟩
    · rw [if_neg hmine] at hok
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ parties := .put p.id.val { p with realm := (((s.party? p.id).map (·.realm)).getD r) } }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hp : u.party? p.id = s.party? p.id :=
          (hu.parties p.id (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        have hm : u.member? au = s.member? au := by simp only [State.member?, hu.members]
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hp, hm,
            if_neg hmine] <;> rfl⟩
  case putGroup g =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure] at hok
    by_cases hempty : g.members.isEmpty = true
    · rw [if_pos hempty] at hok; simp at hok
    rw [if_neg hempty] at hok
    cases hg : ofThisRealm? PartyGroup.name PartyGroup.realm r s.groups[g.name]? with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ groups := .put g.name { g with realm := r } }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hn : u.groups[g.name]? = s.groups[g.name]? :=
          (hu.groups g.name (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
            Except.pure, if_neg hempty, hn, hg] <;> rfl⟩
  case deleteGroup name =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hg : ofThisRealm? PartyGroup.name PartyGroup.realm r s.groups[name]? with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ groups := .drop name }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hn : u.groups[name]? = s.groups[name]? :=
          (hu.groups name (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hn, hg] <;> rfl⟩
  case putTrip tp =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hg : ofThisRealm? Trip.name Trip.realm r s.trips[tp.name]? with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ trips := .put tp.name { tp with realm := r } }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hn : u.trips[tp.name]? = s.trips[tp.name]? :=
          (hu.trips tp.name (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hn, hg] <;> rfl⟩
  case deleteTrip name =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hg : ofThisRealm? Trip.name Trip.realm r s.trips[name]? with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ trips := .drop name }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hn : u.trips[name]? = s.trips[name]? :=
          (hu.trips name (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hn, hg] <;> rfl⟩
  case putRule rl =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hg : ofThisRealm? Rule.name Rule.realm r (s.rule? rl.id) with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ rules := .put rl.id.val { rl with realm := r } }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hn : u.rule? rl.id = s.rule? rl.id :=
          (hu.rules rl.id (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hn, hg] <;> rfl⟩
  case recordImportBatch b =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hg : ofThisRealm? (fun x => s!"the import {x.id.val}") ImportBatch.realm r
        s.batches[b.id.val]? with
    | error e => simp only [hg] at hok; simp at hok
    | ok gu =>
      cases gu
      simp only [hg, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ batches := .put b.id.val { b with realm := r } }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        have hn : u.batches[b.id.val]? = s.batches[b.id.val]? :=
          (hu.batches b.id (mem_footprint_entity (by simp [Op.touchesEntities]))).symm
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, pure, Except.pure, hn, hg] <;> rfl⟩
  case registerBlob file =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure] at hok
    cases hblob : s.blob? file.sha256 with
    | some b =>
      simp only [hblob] at hok
      by_cases hmine : (b.registeredBy != au && !s.canAdminister au b.realm) = true
      · rw [if_pos hmine] at hok; simp at hok
      rw [if_neg hmine] at hok
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      let rewrapped : BlobState :=
        { b with realm := r, file := { b.file with
            cipherHash := file.cipherHash <|> b.file.cipherHash
            wrappedKey := file.wrappedKey <|> b.file.wrappedKey } }
      refine ⟨{ blobs := .put file.sha256 rewrapped }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
            Except.pure,
            ← hu.blobs file.sha256 (mem_footprint_entity (by simp [Op.touchesEntities])),
            hblob, ← canAdminister_congr hu.realms, if_neg hmine] <;> rfl⟩
    | none =>
      simp only [hblob, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ blobs := .put file.sha256 { file := file, registeredBy := au, realm := r } }, ?_,
        hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        exact ⟨_, by
          simp only [applyChecked, pure, Except.pure,
            ← hu.blobs file.sha256 (mem_footprint_entity (by simp [Op.touchesEntities])),
            hblob] <;> rfl⟩
  case attach txn sha =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure] at hok
    cases hget : txnOf s txn with
    | error e => simp only [hget] at hok; simp at hok
    | ok tx =>
      have hkeyed : tx.id.val = txn.val := hinv.keyed txn.val tx (txnOf_ok hget)
      simp only [hget] at hok
      cases hlegs : checkOwnLegs s au r tx.postings with
      | error e => simp only [hlegs] at hok; simp at hok
      | ok lu =>
      cases lu
      simp only [hlegs] at hok
      cases hblob : s.blob? sha with
      | none => simp only [hblob] at hok; simp at hok
      | some b =>
        simp only [hblob] at hok
        by_cases hhas : tx.attachments.contains sha = true
        · rw [if_pos hhas] at hok
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          refine ⟨{}, by simp [Delta.keys, Upd.key], hok.1.symm, ?_⟩
          intro u hu
          exact ⟨_, by
            simp only [applyChecked, bind, Except.bind, pure,
              Except.pure, ← txnOf_congr (hu.txns txn (mem_footprint_txn
                (by simp [Op.touchesTxns]))), hget,
              ← checkOwnLegs_congr hu.accounts hu.realms hu.budgets, hlegs,
              ← hu.blobs sha (mem_footprint_entity (by simp [Op.touchesEntities])), hblob,
              if_pos hhas] <;> rfl⟩
        · rw [if_neg hhas] at hok
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          let attached : Transaction := { tx with attachments := tx.attachments ++ [sha] }
          refine ⟨{ txns := .put tx.id.val attached }, ?_, hok.1.symm, ?_⟩
          · intro k hk
            simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none,
              List.map_cons, List.map_nil, List.append_nil,
              List.mem_singleton] at hk
            subst hk
            rw [hkeyed]
            exact mem_footprint_txn (by simp [Op.touchesTxns])
          · intro u hu
            exact ⟨_, by
              simp only [applyChecked, bind, Except.bind, pure,
                Except.pure, ← txnOf_congr (hu.txns txn (mem_footprint_txn
                  (by simp [Op.touchesTxns]))), hget,
                ← checkOwnLegs_congr hu.accounts hu.realms hu.budgets, hlegs,
                ← hu.blobs sha (mem_footprint_entity (by simp [Op.touchesEntities])), hblob,
                if_neg hhas] <;> rfl⟩
  case forgetBlob sha =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure] at hok
    by_cases hadm : (!s.canAdminister au r) = true
    · rw [if_pos hadm] at hok; simp at hok
    rw [if_neg hadm] at hok
    cases hblob : s.blob? sha with
    | none => simp only [hblob] at hok; simp at hok
    | some b =>
      simp only [hblob] at hok
      cases hhere : ofThisRealm "that receipt" r b.realm with
      | error e => simp only [hhere] at hok; simp at hok
      | ok hu0 =>
      cases hu0
      simp only [hhere, Except.ok.injEq, Prod.mk.injEq] at hok
      refine ⟨{ blobs := .drop sha }, ?_, hok.1.symm, ?_⟩
      · intro k hk
        simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
          List.map_nil, List.nil_append, List.append_nil, List.mem_singleton] at hk
        subst hk
        exact mem_footprint_entity (by simp [Op.touchesEntities])
      · intro u hu
        exact ⟨_, by
          simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
            Except.pure, ← canAdminister_congr hu.realms, if_neg hadm,
            ← hu.blobs sha (mem_footprint_entity (by simp [Op.touchesEntities])),
            hblob, hhere] <;> rfl⟩
  case detach txn sha =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    cases hget : txnOf s txn with
    | error e => simp only [hget] at hok; simp at hok
    | ok tx =>
      have hkeyed : tx.id.val = txn.val := hinv.keyed txn.val tx (txnOf_ok hget)
      simp only [hget] at hok
      cases hlegs : checkOwnLegs s au r tx.postings with
      | error e => simp only [hlegs] at hok; simp at hok
      | ok lu =>
        cases lu
        simp only [hlegs, Except.ok.injEq, Prod.mk.injEq] at hok
        let stripped : Transaction := { tx with attachments := tx.attachments.filter (· != sha) }
        refine ⟨{ txns := .put tx.id.val stripped }, ?_, hok.1.symm, ?_⟩
        · intro k hk
          simp only [Delta.keys, Upd.key, Option.toList_some, Option.toList_none, List.map_cons,
            List.map_nil, List.append_nil, List.mem_singleton] at hk
          subst hk
          rw [hkeyed]
          exact mem_footprint_txn (by simp [Op.touchesTxns])
        · intro u hu
          exact ⟨_, by
            simp only [applyChecked, bind, Except.bind, pure, Except.pure,
              ← txnOf_congr (hu.txns txn (mem_footprint_txn (by simp [Op.touchesTxns]))),
              hget, ← checkOwnLegs_congr hu.accounts hu.realms hu.budgets, hlegs] <;> rfl⟩
  all_goals simp [Op.Rebasable] at hreb

/-! ## The theorems -/

/-- A write that names nothing an operation reads leaves everything it reads alone. -/
theorem agree_run {o o' : Op} {d : Delta} {s : State} (hi : Op.Independent o' o)
    (hd : ∀ k ∈ d.keys, k ∈ o'.footprint) : Agree o s (d.run s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id hk
    refine (Delta.txn?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.txn ⟨id.val⟩) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro sha hk
    refine (Delta.blob?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.blob sha) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro id hk
    refine (Upd.getElem?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.label ⟨id.val⟩) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro id hk
    refine (Upd.getElem?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.party ⟨id.val⟩) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro n hk
    refine (Upd.getElem?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.group n) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro n hk
    refine (Upd.getElem?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.trip n) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro id hk
    refine (Upd.getElem?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.rule ⟨id.val⟩) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro id hk
    refine (Upd.getElem?_run_of_ne ?_).symm
    intro k hkm hc
    subst hc
    exact hi.not_mem (hd (Key.batch ⟨id.val⟩) (by simp [Delta.keys, Option.mem_def.mp hkm])) hk
  · intro f hk
    refine (Delta.contains_run_of_ne ?_).symm
    intro g hg hc
    subst hc
    exact hi.not_mem (hd (Key.fingerprint f) (by simp [Delta.keys, Option.mem_def.mp hg])) hk

/--
An operation that was going to succeed still succeeds after an independent one.

This is what a rebase needs. The client composed `b` against `s`; `a` arrived in
front of it; `b` still applies, because everything it reads is where it was.
`Inv` is needed for the same reason it is in `applyOp_frame`.
-/
theorem applyOp_success_comm {a b : Op} {au : MemberId} {r : RealmId} {s s₁ t₁ : State}
    {cs₁ ds₁ : List Change} (hinv : Inv r s) (hi : Op.Independent a b)
    (ha : applyOp s au r a = .ok (s₁, cs₁)) (hb : applyOp s au r b = .ok (t₁, ds₁)) :
    ∃ (t : State) (cs : List Change), applyOp s₁ au r b = .ok (t, cs) := by
  obtain ⟨-, -, hac⟩ := applyOp_eq.mp ha
  obtain ⟨hbr, hbb, hbc⟩ := applyOp_eq.mp hb
  obtain ⟨da, hda, rfl, -⟩ := applyOp_frame hinv hi.left hac
  obtain ⟨db, -, -, hball⟩ := applyOp_frame hinv hi.right hbc
  obtain ⟨cs, hcs⟩ := hball (da.run s) (agree_run hi hda)
  refine ⟨_, cs, applyOp_of_applyChecked ?_ hbb hcs⟩
  rw [checkRights_congr hi.right (Delta.realms_run da s) (Delta.members_run da s)]
  exact hbr

/--
Two independent operations reach the same ledger either way round.

Both orders succeed, and the two states they reach hold the same entry under
every key — all that can be asked of two hash maps built by the same writes in
different orders. `State.Same.sections` turns that into the equality of every
sorted list `State.canonical` prints.

`Inv` is the standing invariant of every replayed state (`inv_state`), and it is
here for `attach` and `detach`: they write the transaction they read back under
the id it carries, and `Inv.keyed` is what says that id is the key it was found
under.
-/
theorem applyOp_comm {a b : Op} {au : MemberId} {r : RealmId} {s s₁ s₂ : State}
    {cs₁ cs₂ : List Change} (hinv : Inv r s) (hi : Op.Independent a b)
    (h1 : applyOp s au r a = .ok (s₁, cs₁)) (h2 : applyOp s₁ au r b = .ok (s₂, cs₂)) :
    ∃ (t₁ t₂ : State) (ds₁ ds₂ : List Change),
      applyOp s au r b = .ok (t₁, ds₁) ∧ applyOp t₁ au r a = .ok (t₂, ds₂) ∧
        State.Same t₂ s₂ := by
  obtain ⟨h1r, h1b, h1c⟩ := applyOp_eq.mp h1
  obtain ⟨h2r, h2b, h2c⟩ := applyOp_eq.mp h2
  obtain ⟨da, hda, rfl, haall⟩ := applyOp_frame hinv hi.left h1c
  have hinv1 : Inv r (da.run s) := inv_applyOp hinv h1
  obtain ⟨db, hdb, hs₂, hball⟩ := applyOp_frame hinv1 hi.right h2c
  obtain ⟨ds₁, hb1⟩ := hball s (agree_run hi hda).symm
  obtain ⟨ds₂, ha2⟩ := haall (db.run s) (agree_run hi.symm hdb)
  refine ⟨db.run s, da.run (db.run s), ds₁, ds₂, ?_, ?_, ?_⟩
  · refine applyOp_of_applyChecked ?_ h2b hb1
    rw [checkRights_congr hi.right (Delta.realms_run da s).symm (Delta.members_run da s).symm]
    exact h2r
  · refine applyOp_of_applyChecked ?_ h1b ha2
    rw [checkRights_congr hi.left (Delta.realms_run db s) (Delta.members_run db s)]
    exact h1r
  rw [hs₂]
  exact Delta.run_comm (fun k hk k' hk' hc =>
    hi.not_mem (hda k hk) (by rw [hc]; exact hdb k' hk'))

/-! ## Rebasing

What a client does with the theorems above: it has composed an operation against
a state, and by the time it is sent, other operations have been applied in
front. `check` says whether it may resubmit without asking anybody, and
`rebase_sound` is why that answer is worth acting on.
-/

/-- Applying operations in order, stopping at the first refusal. -/
def applyOps (s : State) (au : MemberId) (r : RealmId) : List Op → Except String State
  | [] => .ok s
  | o :: os =>
    match applyOp s au r o with
    | .ok (s', _) => applyOps s' au r os
    | .error e => .error e

namespace Rebase

/--
Whether an operation may be resubmitted over the ones that arrived in front.

Every one of them has to be rebasable and independent of it, and so does the
operation itself. This is a decision about syntax alone: no state is read, which
is what lets a client take it before it has replayed anything.
-/
def check (intervening : List Op) (mine : Op) : Bool :=
  mine.Rebasable && intervening.all (fun o => o.Rebasable && Op.independent o mine)

end Rebase

/--
What `Rebase.check` promises.

An operation that applied to the state it was composed against, and that passes
the check against everything applied since, applies to the state those left. The
client may resubmit it unchanged; nothing it reads has moved.
-/
theorem rebase_sound {au : MemberId} {r : RealmId} {ops : List Op} {mine : Op} :
    ∀ {s s' : State}, Inv r s → Rebase.check ops mine = true →
      (∃ v, applyOp s au r mine = .ok v) → applyOps s au r ops = .ok s' →
        ∃ v, applyOp s' au r mine = .ok v := by
  induction ops with
  | nil =>
    intro s s' _ _ hmine hops
    simp only [applyOps, Except.ok.injEq] at hops
    exact hops ▸ hmine
  | cons o os ih =>
    intro s s' hinv hchk hmine hops
    simp only [Rebase.check, List.all_cons, Bool.and_eq_true] at hchk
    obtain ⟨hmr, ⟨hor, hind⟩, hrest⟩ := hchk
    simp only [applyOps] at hops
    cases hstep : applyOp s au r o with
    | error e => rw [hstep] at hops; simp at hops
    | ok v =>
      obtain ⟨s₁, cs₁⟩ := v
      rw [hstep] at hops
      obtain ⟨⟨t₁, ds₁⟩, hb⟩ := hmine
      refine ih (s := s₁) ?_ ?_ ?_ hops
      · exact inv_applyOp hinv hstep
      · simp only [Rebase.check, hmr, hrest, Bool.and_self]
      · obtain ⟨t, cs, hmine'⟩ := applyOp_success_comm hinv hind hstep hb
        exact ⟨(t, cs), hmine'⟩

end Resources
