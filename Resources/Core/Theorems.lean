import Resources.Core.Apply
import Std.Data.HashMap.Lemmas

/-!
# What replaying a log guarantees

`Core/Apply.lean` says what an operation does; this file says what is true of
every state an operation can produce.

*An invalid part changes nothing.* A part whose operation is refused leaves the
state exactly as it was, and an event all of whose parts are refused is a no-op
— which is what makes a part the unit of sharing rather than an event.

*Replay composes.* Replaying `l₁ ++ l₂` is replaying `l₂` on top of the state
`l₁` replayed to, so a client that has applied a prefix never has to start over.

*Replay is deterministic.* `state` is a function of the log alone: there is no
clock, no identifier generator and no map iteration in it, so two replays of one
log are the same state, not merely equal-looking ones.

*The ledger stays a ledger.* `Inv` below is the property every stored
transaction has: it balances, it is filed under its own id, every account it
mentions still exists, and every account the state knows sits in one realm.
`inv_state` carries it from `State.init` along a whole log.

*Money is conserved.* Every transaction a write reports nets to zero in every
commodity, and so does the whole replayed ledger — a trial balance that is a
theorem rather than a report.

*A claim is two legs.* A pending transaction has exactly one account that owes
and one that is owed, which is what makes `Pendings.amount` a reading rather
than a guess. `putTxn` refuses anything else, so this is the fifth clause of
`Inv` rather than — as it was — a definition saying what would have to change.

One property the design asks for is still written here as a definition rather
than a theorem: `PurseAntisymmetry`. `Account.mirrorOf` now says which bridge a
private account mirrors, so the claim is expressible; what is missing is anything
that makes it *true*, and the section at the end of this file says exactly which
part of it is provable today and which part the sync protocol has to supply.

The invariant is stated for a *domestic* log — one whose parts all name the same
realm (`Part.Domestic`). That is not a simplification of the proof but of the
design: `putTxn` keeps the legs of a transaction that sit in realms it is not
writing, which is deliberate, because a part must be applicable without the
others, and it means that "every stored transaction balances" is a statement
about one realm's ledger.

`Op.Domestic` is gone, and with it every side condition an operation used to
carry. `grant` had to *promise* that the realm it named was the realm its part
named; `checkRights` requires it, so a viewer of one realm can no longer write
themselves into another's. And `snapshot` had to promise that the state it
carried was itself invariant; there is no such promise to make, because no part
may carry a snapshot at all — `applyOp` refuses every one of them, and what a log
starts from is read off the first *event* by `replay`.

That moves the one thing a proof cannot get for free to the one place it belongs.
A genesis is believed rather than folded, so `inv_state` takes `Inv` of it as a
hypothesis — once, about the head of the log, and about nothing else. Prefix
compositionality (`state_append`) asks for a non-empty prefix for the same
reason: which event is the beginning is decided by position, and a prefix of no
events has not decided yet.
-/

namespace Resources

/-! ## Events that change nothing -/

/--
A fold over parts that are all refused at `s` returns `s` and adds no changes.

The state the fold carries never moves, so every part is refused at the same
state it was tested at, which is what makes the induction go through.
-/
private theorem foldl_parts_error (author : MemberId) (s : State) :
    ∀ (ps : List Part) (init : List Change),
      (∀ p ∈ ps, ∃ msg, applyPart s author p = .error msg) →
      ps.foldl (fun (acc : State × List Change) p =>
          match applyPart acc.1 author p with
          | .ok (s', cs) => (s', acc.2 ++ cs)
          | .error _ => acc) (s, init) = (s, init)
  | [], _, _ => rfl
  | p :: ps, init, h => by
    obtain ⟨msg, hmsg⟩ := h p (by simp)
    simp only [List.foldl_cons, hmsg]
    exact foldl_parts_error author s ps init (fun q hq => h q (by simp [hq]))

/-- An event whose parts are all refused leaves the state and the changes empty. -/
theorem step_of_all_error (s : State) (e : Event)
    (h : ∀ p ∈ e.parts, ∃ msg, applyPart s e.author p = .error msg) : step s e = (s, []) :=
  foldl_parts_error e.author s e.parts [] h

/-- One refused part is a no-op: the state is unchanged and nothing is reported. -/
theorem step_of_error (s : State) (e : Event) (p : Part) (msg : String)
    (h : applyPart s e.author p = .error msg) : step s { e with parts := [p] } = (s, []) := by
  refine step_of_all_error s { e with parts := [p] } ?_
  intro q hq
  simp only [List.mem_singleton] at hq
  exact ⟨msg, hq ▸ h⟩

/-- An event with no parts at all is a no-op. -/
theorem step_nil (s : State) (e : Event) (h : e.parts = []) : step s e = (s, []) := by
  simp [step, h]

/-! ## Replay composes -/

/-- Replaying nothing is the state the ledger starts in. -/
theorem state_nil : state [] = State.init := rfl

/--
Replaying a log is replaying its prefix and then the rest: the fold over
`l₁ ++ l₂` is the fold over `l₂` started from where `l₁` left off.

The prefix has to be non-empty, and that is the whole of what positional genesis
costs: an event is a genesis when it is *first*, so a prefix of no events at all
has not decided yet where the fold begins, and the first event of `l₂` would be
read as an ordinary event on the left and as a beginning on the right. Every
reader that has applied anything at all is covered, which is what a client
resuming a replay needs.
-/
theorem state_append (l₁ l₂ : List Event) (h : l₁ ≠ []) :
    state (l₁ ++ l₂) = l₂.foldl (fun s e => (step s e).1) (state l₁) := by
  match l₁, h with
  | e :: rest, _ =>
    simp only [state, replay, List.cons_append]
    cases hg : e.genesis? with
    | some g => simp [List.foldl_append]
    | none => simp [List.foldl_append]

/-- One more event moves the replayed state by exactly one `step`. -/
theorem state_concat (l : List Event) (e : Event) (h : l ≠ []) :
    state (l ++ [e]) = (step (state l) e).1 := by
  simp [state_append l [e] h]

/-! ## Replay is deterministic

`state` is a function, so this is `rfl`; it is worth writing down because the
property it records — that nothing in `Core` reads a clock, a random source or
the iteration order of a hash map — is a property of `applyOp`, not of `Eq`.
-/

/-- Two replays of the same log are the same state. -/
theorem state_deterministic {l₁ l₂ : List Event} (h : l₁ = l₂) : state l₁ = state l₂ := by
  rw [h]

/-- A state is `BEq`-equal to itself: its canonical form is a function of it. -/
theorem beq_self (s : State) : (s == s) = true := beq_self_eq_true s.canonical

/-- Two replays of the same log compare equal by the canonical form the tests use. -/
theorem state_beq {l₁ l₂ : List Event} (h : l₁ = l₂) : (state l₁ == state l₂) = true := by
  subst h; exact beq_self _

/-! ## Reading a hash map in sorted order

`Core` iterates over a map through `sortedValues`, so the two directions between
"stored under some key" and "reached by an iteration" are needed throughout.
-/

/-- Everything stored in a map is reached by iterating over it. -/
theorem mem_sortedValues {α : Type} {m : Std.HashMap String α} {k : String} {v : α}
    (h : m[k]? = some v) : v ∈ sortedValues m := by
  have hmem : (k, v) ∈ m.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
  have hperm := List.mergeSort_perm m.toList (fun a b => a.1 ≤ b.1)
  exact List.mem_map_of_mem ((hperm.mem_iff).mpr hmem)

/-- Everything an iteration reaches is stored under some key. -/
theorem exists_getElem?_of_mem_sortedValues {α : Type} {m : Std.HashMap String α} {v : α}
    (h : v ∈ sortedValues m) : ∃ k : String, m[k]? = some v := by
  obtain ⟨⟨k, v'⟩, hmem, rfl⟩ := List.mem_map.mp h
  have hperm := List.mergeSort_perm m.toList (fun a b => a.1 ≤ b.1)
  exact ⟨k, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp ((hperm.mem_iff).mp hmem)⟩

/-! ## Loops

Every loop in `Core/Apply.lean` is a `for` over a list in the `Except` monad,
carrying the state it is building. One lemma covers all of them: a property that
survives one turn of the body survives the loop.
-/

/--
A property of the state and of what the loop has left to do, preserved by the
body, holds when the loop is finished. Indexing by the remaining list is what
lets a proof say "everything already processed has been rewritten".
-/
theorem forIn_invariant_of_list {α β : Type} {R : List α → β → Prop}
    {f : α → β → Except String (ForInStep β)}
    (hy : ∀ (a : α) (l : List α) (b b' : β), R (a :: l) b → f a b = .ok (.yield b') → R l b')
    (hd : ∀ (a : α) (l : List α) (b b' : β), R (a :: l) b → f a b = .ok (.done b') → R [] b') :
    ∀ (l : List α) (b out : β), R l b → forIn l b f = .ok out → R [] out := by
  intro l
  induction l with
  | nil =>
    intro b out hb h
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | cons a l ih =>
    intro b out hb h
    rw [List.forIn_cons] at h
    cases hf : f a b with
    | error e => rw [hf] at h; simp only [bind, Except.bind] at h; exact absurd h (by simp)
    | ok stp =>
      rw [hf] at h
      simp only [bind, Except.bind] at h
      cases stp with
      | done b' =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hd a l b b' hb hf
      | yield b' => exact ih b' out (hy a l b b' hb hf) h

/-- A property preserved by the body of a `for` loop holds of whatever it returns. -/
theorem forIn_invariant {α β : Type} {R : β → Prop} {f : α → β → Except String (ForInStep β)}
    (hy : ∀ a b b', R b → f a b = .ok (.yield b') → R b')
    (hd : ∀ a b b', R b → f a b = .ok (.done b') → R b') :
    ∀ (l : List α) (b out : β), R b → forIn l b f = .ok out → R out :=
  forIn_invariant_of_list (R := fun _ b => R b) (fun a _ b b' => hy a b b')
    (fun a _ b b' => hd a b b')

/-! ## The write path

Every transaction the state holds was written by `putTxn`, and `putTxn` writes
only what `Transaction.validate` accepted. These are the lemmas that say so.
-/

/-- Reading an account succeeds only for an account the state has. -/
theorem accountOf_ok {s : State} {id : AccountId} {a : Account} (h : accountOf s id = .ok a) :
    s.account? id = some a := by
  unfold accountOf at h
  split at h
  · rename_i x heq; simp only [Except.ok.injEq] at h; exact h ▸ heq
  · simp at h

/-- Reading a transaction succeeds only for a transaction the state has. -/
theorem txnOf_ok {s : State} {id : TxId} {t : Transaction} (h : txnOf s id = .ok t) :
    s.txn? id = some t := by
  unfold txnOf at h
  split at h
  · rename_i x heq; simp only [Except.ok.injEq] at h; exact h ▸ heq
  · simp at h

/-- What `Transaction.validate` hands back is the transaction it was given, and it balances. -/
theorem validate_val {t : Transaction} {v : { u : Transaction // u.Balanced }}
    (h : t.validate = .ok v) : v.val = t ∧ t.Balanced := by
  unfold Transaction.validate at h
  split at h
  · rename_i hb; simp only [Except.ok.injEq] at h; exact ⟨by rw [← h], hb⟩
  · simp at h

/-- Checking the head of a list of postings, and the rest of them. -/
private theorem checkPostings_cons {s : State} {author : MemberId} {realm : RealmId}
    {allowed : List AccountId} {q : Posting} {qs : List Posting} {u : Unit}
    (h : checkPostings s author realm (q :: qs) allowed = .ok u) :
    (∃ a, s.account? q.account = some a ∧ a.realm = realm) ∧
      checkPostings s author realm qs allowed = .ok () := by
  simp only [checkPostings, List.forIn_cons, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at h ⊢
  cases hacc : accountOf s q.account with
  | error e => rw [hacc] at h; simp at h
  | ok acc =>
    simp only [hacc] at h
    have hacc' := accountOf_ok hacc
    by_cases h1 : (acc.realm != realm) = true
    · rw [if_pos h1] at h; simp at h
    · rw [if_neg h1] at h
      by_cases h2 : acc.closedOn.isSome = true
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        by_cases h3 : (!(allowed.contains q.account || s.canPostLeg author acc q.amount.minor))
            = true
        · rw [if_pos h3] at h; simp at h
        · rw [if_neg h3] at h
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h1
          exact ⟨⟨acc, hacc', h1⟩, h⟩

/--
A part's postings are checked one by one, so every leg it writes lands in an
account the state has, in the realm the part names.
-/
theorem account_of_checkPostings {s : State} {author : MemberId} {realm : RealmId}
    {allowed : List AccountId} :
    ∀ {ps : List Posting} {u : Unit}, checkPostings s author realm ps allowed = .ok u →
      ∀ p ∈ ps, ∃ a, s.account? p.account = some a ∧ a.realm = realm
  | [], _, _, p, hp => by cases hp
  | q :: qs, u, h, p, hp => by
    obtain ⟨hq, hrest⟩ := checkPostings_cons h
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hq
    · exact account_of_checkPostings hrest p hp'

/-! ## The invariant

`Inv` is what the ledger keeps. The first two clauses are about transactions:
each one balances, and each is filed under its own id — which is what makes
"the transaction with this id" a question the state can answer. The third says
no transaction points at an account that is gone, and the fourth pins the
accounts to one realm, which is what phase 1 has and what makes the legs a part
keeps from other realms empty.

The fifth is about claims. A pending transaction is a promise that somebody will
move money from one account to another, and `Pendings.amount` reads what it asks
for off its one positive leg: a third leg would make all three of "who owes",
"who is owed" and "how much" ambiguous. `putTxn` refuses one, so this is a clause
`Inv` carries rather than a property the design is still missing.
-/

/-- What every state a domestic log replays to satisfies. -/
structure Inv (r : RealmId) (s : State) : Prop where
  /-- Every stored transaction balances. -/
  balanced : ∀ (k : String) (t : Transaction), s.txns[k]? = some t → t.Balanced
  /-- Every stored transaction is filed under its own id. -/
  keyed : ∀ (k : String) (t : Transaction), s.txns[k]? = some t → t.id.val = k
  /-- Every posting of every stored transaction names an account the state has. -/
  grounded : ∀ (k : String) (t : Transaction), s.txns[k]? = some t →
    ∀ p ∈ t.postings, (s.account? p.account).isSome
  /-- Every account the state knows sits in realm `r`. -/
  oneRealm : ∀ (k : String) (a : Account), s.accounts[k]? = some a → a.realm = r
  /-- Every stored claim — every pending transaction — has exactly two legs. -/
  twoLegs : ∀ (k : String) (t : Transaction), s.txns[k]? = some t → t.state = .pending →
    t.postings.length = 2

/-- The ledger starts with no transactions and no accounts, so it starts invariant. -/
theorem inv_init : Inv Realm.selfId State.init := by
  constructor <;> intro k t h <;> simp [State.init] at h

/-- Reading back what was just inserted: either the new value, or what was there before. -/
theorem getElem?_insert_cases {α : Type} {m : Std.HashMap String α} {k k' : String} {v w : α}
    (h : (m.insert k v)[k']? = some w) : (k' = k ∧ w = v) ∨ (k' ≠ k ∧ m[k']? = some w) := by
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq] at hk
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨hk.symm, h.symm⟩
  · rename_i hk
    simp only [beq_iff_eq] at hk
    exact Or.inr ⟨fun hc => hk hc.symm, h⟩

/-- Reading back after an erase: the key is a different one, and it held this already. -/
theorem getElem?_erase_cases {α : Type} {m : Std.HashMap String α} {k k' : String} {w : α}
    (h : (m.erase k)[k']? = some w) : k' ≠ k ∧ m[k']? = some w := by
  rw [Std.HashMap.getElem?_erase] at h
  split at h
  · simp at h
  · rename_i hk; simp only [beq_iff_eq] at hk; exact ⟨fun hc => hk (by rw [hc]), h⟩

/-- Under the invariant, every leg of a stored transaction sits in the one realm. -/
theorem realmOf_of_inv {s : State} {r : RealmId} {k : String} {t : Transaction} (h : Inv r s)
    (hk : s.txns[k]? = some t) {p : Posting} (hp : p ∈ t.postings) :
    s.realmOf p.account = some r := by
  have hg := h.grounded k t hk p hp
  simp only [State.realmOf, Option.isSome_iff_exists] at hg ⊢
  obtain ⟨a, ha⟩ := hg
  rw [ha]
  simp only [Option.map_some, Option.some.injEq]
  exact h.oneRealm p.account.val a ha

/--
The legs a write keeps from other realms: under the invariant there are none,
because every leg of the transaction being replaced is in this realm already.
-/
theorem kept_nil {s : State} {r : RealmId} (h : Inv r s) (id : TxId) :
    ((Option.map (fun x : Transaction => x.postings) (s.txn? id)).getD []).filter
      (fun p => s.realmOf p.account != some r) = [] := by
  cases hold : s.txn? id with
  | none => simp
  | some t =>
    simp only [Option.map_some, Option.getD_some]
    refine List.filter_eq_nil_iff.mpr ?_
    intro p hp
    simp only [bne_iff_ne, ne_eq, Decidable.not_not]
    exact realmOf_of_inv h hold hp

/-- A state that differs only in its import fingerprints reads accounts the same way. -/
private theorem realmOf_fps (s : State) (fps : Std.HashSet String) :
    ({ s with fingerprints := fps } : State).realmOf = s.realmOf := rfl

/--
What `putTxn` does, given the invariant: it writes exactly the transaction it
validated, under that transaction's own id, touching no account and reporting
no other transaction.
-/
theorem putTxn_spec {s s' : State} {author : MemberId} {r : RealmId} {t : Transaction}
    {allowed : List AccountId} {cs : List Change} (h : Inv r s)
    (hok : putTxn s author r t allowed = .ok (s', cs)) :
    t.Balanced ∧ (∀ p ∈ t.postings, ∃ a, s.account? p.account = some a ∧ a.realm = r) ∧
      s'.txns = s.txns.insert t.id.val t ∧ s'.accounts = s.accounts ∧
      (∀ t', Change.txn t' ∈ cs → t' = t) ∧ (t.state = .pending → t.postings.length = 2) := by
  simp only [putTxn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure] at hok
  cases hchk : checkPostings s author r t.postings allowed with
  | error e => simp only [hchk] at hok; simp at hok
  | ok u =>
    simp only [hchk] at hok
    cases hval : t.validate with
    | error e => simp only [hval] at hok; simp at hok
    | ok v =>
      obtain ⟨hv, hb⟩ := validate_val hval
      simp only [hval, hv, kept_nil h, List.nil_append] at hok
      by_cases hlegs : (t.state == .pending && t.postings.length != 2) = true
      · rw [if_pos hlegs] at hok; simp at hok
      rw [if_neg hlegs] at hok
      have htwo : t.state = .pending → t.postings.length = 2 := fun hst => by
        simpa [hst] using hlegs
      refine ⟨hb, account_of_checkPostings hchk, ?_⟩
      by_cases hlen : t.postings.length > maxPostings
      · rw [if_pos hlen] at hok; simp at hok
      rw [if_neg hlen] at hok
      split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨rfl, rfl, ?_, htwo⟩
            intro t' ht'
            simp only [written, List.singleton_append, List.mem_cons] at ht'
            rcases ht' with ht' | ht' <;> simp_all
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            refine ⟨rfl, rfl, ?_, htwo⟩
            intro t' ht'
            simp only [written, List.mem_singleton] at ht'
            simp_all
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        refine ⟨rfl, rfl, ?_, htwo⟩
        intro t' ht'
        simp only [written, List.mem_singleton] at ht'
        simp_all

/-- A state that holds the same transactions in the same accounts is as invariant. -/
theorem inv_of_eq {r : RealmId} {s s' : State} (h : Inv r s) (ht : s'.txns = s.txns)
    (ha : s'.accounts = s.accounts) : Inv r s' := by
  have hacc : ∀ id, s'.account? id = s.account? id := by
    intro id; simp only [State.account?, ha]
  constructor
  · intro k t hk; exact h.balanced k t (ht ▸ hk)
  · intro k t hk; exact h.keyed k t (ht ▸ hk)
  · intro k t hk p hp; rw [hacc]; exact h.grounded k t (ht ▸ hk) p hp
  · intro k a hk; exact h.oneRealm k a (ha ▸ hk)
  · intro k t hk; exact h.twoLegs k t (ht ▸ hk)

/-- Writing a balanced transaction whose accounts all exist keeps the invariant. -/
theorem inv_written {r : RealmId} {s : State} {t : Transaction} (h : Inv r s) (hb : t.Balanced)
    (hg : ∀ p ∈ t.postings, (s.account? p.account).isSome)
    (hp : t.state = .pending → t.postings.length = 2) : Inv r (written s t).1 := by
  constructor
  · intro k t' hk
    rcases getElem?_insert_cases hk with ⟨_, rfl⟩ | ⟨-, hk'⟩
    · exact hb
    · exact h.balanced k t' hk'
  · intro k t' hk
    rcases getElem?_insert_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · rfl
    · exact h.keyed k t' hk'
  · intro k t' hk p hp'
    rcases getElem?_insert_cases hk with ⟨_, rfl⟩ | ⟨-, hk'⟩
    · exact hg p hp'
    · exact h.grounded k t' hk' p hp'
  · intro k a hk; exact h.oneRealm k a hk
  · intro k t' hk
    rcases getElem?_insert_cases hk with ⟨_, rfl⟩ | ⟨-, hk'⟩
    · exact hp
    · exact h.twoLegs k t' hk'

/-- Removing a transaction keeps the invariant. -/
theorem inv_removed {r : RealmId} {s : State} (h : Inv r s) (id : TxId) :
    Inv r (removed s id).1 := by
  constructor
  · intro k t hk; exact h.balanced k t (getElem?_erase_cases hk).2
  · intro k t hk; exact h.keyed k t (getElem?_erase_cases hk).2
  · intro k t hk p hp; exact h.grounded k t (getElem?_erase_cases hk).2 p hp
  · intro k a hk; exact h.oneRealm k a hk
  · intro k t hk; exact h.twoLegs k t (getElem?_erase_cases hk).2

/-- Writing a transaction through `putTxn` keeps the invariant, and moves no account. -/
theorem inv_putTxn {s s' : State} {author : MemberId} {r : RealmId} {t : Transaction}
    {allowed : List AccountId} {cs : List Change} (h : Inv r s)
    (hok : putTxn s author r t allowed = .ok (s', cs)) :
    Inv r s' ∧ s'.accounts = s.accounts := by
  obtain ⟨hb, hacc, htxns, haccounts, -, htwo⟩ := putTxn_spec h hok
  refine ⟨?_, haccounts⟩
  refine inv_of_eq (s := (written s t).1) ?_ htxns haccounts
  exact inv_written h hb (fun p hp => by obtain ⟨a, ha, -⟩ := hacc p hp; simp [ha]) htwo

/-! ## Writing through the helpers

`putTxn` is the only way a transaction enters the state, and the operations
reach it through four helpers: directly, in a loop (`writeAll`), after a
retirement (`replaceParts`), or through a budget division. Each of them keeps
the invariant because `putTxn` does.
-/

/-- Balancing is a property of the postings alone. -/
theorem balanced_of_postings_eq {t u : Transaction} (h : u.postings = t.postings)
    (hb : t.Balanced) : u.Balanced := by
  intro c hc
  simp only [Transaction.commodityCodes, h] at hc
  simp only [Transaction.net, h]
  exact hb c hc

/-- A loop that writes transactions through `putTxn` keeps the invariant. -/
theorem inv_forIn_putTxn {author : MemberId} {r : RealmId} {allowed : List AccountId}
    {f : Transaction → (State × List Change) → Except String (ForInStep (State × List Change))}
    (hf : ∀ t b stp, f t b = .ok stp →
      ∃ cs', putTxn b.1 author r t allowed = .ok (stp.value.1, cs'))
    {ts : List Transaction} {b out : State × List Change} (h : Inv r b.1)
    (hforIn : forIn ts b f = .ok out) : Inv r out.1 := by
  refine forIn_invariant (R := fun b : State × List Change => Inv r b.1) ?_ ?_ ts b out h hforIn
  · intro t x x' hx hstp
    obtain ⟨cs', hp⟩ := hf t x (.yield x') hstp
    exact (inv_putTxn hx hp).1
  · intro t x x' hx hstp
    obtain ⟨cs', hp⟩ := hf t x (.done x') hstp
    exact (inv_putTxn hx hp).1

/-- Writing the transactions an intent produced keeps the invariant. -/
theorem inv_writeAll {s s' : State} {author : MemberId} {r : RealmId} {ts : List Transaction}
    {allowed : List AccountId} {cs : List Change} (h : Inv r s)
    (hok : writeAll s author r ts allowed = .ok (s', cs)) : Inv r s' := by
  simp only [writeAll, bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i out hforIn
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, -⟩ := hok
    refine inv_forIn_putTxn (author := author) (allowed := allowed) ?_ h hforIn
    intro t x stp hstp
    cases hp : putTxn x.1 author r t allowed with
    | error e => simp only [hp] at hstp; simp at hstp
    | ok v =>
      simp only [hp, Except.ok.injEq] at hstp
      subst hstp
      exact ⟨v.2, rfl⟩

/-- Retiring a transaction and writing the parts it was divided into keeps the invariant. -/
theorem inv_replaceParts {s s' : State} {author : MemberId} {r : RealmId} {id : TxId}
    {parts : List Transaction} {cs : List Change} (h : Inv r s)
    (hok : replaceParts s author r id parts = .ok (s', cs)) : Inv r s' := by
  simp only [replaceParts, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hok
  repeat' split at hok
  all_goals try (exfalso; revert hok; simp; done)
  all_goals
    (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
     obtain ⟨rfl, -⟩ := hok
     refine inv_forIn_putTxn (author := author) (allowed := []) ?_ (inv_removed h id)
       (by assumption)
     intro t x stp hstp
     cases hp : putTxn x.1 author r t with
     | error e => simp only [hp] at hstp; simp at hstp
     | ok v =>
       simp only [hp, Except.ok.injEq] at hstp
       subst hstp
       exact ⟨v.2, rfl⟩)

/-! ## Accounts

Three of the four clauses of `Inv` are about transactions; the fourth is about
accounts, and so are the operations below. What has to be shown of a write is
that the account it stores is in this realm, and of a removal that nothing
points at what is going.
-/

/-- Inserting into a map cannot take away a key that was there. -/
theorem isSome_insert {α : Type} {m : Std.HashMap String α} {k k' : String} {v : α}
    (h : (m[k']?).isSome) : ((m.insert k v)[k']?).isSome := by
  rw [Std.HashMap.getElem?_insert]
  split
  · simp
  · exact h

/-- Recording an account of this realm keeps the invariant. -/
theorem inv_insert_account {r : RealmId} {s s' : State} {k : String} {a : Account} (h : Inv r s)
    (ht : s'.txns = s.txns) (hacc : s'.accounts = s.accounts.insert k a) (ha : a.realm = r) :
    Inv r s' := by
  constructor
  · intro k' t hk; exact h.balanced k' t (ht ▸ hk)
  · intro k' t hk; exact h.keyed k' t (ht ▸ hk)
  · intro k' t hk p hp
    show ((s'.accounts)[p.account.val]?).isSome
    rw [hacc]
    exact isSome_insert (h.grounded k' t (ht ▸ hk) p hp)
  · intro k' a' hk'
    rw [hacc] at hk'
    rcases getElem?_insert_cases hk' with ⟨-, rfl⟩ | ⟨-, hk''⟩
    · exact ha
    · exact h.oneRealm k' a' hk''
  · intro k' t hk; exact h.twoLegs k' t (ht ▸ hk)

/-- An account an iteration found is an account the state has, so it is in this realm. -/
theorem oneRealm_find? {r : RealmId} {s : State} (h : Inv r s) {p : Account → Bool} {a : Account}
    (hf : s.accountsSorted.find? p = some a) : a.realm = r := by
  obtain ⟨k, hk⟩ := exists_getElem?_of_mem_sortedValues (List.mem_of_find?_eq_some hf)
  exact h.oneRealm k a hk

/-- A list of naturals that sums to zero is a list of zeros. -/
private theorem eq_zero_of_mem_of_sum_eq_zero : ∀ {l : List Nat} {x : Nat}, x ∈ l → l.sum = 0 →
    x = 0
  | y :: ys, x, hx, hsum => by
    simp only [List.sum_cons, Nat.add_eq_zero_iff] at hsum
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hsum.1
    · exact eq_zero_of_mem_of_sum_eq_zero hx' hsum.2

/--
The check `deleteAccount` makes, read as a fact about the state: an account no
posting counts towards is an account no stored transaction mentions.
-/
theorem account_free_of_postingCount {s : State} {id : AccountId} (h : s.postingCount id = 0)
    {k : String} {t : Transaction} (hk : s.txns[k]? = some t) :
    ∀ p ∈ t.postings, p.account ≠ id := by
  have hmem : (t.postings.filter (fun p => p.account == id)).length ∈
      (s.txnsSorted.map (fun t => (t.postings.filter (fun p => p.account == id)).length)) :=
    List.mem_map_of_mem (mem_sortedValues hk)
  have hzero := eq_zero_of_mem_of_sum_eq_zero hmem h
  intro p hp hc
  have : p ∈ t.postings.filter (fun p => p.account == id) :=
    List.mem_filter.mpr ⟨hp, by simp [hc]⟩
  simp [List.eq_nil_of_length_eq_zero hzero] at this

/-- Removing an account nothing points at keeps the invariant. -/
theorem inv_erase_account {r : RealmId} {s s' : State} {id : AccountId} (h : Inv r s)
    (ht : s'.txns = s.txns) (hacc : s'.accounts = s.accounts.erase id.val)
    (hfree : ∀ (k : String) (t : Transaction), s.txns[k]? = some t →
      ∀ p ∈ t.postings, p.account ≠ id) :
    Inv r s' := by
  constructor
  · intro k' t hk; exact h.balanced k' t (ht ▸ hk)
  · intro k' t hk; exact h.keyed k' t (ht ▸ hk)
  · intro k' t hk p hp
    have hne : p.account ≠ id := hfree k' t (ht ▸ hk) p hp
    have hval : p.account.val ≠ id.val := fun hc => hne (congrArg AccountId.mk hc)
    show ((s'.accounts)[p.account.val]?).isSome
    rw [hacc, Std.HashMap.getElem?_erase]
    simp only [beq_iff_eq]
    rw [if_neg (fun hc => hval hc.symm)]
    exact h.grounded k' t (ht ▸ hk) p hp
  · intro k' a' hk'
    rw [hacc] at hk'
    exact h.oneRealm k' a' (getElem?_erase_cases hk').2
  · intro k' t hk; exact h.twoLegs k' t (ht ▸ hk)

/-- Balancing depends only on the amounts: moving a posting to another account keeps it. -/
theorem balanced_of_amounts_eq {t u : Transaction}
    (h : u.postings.map (·.amount) = t.postings.map (·.amount)) (hb : t.Balanced) : u.Balanced := by
  have hnet : ∀ c, u.net c = t.net c := by
    intro c
    show (u.postings.map (Posting.net c)).sum = (t.postings.map (Posting.net c)).sum
    have e : ∀ ps : List Posting, ps.map (Posting.net c) =
        (ps.map (·.amount)).map (fun a => if a.commodity.code = c then a.minor else 0) := by
      intro ps; simp [List.map_map, Posting.net, Function.comp_def]
    rw [e, e, h]
  intro c _
  rw [hnet c]
  exact Transaction.net_of_balanced hb c

/-- Stripping a label from every transaction that carried it keeps the invariant. -/
theorem inv_deleteLabel {s s' : State} {author : MemberId} {r : RealmId} {cs : List Change}
    {id : LabelId} (h : Inv r s)
    (hok : applyChecked s author r (.deleteLabel id) = .ok (s', cs)) : Inv r s' := by
  simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hok
  repeat' split at hok
  all_goals try (exfalso; revert hok; simp; done)
  · rename_i out hforIn
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, -⟩ := hok
    refine (forIn_invariant_of_list
      (R := fun (l : List Transaction) (b : State × List Change) =>
        (∀ x ∈ l, ∃ k : String, s.txns[k]? = some x) ∧ Inv r b.1 ∧ b.1.accounts = s.accounts)
      ?_ ?_ _ _ _ ⟨fun x hx => exists_getElem?_of_mem_sortedValues hx,
        inv_of_eq h rfl rfl, rfl⟩ hforIn).2.1
    · rintro t l b b' ⟨hmem, hinv, hacc⟩ hstp
      refine ⟨fun x hx => hmem x (List.mem_cons_of_mem _ hx), ?_⟩
      obtain ⟨k, hk⟩ := hmem t (by simp)
      split at hstp
      · simp only [Except.ok.injEq, ForInStep.yield.injEq] at hstp
        subst hstp
        refine ⟨inv_written hinv ?_ ?_ ?_, hacc⟩
        · exact balanced_of_postings_eq rfl (h.balanced k t hk)
        · intro p hp
          show ((b.1.accounts)[p.account.val]?).isSome
          rw [hacc]
          exact h.grounded k t hk p hp
        · exact h.twoLegs k t hk
      · simp only [Except.ok.injEq, ForInStep.yield.injEq] at hstp
        subst hstp
        exact ⟨hinv, hacc⟩
    · rintro t l b b' ⟨hmem, hinv, hacc⟩ hstp
      split at hstp <;> simp at hstp

/--
Rebooking every posting from one account into another keeps the invariant.

The postings keep their amounts and only change which account they land in, so
nothing can stop balancing; and the emptied account goes only after the loop has
rewritten every transaction that mentioned it, which is what leaves nothing
pointing at an account that is no longer there.
-/
theorem inv_mergeAccounts {s s' : State} {author : MemberId} {r : RealmId} {cs : List Change}
    {from_ into : AccountId} (h : Inv r s)
    (hok : applyChecked s author r (.mergeAccounts from_ into) = .ok (s', cs)) : Inv r s' := by
  simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hok
  split at hok
  · simp at hok
  · rename_i hne
    simp only [beq_iff_eq] at hne
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i dst hdst
        have hdst' := accountOf_ok hdst
        split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · rename_i out1 hloop1
                have hR : (∀ x ∈ ([] : List Transaction), ∃ k : String, s.txns[k]? = some x) ∧
                    Inv r out1.1 ∧ out1.1.accounts = s.accounts ∧
                    (∀ (k : String) (t' : Transaction), out1.1.txns[k]? = some t' →
                      (t'.postings.any (fun p => p.account == from_)) = true →
                        s.txns[k]? = some t' ∧ t' ∈ ([] : List Transaction)) := by
                  refine forIn_invariant_of_list
                    (R := fun (l : List Transaction) (b : State × List Change) =>
                      (∀ x ∈ l, ∃ k : String, s.txns[k]? = some x) ∧ Inv r b.1 ∧
                        b.1.accounts = s.accounts ∧
                        (∀ (k : String) (t' : Transaction), b.1.txns[k]? = some t' →
                          (t'.postings.any (fun p => p.account == from_)) = true →
                            s.txns[k]? = some t' ∧ t' ∈ l))
                    ?_ ?_ _ _ _ ⟨fun x hx => exists_getElem?_of_mem_sortedValues hx,
                      inv_of_eq h rfl rfl, rfl, fun k t' hk _ => ⟨hk, mem_sortedValues hk⟩⟩ hloop1
                  · rintro t l b b' ⟨hmem, hinv, hacc, hfree⟩ hstp
                    obtain ⟨k, hk⟩ := hmem t (by simp)
                    refine ⟨fun x hx => hmem x (List.mem_cons_of_mem _ hx), ?_⟩
                    split at hstp
                    · simp only [Except.ok.injEq, ForInStep.yield.injEq] at hstp
                      subst hstp
                      have hamt : (List.map (fun p => if (p.account == from_) = true then
                          ({ account := into, amount := p.amount, party := p.party, note := p.note,
                             origin := p.origin, tag := p.tag } : Posting) else p) t.postings).map
                            (·.amount) = t.postings.map (·.amount) := by
                        simp only [List.map_map, Function.comp_def, List.map_inj_left]
                        intro a _
                        split <;> rfl
                      have hmoved : ∀ p ∈ (List.map (fun p => if (p.account == from_) = true then
                          ({ account := into, amount := p.amount, party := p.party, note := p.note,
                             origin := p.origin, tag := p.tag } : Posting) else p) t.postings),
                          p.account = into ∨
                            ∃ q ∈ t.postings, q.account = p.account ∧ p.account ≠ from_ := by
                        intro p hp
                        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
                        by_cases hqa : (q.account == from_) = true
                        · simp [hqa]
                        · simp only [beq_iff_eq] at hqa
                          exact Or.inr ⟨q, hq, by simp [hqa], by simp [hqa]⟩
                      refine ⟨inv_written hinv (balanced_of_amounts_eq hamt (h.balanced k t hk)) ?_
                        (fun hst => by simpa using h.twoLegs k t hk hst), hacc, ?_⟩
                      · intro p hp
                        show ((b.1.accounts)[p.account.val]?).isSome
                        rw [hacc]
                        rcases hmoved p hp with hinto | ⟨q, hq, hqp, -⟩
                        · rw [hinto]
                          have hd2 : s.accounts[into.val]? = some dst := hdst'
                          rw [hd2]
                          rfl
                        · rw [← hqp]; exact h.grounded k t hk q hq
                      · intro k' t'' hk' hany
                        rcases getElem?_insert_cases hk' with ⟨-, rfl⟩ | ⟨hkne, hk''⟩
                        · exfalso
                          simp only [List.any_eq_true] at hany
                          obtain ⟨p, hp, hpa⟩ := hany
                          simp only [beq_iff_eq] at hpa
                          rcases hmoved p hp with hinto | ⟨q, hq, hqp, hpne⟩
                          · exact hne (by rw [← hinto, hpa])
                          · exact hpne hpa
                        · obtain ⟨hs, hmem'⟩ := hfree k' t'' hk'' hany
                          refine ⟨hs, ?_⟩
                          rcases List.mem_cons.mp hmem' with rfl | hmem''
                          · exact absurd (h.keyed k' t'' hs).symm hkne
                          · exact hmem''
                    · simp only [Except.ok.injEq, ForInStep.yield.injEq] at hstp
                      subst hstp
                      refine ⟨hinv, hacc, ?_⟩
                      intro k' t'' hk' hany
                      obtain ⟨hs, hmem'⟩ := hfree k' t'' hk' hany
                      refine ⟨hs, ?_⟩
                      rcases List.mem_cons.mp hmem' with rfl | hmem''
                      · rename_i hthen
                        exact absurd hany (by simp [hthen])
                      · exact hmem''
                  · rintro t l b b' ⟨hmem, hinv, hacc, hfree⟩ hstp
                    split at hstp <;> simp at hstp
                have hfree2 : ∀ (k : String) (t' : Transaction), out1.1.txns[k]? = some t' →
                    ∀ p ∈ t'.postings, p.account ≠ from_ := by
                  intro k t' hk p hp hc
                  have hmem := (hR.2.2.2 k t' hk (List.any_eq_true.mpr ⟨p, hp, by simp [hc]⟩)).2
                  simp at hmem
                split at hok
                · simp at hok
                · rename_i out2 hloop2
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hok
                  obtain ⟨rfl, -⟩ := hok
                  have hinit : Inv r { out1.1 with accounts := out1.1.accounts.erase from_.val } :=
                    inv_erase_account hR.2.1 rfl rfl hfree2
                  refine forIn_invariant (R := fun b : State × List Change => Inv r b.1) ?_ ?_ _ _ _
                    hinit hloop2
                  · intro x b b' hb hstp
                    split at hstp <;>
                      (simp only [Except.ok.injEq, ForInStep.yield.injEq] at hstp
                       subst hstp
                       exact inv_of_eq hb rfl rfl)
                  · intro x b b' hb hstp
                    split at hstp <;> simp at hstp

/-- A loop that leaves transactions and accounts alone keeps the invariant. -/
theorem inv_forIn_other {r : RealmId} {α : Type}
    {f : α → (State × List Change) → Except String (ForInStep (State × List Change))}
    (hf : ∀ a b stp, f a b = .ok stp →
      stp.value.1.txns = b.1.txns ∧ stp.value.1.accounts = b.1.accounts)
    {l : List α} {b out : State × List Change} (h : Inv r b.1) (hforIn : forIn l b f = .ok out) :
    Inv r out.1 := by
  refine forIn_invariant (R := fun b : State × List Change => Inv r b.1) ?_ ?_ l b out h hforIn
  · intro a x x' hx hstp
    obtain ⟨ht, ha⟩ := hf a x (.yield x') hstp
    exact inv_of_eq hx ht ha
  · intro a x x' hx hstp
    obtain ⟨ht, ha⟩ := hf a x (.done x') hstp
    exact inv_of_eq hx ht ha

/-- A loop that only retires transactions keeps the invariant. -/
theorem inv_forIn_removed {r : RealmId} {α : Type}
    {f : α → (State × List Change) → Except String (ForInStep (State × List Change))}
    (hf : ∀ a b stp, f a b = .ok stp → ∃ id : TxId, stp.value.1 = (removed b.1 id).1)
    {l : List α} {b out : State × List Change} (h : Inv r b.1) (hforIn : forIn l b f = .ok out) :
    Inv r out.1 := by
  refine forIn_invariant (R := fun b : State × List Change => Inv r b.1) ?_ ?_ l b out h hforIn
  · intro a x x' hx hstp
    obtain ⟨id, hid⟩ := hf a x (.yield x') hstp
    have hx' : x'.1 = (removed x.1 id).1 := hid
    rw [hx']; exact inv_removed hx id
  · intro a x x' hx hstp
    obtain ⟨id, hid⟩ := hf a x (.done x') hstp
    have hx' : x'.1 = (removed x.1 id).1 := hid
    rw [hx']; exact inv_removed hx id

/-- Raising the claims that square a budget up keeps the invariant. -/
theorem inv_squareUp {s s' : State} {author : MemberId} {r : RealmId} {b : Budget}
    {c : Commodity} {hub : Option PartyId} {due : Date} {claimIds : List TxId} {label : LabelId}
    {cs : List Change} (h : Inv r s)
    (hok : squareUp s author r b c hub due claimIds label = .ok (s', cs)) : Inv r s' := by
  simp only [squareUp, bind, Except.bind] at hok
  split at hok
  · simp at hok
  · exact inv_writeAll h hok

/-- Dividing what a budget holds, and asking for it, keeps the invariant. -/
theorem inv_divideUp {s s' : State} {author : MemberId} {r : RealmId} {b : Budget}
    {among : List Participant} {c : Commodity} {date : Date} {txnId : TxId} {hub : Option PartyId}
    {claimIds : List TxId} {label : LabelId} {cs : List Change} {flag : Bool} (h : Inv r s)
    (hok : divideUp s author r b among c date txnId hub claimIds label = .ok (s', cs, flag)) :
    Inv r s' := by
  simp only [divideUp, bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · split at hok
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, -⟩ := hok
      subst heq
      exact h
    · split at hok
      · simp at hok
      · rename_i v1 hv1
        split at hok
        · simp at hok
        · rename_i v2 hv2
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨heq, -⟩ := hok
          subst heq
          exact inv_squareUp (inv_putTxn h hv1).1 hv2

/-- Rewriting a stored transaction without touching its postings keeps the invariant. -/
theorem inv_written_of_stored {r : RealmId} {s : State} {id : TxId} {t u : Transaction}
    (h : Inv r s) (hst : s.txn? id = some t) (hp : u.postings = t.postings)
    (hs : u.state = t.state) : Inv r (written s u).1 :=
  inv_written h (balanced_of_postings_eq hp (h.balanced id.val t hst))
    (fun p hpm => h.grounded id.val t hst p (hp ▸ hpm))
    (fun hst' => hp ▸ h.twoLegs id.val t hst (hs ▸ hst'))

/--
`inv_putTxn` with the equation first, so a chain of writes can be followed
backwards: each write names the state the one before it produced.
-/
theorem inv_putTxn_fst {s s' : State} {author : MemberId} {r : RealmId} {t : Transaction}
    {allowed : List AccountId} {cs : List Change}
    (hok : putTxn s author r t allowed = .ok (s', cs)) (h : Inv r s) : Inv r s' :=
  (inv_putTxn h hok).1

/-- `inv_forIn_putTxn` with the loop first, so the state it started from is read off it. -/
theorem inv_forIn_putTxn_of {author : MemberId} {r : RealmId} {allowed : List AccountId}
    {f : Transaction → (State × List Change) → Except String (ForInStep (State × List Change))}
    {ts : List Transaction} {b out : State × List Change} (hforIn : forIn ts b f = .ok out)
    (hf : ∀ t b stp, f t b = .ok stp →
      ∃ cs', putTxn b.1 author r t allowed = .ok (stp.value.1, cs'))
    (h : Inv r b.1) : Inv r out.1 :=
  inv_forIn_putTxn hf h hforIn

/-- `inv_forIn_removed` with the loop first, for the same reason. -/
theorem inv_forIn_removed_of {r : RealmId} {α : Type}
    {f : α → (State × List Change) → Except String (ForInStep (State × List Change))}
    {l : List α} {b out : State × List Change} (hforIn : forIn l b f = .ok out)
    (hf : ∀ a b stp, f a b = .ok stp → ∃ id : TxId, stp.value.1 = (removed b.1 id).1)
    (h : Inv r b.1) : Inv r out.1 :=
  inv_forIn_removed hf h hforIn

/--
Meeting a claim keeps the invariant: every write it makes goes through `putTxn`.

`resolveClaim` and `payClaim` both end here, so the three writes a settlement can
make — the payment pointed at whose money it was, the claim marked settled, and
the two halves a part payment leaves — are checked once.
-/
theorem inv_settleClaim {s s' : State} {author : MemberId} {r : RealmId}
    {id actual splitId : TxId} {allowed : List AccountId} {cs : List Change} (h : Inv r s)
    (hok : settleClaim s author r id actual splitId allowed = .ok (s', cs)) : Inv r s' := by
  simp only [settleClaim, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
  repeat' split at hok
  all_goals first
    | exact inv_writeAll h hok
    | simp at hok

/-! ## Every operation keeps the invariant

The cases below are the whole of `applyOp`. Most of them do not touch a
transaction or an account at all, and the invariant passes through them
unchanged; the ones that write go through `putTxn`, `written` or `removed`, and
the lemmas above say what each of those does.

No operation carries a side condition any more. `snapshot` used to: it replaces
the state wholesale, so it could only be as sound as the state it carried. It is
refused outright now, wherever it appears and whoever wrote it, so the case
below has nothing to prove — and the soundness of a genesis is `inv_state`'s
hypothesis, about the head of the log, where it belongs.

`grant` used to carry one too — a grant could name a realm other than its part's,
and the purse it opened landed there. `checkRights` refuses that now, and the
proof reads the refusal rather than assuming it away: the `grant` case below
recovers `target = r` from the rights check the operation passed.

Three operations have a second door, for the member they are about: `addMember`
for somebody's own record, `grant` for their own viewer role, and `putParty` for
the party their own spending lands on. None needs a word here. A self-grant
inserts a purse in the realm the part names, as the admin path does; and the
party records `addMember` and `putParty` write touch no transaction and no
account, which is the whole of what `inv_of_eq` asks of a change.
-/

/-- Unfolds one operation and finishes the cases that leave transactions and accounts alone. -/
macro "plain_op " h:ident hv:ident : tactic =>
  `(tactic|
    (simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at $h:ident
     repeat' split at $h:ident
     all_goals first
       | (simp only [Except.ok.injEq, Prod.mk.injEq] at $h:ident
          obtain ⟨heq, -⟩ := $h:ident
          subst heq
          exact inv_of_eq $hv:ident rfl rfl)
       | simp at $h:ident))

/--
A part is domestic when it applies in `r`.

It used to promise something about the operation as well: a snapshot carries a
whole state, so the invariant could only be as good as what that state
contained. That condition is gone because the operation is gone — no part may
carry a snapshot at all, so nothing an event says can replace the state, and
what a log starts from is `replay`'s business rather than a part's. The genesis
hypothesis of `inv_state` is where it reappears, once, at the only position it
can matter.
-/
def Part.Domestic (r : RealmId) (p : Part) : Prop := p.realm = r

/--
Every operation an invariant state accepts leaves an invariant state.

This is the phase's theorem: whatever a log asks for, what it replays into is a
ledger whose transactions balance, are filed under their own ids, and point only
at accounts the state has.
-/
theorem inv_applyOp {s s' : State} {author : MemberId} {r : RealmId} {op : Op} {cs : List Change}
    (h : Inv r s) (hok : applyOp s author r op = .ok (s', cs)) : Inv r s' := by
  obtain ⟨hrights, -, hok⟩ := applyOp_eq.mp hok
  cases op with
  | createRealm x => plain_op hok h
  | putAccount a =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · rename_i old hold
      split at hok
      · simp at hok
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨heq, -⟩ := hok
        subst heq
        exact inv_insert_account h rfl rfl (h.oneRealm a.id.val old hold)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨heq, -⟩ := hok
      subst heq
      exact inv_insert_account h rfl rfl rfl
  | mergeAccounts from_ into => exact inv_mergeAccounts h hok
  | deleteAccount id =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i hcount
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨heq, -⟩ := hok
          subst heq
          exact inv_erase_account h rfl rfl
            (fun k t hk => account_free_of_postingCount (by omega) hk)
  | setAccountRights id posters =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · simp at hok
    · rename_i a ha
      split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨heq, -⟩ := hok
          subst heq
          exact inv_insert_account h rfl rfl (h.oneRealm id.val a (accountOf_ok ha))
  | setAccountOwner id owner =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · simp at hok
    · rename_i a ha
      split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨heq, -⟩ := hok
          subst heq
          exact inv_insert_account h rfl rfl (h.oneRealm id.val a (accountOf_ok ha))
  | putLabel l => plain_op hok h
  | deleteLabel id => exact inv_deleteLabel h hok
  | putParty p => plain_op hok h
  | putGroup g => plain_op hok h
  | deleteGroup name => plain_op hok h
  | putTrip t => plain_op hok h
  | deleteTrip name => plain_op hok h
  | putRule rule => plain_op hok h
  | deleteRule idOrName =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · rename_i out hloop
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨heq, -⟩ := hok
        subst heq
        refine inv_forIn_other ?_ h hloop
        intro a b stp hstp
        simp only [Except.ok.injEq] at hstp
        subst hstp
        exact ⟨rfl, rfl⟩
  | putTransaction t =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals first
      | exact (inv_putTxn h hok).1
      | simp at hok
  | deleteTransaction id =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    repeat' split at hok
    all_goals first
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
         obtain ⟨heq, -⟩ := hok
         subst heq
         exact inv_removed h id)
      | simp at hok
  | splitTransaction id targets keepShare =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals first
      | exact (inv_putTxn h hok).1
      | simp at hok
  | mergeTransactions ids newId payee narration cancelIn =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals try (exfalso; revert hok; simp; done)
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
       obtain ⟨heq, -⟩ := hok
       subst heq
       refine inv_putTxn_fst (by assumption) (inv_forIn_removed_of (by assumption) ?_ h)
       intro a b stp hstp
       simp only [Except.ok.injEq] at hstp
       subst hstp
       exact ⟨a.id, rfl⟩)
  | unmergeTransaction id newIds =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals try (exfalso; revert hok; simp; done)
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
       obtain ⟨heq, -⟩ := hok
       subst heq
       refine inv_forIn_putTxn_of (author := author) (allowed := []) (by assumption) ?_
         (inv_removed h id)
       intro t x stp hstp
       cases hp : putTxn x.1 author r t with
       | error e => simp only [hp] at hstp; simp at hstp
       | ok v =>
         simp only [hp, Except.ok.injEq] at hstp
         subst hstp
         exact ⟨v.2, rfl⟩)
  | replaceTransaction id parts kind =>
    simp only [applyChecked] at hok
    exact inv_replaceParts h hok
  | divideByItems id groups newIds =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals try (exact absurd hok (by simp))
    all_goals exact inv_replaceParts h hok
  | raiseClaim t =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals first
      | exact (inv_putTxn h hok).1
      | simp at hok
  | resolveClaim id actual splitId =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals first
      | exact inv_settleClaim h hok
      | simp at hok
  | voidClaim id writeOff =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals try (exfalso; revert hok; simp; done)
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
       obtain ⟨heq, -⟩ := hok
       subst heq
       first
         | exact h
         | exact inv_putTxn_fst (by assumption) h
         | exact inv_putTxn_fst (by assumption) (inv_putTxn_fst (by assumption) h))
  | openBudget b account =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals try (exfalso; revert hok; simp; done)
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
       obtain ⟨heq, -⟩ := hok
       subst heq
       first
         | exact h
         | (refine inv_insert_account h rfl rfl ?_
            first
              | rfl
              | exact oneRealm_find? h (by assumption)))
  | setParticipants budget among => plain_op hok h
  | contribute budget t =>
    simp only [applyChecked, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals first
      | exact (inv_putTxn h hok).1
      | simp at hok
  | allocate budget among commodity date hub txnId claimIds labelId =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i v hv
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨heq, -⟩ := hok
          subst heq
          exact inv_of_eq (inv_divideUp h hv) (pinLabel_frame _ _ _).1 (pinLabel_frame _ _ _).2
  | settle budget commodity hub due claimIds labelId =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · rename_i v hv
          simp only [Except.ok.injEq, Prod.mk.injEq] at hok
          obtain ⟨heq, -⟩ := hok
          subst heq
          exact inv_of_eq (inv_squareUp h hv) (pinLabel_frame _ _ _).1 (pinLabel_frame _ _ _).2
  | closeBudget budget among commodity hub date txnId claimIds labelId =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · simp at hok
    · split at hok
      · simp at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · rename_i v hv
              have h1 : Inv r v.1 := inv_divideUp h hv
              split at hok
              · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
                obtain ⟨heq, -⟩ := hok
                subst heq
                exact inv_of_eq h1 rfl rfl
              · split at hok
                · simp at hok
                · rename_i v2 hv2
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hok
                  obtain ⟨heq, -⟩ := hok
                  subst heq
                  exact inv_of_eq (inv_squareUp h1 hv2) rfl rfl
  | reopenBudget budget => plain_op hok h
  | deleteBudget budget => plain_op hok h
  | issueInvoice inv sources => plain_op hok h
  | setInvoiceStatus id status => plain_op hok h
  | settleInvoice id txn => plain_op hok h
  | deleteInvoice id => plain_op hok h
  | registerBlob file => plain_op hok h
  | attach txn sha =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    split at hok
    · simp at hok
    · rename_i t ht
      repeat' split at hok
      all_goals first
        | (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
           obtain ⟨heq, -⟩ := hok
           subst heq
           first
             | exact h
             | exact inv_written_of_stored h (txnOf_ok ht) rfl rfl)
        | simp at hok
  | detach txn sha =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure] at hok
    split at hok
    · simp at hok
    · rename_i t ht
      repeat' split at hok
      all_goals first
        | (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
           obtain ⟨heq, -⟩ := hok
           subst heq
           exact inv_written_of_stored h (txnOf_ok ht) rfl rfl)
        | simp at hok
  | recordExtraction sha e => plain_op hok h
  | setReceiptLines sha items => plain_op hok h
  | forgetBlob sha => plain_op hok h
  | recordImportBatch b => plain_op hok h
  | addMember m => plain_op hok h
  | removeMember id => plain_op hok h
  | grant target member role bridge =>
    -- The purse a grant opens is opened in the realm the grant names, and
    -- `checkRights` has already refused a grant naming any realm but this
    -- part's — which is what used to be assumed here rather than checked.
    have htarget : target = r := by
      simp only [checkRights, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at hrights
      by_cases hc : (target != r) = true
      · rw [if_pos hc] at hrights; simp at hrights
      · simpa using hc
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals first
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
         obtain ⟨heq, -⟩ := hok
         subst heq
         first
           | exact inv_of_eq h rfl rfl
           | exact inv_insert_account h rfl rfl htarget)
      | simp at hok
  | revoke target member => plain_op hok h
  | setRole target member role => plain_op hok h
  | rotateRealmKey target => plain_op hok h
  | snapshot genesis =>
    -- Refused, always: genesis is a position in the log, and `Core.replay` is
    -- what reads it. So there is nothing here to keep the invariant through.
    simp [applyChecked] at hok
  | payClaim id payment date =>
    simp only [applyChecked, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hok
    repeat' split at hok
    all_goals try (exfalso; revert hok; simp; done)
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at hok
       obtain ⟨heq, -⟩ := hok
       subst heq
       rename_i _ vput hput _ vset hset
       exact inv_settleClaim (inv_putTxn h hput).1 hset)

/-! ## Replaying a whole log -/

/-- The fold `step` performs: an invariant state stays invariant, part by part. -/
private theorem inv_foldl_parts {r : RealmId} (author : MemberId) :
    ∀ (ps : List Part) (acc : State × List Change), Inv r acc.1 →
      (∀ p ∈ ps, Part.Domestic r p) →
      Inv r (ps.foldl (fun (acc : State × List Change) p =>
          match applyPart acc.1 author p with
          | .ok (s', cs) => (s', acc.2 ++ cs)
          | .error _ => acc) acc).1
  | [], _, h, _ => h
  | p :: ps, acc, h, hd => by
    simp only [List.foldl_cons]
    refine inv_foldl_parts author ps _ ?_ (fun q hq => hd q (by simp [hq]))
    have hrealm := hd p (by simp)
    cases hp : applyPart acc.1 author p with
    | error e => exact h
    | ok v =>
      exact inv_applyOp h (show applyOp acc.1 author r p.op = .ok (v.1, v.2) by
        rw [← hrealm]; exact hp)

/--
Applying an event keeps the invariant.

A part that is refused leaves the state where it was, and a part that is applied
is an operation this state accepts, so every part of the fold is covered.
-/
theorem inv_step {r : RealmId} {s : State} {e : Event} (h : Inv r s)
    (hd : ∀ p ∈ e.parts, Part.Domestic r p) : Inv r (step s e).1 :=
  inv_foldl_parts e.author e.parts (s, []) h hd

/-- The fold `state` performs: an invariant state stays invariant, event by event. -/
private theorem inv_foldl_events {r : RealmId} :
    ∀ (log : List Event) (s : State), Inv r s →
      (∀ e ∈ log, ∀ p ∈ e.parts, Part.Domestic r p) →
      Inv r (log.foldl (fun s e => (step s e).1) s)
  | [], _, h, _ => h
  | e :: es, s, h, hd =>
    inv_foldl_events es (step s e).1 (inv_step h (hd e (by simp)))
      (fun x hx => hd x (by simp [hx]))

/--
Replaying a domestic log gives a ledger that keeps the invariant.

This is phase 2's theorem, at the level a reader of the log cares about: whatever
sequence of events is replayed — valid, invalid, out of order, repeated — every
transaction in the resulting state balances, is filed under its own id, and
names only accounts the state has.
-/
theorem inv_state (log : List Event)
    (hg : ∀ e ∈ log.head?, ∀ g ∈ e.genesis?, Inv Realm.selfId g)
    (hd : ∀ e ∈ log, ∀ p ∈ e.parts, Part.Domestic Realm.selfId p) :
    Inv Realm.selfId (state log) := by
  match log with
  | [] => exact inv_init
  | e :: rest =>
    simp only [state, replay]
    cases hge : e.genesis? with
    | some g =>
      -- The genesis is believed, and this is the one hypothesis that says so.
      -- A whole state cannot be checked by folding it; what can be checked is
      -- that it is read at position 1 and nowhere else, which is `replay`'s
      -- shape rather than a theorem.
      exact inv_foldl_events rest g (hg e (by simp) g (by simp [hge]))
        (fun x hx => hd x (by simp [hx]))
    | none =>
      exact inv_foldl_events (e :: rest) State.init inv_init hd

/-! ## Conservation

A balanced transaction nets to zero in every commodity (`net_of_balanced`), and
the invariant says every stored transaction is balanced; putting the two
together is what "the money is conserved" means for a state and for a log.
-/

/--
The trial balance of an invariant state is zero, in every commodity.

This is `Ledger.totalNet_eq_zero` lifted to a state: every posted transaction it
holds balances, so the total across all accounts is zero — money is conserved by
replay, not merely by each entry.
-/
theorem totalNet_eq_zero_of_inv {r : RealmId} {s : State} (h : Inv r s) (c : String) :
    s.ledger.totalNet c = 0 := by
  refine Ledger.totalNet_eq_zero _ (fun t ht => ?_) c
  have ht' : t ∈ s.txnsSorted := (List.mem_filter.mp ht).1
  obtain ⟨k, hk⟩ := exists_getElem?_of_mem_sortedValues ht'
  exact h.balanced k t hk


/-- Every transaction an accepted operation leaves in the ledger nets to zero, per commodity. -/
theorem net_eq_zero_of_applyOp {s s' : State} {author : MemberId} {r : RealmId} {op : Op}
    {cs : List Change} (h : Inv r s)
    (hok : applyOp s author r op = .ok (s', cs)) (k : String) (t : Transaction)
    (hk : s'.txns[k]? = some t) (c : String) : t.net c = 0 :=
  Transaction.net_of_balanced ((inv_applyOp h hok).balanced k t hk) c

/--
Conservation, per part: every transaction a write reports balances.

`putTxn` reports the transaction it validated and nothing else, so each `Change`
the store projects into SQL sums to zero in every commodity — which is what
makes a part something another reader can apply on its own.
-/
theorem net_eq_zero_of_changes {s s' : State} {author : MemberId} {r : RealmId} {t : Transaction}
    {cs : List Change} (h : Inv r s) (hok : putTxn s author r t = .ok (s', cs))
    (t' : Transaction) (hmem : Change.txn t' ∈ cs) (c : String) : t'.net c = 0 := by
  obtain ⟨hb, -, -, -, hch, -⟩ := putTxn_spec h hok
  rw [hch t' hmem]
  exact Transaction.net_of_balanced hb c

/-- The trial balance of any replayed ledger is zero. -/
theorem totalNet_state (log : List Event)
    (hg : ∀ e ∈ log.head?, ∀ g ∈ e.genesis?, Inv Realm.selfId g)
    (hd : ∀ e ∈ log, ∀ p ∈ e.parts, Part.Domestic Realm.selfId p) (c : String) :
    (state log).ledger.totalNet c = 0 :=
  totalNet_eq_zero_of_inv (inv_state log hg hd) c

/-! ## Purses

A member's balance inside somebody else's realm lives on a *bridge* account
there; the same balance, seen from their own books, lives on a private account in
their own realm, and `Account.mirrorOf` on the private one names the bridge. The
question this section answers is what follows from that link, and what does not.
-/

/-- Over postings that land in one of two accounts, the two nets add up to the whole. -/
private theorem netIn_add_netIn (b m : AccountId) (c : String) (hne : b ≠ m) :
    ∀ ps : List Posting, (∀ p ∈ ps, p.account = b ∨ p.account = m) →
      (ps.map (Posting.netIn b c)).sum + (ps.map (Posting.netIn m c)).sum =
        (ps.map (Posting.net c)).sum
  | [], _ => by simp
  | p :: ps, hall => by
    have ih := netIn_add_netIn b m c hne ps (fun q hq => hall q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, Posting.netIn]
    rcases hall p (by simp) with hb | hm
    · rw [if_pos hb, if_neg (fun hc : p.account = m => hne (by rw [← hb, hc]))]
      omega
    · rw [if_pos hm, if_neg (fun hc : p.account = b => hne (by rw [← hc, hm]))]
      omega

/--
Antisymmetry for a transaction with nothing else in it.

A transaction that touches exactly two accounts — a member's purse and whatever
it faces — moves them by equal and opposite amounts in every commodity.
-/
theorem netIn_antisymm {t : Transaction} {b m : AccountId} (hne : b ≠ m) (hb : t.Balanced)
    (hall : ∀ p ∈ t.postings, p.account = b ∨ p.account = m) (c : String) :
    t.netIn b c = -t.netIn m c := by
  have hsum := netIn_add_netIn b m c hne t.postings hall
  have hzero := Transaction.net_of_balanced hb c
  simp only [Transaction.net] at hzero
  simp only [Transaction.netIn]
  omega

/-- One account's net, and the net of everything beside it, add up to the whole. -/
private theorem sum_netIn_add_rest (a : AccountId) (c : String) : ∀ ps : List Posting,
    (ps.map (Posting.netIn a c)).sum +
        ((ps.filter (fun p => p.account != a)).map (Posting.net c)).sum =
      (ps.map (Posting.net c)).sum
  | [] => by simp
  | p :: ps => by
    have ih := sum_netIn_add_rest a c ps
    by_cases h : p.account = a
    · simp only [List.map_cons, List.sum_cons, List.filter_cons]
      rw [show Posting.netIn a c p = Posting.net c p from by simp [Posting.netIn, h],
        if_neg (by simp [h] : ¬(p.account != a) = true)]
      omega
    · simp only [List.map_cons, List.sum_cons, List.filter_cons]
      rw [show Posting.netIn a c p = 0 from by simp [Posting.netIn, h],
        if_pos (by simp [h] : (p.account != a) = true)]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Postings that land nowhere near an account contribute nothing to its balance. -/
private theorem sum_netIn_eq_zero (a : AccountId) (c : String) : ∀ ps : List Posting,
    (∀ p ∈ ps, p.account ≠ a) → (ps.map (Posting.netIn a c)).sum = 0
  | [], _ => by simp
  | p :: ps, h => by
    have ih := sum_netIn_eq_zero a c ps (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, Posting.netIn, if_neg (h p (by simp))]
    omega

/--
What a balanced part says about one account inside it: its net is the negation
of everything else in that part, and nothing more.
-/
theorem netIn_eq_neg_rest {ps : List Posting} (a : AccountId) (c : String)
    (h : (ps.map (Posting.net c)).sum = 0) :
    (ps.map (Posting.netIn a c)).sum =
      -((ps.filter (fun p => p.account != a)).map (Posting.net c)).sum := by
  have := sum_netIn_add_rest a c ps
  omega

/--
What purse antisymmetry says, now that a mirror names the bridge it mirrors.

Antisymmetry is the claim that a transaction moving the pair moves them by equal
and opposite amounts, so that the two together can neither create money nor
destroy it. `a` is the private account, `b` the bridge `a.mirrorOf` names.

This is a definition and not a theorem, and the reason is now a fact about
transactions rather than a gap in what the state can express. A transaction
written across two realms is written in two parts, each balancing on its own —
that is what makes a part something a reader who can decrypt only one realm can
apply. `netIn_eq_neg_rest` is everything each part gives: the leg on `a` is minus
the rest of `a`'s part, and the leg on `b` is minus the rest of `b`'s part. The
two parts are otherwise unrelated, so nothing stops a composer from writing
`a -10, Expenses +10` in one and `b -10, Expenses +10` in the other: both parts
balance, both are accepted, and `a` and `b` move the same way rather than
opposite ways. Making the claim true is the composer's obligation and the sync
protocol's to check — the part carrying a purse movement has to reach both realms
and say the same thing in each — not something `applyOp` can enforce from inside
one part. What is provable here is `purseAntisymmetry_of_two_legs`: when the
transaction is nothing but the pair, the two do move opposite ways.
-/
def PurseAntisymmetry (s : State) (t : Transaction) (c : String) : Prop :=
  ∀ a b : Account, s.account? a.id = some a → s.account? b.id = some b →
    a.mirrorOf = some b.id → t.netIn a.id c = -t.netIn b.id c

/--
Antisymmetry holds of a transaction that is nothing but a mirror and its bridge.

This is the single-transaction form the design asked for, in the only shape it
is true in: a payment between the two accounts and no third leg anywhere.
-/
theorem purseAntisymmetry_of_two_legs {s : State} {t : Transaction} {c : String}
    (hbal : t.Balanced)
    (hall : ∀ a b : Account, s.account? a.id = some a → s.account? b.id = some b →
      a.mirrorOf = some b.id →
        a.id ≠ b.id ∧ ∀ p ∈ t.postings, p.account = a.id ∨ p.account = b.id) :
    PurseAntisymmetry s t c := by
  intro a b ha hb hm
  obtain ⟨hne, hlegs⟩ := hall a b ha hb hm
  exact netIn_antisymm hne hbal hlegs c

/--
The two-part form, and exactly how far it gets.

`t` is written in two parts: `ps`, the legs in the private account's realm, and
`qs`, the legs in the bridge's. Each part balances on its own; `a` appears only
in `ps` and `b` only in `qs`. What follows is one equation per part — each
account's leg is minus the rest of its own part — and `t.netIn a c = -t.netIn b c`
is not among them, because the two right-hand sides are sums over disjoint sets
of postings that nothing here relates.
-/
theorem netIn_of_balanced_parts {t : Transaction} {c : String} {ps qs : List Posting}
    {a b : AccountId} (hsplit : t.postings = ps ++ qs)
    (hp : (ps.map (Posting.net c)).sum = 0) (hq : (qs.map (Posting.net c)).sum = 0)
    (hqa : ∀ p ∈ qs, p.account ≠ a) (hpb : ∀ p ∈ ps, p.account ≠ b) :
    t.netIn a c = -((ps.filter (fun p => p.account != a)).map (Posting.net c)).sum ∧
      t.netIn b c = -((qs.filter (fun p => p.account != b)).map (Posting.net c)).sum := by
  constructor
  · simp only [Transaction.netIn, hsplit, List.map_append, List.sum_append,
      sum_netIn_eq_zero a c qs hqa, Int.add_zero]
    exact netIn_eq_neg_rest a c hp
  · simp only [Transaction.netIn, hsplit, List.map_append, List.sum_append,
      sum_netIn_eq_zero b c ps hpb, Int.zero_add]
    exact netIn_eq_neg_rest b c hq

end Resources
