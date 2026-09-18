import Resources.Import.Staging

/-!
# Linking rows that are one event

Banks routinely post one economic event as several lines: a card purchase abroad
and the foreign-use fee beside it, or a transfer that appears in both accounts'
statements. This module finds those pairs so they can be promoted as a single
transaction.

Nothing here decides anything on its own — it produces proposals that a person
confirms, because a wrong merge is far more annoying to unpick than a missed one.
-/

namespace Resources

/-! ## Card transaction signatures

A Consorsbank fee line quotes its parent purchase:

```
Gebühren     -1,23  VISA 63371014 KINGS X (N) 50,00 GBP           20.08.  12874112
Lastschrift -58,56  VISA 63371014 KINGS X (N) 50,00 GBP 1,1711700 19.08.  58,56 10354112
```

The card number, merchant and original foreign amount are shared; the booking
date and the exchange rate are not. That gives an exact join key, rather than a
similarity score.
-/

/-- The parts of a card purchase that both the purchase and its fee line quote. -/
structure CardSignature where
  card : String
  merchant : String
  amount : String
  currency : String
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace CardSignature

instance : ToString CardSignature :=
  ⟨fun s => s!"{s.card}/{s.merchant}/{s.amount} {s.currency}"⟩

/-- A German-formatted money token such as `50,00` or `1.234,56`. -/
private def isMoneyToken (s : String) : Bool :=
  match s.splitOn "," with
  | [whole, frac] =>
    frac.length == 2 && frac.all Char.isDigit &&
      !whole.isEmpty && whole.all (fun c => c.isDigit || c == '.')
  | _ => false

/-- A three-letter ISO currency code. -/
private def isCurrencyToken (s : String) : Bool :=
  s.length == 3 && s.all (fun c => c.isUpper && c.isAlpha)

/--
Extracts the signature from a purpose line of the form
`VISA <card> <merchant…> <amount> <CUR> …`.

The exchange rate that follows the currency on a purchase line is deliberately
ignored: only the fields both lines carry may take part in the key.
-/
def parse? (purpose : String) : Option CardSignature := Id.run do
  let tokens := (purpose.splitOn " ").filter (fun t => !t.isEmpty)
  let arr := tokens.toArray
  -- The amount is the money token immediately followed by a currency code.
  let mut found : Option Nat := none
  for i in [0 : arr.size] do
    if found.isNone && i + 1 < arr.size then
      if isMoneyToken arr[i]! && isCurrencyToken arr[i + 1]! then found := some i
  let some idx := found | return none
  let some cardAt := (List.range arr.size).find? (fun i => arr[i]! == "VISA") | return none
  if cardAt + 1 ≥ idx then return none
  let card := arr[cardAt + 1]!
  let merchant := String.intercalate " "
    ((List.range idx).filter (fun i => i > cardAt + 1) |>.map (fun i => arr[i]!))
  return some { card, merchant, amount := arr[idx]!, currency := arr[idx + 1]! }

end CardSignature

/-! ## Proposals -/

/-- A suggestion that two staged rows are one event. -/
structure MergeProposal where
  /-- The row carrying the main amount. -/
  parent : StagedId
  /-- The row that belongs with it, typically a fee. -/
  child : StagedId
  /-- Why they were paired, shown to the person confirming. -/
  reason : String
  /-- `high` when the pairing is unambiguous, `medium` when it was disambiguated. -/
  confidence : String
  deriving Repr

namespace Link

/-- Nearest-integer division, used to predict a fee from a percentage. -/
private def divRoundLink (a b : Int) : Int :=
  if b == 0 then 0 else if a ≥ 0 then (a + b / 2) / b else -((-a + b / 2) / b)

/--
The little that pairing needs to know about a row. Staged entries and already
promoted transactions both reduce to this, so one algorithm serves both.
-/
structure Item where
  key : String
  payee : String
  purpose : String
  /-- `|amount|` in minor units. -/
  magnitude : Int
  deriving Repr, Inhabited

/-- Whether an item looks like a fee posted beside another row. -/
def isFee (feeWords : List String) (i : Item) : Bool :=
  let hay := (i.payee ++ " " ++ i.purpose).toLower
  feeWords.any (fun w => Str.containsCI hay w)

/-- A staged row as a pairing item. -/
def ofStaged (e : StagedEntry) : Item :=
  { key := e.id.val, payee := e.raw.payee.getD "", purpose := e.raw.purpose.getD ""
    magnitude := let m := e.raw.amount.minor; if m < 0 then -m else m }

/-- A transaction as a pairing item, measured by its largest posting. -/
def ofTxn (t : Transaction) : Item :=
  { key := t.id.val, payee := t.payee.getD "", purpose := t.narration
    magnitude := t.postings.foldl (fun best p =>
      let m := p.amount.minor
      max best (if m < 0 then -m else m)) 0 }

/--
Pairs fee rows with their parent purchases.

Matching is exact on the card signature. Where a signature occurs more than once
— the same amount at the same merchant twice — the fee is assigned to the
candidate whose amount best matches the expected percentage, then to the nearest
booking date, and each purchase can only be claimed once.
-/
def proposePairs (items : Array Item) (feeWords : List String) (feeRateBp : Int) :
    Array (String × String × String × String) := Id.run do
  let fees := items.filter (isFee feeWords)
  let purchases := items.filter (fun i => !isFee feeWords i)
  let mut claimed : List String := []
  let mut out : Array (String × String × String × String) := #[]
  for fee in fees do
    let some sig := CardSignature.parse? fee.purpose | continue
    let candidates := purchases.filter fun p =>
      !claimed.contains p.key && (CardSignature.parse? p.purpose).any (· == sig)
    if candidates.isEmpty then continue
    if candidates.size == 1 then
      claimed := candidates[0]!.key :: claimed
      out := out.push (candidates[0]!.key, fee.key, s!"same card transaction: {sig}", "high")
    else
      -- Corroborate with the fee percentage, which separates otherwise identical
      -- repeat purchases at the same merchant.
      let expected (p : Item) : Int :=
        if feeRateBp == 0 then 0 else divRoundLink (p.magnitude * feeRateBp) 10000
      let best := candidates.foldl (init := candidates[0]!) fun best p =>
        let err (x : Item) : Int :=
          let d := expected x - fee.magnitude
          if d < 0 then -d else d
        if err p < err best then p else best
      claimed := best.key :: claimed
      out := out.push (best.key, fee.key,
        s!"{sig}, one of {candidates.size} matching rows, chosen by fee percentage", "medium")
  return out

/-- Pairs fee rows with their parent purchases among staged rows. -/
def proposeFees (entries : Array StagedEntry) (feeWords : List String)
    (feeRateBp : Int) : Array MergeProposal :=
  (proposePairs ((entries.filter (fun e => e.state == "new")).map ofStaged) feeWords feeRateBp).map
    fun (parent, child, reason, confidence) =>
      { parent := ⟨parent⟩, child := ⟨child⟩, reason, confidence }

/-- Groups staged ids so that each proposal's pair ends up in one group. -/
def groupsOf (entries : Array StagedEntry) (proposals : Array MergeProposal) :
    Array (Array StagedId) := Id.run do
  let mut groups : Array (Array StagedId) := #[]
  let mut placed : List String := []
  for p in proposals do
    groups := groups.push #[p.parent, p.child]
    placed := p.parent.val :: p.child.val :: placed
  for e in entries do
    if e.state == "new" && !placed.contains e.id.val then
      groups := groups.push #[e.id]
  return groups

/--
Promotes staged rows a group at a time, merging each group into one
transaction. A group of one behaves exactly like an ordinary promotion.
-/
def promoteGroups (ctx : Ctx) (groups : Array (Array StagedId)) (actor : String) :
    IO (Array TxId × Nat) := do
  let mut created : Array TxId := #[]
  let mut merges := 0
  for group in groups do
    let ids ← Imports.promote ctx group actor
    if ids.size > 1 then
      let merged ← Txns.merge ctx ids actor
      created := created.push merged.id
      merges := merges + 1
    else
      created := created ++ ids
  return (created, merges)

/-- The profile a batch was imported with. -/
def profileOf (ctx : Ctx) (batch : BatchId) : IO (Option CsvProfile) := do
  let batches ← Imports.listBatches ctx
  let name := ((batches.find? (fun b => b.id == batch)).map (·.profile)).getD ""
  let profiles ← CsvProfile.loadAll (ctx.cfg.dataDir / "profiles")
  return profiles.find? (fun p => p.name == name)

/-- The proposals for a batch, using the profile the batch was imported with. -/
def proposalsFor (ctx : Ctx) (batch : BatchId) : IO (Array MergeProposal) := do
  match ← profileOf ctx batch with
  | some p =>
    let entries ← Imports.listStaged ctx (some batch) (some "new")
    return proposeFees entries p.feeWords p.feeRateBp
  | none => return #[]

/--
Promotes a batch, combining each proposed pair into one transaction and routing
fee rows to the profile's fee account so they stay visible.
-/
def promoteAuto (ctx : Ctx) (batch : BatchId) (only : Option (Array String))
    (actor : String) : IO (Array TxId × Nat) := do
  let entries ← Imports.listStaged ctx (some batch) (some "new")
  let chosen :=
    match only with
    | some xs => entries.filter (fun e => xs.contains e.id.val)
    | none => entries
  let proposals := (← proposalsFor ctx batch).filter fun p =>
    chosen.any (·.id == p.parent) && chosen.any (·.id == p.child)
  match ← profileOf ctx batch with
  | some prof =>
    if !prof.feeAccount.isEmpty then
      for p in proposals do
        Imports.suggest ctx p.child prof.feeAccount
  | none => pure ()
  promoteGroups ctx (groupsOf chosen proposals) actor

/--
Marks every posting that came from a fee line with the `fee` tag.

The staged rows keep their fingerprints for the life of the store, and a
posting records the fingerprint it came from, so this works retroactively on
transactions imported before tagging existed — and stays correct after a fee
has been moved into a receivable.

Tagging a leg is rewriting the transaction it belongs to, so the rewrites are
gathered first and committed together. That is not only tidiness: one
transaction can be reached twice, once for the account its fee now sits in and
once for the bank line it came from, and the second reading has to see what the
first decided.
-/
def tagFeePostings (ctx : Ctx) : IO Nat := do
  let batches ← Imports.listBatches ctx
  let profiles ← CsvProfile.loadAll (ctx.cfg.dataDir / "profiles")
  let s ← ctx.state.get
  -- Anything sitting in a fee account is a fee, whatever it was imported by.
  -- This is what catches transactions booked before postings had origins, and
  -- it is safe to repeat: the tag survives the posting being moved elsewhere.
  let feeAccounts := (s.accountsSorted.filter fun a =>
    Account.isUnder a.name "Expenses.Fees").map (·.id)
  let untagged (p : Posting) : Bool := p.tag != some "fee"
  let mut rewritten : Std.HashMap String Transaction := {}
  let mut tagged := 0
  for t in s.ledger do
    let hits := (t.postings.filter fun p => feeAccounts.contains p.account && untagged p).length
    if hits > 0 then
      rewritten := rewritten.insert t.id.val
        { t with postings := t.postings.map fun p =>
            if feeAccounts.contains p.account then { p with tag := some "fee" } else p }
      tagged := tagged + hits
  for batch in batches do
    let some prof := profiles.find? (fun p => p.name == batch.profile) | continue
    if prof.feeWords.isEmpty then continue
    let entries ← Imports.listStaged ctx (some batch.id) none
    for e in entries do
      if !isFee prof.feeWords (ofStaged e) then continue
      let mut hits := 0
      for t in s.ledger do
        let current := rewritten.getD t.id.val t
        let n := (current.postings.filter fun p =>
          p.origin == some e.fingerprint && untagged p).length
        if n > 0 then
          rewritten := rewritten.insert t.id.val
            { current with postings := current.postings.map fun p =>
                if p.origin == some e.fingerprint then { p with tag := some "fee" } else p }
          hits := hits + n
      if hits > 0 then
        tagged := tagged + hits
      else
        -- Transactions promoted before postings carried origins. The staged row
        -- still records which transaction it became, and within that
        -- transaction the fee is the counter leg of exactly its amount — which
        -- finds it even after the leg has been recategorised by hand.
        let some txn := e.txnId | continue
        let some original := s.txn? txn | continue
        if original.state != .posted then continue
        let current := rewritten.getD txn.val original
        let counter := -e.raw.amount.minor
        let some i := current.postings.findIdx? (fun p => p.amount.minor == counter && untagged p)
          | continue
        let some leg := current.postings[i]? | continue
        rewritten := rewritten.insert txn.val
          { current with postings := current.postings.set i { leg with tag := some "fee" } }
        tagged := tagged + 1
  let ops := (sortedValues rewritten).map Op.putTransaction
  if !ops.isEmpty then
    discard <| ctx.commit "system" ops (kind := "categorise")
  return tagged

/-! ## Linking transactions that are already in the ledger

The same pairing, applied after the fact. Each transaction is matched using the
profile of the batch it was imported from, so two banks' fee conventions cannot
be confused with one another.
-/

/-- A proposal to merge two transactions already in the ledger. -/
structure TxnPair where
  parent : Transaction
  child : Transaction
  reason : String
  confidence : String

/-- Finds fee transactions that belong with an existing purchase. -/
def proposeTxnPairs (ctx : Ctx) : IO (Array TxnPair) := do
  let batches ← Imports.listBatches ctx
  let profiles ← CsvProfile.loadAll (ctx.cfg.dataDir / "profiles")
  let txns ← Txns.list ctx .all {} 1000000
  -- Anything already built from several bank lines is left alone.
  let candidates := txns.filter (fun t => t.origins.length ≤ 1)
  let profileNameOf (t : Transaction) : String :=
    match t.source with
    | .imported batch _ =>
      ((batches.find? (fun b => b.id == batch)).map (·.profile)).getD ""
    | _ => ""
  let mut out : Array TxnPair := #[]
  for prof in profiles do
    if prof.feeWords.isEmpty then continue
    let mine := candidates.filter (fun t => profileNameOf t == prof.name)
    if mine.isEmpty then continue
    let pairs := proposePairs (mine.map ofTxn) prof.feeWords prof.feeRateBp
    for (parent, child, reason, confidence) in pairs do
      match mine.find? (fun t => t.id.val == parent), mine.find? (fun t => t.id.val == child) with
      | some p, some c => out := out.push { parent := p, child := c, reason, confidence }
      | _, _ => pure ()
  return out

/--
Merges every proposed pair, routing the fee leg to its profile's fee account so
it stops hiding in `Unclassified`. Returns the transactions created.
-/
def linkTxnPairs (ctx : Ctx) (pairs : Array TxnPair) (actor : String) : IO (Array TxId) := do
  let batches ← Imports.listBatches ctx
  let profiles ← CsvProfile.loadAll (ctx.cfg.dataDir / "profiles")
  let mut created : Array TxId := #[]
  for pair in pairs do
    -- Rebook the fee before merging, so the merged entry shows it as a fee.
    let profName :=
      match pair.child.source with
      | .imported batch _ => ((batches.find? (fun b => b.id == batch)).map (·.profile)).getD ""
      | _ => ""
    match profiles.find? (fun p => p.name == profName) with
    | some prof =>
      if !prof.feeAccount.isEmpty then
        let feeAcc ← Accounts.ensure ctx prof.feeAccount
        let rebooked : Transaction :=
          { pair.child with postings := pair.child.postings.map fun p =>
              if p.amount.minor > 0 then { p with account := feeAcc.id } else p }
        match rebooked.validate with
        | .ok bt => Txns.put ctx bt actor "categorise"
        | .error _ => pure ()
    | none => pure ()
    let merged ← Txns.merge ctx #[pair.parent.id, pair.child.id] actor
    created := created.push merged.id
  return created

end Link

namespace Rules

/-- What a rule would do, or did, to one transaction. -/
structure Applied where
  txn : Transaction
  rule : String
  account : String
  labels : List String

/--
Runs the rules over transactions already in the ledger, rebooking the leg that
is still sitting in an `Unclassified` account.

Only that leg is touched: a transaction someone has already categorised by hand
is left alone, so re-running this is safe and idempotent. With `commit := false`
nothing is written and the caller can show what would happen.
-/
def applyToLedger (ctx : Ctx) (actor : String) (commit : Bool) : IO (Array Applied) := do
  let accounts ← Accounts.list ctx
  let labels ← Labels.list ctx
  let parties ← Parties.list ctx
  let env := Filter.Env.ofLists accounts.toList labels.toList parties.toList
  let rules ← Rules.list ctx
  let unclassified := (accounts.filter fun a =>
    Account.isUnder a.name "Expenses.Unclassified" ||
      Account.isUnder a.name "Income.Unclassified").map (·.id)
  let txns ← Txns.list ctx .all {} 1000000
  let mut out : Array Applied := #[]
  for t in txns do
    if !t.postings.any (fun p => unclassified.contains p.account) then continue
    let some rule := rules.find? (fun r => r.filter.eval env t) | continue
    let some target := rule.setAccount | continue
    let acc ← Accounts.ensure ctx target
    let labelIds ← rule.addLabels.mapM fun n => do return (← Labels.ensure ctx n).id
    let moved : Transaction :=
      { t with
        postings := t.postings.map fun p =>
          if unclassified.contains p.account then { p with account := acc.id } else p
        labels := t.labels ++ labelIds.filter (fun l => !t.labels.contains l) }
    match moved.validate with
    | .error _ => continue
    | .ok bt =>
      if commit then Txns.put ctx bt actor "rule"
      out := out.push { txn := bt.val, rule := rule.name, account := target,
                        labels := rule.addLabels }
  return out

end Rules

end Resources
