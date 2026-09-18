import Resources.Core.Budgets
import Resources.Core.Claim
import Resources.Core.Event

/-!
# Applying an operation

`applyOp` is the whole of what this ledger can do to itself: one pure function
from a state and an operation to the next state, or to the sentence explaining
why not. The store applies the very same function and then projects the
`Change`s it returns into SQL, so there is one implementation of "what a split
does" rather than one per caller.

Three rules run through every case below.

*Nothing balances by accident.* Every transaction written from here goes through
`Transaction.validate`, and the `Balanced` proof it hands back is what the write
is made from. An intent that would unbalance the ledger is refused with what is
missing, never silently repaired.

*Nothing is implied.* An operation returns the full new value of every entity it
touched — including the transactions a merge rewrote and the rules an account
merge repointed — so a reader of the changes never has to re-derive what the
operation meant.

*Nobody writes where they may not.* Every operation has a rule, `Op.rights` says
which, and `checkRights` enforces it at the top of this function before anything
is read for effect. That is the shape the file was missing: about half the
operations used to read neither the author nor the realm, so a viewer of any
realm could delete any transaction in the ledger, rewrite any account, take over
the whole state with a snapshot, or write themselves into somebody's private
realm. The rule is now a total function, which means an operation cannot be added
without somebody deciding who may use it.

*Nothing is written outside the realm the part names.* Every entity the ledger
keeps says which realm it is in, and `ofThisRealm` is the one line that enforces
it: an operation about an entry of another realm is refused, and a new entry is
created in the realm the part names. Eight kinds of entry used to have no realm
at all — labels, people, groups, trips, rules, import batches, stored receipts
and the invoice counter — so "an admin of the part's realm" reached across every
realm a reader could open. That is a right anybody can manufacture, because
anybody may create a realm, make themselves its admin and hand you a key to it;
from inside it they could delete a label out of every transaction you hold,
rewrite any person in your books, install the rules that drive what your imports
file where, forget your receipts and move your invoice numbering.

*A snapshot is where a log starts, not something a part may say.* `applyOp`
refuses one wherever it appears, including on an empty ledger, and `replay`
reads the genesis off the first event of the log instead. The section at the
bottom of this file says why the old rule — "a state nothing has happened in" —
was a question about the reader rather than about the log.

What the rule cannot decide is decided in the case that knows about it: whether
the author may write the *legs* a transaction carries (`checkPostings` and
`checkOwnLegs`, leg by leg, against `canPostLeg`), whether they may speak about a
claim (`checkClaimParty` — the creditor, or an admin), and whether they may say
what a receipt contains (`checkReceipt`). `payClaim` is the one operation that
writes postings without `canPost`, and it is not an exception but a different
reading: the accounts it writes are the two the claim already names, so who may
perform a claim is a question about the claim.

*Nothing is unbounded.* Every list, every string and every bare number an
operation carries is checked against `checkBounds` before any of it is used. A
reader applies what an author sends it, and a quantity of a thousand million on
one receipt line used to make every node and every browser replaying the log
allocate a list of that length. The three numbers with no type over them — a
date's year, a commodity's exponent and the count of minor units in an amount —
are bounded here too, and again in the decoder, because an exponent of ten
million is six bytes to send and a bignum with three million digits to render.

Three operations a member may perform about themselves alone: `addMember` for
their own record, `grant` for their own viewer role, and `putParty` for the
party their own spending lands on. The first two are what a person who joined a
realm through an invite writes, because the admin who invited them was a link in
a browser rather than a node composing events, and without them nothing in the
log would say the newcomer is there at all. The attestation is not taken on
trust: a part for a realm reaches a reader only because the sequencer accepted
it, and it accepted it only from somebody it already holds a grant for in that
realm. So the log is repeating a decision that has been made, and it repeats the
weakest form of it — a view of *this* realm, a member record whose party is
theirs alone, and a purse named after them, of the kind money is held in, with
nobody else on it. Everything else a self-`grant` carries is ignored, because
the door is open to any member about themselves and it used to write the name,
the kind and the posters verbatim: a viewer could mint an account per grant, of
any name, in a realm they merely read, and post to it without limit.
-/

namespace Resources

/-! ## Reading what an operation names -/

/-- The account with this id, or the error naming what is missing. -/
def accountOf (s : State) (id : AccountId) : Except String Account :=
  match s.account? id with
  | some a => .ok a
  | none => .error s!"no such account: {id.val}"

/-- The transaction with this id, or the error naming what is missing. -/
def txnOf (s : State) (id : TxId) : Except String Transaction :=
  match s.txn? id with
  | some t => .ok t
  | none => .error s!"no such transaction: {id.val}"

/-- The import fingerprint a transaction carries, when it came off a bank line. -/
def fingerprintOf (t : Transaction) : Option String :=
  match t.source with
  | .imported _ fp => some fp
  | _ => none

/-! ## Who may do this

`Op.rights` says what an operation asks of its author before anything else is
looked at, and `checkRights` is where that is enforced — once, at the top of
`applyOp`, for every operation there is. Nothing below it can be reached without
passing through it, which is the point: an operation added without a rule does
not compile.

Two things it cannot decide, and they are checked in the case that knows about
them. Whether the author may write the *legs* a transaction carries is a
question about accounts, so it is `checkPostings`; and whether they may speak
about a claim, a budget or a receipt is a question about that entity.
-/

/-- Whether a member may speak for a realm, as an admin or about themselves alone. -/
def checkRights (s : State) (author : MemberId) (realm : RealmId) (op : Op) :
    Except String Unit := do
  match op with
  -- A snapshot is not an operation. It is what a log *starts from*, and where a
  -- log starts is a fact about the reader's position in the order rather than
  -- about the state the reader has managed to fold: a client that holds one
  -- generation's key skips everything written under every other one and arrives
  -- at a fresh-looking state part way along, from which one snapshot by anybody
  -- still in the realm replaced the whole of it. So no part may carry one, ever,
  -- and `Core.replay` reads the genesis off position 1 instead.
  | .snapshot _ =>
    throw "a snapshot is where a log starts, not something a part may say"
  -- A grant, a revoke, a role and a rotation each name a realm of their own. The
  -- only evidence anybody has that the author may speak at all is the grant the
  -- sequencer holds for them on the realm the *part* names, so that is the only
  -- realm they may speak about: a viewer of one realm writing themselves into
  -- somebody else's was a door with nothing behind it.
  | .grant target .. | .revoke target _ | .setRole target .. | .rotateRealmKey target =>
    if target != realm then
      throw "a part can only change the realm it names"
  | _ => pure ()
  match op.rights with
  | .known =>
    if (s.member? author).isNone then
      throw s!"{author.val} is not a member of this ledger"
  | .attest =>
    -- The self door, and the whole of it: your own record, your own view, or the
    -- party your own spending lands on.
    let selfDoor : Bool := match op with
      | .addMember m => m.id == author
      | .grant _ member role _ => member == author && role == .viewer
      | .putParty p => (s.member? author).map (·.party) == some p.id
      | _ => false
    if !(s.canAdminister author realm || selfDoor) then
      throw "only an admin of that realm may do that for somebody else"
  | .member =>
    if !s.isMemberOf author realm then
      throw "you are not in that realm"
  | .admin =>
    if !s.canAdminister author realm then
      throw "only an admin of that realm may do that"

/-! ## How much of it

Every list and every string an operation carries is bounded. A reader applies
what an author sends it, and one short event naming a quantity of a thousand
million used to make every node and every browser replaying the log allocate a
list of that length. The numbers are far above anything a person writes and far
below anything that costs a reader more than the event itself.

Three of them are not lengths at all but values a computation is done with: the
year of a date, the exponent of a commodity and the count of minor units in an
amount. They are bounded in `Core/Event.lean` beside the lengths, refused here by
`boundedDate`, `boundedCommodity` and `boundedAmount`, and refused again by the
decoder — because an operation can arrive as bytes as well as as JSON, and the
two doors are not the same door.
-/

/-- Refuses an identifier or a name longer than anything a person writes. -/
def boundedName (what v : String) : Except String Unit :=
  if v.length > maxIdLength then .error s!"{what} is longer than {maxIdLength} characters"
  else .ok ()

/-- Refuses free text longer than anything a person writes. -/
def boundedText (what v : String) : Except String Unit :=
  if v.length > maxTextLength then .error s!"{what} is longer than {maxTextLength} characters"
  else .ok ()

/-- Refuses an optional name that is too long. -/
def boundedName? (what : String) (v : Option String) : Except String Unit :=
  match v with | some x => boundedName what x | none => .ok ()

/-- Refuses an optional text that is too long. -/
def boundedText? (what : String) (v : Option String) : Except String Unit :=
  match v with | some x => boundedText what x | none => .ok ()

/--
Refuses a date outside the years the ledger will take.

A `Date` is Std's `PlainDate`, so its month and its day are already a date: the
type will not hold a thirteenth month and the proof it carries will not hold the
thirty-first of February. Only the year is an `Int` with nothing over it, which
is why only the year is asked about here — and why a port, whose date is three
numbers, has to ask about all three.
-/
def boundedDate (what : String) (d : Date) : Except String Unit :=
  if d.inRange then .ok ()
  else .error s!"{what} names the year {d.year}, and a year has to be between {minYear} \
                 and {maxYear}"

/-- Refuses an optional date that is out of range. -/
def boundedDate? (what : String) (d : Option Date) : Except String Unit :=
  match d with | some x => boundedDate what x | none => .ok ()

/--
Refuses a commodity nothing can compute in.

`Commodity.scale` is `10 ^ exponent`, so an exponent is the one field in an
operation that turns six bytes on the wire into a number with millions of
digits. Eighteen places is more than any currency has ever had.
-/
def boundedCommodity (c : Commodity) : Except String Unit := do
  boundedName "a commodity code" c.code
  if c.exponent > maxExponent then
    .error s!"a commodity has at most {maxExponent} decimal places, and {c.code} claims \
              {c.exponent}"

/-- Refuses an amount whose commodity is one nothing can compute in. -/
def boundedAmount (a : Amount) : Except String Unit := boundedCommodity a.commodity

/-- Refuses a filter comparing against a date or an amount that is out of range. -/
def boundedFilter (what : String) (f : Filter) : Except String Unit :=
  if f.inRange then .ok ()
  else .error s!"{what} names a date or an amount outside what this ledger carries"

/-- Refuses a list longer than an operation may carry. -/
def boundedList {α : Type} (what : String) (xs : List α) (limit : Nat := maxParts) :
    Except String Unit :=
  if xs.length > limit then .error s!"{what}: at most {limit} are allowed" else .ok ()

/-- The lines printed on a receipt, bounded, quantities included. -/
def boundedItems (items : List LineItem) : Except String Unit := do
  boundedList "a receipt's lines" items maxLines
  for i in items do
    boundedText "a line's description" i.description
    boundedAmount i.amount
    match i.qty with
    | some q => if q.natAbs > maxQty then throw s!"a line covers at most {maxQty} units"
    | none => pure ()

/-- Everything a transaction carries, bounded. -/
def boundedTxn (t : Transaction) : Except String Unit := do
  boundedList "a transaction's postings" t.postings maxPostings
  boundedName "a transaction id" t.id.val
  boundedDate "a transaction's date" t.date
  boundedText "a narration" t.narration
  boundedText? "a payee" t.payee
  boundedList "a transaction's labels" t.labels
  boundedList "a transaction's attachments" t.attachments
  match t.items with
  | some its => boundedItems its
  | none => pure ()
  for l in t.labels do
    boundedName "a label id" l.val
  for a in t.attachments do
    boundedName "an attachment hash" a
  for p in t.postings do
    boundedName "an account id" p.account.val
    boundedAmount p.amount
    boundedText? "a posting note" p.note
    boundedName? "a posting origin" p.origin
    boundedName? "a posting tag" p.tag

/-- Everything an account carries, bounded. -/
def boundedAccount (a : Account) : Except String Unit := do
  boundedName "an account id" a.id.val
  boundedName "an account name" a.name
  boundedName? "an iban" a.iban
  boundedText? "an account note" a.note
  boundedList "an account's posters" a.posters
  boundedDate? "an account's closing date" a.closedOn
  match a.commodity with
  | some c => boundedCommodity c
  | none => pure ()

/-- The people a budget is divided among, bounded, weights included. -/
def boundedParticipants (among : List Participant) : Except String Unit := do
  boundedList "a budget's participants" among maxParticipants
  for p in among do
    boundedName "a participant's account" p.account
    boundedName "a participant's name" p.name
    if p.weight < 1 || p.weight > maxWeight then
      throw s!"a share's weight has to be between 1 and {maxWeight}"
  -- The weights add up to how many parts `shareOut` cuts the money into, so the
  -- sum is bounded as well as each of them.
  if (among.map (fun p => max p.weight 1)).sum > maxParts then
    throw s!"the weights of a division add up to more than {maxParts}"

/--
Everything an operation carries, bounded: the one place a size is refused.

Every case that names a date, a commodity or an amount asks about it, including
the ones buried inside a transaction, an account, an invoice line, a receipt line
or a rule's filter. What an operation does not reach is a `snapshot`, which
carries a whole state and is refused before its bounds are ever asked about.
-/
def checkBounds : Op → Except String Unit
  | .createRealm r => do
    boundedName "a realm id" r.id.val
    boundedName "a realm name" r.name
    boundedList "a realm's members" r.members
  | .putAccount a => boundedAccount a
  | .mergeAccounts f i => do
    boundedName "an account id" f.val
    boundedName "an account id" i.val
  | .deleteAccount i => boundedName "an account id" i.val
  | .setAccountRights i ps => do
    boundedName "an account id" i.val
    boundedList "an account's posters" ps
  | .setAccountOwner i o => do
    boundedName "an account id" i.val
    boundedName "a party id" o.val
  | .putLabel l => do
    boundedName "a label id" l.id.val
    boundedName "a label name" l.name
    boundedName? "a colour" l.colour
  | .deleteLabel i => boundedName "a label id" i.val
  | .putParty p => do
    boundedName "a party id" p.id.val
    boundedName "a party name" p.name
    boundedName? "an iban" p.iban
    boundedName? "an email" p.email
    boundedText? "a party note" p.note
  | .putGroup g => do
    boundedName "a group name" g.name
    boundedList "a group's members" g.members
    for m in g.members do boundedName "a group member" m
  | .deleteGroup n => boundedName "a group name" n
  | .putTrip t => do
    boundedName "a trip id" t.id
    boundedName "a trip name" t.name
    boundedName "a payer" t.payer
    boundedText? "a trip note" t.note
    boundedDate "a trip's first day" t.starts
    boundedDate "a trip's last day" t.ends
  | .deleteTrip n => boundedName "a trip name" n
  | .putRule r => do
    boundedName "a rule id" r.id.val
    boundedName "a rule name" r.name
    boundedText "a filter" r.filterSrc
    boundedFilter "a rule's filter" r.filter
    boundedName? "an account name" r.setAccount
    boundedName? "a party" r.setParty
    boundedList "a rule's labels" r.addLabels
    for l in r.addLabels do boundedName "a label" l
  | .deleteRule n => boundedName "a rule name" n
  | .putTransaction t | .raiseClaim t | .contribute _ t => boundedTxn t
  | .deleteTransaction i => boundedName "a transaction id" i.val
  | .splitTransaction i ts _ => do
    boundedName "a transaction id" i.val
    boundedList "a split's targets" ts
    for a in ts do boundedName "an account id" a.val
  | .mergeTransactions ids n p nr c => do
    boundedList "a merge's sources" ids
    boundedName "a transaction id" n.val
    boundedText? "a payee" p
    boundedText? "a narration" nr
    boundedList "a merge's cancellations" c
  | .unmergeTransaction i ns => do
    boundedName "a transaction id" i.val
    boundedList "an unmerge's fresh ids" ns
  | .replaceTransaction i ps k => do
    boundedName "a transaction id" i.val
    boundedList "a division's parts" ps
    boundedName "a division's kind" k
    for t in ps do boundedTxn t
  | .divideByItems i gs ns => do
    boundedName "a transaction id" i.val
    boundedList "a division's groups" gs
    boundedList "a division's fresh ids" ns
    for g in gs do
      boundedName "an account id" g.into
      boundedList "a group's lines" g.items maxLines
      for sh in g.items do
        if sh.qty.getD 0 > maxQty then
          throw s!"a share covers at most {maxQty} units"
  | .resolveClaim i a sp => do
    boundedName "a transaction id" i.val
    boundedName "a transaction id" a.val
    boundedName "a transaction id" sp.val
  | .voidClaim i w => do
    boundedName "a transaction id" i.val
    match w with
    | some (a, t, d) => do
      boundedName "an account id" a.val
      boundedName "a transaction id" t.val
      boundedDate "a write-off's date" d
    | none => pure ()
  | .openBudget b a => do
    boundedName "a budget id" b.id.val
    boundedName "a budget name" b.name
    boundedText? "a budget note" b.note
    boundedAccount a
  | .setParticipants b among => do
    boundedName "a budget id" b.val
    boundedParticipants among
  | .allocate b among c d _ t cs l => do
    boundedName "a budget id" b.val
    boundedParticipants among
    boundedCommodity c
    boundedDate "a division's date" d
    boundedName "a transaction id" t.val
    boundedList "a division's claim ids" cs
    boundedName "a label id" l.val
  | .settle b c _ due cs l => do
    boundedName "a budget id" b.val
    boundedCommodity c
    boundedDate "a settlement's due date" due
    boundedList "a settlement's claim ids" cs
    boundedName "a label id" l.val
  | .closeBudget b among c _ d t cs l => do
    boundedName "a budget id" b.val
    boundedParticipants (among.getD [])
    boundedCommodity c
    boundedDate "a close's date" d
    boundedName "a transaction id" t.val
    boundedList "a close's claim ids" cs
    boundedName "a label id" l.val
  | .reopenBudget b | .deleteBudget b => boundedName "a budget id" b.val
  | .issueInvoice inv sources => do
    boundedName "an invoice id" inv.id.val
    boundedName "an invoice number" inv.number
    boundedName "a payer" inv.payerName
    boundedText? "an invoice note" inv.note
    boundedList "an invoice's lines" inv.lines
    boundedList "an invoice's sources" sources
    boundedDate "an invoice's issue date" inv.issued
    boundedDate "an invoice's due date" inv.due
    boundedCommodity inv.commodity
    for l in inv.lines do
      boundedText "a line's description" l.description
      boundedAmount l.unitPrice
  | .setInvoiceStatus i _ => boundedName "an invoice id" i.val
  | .settleInvoice i t => do
    boundedName "an invoice id" i.val
    boundedName "a transaction id" t.val
  | .deleteInvoice i => boundedName "an invoice id" i.val
  | .registerBlob f => do
    boundedName "a content hash" f.sha256
    boundedName "a media type" f.mime
    boundedName? "a file name" f.origName
    boundedName "a timestamp" f.createdAt
    boundedName? "a ciphertext hash" f.cipherHash
    boundedText? "a wrapped key" f.wrappedKey
  | .attach t sha | .detach t sha => do
    boundedName "a transaction id" t.val
    boundedName "a content hash" sha
  | .recordExtraction sha e => do
    boundedName "a content hash" sha
    boundedName? "a merchant" e.merchant
    boundedText "the text read off a receipt" e.rawText
    boundedName "an extractor" e.extractor
    boundedDate? "a receipt's date" e.date
    match e.total with
    | some a => boundedAmount a
    | none => pure ()
    boundedItems e.items
  | .setReceiptLines sha items => do
    boundedName "a content hash" sha
    boundedItems items
  | .forgetBlob sha => boundedName "a content hash" sha
  | .recordImportBatch b => do
    boundedName "a batch id" b.id.val
    boundedName "a profile" b.profile
    boundedName? "a file name" b.filename
    boundedName "a timestamp" b.stamp
  | .addMember m => do
    boundedName "a member id" m.id.val
    boundedName "a member name" m.name
    boundedName "a party id" m.party.val
  | .removeMember i => boundedName "a member id" i.val
  | .grant r m _ b => do
    boundedName "a realm id" r.val
    boundedName "a member id" m.val
    boundedAccount b
  | .revoke r m | .setRole r m _ => do
    boundedName "a realm id" r.val
    boundedName "a member id" m.val
  | .rotateRealmKey r => boundedName "a realm id" r.val
  | .snapshot _ => .ok ()
  | .payClaim c p d => do
    boundedName "a transaction id" c.val
    boundedName "a transaction id" p.val
    boundedDate "a payment's date" d

/-! ## Which realm an entry belongs to

Every entity the ledger keeps now says which realm it is in, and the rule is one
line: a part may only speak about an entry of the realm it names. It used to be
that eight kinds of entry — labels, parties, groups, trips, rules, import
batches, stored receipts, and the invoice counter — had no realm at all, so
"an admin of the part's realm" reached across every realm a reader could open.
Anybody can manufacture that right: they create a realm, make themselves its
admin, hand you a key, and from inside it delete a label out of every
transaction you hold, rewrite any person in your books, install rules that drive
what your imports file where, and forget your receipts.

`ofThisRealm` is that rule for an entry that already exists. A new entry is
created in the realm the part names, which is the other half and is written at
each `put` below.
-/

/-- Refuses an entry that belongs to another realm. -/
def ofThisRealm (what : String) (realm : RealmId) (entry : RealmId) : Except String Unit :=
  if entry != realm then .error s!"{what} is not in this realm" else .ok ()

/--
The same, asked of an entry that may not be there yet.

A key nothing is filed under is nobody's, so a `put` that names one is creating
it here rather than reaching into somewhere else.
-/
def ofThisRealm? {α : Type} (name : α → String) (of : α → RealmId) (realm : RealmId) :
    Option α → Except String Unit
  | some x => ofThisRealm (name x) realm (of x)
  | none => .ok ()

/-! ## Writing -/

/--
Checks that these postings may be written here.

Three things have to hold of every leg, and they are the reason a part can be
applied on its own: the account exists and belongs to this realm, it is open,
and the author may post to it.

`allowed` names the accounts the caller has already established a right to,
which is how `payClaim` writes the two legs of a claim between purses neither of
which is the author's alone. It never excuses the other two checks: an account
named there still has to exist, be open, and be in this realm.
-/
def checkPostings (s : State) (author : MemberId) (realm : RealmId)
    (ps : List Posting) (allowed : List AccountId := []) : Except String Unit := do
  for p in ps do
    let a ← accountOf s p.account
    if a.realm != realm then
      throw s!"{a.name} is not in this realm"
    if a.closedOn.isSome then
      throw s!"{a.name} is closed; it cannot take new postings"
    if !(allowed.contains p.account || s.canPostLeg author a p.amount.minor) then
      throw s!"you may not post to {a.name}"

/--
Checks that these legs are this realm's and that the author may write them.

The check `checkPostings` makes about a part it is *writing*, asked about legs
that are already there: a transaction is not somebody's to retire, to divide or
to hang a receipt on unless every leg of it is in the realm the part names and
every one of them is a leg they could have written themselves. Closure is left
out on purpose — an account closed since is still an account whose entries its
own people may tidy up.
-/
def checkOwnLegs (s : State) (author : MemberId) (realm : RealmId) (ps : List Posting) :
    Except String Unit := do
  for p in ps do
    let a ← accountOf s p.account
    if a.realm != realm then
      throw s!"{a.name} is not in this realm"
    if !s.canPostLeg author a p.amount.minor then
      throw s!"you may not post to {a.name}"

/--
The guard a rewrite makes about the transaction it is replacing.

A `putTransaction` that names an id the ledger already has is a rewrite, and the
legs it is rewriting are this realm's. There have to be some — a part with no leg
here has nothing of this realm's to replace, and writing one anyway was how the
metadata of any transaction in the ledger, in any realm, could be rewritten from
a realm that had never seen it — and they have to be legs this author could have
written.
-/
def putGuard (s : State) (author : MemberId) (realm : RealmId) (t : Transaction) :
    Except String Unit := do
  match s.txn? t.id with
  | some old =>
    -- A claim is changed by a claim verb. `resolveClaim` and `voidClaim` both ask
    -- who the claim is owed to; plain `putTransaction` asked nothing about what
    -- it was replacing, so an author who could post both legs of a stored claim
    -- could rewrite it as a posted transaction — which takes it out of the
    -- settlement arithmetic and puts its amounts into every balance — without
    -- going through either verb. The same door reached a settled claim, and so
    -- booked money that had already moved a second time.
    if old.state != .posted then
      throw s!"{t.id.val} is {old.state}; a claim is met or withdrawn, not overwritten"
    let here := old.postings.filter (fun p => s.realmOf p.account == some realm)
    if here.isEmpty then
      throw "that transaction has no leg in this realm"
    checkOwnLegs s author realm here
  | none => pure ()

/-- Puts a transaction into state, as the full new value of that entity. -/
def written (s : State) (t : Transaction) : State × Change :=
  ({ s with txns := s.txns.insert t.id.val t }, .txn t)

/-- Takes a transaction out of state. -/
def removed (s : State) (id : TxId) : State × Change :=
  ({ s with txns := s.txns.erase id.val }, .txnDeleted id)

/--
Writes one realm's legs of a transaction.

The legs of `t.id` that sit in this realm are replaced by `t.postings` and the
metadata is replaced wholesale; legs in other realms are kept, because they
belong to a part this author may not even be able to read. The part balances on
its own or it is refused, and an entry whose import fingerprint has been seen
before is refused too — that refusal is what makes re-importing an overlapping
date range a no-op rather than a duplicate.
-/
def putTxn (s : State) (author : MemberId) (realm : RealmId) (t : Transaction)
    (allowed : List AccountId := []) : Except String (State × List Change) := do
  checkPostings s author realm t.postings allowed
  let checked ← t.validate
  let t := checked.val
  -- A claim is exactly two legs: one account owes and one is owed, and
  -- `Pendings.amount` reads what is asked for off the positive one. A pending
  -- transaction with three balanced legs would be ambiguous about all three,
  -- so it is refused here rather than in `raiseClaim` alone — this is the one
  -- door every transaction comes through.
  if t.state == .pending && t.postings.length != 2 then
    throw "a claim is exactly two legs"
  let old := s.txn? t.id
  -- Other realms' legs are none of this part's business, so they stay.
  let kept := ((old.map (·.postings)).getD []).filter
    (fun p => s.realmOf p.account != some realm)
  -- The bound again, on what is about to be written rather than on what the
  -- operation carried. `checkBounds` refuses a *submitted* transaction of more
  -- than `maxPostings` legs; it says nothing about one an intent *computed*, and
  -- a split across a hundred thousand targets, a merge of a hundred thousand
  -- sources or a division into a hundred thousand parts each produce
  -- transactions far larger than anything anybody sent. This is the one door
  -- every written transaction comes through, so it is the one place a result can
  -- be bounded at all.
  if (kept ++ t.postings).length > maxPostings then
    throw s!"that would write a transaction of {(kept ++ t.postings).length} postings, \
             and at most {maxPostings} are allowed"
  let whole : Transaction := { t with postings := kept ++ t.postings }
  let mut st := s
  let mut changes : List Change := []
  match fingerprintOf t with
  | some fp =>
    if st.fingerprints.contains fp && (old.bind fingerprintOf) != some fp then
      throw s!"this bank line has already been imported: {fp}"
    if !st.fingerprints.contains fp then
      st := { st with fingerprints := st.fingerprints.insert fp }
      changes := changes ++ [.fingerprint fp]
  | none => pure ()
  let (st', change) := written st whole
  return (st', changes ++ [change])

/--
Replaces a transaction with the parts it was divided into.

Dividing is not unmerging: the parts may book their spending wherever they
belong, which is the whole point, so what they own is allowed to differ from
what the original said. What may not differ is the funding. Together the parts
must take exactly what the original took, out of exactly the accounts it took it
from — otherwise a division could quietly invent money, and the ledger would
still balance while being wrong.
-/
def replaceParts (s : State) (author : MemberId) (realm : RealmId) (id : TxId)
    (parts : List Transaction) : Except String (State × List Change) := do
  let t ← txnOf s id
  checkOwnLegs s author realm t.postings
  if parts.isEmpty then
    throw "a division has to leave something behind"
  for part in parts do
    -- A part carrying the original's id would be written and then deleted again
    -- by the retirement below, taking its money out of the ledger silently.
    if part.id == id then
      throw "a part cannot reuse the id of the transaction being divided"
    match part.validate with
    | .error e => throw s!"a part does not balance: {e}"
    | .ok _ => pure ()
  let codes := (t.commodityCodes ++ parts.flatMap (·.commodityCodes)).eraseDups
  let accounts := ((t.postings ++ parts.flatMap (·.postings)).map (·.account)).eraseDups
  for c in codes do
    for a in accounts do
      let before := t.netIn a c
      let after := (parts.map (fun p => p.netIn a c)).sum
      if (before < 0 || after < 0) && before != after then
        throw s!"the parts do not take the same money out of {a.val} as the original did"
  let (s1, gone) := removed s id
  let mut st := s1
  let mut changes : List Change := [gone]
  for part in parts do
    let (st', cs) ← putTxn st author realm part
    st := st'
    changes := changes ++ cs
  return (st, changes)

/-! ## Budgets

Reading a budget is `Core/Budgets.lean`; what is here is only the writing. A
division and a settlement are computed there, in full, before a single posting
is written — so an operation that cannot be carried out says so and leaves the
state exactly as it found it.
-/

/-- The budget with this id, or the error naming what is missing. -/
def budgetOf (s : State) (id : BudgetId) : Except String BudgetState :=
  match s.budget? id with
  | some b => .ok b
  | none => .error s!"no such budget: {id.val}"

/--
Checks that this author may decide things about a budget.

A budget belongs to one realm, written down when it was opened, and the people
who may say what happens to it are the ones who administer that realm. The part
has to name it too: a decision about a budget reaches the people who share it
only if it is written under the key they hold.
-/
def checkBudget (s : State) (author : MemberId) (realm : RealmId) (bs : BudgetState) :
    Except String Unit := do
  if bs.realm != realm then
    throw s!"{bs.budget.shortName} is not in this realm"
  if !s.canAdminister author bs.realm then
    throw s!"only an admin of that realm may decide about {bs.budget.shortName}"

/--
Records the label a budget's claims are being raised under.

`openBudget` pins it when the ledger already has a label of the budget's name;
otherwise the first division or settlement that raises claims says which label
they carry, and that is the one every later reading of the budget's claims uses.
-/
def pinLabel (s : State) (id : BudgetId) (label : LabelId) : State × List Change :=
  match s.budget? id with
  | some bs =>
    if bs.label == label || label.val.isEmpty then (s, [])
    else
      let pinned := { bs with label }
      ({ s with budgets := s.budgets.insert id.val pinned }, [.budget pinned])
  | none => (s, [])

/-- Pinning a label writes a budget and touches nothing else. -/
theorem pinLabel_frame (s : State) (id : BudgetId) (label : LabelId) :
    (pinLabel s id label).1.txns = s.txns ∧ (pinLabel s id label).1.accounts = s.accounts := by
  simp only [pinLabel]
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/--
Whether this author may say what a stored receipt contains.

Three ways, and they are the same person read three ways: the member who filed
the bytes, somebody who may post the transaction the receipt is hanging on, or
an admin of the realm. What a receipt says is what `divideByItems` divides by,
so rewriting one is rewriting a division that has not happened yet.
-/
def checkReceipt (s : State) (author : MemberId) (realm : RealmId) (sha : String)
    (b : BlobState) : Except String Unit := do
  -- The realm first, and before the three doors below: the second of them used
  -- to ask nothing at all about where the bytes were filed, so whoever first
  -- registered a receipt kept the right to rewrite what it said from a part in
  -- any realm they held a key for — including after it had been attached to a
  -- transaction in a realm they could not otherwise touch.
  ofThisRealm "that receipt" realm b.realm
  if s.canAdminister author realm || b.registeredBy == author then
    return
  let attached := s.txnsSorted.filter (fun t => t.attachments.contains sha)
  let entitled := attached.any fun t =>
    !t.postings.isEmpty && (checkOwnLegs s author realm t.postings).toOption.isSome
  if !entitled then
    throw "only the member who registered that receipt, somebody who may post what it \
           belongs to, or an admin of that realm, may say what it contains"

/-- Whether this author may speak about a claim: the member it is owed to, or an admin. -/
def checkClaimParty (s : State) (author : MemberId) (realm : RealmId) (claim : Transaction)
    (verb : String) : Except String Unit := do
  if s.canAdminister author realm then
    return
  let some recv := Pendings.receiver? claim | throw "this claim has no receiving leg"
  let some acc := s.account? recv | throw "the receiving account is gone"
  if acc.bridgeOf != some author then
    throw s!"only the member who is owed, or an admin of that realm, may {verb} this claim"

/-- Writes every transaction an intent produced, in order. -/
def writeAll (s : State) (author : MemberId) (realm : RealmId) (ts : List Transaction)
    (allowed : List AccountId := []) : Except String (State × List Change) := do
  let mut st := s
  let mut changes : List Change := []
  for t in ts do
    let (st', cs) ← putTxn st author realm t allowed
    st := st'
    changes := changes ++ cs
  return (st, changes)

/-- Raises, revises and withdraws the claims that square a budget up. -/
def squareUp (s : State) (author : MemberId) (realm : RealmId) (b : Budget)
    (c : Commodity) (hub : Option PartyId) (due : Date) (claimIds : List TxId)
    (label : LabelId) : Except String (State × List Change) := do
  writeAll s author realm (← Budget.settlementOf b s c hub due claimIds label author.val)

/--
Divides what a budget holds and asks for what that leaves people owing.

Deciding and paying are two facts, so they are two entries. The claims are
raised here rather than by a second operation because the moment the division is
known is the moment the arithmetic behind them is cheapest to get right, and
because a division nobody has been asked to settle is a worklist entry that
looks finished.
-/
def divideUp (s : State) (author : MemberId) (realm : RealmId) (b : Budget)
    (among : List Participant) (c : Commodity) (date : Date) (txnId : TxId)
    (hub : Option PartyId) (claimIds : List TxId) (label : LabelId) :
    Except String (State × List Change × Bool) := do
  match ← Budget.divisionOf b s realm among c date txnId author.val with
  | none => return (s, [], false)
  | some t =>
    let (st, cs) ← putTxn s author realm t
    let (st', cs') ← squareUp st author realm b c hub date claimIds label
    return (st', cs ++ cs', true)

/--
The parts a payment divides into, as the lines printed on its receipt group them.

All of it is arithmetic over the lines and the payment: no line may be claimed
for more than it covers, the lines have to be priced in the currency the payment
moved, and what no group claimed stays where it was. Nothing here touches the
state — the parts are handed to `replaceParts`, which is what writes them — so a
division that cannot be carried out is a sentence rather than a half-written
ledger.

`printed` is what the payment is divisible by: the lines read off its receipt,
or, when it is itself a part of an earlier division, the shorter list that part
was left with. Every part carries away the lines it claimed, and the remainder
the units they left, so no line is ever offered twice — the receipt itself is
untouched, because what it says is a fact about the paper rather than about who
ended up paying for which half of it.
-/
def itemParts (t : Transaction) (printed : List LineItem) (groups : List Receipts.ItemGroup)
    (newIds : List TxId) : Except String (List Transaction) := do
  let lines := printed.toArray
  if lines.isEmpty then
    throw "no lines were read off that receipt; run 'resources receipt scan' on it first"
  -- A line's printed quantity is what its total is cut into, and a receipt filed
  -- before these bounds existed can carry any number at all.
  for l in printed do
    match l.qty with
    | some q => if q.natAbs > maxQty then
        throw s!"a line covering {q} units is more than a receipt prints; at most {maxQty}"
    | none => pure ()
  let commodity := lines[0]!.amount.commodity
  let code := commodity.code
  -- How many units a line covers.
  let unitsOf (n : Nat) : Nat := max 1 (((lines[n - 1]!).qty.map Int.natAbs).getD 1)
  -- Some of a line, as a line of its own: what it is called, how many of its
  -- units these are, and exactly the money carved for them. All of it is the
  -- line as printed, count and all, because a part that took everything a line
  -- covers paid for precisely what the bill says. A count a till printed
  -- negative stays negative: a correction taken in part is still a correction.
  let shareLine (n : Nat) (want : Nat) (amount : Int) : LineItem :=
    let line := lines[n - 1]!
    if want == unitsOf n then line
    else
      let count : Int := if (line.qty.getD 1) < 0 then -(want : Int) else (want : Int)
      { line with qty := some count, amount := ⟨commodity, amount⟩ }
  -- Check the whole division before writing any of it: no line may be claimed
  -- for more than it covers, or the same money would be booked twice and the
  -- remainder would absorb the difference in silence.
  let mut taken : Array Nat := (List.replicate lines.size 0).toArray
  for g in groups do
    for sh in g.items do
      if sh.line < 1 || sh.line > lines.size then
        throw s!"there is no line {sh.line}; this receipt has {lines.size}"
      let units := unitsOf sh.line
      let want := sh.qty.getD (units - taken[sh.line - 1]!)
      if want < 1 then
        throw s!"line {sh.line}: a share has to be at least one"
      if taken[sh.line - 1]! + want > units then
        throw s!"line {sh.line} covers {units}, and {taken[sh.line - 1]! + want} are spoken for"
      taken := taken.set! (sh.line - 1) (taken[sh.line - 1]! + want)
  -- How each claimed line's total divides between the units it covers, computed
  -- once per line and indexed. It used to be computed once per *share*, and a
  -- line may cover a hundred thousand units while an event may carry a hundred
  -- thousand shares — so one event of a megabyte made every node and every
  -- browser allocate ten billion cells, on every replay, for ever. The check
  -- above bounds the total quantity claimed per line and says nothing about how
  -- many shares claim it; this is what bounds the work.
  let mut cuts : Array (Option (Array Int)) := Array.replicate lines.size none
  for g in groups do
    for sh in g.items do
      if (cuts[sh.line - 1]!).isNone then
        cuts := cuts.set! (sh.line - 1)
          (some (splitParts (lines[sh.line - 1]!).amount.minor (unitsOf sh.line)).toArray)
  -- The lines are priced in the receipt's currency, and the parts have to be
  -- booked in the payment's. When a Swiss bill is settled by a euro card these
  -- differ, and nothing here knows the rate the bank used.
  if !(t.commodityCodes.contains code) then
    throw s!"this payment moved {String.intercalate ", " t.commodityCodes.eraseDups}, but the \
             receipt is priced in {code}; dividing needs them to agree"
  -- One account the money left, one it landed in. A transaction carrying more
  -- than that has been merged with something, and which leg a line belongs to
  -- is then a guess rather than a reading.
  let accounts := (t.postings.map (·.account)).eraseDups
  let moving := accounts.filter (fun a => t.netIn a code != 0)
  let some src := moving.find? (fun a => t.netIn a code < 0)
    | throw s!"nothing in {code} leaves this transaction"
  let some dst := moving.find? (fun a => t.netIn a code > 0)
    | throw s!"nothing in {code} arrives in this transaction"
  if moving.length != 2 then
    throw "dividing by lines needs one account the money left and one it landed in; \
           this transaction touches more, so unmerge it first"
  -- Carve from the largest leg on each side, leaving fees and the rest alone.
  let biggest (a : AccountId) (sign : Int) : Nat := Id.run do
    let mut best := 0
    let mut bestMag : Int := -1
    for (p, i) in t.postings.zipIdx do
      if p.account == a && p.amount.commodity.code == code &&
          sign * p.amount.minor > bestMag then
        best := i
        bestMag := sign * p.amount.minor
    return best
  let srcIdx := biggest src (-1)
  let dstIdx := biggest dst 1
  let srcPost := t.postings[srcIdx]!
  let dstPost := t.postings[dstIdx]!
  let mut parts : List Transaction := []
  let mut carved : Int := 0
  -- Hand the units out in order, so two groups claiming the same line get
  -- different slices of it and together take exactly what the line came to.
  let mut cursor : Array Nat := (List.replicate lines.size 0).toArray
  for (g, gi) in groups.zipIdx do
    let mut amount : Int := 0
    let mut names : List String := []
    let mut mine : List LineItem := []
    for sh in g.items do
      let units := unitsOf sh.line
      let from_ := cursor[sh.line - 1]!
      let want := sh.qty.getD (units - from_)
      let cut := (cuts[sh.line - 1]!).getD #[]
      let mut share : Int := 0
      for k in [from_ : from_ + want] do
        share := share + cut[k]!
      amount := amount + share
      cursor := cursor.set! (sh.line - 1) (from_ + want)
      let desc := (lines[sh.line - 1]!).description
      names := names ++ [if want == units then desc else s!"{want} × {desc}"]
      mine := mine ++ [shareLine sh.line want share]
    let some nid := newIds[gi]?
      | throw s!"dividing this needs {groups.length + 1} new ids, and \
                 {newIds.length} were given"
    carved := carved + amount
    parts := parts ++ [{ t with
      id := nid
      narration := String.intercalate ", " names
      items := some mine
      postings :=
        [{ srcPost with amount := ⟨commodity, -amount⟩ },
         { dstPost with account := ⟨g.into⟩, amount := ⟨commodity, amount⟩ }] }]
  if carved > -srcPost.amount.minor then
    throw s!"those lines come to more than the \
             {(Amount.mk commodity (-srcPost.amount.minor)).render} this payment moved"
  -- What no group claimed stays where it was, carrying the legs nobody divided.
  let rest := t.postings.zipIdx.map (fun (p, i) =>
    if i == srcIdx then { p with amount := ⟨commodity, p.amount.minor + carved⟩ }
    else if i == dstIdx then { p with amount := ⟨commodity, p.amount.minor - carved⟩ }
    else p)
  -- ...and so do the lines: one nobody claimed as it was printed, one claimed in
  -- part shrunk to the units still on it, and one claimed in full gone
  -- altogether. A remainder listing the whole bill would offer a second division
  -- the lines the first one already spent.
  let mut left : List LineItem := []
  let mut leftNames : List String := []
  for n in [1 : lines.size + 1] do
    let units := unitsOf n
    let from_ := cursor[n - 1]!
    let desc := (lines[n - 1]!).description
    if from_ == 0 then
      left := left ++ [lines[n - 1]!]
      leftNames := leftNames ++ [desc]
    else if from_ < units then
      let cut := (cuts[n - 1]!).getD #[]
      let mut over : Int := 0
      for k in [from_ : units] do
        over := over + cut[k]!
      left := left ++ [shareLine n (units - from_) over]
      leftNames := leftNames ++ [s!"{units - from_} × {desc}"]
  -- When the lines account for the whole payment there is nothing left to keep.
  if rest.any (fun p => p.amount.minor != 0) then
    let some rid := newIds[groups.length]?
      | throw s!"dividing this needs {groups.length + 1} new ids, and \
                 {newIds.length} were given"
    -- What the remainder is called. A payment's own words are the payment's —
    -- "cash receipt", the payee, whatever the bank said — and they still
    -- describe what is left of it. A part's are a list the last division wrote,
    -- and a list still naming what has gone to the siblings describes the wrong
    -- money, so a part's remainder is named the way a part is: by its lines.
    let narration := if t.items.isSome then String.intercalate ", " leftNames else t.narration
    parts := parts ++ [{ t with id := rid, narration, postings := rest, items := some left }]
  return parts

/-! ## Claims

Meeting a claim is one piece of arithmetic with two doors into it. `resolveClaim`
points an existing transaction at the claim it discharged; `payClaim` writes that
transaction itself, between the claim's own two accounts, and then walks the very
same path. Both end in the same three writes, which is why the path is a
function rather than two cases that have to be kept in step.
-/

/--
Settles a claim against the transaction that performed it.

`allowed` is handed straight to `putTxn`: `payClaim` has already established that
the author may move money between the claim's two accounts, and the legs written
here are on no others.
-/
def settleClaim (s : State) (author : MemberId) (realm : RealmId) (id actual splitId : TxId)
    (allowed : List AccountId := []) : Except String (State × List Change) := do
  let some claim := s.txn? id | throw s!"no such claim: {id.val}"
  if claim.state != .pending then
    throw s!"that claim is already {claim.state}"
  let act ← txnOf s actual
  if act.state != .posted then
    throw "a claim can only be met by a transaction that actually happened"
  let some recv := Pendings.receiver? claim | throw "this claim has no receiving leg"
  let some payAcc := Pendings.payer? claim | throw "this claim has no paying leg"
  let asked := Pendings.amount claim
  let arrived := act.netIn recv asked.commodity.code
  if arrived ≤ 0 then
    let some acc := s.account? recv | throw "the receiving account is gone"
    throw s!"{actual.val} brings nothing into {acc.name}"
  let some payer := s.account? payAcc | throw "the paying account is gone"
  let matched := min arrived asked.minor
  let left := asked.minor - matched
  let mut ts : List Transaction := []
  -- What the claim contributes to the real transaction: who the money was
  -- from. Anything it overpays goes to the same place, which is right — an
  -- overpayment leaves their purse owing them the difference.
  let funding := s.fundingAccounts
  let moved : Transaction := { act with postings := act.postings.map (fun p =>
    if funding.contains p.account then p else { p with account := payer.id }) }
  if moved.postings != act.postings then
    match moved.validate with
    | .error e => throw s!"claiming {actual.val} would not balance: {e}"
    | .ok bt => ts := ts ++ [bt.val]
  -- A met claim is stamped the way a merge stamps its sources, so it points at
  -- the entry that discharged it.
  let stamp (t : Transaction) : Transaction :=
    { t with postings := t.postings.map fun p =>
        { p with origin := p.origin <|> some actual.val } }
  let resize (n : Int) (t : Transaction) : Transaction :=
    { t with postings := t.postings.map fun p =>
        { p with amount := ⟨p.amount.commodity, if p.amount.minor > 0 then n else -n⟩ } }
  if left == 0 then
    ts := ts ++ [stamp { claim with state := .settled }]
  else
    -- The part that was met becomes a record in its own right, so what has been
    -- asked for stays the sum of both halves. A settlement nets off what has
    -- already been asked for, and a claim that had quietly shrunk would let the
    -- difference be asked for a second time. Both halves keep the two legs the
    -- claim had, so a part payment leaves two claims rather than one odd one.
    ts := ts ++ [stamp (resize matched { claim with id := splitId, date := act.date,
                                                    state := .settled }),
                 resize left claim]
  writeAll s author realm ts allowed

/-! ## Applying -/

/--
Applies one operation, inside one realm, on behalf of one member.

Every failure is a sentence a person can act on, and nothing is written when one
happens: an operation either has its whole effect or none of it.
-/
def applyChecked (s : State) (author : MemberId) (realm : RealmId) (op : Op) :
    Except String (State × List Change) := do
  match op with
  | .createRealm r =>
    if (s.realm? r.id).isSome then
      throw s!"a realm with that id already exists: {r.id.val}"
    -- The membership list is not the author's to choose. A realm created with
    -- somebody else already inside it — or with a generation that says keys have
    -- been rotated — is a realm whose history starts with a lie.
    if r.members != [(author, RealmRole.admin)] then
      throw "a realm is created with its author as its only admin"
    if r.generation != 0 then
      throw "a new realm starts at generation 0"
    return ({ s with realms := s.realms.insert r.id.val r }, [.realm r])
  | .putAccount a =>
    -- An account that already exists keeps its owner, its realm and what it
    -- mirrors: retagging somebody's account by mentioning its name in passing is
    -- exactly the confusion an owner exists to prevent, moving it between realms
    -- would move money out from under a key, and a mirror that could be repointed
    -- afterwards would say two accounts are one balance when they never were.
    -- A new one is an admin's to shape, which is why `owner`, `posters` and
    -- `bridgeOf` may be set here at all: whoever may write an account into a
    -- realm already decides who posts to everything in it.
    match s.account? a.id with
    | some old =>
      if old.realm != realm then
        throw s!"{old.name} is not in this realm"
      let merged :=
        { a with owner := old.owner, realm := old.realm, bridgeOf := old.bridgeOf,
                 posters := old.posters, mirrorOf := old.mirrorOf }
      return ({ s with accounts := s.accounts.insert merged.id.val merged }, [.account merged])
    | none =>
      let merged := { a with realm }
      return ({ s with accounts := s.accounts.insert merged.id.val merged }, [.account merged])
  | .mergeAccounts from_ into =>
    if from_ == into then
      throw "an account cannot be merged into itself"
    let src ← accountOf s from_
    let dst ← accountOf s into
    if src.realm != realm || dst.realm != realm then
      throw "both accounts have to be in this realm"
    -- Both sides, not just the destination. A merge empties the account it
    -- names and rebooks every posting that landed there, so asking only about
    -- the destination let anybody pour somebody else's balance into their own.
    if !s.canPost author src then
      throw s!"you may not post to {src.name}"
    if !s.canPost author dst then
      throw s!"you may not post to {dst.name}"
    let mut st := s
    let mut changes : List Change := []
    -- Balance is untouched: each posting keeps its amount and only changes
    -- which account it lands in.
    for t in s.txnsSorted do
      if t.postings.any (fun p => p.account == from_) then
        let moved : Transaction := { t with postings := t.postings.map (fun p =>
          if p.account == from_ then { p with account := into } else p) }
        let (st', c) := written st moved
        st := st'
        changes := changes ++ [c]
    st := { st with accounts := st.accounts.erase from_.val }
    changes := changes ++ [.accountDeleted from_]
    -- A rule that filed things into the emptied account now files them into the
    -- one that absorbed it, which is what a merge means for anything pointing at it.
    for r in s.rulesSorted do
      if r.setAccount == some from_.val then
        let moved := { r with setAccount := some into.val }
        st := { st with rules := st.rules.insert moved.id.val moved }
        changes := changes ++ [.rule moved]
    return (st, changes)
  | .deleteAccount id =>
    let a ← accountOf s id
    if a.realm != realm then
      throw s!"{a.name} is not in this realm"
    let n := s.postingCount id
    if n > 0 then
      throw s!"account still has {n} postings; move them first"
    return ({ s with accounts := s.accounts.erase id.val }, [.accountDeleted id])
  | .setAccountRights id posters =>
    let a ← accountOf s id
    if a.realm != realm then
      throw s!"{a.name} is not in this realm"
    if !s.canAdminister author a.realm then
      throw s!"only an admin of that realm may say who posts to {a.name}"
    let opened := { a with posters }
    return ({ s with accounts := s.accounts.insert id.val opened }, [.account opened])
  | .setAccountOwner id owner =>
    let a ← accountOf s id
    if a.realm != realm then
      throw s!"{a.name} is not in this realm"
    if !s.canAdminister author a.realm then
      throw s!"only an admin of that realm may hand {a.name} to somebody else"
    let handed := { a with owner }
    return ({ s with accounts := s.accounts.insert id.val handed }, [.account handed])
  | .putLabel l =>
    ofThisRealm? Label.name Label.realm realm (s.label? l.id)
    let written := { l with realm }
    return ({ s with labels := s.labels.insert l.id.val written }, [.label written])
  | .deleteLabel id =>
    -- A label nothing is filed under is nobody's, so deleting one is the no-op
    -- it always was; one that is there is its realm's.
    ofThisRealm? Label.name Label.realm realm (s.label? id)
    -- The label is gone from the transactions that carried it too; a label id
    -- nothing can resolve is worse than no label at all. Only from this realm's
    -- transactions, though: the rewrite used to reach every transaction in every
    -- realm the reader held, and deleting a budget's label that way made its
    -- settled claims invisible, so the settlement asked a second time for money
    -- that had already moved. A transaction with no leg here is not this part's
    -- to rewrite, so rather than leave a label id nothing resolves, the deletion
    -- is refused and the label stays.
    if s.txnsSorted.any (fun t => t.labels.contains id &&
        !t.postings.any (fun p => s.realmOf p.account == some realm)) then
      throw s!"{id.val} is on a transaction with no leg in this realm"
    let mut st := { s with labels := s.labels.erase id.val }
    let mut changes : List Change := [.labelDeleted id]
    for t in s.txnsSorted do
      if t.labels.contains id then
        let stripped := { t with labels := t.labels.filter (· != id) }
        let (st', c) := written st stripped
        st := st'
        changes := changes ++ [c]
    return (st, changes)
  | .putParty p =>
    -- A member owns the record their own spending lands on, and holds it from
    -- wherever they are: the party keeps the realm it was introduced in, and
    -- the rule that let them write it is `checkRights`'s self door. Anybody
    -- else's is an admin's, of the realm that person is recorded in.
    let old := s.party? p.id
    if (s.member? author).map (·.party) != some p.id then
      ofThisRealm? Party.name Party.realm realm old
    let written := { p with realm := ((old.map (·.realm)).getD realm) }
    return ({ s with parties := s.parties.insert p.id.val written }, [.party written])
  | .putGroup g =>
    if g.members.isEmpty then
      throw "a group needs at least one member"
    ofThisRealm? PartyGroup.name PartyGroup.realm realm s.groups[g.name]?
    let written := { g with realm }
    return ({ s with groups := s.groups.insert g.name written }, [.group written])
  | .deleteGroup name =>
    ofThisRealm? PartyGroup.name PartyGroup.realm realm s.groups[name]?
    return ({ s with groups := s.groups.erase name }, [.groupDeleted name])
  | .putTrip t =>
    ofThisRealm? Trip.name Trip.realm realm s.trips[t.name]?
    let written := { t with realm }
    return ({ s with trips := s.trips.insert t.name written }, [.trip written])
  | .deleteTrip name =>
    ofThisRealm? Trip.name Trip.realm realm s.trips[name]?
    return ({ s with trips := s.trips.erase name }, [.tripDeleted name])
  | .putRule r =>
    ofThisRealm? Rule.name Rule.realm realm (s.rule? r.id)
    let written := { r with realm }
    return ({ s with rules := s.rules.insert r.id.val written }, [.rule written])
  | .deleteRule idOrName =>
    -- This realm's rules of that name or id, and no others: a rule is removed
    -- from the realm it drives imports in.
    let hits := s.rulesSorted.filter fun r =>
      (r.id.val == idOrName || r.name == idOrName) && r.realm == realm
    if hits.isEmpty then
      throw s!"no such rule: {idOrName}"
    let mut st := s
    let mut changes : List Change := []
    for r in hits do
      st := { st with rules := st.rules.erase r.id.val }
      changes := changes ++ [.ruleDeleted r.id]
    return (st, changes)
  | .putTransaction t =>
    -- An empty posting list is vacuously balanced, which used to make this the
    -- way to rewrite the metadata of any transaction anywhere — including
    -- voiding it, and so taking it out of every balance for every reader.
    if t.postings.isEmpty then
      throw "a transaction needs postings"
    -- A transaction is written as something that happened. The three other
    -- states belong to claims, and claims have their own verbs, each of which
    -- asks who is entitled to say the thing it says.
    if t.state != .posted then
      throw "a transaction is written as posted; a claim is raised, met or withdrawn"
    putGuard s author realm t
    putTxn s author realm t
  | .deleteTransaction id =>
    let t ← txnOf s id
    -- Every leg, not merely the ones in this realm: a transaction that reaches
    -- past this realm is not this part's to retire, and one inside it is only
    -- retired by somebody who could have written it.
    checkOwnLegs s author realm t.postings
    let (st, c) := removed s id
    return (st, [c])
  | .splitTransaction id targets keepShare =>
    if targets.isEmpty then
      throw "say who to split this with"
    let t ← txnOf s id
    checkOwnLegs s author realm t.postings
    let funding := s.fundingAccounts
    let shareCount := targets.length + (if keepShare then 1 else 0)
    let mut postings : List Posting := []
    -- Each leg is split separately, which keeps a card fee tagged as a fee
    -- inside every share rather than smearing it into the principal.
    for p in t.postings do
      if funding.contains p.account then
        postings := postings ++ [p]
      else
        let parts := splitParts p.amount.minor shareCount
        -- Your share, if you are keeping one, stays where the posting already was.
        let mine := if keepShare then parts.take 1 else []
        let theirs := if keepShare then parts.drop 1 else parts
        for m in mine do
          if m != 0 then
            postings := postings ++ [{ p with amount := ⟨p.amount.commodity, m⟩ }]
        for (share, target) in theirs.zip targets do
          if share != 0 then
            postings := postings ++
              [{ p with account := target, amount := ⟨p.amount.commodity, share⟩ }]
    match ({ t with postings } : Transaction).validate with
    | .error e => throw s!"splitting would not balance: {e}"
    | .ok bt => putTxn s author realm bt.val
  | .mergeTransactions ids newId payee narration cancelIn =>
    if ids.length < 2 then
      throw "merging needs at least two transactions"
    let mut sources : List Transaction := []
    for id in ids do
      let src ← txnOf s id
      checkOwnLegs s author realm src.postings
      sources := sources ++ [src]
    -- A source's own postings may already carry origins from an earlier import;
    -- anything unstamped is attributed to the transaction it came from.
    let stamped := sources.map (fun t => t.withOrigin t.id.val)
    let some head := stamped.head? | throw "merging needs at least two transactions"
    let merged := head.mergeAll (stamped.drop 1)
    let weight (t : Transaction) : Int :=
      t.postings.foldl (fun acc p =>
        let m := p.amount.minor
        acc + (if m < 0 then -m else m)) 0
    -- The "principal" source is the one carrying the largest movement; its payee
    -- and narration describe the combined event best.
    let principal := stamped.foldl (fun best t => if weight t > weight best then t else best) head
    let mut result : Transaction :=
      { merged with
        id := newId
        date := stamped.foldl (fun d t => if Date.lt t.date d then t.date else d) head.date
        payee := payee <|> principal.payee
        narration := narration.getD principal.narration }
    -- The `Unclassified` legs auto-balancing created on both halves of a
    -- transfer cancel once the halves are in one transaction.
    for a in cancelIn do
      result := result.dropAccount a
    match result.validate with
    | .error e => throw s!"merge would not balance: {e}"
    | .ok bt =>
      let mut st := s
      let mut changes : List Change := []
      -- The sources go first, so merging into an id one of them held still writes.
      for t in sources do
        let (st', c) := removed st t.id
        st := st'
        changes := changes ++ [c]
      let (st', cs) ← putTxn st author realm bt.val
      return (st', changes ++ cs)
  | .unmergeTransaction id newIds =>
    let t ← txnOf s id
    checkOwnLegs s author realm t.postings
    let origins := t.origins
    if origins.length < 2 then
      throw "this transaction came from a single entry; there is nothing to unmerge"
    if t.postings.any (fun p => p.origin.isNone) then
      throw "some postings have no origin; unmerging would lose them"
    if newIds.length < origins.length then
      throw s!"unmerging this needs {origins.length} new ids, and {newIds.length} were given"
    let parts := t.unmerge (newIds.take origins.length)
    for part in parts do
      match part.validate with
      | .error e => throw s!"unmerging would leave an unbalanced part: {e}"
      | .ok _ => pure ()
    let (s1, gone) := removed s id
    let mut st := s1
    let mut changes : List Change := [gone]
    for part in parts do
      let (st', cs) ← putTxn st author realm part
      st := st'
      changes := changes ++ cs
    return (st, changes)
  | .replaceTransaction id parts _kind =>
    replaceParts s author realm id parts
  | .divideByItems id groups newIds =>
    if groups.isEmpty then
      throw "say which lines go together: --group 1+2=Account"
    let t ← txnOf s id
    -- A part of an earlier division is divided by what it was left with, not by
    -- the receipt: the lines its siblings took are theirs, and reading the page
    -- again would sell them twice. Everything else is divided by the page.
    let printed ← match t.items with
      | some [] =>
        throw "every line on that receipt already belongs to one of the parts this was \
               divided into; there is nothing left here to divide"
      | some its => pure its
      | none => do
        let some sha := t.attachments.head?
          | throw "this transaction has no receipt to take lines from"
        let some blob := s.blob? sha | throw s!"no such receipt: {sha}"
        pure blob.items
    let parts ← itemParts t printed groups newIds
    replaceParts s author realm id parts
  | .raiseClaim t =>
    if t.state != .pending then
      throw "a claim is a transaction that has not happened; raise it as pending"
    -- One account owes and one is owed. `putTxn` refuses a third leg wherever it
    -- comes from; saying so here too is what makes the verb that raises claims
    -- state its own shape.
    if t.postings.length != 2 then
      throw "a claim is exactly two legs"
    let asked := Pendings.amount t
    if asked.minor ≤ 0 then
      throw "a claim has to ask for something"
    let some recv := Pendings.receiver? t | throw "this claim has no receiving leg"
    let some pay := Pendings.payer? t | throw "this claim has no paying leg"
    if recv == pay then
      throw "a claim between one account and itself asks for nothing"
    -- Both legs are tagged, so a claim is recognisable leg by leg wherever it sits.
    let tagged := { t with postings := t.postings.map fun p =>
      { p with tag := p.tag <|> some Pendings.tag } }
    putTxn s author realm tagged
  | .resolveClaim id actual splitId =>
    let some claim := s.txn? id | throw s!"no such claim: {id.val}"
    -- Whose decision it is that a claim has been met: the person who would have
    -- seen the money arrive, or an admin. The debtor saying so is a receipt they
    -- wrote themselves.
    checkClaimParty s author realm claim "meet"
    -- The two legs are the claim's own and the right to meet it was settled
    -- above, so the poster check is that authorisation rather than `canPost` —
    -- exactly as `voidClaim` and `payClaim` already do it. Without this the
    -- right the table grants the receiver was unreachable: settling writes the
    -- claim back, and the claim's paying leg is the *debtor's* purse, which the
    -- receiver cannot post to. Every test that passed did so because its author
    -- happened to administer the realm.
    let allowed := (Pendings.payer? claim).toList ++ (Pendings.receiver? claim).toList
    settleClaim s author realm id actual splitId allowed
  | .voidClaim id writeOff =>
    let some claim := s.txn? id | throw s!"no such claim: {id.val}"
    -- Only an outstanding one. Withdrawing a claim that has been *met* used to
    -- take the payment it recorded out of the settlement arithmetic, so the same
    -- money was asked for a second time.
    if claim.state != .pending then
      throw "only an outstanding claim can be withdrawn"
    -- Withdrawing is the creditor's decision. The debtor withdrawing the claim
    -- against them is simply not paying.
    checkClaimParty s author realm claim "withdraw"
    let mut st := s
    let mut changes : List Change := []
    -- The spending stays where the division put it. Somebody consumed it, and
    -- their not paying does not turn it into your consumption — it turns it
    -- into your loss, which is a different account and a different sentence.
    match writeOff with
    | some (into, entryId, date) =>
      let some payAcc := Pendings.payer? claim | throw "this claim has no paying leg to write off"
      let loss ← accountOf s into
      if !loss.mine then
        throw s!"{loss.name} is not yours, so the loss cannot land there"
      let amount := Pendings.amount claim
      let entry : Transaction :=
        { id := entryId, date, payee := claim.payee
          narration := s!"written off: {claim.narration}"
          postings :=
            [{ account := loss.id, amount },
             { account := payAcc, amount := ⟨amount.commodity, -amount.minor⟩ }]
          labels := claim.labels, source := .manual author.val }
      match entry.validate with
      | .error e => throw s!"the write-off would not balance: {e}"
      | .ok bt =>
        let (st', cs) ← putTxn st author realm bt.val
        st := st'
        changes := changes ++ cs
    | none => pure ()
    -- The two legs are the claim's own and the right to withdraw it was settled
    -- above, so the poster check here is that authorisation rather than
    -- `canPost` — a claim between two purses belongs to neither alone.
    let allowed := (Pendings.payer? claim).toList ++ (Pendings.receiver? claim).toList
    let (st', cs) ← putTxn st author realm { claim with state := .void } allowed
    return (st', changes ++ cs)
  | .openBudget b account =>
    let full := Budget.accountName b.name
    -- Opening a budget that is already open says nothing new.
    let already := (sortedValues s.budgets).find? fun x =>
      x.budget.id == b.id || (x.realm == realm && x.budget.name == full)
    match already with
    | some existing => return (s, [.budget existing])
    | none =>
      -- Equity, deliberately: a budget balance is not wealth you hold. You have
      -- already parted with it, and the part that turns out to be your own share
      -- is never coming back.
      --
      -- An account of that name in this realm is adopted, and only if it is
      -- what a pot is. Reaching across realms for it would put the pot under a
      -- key the realm opening it does not hold; adopting whatever is there was
      -- worse, because the attest door mints accounts with a name of the
      -- author's choosing — so a viewer who self-granted a purse called
      -- `Budget.Hut` before the admin opened `Hut` had the pot adopted as their
      -- own bridge, which they may post to in either direction. Three questions
      -- say an account is a pot and nobody's purse, and an account of that name
      -- that fails any of them is a refusal rather than an adoption.
      let acc ← match s.accountByNameIn? realm full with
        | some a => do
          if a.kind != .equity then
            throw s!"{full} is already an account of another kind in this realm"
          if a.bridgeOf.isSome then
            throw s!"{full} is somebody's purse in this realm; a budget cannot be held in it"
          if !a.posters.isEmpty then
            throw s!"{full} already names its own posters; a budget cannot be held in it"
          pure a
        | none => do
          if (s.account? account.id).isSome then
            throw s!"an account with that id already exists: {account.id.val}"
          pure { account with name := full, kind := .equity, realm, bridgeOf := none }
      -- The label is pinned by id here when this realm already has one of the
      -- budget's name; when it does not, the first division or settlement says
      -- which label its claims carry, and that one is recorded then.
      --
      -- In this realm, like every other lookup that still goes by name. The
      -- label pinned here is what `Budget.claims` reads the budget's claims out
      -- of, so a label of the budget's name written in any realm a reader could
      -- open used to decide which claims a budget could see.
      let lbl := ((sortedValues s.labels).find?
        (fun l => l.name == b.label && l.realm == realm)).map (·.id)
      let opened : BudgetState :=
        { budget := { b with name := full, closed := false }
          realm, account := acc.id, label := lbl.getD ⟨""⟩ }
      return ({ s with accounts := s.accounts.insert acc.id.val acc
                       budgets := s.budgets.insert b.id.val opened },
              [.account acc, .budget opened])
  | .setParticipants id among =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    -- Costs already booked keep the division they were booked under: they were
    -- divided under the rule in force at the time, and rewriting them would
    -- change what somebody was told they owed for a weekend that is over.
    let weighed := among.map fun p => { p with weight := max p.weight 1 }
    let named := { bs with participants := weighed }
    return ({ s with budgets := s.budgets.insert id.val named }, [.budget named])
  | .contribute id t =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    if bs.budget.closed then
      throw s!"{bs.budget.shortName} is closed; reopen it to add costs"
    let some acc := Budget.account? bs.budget s
      | throw s!"{bs.budget.shortName} has no account of its own"
    if !t.commodityCodes.eraseDups.any (fun code => t.netIn acc.id code > 0) then
      throw "a contribution has to be an amount that was spent"
    putTxn s author realm t
  | .allocate id among c date hub txnId claimIds labelId =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    let (st, changes, _) ←
      divideUp s author realm bs.budget among c date txnId hub claimIds labelId
    let pinned := pinLabel st id labelId
    return (pinned.1, changes ++ pinned.2)
  | .settle id c hub due claimIds labelId =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    let (st, changes) ← squareUp s author realm bs.budget c hub due claimIds labelId
    let pinned := pinLabel st id labelId
    return (pinned.1, changes ++ pinned.2)
  | .closeBudget id among c hub date txnId claimIds labelId =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    if bs.budget.closed then
      throw s!"{bs.budget.shortName} is already closed"
    let people := among.getD bs.participants
    if people.isEmpty then
      throw s!"say who shares {bs.budget.shortName} first: \
               budget among {bs.budget.shortName} anna= …"
    let (st, changes, divided) ←
      divideUp s author realm bs.budget people c date txnId hub claimIds labelId
    -- Dividing settles as it goes; with nothing left to divide there is still
    -- the chance that a claim was written off or an invoice voided since.
    let (st, changes) ←
      if divided || (Budget.balance bs.budget st c).minor != 0 then pure (st, changes)
      else do
        let (st', cs) ← squareUp st author realm bs.budget c hub date claimIds labelId
        pure (st', changes ++ cs)
    -- Closed last on purpose. A failure between dividing and closing leaves the
    -- budget open, and closing again then divides only whatever is still
    -- waiting — where a half-applied close that had already flipped the flag
    -- would be a budget nobody could finish dividing.
    let closed : BudgetState :=
      { bs with budget := { bs.budget with closed := true }
                label := if labelId.val.isEmpty then bs.label else labelId }
    return ({ st with budgets := st.budgets.insert id.val closed }, changes ++ [.budget closed])
  | .reopenBudget id =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    if !bs.budget.closed then
      throw s!"{bs.budget.shortName} is already open"
    -- Nothing that was decided is undone: every division stands, and so does
    -- every claim raised from one.
    let opened : BudgetState := { bs with budget := { bs.budget with closed := false } }
    return ({ s with budgets := s.budgets.insert id.val opened }, [.budget opened])
  | .deleteBudget id =>
    let bs ← budgetOf s id
    checkBudget s author realm bs
    -- The transactions it touched are left alone: what was decided stays decided.
    return ({ s with budgets := s.budgets.erase id.val }, [.budgetDeleted bs.budget.id])
  | .issueInvoice inv sources =>
    if (s.invoice? inv.id).isSome then
      throw s!"an invoice with that id already exists: {inv.id.val}"
    -- Gapless, per year, and allocated here rather than by the caller: a gap in
    -- invoice numbers is a question an auditor asks and nobody can answer
    -- afterwards.
    -- Keyed by realm. One counter for the whole ledger meant that an admin of
    -- any realm a reader could open moved the ledger owner's invoice sequence:
    -- burning numbers with `issueInvoice` or winding it back with `deleteInvoice`.
    let counter := s!"{realm.val}:invoice:{inv.issued.year.toInt.toNat}"
    let n := (s.counters[counter]?.getD 0) + 1
    let number := s!"{inv.issued.year.toInt.toNat}-" ++ Str.padLeft (toString n) 4 '0'
    -- The payer is looked up by name, so an invoice to somebody you already know
    -- is addressed to the person rather than to a second record of them.
    --
    -- In this realm, and nowhere else. The lookup used to be the first party of
    -- that name in id order across every realm a reader could open, and a member
    -- may set the name of their own party to anything at all from any realm they
    -- are in (`putParty` goes through the attest door). So a member whose party
    -- id sorted low renamed it to a customer's name, and every invoice the ledger
    -- owner afterwards issued to that name was addressed to them instead: the
    -- `payerId`, the reference, and the receivable in every standing. Nothing was
    -- refused and nothing looked wrong.
    let known := (sortedValues s.parties).find?
      (fun p => p.name == inv.payerName && p.realm == realm)
    let payer ← match known, inv.payerId with
      | some p, _ => pure p.id
      | none, some id => pure id
      | none, none => throw s!"there is nobody called {inv.payerName} in this realm; \
                               give the invoice a payer id"
    let mut st := s
    let mut changes : List Change := []
    if known.isNone && (s.party? payer).isNone then
      -- Created here, like every other new entry: a party introduced by an
      -- invoice belongs to the realm the invoice was issued in.
      let p : Party := { id := payer, name := inv.payerName, realm }
      st := { st with parties := st.parties.insert payer.val p }
      changes := changes ++ [.party p]
    let raised : InvoiceState :=
      { invoice := { inv with number, payerId := some payer
                              reference := Rf.make (number.replace "-" "") }
        sources, realm }
    st := { st with invoices := st.invoices.insert inv.id.val raised
                    counters := st.counters.insert counter n }
    return (st, changes ++ [.counter counter n, .invoice raised])
  | .setInvoiceStatus id status =>
    let some inv := s.invoice? id | throw s!"no such invoice: {id.val}"
    -- An invoice is a document one realm sent to somebody, so what it says it is
    -- now is that realm's to say. Without this an admin of any realm a reader
    -- could open marked any invoice in the ledger `paid` or `void`.
    ofThisRealm s!"invoice {inv.invoice.number}" realm inv.realm
    let moved := { inv with invoice := { inv.invoice with status } }
    return ({ s with invoices := s.invoices.insert id.val moved }, [.invoice moved])
  | .settleInvoice id txn =>
    let some inv := s.invoice? id | throw s!"no such invoice: {id.val}"
    ofThisRealm s!"invoice {inv.invoice.number}" realm inv.realm
    let _ ← txnOf s txn
    let paid := { inv with
      invoice := { inv.invoice with status := .paid, settledTxn := some txn } }
    return ({ s with invoices := s.invoices.insert id.val paid }, [.invoice paid])
  | .deleteInvoice id =>
    let some inv := s.invoice? id | throw s!"no such invoice: {id.val}"
    -- The realm that handed the number out is the one that may give it back.
    -- The counter is keyed by realm, so a part from somewhere else deleting this
    -- invoice wound back a sequence that had never issued it: the issuing realm
    -- kept the burnt number, and the next invoice in the other realm duplicated
    -- one already sent.
    ofThisRealm s!"invoice {inv.invoice.number}" realm inv.realm
    -- Only a draft may go: once a number has been sent to somebody it has to be
    -- voided instead, because they have seen it.
    if inv.invoice.status != .draft then
      throw s!"invoice {inv.invoice.number} is {inv.invoice.status}; \
               void it rather than deleting it"
    let mut st := { s with invoices := s.invoices.erase id.val }
    let mut changes : List Change := [.invoiceDeleted id]
    -- The year's counter goes back when the number that is going was the last
    -- one it handed out, so removing an invoice raised by mistake leaves no hole.
    match inv.invoice.number.splitOn "-" with
    | [year, seq] =>
      let counter := s!"{inv.realm.val}:invoice:{year}"
      let held := st.counters[counter]?.getD 0
      if (seq.toNat?.map Int.ofNat) == some held then
        st := { st with counters := st.counters.insert counter (held - 1) }
        changes := changes ++ [.counter counter (held - 1)]
    | _ => pure ()
    return (st, changes)
  | .registerBlob file =>
    -- Storing the same bytes twice is one file and one record, so a second
    -- registration says nothing new about the file itself — not its size, not
    -- its name, and never what was read off it.
    --
    -- Two fields are the exception, and they are the two that are not about the
    -- bytes but about where a copy of them is kept: the hash of the ciphertext
    -- and the key that opens it. A receipt filed in one realm and then attached
    -- to a transaction in another is sealed again under that realm's key, and
    -- the re-registration is how the new sealing reaches everybody who can read
    -- the second realm. A registration that carries neither leaves both as they
    -- were, which is what makes storing the same bytes twice a no-op still.
    match s.blob? file.sha256 with
    | some b =>
      -- Re-sealing somebody else's file is a decision about where their bytes
      -- are kept and which key opens them, so it is theirs or an admin's — and
      -- an admin of the realm the record is *in*, rather than of the realm the
      -- part names. That is what the second door used to be missing: it asked
      -- nothing at all about where the bytes had been filed, so an admin of any
      -- realm a reader could open could re-seal any receipt in the ledger.
      --
      -- The record then moves to the realm the part names, and this is the one
      -- operation that may move one. A receipt is filed in whichever realm it
      -- was scanned in and attached to a payment that may be in another, and
      -- everybody who can read that payment has to be able to read the paper
      -- behind it — so the re-seal and the attachment are one event, in the
      -- payment's realm. The receipt follows the payment, and with it the right
      -- to say what it contains.
      if b.registeredBy != author && !s.canAdminister author b.realm then
        throw "only the member who registered that file, or an admin of the realm it was \
               filed in, may register it again"
      let rewrapped : BlobState :=
        { b with realm, file := { b.file with
            cipherHash := file.cipherHash <|> b.file.cipherHash
            wrappedKey := file.wrappedKey <|> b.file.wrappedKey } }
      return ({ s with blobs := s.blobs.insert file.sha256 rewrapped }, [.blob rewrapped])
    | none =>
      let b : BlobState := { file, registeredBy := author, realm }
      return ({ s with blobs := s.blobs.insert file.sha256 b }, [.blob b])
  | .attach txn sha =>
    let t ← txnOf s txn
    checkOwnLegs s author realm t.postings
    let some _ := s.blob? sha | throw s!"no such receipt: {sha}"
    if t.attachments.contains sha then
      return (s, [.txn t])
    let (st, c) := written s { t with attachments := t.attachments ++ [sha] }
    return (st, [c])
  | .detach txn sha =>
    let t ← txnOf s txn
    checkOwnLegs s author realm t.postings
    let (st, c) := written s { t with attachments := t.attachments.filter (· != sha) }
    return (st, [c])
  | .recordExtraction sha e =>
    let some b := s.blob? sha | throw s!"no such receipt: {sha}"
    checkReceipt s author realm sha b
    let read := { b with extracted := { e with items := [] }, items := e.items }
    return ({ s with blobs := s.blobs.insert sha read }, [.blob read])
  | .setReceiptLines sha items =>
    let some b := s.blob? sha | throw s!"no such receipt: {sha}"
    checkReceipt s author realm sha b
    -- Lines are allowed to fall short of the total — paper folds, and a service
    -- charge is nobody's line — but never to overrun it, because then they would
    -- be describing a payment that did not happen.
    match b.total? with
    | some stated =>
      let used := (items.map (·.amount.minor)).sum
      if used.natAbs > stated.minor.natAbs then
        throw s!"that would take the lines past the {stated.render} on this receipt"
    | none => pure ()
    let lined := { b with items }
    return ({ s with blobs := s.blobs.insert sha lined }, [.blob lined])
  | .forgetBlob sha =>
    -- Forgetting is not detaching: the bytes are already gone from the store by
    -- the time this is applied, so only somebody who administers the realm may
    -- do it, and a receipt still attached to something is left alone by the
    -- caller rather than refused here.
    if !s.canAdminister author realm then
      throw "only an admin of that realm may forget a receipt"
    let some b := s.blob? sha | throw s!"no such receipt: {sha}"
    ofThisRealm "that receipt" realm b.realm
    return ({ s with blobs := s.blobs.erase sha }, [.blobDeleted sha])
  | .recordImportBatch b =>
    ofThisRealm? (fun x => s!"the import {x.id.val}") ImportBatch.realm realm s.batches[b.id.val]?
    let written := { b with realm }
    return ({ s with batches := s.batches.insert b.id.val written }, [.batch written])
  | .addMember m =>
    -- Two ways somebody gets into the books. An admin of this realm writes them
    -- in, which is how you record a person you are about to let in; or a member
    -- introduces themselves, which is the only way somebody who joined through
    -- an invite ever reaches the log at all — the admin's node was not there.
    -- The sequencer took their part for this realm only because it already
    -- holds a grant for them here, so the log may take their word for who they
    -- are, and for nothing else.
    --
    -- "Who they are" is the whole of it, and the party is part of who they are.
    -- A self-introduction naming somebody else's party — or the ledger's own —
    -- would attribute the newcomer's spending to that person in every budget
    -- standing and every invoice, so a newcomer may only name a party nobody
    -- has yet, or the one already recorded for them.
    if !s.canAdminister author realm then
      match s.member? m.id with
      | some existing =>
        -- Somebody the ledger already knows is saying so again, which is what
        -- the owner of a ledger does when they open a second realm. The party
        -- is the one thing they may not revise.
        if existing.party != m.party then
          throw "a member cannot change the party their spending lands on"
      | none =>
        -- A newcomer. `Party.selfId` is what `Account.mine` tests, so taking it
        -- would make their spending the ledger owner's; taking somebody else's
        -- would attribute it to that person in every budget standing.
        if m.party == Party.selfId then
          throw "a member cannot introduce themselves as the ledger's own party"
        if (sortedValues s.members).any (fun x => x.party == m.party) then
          throw "that party is already somebody else's"
        if (s.party? m.party).isSome then
          throw "that party is already in the books; an admin has to write you in"
    match s.party? m.party with
    | some _ => return ({ s with members := s.members.insert m.id.val m }, [.member m])
    | none =>
      -- A member names the party their own spending lands on, and a remote
      -- reader has no other record of a newcomer. Writing the party here is
      -- what keeps that reference from dangling for everybody downstream, and
      -- it is written in the realm the part names — the one everybody who can
      -- read this can read.
      let p : Party := { id := m.party, name := m.name, kind := "contact", realm }
      return ({ s with parties := s.parties.insert p.id.val p
                       members := s.members.insert m.id.val m }, [.party p, .member m])
  | .removeMember id =>
    if id == Member.selfId then
      throw "the member this ledger belongs to cannot be removed"
    let some _ := s.member? id | throw s!"no such member: {id.val}"
    -- What an admin of one realm may do is put somebody out of *that* realm.
    -- The identity itself is shared with every other realm they are in, so it
    -- goes only when nothing is left pointing at it.
    let mut st := s
    let mut changes : List Change := []
    match s.realm? realm with
    | some r =>
      if r.isMember id then
        let closed := r.withoutMember id
        st := { st with realms := st.realms.insert realm.val closed }
        changes := changes ++ [.realm closed]
    | none => pure ()
    if !(sortedValues st.realms).any (fun r => r.isMember id) then
      st := { st with members := st.members.erase id.val }
      changes := changes ++ [.memberDeleted id]
    return (st, changes)
  | .grant target member role bridge =>
    -- An admin lets somebody in; or a member attests their own viewer grant,
    -- which is what a joiner does once an invite has been spent. The sequencer
    -- accepted a part for this realm from them only because it already holds a
    -- grant for them here, so the claim is one somebody has checked. It buys a
    -- view and nothing else: a self-granted admin role would be a realm taken
    -- over by the person writing the takeover down.
    let some r := s.realm? target | throw s!"no such realm: {target.val}"
    let some m := s.member? member
      | throw s!"cannot grant an unknown member: add {member.val} first"
    let opened := r.withMember member role
    if s.canAdminister author target then
      -- An admin's grant, which is the ordinary one. An account that is already
      -- there stays exactly as it is: a grant hands out a purse; it is not a way
      -- to move somebody's account between realms, which would move money out
      -- from under a key while transactions still point at it.
      -- By name *in this realm*. The unscoped lookup found the first account of
      -- that name in any realm and then refused the grant because it was
      -- elsewhere — and `Members.<name>` is a name any member can mint about
      -- themselves through the attest door, in any realm they may write in. So
      -- one member could block an admin from granting a bridge of that name in
      -- every other realm, for ever. It failed closed, so it was a denial rather
      -- than a capture; it is still not a rule anybody would write down.
      match (s.account? bridge.id) <|> s.accountByNameIn? target bridge.name with
      | some old =>
        if old.realm != target then
          throw s!"{old.name} is in another realm; a grant cannot move it"
        return ({ s with realms := s.realms.insert target.val opened }, [.realm opened])
      | none =>
        -- The bridge is how they hold a balance here: it is theirs, in this
        -- realm, and it is the one account they may always post to. Whose it is
        -- comes from the member record rather than from the operation.
        let purse :=
          { bridge with owner := m.party, realm := target, bridgeOf := some member
                        mirrorOf := none }
        return ({ s with realms := s.realms.insert target.val opened
                         accounts := s.accounts.insert purse.id.val purse },
                [.realm opened, .account purse])
    else
      -- The attest door, and the whole of what it may make: one purse, named
      -- after the member it belongs to, of the one kind money is held in, with
      -- nobody else on it and mirroring nothing.
      --
      -- Everything else in `bridge` is ignored, and that is the fix. The door is
      -- open to any member about themselves, and it used to write the operation's
      -- `name`, `kind`, `posters`, `iban` and `note` verbatim — so a viewer could
      -- mint an account per grant, of any name and kind, in a realm they merely
      -- read, postable by them without limit. Two lookups elsewhere still went by
      -- name, so `Budget.Hut` could be squatted before a budget was opened, and a
      -- participant's share could be blocked for ever by an account named after
      -- their purse. Nothing is adopted here either: a name or an id that is
      -- already spoken for in this realm is a refusal, because a joiner taking
      -- over an account that is already there is the same hole read backwards.
      let name := "Members." ++ m.name
      if (s.account? bridge.id).isSome then
        throw s!"an account with that id already exists: {bridge.id.val}"
      if (s.accountByNameIn? target name).isSome then
        throw s!"{name} is already an account in that realm; an admin has to let you in"
      let purse : Account :=
        { id := bridge.id, name, kind := .asset, owner := m.party, realm := target
          bridgeOf := some member, posters := [], mirrorOf := none }
      return ({ s with realms := s.realms.insert target.val opened
                       accounts := s.accounts.insert purse.id.val purse },
              [.realm opened, .account purse])
  | .revoke target member =>
    let some r := s.realm? target | throw s!"no such realm: {target.val}"
    -- The generation moves, because what they have already seen they have seen;
    -- what is written from here on is written under a key they do not hold.
    let closed := { r.withoutMember member with generation := r.generation + 1 }
    return ({ s with realms := s.realms.insert target.val closed }, [.realm closed])
  | .setRole target member role =>
    let some r := s.realm? target | throw s!"no such realm: {target.val}"
    if !r.isMember member then
      throw s!"{member.val} is not in that realm"
    let changed := r.withMember member role
    return ({ s with realms := s.realms.insert target.val changed }, [.realm changed])
  | .rotateRealmKey target =>
    let some r := s.realm? target | throw s!"no such realm: {target.val}"
    let rotated := { r with generation := r.generation + 1 }
    return ({ s with realms := s.realms.insert target.val rotated }, [.realm rotated])
  | .snapshot _ =>
    -- Unreachable: `checkRights` refuses a snapshot before `applyChecked` is
    -- called at all. It is refused here too so that the two doors say the same
    -- thing, and so that nothing reaches a whole state through this one.
    throw "a snapshot is where a log starts, not something a part may say"
  | .payClaim id payment date =>
    let some claim := s.txn? id | throw s!"no such claim: {id.val}"
    if claim.state != .pending then
      throw s!"that claim is already {claim.state}"
    if (s.txn? payment).isSome then
      throw s!"a transaction with that id already exists: {payment.val}"
    let some recv := Pendings.receiver? claim | throw "this claim has no receiving leg"
    let some payAcc := Pendings.payer? claim | throw "this claim has no paying leg"
    let payer ← accountOf s payAcc
    let receiver ← accountOf s recv
    -- Both legs have to be able to hold a balance. A claim whose receiving leg
    -- is an equity account was settled by a payment `settleClaim` then rewrote
    -- onto the paying account alone, so the claim came out met and no money had
    -- gone anywhere.
    if !payer.holdsMoney || !receiver.holdsMoney then
      throw "a claim is paid between two accounts that can hold money"
    -- Who may say a claim was met: whoever's purse is owed, or somebody who
    -- administers the realm the two of them sit in. Not the payer: the amount
    -- being the claim's stops them inventing the *size* of a payment, and stops
    -- nothing about inventing the payment itself.
    if receiver.bridgeOf != some author && !s.canAdminister author realm then
      throw "only the receiver or an admin of that realm may say this claim was paid"
    let asked := Pendings.amount claim
    let entry : Transaction :=
      { id := payment, date
        narration := "payment of " ++ claim.narration
        postings :=
          [{ account := payAcc, amount := ⟨asked.commodity, -asked.minor⟩
             tag := some Pendings.tag },
           { account := recv, amount := asked, tag := some Pendings.tag }]
        source := .manual author.val }
    -- The two legs are the claim's own, so the poster check is the
    -- authorisation above rather than `canPost`; the accounts still have to
    -- exist, be open and be in this realm, which is what `putTxn` checks.
    let allowed := [payAcc, recv]
    let (st, cs) ← putTxn s author realm entry allowed
    -- The claim is met in full by construction — the payment is exactly what it
    -- asked for — so the part id below never names anything.
    let (st', cs') ← settleClaim st author realm id payment ⟨payment.val ++ ":part"⟩ allowed
    return (st', cs ++ cs')

/--
Applies one operation: the rule, the bounds, and then what it does.

Three steps, always in this order, and the first two are total functions of the
operation and of who wrote it. Nothing in `applyChecked` re-derives who may act;
what it adds is the part of a rule that depends on what the operation *names* —
the legs it writes, the claim it speaks about, the receipt it rewrites.
-/
def applyOp (s : State) (author : MemberId) (realm : RealmId) (op : Op) :
    Except String (State × List Change) := do
  checkRights s author realm op
  checkBounds op
  applyChecked s author realm op

/--
The three steps, separated: an accepted operation passed its rule and its
bounds, and did what `applyChecked` says.

Every theorem about what an operation *does* is a theorem about `applyChecked`,
and this is how it reaches `applyOp`.
-/
theorem applyOp_eq {s : State} {author : MemberId} {realm : RealmId} {op : Op}
    {v : State × List Change} :
    applyOp s author realm op = .ok v ↔
      (checkRights s author realm op = .ok () ∧ checkBounds op = .ok () ∧
        applyChecked s author realm op = .ok v) := by
  simp only [applyOp, bind, Except.bind]
  cases hr : checkRights s author realm op with
  | error e => simp
  | ok u =>
    cases u
    cases hb : checkBounds op with
    | error e => simp
    | ok w =>
      cases w
      simp

/-- What an accepted operation did, with the checks it passed peeled off. -/
theorem applyChecked_of_applyOp {s : State} {author : MemberId} {realm : RealmId} {op : Op}
    {v : State × List Change} (h : applyOp s author realm op = .ok v) :
    applyChecked s author realm op = .ok v := (applyOp_eq.mp h).2.2

/-- An operation that passes its rule and its bounds is `applyChecked`. -/
theorem applyOp_of_applyChecked {s : State} {author : MemberId} {realm : RealmId} {op : Op}
    {v : State × List Change} (hr : checkRights s author realm op = .ok ())
    (hb : checkBounds op = .ok ()) (h : applyChecked s author realm op = .ok v) :
    applyOp s author realm op = .ok v := applyOp_eq.mpr ⟨hr, hb, h⟩

/-- Applies one part of an event: its operation, in the realm it names. -/
def applyPart (s : State) (author : MemberId) (p : Part) : Except String (State × List Change) :=
  applyOp s author p.realm p.op

/--
Applies an event, part by part.

Parts are independent, which is what makes a part the unit of sharing: a reader
who cannot read one realm's part goes on applying the others. An invalid part is
skipped for the same reason — it is a fact about that part, not about the event
— so this cannot fail, and what it could not apply is simply not in the changes.
-/
def step (s : State) (e : Event) : State × List Change :=
  e.parts.foldl
    (fun (acc : State × List Change) p =>
      match applyPart acc.1 e.author p with
      | .ok (s', cs) => (s', acc.2 ++ cs)
      | .error _ => acc)
    (s, [])

/-! ## Genesis, and where a log starts

A log starts from a state. The state is carried by the first event, as its one
part, and reading it is a matter of *position*: the first event of the order, or
nowhere.

That is the whole of the rule, and it is a change of subject rather than a
tightening. It used to be that `applyOp` took a snapshot whenever the state it
landed on looked untouched — which is a fact about what the reader had managed
to fold, not about where the reader stood. A browser holds one generation's key
while a node holds every generation, so after any revoke or key rotation a
browser replaying from the beginning skips every part written before the
rotation and arrives, part way along, at a state that looks exactly like a new
ledger. One snapshot by anybody still in the realm then replaced the whole of
what that browser displayed — balances, standings, who administers the realm —
and since the snapshot could name its author an admin, every checkpoint they
published afterwards was trusted too.

So no part may carry a snapshot, `applyOp` refuses one wherever it appears, and
the genesis is read off position 1 by `replay`. A reader that starts anywhere
else starts from a checkpoint it has verified, and one that cannot read every
part of a realm between its start and the head refuses to display that realm
rather than folding around the gap: what it would show is not a ledger anybody
wrote.
-/

/--
Everything a whole state amounts to, as changes, in sorted order.

The list a store projects to hold exactly this state, however its tables are
keyed — and the one list that cannot leave an entity out, which is why a rebuild
and a genesis are the same statement made to two different places.
-/
def snapshotChanges (g : State) : List Change :=
  (sortedValues g.realms).map Change.realm ++
  (sortedValues g.members).map Change.member ++
  (sortedValues g.accounts).map Change.account ++
  (sortedValues g.labels).map Change.label ++
  (sortedValues g.parties).map Change.party ++
  (sortedValues g.groups).map Change.group ++
  (sortedValues g.trips).map Change.trip ++
  (sortedValues g.rules).map Change.rule ++
  (sortedValues g.txns).map Change.txn ++
  (sortedValues g.budgets).map Change.budget ++
  (sortedValues g.invoices).map Change.invoice ++
  (sortedValues g.blobs).map Change.blob ++
  (sortedValues g.batches).map Change.batch ++
  (sortedPairs g.counters).map (fun (n, v) => Change.counter n v) ++
  (g.fingerprints.toList.mergeSort (· ≤ ·)).map Change.fingerprint

/--
Applying one event at a known position in the order.

Position 1 is the only place a genesis is read, and `Event.genesis?` is the only
shape that counts as one. Everywhere else this is `step`, and a part carrying a
snapshot is refused like any other invalid part.

A reader that folds its own log event by event — the node, as it takes entries
in — uses this; a reader that has the whole log uses `replay`, which is this
over the whole of it.
-/
def stepAt (pos : Nat) (s : State) (e : Event) : State × List Change :=
  if pos == 1 then
    match e.genesis? with
    | some g => (g, snapshotChanges g)
    | none => step s e
  else step s e

/--
Replays a log from the beginning. The same log always gives the same state.

The first event is the genesis when it is one event of one snapshot part;
otherwise the fold starts from `State.init` and the first event is applied like
any other. Nothing later in the log can be a genesis, wherever it appears in
whatever order.
-/
def replay (log : List Event) : State :=
  match log with
  | [] => State.init
  | e :: rest =>
    match e.genesis? with
    | some g => rest.foldl (fun s e => (step s e).1) g
    | none => (e :: rest).foldl (fun s e => (step s e).1) State.init

/-- The state a log replays to: `replay`, under the name the rest of the system uses. -/
def state (log : List Event) : State := replay log

end Resources
