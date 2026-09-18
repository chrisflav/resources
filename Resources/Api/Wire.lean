import Resources.Import.Staging
import Resources.Invoice.Render
import Resources.Store.Blob
import Resources.Store.Receipts
import Resources.Store.Tokens

/-!
# Wire types

The only shapes the CLI and the web client ever see. They are deliberately
separate from the domain types: the wire carries resolved account and label
*names* alongside ids, which the domain has no business knowing about, and
amounts travel as exact integer minor units plus a rendered string so no
JavaScript client is ever tempted to do float arithmetic on money.
-/

open Lean

namespace Resources
namespace Wire

/-- Everything needed to render ids as names in one payload. -/
structure NameEnv where
  accounts : Array Account
  labels : Array Label
  parties : Array Party

/-- Loads the name environment from the store. -/
def NameEnv.load (ctx : Ctx) : IO NameEnv := do
  return { accounts := ← Accounts.list ctx, labels := ← Labels.list ctx,
           parties := ← Parties.list ctx }

/-- The account name for an id, or the raw id if it has been deleted. -/
def NameEnv.account (e : NameEnv) (id : AccountId) : String :=
  ((e.accounts.find? (·.id == id)).map (·.name)).getD id.val

/-- The label name for an id. -/
def NameEnv.label (e : NameEnv) (id : LabelId) : String :=
  ((e.labels.find? (·.id == id)).map (·.name)).getD id.val

/-- The kind of the account an id names. -/
def NameEnv.accountKind (e : NameEnv) (id : AccountId) : String :=
  match e.accounts.find? (fun a => a.id == id) with
  | some a => a.kind.toString
  | none => "expense"

/-- The party name for an id. -/
def NameEnv.party (e : NameEnv) (id : PartyId) : String :=
  ((e.parties.find? (·.id == id)).map (·.name)).getD id.val

/-- Who an account belongs to. -/
def NameEnv.owner (e : NameEnv) (id : AccountId) : PartyId :=
  ((e.accounts.find? (·.id == id)).map (·.owner)).getD Party.selfId

/-- The name of the person an account belongs to. -/
def NameEnv.ownerName (e : NameEnv) (id : AccountId) : String := e.party (e.owner id)

/-- Looks an account up by name or id. -/
def NameEnv.accountId? (e : NameEnv) (nameOrId : String) : Option AccountId :=
  ((e.accounts.find? (fun a => a.name == nameOrId || a.id.val == nameOrId)).map (·.id))

private def jint (n : Int) : Json := Json.num (JsonNumber.fromInt n)

private def jopt : Option String → Json
  | some s => Json.str s
  | none => Json.null

/-- An amount, as exact minor units plus a pre-rendered string. -/
def amountJson (a : Amount) : Json :=
  Json.mkObj [("minor", jint a.minor), ("commodity", a.commodity.code),
              ("exponent", jint a.commodity.exponent), ("text", a.digits)]

/--
An account.

`mine` travels beside `kind` on purpose. They answer different questions — what
this account is, and whose it is — and every client that wants a net worth wants
the second, not a rule of thumb about the first.
-/
def accountJson (e : NameEnv) (a : Account) : Json :=
  Json.mkObj [
    ("id", a.id.val), ("name", a.name), ("kind", a.kind.toString),
    ("owner", a.owner.val), ("ownerName", e.party a.owner), ("mine", Json.bool a.mine),
    ("commodity", jopt (a.commodity.map (·.code))), ("iban", jopt a.iban),
    ("note", jopt a.note), ("closedOn", jopt (a.closedOn.map (·.toIso)))]

/-- A label. -/
def labelJson (l : Label) : Json :=
  Json.mkObj [("id", l.id.val), ("name", l.name), ("colour", jopt l.colour)]

/-- A party. -/
def partyJson (p : Party) : Json :=
  Json.mkObj [("id", p.id.val), ("name", p.name), ("iban", jopt p.iban),
              ("email", jopt p.email), ("note", jopt p.note), ("kind", p.kind)]

/-- A posting, with the account name resolved. -/
def postingJson (e : NameEnv) (p : Posting) : Json :=
  Json.mkObj [
    ("account", e.account p.account), ("accountId", p.account.val),
    ("kind", e.accountKind p.account), ("owner", e.ownerName p.account),
    ("mine", Json.bool (e.owner p.account == Party.selfId)),
    ("amount", amountJson p.amount),
    ("party", jopt (p.party.map e.party)), ("note", jopt p.note),
    ("origin", jopt p.origin), ("tag", jopt p.tag)]

/-- One priced line read off a receipt. -/
def lineItemJson (i : LineItem) : Json :=
  Json.mkObj [("description", i.description),
              ("qty", match i.qty with | some q => jint q | none => Json.null),
              ("amount", amountJson i.amount)]

/--
The line a person recognises: the net movement on the account that carries the
money. Postings on one account are summed first, so a purchase and its fee read
as a single figure rather than two.
-/
def headline (e : NameEnv) (t : Transaction) : Option (String × Amount) :=
  (t.principal fun a =>
    let kind := e.accountKind a
    kind == "asset" || kind == "liability").map fun (account, amount) =>
      (e.account account, amount)


/-- A transaction. -/
def txnJson (e : NameEnv) (t : Transaction) : Json :=
  Json.mkObj [
    ("id", t.id.val), ("date", t.date.toIso), ("payee", jopt t.payee),
    ("narration", t.narration), ("source", t.source.encode),
    ("state", t.state.toString),
    ("balanced", Json.bool (decide t.Balanced)),
    ("postings", Json.arr (t.postings.map (postingJson e)).toArray),
    ("labels", Json.arr (t.labels.map (fun l => Json.str (e.label l))).toArray),
    ("attachments", Json.arr (t.attachments.map Json.str).toArray),
    -- What this one paid for, when it is a part of a division and so paid for
    -- only some of the page it hangs on. Null is the ordinary case: whatever its
    -- receipt says, all of it.
    ("items", match t.items with
              | some its => Json.arr (its.map lineItemJson).toArray
              | none => Json.null),
    ("origins", Json.arr (t.origins.map Json.str).toArray),
    ("headline",
      match headline e t with
      | some (account, amount) =>
        Json.mkObj [("account", account), ("amount", amountJson amount)]
      | none => Json.null)]

/-- A balance line. -/
def balanceJson (b : Balances.Entry) : Json :=
  Json.mkObj [("account", b.account), ("commodity", b.commodity), ("minor", jint b.minor),
              ("text", (Amount.mk (Commodity.ofCode b.commodity) b.minor).digits)]

/-- A staged import row. -/
def stagedJson (e : StagedEntry) : Json :=
  Json.mkObj [
    ("id", e.id.val), ("batch", e.batch.val), ("fingerprint", e.fingerprint),
    ("date", e.raw.date.toIso), ("payee", jopt e.raw.payee), ("purpose", jopt e.raw.purpose),
    ("amount", amountJson e.raw.amount), ("counterIban", jopt e.raw.counterIban),
    ("bankRef", jopt e.raw.bankRef), ("state", e.state),
    ("suggestedAccount", jopt e.suggestedAccount),
    ("txnId", jopt (e.txnId.map (·.val)))]

/-- An import batch. -/
def batchJson (b : ImportBatch) : Json :=
  Json.mkObj [
    ("id", b.id.val), ("profile", b.profile), ("filename", jopt b.filename),
    ("account", jopt (b.account.map (·.val))), ("at", b.stamp),
    ("total", jint b.total), ("duplicates", jint b.duplicates)]

/-- A receipt. -/
def attachmentJson (a : Attachment) : Json :=
  Json.mkObj [("sha256", a.sha256), ("mime", a.mime), ("bytes", jint a.bytes),
              ("origName", jopt a.origName), ("createdAt", a.createdAt)]

/-- A rule. -/
def ruleJson (r : Rule) : Json :=
  Json.mkObj [
    ("id", r.id.val), ("name", r.name), ("filter", r.filterSrc),
    ("setAccount", jopt r.setAccount),
    ("addLabels", Json.arr (r.addLabels.map Json.str).toArray),
    ("setParty", jopt r.setParty), ("priority", jint r.priority)]

/-- An API token, never including the secret. -/
def tokenJson (t : ApiToken) : Json :=
  Json.mkObj [
    ("id", t.id.val), ("name", t.name), ("scopes", toString t.scopes),
    ("createdAt", t.createdAt), ("lastUsedAt", jopt t.lastUsedAt),
    ("expiresAt", jopt t.expiresAt)]

/-- A revision. -/
def revisionJson (r : Txns.Revision) : Json :=
  Json.mkObj [("seq", jint r.seq), ("at", r.stamp), ("actor", r.actor),
              ("kind", r.kind), ("patch", r.patch)]

/--
A claim: what is expected to pass between two accounts, and by when.

The two accounts are given as names *and* as owners, because a claim is read as
"who owes whom" far more often than as "which account to which account", and
resolving that on the client would mean shipping the account list to do it.
-/
def claimJson (e : NameEnv) (t : Transaction) : Json :=
  let amount := Pendings.amount t
  let payer := Pendings.payer? t
  let receiver := Pendings.receiver? t
  Json.mkObj [
    ("id", t.id.val), ("due", t.date.toIso), ("state", t.state.toString),
    ("narration", t.narration),
    ("amount", amountJson amount),
    ("fromAccount", jopt (payer.map e.account)),
    ("from", jopt (payer.map e.ownerName)),
    ("toAccount", jopt (receiver.map e.account)),
    ("to", jopt (receiver.map e.ownerName)),
    ("mineToCollect", Json.bool ((receiver.map (fun a => e.owner a == Party.selfId)).getD false)),
    ("labels", Json.arr (t.labels.map (fun l => Json.str (e.label l))).toArray),
    ("settledBy", jopt ((t.postings.findSome? (·.origin))))]

/-- One person a budget is divided among, and where their share lands. -/
def participantJson (p : Participant) : Json :=
  Json.mkObj [
    ("owner", p.owner.val), ("name", p.name), ("account", p.account),
    ("weight", Json.num (JsonNumber.fromNat p.weight)), ("mine", Json.bool p.mine)]

/-- Where one person stands in a budget: positive means they owe the group. -/
def standingJson (s : Standing) : Json :=
  Json.mkObj [
    ("owner", s.owner.val), ("name", s.name), ("amount", amountJson s.amount),
    ("owes", Json.bool (s.amount.minor > 0))]

/-! ## Realms, invites and sync

What the node's own half of the API says about itself. A realm is the unit of
sharing — one key, one set of members, one thing other people can be let into —
and everything here is a way of looking at one: who is in it, whether this node
can still open it, and how far the order it belongs to has got.
-/

/-- What one round of sync came to. -/
structure Round where
  /-- When it ran. `at` is a keyword, so the field is `ran` and the wire says "at". -/
  ran : String := ""
  /-- Entries taken in and applied. -/
  applied : Nat := 0
  /-- Entries carrying nothing this node holds a key for. -/
  unreadable : Nat := 0
  /-- Entries that were coherent bytes saying incoherent things. -/
  rejected : Nat := 0
  /-- Local events offered and accepted. -/
  pushed : Nat := 0
  /-- Times the head had moved under us. -/
  conflicts : Nat := 0
  /-- Where the remote order stands for this node now. -/
  seq : Nat := 0
  /-- Why the round stopped early, or empty when it did not. -/
  trouble : String := ""
  deriving Inhabited

/-- Where this store syncs, and how far it has got. -/
structure SyncStatus where
  /-- Whether there is a sequencer at all. Everything below is empty when not. -/
  configured : Bool := false
  /-- Base URL of the sequencer. -/
  sequencer : String := ""
  /-- Which ledger on it this store is. -/
  ledger : String := ""
  /-- This node's member id: the hex of its signing key. -/
  member : String := ""
  /-- This node's agreement key, which realm keys are wrapped to. -/
  boxPk : String := ""
  /-- The last position in the remote order this node has taken in. -/
  seq : Nat := 0
  /-- The hash of the entry at that position. -/
  hash : String := ""
  /-- How many local events are waiting to be offered. -/
  pending : Nat := 0
  /-- How many events the local log holds. -/
  events : Nat := 0
  /-- Realms this node missed a part of, and whose projection is therefore not comparable. -/
  unverified : List String := []
  /-- What the last round this process ran came to, if it has run one. -/
  lastRound : Option Round := none
  deriving Inhabited

/-- One member of a realm: who they are here, and what they may do. -/
def realmMemberJson (m : Member) (role : RealmRole) (mine : Bool) : Json :=
  Json.mkObj [("id", m.id.val), ("name", m.name), ("role", toString role),
              ("mine", Json.bool mine)]

/-- The member record for an id, or a stand-in for one the ledger has forgotten. -/
def memberOr (s : State) (id : MemberId) : Member :=
  (s.member? id).getD { id, name := id.val }

/--
The budget a realm was made for, when it was made for one.

A budget record names the realm its admins decide about it in, and the equity
account that holds it is asked for inside that realm. It used to be asked for by
name across the whole ledger, which is the first account of that name in id
order — so a purse somebody had called `Budget.Sicily` in a realm of their own
could answer for a budget held somewhere else entirely, and name this realm as
the one that budget was made for.
-/
def budgetOfRealm (s : State) (r : Realm) : Option String :=
  (sortedValues s.budgets).findSome? fun b =>
    if b.realm == r.id && (s.accountByNameIn? r.id b.budget.name).isSome then
      some (Budget.shortName b.budget)
    else none

/--
A realm: who is in it, which generation of its key it is on, and whether this
node still holds that key.

`hasKey` is about this node and not about the realm. A realm whose generation
has moved past the newest key here is one this node has been put out of, and
saying so is the difference between "nothing has been written lately" and "you
can no longer read what is being written".

`unverified` is the other half of the same honesty. It is true when some entry
of the shared order carried a part in this realm that this node could not open,
so what is shown of the realm is a fold *around* a hole: a node that was revoked
and let back in, or one that joined without a usable checkpoint, has exactly
this. Such a realm cannot have a checkpoint published for it and cannot have
anybody else's checked against it, and a reader who is not told so is a reader
being shown a partial ledger as though it were the ledger.
-/
def realmJson (s : State) (me : MemberId) (r : Realm) (hasKey : Bool)
    (unverified : Bool := false) : Json :=
  Json.mkObj [
    ("id", r.id.val), ("name", r.name),
    ("generation", Json.num (JsonNumber.fromNat r.generation)),
    ("hasKey", Json.bool hasKey), ("unverified", Json.bool unverified),
    ("admin", Json.bool (r.isAdmin me)),
    ("budget", jopt (budgetOfRealm s r)),
    ("members", Json.arr (r.members.map fun (id, role) =>
      realmMemberJson (memberOr s id) role (id == me)).toArray)]

/--
A realm's membership, seen from both sides.

The ledger says who is in the realm; the sequencer says who holds a key for it,
which is what decides whether they can read a word of it. `granted` is null when
nobody was asked, because an empty list would say something much stronger.
-/
def realmMembersJson (s : State) (me : MemberId) (r : Realm) (granted : Option (Array String)) :
    Json :=
  Json.mkObj [
    ("realm", r.id.val), ("name", r.name),
    ("members", Json.arr (r.members.map fun (m, role) =>
      realmMemberJson (memberOr s m) role (m == me)).toArray),
    ("granted", match granted with
                | some ms => Json.arr (ms.map Json.str)
                | none => Json.null)]

/-- An invite: who it is for, what it lets them do, and the link that redeems it. -/
def inviteJson (r : Realm) (who role expires link : String) : Json :=
  Json.mkObj [
    ("realm", r.id.val), ("name", r.name), ("for", who), ("role", role),
    ("expires", expires), ("link", link)]

/-- What one round of sync came to. -/
def roundJson (r : Round) : Json :=
  let jnat (n : Nat) : Json := Json.num (JsonNumber.fromNat n)
  Json.mkObj [
    ("at", r.ran), ("applied", jnat r.applied), ("unreadable", jnat r.unreadable),
    ("rejected", jnat r.rejected), ("pushed", jnat r.pushed),
    ("conflicts", jnat r.conflicts), ("seq", jnat r.seq), ("trouble", r.trouble)]

/-- Where this store syncs, and how far it has got. -/
def syncStatusJson (s : SyncStatus) : Json :=
  let jnat (n : Nat) : Json := Json.num (JsonNumber.fromNat n)
  Json.mkObj [
    ("configured", Json.bool s.configured), ("sequencer", s.sequencer),
    ("ledger", s.ledger), ("member", s.member), ("boxPk", s.boxPk),
    ("seq", jnat s.seq), ("hash", s.hash), ("pending", jnat s.pending),
    ("events", jnat s.events),
    ("unverified", Json.arr (s.unverified.map Json.str).toArray),
    ("lastRound", match s.lastRound with | some r => roundJson r | none => Json.null)]

/-! ## Parsing incoming transactions -/

private def getStr? (j : Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption

private def getInt? (j : Json) (k : String) : Option Int :=
  (j.getObjValAs? Int k).toOption

/--
Reads a posting from JSON. `account` may be a name or an id; the account is
created if it does not exist yet, which is what makes the CLI pleasant to use.
Amounts arrive either as exact `minor` integers or as a decimal string.
-/
def postingOfJson (ctx : Ctx) (j : Json) : IO Posting := do
  let accountName := (getStr? j "account").getD ""
  if accountName.isEmpty then throw <| IO.userError "posting needs an account"
  let account ← Accounts.ensure ctx accountName
  let commodity := Commodity.ofCode ((getStr? j "commodity").getD "EUR")
  let amount ←
    match getInt? j "minor" with
    | some m => pure (Amount.mk commodity m)
    | none =>
      match getStr? j "amount" with
      | some s => IO.ofExcept (Amount.parse s commodity)
      | none => throw <| IO.userError "posting needs an amount or minor"
  let party ← match getStr? j "party" with
    | some p => do let pt ← Parties.ensure ctx p; pure (some pt.id)
    | none => pure none
  return { account := account.id, amount, party, note := getStr? j "note" }

/--
Applies a partial edit to an existing transaction: only the fields actually
present in the JSON are touched.

This is what `PATCH` means, and getting it wrong here is dangerous rather than
merely surprising — a body of `{"labels": ["food"]}` interpreted as a full
replacement leaves a transaction with no postings at all, which balances
vacuously and so passes validation. Provenance is deliberately kept: an edit
does not turn an imported entry into a manual one, and who made the change is
already recorded in the revision log.
-/
def txnPatch (ctx : Ctx) (old : Transaction) (j : Json) : IO Transaction := do
  let date := ((getStr? j "date").bind Date.ofIso?).getD old.date
  -- An explicit `null` clears the payee; an absent key leaves it alone.
  let payee := if (j.getObjVal? "payee").toOption.isSome then getStr? j "payee" else old.payee
  let narration := (getStr? j "narration").getD old.narration
  let postings ←
    match (j.getObjValAs? (Array Json) "postings").toOption with
    | some ps => ps.toList.mapM (postingOfJson ctx)
    | none => pure old.postings
  let labels ←
    match (j.getObjValAs? (Array String) "labels").toOption with
    | some ls => ls.toList.mapM fun n => do return (← Labels.ensure ctx n).id
    | none => pure old.labels
  let attachments :=
    match (j.getObjValAs? (Array String) "attachments").toOption with
    | some a => a.toList
    | none => old.attachments
  let merged : Transaction :=
    { old with date, payee, narration, postings, labels, attachments }
  match getStr? j "balanceInto" with
  | some name => do
    let acc ← Accounts.ensure ctx name
    return merged.autoBalance acc.id
  | none => return merged

/--
Reads a transaction from JSON. If the postings do not balance and
`balanceInto` names an account, the remainder is booked there; otherwise the
transaction is rejected.
-/
def txnOfJson (ctx : Ctx) (j : Json) (actor : String) : IO Transaction := do
  let date ←
    match (getStr? j "date").bind Date.ofIso? with
    | some d => pure d
    | none => Date.today
  let postingsJson := (j.getObjValAs? (Array Json) "postings").toOption.getD #[]
  let postings ← postingsJson.toList.mapM (postingOfJson ctx)
  let labels ← ((j.getObjValAs? (Array String) "labels").toOption.getD #[]).toList.mapM
    fun n => do return (← Labels.ensure ctx n).id
  let id := (getStr? j "id").getD (← freshId)
  let base : Transaction :=
    { id := ⟨id⟩, date, payee := getStr? j "payee",
      narration := (getStr? j "narration").getD "",
      postings, labels, source := .manual actor,
      attachments := ((j.getObjValAs? (Array String) "attachments").toOption.getD #[]).toList }
  match getStr? j "balanceInto" with
  | some name => do
    let acc ← Accounts.ensure ctx name
    return base.autoBalance acc.id
  | none => return base

/--
A budget with what it still holds, where everybody stands, and what has been
asked of them.

`outstanding` is the part nobody has been given yet: money paid out and not yet
decided about. It is the whole reason a budget is worth naming, and it is also
what has to reach zero before a settlement can be planned at all.
-/
def budgetJson (e : NameEnv) (b : Budget) (outstanding allocated : Amount) (costs : Nat)
    (among : Array Participant) (standings : Array Standing) (claims : Array Transaction) :
    Json :=
  Json.mkObj [
    ("id", Json.str b.id.val), ("name", Json.str b.name),
    ("shortName", Json.str (Budget.shortName b)),
    ("note", Json.str (b.note.getD "")), ("closed", Json.bool b.closed),
    ("outstanding", amountJson outstanding),
    ("allocated", amountJson allocated),
    ("costs", Json.num (JsonNumber.fromNat costs)),
    ("among", Json.arr (among.map participantJson)),
    ("standings", Json.arr (standings.map standingJson)),
    ("claims", Json.arr (claims.map (claimJson e)))]

end Wire
end Resources
