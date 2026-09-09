import Resources.Import.Staging
import Resources.Invoice.Render
import Resources.Store.Blob
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
    ("expiresAt", jopt t.expiresAt),
    ("guest", Json.bool t.guest.isSome),
    ("owner", jopt (t.guest.map (·.owner.val))),
    ("budget", jopt (t.guest.map (·.budget.val)))]

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

/-! ## The guest view

What somebody holding a share link may see. It is a separate shape rather than a
filtered version of the ordinary one, because "filtered" is a property of the
code that does the filtering, and this has to be a property of the payload: no
account names of yours, no other budgets, no contacts, no ids that address
anything outside the budget the link names.
-/

/-- One cost, as the person you shared it with may see it. -/
def guestCostJson (t : Transaction) (amount : Amount) (paidBy : String) (mine : Bool) : Json :=
  Json.mkObj [
    ("id", t.id.val), ("date", t.date.toIso),
    ("what", if (t.payee.getD "").trimAscii.isEmpty then t.narration else t.payee.getD ""),
    ("amount", amountJson amount), ("paidBy", paidBy), ("mine", Json.bool mine)]

/-- A claim, without naming anybody's accounts. -/
def guestClaimJson (e : NameEnv) (t : Transaction) : Json :=
  Json.mkObj [
    ("id", t.id.val), ("due", t.date.toIso), ("state", t.state.toString),
    ("amount", amountJson (Pendings.amount t)),
    ("from", jopt ((Pendings.payer? t).map e.ownerName)),
    ("to", jopt ((Pendings.receiver? t).map e.ownerName))]

/-- A budget as a guest sees it: the costs, where everybody stands, what is asked. -/
def guestJson (b : Budget) (who : String) (outstanding total : Amount) (costs : Array Json)
    (standings : Array Standing) (claims : Array Json) : Json :=
  Json.mkObj [
    ("budget", Budget.shortName b), ("note", Json.str (b.note.getD "")),
    ("closed", Json.bool b.closed),
    ("you", who),
    ("total", amountJson total),
    ("undivided", amountJson outstanding),
    ("costs", Json.arr costs),
    ("standings", Json.arr (standings.map standingJson)),
    ("claims", Json.arr claims)]

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
