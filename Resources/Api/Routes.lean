import Resources.Api.Wire
import Resources.Import.Link
import Resources.Store.Receipts
import Resources.Store.Trips
import Resources.Store.Contacts

/-!
# Routes

The whole API, expressed without reference to any HTTP library. `Std.Http` never
appears here — it only appears in `Resources.Api.Server`, which adapts this to
sockets. That keeps the young part of the stack in one file, and it means the
CLI in local mode executes exactly the same code the server does, rather than a
parallel implementation that can drift.
-/

open Lean

namespace Resources
namespace Api

/-- What a route produces. -/
inductive Reply
  /-- A JSON payload with a status code. -/
  | json (code : Nat) (payload : Json)
  /-- A binary payload: receipts, QR codes, PDFs. -/
  | bytes (code : Nat) (contentType : String) (data : ByteArray)
      (extra : List (String × String) := [])
  deriving Inhabited

namespace Reply

/-- The status code of a reply. -/
def code : Reply → Nat
  | .json c _ => c
  | .bytes c _ _ _ => c

/-- The JSON payload, if this reply carries one. -/
def json? : Reply → Option Json
  | .json _ p => some p
  | .bytes .. => none

end Reply

/-- The caller behind a request, after authentication. -/
structure Caller where
  actor : String
  scopes : Scopes
  /--
  Set when this caller is a share link rather than you.

  A guest is not a caller with fewer scopes. Scopes say what somebody may *do*;
  the question a share link raises is what they may *touch*, and no combination
  of read and write answers it. So a guest is dispatched to a route table of its
  own, and the property that matters — a guest can only ever post to the budget
  its token names and to accounts it owns — is true because there is nowhere
  else to go, rather than because every route remembered to check.
  -/
  guest : Option Guest := none

/-- Everything a route needs from the transport. -/
structure Req where
  /-- Uppercase HTTP method. -/
  method : String
  /-- Decoded path segments below `/api/v1`. -/
  segments : List String
  query : String → Option String
  header : String → Option String
  body : ByteArray

namespace Req

/-- A request with no query, headers or body. -/
def simple (method : String) (segments : List String) : Req :=
  { method, segments, query := fun _ => none, header := fun _ => none, body := ByteArray.empty }

/-- Attaches query parameters from a list. -/
def withQuery (r : Req) (kvs : List (String × String)) : Req :=
  { r with query := fun k => (kvs.find? (·.1 == k)).map (·.2) }

/-- Attaches headers from a list, matched case-insensitively. -/
def withHeaders (r : Req) (kvs : List (String × String)) : Req :=
  { r with header := fun k => (kvs.find? (·.1.toLower == k.toLower)).map (·.2) }

/-- Attaches a JSON body. -/
def withJson (r : Req) (j : Json) : Req := { r with body := j.compress.toUTF8 }

/-- Attaches a raw body. -/
def withBody (r : Req) (b : ByteArray) : Req := { r with body := b }

end Req

private def jint (n : Int) : Json := Json.num (JsonNumber.fromInt n)

private def jopt : Option String → Json
  | some s => Json.str s
  | none => Json.null

private def bodyJson (body : ByteArray) : IO Json := do
  let text := (String.fromUTF8? body).getD ""
  if text.trimAscii.isEmpty then return Json.mkObj []
  IO.ofExcept (Json.parse text)

private def natParam (r : Req) (key : String) (dflt : Nat) : Nat :=
  ((r.query key).bind String.toNat?).getD dflt

private def amountOf (j : Json) (commodity : Commodity) : IO Int := do
  match (j.getObjValAs? Int "minor").toOption with
  | some m => pure m
  | none =>
    match (j.getObjValAs? String "amount").toOption with
    | some a => do return (← IO.ofExcept (Amount.parse a commodity)).minor
    | none => throw <| IO.userError "say how much"

private def dateOf (j : Json) (key : String) : IO Date := do
  match ((j.getObjValAs? String key).toOption).bind Date.ofIso? with
  | some d => pure d
  | none => Date.today

/--
Resolves "who, and where their share lands" into a participant.

The asymmetry between you and everybody else is deliberate and is the whole
arrangement. You keep your own books, so your share has to name the expense
account it belongs to — classifying it is the point. You do not keep theirs, so
theirs lands in an account of their own, their purse unless you say otherwise,
and an account belonging to somebody else is refused outright.
-/
private def participantOf (ctx : Ctx) (j : Json) : IO Participant := do
  let name := ((j.getObjValAs? String "name").toOption.getD "").trimAscii.toString
  let account := ((j.getObjValAs? String "account").toOption.getD "").trimAscii.toString
  let weight := (j.getObjValAs? Nat "weight").toOption.getD 1
  let who ←
    if name.isEmpty || name == "me" then Parties.self ctx else Parties.contact ctx name
  if who.id == Party.selfId then
    if account.isEmpty then
      throw <| IO.userError
        "your own share needs an expense account — that is how it gets classified"
    return { owner := who.id, name := who.name, account, weight }
  let acc ←
    if account.isEmpty then Accounts.purse ctx who
    else Accounts.ensure ctx account none (some who.id)
  if acc.owner != who.id then
    throw <| IO.userError
      s!"{acc.name} belongs to somebody else, so {who.name} cannot have a share there"
  return { owner := who.id, name := who.name, account := acc.name, weight }

/-- Reads a cost somebody else paid for out of their own account. -/
private def contributionOf (ctx : Ctx) (b : Budget) (j : Json) (actor : String) :
    IO Transaction := do
  let who := ((j.getObjValAs? String "who").toOption.getD "").trimAscii.toString
  if who.isEmpty then throw <| IO.userError "say who paid for this"
  let person ← Parties.contact ctx who
  let from_ ←
    match (j.getObjValAs? String "account").toOption with
    | some n => Accounts.ensure ctx n none (some person.id)
    | none => Accounts.purse ctx person
  if from_.owner != person.id then
    throw <| IO.userError s!"{from_.name} does not belong to {person.name}"
  let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
  Budgets.contribute ctx b from_ ⟨commodity, ← amountOf j commodity⟩ (← dateOf j "date")
    ((j.getObjValAs? String "narration").toOption.getD "")
    actor ((j.getObjValAs? String "payee").toOption)

/--
Who a settlement should route through, when the shortest plan is not what is
wanted.

The shortest plan will tell two people who never dealt with each other to pay
one another. Naming a hub says everybody settles with that one person instead —
the same number of transfers in the worst case, and a great deal less
explaining.
-/
private def hubOf (ctx : Ctx) (j : Json) : IO (Option PartyId) := do
  match (j.getObjValAs? String "through").toOption with
  | none => return none
  | some who =>
    if who.trimAscii.isEmpty then return none
    if who == "me" then return some Party.selfId
    return some (← Parties.contact ctx who).id

/--
The whole of what a share link can do.

Four routes. Everything else is a 404, including every route the ordinary table
grows in future, which is the point of writing it out separately.
-/
def guestHandle (ctx : Ctx) (actor : String) (g : Guest) (r : Req) : IO Reply := do
  let some b ← Budgets.get? ctx g.budget.val
    | return .json 404 (Json.mkObj [("error", "this link no longer points at anything")])
  let some who ← Parties.byId? ctx g.owner
    | return .json 404 (Json.mkObj [("error", "this link no longer points at anybody")])
  let acc ← Budgets.account ctx b
  let accounts ← Accounts.list ctx
  let theirs := accounts.filter (·.owner == g.owner)
  -- The reachable set, written down once: this budget, and accounts belonging to
  -- whoever holds the link. Nothing below widens it.
  let reachable (t : Transaction) : Bool :=
    t.postings.all fun p => p.account == acc.id || theirs.any (·.id == p.account)
  match r.method, r.segments with
  | "GET", ["guest"] => do
    let env ← Wire.NameEnv.load ctx
    let costs ← Budgets.costs ctx b
    let mut rows : Array Json := #[]
    let mut total : Int := 0
    for t in costs do
      let amount := t.netIn acc.id "EUR"
      total := total + amount
      -- Whoever's money account the cost came out of paid for it.
      let payer := t.postings.findSome? fun p =>
        match accounts.find? (·.id == p.account) with
        | some a => if a.holdsMoney && p.amount.minor < (0 : Int) then some a.owner else none
        | none => none
      let paidBy := (payer.map env.party).getD "somebody"
      rows := rows.push
        (Wire.guestCostJson t ⟨Commodity.eur, amount⟩ paidBy ((payer == some g.owner)))
    let claims := (← Budgets.claims ctx b).filter fun t =>
      t.postings.any fun p =>
        match accounts.find? (·.id == p.account) with
        | some a => a.owner == g.owner
        | none => false
    return .json 200 (Wire.guestJson b who.name (← Budgets.balance ctx b)
      ⟨Commodity.eur, total⟩ rows (← Budgets.standings ctx b)
      (claims.map (Wire.guestClaimJson env)))
  | "POST", ["guest", "expenses"] => do
    if b.closed then
      throw <| IO.userError "this budget is closed"
    let j ← bodyJson r.body
    let from_ ← Accounts.purse ctx who
    let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
    let t ← Budgets.contribute ctx b from_ ⟨commodity, ← amountOf j commodity⟩
      (← dateOf j "date") ((j.getObjValAs? String "narration").toOption.getD "")
      actor ((j.getObjValAs? String "payee").toOption)
    return .json 201 (Wire.guestCostJson t ⟨commodity, t.netIn acc.id commodity.code⟩
      who.name true)
  | "DELETE", ["guest", "expenses", id] => do
    if b.closed then
      throw <| IO.userError "this budget is closed"
    let some t ← Txns.get? ctx ⟨id⟩
      | return .json 404 (Json.mkObj [("error", "no such expense")])
    if !reachable t then
      return .json 404 (Json.mkObj [("error", "no such expense")])
    -- Once part of it has been divided it is not theirs to withdraw: somebody
    -- has already been told whose that spending was.
    let left := (← Budgets.remaining ctx b).find? fun (x, _) => x.id == t.id
    let whole := t.netIn acc.id "EUR"
    if (left.map (fun (_, n) => n)).getD 0 != whole then
      throw <| IO.userError "this has already been divided up, so it cannot be withdrawn"
    Txns.delete ctx t.id actor
    return .json 200 (Json.mkObj [("deleted", id)])
  | "GET", ["health"] =>
    return .json 200 (Json.mkObj [("status", "ok"), ("guest", Json.bool true)])
  | _, _ => return .json 404 (Json.mkObj [("error", "no such route")])

/--
Handles one request. Errors are thrown as `IO.userError` and turned into 400s by
the caller, so individual routes stay readable.
-/
def handle (ctx : Ctx) (caller : Caller) (r : Req) : IO Reply := do
  let needs (s : Scope) : IO Unit :=
    if caller.scopes.has s then pure ()
    else throw <| IO.userError s!"token lacks the '{s}' scope"
  let ok (j : Json) : IO Reply := return .json 200 j
  let created (j : Json) : IO Reply := return .json 201 j
  let notFound (what : String) : IO Reply :=
    return .json 404 (Json.mkObj [("error", s!"no such {what}")])
  if let some g := caller.guest then
    return ← guestHandle ctx caller.actor g r
  match r.method, r.segments with
  | "GET", ["health"] =>
    ok (Json.mkObj [("status", "ok"), ("schema", jint Schema.targetVersion),
                    ("actor", caller.actor), ("scopes", toString caller.scopes)])

  /- ## Accounts -/
  | "GET", ["accounts"] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    ok (Json.arr ((← Accounts.list ctx).map (Wire.accountJson env)))
  | "POST", ["accounts"] => do
    needs .write
    let j ← bodyJson r.body
    let name := (j.getObjValAs? String "name").toOption.getD ""
    if name.isEmpty then throw <| IO.userError "an account needs a name"
    let kind := ((j.getObjValAs? String "kind").toOption).bind AccountKind.ofString?
    -- Naming an owner is how somebody else's account gets into the ledger. It
    -- is an ordinary asset; the owner is the only thing keeping it out of your
    -- net worth, and it is the only thing that needs to.
    let owner ← match (j.getObjValAs? String "owner").toOption with
      | some who => do
        let person ← Parties.contact ctx who
        pure (some person.id)
      | none => pure none
    let acc ← Accounts.ensure ctx name kind owner
    -- Posting an existing name edits it. Only the fields actually present are
    -- touched, so a partial edit cannot silently wipe an IBAN, and an explicit
    -- kind applies to an account that already exists rather than being ignored.
    let acc := { acc with
      kind := kind.getD acc.kind
      iban := ((j.getObjValAs? String "iban").toOption) <|> acc.iban
      note := ((j.getObjValAs? String "note").toOption) <|> acc.note
      commodity := (((j.getObjValAs? String "commodity").toOption).map Commodity.ofCode)
                     <|> acc.commodity
      owner := owner.getD acc.owner }
    Accounts.update ctx acc
    let env ← Wire.NameEnv.load ctx
    created (Wire.accountJson env acc)
  | "POST", ["accounts", "merge"] => do
    needs .write
    let j ← bodyJson r.body
    let name (k : String) : IO Account := do
      let n := (j.getObjValAs? String k).toOption.getD ""
      match ← Accounts.byName? ctx n with
      | some a => pure a
      | none => throw <| IO.userError s!"no such account: {n}"
    let source ← name "from"
    let target ← name "into"
    let moved ← Accounts.mergeInto ctx source.id target.id caller.actor
    ok (Json.mkObj [("from", source.name), ("into", target.name), ("moved", jint moved)])
  | "DELETE", ["accounts", id] => do
    needs .write
    Accounts.delete ctx ⟨id⟩
    ok (Json.mkObj [("deleted", id)])
  | "GET", ["accounts", name, "balance"] => do
    needs .read
    let asOf := (r.query "at").bind Date.ofIso?
    ok (Json.arr ((← Balances.subtree ctx name asOf).map Wire.balanceJson))

  /- ## Labels and parties -/
  | "GET", ["labels"] => do
    needs .read
    ok (Json.arr ((← Labels.list ctx).map Wire.labelJson))
  | "POST", ["labels"] => do
    needs .write
    let j ← bodyJson r.body
    created (Wire.labelJson (← Labels.ensure ctx ((j.getObjValAs? String "name").toOption.getD "")))
  | "GET", ["contacts", "books"] => do
    needs .read
    ok (Json.arr ((← Contacts.edsBookCounts).map fun (name, n) =>
      Json.mkObj [("name", name), ("contacts", jint n)]))
  | "POST", ["contacts", "source"] => do
    needs .write
    let j ← bodyJson r.body
    let str (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
    let chosen : ContactSource :=
      match str "kind" with
      | "eds" => .eds
      | "files" => .files (str "path")
      | "carddav" =>
        .carddav (str "url") (str "user")
          (((j.getObjValAs? (Array String) "passwordCommand").toOption.getD #[]).toList)
      | _ => .none
    Contacts.saveSource ctx chosen
    ok (Json.mkObj [("source", Contacts.describe chosen)])
  | "GET", ["contacts"] => do
    needs .read
    let source ← Contacts.source ctx
    let people ← try Contacts.all ctx catch _ => pure #[]
    ok (Json.mkObj [
      ("source", Contacts.describe source),
      ("configured", Json.bool (match source with | .none => false | _ => true)),
      ("items", Json.arr (people.map fun c =>
        Json.mkObj [("name", c.name), ("email", jopt c.email), ("iban", jopt c.iban),
                    ("note", jopt c.note)]))])
  | "GET", ["parties"] => do
    needs .read
    -- Counterparties seen in the ledger. People come from `GET /contacts`.
    ok (Json.arr ((← Parties.list ctx).map Wire.partyJson))
  | "POST", ["parties"] => do
    needs .write
    let j ← bodyJson r.body
    let name := (j.getObjValAs? String "name").toOption.getD ""
    if name.isEmpty then throw <| IO.userError "a contact needs a name"
    let p ← Parties.ensure ctx name "contact"
    let p := { p with iban := ((j.getObjValAs? String "iban").toOption) <|> p.iban
                      email := ((j.getObjValAs? String "email").toOption) <|> p.email
                      note := ((j.getObjValAs? String "note").toOption) <|> p.note
                      kind := ((j.getObjValAs? String "kind").toOption).getD "contact" }
    Parties.update ctx p
    created (Wire.partyJson p)

  /- ## Transactions -/
  | "GET", ["transactions"] => do
    needs .read
    let f ← IO.ofExcept (Filter.parse ((r.query "filter").getD ""))
    let sort := Filter.SortSpec.parse ((r.query "sort").getD "-date")
    let limit := natParam r "limit" 100
    let offset := natParam r "offset" 0
    let env ← Wire.NameEnv.load ctx
    let txns ← Txns.list ctx f sort limit offset
    ok (Json.mkObj [
      ("total", jint (← Txns.count ctx f)), ("limit", jint limit), ("offset", jint offset),
      ("filter", f.render),
      ("items", Json.arr (txns.map (Wire.txnJson env)))])
  | "POST", ["transactions"] => do
    needs .write
    let j ← bodyJson r.body
    let t ← Wire.txnOfJson ctx j caller.actor
    match t.validate with
    | .error e => return .json 400 (Json.mkObj [("error", e)])
    | .ok bt =>
      Txns.put ctx bt caller.actor "create"
      created (Wire.txnJson (← Wire.NameEnv.load ctx) bt.val)
  | "GET", ["transactions", "link-proposals"] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    ok (Json.arr ((← Link.proposeTxnPairs ctx).map fun p =>
      Json.mkObj [("parent", Wire.txnJson env p.parent), ("child", Wire.txnJson env p.child),
                  ("reason", p.reason), ("confidence", p.confidence)]))
  | "GET", ["transactions", id] => do
    needs .read
    match ← Txns.get? ctx ⟨id⟩ with
    | none => notFound "transaction"
    | some t => ok (Wire.txnJson (← Wire.NameEnv.load ctx) t)
  | "PATCH", ["transactions", id] => do
    needs .write
    match ← Txns.get? ctx ⟨id⟩ with
    | none => notFound "transaction"
    | some existing =>
      let t ← Wire.txnPatch ctx existing (← bodyJson r.body)
      match t.validate with
      | .error e => return .json 400 (Json.mkObj [("error", e)])
      | .ok bt =>
        Txns.put ctx bt caller.actor "update"
        ok (Wire.txnJson (← Wire.NameEnv.load ctx) bt.val)
  | "DELETE", ["transactions", id] => do
    needs .write
    Txns.delete ctx ⟨id⟩ caller.actor
    ok (Json.mkObj [("deleted", id)])
  | "POST", ["transactions", "link"] => do
    needs .write
    let j ← bodyJson r.body
    let only := (j.getObjValAs? String "confidence").toOption
    let pairs := (← Link.proposeTxnPairs ctx).filter fun p =>
      match only with
      | some c => p.confidence == c
      | none => true
    let created ← Link.linkTxnPairs ctx pairs caller.actor
    ok (Json.mkObj [("merged", jint created.size),
                    ("created", Json.arr (created.map (fun t => Json.str t.val)))])
  | "POST", ["transactions", "split"] => do
    needs .write
    let j ← bodyJson r.body
    let keep := ((j.getObjValAs? Bool "keepShare").toOption).getD true
    -- The people can be listed, or named as a saved group.
    let among ←
      match (j.getObjValAs? String "group").toOption with
      | some g =>
        match ← Groups.byName? ctx g with
        | some grp => pure grp.members
        | none => throw <| IO.userError s!"no such group: {g}"
      | none => pure ((j.getObjValAs? (Array String) "among").toOption.getD #[]).toList
    let ids ←
      match (j.getObjValAs? (Array String) "ids").toOption with
      | some xs => pure (xs.map (fun x => (⟨x⟩ : TxId)))
      | none =>
        let f ← IO.ofExcept (Filter.parse ((j.getObjValAs? String "filter").toOption.getD ""))
        pure ((← Txns.list ctx f {} 10000).map (·.id))
    let done ← Txns.splitAll ctx ids among keep caller.actor
    let env ← Wire.NameEnv.load ctx
    ok (Json.mkObj [("count", jint done.size), ("among", Json.arr (among.map Json.str).toArray),
                    ("items", Json.arr (done.map (Wire.txnJson env)))])
  | "POST", ["transactions", id, "split"] => do
    needs .write
    let j ← bodyJson r.body
    let among := ((j.getObjValAs? (Array String) "among").toOption.getD #[]).toList
    let keep := ((j.getObjValAs? Bool "keepShare").toOption).getD true
    let t ← Txns.split ctx ⟨id⟩ among keep caller.actor
    ok (Wire.txnJson (← Wire.NameEnv.load ctx) t)
  | "GET", ["groups"] => do
    needs .read
    ok (Json.arr ((← Groups.list ctx).map fun g =>
      Json.mkObj [("name", g.name),
                  ("members", Json.arr (g.members.map Json.str).toArray)]))
  | "POST", ["groups"] => do
    needs .write
    let j ← bodyJson r.body
    let g ← Groups.save ctx ((j.getObjValAs? String "name").toOption.getD "")
      (((j.getObjValAs? (Array String) "members").toOption.getD #[]).toList)
    created (Json.mkObj [("name", g.name),
                         ("members", Json.arr (g.members.map Json.str).toArray)])
  | "DELETE", ["groups", name] => do
    needs .write
    Groups.delete ctx name
    ok (Json.mkObj [("deleted", name)])
  | "POST", ["transactions", "move"] => do
    needs .write
    let j ← bodyJson r.body
    let into := (j.getObjValAs? String "into").toOption.getD ""
    if into.isEmpty then throw <| IO.userError "say which account to move them into"
    let ids ←
      match (j.getObjValAs? (Array String) "ids").toOption with
      | some xs => pure (xs.map (fun x => (⟨x⟩ : TxId)))
      | none =>
        let f ← IO.ofExcept (Filter.parse ((j.getObjValAs? String "filter").toOption.getD ""))
        pure ((← Txns.list ctx f {} 10000).map (·.id))
    let funding := ((j.getObjValAs? Bool "funding").toOption).getD false
    let moved ← Txns.moveMany ctx ids into caller.actor funding
    let env ← Wire.NameEnv.load ctx
    ok (Json.mkObj [("into", into), ("count", jint moved.size),
                    ("items", Json.arr (moved.map (Wire.txnJson env)))])
  | "POST", ["transactions", "claim"] => do
    needs .write
    let j ← bodyJson r.body
    let who := (j.getObjValAs? String "who").toOption.getD ""
    if who.isEmpty then throw <| IO.userError "say whose spending this was"
    let into := (← Accounts.purse ctx (← Parties.contact ctx who)).name
    let ids ←
      match (j.getObjValAs? (Array String) "ids").toOption with
      | some xs => pure (xs.map (fun x => (⟨x⟩ : TxId)))
      | none =>
        let f ← IO.ofExcept (Filter.parse ((j.getObjValAs? String "filter").toOption.getD ""))
        return ← (do
          let txns ← Txns.list ctx f {} 100000
          let claimed ← Txns.claim ctx (txns.map (·.id)) into caller.actor
          let env ← Wire.NameEnv.load ctx
          ok (Json.mkObj [("into", into), ("count", jint claimed.size),
                          ("items", Json.arr (claimed.map (Wire.txnJson env)))]))
    let claimed ← Txns.claim ctx ids into caller.actor
    let env ← Wire.NameEnv.load ctx
    ok (Json.mkObj [("into", into), ("count", jint claimed.size),
                    ("items", Json.arr (claimed.map (Wire.txnJson env)))])
  | "POST", ["postings", "tag-fees"] => do
    needs .write
    ok (Json.mkObj [("tagged", jint (← Link.tagFeePostings ctx))])
  | "POST", ["transactions", "merge"] => do
    needs .write
    let j ← bodyJson r.body
    let ids := (j.getObjValAs? (Array String) "ids").toOption.getD #[]
    let cancel := ((j.getObjValAs? (Array String) "cancelIn").toOption.getD #[]).toList
    let merged ← Txns.merge ctx (ids.map (⟨·⟩)) caller.actor
      ((j.getObjValAs? String "payee").toOption)
      ((j.getObjValAs? String "narration").toOption) cancel
    created (Wire.txnJson (← Wire.NameEnv.load ctx) merged)
  | "POST", ["transactions", id, "unmerge"] => do
    needs .write
    let parts ← Txns.unmerge ctx ⟨id⟩ caller.actor
    let env ← Wire.NameEnv.load ctx
    ok (Json.arr (parts.map (Wire.txnJson env)))
  | "GET", ["transactions", id, "revisions"] => do
    needs .read
    ok (Json.arr ((← Txns.revisions ctx ⟨id⟩).map Wire.revisionJson))
  | "POST", ["transactions", id, "attachments"] => do
    needs .write
    let j ← bodyJson r.body
    let sha := (j.getObjValAs? String "sha256").toOption.getD ""
    Blobs.attach ctx ⟨id⟩ sha
    ok (Json.mkObj [("txn", id), ("sha256", sha)])
  | "DELETE", ["transactions", id, "attachments", sha] => do
    needs .write
    Blobs.detach ctx ⟨id⟩ sha
    ok (Json.mkObj [("txn", id), ("detached", sha)])

  /- ## Imports -/
  | "GET", ["imports"] => do
    needs .read
    ok (Json.arr ((← Imports.listBatches ctx).map Wire.batchJson))
  | "GET", ["imports", id, "staged"] => do
    needs .read
    let state := r.query "state"
    ok (Json.arr ((← Imports.listStaged ctx (some ⟨id⟩) state).map Wire.stagedJson))
  | "POST", ["imports"] => do
    needs .import
    -- Query parameters are percent-encoded end to end. Headers are kept as a
    -- fallback, but they cannot carry a non-ASCII account or file name: HTTP
    -- header values are ASCII, and a bank export called `Umsatzübersicht.csv`
    -- makes the server's own parser reject the request before it is routed.
    let profileName := ((r.query "profile") <|> (r.header "x-profile")).getD "auto"
    let accountName := ((r.query "account") <|> (r.header "x-account")).getD ""
    if accountName.isEmpty then
      throw <| IO.userError
        "name the bank account to import into, as ?account= or an X-Account header"
    let account ← Accounts.ensure ctx accountName
    let profiles ← CsvProfile.loadAll (ctx.cfg.dataDir / "profiles")
    let pick ←
      if profileName == "auto" then
        match CsvProfile.detect profiles r.body with
        | some p => pure p
        | none => throw <| IO.userError "no profile parses this file"
      else
        match profiles.find? (·.name == profileName) with
        | some p => pure p
        | none => throw <| IO.userError s!"unknown profile: {profileName}"
    let (records, problems) ← IO.ofExcept (pick.parseRows (pick.enc.decode r.body))
    let (batch, staged) ←
      Imports.stage ctx account.id pick.name ((r.query "filename") <|> (r.header "x-filename"))
        records
    created (Json.mkObj [
      ("batch", Wire.batchJson batch), ("profile", pick.name),
      ("staged", Json.arr (staged.map Wire.stagedJson)),
      ("problems", Json.arr (problems.map Json.str))])
  | "GET", ["imports", id, "proposals"] => do
    needs .read
    let entries ← Imports.listStaged ctx (some ⟨id⟩) (some "new")
    let byId (sid : StagedId) : Json :=
      match entries.find? (fun e => e.id == sid) with
      | some e => Wire.stagedJson e
      | none => Json.null
    ok (Json.arr ((← Link.proposalsFor ctx ⟨id⟩).map fun p =>
      Json.mkObj [("parent", byId p.parent), ("child", byId p.child),
                  ("reason", p.reason), ("confidence", p.confidence)]))
  | "POST", ["imports", id, "promote"] => do
    needs .import
    let j ← bodyJson r.body
    -- `merge: "auto"` promotes each proposed pair as one transaction;
    -- `merge: true` merges everything named in `ids` into one.
    let mergeMode := ((j.getObjValAs? String "merge").toOption).getD ""
    let explicit := (j.getObjValAs? (Array String) "ids").toOption
    let mut merges := 0
    let created' ←
      if mergeMode == "auto" then do
        let (ids', n) ← Link.promoteAuto ctx ⟨id⟩ explicit caller.actor
        merges := n
        pure ids'
      else if mergeMode == "true" then do
        let some xs := explicit
          | throw <| IO.userError "merging a promotion needs the ids to merge"
        let (ids', n) ← Link.promoteGroups ctx #[xs.map (⟨·⟩)] caller.actor
        merges := n
        pure ids'
      else
        match explicit with
        | some xs => Imports.promote ctx (xs.map (⟨·⟩)) caller.actor
        | none => Imports.promoteBatch ctx ⟨id⟩ caller.actor
    let settled ← Invoices.reconcile ctx
    ok (Json.mkObj [
      ("created", Json.arr (created'.map (fun t => Json.str t.val))),
      ("merged", jint merges),
      ("settledInvoices", Json.arr (settled.map (fun (n, _) => Json.str n)))])
  | "POST", ["staged", id, "suggest"] => do
    needs .import
    let j ← bodyJson r.body
    Imports.suggest ctx ⟨id⟩ ((j.getObjValAs? String "account").toOption.getD "")
    ok (Json.mkObj [("staged", id)])
  | "POST", ["staged", "ignore"] => do
    needs .import
    let j ← bodyJson r.body
    let ids := (j.getObjValAs? (Array String) "ids").toOption.getD #[]
    Imports.ignore ctx (ids.map (⟨·⟩))
    ok (Json.mkObj [("ignored", jint ids.size)])

  /- ## Trips -/
  | "GET", ["trips"] => do
    needs .read
    let trips ← Trips.list ctx
    let mut out : Array Json := #[]
    for t in trips do
      let total ← Trips.total ctx t
      out := out.push (Json.mkObj [
        ("name", t.name), ("starts", t.starts.toIso), ("ends", t.ends.toIso),
        ("payer", t.payer), ("label", Trips.label t), ("purse", Trips.purse t),
        ("note", jopt t.note), ("total", Wire.amountJson total),
        ("members", jint (← Trips.members ctx t).size)])
    ok (Json.arr out)
  | "POST", ["trips"] => do
    needs .write
    let j ← bodyJson r.body
    let date (k : String) : IO Date :=
      match ((j.getObjValAs? String k).toOption).bind Date.ofIso? with
      | some d => pure d
      | none => throw <| IO.userError s!"a trip needs an ISO {k} date"
    let t ← Trips.create ctx ((j.getObjValAs? String "name").toOption.getD "")
      (← date "starts") (← date "ends")
      ((j.getObjValAs? String "payer").toOption.getD "")
      ((j.getObjValAs? String "note").toOption)
    created (Json.mkObj [("name", t.name), ("label", Trips.label t),
                         ("purse", Trips.purse t)])
  | "GET", ["trips", name, "suggest"] => do
    needs .read
    let some t ← Trips.byName? ctx name | notFound "trip"
    let env ← Wire.NameEnv.load ctx
    ok (Json.arr ((← Trips.suggest ctx t).map (Wire.txnJson env)))
  | "GET", ["trips", name, "members"] => do
    needs .read
    let some t ← Trips.byName? ctx name | notFound "trip"
    let env ← Wire.NameEnv.load ctx
    ok (Json.arr ((← Trips.members ctx t).map (Wire.txnJson env)))
  | "POST", ["trips", name, "add"] => do
    needs .write
    let some t ← Trips.byName? ctx name | notFound "trip"
    let j ← bodyJson r.body
    let ids := ((j.getObjValAs? (Array String) "ids").toOption.getD #[]).map (fun x => (⟨x⟩ : TxId))
    ok (Json.mkObj [("added", jint (← Trips.add ctx t ids caller.actor))])
  | "POST", ["trips", name, "drop"] => do
    needs .write
    let some t ← Trips.byName? ctx name | notFound "trip"
    let j ← bodyJson r.body
    let ids := ((j.getObjValAs? (Array String) "ids").toOption.getD #[]).map (fun x => (⟨x⟩ : TxId))
    ok (Json.mkObj [("dropped", jint (← Trips.drop ctx t ids caller.actor))])
  | "DELETE", ["trips", name] => do
    needs .write
    Trips.delete ctx name
    ok (Json.mkObj [("deleted", name)])

  /- ## Scanned receipts -/
  | "GET", ["receipts"] => do
    needs .read
    ok (Json.arr ((← Receipts.unattached ctx).map fun s =>
      Json.mkObj [("sha256", s.sha256), ("mime", s.mime), ("origName", jopt s.origName),
                  ("merchant", jopt s.merchant), ("date", jopt (s.date.map (·.toIso))),
                  ("total", match s.total with
                            | some a => Wire.amountJson a
                            | none => Json.null)]))
  | "POST", ["receipts", sha, "extract"] => do
    needs .write
    let e ← Receipts.extract ctx sha
    Receipts.record ctx sha e
    ok (Json.mkObj [
      ("sha256", sha), ("merchant", jopt e.merchant),
      ("date", jopt (e.date.map (·.toIso))),
      ("total", match e.total with | some a => Wire.amountJson a | none => Json.null),
      ("extractor", e.extractor), ("textLength", jint e.rawText.length)])
  | "GET", ["receipts", "proposals"] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    ok (Json.arr ((← Receipts.proposals ctx).map fun m =>
      Json.mkObj [("sha256", m.sha256), ("txn", Wire.txnJson env m.txn),
                  ("reason", m.reason), ("confidence", m.confidence)]))
  | "POST", ["receipts", sha, "cash"] => do
    needs .write
    let j ← bodyJson r.body
    let t ← Receipts.toCashTransaction ctx sha
      ((j.getObjValAs? String "from").toOption.getD "Assets.Cash")
      ((j.getObjValAs? String "into").toOption.getD "Expenses.Unclassified")
      caller.actor
    created (Wire.txnJson (← Wire.NameEnv.load ctx) t)

  /- ## Rules -/
  | "GET", ["rules"] => do
    needs .read
    ok (Json.arr ((← Rules.list ctx).map Wire.ruleJson))
  | "POST", ["rules"] => do
    needs .write
    let j ← bodyJson r.body
    let rule ← Rules.add ctx
      ((j.getObjValAs? String "name").toOption.getD "rule")
      ((j.getObjValAs? String "filter").toOption.getD "*")
      ((j.getObjValAs? String "setAccount").toOption)
      (((j.getObjValAs? (Array String) "addLabels").toOption.getD #[]).toList)
      ((j.getObjValAs? String "setParty").toOption)
      (((j.getObjValAs? Int "priority").toOption).getD 0)
    created (Wire.ruleJson rule)
  | "POST", ["rules", "apply"] => do
    needs .write
    let j ← bodyJson r.body
    let commit := ((j.getObjValAs? Bool "commit").toOption).getD false
    let env ← Wire.NameEnv.load ctx
    let applied ← Rules.applyToLedger ctx caller.actor commit
    ok (Json.mkObj [
      ("committed", Json.bool commit), ("count", jint applied.size),
      ("items", Json.arr (applied.map fun a =>
        Json.mkObj [("txn", Wire.txnJson env a.txn), ("rule", a.rule),
                    ("account", a.account),
                    ("labels", Json.arr (a.labels.map Json.str).toArray)]))])
  | "DELETE", ["rules", id] => do
    needs .write
    Rules.delete ctx id
    ok (Json.mkObj [("deleted", id)])

  /- ## Receipts -/
  | "GET", ["attachments"] => do
    needs .read
    ok (Json.arr ((← Blobs.list ctx).map Wire.attachmentJson))
  | "PUT", ["attachments"] => do
    needs .write
    let mime := (r.header "content-type").getD "application/octet-stream"
    let sha ← Blobs.put ctx r.body mime ((r.query "filename") <|> (r.header "x-filename"))
    match ← Blobs.meta? ctx sha with
    | some m => created (Wire.attachmentJson m)
    | none => created (Json.mkObj [("sha256", sha)])
  | "GET", ["attachments", sha] => do
    needs .read
    match ← Blobs.get? ctx sha, ← Blobs.meta? ctx sha with
    | some data, some info =>
      return .bytes 200 info.mime data
        [("content-disposition", s!"inline; filename=\"{info.origName.getD sha}\""),
         ("cache-control", "public, max-age=31536000, immutable")]
    | _, _ => notFound "attachment"
  | "POST", ["attachments", "gc"] => do
    needs .write
    ok (Json.mkObj [("removed", jint (← Blobs.gc ctx))])

  /- ## Invoices -/
  /- ## Budgets

     A shared payment is a loan from the paying account to an auxiliary budget.
     `lend` and `contribute` fill it, `allocate` decides whose the spending was
     and raises the claims that would square it, and `Pendings.resolve` meets
     one when the money arrives. Whose the spending was and who has paid are
     different questions, so they are different entries. -/
  | "GET", ["budgets"] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    let bs ← Budgets.list ctx
    let mut out : Array Json := #[]
    for b in bs do
      let held ← Budgets.balance ctx b
      let costs ← Budgets.costs ctx b
      out := out.push (Wire.budgetJson env b held (← Budgets.allocated ctx b) costs.size
        (← Budgets.participants ctx b).toArray
        (← Budgets.standings ctx b) (← Budgets.claims ctx b))
    ok (Json.arr out)
  | "GET", ["budgets", name] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    let some b ← Budgets.get? ctx name | notFound "budget"
    let costs ← Budgets.costs ctx b
    ok (Json.mkObj [
      ("budget", Wire.budgetJson env b (← Budgets.balance ctx b) (← Budgets.allocated ctx b)
        costs.size (← Budgets.participants ctx b).toArray
        (← Budgets.standings ctx b) (← Budgets.claims ctx b)),
      ("items", Json.arr (costs.map (Wire.txnJson env)))])
  | "POST", ["budgets"] => do
    needs .write
    let j ← bodyJson r.body
    let name := ((j.getObjValAs? String "name").toOption.getD "").trimAscii.toString
    if name.isEmpty then throw <| IO.userError "a budget needs a name"
    let b ← Budgets.open ctx name ((j.getObjValAs? String "note").toOption)
    -- Saying who shares it up front is the normal case, and it is what stops
    -- there ever being an allocation step: every cost added afterwards is
    -- booked already divided.
    let raw := (j.getObjValAs? (Array Json) "among").toOption.getD #[]
    if !raw.isEmpty then
      let mut among : List Participant := []
      for p in raw do
        among := among ++ [← participantOf ctx p]
      Budgets.setParticipants ctx b among
    -- Naming the costs at the same time is the normal case: you are looking at
    -- them when you decide they are shared.
    let ids := ((j.getObjValAs? (Array String) "transactions").toOption.getD #[]).map
      (fun x => (⟨x⟩ : TxId))
    let lent ← if ids.isEmpty then pure #[] else Budgets.lend ctx b ids caller.actor
    return .json 201 (Json.mkObj [
      ("id", b.id.val), ("name", b.name), ("lent", jint lent.size)])
  | "POST", ["budgets", name, "among"] => do
    needs .write
    let j ← bodyJson r.body
    let some b ← Budgets.get? ctx name | notFound "budget"
    let raw := (j.getObjValAs? (Array Json) "among").toOption.getD #[]
    let mut among : List Participant := []
    for p in raw do
      among := among ++ [← participantOf ctx p]
    -- Recording the rule only. Nothing is divided here: dividing is what
    -- closing the budget does, and it is deliberate.
    Budgets.setParticipants ctx b among
    ok (Json.mkObj [
      ("budget", Json.str b.name),
      ("among", Json.arr ((← Budgets.participants ctx b).map Wire.participantJson).toArray),
      ("undivided", Wire.amountJson (← Budgets.balance ctx b))])
  | "POST", ["budgets", name, "lend"] => do
    needs .write
    let j ← bodyJson r.body
    let some b ← Budgets.get? ctx name | notFound "budget"
    let ids ←
      match (j.getObjValAs? (Array String) "transactions").toOption with
      | some xs => pure (xs.map (fun x => (⟨x⟩ : TxId)))
      | none =>
        match (j.getObjValAs? String "filter").toOption with
        | some src => do
          let f ← IO.ofExcept (Filter.parse src)
          pure ((← Txns.list ctx f {} 10000).map (·.id))
        | none => throw <| IO.userError "name the transactions to lend, or a filter for them"
    let lent ← Budgets.lend ctx b ids caller.actor
    ok (Json.mkObj [("budget", Json.str b.name), ("lent", jint lent.size)])
  | "POST", ["budgets", name, "contribute"] => do
    needs .write
    let j ← bodyJson r.body
    let some b ← Budgets.get? ctx name | notFound "budget"
    let t ← contributionOf ctx b j caller.actor
    let env ← Wire.NameEnv.load ctx
    created (Wire.txnJson env t)
  | "POST", ["budgets", name, "allocate"] => do
    needs .write
    let j ← bodyJson r.body
    let some b ← Budgets.get? ctx name | notFound "budget"
    if b.closed then
      throw <| IO.userError s!"{b.name} is closed; closing it is what divided it"
    let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
    let raw := (j.getObjValAs? (Array Json) "among").toOption.getD #[]
    let mut among : List Participant := []
    for p in raw do
      among := among ++ [← participantOf ctx p]
    -- With the participants already named there is nothing to repeat.
    if among.isEmpty then among ← Budgets.participants ctx b
    if among.isEmpty then throw <| IO.userError "say who to divide this among"
    let hub ← hubOf ctx j
    match ← Budgets.allocate ctx b among caller.actor commodity none hub with
    | none =>
      if !(← Budgets.participants ctx b).isEmpty then
        throw <| IO.userError
          s!"{b.name} has nothing waiting: with its participants named, every cost \
is booked already divided as it goes in"
      throw <| IO.userError
        s!"{b.name} holds nothing undivided; lend some costs into it first"
    | some (t, claims) =>
      let env ← Wire.NameEnv.load ctx
      ok (Json.mkObj [
        ("budget", Json.str b.name), ("txn", Json.str t.id.val),
        ("standings", Json.arr ((← Budgets.standings ctx b commodity).map Wire.standingJson)),
        ("claims", Json.arr (claims.map (Wire.claimJson env)))])
  | "POST", ["budgets", name, "settle"] => do
    needs .write
    let j ← bodyJson r.body
    let some b ← Budgets.get? ctx name | notFound "budget"
    let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
    let raised ← Budgets.settle ctx b caller.actor commodity (← hubOf ctx j)
    let env ← Wire.NameEnv.load ctx
    ok (Json.mkObj [
      ("budget", Json.str b.name),
      ("standings", Json.arr ((← Budgets.standings ctx b commodity).map Wire.standingJson)),
      ("claims", Json.arr (raised.map (Wire.claimJson env)))])
  | "POST", ["budgets", name, "close"] => do
    needs .write
    let j ← bodyJson r.body
    let some b ← Budgets.get? ctx name | notFound "budget"
    let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
    let raw := (j.getObjValAs? (Array Json) "among").toOption.getD #[]
    let among ←
      if raw.isEmpty then pure none
      else do
        let mut ps : List Participant := []
        for p in raw do
          ps := ps ++ [← participantOf ctx p]
        pure (some ps)
    let (divided, claims) ← Budgets.close ctx b caller.actor commodity among (← hubOf ctx j)
    let env ← Wire.NameEnv.load ctx
    ok (Json.mkObj [
      ("budget", Json.str b.name), ("closed", Json.bool true),
      ("division", jopt (divided.map (·.id.val))),
      ("standings", Json.arr ((← Budgets.standings ctx b commodity).map Wire.standingJson)),
      ("claims", Json.arr (claims.map (Wire.claimJson env)))])
  | "POST", ["budgets", name, "reopen"] => do
    needs .write
    let some b ← Budgets.get? ctx name | notFound "budget"
    Budgets.reopen ctx b caller.actor
    ok (Json.mkObj [("budget", Json.str b.name), ("closed", Json.bool false)])
  | "DELETE", ["budgets", name] => do
    needs .write
    let some b ← Budgets.get? ctx name | notFound "budget"
    Budgets.delete ctx b
    ok (Json.mkObj [("deleted", Json.str b.name)])

  /- ## Claims

     A transaction that has not happened. Raised by a settlement or by an
     invoice, met by the entry that actually performed it, voided when it never
     will be. None of them can reach a balance: the `posting` view sees only
     what is posted. -/
  | "GET", ["claims"] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    let f ← IO.ofExcept (Filter.parse ((r.query "filter").getD ""))
    let claims ←
      if (r.query "all").isSome then Pendings.history ctx f (natParam r "limit" 500)
      else Pendings.list ctx f (natParam r "limit" 500)
    ok (Json.arr (claims.map (Wire.claimJson env)))
  | "POST", ["claims"] => do
    needs .write
    let j ← bodyJson r.body
    let env ← Wire.NameEnv.load ctx
    let account (k : String) : IO Account := do
      let n := (j.getObjValAs? String k).toOption.getD ""
      match ← Accounts.byName? ctx n with
      | some a => pure a
      | none => throw <| IO.userError s!"no such account: {n}"
    let payer ← account "from"
    let receiver ← account "to"
    let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
    let minor ← amountOf j commodity
    let due ← dateOf j "due"
    let t ← Pendings.create ctx payer.id receiver.id ⟨commodity, minor⟩ due
      ((j.getObjValAs? String "narration").toOption.getD "") caller.actor
    created (Wire.claimJson env t)
  | "GET", ["claims", id, "candidates"] => do
    needs .read
    let env ← Wire.NameEnv.load ctx
    let some t ← Txns.get? ctx ⟨id⟩ | notFound "claim"
    ok (Json.arr ((← Pendings.candidates ctx t).map (Wire.txnJson env)))
  | "POST", ["claims", id, "resolve"] => do
    needs .write
    let j ← bodyJson r.body
    let some actual := (j.getObjValAs? String "transaction").toOption
      | throw <| IO.userError "say which transaction met this claim"
    let t ← Pendings.resolve ctx ⟨id⟩ ⟨actual⟩ caller.actor
    let env ← Wire.NameEnv.load ctx
    ok (Wire.claimJson env t)
  | "POST", ["claims", id, "void"] => do
    needs .write
    let j ← bodyJson r.body
    let t ← Pendings.void ctx ⟨id⟩ caller.actor ((j.getObjValAs? String "writeOffTo").toOption)
    let env ← Wire.NameEnv.load ctx
    ok (Wire.claimJson env t)

  | "GET", ["invoices"] => do
    needs .read
    ok (Json.arr ((← Invoices.list ctx).map Invoice.toJson))
  | "GET", ["invoices", id] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      let sources ← Invoices.sourcesOf ctx inv.id
      ok (inv.toJson.setObjVal! "sources"
        (Json.arr (sources.map (fun t => Json.str t.val))))
  | "POST", ["invoices"] => do
    needs .write
    let j ← bodyJson r.body
    let today ← Date.today
    let issued := ((j.getObjValAs? String "issued").toOption.bind Date.ofIso?).getD today
    let due := ((j.getObjValAs? String "due").toOption.bind Date.ofIso?).getD (issued.plusDays 14)
    let commodity := Commodity.ofCode ((j.getObjValAs? String "commodity").toOption.getD "EUR")
    let payment :=
      match (j.getObjValAs? String "paymentLink").toOption with
      | some url => PaymentRequest.link url
      | none =>
        PaymentRequest.epc
          ((j.getObjValAs? String "beneficiary").toOption.getD "")
          ((j.getObjValAs? String "iban").toOption.getD "")
          ((j.getObjValAs? String "bic").toOption)
    -- An invoice is a document about a claim: costs that have already been
    -- allocated, and the payment that has not happened yet. It never moves
    -- money and it never divides anything.
    let some name := (j.getObjValAs? String "budget").toOption
      | throw <| IO.userError
          "say which budget to invoice: an invoice is a document about costs already allocated"
    let some b ← Budgets.get? ctx name
      | throw <| IO.userError s!"no such budget: {name}"
    if (← Budgets.claims ctx b).isEmpty then
      throw <| IO.userError
        s!"{name} has nothing outstanding, so there is nothing to invoice"
    let only := ((j.getObjValAs? (Array String) "claims").toOption).map (·.toList)
    let issuedInvoices ← Invoices.forBudget ctx b payment issued due commodity
      ((j.getObjValAs? String "note").toOption) only
    return .json 201 (Json.mkObj [
      ("count", jint issuedInvoices.size),
      ("budget", Json.str b.name),
      ("items", Json.arr (issuedInvoices.map Invoice.toJson))])
  | "POST", ["invoices", id, "status"] => do
    needs .write
    let j ← bodyJson r.body
    let some st := InvoiceStatus.ofString? ((j.getObjValAs? String "status").toOption.getD "")
      | throw <| IO.userError "status must be draft, sent, paid or void"
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      Invoices.setStatus ctx inv.id st
      ok (Json.mkObj [("invoice", inv.number), ("status", st.toString)])
  | "DELETE", ["invoices", id] => do
    needs .write
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      if inv.status != .draft then
        throw <| IO.userError
          "that invoice has left your hands; void it instead so the number stays accounted for"
      Invoices.delete ctx inv.id
      ok (Json.mkObj [("deleted", Json.str inv.number)])
  | "POST", ["invoices", "reconcile"] => do
    needs .write
    ok (Json.arr ((← Invoices.reconcile ctx).map fun (n, t) =>
      Json.mkObj [("invoice", n), ("txn", t.val)]))
  | "GET", ["invoices", id, "qr.svg"] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      match inv.qrPayload with
      | .error e => return .json 400 (Json.mkObj [("error", e)])
      | .ok payload => return .bytes 200 "image/svg+xml" (← Qr.svg payload).toUTF8
  | "GET", ["invoices", id, "qr.txt"] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      match inv.qrPayload with
      | .error e => return .json 400 (Json.mkObj [("error", e)])
      | .ok payload => return .bytes 200 "text/plain; charset=utf-8" (← Qr.ansi payload).toUTF8
  | "GET", ["invoices", id, "qr.png"] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      match inv.qrPayload with
      | .error e => return .json 400 (Json.mkObj [("error", e)])
      | .ok payload => return .bytes 200 "image/png" (← Qr.png payload)
  | "GET", ["invoices", id, "mailto"] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv => ok (Json.mkObj [("mailto", ← Invoices.mailto ctx inv)])
  | "GET", ["invoices", id, "html"] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      let svg : Option String ←
        match inv.qrPayload with
        | .ok payload => try pure (some (← Qr.svg payload)) catch _ => pure none
        | .error _ => pure none
      return .bytes 200 "text/html; charset=utf-8" (Render.html inv svg).toUTF8
  | "GET", ["invoices", id, "pdf"] => do
    needs .read
    match ← Invoices.get? ctx id with
    | none => notFound "invoice"
    | some inv =>
      let tmp : System.FilePath := ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"inv-{← freshId}.pdf"
      Render.pdf inv tmp
      let bytes ← IO.FS.readBinFile tmp
      IO.FS.removeFile tmp
      return .bytes 200 "application/pdf" bytes
        [("content-disposition", s!"inline; filename=\"invoice-{inv.number}.pdf\"")]

  /- ## Reports -/
  | "GET", ["reports", "balances"] => do
    needs .read
    let asOf := (r.query "at").bind Date.ofIso?
    ok (Json.arr ((← Balances.all ctx asOf).map Wire.balanceJson))
  | "GET", ["reports", "people"] => do
    needs .read
    -- What passes between you and everybody else. The balance of somebody's own
    -- accounts already says which way it runs — positive, they owe you — and
    -- what is *outstanding* is the claims, each of which names a specific thing
    -- rather than being aged against the oldest outlay by convention.
    let env ← Wire.NameEnv.load ctx
    let accounts ← Accounts.list ctx
    let balances ← Balances.all ctx
    let claims ← Pendings.list ctx
    let mut out : Array Json := #[]
    for party in ← Parties.list ctx do
      if party.id == Party.selfId then continue
      let theirs := accounts.filter (·.owner == party.id)
      if theirs.isEmpty then continue
      let names := theirs.map (·.name)
      let held := balances.filter (fun e => names.contains e.account)
      let mine := claims.filter fun t =>
        t.postings.any fun p => theirs.any (·.id == p.account)
      let net := held.foldl (fun acc e => acc + e.minor) 0
      if net == 0 && mine.isEmpty then continue
      out := out.push (Json.mkObj [
        ("party", party.id.val), ("name", party.name), ("iban", jopt party.iban),
        ("email", jopt party.email),
        ("net", jint net), ("netText", (Amount.mk Commodity.eur net).digits),
        ("accounts", Json.arr (theirs.map (Wire.accountJson env))),
        ("balances", Json.arr (held.map Wire.balanceJson)),
        ("claims", Json.arr (mine.map (Wire.claimJson env)))])
    ok (Json.arr out)
  | "GET", ["reports", "worth"] => do
    needs .read
    let commodity := (r.query "commodity").getD "EUR"
    let minor ← Balances.netWorth ctx commodity
    ok (Json.mkObj [("commodity", commodity), ("minor", jint minor),
                    ("text", (Amount.mk (Commodity.ofCode commodity) minor).digits)])
  | "GET", ["reports", "trial"] => do
    needs .read
    ok (Json.arr ((← Balances.trial ctx).map Wire.balanceJson))
  | "GET", ["reports", "monthly"] => do
    needs .read
    let rows ← Balances.monthly ctx ((r.query "account").getD "Expenses")
      ((r.query "commodity").getD "EUR")
    ok (Json.arr (rows.map fun (m, v) => Json.mkObj [("month", m), ("minor", jint v)]))

  /- ## Tokens -/
  | "GET", ["tokens"] => do
    needs .admin
    ok (Json.arr ((← Tokens.list ctx).map Wire.tokenJson))
  | "POST", ["tokens"] => do
    needs .admin
    let j ← bodyJson r.body
    -- A share link: one person, one budget. Its scopes are not what confines
    -- it — the guest route table is — so they are not read from the request.
    let guest ←
      match (j.getObjValAs? String "budget").toOption with
      | none => pure none
      | some name => do
        let some b ← Budgets.get? ctx name
          | throw <| IO.userError s!"no such budget: {name}"
        let who := ((j.getObjValAs? String "for").toOption.getD "").trimAscii.toString
        if who.isEmpty then
          throw <| IO.userError "say who the link is for"
        let person ← Parties.contact ctx who
        if person.id == Party.selfId then
          throw <| IO.userError "a share link is for somebody else"
        -- Created up front so the link works before they have spent anything.
        discard <| Accounts.purse ctx person
        pure (some ({ owner := person.id, budget := b.id } : Guest))
    let scopes ←
      if guest.isSome then pure (Scopes.ofList [.read, .write])
      else IO.ofExcept (Scopes.parse ((j.getObjValAs? String "scopes").toOption.getD "read"))
    let (tok, secret) ← Tokens.create ctx
      ((j.getObjValAs? String "name").toOption.getD "token") scopes
      ((j.getObjValAs? String "expires").toOption.bind Date.ofIso?) guest
    created (Json.mkObj [("token", Wire.tokenJson tok), ("secret", secret),
                         ("link", Json.str (if guest.isSome then s!"/s/#{secret}" else ""))])
  | "DELETE", ["tokens", id] => do
    needs .admin
    ok (Json.mkObj [("revoked", Json.bool (← Tokens.revoke ctx id))])

  | _, _ => return .json 404 (Json.mkObj [("error", "no such route")])

/-- Runs a request, turning thrown errors into 400 replies. -/
def handleSafe (ctx : Ctx) (caller : Caller) (r : Req) : IO Reply := do
  try
    handle ctx caller r
  catch e =>
    return .json 400 (Json.mkObj [("error", toString e)])

/-- The caller used when no tokens have been minted yet. -/
def bootstrapCaller : Caller :=
  { actor := "bootstrap", scopes := Scopes.ofList [.read, .write, .import, .admin] }

end Api
end Resources
