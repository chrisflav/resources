import Resources.Api.Routes

/-!
# TypeScript type generation

`resources gen-types` writes `web/src/types.ts`. The types are derived by
running the real wire encoders over representative values and reading the shape
off the resulting JSON — so they cannot drift from what the server actually
sends. Renaming a field in `Wire` and forgetting the client is a compile error
in the web build rather than an `undefined` at runtime.
-/

open Lean

namespace Resources
namespace Api
namespace TsGen

/-- The TypeScript type of a JSON value, with objects expanded inline. -/
partial def typeOf (indent : String) : Json → String
  | .str _ => "string"
  | .num _ => "number"
  | .bool _ => "boolean"
  | .null => "string | null"
  | .arr a => if h : 0 < a.size then typeOf indent a[0] ++ "[]" else "unknown[]"
  | .obj kvs =>
    let fields := kvs.toArray.map fun (k, v) =>
      s!"{indent}  {k}: {typeOf (indent ++ "  ") v}"
    "{\n" ++ String.intercalate "\n" fields.toList ++ "\n" ++ indent ++ "}"

/-- Emits one exported interface, with per-field type overrides for shared shapes. -/
def interfaceOf (name : String) (sample : Json) (overrides : List (String × String) := []) :
    String :=
  match sample with
  | .obj kvs =>
    let fields := kvs.toArray.map fun (k, v) =>
      match overrides.lookup k with
      | some t => s!"  {k}: {t}"
      -- The indent has to match the field's, or a nested object closes its brace
      -- at column zero and silently ends the interface early.
      | none => s!"  {k}: {typeOf "  " v}"
    s!"export interface {name} " ++ "{\n" ++ String.intercalate "\n" fields.toList ++ "\n}\n"
  | other => s!"export type {name} = {typeOf "" other}\n"

/-! ## Representative values

Optional fields are left empty on purpose, so they come out as nullable in the
generated types rather than accidentally looking required.
-/

private def sampleCommodity : Commodity := Commodity.eur
private def sampleDate : Date := (Date.ofIso? "2026-01-01").getD default

private def sampleAccount : Account :=
  { id := ⟨"acc"⟩, name := "Assets.Bank.Example", kind := .asset }

private def samplePartner : Party :=
  { id := ⟨"par"⟩, name := "anna", kind := "contact" }

private def samplePosting : Posting :=
  { account := ⟨"acc"⟩, amount := ⟨sampleCommodity, -1234⟩, origin := some "fingerprint" }

private def sampleTxn : Transaction :=
  { id := ⟨"txn"⟩, date := sampleDate, narration := "example",
    postings := [samplePosting], labels := [⟨"lab"⟩], attachments := ["deadbeef"] }

private def samplePurse : Account :=
  { id := ⟨"prs"⟩, name := "Assets.Purse.anna", kind := .asset, owner := samplePartner.id }

private def sampleEnv : Wire.NameEnv :=
  { accounts := #[sampleAccount, samplePurse], labels := #[],
    parties := #[{ id := Party.selfId, name := "me", kind := "self" }, samplePartner] }

private def sampleClaim : Transaction :=
  { id := ⟨"clm"⟩, date := sampleDate, narration := "anna → me for Example"
    state := .pending
    postings :=
      [{ account := sampleAccount.id, amount := ⟨sampleCommodity, 13583⟩, tag := some "claim" },
       { account := samplePurse.id, amount := ⟨sampleCommodity, -13583⟩, tag := some "claim" }] }

private def sampleRaw : RawRecord :=
  { date := sampleDate, amount := ⟨sampleCommodity, -1234⟩ }

private def sampleStaged : StagedEntry :=
  { id := ⟨"stg"⟩, batch := ⟨"bat"⟩, fingerprint := "abc", raw := sampleRaw,
    state := "new", suggestedAccount := none, txnId := none }

private def sampleBatch : ImportBatch :=
  { id := ⟨"bat"⟩, profile := "dkb", filename := none, account := none,
    stamp := "2026-01-01T00:00:00", total := 0, duplicates := 0 }

private def sampleAttachment : Attachment :=
  { sha256 := "deadbeef", mime := "application/pdf", bytes := 0, origName := none,
    createdAt := "2026-01-01T00:00:00" }

private def sampleRule : Rule :=
  { id := ⟨"rul"⟩, name := "example", filterSrc := "payee:X", filter := .all,
    setAccount := none, addLabels := ["food"], setParty := none, priority := 0 }

private def sampleToken : ApiToken :=
  { id := ⟨"tok"⟩, name := "cli", scopes := Scopes.ofList [.read], createdAt := "2026-01-01",
    lastUsedAt := none, expiresAt := none }

private def sampleRevision : Txns.Revision :=
  { seq := 1, stamp := "2026-01-01T00:00:00", actor := "cli", kind := "create", patch := "{}" }

private def sampleInvoice : Invoice :=
  { id := ⟨"inv"⟩, number := "2026-0001", issued := sampleDate, due := sampleDate,
    payerId := none, payerName := "ACME", commodity := sampleCommodity,
    reference := "RF00", status := .draft, note := none, settledTxn := none,
    payment := .epc "Me" "DE00" none, sourceAccount := some "Expenses.Trips.Example",
    budgetId := some ⟨"bud"⟩, pendingTxn := some ⟨"clm"⟩
    lines := [{ description := "Consulting", qtyMilli := 1000,
                unitPrice := ⟨sampleCommodity, 100⟩, taxBp := 1900 }] }

private def sampleBudget : Budget :=
  { id := ⟨"bud"⟩, name := "Budget.Example", note := none, closed := false }

private def sampleParticipant : Participant :=
  { owner := samplePartner.id, name := "anna", account := "Assets.Purse.anna" }

private def sampleStanding : Standing :=
  { owner := samplePartner.id, name := "anna", amount := ⟨sampleCommodity, 13583⟩ }

private def sampleRealm : Realm :=
  { id := ⟨"rlm"⟩, name := "Sicily", generation := 1,
    members := [(Member.selfId, .admin), (⟨"b0"⟩, .viewer)] }

private def sampleRealmState : State :=
  { State.init with realms := State.init.realms.insert sampleRealm.id.val sampleRealm }

private def sampleRound : Wire.Round :=
  { ran := "2026-01-01T00:00:00", applied := 2, pushed := 1, seq := 41 }

private def sampleSyncStatus : Wire.SyncStatus :=
  { configured := true, sequencer := "https://seq.example", ledger := "home",
    member := "3f2a", boxPk := "9c1d", seq := 41, hash := "deadbeef", pending := 0,
    events := 128, lastRound := some sampleRound }

private def sampleInvoiceLines : Array Json :=
  (((Invoice.toJson sampleInvoice).getObjValAs? (Array Json) "lines").toOption).getD #[]

private def samplePage : Json :=
  Json.mkObj [
    ("total", Json.num 0), ("limit", Json.num 0), ("offset", Json.num 0),
    ("filter", Json.str "*"),
    ("items", Json.arr #[Wire.txnJson sampleEnv sampleTxn])]

/-- The complete generated module. -/
def module : String :=
  let header :=
    "// Generated by `resources gen-types`. Do not edit.\n" ++
    "//\n" ++
    "// These types are read off the JSON that the Lean wire encoders actually\n" ++
    "// produce, so they cannot drift from the server. Money is always exact\n" ++
    "// integer minor units; never parse it as a float.\n\n"
  String.intercalate "\n" [
    header,
    interfaceOf "Amount" (Wire.amountJson ⟨sampleCommodity, -1234⟩),
    interfaceOf "Account" (Wire.accountJson sampleEnv sampleAccount),
    interfaceOf "Label" (Wire.labelJson { id := ⟨"lab"⟩, name := "food" }),
    interfaceOf "Party" (Wire.partyJson { id := ⟨"par"⟩, name := "REWE" }),
    interfaceOf "Posting" (Wire.postingJson sampleEnv samplePosting) [("amount", "Amount")],
    interfaceOf "Headline"
      (((Wire.txnJson sampleEnv sampleTxn).getObjVal? "headline").toOption.getD Json.null)
      [("amount", "Amount")],
    interfaceOf "Transaction" (Wire.txnJson sampleEnv sampleTxn)
      [("postings", "Posting[]"), ("headline", "Headline | null")],
    interfaceOf "TransactionPage" samplePage [("items", "Transaction[]")],
    interfaceOf "Balance"
      (Wire.balanceJson { account := "Assets", commodity := "EUR", minor := 0 }),
    interfaceOf "StagedEntry" (Wire.stagedJson sampleStaged) [("amount", "Amount")],
    interfaceOf "ImportBatch" (Wire.batchJson sampleBatch),
    interfaceOf "Attachment" (Wire.attachmentJson sampleAttachment),
    interfaceOf "LineItem"
      (Wire.lineItemJson { description := "Haslikuchen", qty := some 2
                           amount := ⟨sampleCommodity, 1200⟩ }) [("amount", "Amount")],
    interfaceOf "Rule" (Wire.ruleJson sampleRule),
    interfaceOf "ApiToken" (Wire.tokenJson sampleToken),
    interfaceOf "Revision" (Wire.revisionJson sampleRevision),
    interfaceOf "InvoiceLine"
      (sampleInvoiceLines[0]?.getD Json.null),
    interfaceOf "Invoice" (Invoice.toJson sampleInvoice) [("lines", "InvoiceLine[]")],
    interfaceOf "Claim" (Wire.claimJson sampleEnv sampleClaim) [("amount", "Amount")],
    interfaceOf "Participant" (Wire.participantJson sampleParticipant),
    interfaceOf "Standing" (Wire.standingJson sampleStanding) [("amount", "Amount")],
    interfaceOf "Budget"
      (Wire.budgetJson sampleEnv sampleBudget ⟨sampleCommodity, 0⟩ ⟨sampleCommodity, 13583⟩ 2
        #[sampleParticipant] #[sampleStanding] #[sampleClaim])
      [("outstanding", "Amount"), ("allocated", "Amount"), ("among", "Participant[]"),
       ("standings", "Standing[]"), ("claims", "Claim[]")],
    interfaceOf "RealmMember"
      (Wire.realmMemberJson { id := Member.selfId, name := "me" } .admin true),
    interfaceOf "Realm" (Wire.realmJson sampleRealmState Member.selfId sampleRealm true false)
      [("members", "RealmMember[]")],
    interfaceOf "RealmMembers"
      (Wire.realmMembersJson sampleRealmState Member.selfId sampleRealm (some #[Member.selfId.val]))
      [("members", "RealmMember[]"), ("granted", "string[] | null")],
    interfaceOf "Invite"
      (Wire.inviteJson sampleRealm "anna" "viewer" "2026-01-15"
        "https://seq.example/join/#abc"),
    interfaceOf "Round" (Wire.roundJson sampleRound),
    interfaceOf "SyncStatus" (Wire.syncStatusJson sampleSyncStatus)
      [("unverified", "string[]"), ("lastRound", "Round | null")]]

end TsGen
end Api
end Resources
