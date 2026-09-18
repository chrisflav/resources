import Resources.Node.Sync

/-!
# Putting somebody out, and moving a realm onto a new key

Two commands, one procedure. `revoke` takes a member's grant away and re-keys
the realm around them; `rotate` re-keys it without taking anything away, which
is what you do when a key has been on a laptop that was lost, or on a schedule.

## Three places a generation is written

A realm's generation exists three times over, and this file is where the three
are made to agree:

* on the **sequencer**, as `realm.generation`, which is what every append is
  checked against — a part sealed under the old number is refused from the
  moment it moves;
* in the **keyring**, as the generation a key is filed under, which is what the
  next envelope is sealed with;
* in the **log**, as `Realm.generation`, which is what every reader of the
  ledger sees.

The sequencer's is the authority, because it is the one every node consults and
the only one that can be moved atomically. The other two are brought up to it.

## The order, and why it is that order

1. **Push what is pending.** Events composed before the re-key are sealed under
   the key they were composed to be read with, and go out as they are.
2. **Read the membership and the grants**, so that the members to re-grant and
   the keys to wrap for them are known before anything moves.
3. **`DELETE grants/{who}`** on the sequencer. This is the only route that moves
   a generation, and it moves it by one: for a revoke `who` is the member being
   put out, and for a rotation it is this node itself, whose grant is put back a
   moment later. The number it returns is the new generation, and everything
   after this step uses that number rather than one this node worked out.
4. **File a fresh key** in the keyring at that number. Old generations stay:
   what was written under them is still there to be read.
5. **Re-grant this node**, first, because an append with no grant at the current
   generation is refused — including the append in step 7.
6. **Re-grant every remaining holder**, wrapped to the agreement key their member
   record publishes. A member with no agreement key published cannot be wrapped
   for and is reported rather than skipped silently.
7. **Append the operation to the log**: `revoke` or `rotateRealmKey`, plus one
   `rotateRealmKey` for every generation the log is still behind — see below.
8. **Push**, which seals the new entry under the new key.

## What a crash between the steps leaves behind

* **Between 3 and 5** the sequencer has moved and this node holds no grant at
  the new generation. Every append is refused with "no grant on realm R at
  generation g". Running the command again repairs it: it costs one more
  generation, which is cheap, and the alternative — a way to put a generation
  back — would be a way to undo a revoke.
* **Between 5 and 6** this node can write and some of the others cannot read
  what it writes. `resources realm rotate --realm R` re-grants everybody and
  costs a generation.
* **Between 6 and 7** the sequencer is a generation ahead of the log. Nothing is
  broken — the keyring and the sequencer agree, which is what encryption depends
  on — but a reader of the ledger would see a stale number. The next run makes
  it up: step 7 appends as many `rotateRealmKey` operations as it takes to land
  the log exactly on the sequencer's generation, so one interrupted run is
  repaired by the next without anybody having to remember that it happened.
-/

open Lean

namespace Resources
namespace Node

namespace Rekey

/-- What a re-key came to. -/
structure Outcome where
  /-- The realm that moved. -/
  realm : String
  /-- The generation all three records now stand at. -/
  generation : Nat
  /-- The member put out, when one was. -/
  revoked : Option String := none
  /-- The members re-granted at the new generation, this node included. -/
  granted : Array String := #[]
  /-- Members that could not be re-granted, and why. -/
  stranded : Array (String × String) := #[]
  /-- How many entries the push that followed placed. -/
  pushed : Nat := 0
  deriving Inhabited

/--
The agreement key each member of this ledger published, when they really
published it.

`none` for a member whose record carries no key, and for one whose key carries
no signature by their own signing key over it. Those are the same answer on
purpose: the key on a member record is what a realm key would be sealed to, and
one the member did not sign for is one the server supplied. Sealing to it would
hand the realm to whoever wrote it down.
-/
private def boxKeys (s : Session) : IO (Array (String × Option ByteArray)) := do
  let members ← Transport.json s.transport (Transport.get (s.route ["members"]))
  let mut out : Array (String × Option ByteArray) := #[]
  for m in members.getArr?.toOption.getD #[] do
    let id := (Sync.strField? m "member").toLower
    -- `memberKey?` rather than `memberBoxPk?`: a record at a generation below
    -- the highest this node has seen this member publish is a record from
    -- before a rotation, and the sequencer is who it would be coming from.
    out := out.push (id, ← s.memberKey? id (Sync.strField? m "boxPk")
      (Sync.strField? m "boxPkSignature")
      ((m.getObjValAs? Nat "keyGeneration").toOption.getD 0))
  return out

/-- Who holds a grant on a realm, and under which role. -/
private def holders (s : Session) (realm : String) : IO (Array (String × String)) := do
  let grants ← Transport.json s.transport (Transport.get (s.route ["realms", realm, "grants"]))
  return (grants.getArr?.toOption.getD #[]).map fun g =>
    (Sync.strField? g "member", Sync.strField? g "role" "viewer")

/--
Grants one member the realm key at its current generation, wrapped to the key
they signed for and signed by this node.

The signature is what makes the grant worth anything to its holder: they check
it against a key they have a reason to trust before they unwrap, and this node
is that key for everybody it granted.
-/
private def grantTo (s : Session) (realm member : String) (boxPk : Option ByteArray)
    (generation : Nat) (role : String) : IO (Except String Unit) := do
  let some boxPk := boxPk
    | return .error "their member record publishes no agreement key they have signed for"
  let wrapped ← Keys.wrapFor s.keys boxPk realm generation
  let signature := Identity.signHex s.suite s.identity
    (Sync.grantBytes s.ledger realm generation member role wrapped)
  let (code, payload) ← Transport.result s.transport
    (Transport.send "POST" (s.route ["realms", realm, "grants", member])
      (Json.mkObj [("wrappedKey", Json.str (Sync.toBase64 wrapped)), ("role", role),
                   ("grantedBy", s.member), ("signature", signature)]))
  if code == 201 then return .ok () else return .error (Transport.errorOf (.json code payload))

/--
Moves a realm onto a new key, optionally leaving somebody behind.

`dropped` is the member whose grant goes and does not come back. With `none` the
node deletes its own grant instead, which is how a rotation borrows the one
route that moves a generation; its grant is restored at the new generation two
steps later.
-/
def reKey (s : Session) (realm : String) (dropped : Option String) : IO Outcome := do
  if (← Keys.latest s.keys realm).isNone then
    throw <| IO.userError s!"this node holds no key for realm '{realm}', so it cannot re-key it"
  -- 1: what was composed under the old key goes out under the old key.
  discard <| push s
  -- 2: who is here, and what they hold.
  let keys ← boxKeys s
  let held ← holders s realm
  let leaving := dropped.getD s.member
  -- 3: the only route that moves a generation.
  let (code, payload) ← Transport.result s.transport
    (Transport.send "DELETE" (s.route ["realms", realm, "grants", leaving]) Json.null)
  if code != 200 then
    throw <| IO.userError s!"the sequencer would not re-key realm '{realm}': \
                             {Transport.errorOf (.json code payload)}"
  let generation := (payload.getObjValAs? Nat "generation").toOption.getD 0
  -- 4: a fresh key, filed under the number the sequencer chose.
  Keys.put s.keys realm generation (← s.suite.randomBytes s.suite.keySize)
  let mut out : Outcome := { realm, generation, revoked := dropped }
  -- 5: this node first, because the append in step 7 needs it.
  match ← grantTo s realm s.member (some s.identity.boxPk) generation "admin" with
  | .ok _ => out := { out with granted := out.granted.push s.member }
  | .error why =>
    throw <| IO.userError s!"realm '{realm}' is now at generation {generation} and this node \
                             could not take a grant on it: {why}"
  -- 6: everybody who is left.
  for (member, role) in held do
    unless member == s.member || member == leaving do
      let boxPk := ((keys.find? (·.1 == member)).map (·.2)).getD none
      match ← grantTo s realm member boxPk generation role with
      | .ok _ => out := { out with granted := out.granted.push member }
      | .error why => out := { out with stranded := out.stranded.push (member, why) }
  -- 7: the log, brought up to the sequencer in one commit.
  let ctx ← adopt s.ctx
  let stood := (((← ctx.state.get).realm? ⟨realm⟩).map (·.generation)).getD 0
  let first : Op := match dropped with
    | some member => .revoke ⟨realm⟩ ⟨member⟩
    | none => .rotateRealmKey ⟨realm⟩
  let behind := generation - min generation (stood + 1)
  let ops := first :: List.replicate behind (Op.rotateRealmKey ⟨realm⟩)
  discard <| ctx.commit "system" ops (realm := ⟨realm⟩)
  -- 8: and out it goes, sealed under the new key.
  let pushed ← push s
  -- 9: a commitment under the new key. The one published before the re-key is
  -- sealed under a generation nobody who arrives from now on will ever hold, and
  -- a newcomer's only way into a realm whose order predates their key is a
  -- snapshot they can open. See `Node.seedFromOffer`.
  discard <| Checkpoint.publishAll s (← remoteHead s.ctx)
  return { out with pushed := pushed.pushed }

/-- Puts a member out of a realm and re-keys it around them. -/
def revoke (s : Session) (realm member : String) : IO Outcome :=
  reKey s realm (some member)

/-- Moves a realm onto a new key without putting anybody out. -/
def rotate (s : Session) (realm : String) : IO Outcome := reKey s realm none

end Rekey

end Node
end Resources
