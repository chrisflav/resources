import Test.Sync
import Resources.Node.Sync
import Resources.Node.Rekey
import Resources.Node.Blobs
import Resources.Node.Realms

/-!
# Node sync tests

Two nodes and one sequencer, all three in this process, over three real SQLite
files. The sequencer is the one from `Test/Sync.lean` — the same route table,
reached through `Node.Transport.inProcess` rather than a socket — and this time
its verifier is a real one: `Verifier.ofSuite` over the insecure test suite, so
every challenge is answered with a signature that is checked, every envelope is
signed and every join proof is proved.

What the file is for is the property the whole of phase 4 rests on: *two nodes
that have seen the same events hold the same state*. It is asserted twice over,
as `BEq` on the state and as equality of `Encode.hashState`, because those are
two different claims — the first that the values agree, the second that the
bytes a checkpoint would commit to agree.

Around that sit the things that make it hard: a second identity that arrives by
invitation and writes itself into the books, a race for the head that the node
settles by itself and a race it refuses to, an envelope changed in flight, an
entry whose parts are none of this node's business, and a receipt filed in one
realm and attached in another.
-/

open Lean Resources

/-- The primitives under test. Signatures are checked; nothing is secret. -/
private def suite : Node.CryptoSuite := Node.CryptoSuite.insecureForTests

/-- A string field, or the empty string. -/
private def jstr (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

/-- A numeric field, or zero. -/
private def jnat (j : Json) (key : String) : Nat := (j.getObjValAs? Nat key).toOption.getD 0

/-- A boolean field, or false. -/
private def jbool (j : Json) (key : String) : Bool :=
  (j.getObjValAs? Bool key).toOption.getD false

/-- An array field, or empty. -/
private def jarr (j : Json) (key : String) : Array Json :=
  ((j.getObjVal? key).bind Json.getArr?).toOption.getD #[]

/-- One node: its store, its identity, its keys and its way to the sequencer. -/
private structure Peer where
  ctx : Ctx
  identity : Node.Identity
  keys : Node.Keyring
  transport : Node.Transport

/-- Opens a store, gives it an identity, and points it at the sequencer. -/
private def makePeer (root : System.FilePath) (name : String) (seq : Sync.Node) : IO Peer := do
  let cfg := Config.atDir (root / name)
  let opened ← Ctx.open cfg
  let identity ← Node.Identity.create suite (Node.Identity.pathIn cfg) s!"pass-{name}"
  let ctx ← Node.Identity.install opened identity name
  Node.Settings.setMember cfg identity.id
  let keys ← Node.Keys.open suite (Node.Keys.pathIn cfg) s!"pass-{name}" identity
  return { ctx, identity, keys, transport := ← Node.Transport.inProcess suite identity seq }

/-- One part as it arrived, with whatever fields the caller wants replaced. -/
private def partWith (p : Json) (ciphertext cipherHash : Option String) : Json :=
  Json.mkObj [("realm", jstr p "realm"), ("generation", Sync.jnat (jnat p "generation")),
              ("cipherHash", Json.str (cipherHash.getD (jstr p "cipherHash"))),
              ("ciphertext", Json.str (ciphertext.getD (jstr p "ciphertext")))]

/-- One part with a byte of its ciphertext flipped, and its digest left alone. -/
private def tamperPart (p : Json) : Json :=
  match Sync.ofBase64? (jstr p "ciphertext") with
  | some ct =>
    if ct.size == 0 then p
    else
      let flipped := ct.set! (ct.size - 1) (ct[ct.size - 1]! ^^^ 1)
      partWith p (some (Sync.toBase64 flipped)) none
  | none => p

/-- One part whose digest names bytes other than the ones beside it. -/
private def tamperDigest (p : Json) : Json :=
  match Sync.ofHex? (jstr p "cipherHash") with
  | some h =>
    if h.size == 0 then p
    else partWith p none (some (toHex (h.set! (h.size - 1) (h[h.size - 1]! ^^^ 1))))
  | none => p

/-- One entry with each field the caller names replaced, and the rest as it arrived. -/
private def entryWith (e : Json) (parts : Option (Array Json) := none)
    (seq : Option Nat := none) (prevHash : Option String := none) : Json :=
  Json.mkObj [("ledger", jstr e "ledger"), ("seq", Sync.jnat (seq.getD (jnat e "seq"))),
              ("prevHash", Json.str (prevHash.getD (jstr e "prevHash"))),
              ("author", jstr e "author"),
              ("parts", Json.arr (parts.getD (jarr e "parts"))),
              ("signature", jstr e "signature"), ("hash", jstr e "hash")]

/-- The same entry with its first part put through `f`. -/
private def mapFirstPart (f : Json → Json) (e : Json) : Json :=
  let parts := jarr e "parts"
  entryWith e (parts := some (match parts[0]? with
    | none => parts
    | some p => #[f p] ++ parts.extract 1 parts.size))

/-- A fetch's reply with every entry in it put through `f`. -/
private def mapFetch (f : Json → Json) (j : Json) : Json :=
  Json.mkObj [("head", (j.getObjVal? "head").toOption.getD Json.null),
              ("events", Json.arr ((jarr j "events").map f))]

/-- What a checkpoint outcome says about one realm, if it is about that realm. -/
private def outcomeFor (outcomes : Array (String × Node.Checkpoint.Outcome)) (realm : String) :
    Option Node.Checkpoint.Outcome :=
  (outcomes.find? (·.1 == realm)).map (·.2)

/-- The entry a published checkpoint stands at. -/
private def publishedAt : Option Node.Checkpoint.Outcome → Option Nat
  | some (.published p) => some p.seq
  | _ => none

/-- The state hash a published checkpoint commits to. -/
private def publishedHash : Option Node.Checkpoint.Outcome → Option String
  | some (.published p) => some p.stateHash
  | _ => none

/-- Whether a verdict declined to check, which is what a realm nobody granted looks like. -/
private def Resources.Node.Checkpoint.Verdict.isSkipped : Node.Checkpoint.Verdict → Bool
  | .skipped _ => true
  | _ => false

/-- Whether an `Except` refused. -/
private def wasRefused : Except String Unit → Bool
  | .error _ => true
  | .ok _ => false

/--
The POSIX mode of a path, as `stat` prints it, or `none` where there is no
`stat` to ask.

Shelling out because Lean binds `chmod` and not `stat`. The GNU spelling is
tried first and the BSD one second, and a machine with neither answers `none` —
which the checks below read as "not disprovable here" rather than as a failure,
because a test that cannot look must not accuse.
-/
private def modeOf (path : System.FilePath) : IO (Option String) := do
  for args in [#["-c", "%a", path.toString], #["-f", "%Lp", path.toString]] do
    try
      let out ← IO.Process.output { cmd := "stat", args }
      if out.exitCode == 0 then return some out.stdout.trimAscii.toString
    catch _ =>
      pure ()
  return none

/-- Whether a path's mode is the one it should have, where that can be seen. -/
private def hasMode (path : System.FilePath) (expected : String) : IO Bool := do
  return ((← modeOf path).getD expected) == expected

/-- An ISO date, for the transactions below. -/
private def on (iso : String) : Date := (Date.ofIso? iso).getD default

/--
An instant a week from now, in the one shape the sequencer stores.

An invite may no longer be made to stand for ever — the sequencer bounds how far
ahead one may lapse — so the tests ask for a week rather than for the next
century.
-/
private def aWeekFromNow : IO String := do
  let seconds := ((Sync.isoSeconds? (← Sync.Log.utcNow)).getD 0) + 7 * 86400
  let days := seconds / 86400 - (if seconds % 86400 < 0 then 1 else 0)
  let secondOfDay := (seconds - days * 86400).toNat
  let (y, m, d) := Sync.civilFromDays days
  return Sync.isoCanonical y m d (secondOfDay / 3600) (secondOfDay / 60 % 60) (secondOfDay % 60)

-- One long `do` block on purpose — every check after the first depends on the
-- ledger the ones before it built — and one long `do` block is more than the
-- elaborator's default recursion limit is sized for.
set_option maxRecDepth 20000

/--
Two nodes over one sequencer: identities, invites, pushing, pulling, racing and
being lied to.
-/
def nodeTests (r : Report) : IO Report := do
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-node-{← freshId}"
  try
    let log ← Sync.Log.open (Sync.Config.atDir (root / "seq"))
    -- `testOnly`, because the suite behind this verifier recomputes signatures
    -- from the public key: `Sync.Node.make` refuses to build a sequencer over
    -- one that proves nothing unless a test says so in Lean, and the command
    -- line has no spelling for it at all.
    let seq ← Sync.Node.make log (Sync.Verifier.ofSuite suite) (testOnly := true)
    let mut r := r

    /- ## The suite itself -/
    let (pk, sk) ← suite.signKeypair
    r := checkEq r "a signature is the size the suite says it is"
      (suite.sign sk "a message".toUTF8).size suite.signatureSize
    r := check r "a generated key pair signs and verifies"
      (suite.verify pk "a message".toUTF8 (suite.sign sk "a message".toUTF8))
    r := check r "and does not verify a message it did not sign"
      (!suite.verify pk "another message".toUTF8 (suite.sign sk "a message".toUTF8))
    let (boxPk, boxSk) ← suite.boxKeypair
    let realmKey ← suite.randomBytes suite.keySize
    r := checkEq r "a wrapped key comes back to the key it was wrapped for"
      ((suite.unwrapKey boxSk (suite.wrapKey boxPk realmKey)).map toHex) (some (toHex realmKey))
    let nonce ← suite.randomBytes suite.nonceSize
    let sealed := suite.sealPart realmKey nonce "ad".toUTF8 "plaintext".toUTF8
    r := checkEq r "a sealed part opens under the same key, nonce and associated data"
      ((suite.openPart realmKey nonce "ad".toUTF8 sealed).bind String.fromUTF8?)
      (some "plaintext")
    r := check r "and does not open under different associated data"
      (suite.openPart realmKey nonce "other".toUTF8 sealed).isNone

    /- ## Identities -/
    let a ← makePeer root "alice" seq
    r := checkEq r "a member id is the hex of the signing key"
      a.identity.id (toHex a.identity.signPk)
    r := check r "the identity is a member of its own ledger"
      (((← a.ctx.state.get).member? a.identity.memberId).isSome)
    r := check r "and an admin of the self realm"
      ((← a.ctx.state.get).canAdminister a.identity.memberId Realm.selfId)
    r := check r "the store commits as it now"
      (a.ctx.member == a.identity.memberId)
    r := check r "the first member of the log stays 'self', which the core will not remove"
      (((← a.ctx.state.get).member? Member.selfId).isSome)
    let reopened ← Node.Identity.load suite (Node.Identity.pathIn a.ctx.cfg) "pass-alice"
    r := checkEq r "the identity file reopens under its passphrase" reopened.id a.identity.id
    let wrongPass ←
      (do discard <| Node.Identity.load suite (Node.Identity.pathIn a.ctx.cfg) "wrong"
          pure false) <|> pure true
    r := check r "and not under another one" wrongPass

    /- ## How the passphrase was stretched

    The `kdf` object says which stretcher, how many passes and how much memory,
    and all three are read back, checked against a range, used for the derivation
    and bound into the associated data. The last of those is what makes an edited
    `ops` a file that does not open at all rather than one that opens at a cost
    the editor chose — a suite is free to ignore a parameter it does not use, and
    this one does. -/
    let identityFile := Node.Identity.pathIn a.ctx.cfg
    let opens (pass : String) : IO Bool := do
      (do discard <| Node.Identity.load suite identityFile pass; pure true) <|> pure false
    let rewriteKdf (key : String) (value : Json) : IO Unit := do
      let j ← IO.ofExcept (Json.parse (← IO.FS.readFile identityFile))
      let kdf := (Node.objField j "kdf").setObjVal! key value
      IO.FS.writeFile identityFile ((j.setObjVal! "kdf" kdf).pretty ++ "\n")
    let originalFile ← IO.FS.readFile identityFile
    -- One pass more than the file was written with: inside the range this binary
    -- takes, so it is not the range that refuses it.
    rewriteKdf "ops" (Sync.jnat (suite.kdf.ops + 1))
    r := check r "an identity whose 'ops' somebody edited does not open" !(← opens "pass-alice")
    IO.FS.writeFile identityFile originalFile
    r := check r "and the file it was edited from still does" (← opens "pass-alice")
    -- Outside the range, which is the other door: not a cost anybody chose.
    rewriteKdf "ops" (Sync.jnat (Node.maxKdfOps + 1))
    r := check r "an identity asking for more passes than this binary takes does not open"
      !(← opens "pass-alice")
    IO.FS.writeFile identityFile originalFile
    rewriteKdf "mem" (Sync.jnat (Node.minKdfMem - 1))
    r := check r "nor one asking for less memory than a stretcher is worth"
      !(← opens "pass-alice")
    IO.FS.writeFile identityFile originalFile
    rewriteKdf "alg" (Json.str "scrypt")
    r := check r "nor one written with a stretcher this binary cannot compute"
      !(← opens "pass-alice")
    IO.FS.writeFile identityFile originalFile
    -- And a file written at a cost this binary would not have chosen is still
    -- read at the cost it records, which is the whole reason the parameters are
    -- in the file rather than compiled in.
    let elsewhere := a.ctx.cfg.dataDir / "identity-elsewhere.json"
    let otherKdf : Node.KdfParams :=
      { suite.kdf with ops := suite.kdf.ops + 2, mem := Node.minKdfMem }
    Node.Identity.save suite elsewhere "pass-alice" a.identity otherKdf
    let elsewhereJson ← IO.ofExcept (Json.parse (← IO.FS.readFile elsewhere))
    r := checkEq r "a file written with other parameters records them"
      (jnat (Node.objField elsewhereJson "kdf") "ops") otherKdf.ops
    let back ← Node.Identity.load suite elsewhere "pass-alice"
    r := checkEq r "and opens, because the cost comes out of the file" back.id a.identity.id
    r := checkEq r "with the keys it was written with" (toHex back.boxSk) (toHex a.identity.boxSk)
    IO.FS.removeFile elsewhere

    /- ## Taking a ledger onto a sequencer -/
    let sessionA ← Node.initAsAdmin a.ctx suite a.keys a.transport "test:in-process" "home"
    r := checkEq r "a store that joins a sequencer keeps its history to itself"
      (← Db.scalarInt a.ctx.db "SELECT COUNT(*) FROM event WHERE remote_seq = 0") 2
    -- Pushed here rather than by the next round, and that is a pin rather than a
    -- convenience: an invite link names the entry the order begins with, and a
    -- founder whose genesis is still in its own log has no such entry to name.
    -- The documented sequence is `sync init` then `invite`, with nothing between.
    r := checkEq r "and the one entry saying where it came in is in the order already"
      (← Node.remoteHead a.ctx).seq 1
    r := checkEq r "with its fingerprint written down, so a link can name it"
      (← Node.Settings.load a.ctx.cfg).genesisHash
      (Node.genesisFingerprint ((← Node.Checkpoint.remoteHashAt a.ctx 1).getD ""))
    let firstPush ← Node.push sessionA
    r := checkEq r "so the next push has nothing left to offer" firstPush.pushed 0
    r := checkEq r "with nothing to report" firstPush.blocked none
    /- ## What the files this node writes are readable by

    Everything here either is the ledger or opens it: the encrypted identity, the
    keyring, `sync.json`, the database and the receipts beside it. A default
    umask makes every one of them readable by every other user on the machine,
    and the encrypted ones are then only as strong as the passphrase. -/
    r := check r "the data directory is the owner's alone"
      (← hasMode a.ctx.cfg.dataDir "700")
    r := check r "and so is the directory receipts live in" (← hasMode a.ctx.cfg.blobDir "700")
    r := check r "the identity file is readable by nobody else"
      (← hasMode (Node.Identity.pathIn a.ctx.cfg) "600")
    r := check r "nor is the keyring" (← hasMode (Node.Keys.pathIn a.ctx.cfg) "600")
    r := check r "nor sync.json" (← hasMode (Node.Settings.pathIn a.ctx.cfg) "600")
    r := check r "nor the database itself" (← hasMode a.ctx.cfg.dbPath "600")

    let bank : Account := { id := ⟨"acc-bank"⟩, name := "Assets.Bank.Main", kind := .asset }
    let food : Account := { id := ⟨"acc-food"⟩, name := "Expenses.Food", kind := .expense }
    discard <| a.ctx.commit "test" [.putAccount bank, .putAccount food]
    let secondPush ← Node.push sessionA
    r := checkEq r "a commit made afterwards is one more entry" secondPush.pushed 1
    r := checkEq r "and nothing is left waiting" (← Node.pendingCount a.ctx) 0

    /- ## A link has to have an entry to name

    `invite` writes `genesisFingerprint` of entry 1 into the fragment, and a
    founder whose genesis is still sitting in the local log has no entry 1: the
    link would carry `none`, and a link carrying `none` pins nothing at all —
    whoever redeems it folds whichever entry the sequencer serves first and has
    no way to tell a real one from a co-member's. That was the outcome of the
    documented setup, because `sync init` seeded a genesis and pushed nothing.
    Both halves are closed now, so this store is set up the long way round with
    the push left out, which is the only way to get here at all. -/
    let e ← makePeer root "erin" seq
    let quiet : Node.Session :=
      { ctx := e.ctx, suite, keys := e.keys, transport := e.transport, ledger := "quiet" }
    discard <| Node.Transport.json e.transport
      (Node.Transport.send "POST" ["ledgers"] (Json.mkObj [("ledger", "quiet")]))
    Node.Session.publishBoxPk quiet
    Node.ensureRealm quiet Realm.selfId.val
    Node.markPrehistory e.ctx
    Node.seedGenesis e.ctx
    r := check r "a founder whose genesis is still unpushed cannot mint a link"
      (← (do discard <| Node.invite quiet Realm.selfId.val (← aWeekFromNow); pure false)
        <|> pure true)
    r := check r "because there is nothing written down about where its order begins"
      (← Node.Settings.load e.ctx.cfg).genesisHash.isEmpty
    discard <| Node.push quiet
    r := check r "putting the entry into the order fills that in, which is the backfill a \
                  client with no link to read it out of depends on"
      ((← Node.Settings.load e.ctx.cfg).genesisHash
        == Node.genesisFingerprint ((← Node.Checkpoint.remoteHashAt e.ctx 1).getD ""))
    let quietLink ← Node.invite quiet Realm.selfId.val (← aWeekFromNow)
    r := checkEq r "and then a link names it"
      ((Node.readInvite? quietLink).map (·.genesisHash))
      (some (← Node.Settings.load e.ctx.cfg).genesisHash)

    /- ## A second node, invited -/
    let b ← makePeer root "bob" seq
    let link ← Node.invite sessionA Realm.selfId.val (← aWeekFromNow)
    let some inv := Node.readInvite? link
      | throw <| IO.userError "the invite link does not read back"
    r := checkEq r "an invite link carries the ledger" inv.ledger "home"
    r := checkEq r "and the realm" inv.realm Realm.selfId.val
    r := checkEq r "and a secret of the seed's size" inv.secret.size Node.CryptoSuite.seedSize
    r := checkEq r "and the inviter's signing key, to pin as this realm's admin"
      inv.inviter a.identity.id
    r := checkEq r "and the digest of the key it wraps, to check what comes back against"
      (some inv.keyHash)
      ((← Node.Keys.latest a.keys Realm.selfId.val).map (fun (_, k) => Node.realmKeyHash k))
    -- The sixth field: which order this is. A signature on a genesis proves that
    -- some member wrote it, and the state it names may say anything at all about
    -- who administers what — so the inviter, who knows what the order really
    -- begins with, says so in the part of the link no server ever sees.
    r := checkEq r "and the digest of the entry the order begins with"
      inv.genesisHash
      (Node.genesisFingerprint ((← Node.Checkpoint.remoteHashAt a.ctx 1).getD ""))
    r := check r "which is not the literal 'none', because this order has an entry"
      (inv.genesisHash != Node.noGenesis)

    /- ## Whether an entry is a genesis is decided by the envelope

    `Event.genesis?` is asked of what a reader could *open*, and what a reader
    can open is a fact about its key ring. An envelope of two parts — a snapshot
    in a realm you hold, anything at all in a realm you do not — therefore
    reaches a node holding one key as a one-part event and a node holding both
    as a two-part one, and the first would begin its whole store from a state the
    second applies nothing of. That is two honest readers of one order holding
    different states, which is exactly what `Checkpoint.verify` reports as one of
    them lying. So the count comes off the envelope. -/
    let snapshotEvent : Event :=
      { id := "genesis-shape", author := ⟨a.identity.id⟩, composedAt := "", basedOn := 0,
        parts := [{ realm := Realm.selfId, op := .snapshot (← a.ctx.state.get) }] }
    r := check r "one part at position one, carried by a one-part envelope, is a genesis"
      (Node.genesisAt? 1 1 snapshotEvent).isSome
    r := check r "the identical event out of a two-part envelope is not one, for anybody"
      (Node.genesisAt? 1 2 snapshotEvent).isNone
    r := check r "nor is it one anywhere but at the first position"
      (Node.genesisAt? 2 1 snapshotEvent).isNone
    r := check r "and an entry whose one part never opened begins nothing"
      (Node.genesisAt? 1 1 { snapshotEvent with parts := [] }).isNone
    -- A link whose digest has been changed is a link whose sealed key nobody can
    -- vouch for, and it is refused before anything is filed.
    let wrongHash ←
      (do discard <| Node.join b.ctx suite b.keys b.transport "test:in-process"
            { inv with keyHash := String.ofList (List.replicate 32 '0') }
          pure false) <|> pure true
    r := check r "a link whose key digest does not match what the invite hands back is refused"
      wrongHash
    r := check r "and nothing is filed by the attempt"
      ((← Node.Keys.latest b.keys inv.realm).isNone)
    -- A link whose genesis digest names another order is a link to another
    -- ledger, whatever else about it checks out: the first entry decides the
    -- whole of what the joiner will hold. On its own invite, because the check
    -- comes after the redemption — reading the order at all takes a membership,
    -- so the cost of this refusal is the invite, which is the right cost.
    let spoiled ← Node.invite sessionA Realm.selfId.val (← aWeekFromNow)
    let some spoiledInv := Node.readInvite? spoiled
      | throw <| IO.userError "the invite link does not read back"
    let wrongGenesis ←
      (do discard <| Node.join b.ctx suite b.keys b.transport "test:in-process"
            { spoiledInv with genesisHash := String.ofList (List.replicate 32 '0') }
          pure false) <|> pure true
    r := check r "a link whose genesis digest is not the one this order begins with is refused"
      wrongGenesis
    r := check r "and the store it would have emptied still has its own books"
      ((← Db.scalarInt b.ctx.db "SELECT COUNT(*) FROM event") > 0)
    -- Written before the join, to show the join appends rather than assigns: a
    -- node let in by two people needs both anchors, and `Settings.pin` is what
    -- says so.
    Node.Settings.pin b.ctx.cfg "realm-elsewhere" (toHex (Sha256.hash "another admin".toUTF8))
    let sessionB ← Node.join b.ctx suite b.keys b.transport "test:in-process" inv
    r := check r "redeeming it leaves the joiner holding the realm key"
      ((← Node.Keys.latest b.keys inv.realm).isSome)
    r := checkEq r "and pins the inviter, keeping every pin that was already there"
      (((← Node.Settings.load b.ctx.cfg).pinned.map (fun p => s!"{p.realm}/{p.member}")))
      [s!"realm-elsewhere/{toHex (Sha256.hash "another admin".toUTF8)}",
       s!"{inv.realm}/{a.identity.id}"]
    r := checkEq r "and writes down what this order begins with"
      (← Node.Settings.load b.ctx.cfg).genesisHash inv.genesisHash
    r := check r "having seen that entry for itself"
      (← Node.Settings.load b.ctx.cfg).genesisSeen
    let respent ←
      (do discard <| Node.join b.ctx suite b.keys b.transport "test:in-process" inv
          pure false) <|> pure true
    r := check r "and an invite cannot be spent twice" respent

    /- ## Arriving in the books

    An invite is spent on the sequencer, which knows about keys and nothing
    about members. So joining is two halves: the key, and then saying who has
    arrived in the realm's own terms — a member record naming a party of their
    own, and the purse they hold a balance on here. Nobody else could have
    written it, because the admin who sent the link was a browser rather than a
    node. -/
    let bobId : MemberId := ⟨b.identity.id⟩
    r := check r "joining reads the realm it was let into"
      (((← b.ctx.state.get).account? bank.id).isSome)
    let sawBob ← Node.pull sessionA
    r := checkEq r "and leaves exactly one entry for the node that invited them"
      sawBob.applied 1
    let withBob ← a.ctx.state.get
    r := checkEq r "whose books now say who arrived"
      ((withBob.member? bobId).map (·.name)) (some "bob")
    let bobsParty := ((withBob.member? bobId).map (·.party)).getD ⟨""⟩
    r := check r "under a party of their own, which is not the one this ledger belongs to"
      (bobsParty != Party.selfId && (withBob.party? bobsParty).isSome)
    r := checkEq r "the realm lists them, and lists them as a viewer"
      ((withBob.realm? Realm.selfId).bind (·.roleOf bobId)) (some .viewer)
    let bobsBridge := withBob.accountByNameIn? Realm.selfId "Members.bob"
    r := check r "and they hold a purse here, in this realm, owned by their party"
      (match bobsBridge with
       | some acc =>
         acc.bridgeOf == some bobId && acc.realm == Realm.selfId && acc.owner == bobsParty
       | none => false)
    r := check r "the two nodes hold the same state"
      ((← a.ctx.state.get) == (← b.ctx.state.get))
    r := checkEq r "down to the bytes a checkpoint would commit to"
      (Encode.hashState (← b.ctx.state.get)) (Encode.hashState (← a.ctx.state.get))
    -- A join adopts rather than merges: the books this store had are gone, and
    -- the order it joined is the whole of its log. It has to be, because the
    -- first entry of that order is a snapshot and `applyOp` takes a snapshot
    -- only onto a fresh state — a store that kept its own events and applied
    -- somebody else's genesis on top of them would hold a state its own log does
    -- not replay to.
    r := checkEq r "a join adopts the ledger rather than merging into it"
      (← Db.scalarInt b.ctx.db "SELECT COUNT(*) FROM event WHERE remote_seq IS NULL \
                                OR remote_seq = 0") 0
    r := check r "and the log it now keeps replays to the state it holds"
      ((← Replay.state b.ctx.db) == (← b.ctx.state.get))

    /- ## What a purse is for

    A viewer may post in two places and no others: their own purse, and the
    account of a budget that is open. That is the whole of what it takes to say
    "I paid for this too" without being trusted with the realm. -/
    let weekend : Budget :=
      { id := ⟨"b-weekend"⟩, name := "Weekend", note := none, closed := false }
    discard <| a.ctx.commit "test"
      [.openBudget weekend { id := ⟨"acc-weekend"⟩, name := "Weekend", kind := .equity }]
    discard <| Node.push sessionA
    discard <| Node.pull sessionB
    let bobsShare : Transaction :=
      { id := ⟨"tx-bob-share"⟩, date := on "2026-05-02", narration := "bob puts in his half",
        postings := [{ account := (bobsBridge.map (·.id)).getD ⟨""⟩,
                       amount := ⟨Commodity.eur, -4000⟩ },
                     { account := ⟨"acc-weekend"⟩, amount := ⟨Commodity.eur, 4000⟩ }] }
    discard <| b.ctx.commit "test" [.putTransaction bobsShare]
    let contributed ← Node.push sessionB
    r := checkEq r "a viewer may move money from their purse into an open budget"
      contributed.pushed 1
    r := checkEq r "with nothing refused" contributed.blocked none
    discard <| Node.pull sessionA
    r := check r "and the node that invited them sees the contribution"
      (((← a.ctx.state.get).txn? bobsShare.id).isSome)

    /- ## Whose commitment a node acts on

    Any grant holder may publish a checkpoint — it is a claim about what they
    replayed, and the sequencer keeps one per author rather than one per realm,
    so that publishing is not a way to erase everybody else's. Which of them is
    worth anything is the reader's decision, and the rule is the one that governs
    a grant: an admin of that realm in this node's own state, or the inviter it
    pinned. A viewer's commitment is passed over rather than acted on, because
    the mismatch channel is the only integrity alarm this design has and a
    stranger who could set it off would make it worthless. -/
    let viewersCommitment ← Node.checkpoint sessionB
    r := check r "a viewer may publish a commitment"
      (match outcomeFor viewersCommitment Realm.selfId.val with
       | some (.published _) => true
       | _ => false)
    let onlyTheirs ← Node.Checkpoint.verify sessionA Realm.selfId.val (← Node.remoteHead a.ctx)
    r := check r "and nobody acts on it, because a viewer administers nothing"
      onlyTheirs.isSkipped
    discard <| Node.checkpoint sessionA
    let withAdmins ← Node.Checkpoint.verify sessionA Realm.selfId.val (← Node.remoteHead a.ctx)
    r := check r "while an admin's commitment on the same realm is checked, and agreed with"
      (match withAdmins with
       | .agreed .. => true
       | _ => false)

    /- ## And then trusted with more -/
    discard <| a.ctx.commit "test" [.setRole Realm.selfId bobId .admin]
    discard <| Node.push sessionA
    discard <| Node.pull sessionB
    r := check r "an admin of the realm can widen what a newcomer may do"
      ((← b.ctx.state.get).canAdminister bobId Realm.selfId)

    /- ## A grant is worth exactly what its signature is

    `fetchKey` and `ensureRealm` file the key inside a grant, and `Keys.latest`
    hands back the highest generation held — which is the key everything this
    node writes next is sealed under. So a grant taken on a server's word is a
    server reading every future write, and the three questions below are asked
    before one is ever unwrapped. -/
    let sharedRealm := Realm.selfId.val
    let heldKey := ((← Node.Keys.latest b.keys sharedRealm).map (·.2)).getD ByteArray.empty
    let wrapped := suite.wrapKey b.identity.boxPk heldKey
    let grantBytes := Sync.grantBytes "home" sharedRealm 0 b.identity.id "viewer" wrapped
    let unsignedGrant : Node.GrantRecord :=
      { realm := sharedRealm, member := b.identity.id, generation := 0, role := "viewer",
        wrappedKey := wrapped, grantedBy := a.identity.id, signature := "" }
    r := check r "a grant nobody signed is never unwrapped"
      (wasRefused (← Node.Session.checkGrant sessionB unsignedGrant))
    let (strangerPk, strangerSk) := suite.signSeedKeypair (Sha256.hash "a stranger".toUTF8)
    r := check r "nor one signed by somebody who administers nothing in this realm"
      (wasRefused (← Node.Session.checkGrant sessionB
        { unsignedGrant with grantedBy := toHex strangerPk,
                             signature := toHex (suite.sign strangerSk grantBytes) }))
    let properGrant : Node.GrantRecord :=
      { unsignedGrant with
          signature := Node.Identity.signHex suite a.identity grantBytes }
    r := check r "while one signed by an admin of the realm stands"
      (!wasRefused (← Node.Session.checkGrant sessionB properGrant))
    r := check r "and one made out to somebody else is not this node's to unwrap"
      (wasRefused (← Node.Session.checkGrant sessionB
        { properGrant with member := a.identity.id }))

    /- ## An agreement key is a claim only its owner may make

    A realm key is sealed to whatever `boxPk` a member record carries, and the
    server is the one handing that record over. Without the member's own
    signature over it an operator could substitute a key they hold and be
    re-granted every realm on the next rotation, which is the hole that made the
    encryption a formality. -/
    let theirBoxPk := b.identity.boxPkHex
    let ownSignature :=
      Node.Identity.signHex suite b.identity (Sync.memberBytes "home" b.identity.id theirBoxPk)
    r := check r "an agreement key its owner never signed for is never sealed to"
      (Node.Session.memberBoxPk? sessionA b.identity.id theirBoxPk "").isNone
    r := check r "one somebody else signed for is no better"
      (Node.Session.memberBoxPk? sessionA b.identity.id theirBoxPk
        (Node.Identity.signHex suite a.identity
          (Sync.memberBytes "home" b.identity.id theirBoxPk))).isNone
    r := check r "one signed for another ledger is no better either"
      (Node.Session.memberBoxPk? sessionA b.identity.id theirBoxPk
        (Node.Identity.signHex suite b.identity
          (Sync.memberBytes "elsewhere" b.identity.id theirBoxPk))).isNone
    r := check r "and the one its owner did sign for is the key a grant is wrapped to"
      (Node.Session.memberBoxPk? sessionA b.identity.id theirBoxPk ownSignature).isSome

    /- ## The other direction -/
    let bobsShopping : Transaction :=
      { id := ⟨"tx-bob-1"⟩, date := on "2026-05-05", narration := "bob does the shopping",
        postings := [{ account := bank.id, amount := ⟨Commodity.eur, -1250⟩ },
                     { account := food.id, amount := ⟨Commodity.eur, 1250⟩ }] }
    discard <| b.ctx.commit "test" [.putTransaction bobsShopping]
    let bobPush ← Node.push sessionB
    r := checkEq r "the second node appends too" bobPush.pushed 1
    let alicePull ← Node.pull sessionA
    r := checkEq r "and the first takes it in" alicePull.applied 1
    r := check r "the transaction it wrote is in the first node's books"
      (((← a.ctx.state.get).txn? bobsShopping.id).isSome)
    r := check r "and the two agree again" ((← a.ctx.state.get) == (← b.ctx.state.get))

    /- ## A race for the head -/
    discard <| a.ctx.commit "test" [.putLabel { id := ⟨"lbl-a"⟩, name := "alice-was-here" }]
    discard <| b.ctx.commit "test" [.putLabel { id := ⟨"lbl-b"⟩, name := "bob-was-here" }]
    let winner ← Node.push sessionB
    r := checkEq r "one of two simultaneous writers gets the head" winner.pushed 1
    r := checkEq r "without a conflict" winner.conflicts 0
    let loser ← Node.push sessionA
    r := checkEq r "the other is told the head has moved" loser.conflicts 1
    r := checkEq r "pulls what it missed, and appends after it" loser.pushed 1
    r := checkEq r "with nothing left blocked" loser.blocked none
    discard <| Node.pull sessionB
    r := check r "and both hold both labels"
      ((← a.ctx.state.get) == (← b.ctx.state.get))

    /- ## Two writers who never meet

    The same race, over transactions this time, and this is the case the rebase
    is for: neither write names an account, a transaction or a fingerprint the
    other names, so `Rebase.check` says the loser means exactly what it meant
    and may be offered again unchanged — which it is, without anybody being
    asked anything. -/
    let cash : Account := { id := ⟨"acc-cash"⟩, name := "Assets.Cash", kind := .asset }
    let books : Account := { id := ⟨"acc-books"⟩, name := "Expenses.Books", kind := .expense }
    discard <| a.ctx.commit "test" [.putAccount cash, .putAccount books]
    discard <| Node.push sessionA
    discard <| Node.pull sessionB
    let alicesBread : Transaction :=
      { id := ⟨"tx-a-bread"⟩, date := on "2026-05-06", narration := "alice buys bread",
        postings := [{ account := bank.id, amount := ⟨Commodity.eur, -300⟩ },
                     { account := food.id, amount := ⟨Commodity.eur, 300⟩ }] }
    let bobsNovel : Transaction :=
      { id := ⟨"tx-b-novel"⟩, date := on "2026-05-06", narration := "bob buys a novel",
        postings := [{ account := cash.id, amount := ⟨Commodity.eur, -1800⟩ },
                     { account := books.id, amount := ⟨Commodity.eur, 1800⟩ }] }
    discard <| a.ctx.commit "test" [.putTransaction alicesBread]
    discard <| b.ctx.commit "test" [.putTransaction bobsNovel]
    let firstThere ← Node.push sessionB
    r := checkEq r "one of the two gets the head" firstThere.pushed 1
    let rebased ← Node.push sessionA
    r := checkEq r "the other is told it has moved" rebased.conflicts 1
    r := checkEq r "and lands anyway, rebased onto what arrived, without asking" rebased.pushed 1
    r := checkEq r "with nothing to report" rebased.blocked none
    discard <| Node.pull sessionB
    r := check r "both transactions are in both sets of books"
      (((← a.ctx.state.get).txn? bobsNovel.id).isSome
        && ((← b.ctx.state.get).txn? alicesBread.id).isSome)
    r := check r "and the two nodes agree" ((← a.ctx.state.get) == (← b.ctx.state.get))

    /- ## An entry that is none of this node's business -/
    let private_ : RealmId := ⟨"realm-private"⟩
    let hidden : Account :=
      { id := ⟨"acc-hidden"⟩, name := "Assets.Hidden", kind := .asset, realm := private_ }
    discard <| a.ctx.commit "test"
      [.createRealm { id := private_, name := "private"
                      members := [(a.ctx.member, .admin)] }]
      (realm := private_)
    discard <| a.ctx.commit "test" [.putAccount hidden] (realm := private_)
    discard <| Node.push sessionA
    let blindPull ← Node.pull sessionB
    r := checkEq r "an entry in a realm this node holds no key for is stored unreadable"
      blindPull.unreadable 2
    r := checkEq r "and applies nothing" blindPull.applied 0
    let stA ← a.ctx.state.get
    let stB ← b.ctx.state.get
    let withoutPrivate :=
      { stA with realms := stA.realms.erase private_.val,
                 accounts := stA.accounts.erase hidden.id.val }
    r := check r "so the second node holds the first's state minus that realm's parts"
      (withoutPrivate == stB)
    r := checkEq r "while its place in the order keeps up"
      blindPull.seq (← Node.remoteHead a.ctx).seq

    /- ## An envelope changed in flight -/
    discard <| a.ctx.commit "test" [.putLabel { id := ⟨"lbl-t"⟩, name := "in-transit" }]
    discard <| Node.push sessionA
    -- A sequencer that changes what it serves, one way per round.
    let meddling (f : Json → Json) : Node.Transport := fun req => do
      let reply ← b.transport req
      match reply with
      | .json code payload =>
        if code == 200 && req.segments.getLast? == some "events" then
          return .json code (mapFetch f payload)
        else return reply
      | _ => return reply
    let tampering := meddling (mapFirstPart tamperPart)
    let beforeLie ← b.ctx.state.get
    let lied ← Node.pull { sessionB with transport := tampering }
    r := check r "a tampered envelope is refused" lied.refused.isSome
    r := check r "nothing it carried is applied" ((← b.ctx.state.get) == beforeLie)
    r := checkEq r "and the node keeps its place, so the entry can be fetched again"
      (← Node.remoteHead b.ctx).seq lied.seq
    let digestChanged ← Node.pull { sessionB with
      transport := meddling (mapFirstPart tamperDigest) }
    r := check r "a part whose digest has been changed is refused, because the signature \
                  covers the digest and not the bytes" digestChanged.refused.isSome
    let seqSkipped ← Node.pull { sessionB with
      transport := meddling (fun e => entryWith e (seq := some (jnat e "seq" + 1))) }
    r := check r "an entry served at a position that does not follow the last one is refused"
      seqSkipped.refused.isSome
    let zeros := String.ofList (List.replicate 64 '0')
    let chainBroken ← Node.pull { sessionB with
      transport := meddling (fun e => entryWith e (prevHash := some zeros)) }
    r := check r "and one naming a predecessor this node did not compute is refused too"
      chainBroken.refused.isSome
    r := checkEq r "none of the three moved this node's place in the order"
      (← Node.remoteHead b.ctx).seq lied.seq
    r := check r "or touched its state" ((← b.ctx.state.get) == beforeLie)
    let honest ← Node.pull sessionB
    r := checkEq r "an honest fetch of the same entry applies it" honest.applied 1
    let endA ← a.ctx.state.get
    let visible :=
      { endA with realms := endA.realms.erase private_.val,
                  accounts := endA.accounts.erase hidden.id.val }
    r := check r "and the two nodes agree once more, up to the realm one of them cannot see"
      (visible == (← b.ctx.state.get))
    r := checkEq r "with the same state hash"
      (Encode.hashState (← b.ctx.state.get)) (Encode.hashState visible)

    /- ## The two chains -/
    r := check r "the local log still verifies against its own chain"
      ((← Replay.events b.ctx.db).size > 0)
    r := check r "and replays to the state in memory"
      ((← Replay.state b.ctx.db) == (← b.ctx.state.get))

    /- ## A checkpoint, published and checked

    The property under test is the one determinism buys: the realm's projection
    is a fold of the same parts in the same order on both nodes, so the hash one
    of them signs is the hash the other computes. -/
    let aHead ← Node.remoteHead a.ctx
    let published ← Node.checkpoint sessionA
    r := checkEq r "a checkpoint is published for every realm this node holds a key for"
      published.size 2
    r := checkEq r "the one for the shared realm stands at the head of the order"
      (publishedAt (outcomeFor published Realm.selfId.val)) (some aHead.seq)
    r := checkEq r "and commits to the hash of that realm's projection"
      (publishedHash (outcomeFor published Realm.selfId.val))
      (some (Encode.hashState (← Node.Checkpoint.projectionAt a.ctx Realm.selfId.val aHead.seq)))
    r := check r "a realm's projection is not the whole state the node holds"
      (Encode.hashState (← Node.Checkpoint.projectionAt a.ctx Realm.selfId.val aHead.seq)
        != Encode.hashState (← a.ctx.state.get))
    let checkedB ← Node.pull sessionB
    r := checkEq r "the second node checks it and agrees" checkedB.checkpointsAgreed 1
    r := check r "with nothing to report" checkedB.checkpointMismatch.isEmpty
    r := check r "the realm it holds no key for is not one it even asks about"
      ((← Node.Checkpoint.verify sessionB private_.val (← Node.remoteHead b.ctx)).isSkipped)
    let checkedA ← Node.pull sessionA
    r := checkEq r "and the node that signed it agrees with itself"
      checkedA.checkpointsAgreed 2

    /- ## A node whose view of the order has been meddled with

    The fold is over the entries the local log files under the remote order, so
    slipping one more entry into that range is exactly the disagreement two
    honest nodes cannot have. -/
    discard <| b.ctx.commit "test" [.putLabel { id := ⟨"lbl-x"⟩, name := "never-in-the-order" }]
    let (planted, _) ← EventLog.head b.ctx.db
    -- Late in the order, where this node was already an admin: an operation
    -- slipped in before it was let into the realm would be refused by the fold
    -- and change nothing, which is the rights rules working rather than the
    -- meddling being caught.
    Db.exec b.ctx.db
      s!"UPDATE event SET remote_seq = {aHead.seq - 1} WHERE seq = {planted}"
    let lied ← Node.pull sessionB
    r := checkEq r "a node whose projection has gained an entry says so loudly"
      lied.checkpointMismatch.size 1
    r := check r "naming the realm and the entry the commitment speaks about"
      (match lied.checkpointMismatch[0]? with
       | some (realm, seq, _) => realm == Realm.selfId.val && seq == aHead.seq
       | none => false)
    r := checkEq r "and agrees about nothing" lied.checkpointsAgreed 0
    -- Put it back where it belongs: a local event nobody else has seen.
    Db.exec b.ctx.db s!"UPDATE event SET remote_seq = 0 WHERE seq = {planted}"
    let honestAgain ← Node.pull sessionB
    r := check r "with the entry out of the way the two agree again"
      honestAgain.checkpointMismatch.isEmpty
    r := checkEq r "as they did before" honestAgain.checkpointsAgreed 1

    /- ## A receipt, encrypted, through the sequencer -/
    let receipt := "BÄCKEREI\n2 Brötchen  1,80\n".toUTF8
    let sha ← Node.Blobs.put sessionA receipt "text/plain; charset=utf-8" (some "till.txt")
    r := checkEq r "a receipt is named by the hash of its plaintext" sha
      (Sha256.hexBytes receipt)
    let storedMeta ← Blobs.meta? a.ctx sha
    r := check r "and is uploaded under the hash of its ciphertext, which is another hash"
      (match storedMeta.bind (·.cipherHash) with
       | some cipher => cipher != sha
       | none => false)
    r := check r "with its key sealed under this realm's key"
      (match (storedMeta.bind (·.wrappedKey)).bind Node.Blobs.readWrapped? with
       | some (realm, generation, bytes) =>
         realm == Realm.selfId.val && generation == 0 && bytes.size > 0
       | none => false)
    discard <| Node.push sessionA
    discard <| Node.pull sessionB
    r := check r "the second node learns the file exists"
      ((← Blobs.meta? b.ctx sha).isSome)
    r := check r "without the bytes" ((← Blobs.get? b.ctx sha).isNone)
    let fetched ← Node.Blobs.get? sessionB sha
    r := checkEq r "which it fetches, decrypts and checks against the hash the ledger gave it"
      (fetched.map Sha256.hexBytes) (some sha)
    r := check r "and keeps, so the second read asks nobody"
      ((← Blobs.get? b.ctx sha).isSome)

    /- ## A receipt filed in one realm and attached in another

    A receipt is scanned before it is matched, so it is sealed under whichever
    realm the node was working in — here a realm nobody else is in. Attaching it
    to a payment somewhere else has to carry the file across: the blob key is
    unwrapped with the key this node holds and sealed again under the target
    realm's, the bytes are sealed again under associated data naming that realm,
    and the registration that says so travels in the same event as the
    attachment. So a node that was never in the realm the receipt was filed in
    hears of the file and opens it, both for the first time. -/
    let bill := "HÜTTE\n2 Nächte  120,00\n".toUTF8
    let billSha ← Node.Blobs.put sessionA bill "text/plain; charset=utf-8" (some "hut.txt")
      private_.val
    r := check r "a receipt can be filed in a realm of this node's own"
      (match ((← Blobs.meta? a.ctx billSha).bind (·.wrappedKey)).bind Node.Blobs.readWrapped? with
       | some (realm, _, _) => realm == private_.val
       | none => false)
    discard <| Node.push sessionA
    discard <| Node.pull sessionB
    r := check r "which a node holding no key for that realm never hears of"
      ((← Blobs.meta? b.ctx billSha).isNone)
    Node.Blobs.attach sessionA bobsShare.id billSha
    r := check r "attaching it across a realm re-wraps it under the one it lands in"
      (match ((← Blobs.meta? a.ctx billSha).bind (·.wrappedKey)).bind Node.Blobs.readWrapped? with
       | some (realm, _, _) => realm == Realm.selfId.val
       | none => false)
    r := check r "which is a second ciphertext, not a second file"
      ((← Blobs.meta? a.ctx billSha).bind (·.cipherHash) != some billSha)
    r := checkEq r "and the record itself moves to the realm the payment is in"
      (((← a.ctx.state.get).blob? billSha).map (·.realm)) (some Realm.selfId)
    discard <| Node.push sessionA
    discard <| Node.pull sessionB
    r := check r "so the other node now knows the file is there"
      ((← Blobs.meta? b.ctx billSha).isSome)
    r := check r "and that the transaction carries it"
      ((((← b.ctx.state.get).txn? bobsShare.id).map (·.attachments)) == some [billSha])
    let openedBill ← Node.Blobs.get? sessionB billSha
    r := checkEq r "it fetches the new ciphertext and opens it with the key it does hold"
      (openedBill.map Sha256.hexBytes) (some billSha)
    r := checkEq r "and reads what was written on the paper"
      (openedBill.bind String.fromUTF8?) (String.fromUTF8? bill)

    /- ## Being put out, and a new key for those who remain -/
    let revoked ← Node.Rekey.revoke sessionA Realm.selfId.val b.identity.id
    r := checkEq r "a revoke moves the realm on a generation" revoked.generation 1
    r := checkEq r "and the log says the same number"
      (((← a.ctx.state.get).realm? Realm.selfId).map (·.generation)) (some revoked.generation)
    r := checkEq r "and so does the keyring"
      ((← Node.Keys.latest a.keys Realm.selfId.val).map (·.1)) (some revoked.generation)
    r := checkEq r "only the members who are left are granted the new key"
      revoked.granted #[a.identity.id]
    r := check r "and nobody is stranded by it" revoked.stranded.isEmpty
    let rotated ← Node.Rekey.rotate sessionA Realm.selfId.val
    r := checkEq r "a rotation moves it on again" rotated.generation 2
    r := checkEq r "with the log following" (((← a.ctx.state.get).realm? Realm.selfId).map
      (·.generation)) (some 2)
    -- Somebody new, let in at the generation the realm is on now.
    let c ← makePeer root "carol" seq
    let carolLink ← Node.invite sessionA Realm.selfId.val (← aWeekFromNow)
    let some carolInvite := Node.readInvite? carolLink
      | throw <| IO.userError "the invite link does not read back"
    let sessionC ← Node.join c.ctx suite c.keys c.transport "test:in-process" carolInvite
    r := checkEq r "the newcomer holds the current generation and no older one"
      ((← Node.Keys.latest c.keys Realm.selfId.val).map (·.1)) (some 2)
    -- Their whole store came from a commitment they cannot link back to entry 1,
    -- which was allowed only because its author is the inviter the link pinned.
    -- That is a weaker thing than having read the order, and the file says so.
    r := check r "a store started from a checkpoint records that it never saw the beginning"
      (!(← Node.Settings.load c.ctx.cfg).genesisSeen)
    r := checkEq r "while still knowing which entry the order begins with"
      (← Node.Settings.load c.ctx.cfg).genesisHash carolInvite.genesisHash
    -- The arrival of a newcomer is an `addMember` and a `grant`, and neither is
    -- an operation a pending write may be replayed over, so the node that
    -- invited them takes their arrival in before it writes anything else.
    discard <| Node.pull sessionA
    discard <| a.ctx.commit "test" [.putLabel { id := ⟨"lbl-after"⟩, name := "after-the-revoke" }]
    discard <| Node.push sessionA
    let afterB ← Node.pull sessionB
    r := checkEq r "the member who was put out applies nothing written since" afterB.applied 0
    r := check r "and counts what it can no longer read" (afterB.unreadable > 0)
    r := check r "the label is not in its books"
      (((← b.ctx.state.get).label? ⟨"lbl-after"⟩).isNone)
    r := check r "and it accuses nobody of anything, because it cannot check"
      afterB.checkpointMismatch.isEmpty
    -- What it cannot check it also must not show as though it could. The realm
    -- is folded around entries whose parts never opened, so everything this node
    -- says about it is a partial answer, and both the CLI and the API say so.
    r := check r "the realm it was put out of is one it can no longer verify"
      ((← Node.Checkpoint.gappedRealms b.ctx (← Node.remoteHead b.ctx).seq).contains
        Realm.selfId.val)
    let realmRows (ctx : Ctx) : IO (Array Json) := do
      let reply ← Api.handleSafe ctx Api.bootstrapCaller (Api.Req.simple "GET" ["realms"])
        { unverified := Node.Realms.unverified }
      return ((reply.json?.getD Json.null).getArr?).toOption.getD #[]
    r := check r "and the API's payload carries the flag"
      ((← realmRows b.ctx).any fun rl => jstr rl "id" == Realm.selfId.val && jbool rl "unverified")
    r := check r "while a node that read every part of a realm is not flagged for it"
      ((← realmRows a.ctx).any fun rl =>
        jstr rl "id" == Realm.selfId.val && !jbool rl "unverified")
    let afterC ← Node.pull sessionC
    r := check r "the newcomer reads what was written under the key it was given"
      (afterC.applied > 0)
    r := check r "so the label is in its books"
      (((← c.ctx.state.get).label? ⟨"lbl-after"⟩).isSome)
    -- The order begins with a genesis sealed under a generation the newcomer
    -- will never hold, so folding what it can read would give it an empty realm
    -- and refuse every operation it did read. It starts from what its inviter
    -- committed to instead: a signed checkpoint, at a generation it holds,
    -- opened and checked against the state hash inside it. So the history is
    -- shut to it and the state is not.
    r := check r "what was written under the keys it never had is in its books all the same"
      (((← c.ctx.state.get).label? ⟨"lbl-a"⟩).isSome)
    r := check r "because it started from the checkpoint its inviter published"
      ((← Db.scalarInt c.ctx.db "SELECT COUNT(*) FROM event WHERE remote_seq = 1") == 0)
    r := check r "and its own log still replays to the state it holds"
      ((← Replay.state c.ctx.db) == (← c.ctx.state.get))

    /- ## Starting from a snapshot instead of from the beginning -/
    discard <| Node.checkpoint sessionA
    discard <| a.ctx.commit "test"
      [.putLabel { id := ⟨"lbl-tail"⟩, name := "after-the-snapshot" }]
    let full ← Replay.state a.ctx.db
    let (fromSnapshot, startedAt) ← Replay.stateFrom a.ctx.db
    r := check r "a rebuild from the checkpoint starts part way along" (startedAt > 0)
    r := check r "and lands exactly where folding the whole log lands" (full == fromSnapshot)
    r := checkEq r "down to the bytes" (Encode.hashState fromSnapshot) (Encode.hashState full)
    r := checkEq r "the events the snapshot covers are still in the log, every one of them"
      (← Db.scalarInt a.ctx.db "SELECT COUNT(*) FROM event")
      ((← EventLog.head a.ctx.db).1)

    /- ## A race the node will not settle by itself

    `Rebase.check` is a decision about syntax, and it is conservative on
    purpose. Deleting a label strips it from every transaction that carried it,
    so what such an operation touches cannot be read off it, and two of them
    racing is exactly the case a node must not resolve on its own. The loser is
    told which event and which part of it, and the event stays in its log:
    unpushed, unlost, and somebody's to decide about.

    It is last because it leaves the two nodes disagreeing, which is what an
    unresolved conflict is. -/
    -- Deleting a label is an admin's to do, so the newcomer is made one first:
    -- two viewers cannot have this argument.
    discard <| a.ctx.commit "test"
      [ .setRole Realm.selfId ⟨c.identity.id⟩ .admin
      , .putLabel { id := ⟨"lbl-p"⟩, name := "alices-to-drop" }
      , .putLabel { id := ⟨"lbl-q"⟩, name := "carols-to-drop" } ]
    discard <| Node.push sessionA
    discard <| Node.pull sessionC
    discard <| a.ctx.commit "test" [.deleteLabel ⟨"lbl-p"⟩]
    discard <| c.ctx.commit "test" [.deleteLabel ⟨"lbl-q"⟩]
    let took ← Node.push sessionC
    r := checkEq r "the first of two irreconcilable writers is placed" took.pushed 1
    let stopped ← Node.push sessionA
    r := checkEq r "the second is told the head has moved" stopped.conflicts 1
    r := checkEq r "and this time it is not offered again" stopped.pushed 0
    r := check r "the node says which event stopped it, and which part of that event"
      (match stopped.blocked with
       | some why => (why.splitOn "its part 0").length == 2 && (why.splitOn "cannot be").length == 2
       | none => false)
    r := checkEq r "the event is still in the log, waiting for somebody to decide"
      (← Node.pendingCount a.ctx) 1
    r := check r "and it is still the sequencer's order that the other node followed"
      (((← c.ctx.state.get).label? ⟨"lbl-p"⟩).isSome)

    /- ## A rebase asks about every realm, not only the part's own

    `rebase_sound` is stated about the operations that took the state from where
    an event was composed to where it is now, and a node reaches that state by
    applying every readable part of every intervening entry. Filtering them down
    to the part's own realm asked a question the theorem does not answer: a
    co-member's `deleteLabel` in the shared realm moves state a pending part in
    a private realm may depend on, and that part used to be re-offered unchanged
    and unasked.

    The pending write below names nothing the intervening one names, and it is
    still refused — `Rebase.check` is conservative, and a `deleteLabel` rewrites
    every transaction that carried the label, so nothing may be replayed over
    one. What the check now sees is that it happened at all. -/
    -- The backlog the previous section left is what a later round would clear,
    -- and it has to be cleared before this node can race anybody again.
    discard <| Node.pull sessionA
    discard <| Node.push sessionA
    r := checkEq r "the blocked event goes out once its race is over"
      (← Node.pendingCount a.ctx) 0
    -- And the other node takes it in, so that the only thing between the two
    -- writes below is the two writes below.
    discard <| Node.pull sessionC
    discard <| a.ctx.commit "test"
      [.putLabel { id := ⟨"lbl-hidden"⟩, name := "written-in-the-private-realm" }]
      (realm := private_)
    discard <| c.ctx.commit "test" [.deleteLabel ⟨"lbl-after"⟩]
    let elsewhere ← Node.push sessionC
    r := checkEq r "the writer in the shared realm gets the head" elsewhere.pushed 1
    let crossed ← Node.push sessionA
    r := checkEq r "the other is told it has moved" crossed.conflicts 1
    r := checkEq r "and its pending write in a realm of its own is not replayed over it"
      crossed.pushed 0
    r := check r "the refusal naming the realm that write was in"
      (match crossed.blocked with
       | some why => (why.splitOn s!"in realm '{private_.val}'").length == 2
       | none => false)
    r := check r "which is a realm the intervening write was not in"
      (((← c.ctx.state.get).realm? private_).isNone)

    /- ## The pin, checked against the entry that is folded

    `join` asks the sequencer what its order begins with, and then `pull` asks a
    second time for the entries it will apply. Those are two requests and a
    sequencer may answer them differently: the first with the real entry 1, so
    that the link's digest matches and the join goes ahead, and the second with
    one an ordinary member of the realm composed offline — position 1, no
    predecessor, signed with their own key, carrying a snapshot that says whatever
    they like about who administers what. Every check the pull made passed, and
    the state it left was the forger's, because nothing compared what was being
    folded against the digest in the link. It is compared now, in `pull`, where
    the entry that decides the state is; and `join` asks `linksToGenesis` again
    once its first pull is done, because an order served short is not an order
    that matches either.

    The same sequencer serves no checkpoint, which is its to do and which is what
    makes entry 1 the way in: `chooseSnapshot` on the browser side has the same
    hole and the review names it. -/
    let d ← makePeer root "dave" seq
    let daveLink ← Node.invite sessionA Realm.selfId.val (← aWeekFromNow)
    let some daveInv := Node.readInvite? daveLink
      | throw <| IO.userError "the invite link does not read back"
    let forgedState := { ← c.ctx.state.get with
      labels := (← c.ctx.state.get).labels.insert "lbl-forged"
        { id := ⟨"lbl-forged"⟩, name := "a co-member's own beginning" } }
    let forgedEvent : Event :=
      { id := "forged-genesis", author := ⟨c.identity.id⟩, composedAt := "", basedOn := 0,
        parts := [{ realm := Realm.selfId, op := .snapshot forgedState }] }
    let forged ← Node.Envelope.compose suite c.keys "home" forgedEvent 1 "" 0
    let fetches ← IO.mkRef 0
    let twoFaced : Node.Transport := fun req => do
      -- A sequencer holds nobody to serving a commitment, and withholding every
      -- one of them is how it makes a joiner read the order from its beginning.
      if req.segments.getLast? == some "checkpoint" then
        return .json 404 (Json.mkObj [("error", "no commitment here")])
      let reply ← d.transport req
      match reply with
      | .json code payload =>
        if code == 200 && req.method == "GET" && req.segments.getLast? == some "events" then
          fetches.modify (· + 1)
          if (← fetches.get) > 1 then
            return .json code (Json.mkObj
              [("head", (payload.getObjVal? "head").toOption.getD Json.null),
               ("events", Json.arr #[forged.toJson])])
        return reply
      | _ => return reply
    let twoFacedRefused ←
      (do discard <| Node.join d.ctx suite d.keys twoFaced "test:in-process" daveInv
          pure false) <|> pure true
    r := check r "a sequencer that answers the link's check and the pull differently is refused"
      twoFacedRefused
    r := checkEq r "and not one entry of what it served was written down"
      (← Db.scalarInt d.ctx.db "SELECT COUNT(*) FROM event") 0
    r := check r "so the beginning that forgery carried is in nobody's books"
      (((← d.ctx.state.get).label? ⟨"lbl-forged"⟩).isNone)
    r := checkEq r "and the joiner is left standing at the beginning of the order"
      (← Node.remoteHead d.ctx).seq 0
    -- The same refusal one level down, because the fold is where a genesis
    -- decides anything and therefore the only place the check is worth making.
    let daveSession : Node.Session :=
      { ctx := d.ctx, suite, keys := d.keys, transport := twoFaced, ledger := "home" }
    let foldRefused ← Node.pull daveSession
    r := checkEq r "a pull served another entry 1 than the one this node was told about \
                    refuses it at that position" (foldRefused.refused.map (·.1)) (some 1)
    r := check r "saying which digest it was told to expect"
      (match foldRefused.refused with
       | some (_, why) => (why.splitOn daveInv.genesisHash).length == 2
       | none => false)
    r := checkEq r "and it is still standing where it was"
      (← Node.remoteHead d.ctx).seq 0
    return r
  finally
    IO.FS.removeDirAll root <|> pure ()
