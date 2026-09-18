import Resources.Sync.Server
import Resources.Node.Crypto

/-!
# Sequencer tests

The sequencer is exercised the way a client sees it: through the route table,
over a real `sequencer.db` in a temporary directory, with a verifier that really
checks signatures.

That verifier is `Verifier.ofSuite` over `CryptoSuite.insecureForTests`, which
provides no security whatsoever — a signature is a hash of the public key — but
which has the *shape* of a signature scheme: a key pair, a signature over
exactly the bytes the protocol says, and a check that fails when any of them
change. So every signature below is taken for real over the real canonical byte
string, and every refusal below is a refusal the day libsodium is bound.

What the file asserts is everything version 2 added on top of what the server
already decided for itself: that every signature is checked, that a part's
digest is checked against its bytes, that a filtered envelope hashes to what the
whole one hashes to, that an agreement key is only ever published by its owner,
that a grant carries the signature of somebody entitled to make it, that a
checkpoint belongs to its author and may not go backwards, that twelve
simultaneous appends produce one entry and eleven conflicts, and that the caps,
the allowlist and the static-path rule turn away what they are there to turn
away.

The canonical byte strings are pinned as literals. A client in another language
that gets one of them wrong produces signatures this server will not accept, and
that failure is worth being loud about here rather than at three in the morning.
-/

open Lean Resources

/-- A running tally of what passed and what did not. -/
structure Report where
  /-- How many checks have passed. -/
  passed : Nat := 0
  /-- The description of each failure. -/
  failed : Array String := #[]

/-- Records one boolean check. -/
def check (r : Report) (name : String) (ok : Bool) : Report :=
  if ok then { r with passed := r.passed + 1 }
  else { r with failed := r.failed.push name }

/-- Records one equality check, reporting both sides when it fails. -/
def checkEq [BEq α] [ToString α] (r : Report) (name : String) (actual expected : α) : Report :=
  if actual == expected then { r with passed := r.passed + 1 }
  else { r with failed := r.failed.push s!"{name}: got {actual}, expected {expected}" }

/-- The JSON payload of a reply, or null for a binary one. -/
private def payload (reply : Api.Reply) : Json := reply.json?.getD Json.null

/-- A string field, or the empty string. -/
private def jstr (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

/-- A numeric field, or zero. -/
private def jnat (j : Json) (key : String) : Nat := (j.getObjValAs? Nat key).toOption.getD 0

/-- A boolean field, or a stated default. -/
private def jbool (j : Json) (key : String) (dflt : Bool) : Bool :=
  (j.getObjValAs? Bool key).toOption.getD dflt

/-- A nested object field, or null. -/
private def jsub (j : Json) (key : String) : Json := (j.getObjVal? key).toOption.getD Json.null

/-- An array field, or empty. -/
private def jarr (j : Json) (key : String) : Array Json :=
  ((j.getObjVal? key).bind Json.getArr?).toOption.getD #[]

/-- The plaintext a client would encrypt, as the ciphertext the sequencer sees. -/
private def cipher (s : String) : ByteArray := s.toUTF8

/-- The primitives the tests sign with. Shaped like the real ones; secret like none. -/
private def suite : Node.CryptoSuite := Node.CryptoSuite.insecureForTests

/-- One party: a signing key pair whose public half is their member id, and an agreement key. -/
private structure Signer where
  /-- The member id: the hex of the signing public key, 64 characters. -/
  id : String
  /-- The signing secret key. -/
  signSk : ByteArray
  /-- The agreement public key, hex. -/
  boxPk : String
  deriving Inhabited

/-- Derives a party from a name, deterministically, so a failure reads the same twice. -/
private def party (name : String) : Signer :=
  let seed := Sha256.hash name.toUTF8
  let (signPk, signSk) := suite.signSeedKeypair seed
  let (boxPk, _) := suite.boxSeedKeypair seed
  { id := toHex signPk, signSk, boxPk := toHex boxPk }

/-- What this party's signature over some bytes looks like on the wire. -/
private def Signer.sign (i : Signer) (msg : ByteArray) : String := toHex (suite.sign i.signSk msg)

/--
The verifier the sequencer under test checks signatures with.

It states the width of the suite's signatures, so `Verifier.check` gets the
exact length check rather than the range it falls back on — which is the half of
L7 that has to be exercised here, because the day libsodium is bound the number
is 128 and nothing else about this changes.
-/
private def verifier : Sync.Verifier :=
  { Sync.Verifier.ofSuite suite with signatureHexWidth := 2 * suite.signatureSize }

/-- A path's mode as `stat` reports it, or `none` where there is no `stat` to ask. -/
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

/-- One part, with the digest of its ciphertext filled in the way `Part` fills it. -/
private def partOf (realm : String) (generation : Nat) (text : String) : Sync.Part :=
  { realm, generation, ciphertext := cipher text }

/-- An envelope signed by its author over `signingBytes`. -/
private def signedEnvelope (i : Signer) (ledger : String) (seq : Nat) (prevHash : String)
    (parts : List Sync.Part) : Sync.Envelope :=
  let unsigned : Sync.Envelope :=
    { ledger, seq, prevHash, author := i.id, parts, signature := "" }
  { unsigned with signature := i.sign unsigned.signingBytes }

-- One long `do` block on purpose — every check after the first depends on the
-- ledger the ones before it built — and one long `do` block is more than the
-- elaborator's default recursion limit, or the compiler's default budget, is
-- sized for.
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/--
The sequencer, end to end: signatures, membership, realms, grants, the order,
what a fetch may carry back, and every refusal version 2 added.
-/
def syncTests (r : Report) : IO Report := do
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-sync-{← freshId}"
  try
    let origin := "https://resources.example/seq"
    let alice := party "alice"
    let bob := party "bob"
    let carol := party "carol"
    let log ← Sync.Log.open (Sync.Config.atDir root)
    -- Every mutating route is metered now rather than the append alone, and
    -- this file makes a few hundred of them back to back on one key, so the
    -- node under test carries an allowance nothing here is meant to reach.
    -- What the limit does when it *is* reached has nodes of its own below.
    let node ← Sync.Node.make log verifier { burst := 4096 } origin (some #[alice.id])
      (testOnly := true)
    -- The trail as a person would read it: the lines that have something on them.
    let auditLines : IO (List String) := do
      return ((← IO.FS.readFile (Sync.Log.auditPath log)).splitOn "\n").filter
        (fun l => !l.trimAscii.isEmpty)
    -- Talking to a node: a challenge, a signature over it, and a bearer token.
    let loginOn (target : Sync.Node) (i : Signer) (at? : Option String := none) :
        IO (Nat × String) := do
      let challenged ← Sync.handleSafe target
        ((Api.Req.simple "POST" ["challenge"]).withJson (Json.mkObj [("key", i.id)]))
      let nonce := jstr (payload challenged) "nonce"
      let signature := i.sign (Sync.challengeBytes nonce (at?.getD target.origin))
      let authenticated ← Sync.handleSafe target
        ((Api.Req.simple "POST" ["authenticate"]).withJson
          (Json.mkObj [("key", i.id), ("signature", signature)]))
      return (authenticated.code, jstr (payload authenticated) "token")
    let callOn (target : Sync.Node) (token method : String) (segs : List String) (body : Json) :
        IO Api.Reply :=
      Sync.handleSafe target
        (((Api.Req.simple method segs).withJson body).withHeaders
          [("authorization", "Bearer " ++ token)])
    let call := callOn node
    let get (token : String) (segs : List String) (query : List (String × String) := []) :
        IO Api.Reply :=
      Sync.handleSafe node
        (((Api.Req.simple "GET" segs).withQuery query).withHeaders
          [("authorization", "Bearer " ++ token)])
    let listOf (reply : Api.Reply) : Array Json := (payload reply).getArr?.toOption.getD #[]
    -- The body a member sends to publish their own agreement key, at a stated
    -- generation. Absent is zero, which is what a first key carries.
    let boxPkBody (i : Signer) (ledger : String) (generation : Nat := 0)
        (boxPk : String := i.boxPk) : Json :=
      Json.mkObj [("boxPk", boxPk), ("keyGeneration", Sync.jnat generation),
                  ("boxPkSignature", i.sign (Sync.memberBytes ledger i.id boxPk generation))]
    -- The body a realm admin — or a joiner — sends to put a grant on the record.
    let grantBody (issuer : Signer) (ledger realm : String) (generation : Nat)
        (member role : String) (wrapped : ByteArray) : Json :=
      Json.mkObj [("wrappedKey", Sync.toBase64 wrapped), ("role", role),
                  ("grantedBy", issuer.id),
                  ("signature", issuer.sign
                    (Sync.grantBytes ledger realm generation member role wrapped))]
    let mut r := r

    /- ## Encodings -/
    for sample in ["", "a", "ab", "abc", "abcd", "the whole of a receipt line"] do
      let round := (Sync.ofBase64? (Sync.toBase64 (cipher sample))).map Sync.toBase64
      r := checkEq r s!"base64 round-trips '{sample}'" round (some (Sync.toBase64 (cipher sample)))
    r := check r "a character base64 does not spell is refused" (Sync.ofBase64? "ab*d").isNone
    -- The decoder reads the characters as the bytes they are, so the case worth
    -- pinning is one that is more than a byte wide: every byte of it is 0x80 or
    -- above, which base64 does not spell either.
    r := check r "and so is one that is more than a byte wide" (Sync.ofBase64? "ab\u00e9d").isNone
    r := checkEq r "whitespace and padding are skipped wherever they fall"
      ((Sync.ofBase64? "YW\nJj ==").map Sync.toBase64) (some (Sync.toBase64 (cipher "abc")))
    r := checkEq r "hex round-trips" ((Sync.ofHex? "00ff10").map toHex) (some "00ff10")
    r := check r "odd hex is refused" (Sync.ofHex? "abc").isNone
    r := check r "a member id is 64 lowercase hex" (Sync.isMemberId alice.id)
    r := check r "uppercase is not a member id" (!Sync.isMemberId alice.id.toUpper)
    r := check r "and neither is a short one" (!Sync.isMemberId "a11ce0")

    /- ## Roles

    Two of them, the same two the ledger's own state has, and the list is
    closed: a role this binary has never heard of buys nothing, which is the
    difference between a field that is enforced and one that is decoration. -/
    r := checkEq r "there are two roles" Sync.roles ["viewer", "admin"]
    r := check r "a viewer writes" (Sync.mayWrite "viewer")
    r := check r "an admin writes too" (Sync.mayWrite "admin")
    r := check r "a role nobody defined writes nothing" (!Sync.mayWrite "editor")
    r := check r "only an admin administers" (Sync.mayAdminister "admin")
    r := check r "a viewer does not" (!Sync.mayAdminister "viewer")

    /- ## Timestamps

    The one place a client states a time. It is parsed rather than compared as a
    string, and normalised to one UTC shape, because version 1 did neither: `"z"`
    was an offer that never lapsed. -/
    r := checkEq r "the epoch is second zero" (Sync.isoSeconds? "1970-01-01T00:00:00Z") (some 0)
    r := checkEq r "a day later is a day of seconds"
      (Sync.isoSeconds? "1970-01-02T00:00:00") (some 86400)
    r := checkEq r "a leap year is counted"
      (Sync.isoSeconds? "2000-03-01T00:00:00Z") (some 951868800)
    r := checkEq r "the calendar runs backwards too" (Sync.civilFromDays 0) (1970, 1, 1)
    r := checkEq r "a fractional second is dropped, and the zone made explicit"
      (Sync.isoNormalise? "2026-09-18T03:04:05.123456Z") (some "2026-09-18T03:04:05Z")
    r := checkEq r "a naive stamp is read as the UTC it has to be"
      (Sync.isoNormalise? "2026-09-18T03:04:05") (some "2026-09-18T03:04:05Z")
    r := check r "a string that is not a time is not one" (Sync.isoSeconds? "z").isNone
    r := check r "a month that does not exist is refused"
      (Sync.isoSeconds? "2026-13-01T00:00:00Z").isNone
    r := check r "and a day that does not" (Sync.isoSeconds? "2026-02-30T00:00:00Z").isNone
    r := check r "a zone offset is refused rather than converted"
      (Sync.isoSeconds? "2026-09-18T03:04:05+02:00").isNone
    r := check r "and so is trailing rubbish" (Sync.isoSeconds? "2026-09-18T03:04:05Zed").isNone

    /- ## The canonical byte strings

    Pinned as literals, because they are the interface a client in another
    language has to reproduce exactly, and a mistake in one of them shows up as
    "the signature does not verify" with nothing to say why. -/
    r := checkEq r "a challenge names the sequencer it is answered to"
      ((String.fromUTF8? (Sync.challengeBytes "beef" origin)).getD "")
      ("26:resources/seq/v2/challenge" ++ s!"{origin.utf8ByteSize}:{origin}" ++ "4:beef")
    r := checkEq r "a join proof covers the ledger, the realm and the joiner"
      ((String.fromUTF8? (Sync.joinBytes "home" "money" carol.id)).getD "")
      ("17:resources/join/v14:home5:money64:" ++ carol.id)
    r := checkEq r "a member's agreement key is signed under their own id and its generation"
      ((String.fromUTF8? (Sync.memberBytes "home" alice.id "aabb")).getD "")
      ("19:resources/member/v14:home64:" ++ alice.id ++ "1:04:aabb")
    r := checkEq r "and the generation is what tells one of their keys from the next"
      ((String.fromUTF8? (Sync.memberBytes "home" alice.id "aabb" 3)).getD "")
      ("19:resources/member/v14:home64:" ++ alice.id ++ "1:34:aabb")
    r := checkEq r "a grant names realm, generation, member, role and the wrapped key"
      ((String.fromUTF8? (Sync.grantBytes "home" "money" 2 bob.id "viewer" (cipher "wk"))).getD "")
      ("18:resources/grant/v14:home5:money1:264:" ++ bob.id ++ "6:viewer2:wk")
    let pinnedEnvelope : Sync.Envelope :=
      { ledger := "home", seq := 1, prevHash := "", author := alice.id,
        parts := [partOf "money" 0 "one"], signature := "ab" }
    r := checkEq r "an envelope's signature covers each part's digest, not its bytes"
      ((String.fromUTF8? pinnedEnvelope.signingBytes).getD "")
      ("29:resources/seq/v2/envelope-sig4:home1:10:64:" ++ alice.id ++ "1:15:money1:064:"
        ++ Sha256.hexBytes (cipher "one"))
    r := checkEq r "and its hash covers the same fields plus the signature"
      ((String.fromUTF8? pinnedEnvelope.hashBytes).getD "")
      ("25:resources/seq/v2/envelope4:home1:10:64:" ++ alice.id ++ "1:15:money1:064:"
        ++ Sha256.hexBytes (cipher "one") ++ "2:ab")
    let pinnedCommitment : Sync.Checkpoint :=
      { ledger := "home", realm := "money", generation := 1, seq := 3, stateHash := "ab",
        headHash := "cd", author := alice.id, signature := "00", snapshot := ByteArray.empty }
    r := checkEq r "a checkpoint commitment covers the head and the snapshot it ships with"
      ((String.fromUTF8? pinnedCommitment.commitmentBytes).getD "")
      ("27:resources/seq/v2/checkpoint4:home5:money1:11:32:ab2:cd64:"
        ++ Sha256.hexBytes ByteArray.empty)

    /- ## Health -/
    let health ← Sync.handleSafe node (Api.Req.simple "GET" ["health"])
    r := checkEq r "the schema is on the migration blobs became bytes in"
      (jnat (payload health) "schema") 6
    r := checkEq r "health says which verifier is running"
      (jstr (payload health) "verifier") "insecure"
    r := checkEq r "and which origin it binds challenges to"
      (jstr (payload health) "origin") origin
    r := checkEq r "a sequencer with no scheme bound says so"
      Sync.Verifier.rejectAll.name "reject-all"

    /- ## Authentication is a signature over the nonce, at this origin -/
    let (aliceCode, aliceTok) ← loginOn node alice
    r := checkEq r "a signature over the challenge opens a session" aliceCode 200
    r := check r "which hands out a bearer token" (aliceTok.startsWith "seq_")
    let elsewhere ← loginOn node bob (at? := some "https://evil.example/seq")
    r := checkEq r "a signature taken for another sequencer does not open one here"
      elsewhere.1 401
    let challenged ← Sync.handleSafe node
      ((Api.Req.simple "POST" ["challenge"]).withJson (Json.mkObj [("key", bob.id)]))
    let liveNonce := jstr (payload challenged) "nonce"
    r := checkEq r "a challenge states the origin it is to be answered at"
      (jstr (payload challenged) "origin") origin
    r := checkEq r "a signature over another nonce is refused"
      (← Sync.handleSafe node ((Api.Req.simple "POST" ["authenticate"]).withJson
        (Json.mkObj [("key", bob.id),
                     ("signature", bob.sign (Sync.challengeBytes "deadbeef" origin))]))).code 401
    r := checkEq r "so is somebody else's signature over the right nonce"
      (← Sync.handleSafe node ((Api.Req.simple "POST" ["authenticate"]).withJson
        (Json.mkObj [("key", bob.id),
                     ("signature", carol.sign (Sync.challengeBytes liveNonce origin))]))).code 401
    -- The client's half of M7 is a comparison it can only make if it has all
    -- three strings, so the reply that hands out the token states the origin
    -- too: a node checks `health`'s origin, the challenge's and this one against
    -- the URL it dialled, and a relay that repeats the real sequencer's answers
    -- is still not the host that was typed.
    let dave := party "dave"
    let daveNonce ← Sync.handleSafe node
      ((Api.Req.simple "POST" ["challenge"]).withJson (Json.mkObj [("key", dave.id)]))
    let daveAuth ← Sync.handleSafe node ((Api.Req.simple "POST" ["authenticate"]).withJson
      (Json.mkObj [("key", dave.id),
                   ("signature", dave.sign
                     (Sync.challengeBytes (jstr (payload daveNonce) "nonce") origin))]))
    r := checkEq r "the reply that hands out a token names the origin it was signed for"
      (jstr (payload daveAuth) "origin") origin
    r := checkEq r "a key that is not 64 hex characters is refused before anything else"
      (← Sync.handleSafe node ((Api.Req.simple "POST" ["challenge"]).withJson
        (Json.mkObj [("key", "a11ce0")]))).code 400
    r := checkEq r "an unauthenticated route is a 401"
      (← Sync.handleSafe node (Api.Req.simple "GET" ["ledgers", "home", "head"])).code 401
    -- RFC 7235 makes the scheme name case-insensitive, and a conforming client
    -- that sent `bearer` used to get 401s with nothing to say why. There is no
    -- ledger yet, so a session that is honoured gets a 404 and one that is not
    -- gets a 401: the two are easy to tell apart before there is anything to
    -- read.
    let withScheme (scheme : String) : IO Api.Reply :=
      Sync.handleSafe node ((Api.Req.simple "GET" ["ledgers", "home", "head"]).withHeaders
        [("authorization", scheme ++ aliceTok)])
    r := checkEq r "the bearer scheme is matched in lower case" (← withScheme "bearer ").code 404
    r := checkEq r "and in upper" (← withScheme "BEARER ").code 404
    r := checkEq r "another scheme is not a session" (← withScheme "Basic ").code 401

    /- ## What a refusal says, and what it does not

    A route that turns its caller away says why. Everything else — SQLite naming
    a table, `IO.FS` naming a path — is logged against a correlation id and
    answered with a sentence that gives nothing away. -/
    let malformed ← Sync.handleSafe node
      ((Api.Req.simple "POST" ["challenge"]).withBody "{\"key\":".toUTF8)
    r := checkEq r "a body that is not JSON is refused in those words" malformed.code 400
    r := checkEq r "with nothing of the parser in it"
      (jstr (payload malformed) "error") "the body is not JSON"
    let mistyped ← Sync.handleSafe node
      ((Api.Req.simple "POST" ["challenge"]).withJson (Json.mkObj [("key", Sync.jnat 5)]))
    r := checkEq r "a field of the wrong type is named" (jstr (payload mistyped) "error")
      "'key' must be a string"
    r := check r "and neither reply carries the marker that sorts the two apart"
      (((jstr (payload malformed) "error").splitOn "resources/client").length == 1
        && ((jstr (payload mistyped) "error").splitOn "resources/client").length == 1)

    /- ## Body caps and the numbers inside a body -/
    r := checkEq r "a challenge reads four kilobytes"
      (Sync.bodyLimit {} "POST" ["challenge"]) (4 * 1024)
    -- An append used to read a megabyte, which is generous for every entry but
    -- the first one: a genesis is a whole store as one snapshot, and a ledger
    -- kept for years does not fit in it.
    r := checkEq r "an append reads sixteen megabytes"
      (Sync.bodyLimit {} "POST" ["ledgers", "home", "events"]) (16 * 1024 * 1024)
    r := checkEq r "and so does a checkpoint, which carries that same state sealed"
      (Sync.bodyLimit {} "PUT" ["ledgers", "home", "realms", "money", "checkpoint"])
      (16 * 1024 * 1024)
    r := checkEq r "a blob reads sixteen"
      (Sync.bodyLimit {} "PUT" ["ledgers", "home", "blobs", "h"]) (16 * 1024 * 1024)
    r := checkEq r "and everything else sixty-four kilobytes"
      (Sync.bodyLimit {} "POST" ["ledgers", "home", "realms"]) (64 * 1024)
    r := checkEq r "the two generous ones are the number a deployment may set"
      (Sync.bodyLimit { maxAppendBytes := 99 } "POST" ["ledgers", "home", "events"]) 99
    r := checkEq r "and the small ones are not"
      (Sync.bodyLimit { maxAppendBytes := 99 } "POST" ["challenge"]) (4 * 1024)
    let oversized := (String.ofList (List.replicate 5000 'x')).toUTF8
    r := checkEq r "a body over the route's cap is refused without being parsed"
      (← Sync.handleSafe node ((Api.Req.simple "POST" ["challenge"]).withBody oversized)).code 413
    r := check r "an exponent no field uses is spotted before the parser evaluates it"
      (Sync.hasHugeExponent "{\"key\":1e1000000000}".toUTF8)
    r := check r "a modest one is not" (!Sync.hasHugeExponent "{\"n\":1e9}".toUTF8)
    r := check r "and neither is one inside a string"
      (!Sync.hasHugeExponent "{\"key\":\"cafe1e1000000000\"}".toUTF8)
    r := checkEq r "a body carrying one is refused"
      (← Sync.handleSafe node
        ((Api.Req.simple "POST" ["challenge"]).withBody "{\"key\":1e1000000000}".toUTF8)).code 400

    /- ## Creating a ledger, which not everybody may -/
    let (_, carolTok) ← loginOn node carol
    r := checkEq r "a key that is not on the creator list may not make a ledger"
      (← call carolTok "POST" ["ledgers"] (Json.mkObj [("ledger", "theirs")])).code 403
    let created ← call aliceTok "POST" ["ledgers"] (Json.mkObj [("ledger", "home")])
    r := checkEq r "a key that is on it may" created.code 201
    r := checkEq r "creating it twice is a conflict"
      (← call aliceTok "POST" ["ledgers"] (Json.mkObj [("ledger", "home")])).code 409
    let noCreators ← Sync.Node.make log verifier {} origin (some #[]) (testOnly := true)
    let (_, strandedTok) ← loginOn noCreators alice
    r := checkEq r "a sequencer that lists nobody takes no new ledgers at all"
      (← callOn noCreators strandedTok "POST" ["ledgers"]
        (Json.mkObj [("ledger", "nowhere")])).code 403
    let members := listOf (← get aliceTok ["ledgers", "home", "members"])
    r := checkEq r "its creator is its only member" members.size 1
    r := check r "and administrates it" (jbool (members[0]!) "admin" false)
    -- Not even the creator gets an agreement key out of making a ledger: there
    -- is one route that writes one, and it takes the member's own signature.
    r := checkEq r "with no agreement key yet" (jstr (members[0]!) "boxPk") ""
    r := checkEq r "which they publish for themselves"
      (← call aliceTok "PUT" ["ledgers", "home", "members", alice.id, "boxPk"]
        (boxPkBody alice "home")).code 200
    r := checkEq r "and it is theirs"
      (jstr (listOf (← get aliceTok ["ledgers", "home", "members"]))[0]! "boxPk") alice.boxPk

    /- ## An agreement key is the member's own claim and nobody else's -/
    r := checkEq r "an admin adds a member"
      (← call aliceTok "POST" ["ledgers", "home", "members", bob.id] (Json.mkObj [])).code 201
    let twoMembers := listOf (← get aliceTok ["ledgers", "home", "members"])
    r := checkEq r "the ledger now has two members" twoMembers.size 2
    let bobRecord := (twoMembers.find? (fun m => jstr m "member" == bob.id)).getD Json.null
    r := checkEq r "a member record carries the signing key that is their id"
      (jstr bobRecord "signPk") bob.id
    r := checkEq r "and no agreement key, because an admin cannot publish one for them"
      (jstr bobRecord "boxPk") ""
    r := checkEq r "an admin who tries to publish one anyway is ignored"
      (jstr (payload (← call aliceTok "POST" ["ledgers", "home", "members", bob.id]
        (Json.mkObj [("boxPk", carol.boxPk)]))) "boxPk") ""
    let (_, bobTok) ← loginOn node bob
    r := checkEq r "a member publishes their own, with their own signature over it"
      (← call bobTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (boxPkBody bob "home")).code 200
    let publishedBob := listOf (← get aliceTok ["ledgers", "home", "members"])
    let bobNow := (publishedBob.find? (fun m => jstr m "member" == bob.id)).getD Json.null
    r := checkEq r "and it is the key they signed for" (jstr bobNow "boxPk") bob.boxPk
    r := check r "with the signature beside it, so every reader can ask again"
      (suite.verify ((Sync.ofHex? bob.id).getD ByteArray.empty)
        (Sync.memberBytes "home" bob.id bob.boxPk)
        ((Sync.ofHex? (jstr bobNow "boxPkSignature")).getD ByteArray.empty))
    r := checkEq r "a signature that is not over that key is refused"
      (← call bobTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (Json.mkObj [("boxPk", carol.boxPk),
                     ("boxPkSignature",
                       bob.sign (Sync.memberBytes "home" bob.id bob.boxPk))])).code 403
    r := checkEq r "and a member may not publish anybody else's"
      (← call aliceTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (boxPkBody bob "home")).code 403

    /- ## An agreement key can be replaced, and only by a later one

    Without a generation, the first `(boxPk, signature)` pair a member ever
    published stayed a valid self-attestation for ever: a sequencer that kept
    serving it had every later rotation sealed to the key whose secret half had
    leaked, and the member had no way to say "not that one". -/
    r := checkEq r "a member's first key sits at generation zero"
      (jnat bobNow "keyGeneration") 0
    r := checkEq r "replacing it at the same generation is refused"
      (← call bobTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (boxPkBody bob "home" 0 carol.boxPk)).code 409
    r := checkEq r "a later generation is how a key is replaced"
      (← call bobTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (boxPkBody bob "home" 1 carol.boxPk)).code 200
    r := checkEq r "a generation below the one on the record is refused"
      (← call bobTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (boxPkBody bob "home" 0 bob.boxPk)).code 409
    let rotated := listOf (← get aliceTok ["ledgers", "home", "members"])
    let bobRotated := (rotated.find? (fun m => jstr m "member" == bob.id)).getD Json.null
    r := checkEq r "the record carries the newest key" (jstr bobRotated "boxPk") carol.boxPk
    r := checkEq r "at the generation it was published under"
      (jnat bobRotated "keyGeneration") 1
    r := check r "signed over that generation, which every reader checks for themselves"
      (suite.verify ((Sync.ofHex? bob.id).getD ByteArray.empty)
        (Sync.memberBytes "home" bob.id carol.boxPk 1)
        ((Sync.ofHex? (jstr bobRotated "boxPkSignature")).getD ByteArray.empty))
    r := check r "so the attestation for the old key no longer verifies at the new generation"
      (!suite.verify ((Sync.ofHex? bob.id).getD ByteArray.empty)
        (Sync.memberBytes "home" bob.id bob.boxPk 1)
        ((Sync.ofHex? (jstr bobRotated "boxPkSignature")).getD ByteArray.empty))
    r := checkEq r "and bob puts his own key back, one generation further on"
      (← call bobTok "PUT" ["ledgers", "home", "members", bob.id, "boxPk"]
        (boxPkBody bob "home" 2)).code 200

    r := checkEq r "a stranger cannot tell a ledger they are not in from one that is not there"
      (← get carolTok ["ledgers", "home", "members"]).code 404
    r := checkEq r "which is the same answer a ledger that is not there gives"
      (← get carolTok ["ledgers", "nosuch", "members"]).code 404

    /- ## The last admin cannot be taken away -/
    r := checkEq r "the only admin cannot be demoted"
      (← call aliceTok "POST" ["ledgers", "home", "members", alice.id]
        (Json.mkObj [("admin", Json.bool false)])).code 400
    r := checkEq r "nor removed"
      (← call aliceTok "DELETE" ["ledgers", "home", "members", alice.id] (Json.mkObj [])).code 400
    r := checkEq r "a second admin is made"
      (← call aliceTok "POST" ["ledgers", "home", "members", bob.id]
        (Json.mkObj [("admin", Json.bool true)])).code 201
    r := check r "a re-post that says nothing about the flag leaves it alone"
      (jbool (payload (← call aliceTok "POST" ["ledgers", "home", "members", bob.id]
        (Json.mkObj []))) "admin" false)
    r := checkEq r "with two of them, one may be demoted"
      (← call aliceTok "POST" ["ledgers", "home", "members", bob.id]
        (Json.mkObj [("admin", Json.bool false)])).code 201
    let afterDemote := listOf (← get aliceTok ["ledgers", "home", "members"])
    r := check r "and the demotion took"
      (!jbool ((afterDemote.find? (fun m => jstr m "member" == bob.id)).getD Json.null)
        "admin" true)
    r := checkEq r "a member id that is not one is refused"
      (← call aliceTok "POST" ["ledgers", "home", "members", "b0bb1e"] (Json.mkObj [])).code 400

    /- ## Realms and grants, each carrying the signature of whoever made it -/
    r := checkEq r "a member creates a realm"
      (← call aliceTok "POST" ["ledgers", "home", "realms"] (Json.mkObj [("realm", "money")])).code
      201
    let aliceKey := cipher "money-key-for-alice"
    let granted ← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", alice.id]
      (grantBody alice "home" "money" 0 alice.id "admin" aliceKey)
    r := checkEq r "the realm's admin grants themselves the key" granted.code 201
    r := checkEq r "at the realm's current generation" (jnat (payload granted) "generation") 0
    r := checkEq r "recorded as issued by them" (jstr (payload granted) "grantedBy") alice.id
    r := check r "with a signature a reader can check for themselves"
      (suite.verify ((Sync.ofHex? alice.id).getD ByteArray.empty)
        (Sync.grantBytes "home" "money" 0 alice.id "admin" aliceKey)
        ((Sync.ofHex? (jstr (payload granted) "signature")).getD ByteArray.empty))
    r := checkEq r "a grant with no signature at all is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (Json.mkObj [("wrappedKey", Sync.toBase64 (cipher "k"))])).code 403
    r := checkEq r "a grant signed over another role is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (Json.mkObj [("wrappedKey", Sync.toBase64 (cipher "k")), ("role", "admin"),
                     ("grantedBy", alice.id),
                     ("signature", alice.sign
                       (Sync.grantBytes "home" "money" 0 bob.id "viewer" (cipher "k")))])).code 403
    r := checkEq r "a grant signed over another generation is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (grantBody alice "home" "money" 7 bob.id "viewer" (cipher "k"))).code 403
    r := checkEq r "a grant signed over another member is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (grantBody alice "home" "money" 0 carol.id "viewer" (cipher "k"))).code 403
    r := checkEq r "a grant whose issuer is not the caller is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (grantBody bob "home" "money" 0 bob.id "viewer" (cipher "k"))).code 403
    r := checkEq r "and one from somebody who does not administrate the realm is refused"
      (← call bobTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (grantBody bob "home" "money" 0 bob.id "viewer" (cipher "k"))).code 403
    let bobKey := cipher "money-key-for-bob"
    r := checkEq r "the realm's admin grants the other member"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "grants", bob.id]
        (grantBody alice "home" "money" 0 bob.id "viewer" bobKey)).code 201
    let bobGrant ← get aliceTok ["ledgers", "home", "realms", "money", "grants", bob.id]
    r := checkEq r "a grant hands back the wrapped key"
      ((Sync.ofBase64? (jstr (payload bobGrant) "wrappedKey")).map Sync.toBase64)
      (some (Sync.toBase64 bobKey))

    /- ## Appending, with every signature and every digest checked -/
    let head0 ← get aliceTok ["ledgers", "home", "head"]
    r := checkEq r "an empty ledger has no head" (jnat (payload head0) "seq") 0
    r := checkEq r "and an empty hash" (jstr (payload head0) "hash") ""
    let one := signedEnvelope alice "home" 1 "" [partOf "money" 0 "one"]
    let firstReply ← call aliceTok "POST" ["ledgers", "home", "events"] one.toJson
    r := checkEq r "the first envelope is accepted" firstReply.code 201
    r := checkEq r "and becomes the head"
      (jstr (jsub (payload firstReply) "head") "hash") one.hash
    r := checkEq r "an envelope whose signature does not verify is refused"
      (← call aliceTok "POST" ["ledgers", "home", "events"]
        { one with seq := 2, prevHash := one.hash,
                   signature := bob.sign one.signingBytes }.toJson).code 403
    r := checkEq r "so is one signed over different parts"
      (← call aliceTok "POST" ["ledgers", "home", "events"]
        { signedEnvelope alice "home" 2 one.hash [partOf "money" 0 "two"] with
            parts := [partOf "money" 0 "three"] }.toJson).code 403
    -- The digest is what the signature covers, so it is checked against the
    -- bytes before anything else: a part whose digest does not name its own
    -- ciphertext would be served to every other reader as something nobody
    -- signed.
    let lying := signedEnvelope alice "home" 2 one.hash
      [{ partOf "money" 0 "two" with cipherHash := Sha256.hexBytes (cipher "something else") }]
    r := checkEq r "a part that does not hash to its stated digest is refused"
      (← call aliceTok "POST" ["ledgers", "home", "events"] lying.toJson).code 400
    let hollow := signedEnvelope alice "home" 2 one.hash [(partOf "money" 0 "two").stripped]
    r := checkEq r "and so is one that carries no ciphertext at all"
      (← call aliceTok "POST" ["ledgers", "home", "events"] hollow.toJson).code 400
    let two := signedEnvelope alice "home" 2 one.hash [partOf "money" 0 "two"]
    r := checkEq r "the second envelope is accepted"
      (← call aliceTok "POST" ["ledgers", "home", "events"] two.toJson).code 201
    let head2 ← get aliceTok ["ledgers", "home", "head"]
    r := checkEq r "the head has moved on" (jnat (payload head2) "seq") 2
    r := checkEq r "to the second envelope" (jstr (payload head2) "hash") two.hash

    /- ## Compare and swap -/
    let replayed ← call aliceTok "POST" ["ledgers", "home", "events"] two.toJson
    r := checkEq r "replaying an envelope is a conflict" replayed.code 409
    r := checkEq r "which carries the head the client missed"
      (jnat (jsub (payload replayed) "head") "seq") 2
    r := checkEq r "and its hash, so the client can rebase"
      (jstr (jsub (payload replayed) "head") "hash") two.hash

    /- ## Who may append -/
    let stranger := signedEnvelope carol "home" 3 two.hash [partOf "money" 0 "psst"]
    r := checkEq r "a non-member cannot append"
      (← call carolTok "POST" ["ledgers", "home", "events"] stranger.toJson).code 404
    r := checkEq r "and a member cannot append in somebody else's name"
      (← call bobTok "POST" ["ledgers", "home", "events"] stranger.toJson).code 403

    /- ## Which realms a part may name -/
    -- Creating a realm is first-write-wins, so a member who may write anywhere
    -- in a ledger could otherwise squat every name in it: the record would
    -- stand in every reader's state naming the squatter its sole admin, and
    -- the honest creation of that name afterwards would be refused for ever.
    r := checkEq r "a member who does not administer the ledger may not create a realm"
      (← call bobTok "POST" ["ledgers", "home", "realms"]
        (Json.mkObj [("realm", "squatted")])).code 403
    r := checkEq r "so the name is still there for somebody who may"
      (← call aliceTok "POST" ["ledgers", "home", "realms"]
        (Json.mkObj [("realm", "squatted")])).code 201
    r := checkEq r "a second realm is created"
      (← call aliceTok "POST" ["ledgers", "home", "realms"]
        (Json.mkObj [("realm", "private")])).code 201
    let ungranted := signedEnvelope alice "home" 3 two.hash [partOf "private" 0 "psst"]
    r := checkEq r "a part in a realm the author holds no grant on is refused"
      (← call aliceTok "POST" ["ledgers", "home", "events"] ungranted.toJson).code 403
    r := checkEq r "and nothing was written"
      (jnat (payload (← get aliceTok ["ledgers", "home", "head"])) "seq") 2

    /- ## A fetch carries only what the caller may read, and still hashes whole -/
    r := checkEq r "the realm's admin grants themselves the second realm"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "private", "grants", alice.id]
        (grantBody alice "home" "private" 0 alice.id "admin" (cipher "private-key"))).code 201
    let mixed := signedEnvelope alice "home" 3 two.hash
      [partOf "money" 0 "three", partOf "private" 0 "psst"]
    r := checkEq r "an envelope touching two realms is accepted"
      (← call aliceTok "POST" ["ledgers", "home", "events"] mixed.toJson).code 201
    let mine ← get aliceTok ["ledgers", "home", "events"] [("since", "2")]
    let theirs ← get bobTok ["ledgers", "home", "events"] [("since", "2")]
    let minePart := (jarr (payload mine) "events")[0]?.getD Json.null
    let theirsPart := (jarr (payload theirs) "events")[0]?.getD Json.null
    r := checkEq r "the author sees both parts" (jarr minePart "parts").size 2
    r := checkEq r "a member granted one realm still sees both" (jarr theirsPart "parts").size 2
    let withheld := ((jarr theirsPart "parts").find?
      (fun p => jstr p "realm" == "private")).getD Json.null
    r := check r "but the one they hold no key for carries no ciphertext"
      ((withheld.getObjVal? "ciphertext").toOption.isNone)
    r := checkEq r "only the digest the signature was taken over"
      (jstr withheld "cipherHash") (Sha256.hexBytes (cipher "psst"))
    let readable := ((jarr theirsPart "parts").find?
      (fun p => jstr p "realm" == "money")).getD Json.null
    r := checkEq r "and the one they do hold carries its bytes"
      ((Sync.ofBase64? (jstr readable "ciphertext")).map Sync.toBase64)
      (some (Sync.toBase64 (cipher "three")))
    r := checkEq r "the filtered envelope still carries the hash of the whole"
      (jstr theirsPart "hash") mixed.hash
    -- The point of version 2: a reader who was handed half of it can recompute
    -- that hash and check that signature, rather than being told them.
    let reread := (Sync.Envelope.ofJson? theirsPart).toOption.getD default
    r := checkEq r "which a filtered reader recomputes for themselves" reread.hash mixed.hash
    r := check r "and checks the author's signature against, having seen no ciphertext"
      (suite.verify ((Sync.ofHex? alice.id).getD ByteArray.empty) reread.signingBytes
        ((Sync.ofHex? reread.signature).getD ByteArray.empty))

    /- ## One entry by position -/
    let single ← get aliceTok ["ledgers", "home", "events", "3"]
    r := checkEq r "an entry is fetched by position" single.code 200
    r := checkEq r "and is the one asked for" (jnat (payload single) "seq") 3
    r := checkEq r "carrying the hash of the whole" (jstr (payload single) "hash") mixed.hash
    r := checkEq r "a position the ledger has not reached is a 404"
      (← get aliceTok ["ledgers", "home", "events", "99"]).code 404
    r := checkEq r "position zero is not an entry"
      (← get aliceTok ["ledgers", "home", "events", "0"]).code 404
    r := checkEq r "and a position that is not a number is a 400"
      (← get aliceTok ["ledgers", "home", "events", "head"]).code 400

    /- ## Twelve writers at once

    One SQLite connection and a thread pool: without the store's mutex the
    second `BEGIN IMMEDIATE` fails and its rollback aborts the first writer's
    transaction, which is exactly how a compare-and-swap stops being one. What
    the mutex buys is that twelve simultaneous attempts on the same position
    produce one entry and eleven clients told where the head went. -/
    let contested := signedEnvelope alice "home" 4 mixed.hash [partOf "money" 0 "contested"]
    let racers ← (List.range 12).mapM fun _ =>
      IO.asTask (call aliceTok "POST" ["ledgers", "home", "events"] contested.toJson)
        Task.Priority.dedicated
    let outcomes ← racers.mapM fun t => do
      match ← IO.wait t with
      | .ok reply => pure reply.code
      | .error _ => pure 500
    r := checkEq r "one of twelve simultaneous appends is placed"
      (outcomes.filter (· == 201)).length 1
    r := checkEq r "and the other eleven are told the head has moved"
      (outcomes.filter (· == 409)).length 11
    r := checkEq r "the order gained exactly one entry"
      (jnat (payload (← get aliceTok ["ledgers", "home", "head"])) "seq") 4

    /- ## Checkpoints: one per author, and the snapshot is inside the commitment -/
    let commit (i : Signer) (realm : String) (generation seq : Nat) (state head : String)
        (snapshot : ByteArray) : Sync.Checkpoint :=
      let unsigned : Sync.Checkpoint :=
        { ledger := "home", realm, generation, seq, stateHash := state, headHash := head,
          author := i.id, signature := "", snapshot }
      { unsigned with signature := i.sign unsigned.commitmentBytes }
    let headNow ← Sync.Log.head log "home"
    let aliceCommit := commit alice "money" 0 4 "alice-state" headNow.hash (cipher "snapshot-a")
    r := checkEq r "a checkpoint is written"
      (← call aliceTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        aliceCommit.toJson).code 200
    r := checkEq r "a checkpoint whose signature does not verify is refused"
      (← call aliceTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        { aliceCommit with signature := bob.sign aliceCommit.commitmentBytes }.toJson).code 403
    -- The snapshot is inside the commitment now, so swapping the bytes and
    -- keeping the signature no longer produces something a reader would take.
    r := checkEq r "a checkpoint whose snapshot was swapped under its signature is refused"
      (← call aliceTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        { aliceCommit with snapshot := cipher "a different snapshot" }.toJson).code 403
    r := checkEq r "a checkpoint naming another envelope as its head is refused"
      (← call aliceTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        (commit alice "money" 0 4 "alice-state" two.hash (cipher "snapshot-a")).toJson).code 400
    r := checkEq r "and one taken at a position the ledger has not reached"
      (← call aliceTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        (commit alice "money" 0 99 "alice-state" headNow.hash (cipher "s")).toJson).code 400
    r := checkEq r "an author may not roll their own commitment backwards"
      (← call aliceTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        (commit alice "money" 0 2 "older" two.hash (cipher "snapshot-a")).toJson).code 409
    let bobCommit := commit bob "money" 0 2 "bob-state" two.hash (cipher "snapshot-b")
    r := checkEq r "another grant holder publishes their own, further back"
      (← call bobTok "PUT" ["ledgers", "home", "realms", "money", "checkpoint"]
        bobCommit.toJson).code 200
    let checkpoints := listOf (← get aliceTok ["ledgers", "home", "realms", "money", "checkpoint"])
    r := checkEq r "a realm carries one checkpoint per author" checkpoints.size 2
    r := checkEq r "furthest along first" (jnat (checkpoints[0]!) "seq") 4
    r := checkEq r "and the second one did not overwrite the first"
      (jstr ((checkpoints.find? (fun c => jstr c "author" == alice.id)).getD Json.null) "stateHash")
      "alice-state"
    let bobsCommitment := (checkpoints.find? (fun c => jstr c "author" == bob.id)).getD Json.null
    r := checkEq r "each carries the digest of the snapshot it ships with"
      (jstr bobsCommitment "snapshotHash") (Sha256.hexBytes (cipher "snapshot-b"))
    r := checkEq r "a member without a grant cannot read them"
      (← get bobTok ["ledgers", "home", "realms", "private", "checkpoint"]).code 403

    /- ## Revoking -/
    let revoked ← call aliceTok "DELETE" ["ledgers", "home", "realms", "money", "grants", bob.id]
      (Json.mkObj [])
    r := checkEq r "a revoke succeeds" revoked.code 200
    r := checkEq r "and bumps the generation" (jnat (payload revoked) "generation") 1
    r := checkEq r "the revoked grant is gone"
      (← get aliceTok ["ledgers", "home", "realms", "money", "grants", bob.id]).code 404
    let headAfter ← Sync.Log.head log "home"
    let stale := signedEnvelope alice "home" 5 headAfter.hash [partOf "money" 0 "four"]
    r := checkEq r "a part under the revoked generation is refused"
      (← call aliceTok "POST" ["ledgers", "home", "events"] stale.toJson).code 403
    r := checkEq r "the survivor is re-granted at the new generation"
      (jnat (payload (← call aliceTok "POST"
        ["ledgers", "home", "realms", "money", "grants", alice.id]
        (grantBody alice "home" "money" 1 alice.id "admin" (cipher "money-key-2")))) "generation")
      1
    let fresh := signedEnvelope alice "home" 5 headAfter.hash [partOf "money" 1 "four"]
    r := checkEq r "and the order carries on under it"
      (← call aliceTok "POST" ["ledgers", "home", "events"] fresh.toJson).code 201
    r := checkEq r "the head is the re-keyed envelope"
      (jstr (payload (← get aliceTok ["ledgers", "home", "head"])) "hash") fresh.hash

    /- ## What one envelope may carry

    Each part costs a base64 decode and a SHA-256, and the body cap alone let a
    body of JSON spell tens of thousands of them -- the more so now that the cap
    is sixteen megabytes. Both are done before the store is locked, and both are
    bounded. -/
    r := checkEq r "sixty-four parts is the default cap" ({} : Sync.Limits).maxParts 64
    r := checkEq r "and 8 MiB the default part, which is what a genesis needs"
      ({} : Sync.Limits).maxPartBytes (8 * 1024 * 1024)
    r := checkEq r "with 16 MiB of body around it"
      ({} : Sync.Limits).maxAppendBytes (16 * 1024 * 1024)
    let capped ← Sync.Node.make log verifier { maxParts := 2, maxPartBytes := 8 } origin none
      (testOnly := true)
    let (_, cappedTok) ← loginOn capped alice
    let threeParts := signedEnvelope alice "home" 99 fresh.hash
      [partOf "money" 1 "a", partOf "money" 1 "b", partOf "money" 1 "c"]
    r := checkEq r "an envelope carrying more parts than the cap is refused"
      (← callOn capped cappedTok "POST" ["ledgers", "home", "events"] threeParts.toJson).code 400
    let fatPart := signedEnvelope alice "home" 99 fresh.hash
      [partOf "money" 1 "more than eight bytes of ciphertext"]
    r := checkEq r "and so is one whose part carries more bytes than the cap"
      (← callOn capped cappedTok "POST" ["ledgers", "home", "events"] fatPart.toJson).code 400
    -- The decode, the caps and the digests are all `prepare`'s work, which
    -- happens before `handleSafe` takes the store's mutex.
    let asAppend (e : Sync.Envelope) : Api.Req :=
      (Api.Req.simple "POST" ["ledgers", "home", "events"]).withJson e.toJson
    let preparedParts ← Sync.prepare { maxParts := 2 } (asAppend threeParts)
    r := check r "the cap is taken before the store is locked"
      (match preparedParts.envelope with | some (.error _) => true | _ => false)
    let preparedGood ← Sync.prepare {} (asAppend fresh)
    r := check r "and a sound envelope is decoded and hashed there too"
      (match preparedGood.envelope with
       | some (.ok e) => e.parts.length == 1 && e.parts.all (·.intact)
       | _ => false)
    let preparedLying ← Sync.prepare {} (asAppend lying)
    r := check r "which is where a part that lies about its digest is caught"
      (match preparedLying.envelope with | some (.error _) => true | _ => false)
    let preparedRead ← Sync.prepare {} (Api.Req.simple "GET" ["ledgers", "home", "events"])
    r := check r "a request that is not an append prepares no envelope"
      preparedRead.envelope.isNone

    /- ## Rate limiting -/
    -- The same store behind a bucket of one that never refills. The limit is
    -- taken before the append is attempted, so the second request is turned away
    -- rather than reaching the order at all.
    let tight ← Sync.Node.make log verifier
      { burst := 1, perSecond := 0 } origin (some #[alice.id]) (testOnly := true)
    let (_, tightTok) ← loginOn tight alice
    let sixth := signedEnvelope alice "home" 6 fresh.hash [partOf "money" 1 "five"]
    let tightCall : IO Api.Reply :=
      callOn tight tightTok "POST" ["ledgers", "home", "events"] sixth.toJson
    r := checkEq r "the first append fits in the bucket" (← tightCall).code 201
    r := checkEq r "the next one is refused" (← tightCall).code 429

    /- ## An entry the size of a genesis

    The first entry of a shared order is a whole store as one `Op.snapshot`, so
    for a ledger somebody has kept for years it is megabytes rather than the
    kilobytes every later entry is. That is the one entry a ledger cannot be put
    on a sequencer without, so the caps are exercised at the size they are set
    to: eight mebibytes of ciphertext goes in, nine does not, and the refusal is
    a 400 about the bytes rather than a 413 about the route. -/
    let bulk (bytes : Nat) : Sync.Part :=
      { realm := "money", generation := 1, ciphertext := ByteArray.mk (Array.replicate bytes 120) }
    let mib := 1024 * 1024
    let headNow ← Sync.Log.head log "home"
    let genesisSized := signedEnvelope alice "home" (headNow.seq + 1) headNow.hash [bulk (8 * mib)]
    r := checkEq r "a part of exactly the cap is appended"
      (← call aliceTok "POST" ["ledgers", "home", "events"] genesisSized.toJson).code 201
    let afterGenesis ← Sync.Log.head log "home"
    let overSize := signedEnvelope alice "home" (afterGenesis.seq + 1) afterGenesis.hash
      [bulk (9 * mib)]
    let refusedSize ← call aliceTok "POST" ["ledgers", "home", "events"] overSize.toJson
    r := checkEq r "a part over it is refused for its size, not for its route" refusedSize.code 400
    r := check r "and the sentence names the realm and the number"
      (((jstr (payload refusedSize) "error").splitOn "is larger than").length == 2)
    r := checkEq r "the order did not move under the refusal"
      (← Sync.Log.head log "home").hash afterGenesis.hash
    -- Twelve megabytes of base64 is under the body cap, so the refusal above is
    -- the part's. A body over the *route's* cap is the other refusal, and it is
    -- taken before anything is parsed.
    let overBody := (Api.Req.simple "POST" ["ledgers", "home", "events"]).withBody
      (ByteArray.mk (Array.replicate (17 * mib) 120))
    r := checkEq r "a body over the route's cap is a 413, whoever sent it"
      (← Sync.handleSafe node
        (overBody.withHeaders [("authorization", "Bearer " ++ aliceTok)])).code 413
    -- And twenty kilobytes, which the megabyte cap took and the old default part
    -- would have taken, is nowhere near either of them now.
    let twentyK := (Api.Req.simple "POST" ["ledgers", "home", "events"]).withBody
      (ByteArray.mk (Array.replicate (20 * 1024) 120))
    r := checkEq r "twenty kilobytes is read rather than refused for its size"
      (← Sync.handleSafe node
        (twentyK.withHeaders [("authorization", "Bearer " ++ aliceTok)])).code 400

    /- ## Blobs -/
    let bytes := cipher "an encrypted receipt"
    let hash := Sha256.hexBytes bytes
    let stored ← Sync.handleSafe node
      (((Api.Req.simple "PUT" ["ledgers", "home", "blobs", hash]).withBody bytes).withHeaders
        [("authorization", "Bearer " ++ aliceTok)])
    r := checkEq r "a blob is stored under the hash of its ciphertext" stored.code 201
    -- As the bytes themselves rather than as the text of their base64, which
    -- cost a third of the quota again on disk and a decode on every read of
    -- bytes this service is never going to look inside.
    r := checkEq r "as a BLOB rather than as the text of its base64"
      ((← Db.row? String log.db s!"SELECT typeof(bytes) FROM blob
          WHERE ledger = 'home' AND hash = {Db.lit hash}").getD "") "blob"
    let fetched ← get aliceTok ["ledgers", "home", "blobs", hash]
    r := checkEq r "and comes back unchanged"
      (match fetched with | .bytes _ _ data _ => Sync.toBase64 data | _ => "")
      (Sync.toBase64 bytes)
    let wrongBytes := (Api.Req.simple "PUT" ["ledgers", "home", "blobs", hash]).withBody
      (cipher "other")
    let mismatched ← Sync.handleSafe node
      (wrongBytes.withHeaders [("authorization", "Bearer " ++ aliceTok)])
    r := checkEq r "bytes that do not hash to their name are refused" mismatched.code 400
    -- The digest is taken before the store is locked, because it is a question
    -- about the body and nothing else, and on sixteen megabytes it is seconds
    -- of the whole service standing still.
    let preparedBlob ← Sync.prepare node.limits
      ((Api.Req.simple "PUT" ["ledgers", "home", "blobs", hash]).withBody bytes)
    r := checkEq r "a blob's digest is taken outside the lock" preparedBlob.bodyHash hash
    let preparedJson ← Sync.prepare node.limits
      ((Api.Req.simple "POST" ["challenge"]).withJson (Json.mkObj [("key", alice.id)]))
    r := check r "and a body is parsed there too" preparedJson.json.toOption.isSome
    r := checkEq r "a route with no digest to take does not take one" preparedJson.bodyHash ""
    let preparedJunk ← Sync.prepare node.limits
      ((Api.Req.simple "POST" ["challenge"]).withBody "{".toUTF8)
    r := check r "a body that is not JSON is refused there rather than under the lock"
      preparedJunk.json.toOption.isNone
    -- Membership is self-serve, so a member being allowed to store bytes bounds
    -- nothing. The quota is per ledger, because whoever keeps the ledger is who
    -- pays for it.
    let held := jnat (payload stored) "held"
    r := check r "a stored blob is counted against the ledger" (held ≥ bytes.size)
    let pinched ← Sync.Node.make log verifier { blobQuotaBytes := 8 } origin (some #[alice.id])
      (testOnly := true)
    let (_, pinchedTok) ← loginOn pinched alice
    let moreBytes := cipher "a second encrypted receipt"
    let overQuota ← Sync.handleSafe pinched
      (((Api.Req.simple "PUT" ["ledgers", "home", "blobs", Sha256.hexBytes moreBytes]).withBody
        moreBytes).withHeaders [("authorization", "Bearer " ++ pinchedTok)])
    r := checkEq r "a blob that would take the ledger past its quota is refused"
      overQuota.code 507
    r := checkEq r "and is not there afterwards"
      (← get aliceTok ["ledgers", "home", "blobs", Sha256.hexBytes moreBytes]).code 404
    -- Nothing collects blobs, because the sequencer cannot read the order and so
    -- cannot know what still points at one. Somebody who can read it says so.
    r := checkEq r "a member who administers nothing may not remove a blob"
      (← call bobTok "DELETE" ["ledgers", "home", "blobs", hash] (Json.mkObj [])).code 403
    r := checkEq r "a ledger admin may"
      (← call aliceTok "DELETE" ["ledgers", "home", "blobs", hash] (Json.mkObj [])).code 200
    r := checkEq r "and it is gone" (← get aliceTok ["ledgers", "home", "blobs", hash]).code 404
    r := checkEq r "removing it twice is a 404"
      (← call aliceTok "DELETE" ["ledgers", "home", "blobs", hash] (Json.mkObj [])).code 404
    r := checkEq r "which gave the ledger its quota back"
      (← Sync.Log.blobBytes log "home") 0
    -- Nothing collects blobs, so the quota is what makes manual collection
    -- workable, which makes it the one number an operator is likely to set.
    -- `--blob-quota` takes it in the unit a disk is measured in.
    r := checkEq r "a bare number of bytes reads as itself" (Sync.byteSize? "1024") (some 1024)
    r := checkEq r "a binary suffix scales it"
      (Sync.byteSize? "256MiB") (some (256 * 1024 * 1024))
    r := checkEq r "in either spelling" (Sync.byteSize? "512k") (some (512 * 1024))
    r := check r "anything else is not a size" (Sync.byteSize? "lots").isNone
    r := check r "nor is a suffix with no number in front of it" (Sync.byteSize? "MiB").isNone
    r := checkEq r "and 256 MiB is what a sequencer holds for a ledger by default"
      ({} : Sync.Limits).blobQuotaBytes (256 * 1024 * 1024)

    /- ## Every mutating route is metered, not just the append

    `POST realms`, the grant writes, the checkpoint writes, `redeem`, `join`
    and the blob routes were all unmetered: a member with a burst of tokens
    spending them on any of those is the same request queue behind the same
    lock as an append is. -/
    let metered ← Sync.Node.make log verifier
      { burst := 1, perSecond := 0, blobBurst := 1, blobPerSecond := 0 } origin
      (some #[alice.id]) (testOnly := true)
    let (_, meteredTok) ← loginOn metered alice
    r := checkEq r "a mutating request that is not an append comes out of the bucket"
      (← callOn metered meteredTok "POST" ["ledgers", "home", "realms"]
        (Json.mkObj [("realm", "metered-one")])).code 201
    r := checkEq r "and the next one is refused, whatever route it names"
      (← callOn metered meteredTok "POST" ["ledgers", "home", "realms"]
        (Json.mkObj [("realm", "metered-two")])).code 429
    r := checkEq r "a read is not metered at all"
      (← Sync.handleSafe metered
        ((Api.Req.simple "GET" ["ledgers", "home", "head"]).withHeaders
          [("authorization", "Bearer " ++ meteredTok)])).code 200
    -- Blobs have an allowance of their own, so that a run of receipts does not
    -- spend what an append needs -- and it runs out on its own terms.
    let meteredBlob (text : String) : IO Api.Reply := do
      let bs := cipher text
      Sync.handleSafe metered
        (((Api.Req.simple "PUT" ["ledgers", "home", "blobs", Sha256.hexBytes bs]).withBody
          bs).withHeaders [("authorization", "Bearer " ++ meteredTok)])
    r := checkEq r "a blob comes out of a bucket of its own, not the one just emptied"
      (← meteredBlob "one receipt").code 201
    r := checkEq r "which runs out on its own terms" (← meteredBlob "another receipt").code 429
    r := check r "and is the larger of the two by default"
      (({} : Sync.Limits).blobBurst > ({} : Sync.Limits).burst)

    /- ## Invites -/
    let firstInvite := party "invite-one"
    let joinInvite := party "invite-join"
    let lapsedInvite := party "invite-lapsed"
    let staleInvite := party "invite-stale"
    let refusedInvite := party "invite-refused"
    -- An invite may no longer be made to stand for ever, so "never" is now "as
    -- long as this sequencer will allow minus a day".
    let isoAt (seconds : Int) : String :=
      let days := seconds / 86400 - (if seconds % 86400 < 0 then 1 else 0)
      let secondOfDay := (seconds - days * 86400).toNat
      let (y, m, d) := Sync.civilFromDays days
      Sync.isoCanonical y m d (secondOfDay / 3600) (secondOfDay / 60 % 60) (secondOfDay % 60)
    let nowSeconds := (Sync.isoSeconds? (← Sync.Log.utcNow)).getD 0
    let never := isoAt (nowSeconds + 7 * 86400)
    let longAgo := "1970-01-01T00:00:00Z"
    let inviteBody (i : Signer) (expires : String) : Json :=
      Json.mkObj [("inviteSignPk", i.id), ("inviteBoxPk", i.boxPk),
                  ("wrappedKey", Sync.toBase64 (cipher "money-key-for-whoever-comes")),
                  ("role", "viewer"), ("expires", expires)]
    let invited ← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
      (inviteBody firstInvite never)
    r := checkEq r "the realm's admin makes an invite" invited.code 201
    r := checkEq r "at the realm's current generation" (jnat (payload invited) "generation") 1
    r := checkEq r "naming the admin whose word a joiner will pin"
      (jstr (payload invited) "inviterSignPk") alice.id
    r := check r "and it never hands the wrapped key back"
      ((payload invited).getObjVal? "wrappedKey").toOption.isNone
    r := checkEq r "the admin lists what is outstanding"
      (listOf (← get aliceTok ["ledgers", "home", "realms", "money", "invites"])).size 1
    r := checkEq r "another member may not"
      (← get bobTok ["ledgers", "home", "realms", "money", "invites"]).code 403
    r := checkEq r "an invite that has already lapsed is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody lapsedInvite longAgo)).code 400
    r := checkEq r "an invite is withdrawn"
      (← call aliceTok "DELETE" ["ledgers", "home", "realms", "money", "invites", firstInvite.id]
        (Json.mkObj [])).code 200
    r := checkEq r "and withdrawing it twice is a 404"
      (← call aliceTok "DELETE" ["ledgers", "home", "realms", "money", "invites", firstInvite.id]
        (Json.mkObj [])).code 404
    r := checkEq r "nothing is outstanding now"
      (listOf (← get aliceTok ["ledgers", "home", "realms", "money", "invites"])).size 0
    -- An expiry is a time, in UTC, within a month. It used to be any string at
    -- all, compared against a local clock, which made "z" an offer that never
    -- lapsed.
    r := checkEq r "an expiry that is not a time is refused"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody firstInvite "z")).code 400
    r := checkEq r "so is one that is not a date"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody firstInvite "2026-02-30T00:00:00Z")).code 400
    r := checkEq r "so is one carrying a zone offset instead of UTC"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody firstInvite "2026-10-01T12:00:00+02:00")).code 400
    r := checkEq r "and one that would stand for longer than a month"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody firstInvite (isoAt (nowSeconds + 60 * 86400)))).code 400
    -- What a browser sends: `toISOString()`, milliseconds and all.
    let dated ← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
      (inviteBody firstInvite (((isoAt (nowSeconds + 86400)).dropEnd 1).copy ++ ".500Z"))
    r := checkEq r "one inside the bound is taken" dated.code 201
    r := checkEq r "and stored in one UTC shape, whatever shape it arrived in"
      (jstr (payload dated) "expires") (isoAt (nowSeconds + 86400))
    r := checkEq r "which is withdrawn again"
      (← call aliceTok "DELETE" ["ledgers", "home", "realms", "money", "invites", firstInvite.id]
        (Json.mkObj [])).code 200

    /- ## Joining: the proof, then the grant the joiner signs for themselves -/
    let resealed := cipher "money-key-resealed"
    let joinBody (invite : Signer) (joiner : Signer) (generation : Nat)
        (realm : String := "money") : Json :=
      Json.mkObj [("inviteSignPk", invite.id),
                  ("proof", invite.sign (Sync.joinBytes "home" realm joiner.id)),
                  ("wrappedKey", Sync.toBase64 resealed),
                  ("signature", joiner.sign
                    (Sync.grantBytes "home" realm generation joiner.id "viewer" resealed))]
    r := checkEq r "a fresh invite is made for a newcomer"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody joinInvite never)).code 201
    let redeemed ← call carolTok "POST"
      ["ledgers", "home", "realms", "money", "invites", joinInvite.id, "redeem"]
      (Json.mkObj [("proof", joinInvite.sign (Sync.joinBytes "home" "money" carol.id))])
    r := checkEq r "the invited party reads the sealed key before they are a member"
      redeemed.code 200
    r := checkEq r "and it is the key the inviter sealed"
      ((Sync.ofBase64? (jstr (payload redeemed) "wrappedKey")).map Sync.toBase64)
      (some (Sync.toBase64 (cipher "money-key-for-whoever-comes")))
    r := checkEq r "with the key it was sealed to, so they know which secret opens it"
      (jstr (payload redeemed) "inviteBoxPk") joinInvite.boxPk
    r := checkEq r "the inviter, whom they will pin as an admin of this realm"
      (jstr (payload redeemed) "inviterSignPk") alice.id
    r := checkEq r "at the generation it was made on" (jnat (payload redeemed) "generation") 1
    r := checkEq r "and the role it will grant" (jstr (payload redeemed) "role") "viewer"
    r := checkEq r "reading it does not spend it"
      (listOf (← get aliceTok ["ledgers", "home", "realms", "money", "invites"])).size 1
    r := checkEq r "a proof that is not over the joiner's own id is refused"
      (← call carolTok "POST"
        ["ledgers", "home", "realms", "money", "invites", joinInvite.id, "redeem"]
        (Json.mkObj [("proof", joinInvite.sign (Sync.joinBytes "home" "money" bob.id))])).code 403
    r := checkEq r "and a join whose grant signature is not the joiner's own is refused"
      (← call carolTok "POST" ["ledgers", "home", "realms", "money", "join"]
        (Json.mkObj [("inviteSignPk", joinInvite.id),
                     ("proof", joinInvite.sign (Sync.joinBytes "home" "money" carol.id)),
                     ("wrappedKey", Sync.toBase64 resealed),
                     ("signature", bob.sign
                       (Sync.grantBytes "home" "money" 1 carol.id "viewer" resealed))])).code 403
    let joined ← call carolTok "POST" ["ledgers", "home", "realms", "money", "join"]
      (joinBody joinInvite carol 1)
    r := checkEq r "a stranger holding an invite joins" joined.code 201
    r := checkEq r "at the realm's generation" (jnat (payload joined) "generation") 1
    r := checkEq r "and the grant is theirs"
      (jstr (jsub (payload joined) "grant") "member") carol.id
    r := checkEq r "issued by themselves, which is the one case where that is allowed"
      (jstr (jsub (payload joined) "grant") "grantedBy") carol.id
    r := checkEq r "with the role the invite carried"
      (jstr (jsub (payload joined) "grant") "role") "viewer"
    let afterJoin := listOf (← get aliceTok ["ledgers", "home", "members"])
    r := checkEq r "the joiner is a member of the ledger now" afterJoin.size 3
    let carolRecord := (afterJoin.find? (fun m => jstr m "member" == carol.id)).getD Json.null
    r := check r "but not an administrating one" (!jbool carolRecord "admin" true)
    r := checkEq r "and they arrive with no agreement key, to publish for themselves"
      (jstr carolRecord "boxPk") ""
    r := checkEq r "which they then do"
      (← call carolTok "PUT" ["ledgers", "home", "members", carol.id, "boxPk"]
        (boxPkBody carol "home")).code 200
    r := checkEq r "the key they re-sealed is what their grant holds"
      ((Sync.ofBase64? (jstr (payload
        (← get carolTok ["ledgers", "home", "realms", "money", "grants", carol.id]))
        "wrappedKey")).map Sync.toBase64)
      (some (Sync.toBase64 resealed))
    r := checkEq r "the invite is spent"
      (← call carolTok "POST" ["ledgers", "home", "realms", "money", "join"]
        (joinBody joinInvite carol 1)).code 404
    r := checkEq r "and there is nothing left to read from it"
      (← call carolTok "POST"
        ["ledgers", "home", "realms", "money", "invites", joinInvite.id, "redeem"]
        (Json.mkObj [("proof", joinInvite.sign (Sync.joinBytes "home" "money" carol.id))])).code 404
    let listedRealms := listOf (← get carolTok ["ledgers", "home", "realms"])
    r := checkEq r "a member sees the realms they hold a key for" listedRealms.size 1
    r := checkEq r "the one they joined" (jstr (listedRealms[0]!) "realm") "money"
    r := checkEq r "at the generation they hold" (jnat (listedRealms[0]!) "generation") 1
    r := checkEq r "in the role it was granted in" (jstr (listedRealms[0]!) "role") "viewer"

    /- ## An invite is a moment, not a standing offer -/
    -- Put straight into the store, because the route refuses to make one that has
    -- already lapsed. What is being tested is the other end: what a join does
    -- when it meets one.
    let lapsed : Sync.Invite :=
      { realm := "money", signPk := lapsedInvite.id, boxPk := lapsedInvite.boxPk,
        wrappedKey := cipher "money-key-for-nobody", generation := 1, role := "viewer",
        expires := longAgo, createdBy := alice.id }
    r := check r "a lapsed invite is in the store" (← Sync.Log.putInvite log "home" lapsed)
    r := checkEq r "joining on it is refused"
      (← call carolTok "POST" ["ledgers", "home", "realms", "money", "join"]
        (joinBody lapsedInvite carol 1)).code 410
    r := checkEq r "and it has been swept away"
      (listOf (← get aliceTok ["ledgers", "home", "realms", "money", "invites"])).size 0

    /- ## A revoke invalidates the invites made before it -/
    r := checkEq r "an invite is made at the current generation"
      (jnat (payload (← call aliceTok "POST"
        ["ledgers", "home", "realms", "money", "invites"] (inviteBody staleInvite never)))
        "generation") 1
    r := checkEq r "then the realm is re-keyed"
      (jnat (payload (← call aliceTok "DELETE"
        ["ledgers", "home", "realms", "money", "grants", carol.id] (Json.mkObj []))) "generation") 2
    r := checkEq r "the invite from before it no longer opens anything"
      (← call carolTok "POST" ["ledgers", "home", "realms", "money", "join"]
        (joinBody staleInvite carol 1)).code 409
    r := checkEq r "so it is purged rather than left to be tried again"
      (listOf (← get aliceTok ["ledgers", "home", "realms", "money", "invites"])).size 0

    /- ## A proof the invite's own key did not make -/
    r := checkEq r "an invite is outstanding again"
      (← call aliceTok "POST" ["ledgers", "home", "realms", "money", "invites"]
        (inviteBody refusedInvite never)).code 201
    r := checkEq r "reading a sealed key on a proof somebody else signed is refused"
      (← call carolTok "POST"
        ["ledgers", "home", "realms", "money", "invites", refusedInvite.id, "redeem"]
        (Json.mkObj [("proof", bob.sign (Sync.joinBytes "home" "money" carol.id))])).code 403
    r := checkEq r "and so is a join on one"
      (← call carolTok "POST" ["ledgers", "home", "realms", "money", "join"]
        (Json.mkObj [("inviteSignPk", refusedInvite.id),
                     ("proof", bob.sign (Sync.joinBytes "home" "money" carol.id)),
                     ("wrappedKey", Sync.toBase64 resealed),
                     ("signature", carol.sign
                       (Sync.grantBytes "home" "money" 2 carol.id "viewer" resealed))])).code 403
    r := checkEq r "and neither refusal touched the invite they were aimed at"
      (listOf (← get aliceTok ["ledgers", "home", "realms", "money", "invites"])).size 1

    /- ## What the transport refuses before a route is reached -/
    r := checkEq r "no path is the client's own index" (Sync.safeRelPath []) (some "index.html")
    r := checkEq r "an ordinary asset is served"
      (Sync.safeRelPath ["assets", "app.js"]) (some "assets/app.js")
    r := check r "a climb out of the root is refused" (Sync.safeRelPath [".."]).isNone
    r := check r "wherever it is in the path"
      (Sync.safeRelPath ["assets", "..", "..", "secret"]).isNone
    r := check r "a lone dot is refused too" (Sync.safeRelPath ["."]).isNone
    -- Segments arrive percent-decoded, so `%2f` is a separator by the time this
    -- rule sees it: what `..%2f..%2fsecret` amounts to is one segment with two
    -- slashes in it, and a separator inside a segment is the whole of how a
    -- climb is spelled once decoding has been done for you.
    r := check r "a percent-encoded slash is a separator, not part of a name"
      (Sync.safeRelPath ["../../secret"]).isNone
    r := check r "and so is a backslash" (Sync.safeRelPath ["..\\..\\secret"]).isNone
    r := check r "an absolute path in one segment is refused"
      (Sync.safeRelPath ["/etc/passwd"]).isNone
    r := check r "an empty segment is refused" (Sync.safeRelPath ["assets", ""]).isNone
    let headerNames := Sync.securityHeaders.map (·.1)
    r := check r "every response says not to sniff its type"
      (headerNames.contains "x-content-type-options")
    r := check r "carries a content security policy"
      (headerNames.contains "content-security-policy")
    r := check r "and a referrer policy" (headerNames.contains "referrer-policy")
    let csp := ((Sync.securityHeaders.find? (fun h => h.fst == "content-security-policy")).map
      (fun h => h.snd)).getD ""
    r := check r "the policy keeps the client out of anybody's frame"
      ((csp.splitOn "frame-ancestors 'none'").length == 2)

    /- ## What a role buys

    On a ledger of its own, because the point is the difference between the two
    roles rather than anything about the order. A viewer holds the realm's key,
    so a viewer writes in it and commits to what they replayed; what the admin
    role adds is the right to let somebody else in, and to read the list of who
    is already in. -/
    r := checkEq r "a second ledger is made" (← call aliceTok "POST" ["ledgers"]
      (Json.mkObj [("ledger", "roles")])).code 201
    r := checkEq r "with a realm" (← call aliceTok "POST" ["ledgers", "roles", "realms"]
      (Json.mkObj [("realm", "books")])).code 201
    r := checkEq r "whose maker takes its key in the admin role"
      (← call aliceTok "POST" ["ledgers", "roles", "realms", "books", "grants", alice.id]
        (grantBody alice "roles" "books" 0 alice.id "admin" (cipher "books-key"))).code 201
    r := checkEq r "a role this sequencer does not define is refused outright"
      (← call aliceTok "POST" ["ledgers", "roles", "realms", "books", "grants", alice.id]
        (grantBody alice "roles" "books" 0 alice.id "editor" (cipher "books-key"))).code 400
    r := checkEq r "a second member is added" (← call aliceTok "POST"
      ["ledgers", "roles", "members", bob.id] (Json.mkObj [])).code 201
    r := checkEq r "and granted the key as a viewer"
      (← call aliceTok "POST" ["ledgers", "roles", "realms", "books", "grants", bob.id]
        (grantBody alice "roles" "books" 0 bob.id "viewer" (cipher "books-key-bob"))).code 201
    -- A viewer writes. Holding the key is what writing in a realm *is*.
    let viewerEntry := signedEnvelope bob "roles" 1 "" [partOf "books" 0 "bob was here"]
    r := checkEq r "a viewer appends to the order"
      (← call bobTok "POST" ["ledgers", "roles", "events"] viewerEntry.toJson).code 201
    let viewerCommitment : Sync.Checkpoint :=
      { ledger := "roles", realm := "books", generation := 0, seq := 1,
        stateHash := "bobs-reading", headHash := viewerEntry.hash, author := bob.id,
        signature := "", snapshot := cipher "bobs-snapshot" }
    r := checkEq r "and commits to what they replayed"
      (← call bobTok "PUT" ["ledgers", "roles", "realms", "books", "checkpoint"]
        { viewerCommitment with
            signature := bob.sign viewerCommitment.commitmentBytes }.toJson).code 200
    -- What the admin role adds, and only it.
    r := checkEq r "a viewer may not let anybody else in"
      (← call bobTok "POST" ["ledgers", "roles", "realms", "books", "grants", bob.id]
        (grantBody bob "roles" "books" 0 bob.id "viewer" (cipher "k"))).code 403
    r := checkEq r "nor invite"
      (← call bobTok "POST" ["ledgers", "roles", "realms", "books", "invites"]
        (inviteBody joinInvite never)).code 403
    r := checkEq r "nor revoke"
      (← call bobTok "DELETE" ["ledgers", "roles", "realms", "books", "grants", alice.id]
        (Json.mkObj [])).code 403
    -- The membership of a realm is the most revealing thing this server holds
    -- about people who are not the caller, so the list belongs to whoever hands
    -- the keys out.
    r := checkEq r "nor read the list of who holds the realm"
      (← get bobTok ["ledgers", "roles", "realms", "books", "grants"]).code 403
    r := checkEq r "though a holder always reads their own grant"
      (← get bobTok ["ledgers", "roles", "realms", "books", "grants", bob.id]).code 200
    r := checkEq r "and nobody else's"
      (← get bobTok ["ledgers", "roles", "realms", "books", "grants", alice.id]).code 404
    r := checkEq r "the realm's admin reads all of it"
      (listOf (← get aliceTok ["ledgers", "roles", "realms", "books", "grants"])).size 2
    -- A grant in a role written before this binary knew the word buys nothing:
    -- both halves of "enforced, not carried" are the same check.
    discard <| Sync.Log.putGrant log "roles" "books" carol.id (cipher "k") "editor" alice.id "00"
    r := checkEq r "a member is added under it" (← call aliceTok "POST"
      ["ledgers", "roles", "members", carol.id] (Json.mkObj [])).code 201
    let unknownRole := signedEnvelope carol "roles" 2 viewerEntry.hash
      [partOf "books" 0 "carol tries"]
    r := checkEq r "a grant in a role nobody defined appends nothing"
      (← call carolTok "POST" ["ledgers", "roles", "events"] unknownRole.toJson).code 403
    -- Stepping down is a thing you can do to yourself, and it means what it says.
    r := checkEq r "the realm's admin re-grants themselves as a viewer"
      (← call aliceTok "POST" ["ledgers", "roles", "realms", "books", "grants", alice.id]
        (grantBody alice "roles" "books" 0 alice.id "viewer" (cipher "books-key"))).code 201
    r := checkEq r "and has stepped down with it"
      (← call aliceTok "POST" ["ledgers", "roles", "realms", "books", "grants", bob.id]
        (grantBody alice "roles" "books" 0 bob.id "viewer" (cipher "k"))).code 403
    r := checkEq r "though they still write, because they still hold the key"
      (← call aliceTok "POST" ["ledgers", "roles", "events"]
        (signedEnvelope alice "roles" 2 viewerEntry.hash
          [partOf "books" 0 "still here"]).toJson).code 201

    /- ## Names people choose

    A ledger id and a realm id used to be any non-empty string up to the body
    cap: stored, served to every member, and carried through an invite link that
    delimits its fields with `:`. -/
    r := check r "an id is a name in a closed alphabet" (Sync.isPlainId "home-2026.v1")
    r := check r "one with a colon in it is not" (!Sync.isPlainId "home:money")
    r := check r "nor one with a space" (!Sync.isPlainId "my ledger")
    r := check r "nor an empty one" (!Sync.isPlainId "")
    r := check r "nor one carrying a LIKE wildcard" (!Sync.isPlainId "home%")
    r := check r "nor one longer than the bound"
      (!Sync.isPlainId (String.ofList (List.replicate (Sync.idMaxLength + 1) 'a')))
    r := check r "one exactly that long is fine"
      (Sync.isPlainId (String.ofList (List.replicate Sync.idMaxLength 'a')))
    r := checkEq r "a ledger id this sequencer will not name is refused"
      (← call aliceTok "POST" ["ledgers"] (Json.mkObj [("ledger", "home:money")])).code 400
    r := checkEq r "and so is a realm id"
      (← call aliceTok "POST" ["ledgers", "home", "realms"]
        (Json.mkObj [("realm", "my realm")])).code 400

    /- ## Lengths, before the primitive is asked

    `ofHex?` is happy with any even run of hex digits, so a one-byte key and a
    three-byte signature used to reach the verifier — harmless in Lean, a buffer
    over-read in C the day libsodium is behind it. -/
    let realSignature := alice.sign (Sync.memberBytes "home" alice.id alice.boxPk)
    r := check r "a signature over the real bytes verifies"
      (verifier.check alice.id (Sync.memberBytes "home" alice.id alice.boxPk) realSignature)
    r := check r "a key that is not 64 hex characters never reaches the suite"
      (!verifier.check (alice.id.take 62).copy (Sync.memberBytes "home" alice.id alice.boxPk)
        realSignature)
    r := check r "nor does a signature of the wrong width"
      (!verifier.check alice.id (Sync.memberBytes "home" alice.id alice.boxPk)
        (realSignature ++ "00"))
    r := check r "nor a signature that is not hex at all"
      (!verifier.check alice.id (Sync.memberBytes "home" alice.id alice.boxPk)
        (String.ofList (List.replicate realSignature.length 'z')))
    r := check r "a verifier that states no width takes the range the schemes fall in"
      ((Sync.Verifier.ofSuite suite).wellFormedSignature realSignature
        && !(Sync.Verifier.ofSuite suite).wellFormedSignature "ab")
    r := check r "and one that states its width takes exactly that"
      (verifier.wellFormedSignature realSignature
        && !verifier.wellFormedSignature (realSignature ++ realSignature))

    /- ## The allowance table is bounded

    `POST /challenge` needs no session and used to append an entry that nothing
    ever removed, so a stranger could grow the table until the process died and
    make every honest request walk it on the way past. -/
    let now : Int := 1000000
    let table : Sync.Buckets := Std.HashMap.ofArray
      #[("full", { milliTokens := 4000, refilledAt := now }),
        ("idle", { milliTokens := 0, refilledAt := now - 2 * 3600 * 1000 }),
        ("live", { milliTokens := 1000, refilledAt := now })]
    let kept := Sync.prunedBuckets table 4000 0 now 100 (3600 * 1000)
    r := check r "a bucket that has refilled to the brim is dropped" (!kept.contains "full")
    r := check r "so is one nobody has touched for an hour" (!kept.contains "idle")
    r := check r "and one with tokens spent is kept" (kept.contains "live")
    let crowdedTable : Sync.Buckets := Std.HashMap.ofArray
      ((List.range 40).map (fun i => (s!"key-{i}", ({ milliTokens := 0, refilledAt := now } :
        Sync.Bucket)))).toArray
    r := check r "and a table over its ceiling is cut down to it"
      ((Sync.prunedBuckets crowdedTable 4000 0 now 8 (3600 * 1000)).size ≤ 8)
    let crowded ← Sync.Node.make log verifier { maxBuckets := 8 } origin none (testOnly := true)
    for i in [0:40] do
      discard <| Sync.handleSafe crowded ((Api.Req.simple "POST" ["challenge"]).withJson
        (Json.mkObj [("key", (party s!"stranger-{i}").id)]))
    r := check r "so forty strangers leave a table of eight, not of forty"
      ((← crowded.authBuckets.get).size ≤ 8)
    r := check r "while a key that is spending its own allowance keeps it"
      (((← crowded.authBuckets.get).get? (party "stranger-39").id).isSome)

    /- ## Sessions and challenges are swept on a tick, and capped per key

    Both tables used to be swept only when something was inserted into them, so
    a burst followed by silence stayed in memory until somebody else turned up. -/
    let sessioned ← Sync.Node.make log verifier
      { authBurst := 100, maxSessionsPerKey := 3 } origin none (testOnly := true)
    let sessionedHead (token : String) : IO Api.Reply :=
      Sync.handleSafe sessioned ((Api.Req.simple "GET" ["ledgers", "home", "head"]).withHeaders
        [("authorization", "Bearer " ++ token)])
    let mut tokens : List String := []
    for _ in [0:5] do
      tokens := tokens ++ [(← loginOn sessioned dave).2]
    r := checkEq r "a key holds no more sessions than the cap allows"
      ((← sessioned.sessions.get).size) 3
    let mut alive := 0
    for t in tokens do
      if (← sessionedHead t).code == 404 then alive := alive + 1
    r := checkEq r "so five logins from one key leave three tokens that work" alive 3
    r := checkEq r "the newest among them"
      (← sessionedHead (tokens.getLast?.getD "")).code 404
    -- Lapsed entries used to be swept only when something was inserted, so a
    -- burst followed by silence stayed in memory until somebody else turned up.
    let expiring ← Sync.Node.make log verifier
      { sessionMillis := -1, authBurst := 100 } origin none (testOnly := true)
    discard <| loginOn expiring dave
    r := check r "a session that has already lapsed is in the table"
      ((← expiring.sessions.get).size > 0)
    discard <| Sync.handleSafe expiring (Api.Req.simple "GET" ["health"])
    r := checkEq r "until the next request ticks it away, whatever that request is"
      ((← expiring.sessions.get).size) 0
    let lapsing ← Sync.Node.make log verifier
      { challengeMillis := -1, authBurst := 100 } origin none (testOnly := true)
    discard <| Sync.handleSafe lapsing ((Api.Req.simple "POST" ["challenge"]).withJson
      (Json.mkObj [("key", dave.id)]))
    r := check r "and a lapsed challenge the same"
      ((← lapsing.challenges.get).size > 0)
    discard <| Sync.handleSafe lapsing (Api.Req.simple "GET" ["health"])
    r := checkEq r "swept on a tick rather than on the next insert"
      ((← lapsing.challenges.get).size) 0

    /- ## A verifier that proves nothing cannot be built into a sequencer at all

    The gate this replaces was three of them — an environment variable, a flag,
    and a refusal of remote peers inside the route table — and the third one
    fired for nobody in the topology this project documents: behind nginx on a
    loopback socket, every request arrives from 127.0.0.1. A constructor that
    will not build the thing is not a gate that can be walked around. -/
    r := check r "the test verifier says out loud that it proves nothing"
      (verifier.isInsecure && !Sync.Verifier.rejectAll.isInsecure)
    let builds (v : Sync.Verifier) (testOnly : Bool) : IO Bool := do
      try
        discard <| Sync.Node.make log v {} origin none (testOnly := testOnly)
        pure true
      catch _ =>
        pure false
    r := check r "a sequencer refuses to be built with one that recomputes signatures"
      (!(← builds verifier false))
    r := check r "or with one that accepts every signature there is"
      (!(← builds Sync.Verifier.acceptAll false))
    r := check r "unless whoever builds it says in as many words that it is for a test"
      (← builds verifier true)
    r := check r "while the one that refuses everybody needs no such permission"
      (← builds Sync.Verifier.rejectAll false)
    let rejecting ← Sync.Node.make log Sync.Verifier.rejectAll {} origin none
    r := checkEq r "and health still names which of them is running"
      (jstr (payload (← Sync.handleSafe rejecting (Api.Req.simple "GET" ["health"]))) "verifier")
      "reject-all"
    r := checkEq r "whichever it is"
      (jstr (payload (← Sync.handleSafe node (Api.Req.simple "GET" ["health"]))) "verifier")
      verifier.name

    /- ## A sequencer built for a test answers nobody it cannot place here

    Which is what is left of the peer check: not "is this verifier honest", but
    "was this node built by a test". `unknown` is refused along with `remote`,
    because a transport that could not name its peer is evidence of nothing;
    the caller with no socket at all says so for itself. -/
    let fromAfar (peer : Sync.Peer) : IO Api.Reply :=
      Sync.handleSafe node ((Api.Req.simple "GET" ["ledgers", "home", "head"]).withHeaders
        [("authorization", "Bearer " ++ aliceTok)]) peer
    r := checkEq r "an authenticated route is refused from a remote socket"
      (← fromAfar .remote).code 403
    r := checkEq r "and from a socket whose peer the transport could not name"
      (← fromAfar .unknown).code 403
    r := checkEq r "answered over loopback" (← fromAfar .loopback).code 200
    r := checkEq r "and answered in process, where there is no socket to ask about"
      (← fromAfar .inProcess).code 200
    r := checkEq r "health is answered from anywhere, because it is how you find this out"
      (← Sync.handleSafe node (Api.Req.simple "GET" ["health"]) .remote).code 200
    r := checkEq r "while a sequencer that is not a test's answers a remote socket"
      (← Sync.handleSafe rejecting
        ((Api.Req.simple "GET" ["ledgers", "home", "head"]).withHeaders
          [("authorization", "Bearer nothing")]) .remote).code 401

    /- ## What the files this sequencer writes are readable by

    Ciphertext, but also the membership graph — who keeps books with whom — and
    a trail that names people by the keys they are known by. -/
    r := check r "the sequencer's data directory is the owner's alone" (← hasMode root "700")
    r := check r "the database is readable by nobody else"
      (← hasMode (Sync.Config.atDir root).dbPath "600")
    r := check r "nor is the audit trail" (← hasMode (Sync.Log.auditPath log) "600")

    /- ## The audit trail

    An ordering service is also the record somebody reads after something has
    gone wrong, and version 1 wrote nothing down at all. -/
    let before ← auditLines
    r := check r "every mutating request left a line" (before.length > 50)
    r := check r "each one beginning with a UTC instant"
      (before.all (fun l => (Sync.isoSeconds? ((l.splitOn " ").headD "")).isSome))
    r := check r "naming the method, the route, the member and what happened"
      (before.any (fun l =>
        (l.splitOn s!" POST /ledgers/home/events {alice.id} 201").length == 2))
    r := check r "refusals too, which is the half worth having"
      (before.any (fun l => (l.splitOn " 403").length == 2))
    r := check r "an unauthenticated attempt is recorded against nobody"
      (before.any (fun l => (l.splitOn " POST /challenge - ").length == 2))
    r := check r "and reads are left out, so a person can read it"
      (before.all (fun l => (l.splitOn " GET ").length == 1))

    /- ## Nobody writes a line but this server

    Path segments arrive percent-*decoded*, so `%0A` is a newline by the time it
    reaches the file. One unauthenticated request used to leave two lines in the
    trail, the second indistinguishable from a real entry — a forged timestamp,
    method, member and outcome in the only forensic record this service keeps. -/
    r := check r "a control character is one a name cannot carry" (Sync.hasControl "a\nb")
    r := check r "and an ordinary name does not" (!Sync.hasControl "ledgers/home/head")
    r := checkEq r "a field is written printable, with its spaces encoded"
      (Sync.logField "/a b\nc%d") "/a%20b%0ac%25d"
    r := checkEq r "and cut when it runs long" (Sync.logField "abcdef" 3) "abc[cut]"
    r := checkEq r "a line keeps its own separators and loses everything else"
      (Sync.logLine "2026-09-18T00:00:00Z POST /a\nb") "2026-09-18T00:00:00Z POST /a%0ab"
    let forged := "x\n1999-01-01T00:00:00Z DELETE /ledgers/home/members/nobody deadbeef 200"
    r := checkEq r "a path carrying a control character is refused before it is routed"
      (← Sync.handleSafe node (Api.Req.simple "POST" ["ledgers", forged])).code 400
    let after ← auditLines
    r := checkEq r "and leaves exactly one line behind, not two"
      (after.length - before.length) 1
    r := check r "with the newline written as an escape rather than as a newline"
      (after.any (fun l => (l.splitOn "%0a").length == 2))
    r := check r "so nothing in the trail reads as an entry this server did not write"
      (after.all (fun l => !l.startsWith "1999-"))
    r := check r "and the member column is still only ever a key or a dash"
      (after.all (fun l =>
        let who := ((l.splitOn " ").getD 3 "")
        who == "-" || Sync.isMemberId who))

    /- ## A blob written before version 6 is carried over rather than lost

    Blobs were the text of their base64 until then, which cost a third of the
    quota again on disk and a decode on every read. SQLite has no base64, so
    the conversion is Lean's, and it runs inside the migration's own
    transaction. -/
    let legacyDir := root / "legacy"
    IO.FS.createDirAll legacyDir
    let legacyCfg := Sync.Config.atDir legacyDir
    let legacyBytes := cipher "a receipt filed before the migration"
    let legacyHash := Sha256.hexBytes legacyBytes
    let legacyText := Sync.toBase64 legacyBytes
    let old ← SQLite.open legacyCfg.dbPath
    for (v, sql) in Sync.Log.migrations.filter (fun (v, _) => v ≤ 5) do
      Db.exec old sql
      Db.exec old s!"PRAGMA user_version = {v}"
    Db.exec old s!"INSERT INTO blob (ledger, hash, bytes, size, written_at)
      VALUES ('home', {Db.lit legacyHash}, {Db.lit legacyText}, {legacyText.length},
              '1970-01-01T00:00:00Z')"
    r := checkEq r "a store at the old version holds the encoding, not the bytes"
      ((← Db.row? String old "SELECT typeof(bytes) FROM blob").getD "") "text"
    let migrated ← Sync.Log.open legacyCfg
    r := checkEq r "which comes back as the bytes it stood for once it is migrated"
      ((← Sync.Log.blob? migrated "home" legacyHash).map Sync.toBase64) (some legacyText)
    r := checkEq r "as a BLOB" ((← Db.row? String migrated.db
      "SELECT typeof(bytes) FROM blob").getD "") "blob"
    r := checkEq r "counted at what it really costs rather than at its encoding"
      (← Sync.Log.blobBytes migrated "home") legacyBytes.size
    r := checkEq r "and the store is at the version this binary expects"
      (← Sync.Log.currentVersion migrated.db) Sync.Log.targetVersion

    /- ## The trail is rotated rather than left to fill the disk -/
    let rotating ← Sync.Log.open (Sync.Config.atDir (root / "rotated"))
    let line := String.ofList (List.replicate 100 'x')
    for _ in [0:20] do
      Sync.Log.audit rotating line (maxBytes := 500)
    r := check r "a trail past its cap is rotated out of the way"
      (← (Sync.Log.auditPreviousPath rotating).pathExists)
    r := check r "and the live one starts again from nothing"
      ((← IO.FS.readFile (Sync.Log.auditPath rotating)).length ≤ 500 + line.length + 1)
    r := checkEq r "sixty-four megabytes is where that happens by default"
      Sync.Log.auditMaxBytes (64 * 1024 * 1024)
    return r
  finally
    IO.FS.removeDirAll root <|> pure ()
