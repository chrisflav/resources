import Test.Sync
import Resources.Cli.Commands

/-!
# What the second review left on the node

One group, and it is not about the ledger: every check here is one of the
answers a node gives to somebody who is lying to it. The sequencer is untrusted
by design, the machine the API runs on has other users on it, and the browser
pointed at that API belongs to whoever the person was reading when they opened
it. So the questions are: what does a node accept from a server it dialled, what
does it hand to a shell, who is allowed to call its own API before a token
exists, and what does it write into a header.

Most of what is here is exercised as pure functions, because most of these
answers *are* pure functions — an origin comparison, a URL parse, a filename, a
content type — and the ones that are not are given a transport that lies to
them rather than a socket.

The numbers are the review's: N3 the curl config file, N4 the two halves of
asking for the test suite, N5 the peer address behind the bootstrap caller, N6
the origin a node signs for, N11 the invite fragment, N17 the attachment
filename, N18 the cross-site exemptions, L1 the loopback rule, N12 the lengths a
signature check is handed, N13 the realms an entry's unreadable parts were in,
N20's bearer scheme, and the agreement key's generation, which is what makes a
leaked key replaceable.

The third review added four more, and they are all about what a node believes
and on whose word: A3 the pin as a bootstrap rather than a root, A2 the
commitment a store may be started from, N9 the generation a member's agreement
key may go back to, and N15 what an error reply tells whoever asked.
-/

open Lean Resources

/-- The primitives under test. Signatures are checked; nothing is secret. -/
private def suite : Node.CryptoSuite := Node.CryptoSuite.insecureForTests

/-- A string field, or the empty string. -/
private def jstr (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

/-- A numeric field, or zero. -/
private def jnat (j : Json) (key : String) : Nat := (j.getObjValAs? Nat key).toOption.getD 0

/-- An IPv4 socket address, for the peer rule. -/
private def v4 (a b c d : UInt8) : Std.Net.SocketAddress :=
  .v4 { addr := Std.Net.IPv4Addr.ofParts a b c d, port := 8087 }

/-- An IPv6 socket address, for the peer rule. -/
private def v6 (segments : Vector UInt16 8) : Std.Net.SocketAddress :=
  .v6 { addr := { segments }, port := 8087 }

/-- Whether an `IO` action refused. -/
private def refused (act : IO α) : IO Bool := do
  try
    discard <| act
    return false
  catch _ =>
    return true

/--
Whether an `IO` action failed with something that is not the caller's business.

`Api.handleSafe` tells a refusal written for whoever asked from a failure that
came from underneath by the *kind* of the error rather than by reading its
message, so this asks the same question the API asks.
-/
private def failedInternally (act : IO α) : IO Bool := do
  try
    discard <| act
    return false
  catch
  | .userError _ => return false
  | _ => return true

/-- A string field of a reply's payload, or the empty string. -/
private def replyStr (reply : Api.Reply) (key : String) : String :=
  jstr (reply.json?.getD Json.null) key

/-- Whether an `Except` refused. -/
private def wasRefused : Except String Unit → Bool
  | .error _ => true
  | .ok _ => false

/--
A sequencer that answers the handshake and says whatever it is told to say
about itself.

Three origins rather than one, because the three routes that state it are three
chances to be caught: a relay has to repeat the same string on all of them, and
the point of the check is that repeating it is not enough.
-/
private def relay (health challenge issued : String) : Node.Transport := fun q =>
  match q.method, q.segments with
  | "GET", ["health"] =>
    pure (.json 200 (Json.mkObj [("status", "ok"), ("origin", health),
                                 ("verifier", "insecure")]))
  | "POST", ["challenge"] =>
    pure (.json 200 (Json.mkObj [("key", "x"), ("nonce", "0f0f"), ("origin", challenge)]))
  | "POST", ["authenticate"] =>
    pure (.json 200 (Json.mkObj [("token", "seq_TESTTOKEN"), ("origin", issued)]))
  | _, _ => pure (.json 200 (Json.mkObj [("ok", Json.bool true)]))

/--
An invite fragment naming a ledger and a realm, otherwise well formed.

The genesis field defaults to what `genesisFingerprint` really produces —
thirty-two lowercase hex digits, half a SHA-256 — because the parser holds it to
that shape or to the literal `none` and to nothing else.
-/
private def fragmentFor (ledger realm inviter : String)
    (genesisHash : String := "fedcba9876543210fedcba9876543210") : String :=
  Node.Invitation.fragment
    { ledger, realm, inviter, keyHash := "0123456789abcdef", genesisHash,
      secret := ByteArray.mk (Array.replicate Node.CryptoSuite.seedSize 7) }

-- One long `do` block, as the other two groups are, and for the same reason.
set_option maxRecDepth 20000

/-- What a node refuses, and to whom. -/
def nodeHardeningTests (r : Report) : IO Report := do
  let root : System.FilePath :=
    ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"resources-hardening-{← freshId}"
  IO.FS.createDirAll root
  try
    let mut r := r

    /- ## N3 — the token goes into a file curl reads as directives

    `curlFetch` writes the bearer token into a `--config` file, and the token is
    a string the *server* chose. A quote and a newline in one close the header
    and open `--output`, `--upload-file` or another `--config`: file write and
    file read on this machine, at the word of the party the design is written
    against. -/
    r := check r "a token is letters, digits and three punctuation marks"
      (Node.Transport.wellFormedToken "seq_01ABCabc.-_")
    r := check r "an empty one is not a token" (!Node.Transport.wellFormedToken "")
    r := check r "nor is one carrying a quote" (!Node.Transport.wellFormedToken "x\"y")
    r := check r "nor one carrying a newline and a directive"
      (!Node.Transport.wellFormedToken "x\noutput = /home/me/.local/share/resources/keys.json")
    r := check r "nor one carrying a space or a backslash"
      (!Node.Transport.wellFormedToken "a b" && !Node.Transport.wellFormedToken "a\\b")
    r := check r "nor one longer than a token is"
      (!Node.Transport.wellFormedToken (String.ofList (List.replicate 513 'a')))
    r := checkEq r "a config line quotes its value and escapes what curl reads out of it"
      (Node.Transport.curlConfigLine "header" "a\"b\\c") "header = \"a\\\"b\\\\c\"\n"
    r := check r "and a token that is not one never reaches a config file"
      (← refused (Node.Transport.curlFetch
        { url := "http://127.0.0.1:1/", method := "GET"
          token := some "x\"\noutput = /tmp/owned" }))

    /- ## L1 — which URLs name this machine

    The answer decides whether a plaintext transfer is allowed, so a URL that
    can be read two ways has to be read as the one that is not loopback. -/
    r := check r "http://127.0.0.1 is this machine"
      (Node.Transport.loopbackUrl "http://127.0.0.1")
    r := check r "and http://localhost:8087 is"
      (Node.Transport.loopbackUrl "http://localhost:8087")
    r := check r "and http://[::1]:8088 is"
      (Node.Transport.loopbackUrl "http://[::1]:8088")
    r := check r "a name that merely begins with 127. is not"
      (!Node.Transport.loopbackUrl "http://127.evil.example/x")
    r := check r "userinfo that looks like loopback is not the host"
      (!Node.Transport.loopbackUrl "http://127.0.0.1@evil.example/")
    r := check r "and a path carrying another scheme is not the authority"
      (!Node.Transport.loopbackUrl "https://ok.example/x://127.0.0.1")
    r := check r "a string that is not a URL names no machine"
      (!Node.Transport.loopbackUrl "127.0.0.1")
    r := checkEq r "an origin is a scheme, a host and a port, whatever was written"
      ((Node.Transport.originOf? "https://Seq.Example/x?y=1").getD "-")
      "https://seq.example:443"
    r := check r "so a default port and a trailing slash are the same origin"
      (Node.Transport.sameOrigin "https://seq.example" "https://seq.example:443/")
    r := check r "and a scheme is not"
      (!Node.Transport.sameOrigin "http://seq.example" "https://seq.example")

    /- ## N6 — the origin a node signs for

    `health` says what the server calls itself and `challenge` says it again,
    but both come from the same party. A relay repeats the real deployment's
    origin on every route, forwards the challenge it got from the real
    sequencer, and takes the signature. What it cannot be is the host the node
    dialled. -/
    let identity ← Node.Identity.create suite (root / "identity.json") "pass"
    let dial (t : Node.Transport) (base : Option String) : IO Bool := do
      let attempt : IO Unit := do
        let session ← Node.Transport.sessioned suite identity t base
        discard <| session (Node.Transport.get ["ledgers", "home", "head"])
      return !(← refused attempt)
    r := check r "a sequencer whose origin is the URL it was dialled at is signed for"
      (← dial (relay "https://seq.example" "https://seq.example" "https://seq.example")
        (some "https://seq.example"))
    r := check r "written another way, it is still the same origin"
      (← dial (relay "https://seq.example:443/" "https://seq.example:443/"
                     "https://seq.example:443/") (some "https://SEQ.example"))
    r := check r "a server that names an origin other than the one it was reached at is not"
      (!(← dial (relay "https://seq.example" "https://seq.example" "https://seq.example")
        (some "https://evil.example")))
    r := check r "nor is one that hands out a token for a third origin"
      (!(← dial (relay "https://seq.example" "https://seq.example" "https://other.example")
        (some "https://seq.example")))
    r := check r "nor one that changes its answer between health and challenge"
      (!(← dial (relay "https://seq.example" "https://other.example" "https://seq.example")
        (some "https://seq.example")))
    r := check r "while a transport that dialled nothing has nothing to compare"
      (← dial (relay "https://anything" "https://anything" "https://anything") none)

    /- ## N4 — both halves of asking for the test suite

    A variable is inherited and a flag is not, so the flag is the half that
    cannot arrive by accident. Neither alone opens the test suite, and what a
    node runs with when nothing is asked for is libsodium. -/
    let variableSet := (← IO.getEnv "RESOURCES_INSECURE_CRYPTO") == some "1"
    let held ← Node.CryptoSuite.insecureDevAsked
    let chosen : IO String := do
      try return (← Node.CryptoSuite.forNode).verifierName catch _ => return "refused"
    Node.CryptoSuite.insecureDevFlag.set false
    r := checkEq r "without --insecure-dev, the environment alone reaches no test suite"
      (← chosen) (if variableSet then "refused" else "sodium")
    Node.CryptoSuite.allowInsecureDev
    r := checkEq r "and with it, the test suite is reached exactly when the variable is set too"
      (← chosen) (if variableSet then "insecure" else "refused")
    Node.CryptoSuite.insecureDevFlag.set held

    /- ## N5 — who the API is open to before a token exists

    The bootstrap caller holds every scope, so the question of where a request
    came from is answered by the socket and not by a header a stranger writes. -/
    r := check r "a connection from 127.0.0.1 came from this machine"
      (Api.loopbackAddress (v4 127 0 0 1))
    r := check r "and one from anywhere else in 127/8 did"
      (Api.loopbackAddress (v4 127 13 2 9))
    r := check r "a connection from a private address did not"
      (!Api.loopbackAddress (v4 10 0 0 5))
    r := check r "::1 is this machine"
      (Api.loopbackAddress (v6 #v[0, 0, 0, 0, 0, 0, 0, 1]))
    r := check r "and so is the mapped form a dual-stack listener reports"
      (Api.loopbackAddress (v6 #v[0, 0, 0, 0, 0, 0xffff, 0x7f00, 1]))
    r := check r "a global address is not"
      (!Api.loopbackAddress (v6 #v[0x2001, 0xdb8, 0, 0, 0, 0, 0, 1]))
    r := check r "a peer the transport could not name is not this machine"
      (!Api.loopbackPeer? none)
    r := check r "and one it could is" (Api.loopbackPeer? (some (v4 127 0 0 1)))
    r := check r "the Host rule is still asked, because it is the other direction"
      (Api.loopbackHost "localhost:8087" && !Api.loopbackHost "attacker.example")

    /- ## N18 — what a form could have sent

    The exemptions are keyed on the method as well as the path: `PUT` is not a
    method a form can issue, and the argument for letting `attachments` through
    untyped was entirely about `PUT`. -/
    r := check r "a receipt arrives by PUT, which no form can issue"
      (Api.wellTyped "PUT" ["attachments"] "image/png")
    r := check r "a POST to the same path is not exempt"
      (!Api.wellTyped "POST" ["attachments"] "image/png")
    r := check r "an import says what the file is, and text/csv is not a type a form sends"
      (Api.wellTyped "POST" ["imports"] "text/csv")
    r := check r "text/plain is one, so it is refused"
      (!Api.wellTyped "POST" ["imports"] "text/plain")
    r := check r "and an import with no type at all is refused"
      (!Api.wellTyped "POST" ["imports"] "")
    r := check r "a PUT to imports is not the exemption either"
      (!Api.wellTyped "PUT" ["imports"] "text/csv")
    r := check r "everything else that changes something is JSON and says so"
      (Api.wellTyped "POST" ["transactions"] "application/json; charset=utf-8")
    r := check r "and a form's content type is not JSON"
      (!Api.wellTyped "POST" ["transactions"] "multipart/form-data")

    /- ## N17 — the name an attachment is offered under

    It arrives in a header, or in an op written by any member of a realm this
    node reads, and it is put into a response header. -/
    r := checkEq r "an ordinary name is offered as it is"
      (Api.contentDispositionName "receipt.pdf" "sha") "; filename=\"receipt.pdf\""
    r := checkEq r "a carriage return and a newline are taken out of it"
      (Api.contentDispositionName "a\r\nx-evil: 1" "sha") "; filename=\"ax-evil: 1\""
    r := checkEq r "so are the characters that would end the quoted string"
      (Api.contentDispositionName "q\";rm -rf" "sha")
      "; filename=\"qrm -rf\"; filename*=UTF-8''q%22%3Brm%20-rf"
    r := checkEq r "a name that is not ASCII is carried by RFC 5987 beside it"
      (Api.contentDispositionName "faktúra.pdf" "sha")
      "; filename=\"faktra.pdf\"; filename*=UTF-8''fakt%C3%BAra.pdf"
    r := checkEq r "and a name that is nothing but control characters is the digest"
      (Api.contentDispositionName "\x01\x02\x7f" "abc123") "; filename=\"abc123\""

    /- ## N11 — an invite fragment that could be read two ways

    Five fields joined with a colon are unambiguous exactly as long as no field
    can carry one. Ledger ids are names people choose, so the client holds them
    to the same rule the sequencer does. -/
    r := check r "an invite naming ids this protocol allows is read"
      (Cli.invitation? (fragmentFor "home" "self" identity.id)).isSome
    r := check r "one whose ledger id carries a colon is refused"
      (Cli.invitation? (fragmentFor "a:b" "self" identity.id)).isNone
    r := check r "and so is one whose realm id is not a name"
      (Cli.invitation? (fragmentFor "home" "a%b" identity.id)).isNone
    r := checkEq r "because the ambiguous one names a realm nobody offered"
      ((Node.readInvite? (fragmentFor "a:b" "self" identity.id)).map (·.realm) |>.getD "-")
      "b:self"
    r := check r "an invite is still refused when its inviter is not a member id"
      (Cli.invitation? (fragmentFor "home" "self" "nobody")).isNone

    /- ## G6 — the sixth field has two spellings and no others

    The genesis digest is what says the whole ledger a joiner is handed is the one
    that was meant, and the parser used to take any non-empty string for it. A
    malformed one failed closed downstream — nothing the sequencer serves can
    fingerprint to it — but it failed there with the wrong sentence, and the thin
    client's parser was already holding the field to a shape. Two parsers written
    to be the same rule should agree about which links exist. -/
    r := check r "a link carrying a real digest is read"
      (Node.readInvite? (fragmentFor "home" "self" identity.id)).isSome
    r := check r "and so is one from before an order had a first entry, because those \
                  are still out there"
      (Node.readInvite? (fragmentFor "home" "self" identity.id Node.noGenesis)).isSome
    r := check r "one carrying half a digest is not"
      (Node.readInvite? (fragmentFor "home" "self" identity.id "fedcba9876543210")).isNone
    r := check r "nor one carrying something the right length that is not hex"
      (Node.readInvite? (fragmentFor "home" "self" identity.id
        (String.ofList (List.replicate 32 'z')))).isNone
    r := check r "nor one that says nothing at all about where the order begins"
      (Node.readInvite? (fragmentFor "home" "self" identity.id "")).isNone
    r := check r "and the whole link is refused by it, not the one field"
      (Cli.invitation? (fragmentFor "home" "self" identity.id "beef")).isNone

    /- ## The agreement key carries a generation

    Without one, the pair a member published before their agreement secret
    leaked stays a valid self-attestation for ever, and an untrusted sequencer
    can go on serving it. -/
    r := checkEq r "a verifier states the width of the suite's signatures"
      (Sync.Verifier.ofSuite suite).signatureHexWidth (2 * suite.signatureSize)
    let verifier := Sync.Verifier.ofSuite suite
    let (pk, sk) := suite.signSeedKeypair (Sha256.hash "width".toUTF8)
    r := check r "so the signature that suite really makes is checked"
      (verifier.check (toHex pk) "hello".toUTF8 (toHex (suite.sign sk "hello".toUTF8)))
    r := check r "and one of another width is refused before the primitive sees it"
      (!verifier.check (toHex pk) "hello".toUTF8 (String.ofList (List.replicate 128 'a')))

    let cfg := Config.atDir (root / "rotating")
    let opened ← Ctx.open cfg
    let ident ← Node.Identity.create suite (Node.Identity.pathIn cfg) "pass"
    let ctx ← Node.Identity.install opened ident "me"
    Node.Settings.setMember cfg ident.id
    let keys ← Node.Keys.open suite (Node.Keys.pathIn cfg) "pass" ident
    let sent ← IO.mkRef (#[] : Array Json)
    -- A sequencer that serves one member record and remembers what was written
    -- to it, which is all the rotation rule reads and all it writes.
    let recorder (heldKey : String) (generation : Nat) : Node.Transport := fun q =>
      match q.method with
      | "GET" =>
        pure (.json 200 (Json.arr #[Json.mkObj
          [("member", ident.id), ("boxPk", heldKey), ("boxPkSignature", ""),
           ("keyGeneration", Sync.jnat generation)]]))
      | _ => do
        sent.modify (·.push ((Json.parse ((String.fromUTF8? q.body).getD "")).toOption.getD
          Json.null))
        pure (.json 200 (Json.mkObj []))
    let publishAgainst (heldKey : String) (generation : Nat) : IO Json := do
      sent.set #[]
      let session : Node.Session :=
        { ctx, suite, keys, transport := recorder heldKey generation, ledger := "home" }
      Node.Session.publishBoxPk session
      return ((← sent.get)[0]?).getD Json.null
    let mine := ident.boxPkHex
    let first ← publishAgainst "" 0
    r := checkEq r "a member's first agreement key is published at generation zero"
      (jnat first "keyGeneration") 0
    r := check r "and it is signed under that generation"
      (suite.checkHex ident.id (Sync.memberBytes "home" ident.id mine 0)
        (jstr first "boxPkSignature"))
    let again ← publishAgainst mine 3
    r := checkEq r "re-publishing the key already on file keeps its generation"
      (jnat again "keyGeneration") 3
    r := check r "signed under the generation it kept"
      (suite.checkHex ident.id (Sync.memberBytes "home" ident.id mine 3)
        (jstr again "boxPkSignature"))
    let rotated ← publishAgainst (String.ofList (List.replicate 64 'a')) 3
    r := checkEq r "while a different key takes the next one"
      (jnat rotated "keyGeneration") 4
    r := check r "signed under that one, so the sequencer will take it"
      (suite.checkHex ident.id (Sync.memberBytes "home" ident.id mine 4)
        (jstr rotated "boxPkSignature"))

    let session : Node.Session :=
      { ctx, suite, keys, transport := recorder "" 0, ledger := "home" }
    let atThree := Node.Identity.signHex suite ident (Sync.memberBytes "home" ident.id mine 3)
    r := check r "an attestation made at generation three does not verify at zero"
      (session.memberBoxPk? ident.id mine atThree).isNone
    r := check r "and does verify at three"
      (session.memberBoxPk? ident.id mine atThree 3).isSome
    r := check r "a key nobody signed for is still not sealed to"
      (session.memberBoxPk? ident.id mine "" 3).isNone

    /- ## M5 — `identity init` writes once

    A second `addMember` and a second `grant` for a key that has both would open
    a second purse for one person and hand out the admin role again, over an
    event every other node has to apply. -/
    let events ← Db.scalarInt ctx.db "SELECT COUNT(*) FROM event"
    let accounts := (← ctx.state.get).accounts.toList.length
    let twice ← Node.Identity.install ctx ident "me"
    r := checkEq r "'identity init' run twice appends nothing the second time"
      (← Db.scalarInt ctx.db "SELECT COUNT(*) FROM event") events
    r := checkEq r "and opens no second purse"
      (← twice.state.get).accounts.toList.length accounts
    r := checkEq r "while still committing as the identity that was asked for"
      twice.member.val ident.id

    /- ## N12 — the lengths a signature check is handed

    `checkHex` decoded two hex fields an untrusted sequencer wrote and passed
    whatever came out to the primitive. A real `crypto_sign_verify_detached`
    reads thirty-two bytes of public key and sixty-four of signature because
    that is what its contract says it is given, so a two-byte "key" is a buffer
    over-read on this node rather than a failed check. The sizes are the
    suite's, and they are asked before the primitive is. -/
    let msg := "a public statement".toUTF8
    let (pk32, sk32) := suite.signSeedKeypair (Sha256.hash "lengths".toUTF8)
    let sig := suite.sign sk32 msg
    r := check r "a key and a signature of the suite's own sizes verify"
      (suite.checkHex (toHex pk32) msg (toHex sig))
    -- A suite whose primitive says yes to anything, so that what turns a
    -- mis-sized key away is `checkHex` and not the check behind it.
    let credulous : Node.CryptoSuite := { suite with verify := fun _ _ _ => true }
    r := check r "a primitive that agrees to everything agrees to the right sizes"
      (credulous.checkHex (toHex pk32) msg (toHex sig))
    r := check r "but is never handed a key shorter than one"
      (!credulous.checkHex (toHex (pk32.extract 0 16)) msg (toHex sig))
    r := check r "nor a longer one"
      (!credulous.checkHex (toHex (pk32 ++ pk32)) msg (toHex sig))
    r := check r "nor a truncated signature"
      (!credulous.checkHex (toHex pk32) msg (toHex (sig.extract 0 8)))
    r := check r "nor a doubled one"
      (!credulous.checkHex (toHex pk32) msg (toHex (sig ++ sig)))
    r := check r "and an empty field is still not hex for anything"
      (!credulous.checkHex (toHex pk32) msg "")

    /- ## N20 — `Bearer` is a word, not a spelling

    RFC 7235 makes the scheme name case-insensitive, and the sequencer was
    taught so; the node's own API still matched the one capitalisation, so a
    conforming client sending `bearer` was told its token was missing. -/
    r := checkEq r "a token presented as the header is usually written is taken"
      (Api.bearerToken? "Bearer seq_ABC") (some "seq_ABC")
    r := checkEq r "and so is one whose scheme is lowercase"
      (Api.bearerToken? "bearer seq_ABC") (some "seq_ABC")
    r := checkEq r "however it is spelled"
      (Api.bearerToken? "BeArEr seq_ABC") (some "seq_ABC")
    r := checkEq r "while the secret itself keeps the case it arrived in"
      (Api.bearerToken? "BEARER SeQ_abc") (some "SeQ_abc")
    r := check r "another scheme presents no bearer token"
      (Api.bearerToken? "Basic dXNlcjpwYXNzd29yZA==").isNone
    r := check r "and neither does a header that names no scheme at all"
      (Api.bearerToken? "seq_ABC").isNone

    /- ## N13 — a realm id is a value and not a pattern

    Which realms an entry's unreadable parts were in used to be one comma-joined
    column, asked about with a `LIKE` pattern built out of the realm id. A realm
    whose id contains `_` then matched every neighbour differing in that one
    character, and one containing `,` was two other realms — either way the
    answer to "did this node miss a part of realm R" comes back "no" about a
    realm where it did. That is the answer that lets a node accuse everybody
    else of a difference it is itself the cause of, so it is a row per realm and
    an equality now. -/
    let only ← Db.scalarInt ctx.db "SELECT MIN(seq) FROM event"
    Db.exec ctx.db s!"UPDATE event SET remote_seq = 1 WHERE seq = {only}"
    Db.exec ctx.db s!"UPDATE event SET unreadable_realms = 'alpha,braXvo'
                      WHERE seq = {only}"
    -- The column as an older binary left it, put back through the migration
    -- that replaces it, which is the only thing that reads it any more. That
    -- migration is run on its own rather than by winding `user_version` back to
    -- 22, because the ones above it can no longer be undone a column at a time:
    -- `invoice.realm_id` is inside a `UNIQUE` since migration 30, and SQLite will
    -- not drop a column a constraint names. A pre-migration store is built from
    -- nothing further down instead, which is what the rebuilds are asked about.
    Db.exec ctx.db "DROP TABLE event_unreadable"
    for (v, sql) in Schema.migrations do
      if v == 23 then
        SQLite.transaction ctx.db (Db.exec ctx.db sql)
    r := checkEq r "migration 23 splits the column it retires into one row per realm"
      (← Db.scalarInt ctx.db "SELECT COUNT(*) FROM event_unreadable") 2
    r := check r "a realm a part was missed in is found by its own name"
      ((← Node.Checkpoint.missedParts ctx "alpha" 1)
        && (← Node.Checkpoint.missedParts ctx "braXvo" 1))
    -- The wildcard is in the id being asked about, so this is the question a
    -- revoked node asks of a realm it still holds: `bra_vo` used to match the
    -- gap recorded against `braXvo` and report a realm as unreadable that was
    -- read, and the same character asked the other way round hid a real gap.
    r := check r "while an underscore in the id asked about is a character and not any character"
      (!(← Node.Checkpoint.missedParts ctx "bra_vo" 1))
    r := check r "a realm nobody named is not named by a wildcard either"
      (!(← Node.Checkpoint.missedParts ctx "%" 1)
        && !(← Node.Checkpoint.missedParts ctx "_" 1)
        && !(← Node.Checkpoint.missedParts ctx "%_%" 1))
    -- A comma is the other half: joined into one column it was a separator, so
    -- a realm named `one,two` was recorded as gaps in `one` and in `two`.
    Db.exec ctx.db s!"INSERT OR IGNORE INTO event_unreadable (seq, realm)
                      VALUES ({only}, 'one,two')"
    r := check r "and a realm id carrying a comma is one realm rather than two"
      ((← Node.Checkpoint.missedParts ctx "one,two" 1)
        && !(← Node.Checkpoint.missedParts ctx "one" 1)
        && !(← Node.Checkpoint.missedParts ctx "two" 1))
    -- A8. The same rows asked the other way round, because a reader of this
    -- node's projection has to be told which realms it is a fold *around*.
    r := checkEq r "the realms a part was missed in are listed, each of them once"
      (← Node.Checkpoint.gappedRealms ctx 1) #["alpha", "braXvo", "one,two"]
    r := check r "and none of them is listed before the entry that missed it"
      (← Node.Checkpoint.gappedRealms ctx 0).isEmpty
    r := check r "a gap is in the order it was recorded at and not before it"
      (!(← Node.Checkpoint.missedParts ctx "alpha" 0))
    -- Nothing reads the column from here on: the rows are the record.
    Db.exec ctx.db "DELETE FROM event_unreadable"
    r := check r "and the column it was migrated out of is not consulted again"
      (!(← Node.Checkpoint.missedParts ctx "alpha" 1))
    r := check r "so a node that read every part of every realm flags none of them"
      (← Node.Checkpoint.gappedRealms ctx 1).isEmpty

    /- ## G4 — five more ledger-wide names that belong to a realm

    Migration 25 made an account's name unique inside its realm and left five
    tables behind it: a party, a label, a trip and a budget are named, an invoice
    is numbered, and every one of them grew a realm in migration 21, 22 or 24. The
    `UNIQUE` is the only thing still forcing uniqueness across the ledger —
    `Core/Apply.lean` stopped refusing a duplicate name when `ofThisRealm?` made
    names realm-local — and it fails from inside the projection's transaction, so
    a realm arriving from a sequencer with a label called what one here is called
    is applied to the state and then cannot be written down, which stops the pull
    rather than the entry. The invoice is the worst of the five: the counter is
    per realm, so two realms mint `2026-0001` as a matter of course.

    The rebuild is migration 25's, with one difference that the account did not
    have. `txn_label`, `budget_participant`, `invoice_line` and `invoice_source`
    reference their parents ON DELETE CASCADE, and a `DROP TABLE` performs an
    implicit `DELETE FROM` that fires it — `defer_foreign_keys` defers the check
    and not the action. So those rows are put aside beside the parent's and put
    back with them, and what this asks is whether they are all still there. -/
    let pre ← SQLite.open (root / "pre26.db") (busyTimeoutMs := 5000)
    Db.exec pre "PRAGMA foreign_keys = ON"
    for (v, sql) in Schema.migrations do
      if v ≤ 25 then
        SQLite.transaction pre do
          Db.exec pre sql
          Db.exec pre s!"PRAGMA user_version = {v}"
    let self := Realm.selfId.val
    Db.exec pre "INSERT INTO realm (id, name, generation) VALUES ('r-sicily', 'Sicily', 0)"
    Db.exec pre s!"INSERT INTO party (id, name, iban, email, note, kind, realm_id)
      VALUES ('p-bo', 'Bo', 'DE02', 'bo@example.test', 'a note', 'contact', '{self}')"
    Db.exec pre s!"INSERT INTO label (id, name, colour, realm_id)
      VALUES ('l-food', 'groceries', 'green', '{self}')"
    Db.exec pre s!"INSERT INTO trip (id, name, starts, ends, payer, note, created_at, realm_id)
      VALUES ('t-sic', 'Sicily', '2026-04-01', '2026-04-08', 'Bo', 'a note', 'x', '{self}')"
    Db.exec pre s!"INSERT INTO account (id, name, kind, owner_id, realm_id)
      VALUES ('acc-hut', 'Budget.Hut', 'equity', 'p-bo', '{self}')"
    Db.exec pre s!"INSERT INTO budget
      (id, name, note, created_at, closed_at, realm_id, account_id, label_id)
      VALUES ('b-hut', 'Budget.Hut', 'a note', 'x', NULL, '{self}', 'acc-hut', 'l-food')"
    Db.exec pre "INSERT INTO budget_participant (budget_id, idx, owner_id, account, weight)
      VALUES ('b-hut', 0, 'p-bo', 'Expenses.Hut', 2)"
    Db.exec pre "INSERT INTO txn (id, date, payee, narration, source, created_at, updated_at)
      VALUES ('tx-1', '2026-04-02', NULL, 'beds', 'manual:old', 'x', 'x')"
    Db.exec pre "INSERT INTO txn_label (txn_id, label_id, idx) VALUES ('tx-1', 'l-food', 0)"
    Db.exec pre s!"INSERT INTO invoice
      (id, number, issued, due, payer_id, payer_name, commodity, reference, status, note,
       settled_txn, created_at, payment_kind, payment_data, source_account, budget_id,
       pending_txn, realm_id)
      VALUES ('inv-1', '2026-0001', '2026-04-01', '2026-05-01', 'p-bo', 'Bo', 'EUR', 'RF18',
              'draft', NULL, NULL, 'x', 'link', 'https://pay.test', 'acc-hut', 'b-hut',
              NULL, '{self}')"
    Db.exec pre "INSERT INTO invoice_line
      (invoice_id, idx, description, qty_milli, unit_minor, tax_bp)
      VALUES ('inv-1', 0, 'beds', 1000, 12000, 0)"
    Db.exec pre "INSERT INTO invoice_source (invoice_id, txn_id, idx) VALUES ('inv-1', 'tx-1', 0)"
    Db.exec pre "INSERT INTO token (id, name, hash, scopes, created_at, owner_id, budget_id)
      VALUES ('tok-1', 'a link', 'h', 1, 'x', 'p-bo', 'b-hut')"
    r := checkEq r "a store written before the five rebuilds stops one short of them"
      (← Schema.currentVersion pre) 25
    -- The five, and whatever has been appended since they shipped.
    r := checkEq r "and all five run when it is opened"
      (← Schema.migrate pre) (Schema.targetVersion - 25)
    r := checkEq r "leaving it at the version this binary expects"
      (← Schema.currentVersion pre) Schema.targetVersion
    r := checkEq r "a party comes through the rebuild with every column it had"
      ((← Db.row? String pre "SELECT name || '/' || iban || '/' || email || '/' || note
                              || '/' || kind || '/' || realm_id
                              FROM party WHERE id = 'p-bo'").getD "")
      s!"Bo/DE02/bo@example.test/a note/contact/{self}"
    r := checkEq r "and a label with its colour and its realm"
      ((← Db.row? String pre
        "SELECT colour || '/' || realm_id FROM label WHERE id = 'l-food'").getD "")
      s!"green/{self}"
    r := checkEq r "and a trip with its dates, its payer and its note"
      ((← Db.row? String pre "SELECT starts || '/' || ends || '/' || payer || '/' || note
                              FROM trip WHERE id = 't-sic'").getD "")
      "2026-04-01/2026-04-08/Bo/a note"
    r := checkEq r "and a budget with the three ids it is keyed to"
      ((← Db.row? String pre "SELECT realm_id || '/' || account_id || '/' || label_id
                              FROM budget WHERE id = 'b-hut'").getD "")
      s!"{self}/acc-hut/l-food"
    r := checkEq r "and an invoice with its payment, its source account and its realm"
      ((← Db.row? String pre "SELECT payment_kind || '/' || payment_data || '/' ||
                                     source_account || '/' || realm_id
                              FROM invoice WHERE id = 'inv-1'").getD "")
      s!"link/https://pay.test/acc-hut/{self}"
    r := checkEq r "the labels a transaction carries survive the rebuild they cascade off"
      (← Db.scalarInt pre "SELECT COUNT(*) FROM txn_label") 1
    r := checkEq r "and a budget's participants, with the weight they were given"
      (← Db.scalarInt pre "SELECT weight FROM budget_participant WHERE budget_id = 'b-hut'") 2
    r := checkEq r "and an invoice's lines"
      (← Db.scalarInt pre "SELECT COUNT(*) FROM invoice_line") 1
    r := checkEq r "and the outlays it bills for"
      (← Db.scalarInt pre "SELECT COUNT(*) FROM invoice_source") 1
    r := checkEq r "with no reference left dangling anywhere in the store"
      (← Db.scalarInt pre "SELECT COUNT(*) FROM pragma_foreign_key_check") 0
    r := checkEq r "and the indexes the dropped tables carried are back"
      (← Db.scalarInt pre "SELECT COUNT(*) FROM sqlite_master WHERE type = 'index'
                           AND name IN ('party_kind', 'invoice_source_txn', 'account_owner')") 3
    -- The constraint the five rebuilds exist to replace, read from both sides.
    let accepted (sql : String) : IO Bool := do
      (do Db.exec pre sql; pure true) <|> pure false
    r := check r "a person's name may be taken again in another realm"
      (← accepted "INSERT INTO party (id, name, kind, realm_id)
                   VALUES ('p-2', 'Bo', 'contact', 'r-sicily')")
    r := check r "and not twice in one"
      (!(← accepted "INSERT INTO party (id, name, kind, realm_id)
                     VALUES ('p-3', 'Bo', 'contact', 'r-sicily')"))
    r := check r "a label's name may be"
      (← accepted "INSERT INTO label (id, name, colour, realm_id)
                   VALUES ('l-2', 'groceries', 'green', 'r-sicily')")
    r := check r "and not twice in one realm either"
      (!(← accepted "INSERT INTO label (id, name, colour, realm_id)
                     VALUES ('l-3', 'groceries', 'green', 'r-sicily')"))
    r := check r "a trip's name may be"
      (← accepted "INSERT INTO trip (id, name, starts, ends, payer, note, created_at, realm_id)
                   VALUES ('t-2', 'Sicily', '2026-04-01', '2026-04-08', 'Bo', NULL, 'x',
                           'r-sicily')")
    r := check r "and not twice in one realm"
      (!(← accepted "INSERT INTO trip (id, name, starts, ends, payer, note, created_at, realm_id)
                     VALUES ('t-3', 'Sicily', '2026-04-01', '2026-04-08', 'Bo', NULL, 'x',
                             'r-sicily')"))
    r := check r "a budget's name may be"
      (← accepted "INSERT INTO budget
                   (id, name, note, created_at, closed_at, realm_id, account_id, label_id)
                   VALUES ('b-2', 'Budget.Hut', NULL, 'x', NULL, 'r-sicily', 'acc-hut', 'l-2')")
    r := check r "and not twice in one realm"
      (!(← accepted "INSERT INTO budget
                     (id, name, note, created_at, closed_at, realm_id, account_id, label_id)
                     VALUES ('b-3', 'Budget.Hut', NULL, 'x', NULL, 'r-sicily', 'acc-hut',
                             'l-2')"))
    r := check r "and two realms may mint the same invoice number, which is what a counter \
                  kept per realm does on purpose"
      (← accepted "INSERT INTO invoice
                   (id, number, issued, due, payer_id, payer_name, commodity, reference, status,
                    note, settled_txn, created_at, payment_kind, payment_data, source_account,
                    budget_id, pending_txn, realm_id)
                   VALUES ('inv-2', '2026-0001', '2026-04-01', '2026-05-01', NULL, 'Bo', 'EUR',
                           'RF19', 'draft', NULL, NULL, 'x', 'link', 'https://pay.test', NULL,
                           NULL, NULL, 'r-sicily')")
    r := check r "while one realm may not mint it twice"
      (!(← accepted "INSERT INTO invoice
                     (id, number, issued, due, payer_id, payer_name, commodity, reference,
                      status, note, settled_txn, created_at, payment_kind, payment_data,
                      source_account, budget_id, pending_txn, realm_id)
                     VALUES ('inv-3', '2026-0001', '2026-04-01', '2026-05-01', NULL, 'Bo',
                             'EUR', 'RF20', 'draft', NULL, NULL, 'x', 'link',
                             'https://pay.test', NULL, NULL, NULL, 'r-sicily')"))

    /- ## G4 — and the projection that could not be written before

    The constraint aborted the transaction the projection was in, so the fix is
    only a fix if the projection can now write both rows and read both back. Two
    realms, the same five names in each, straight through `Project.apply` and out
    again through `Load.fromDb`.

    A trip is the one that does not come back twice, and for a reason that has
    nothing to do with this: `State.trips` is keyed by name rather than by id, so
    the tables hold two and the state holds one. The tables are what the
    projection writes, and writing them is what used to fail. -/
    let bothCtx ← Ctx.open (Config.atDir (root / "two-realms"))
    let sicily : RealmId := ⟨"realm-sicily"⟩
    let day (iso : String) : Date := (Date.ofIso? iso).getD default
    Project.apply bothCtx.db (.realm { id := sicily, name := "Sicily", members := [] })
    let writeInto (realm : RealmId) (tag : String) : IO Unit := do
      Project.apply bothCtx.db (.party
        { id := ⟨s!"p-{tag}"⟩, name := "Bo", kind := "contact", realm })
      Project.apply bothCtx.db (.label { id := ⟨s!"l-{tag}"⟩, name := "groceries", realm })
      Project.apply bothCtx.db (.trip
        { id := s!"t-{tag}", name := "Sicily", starts := day "2026-04-01",
          ends := day "2026-04-08", payer := "Bo", note := none, realm })
      Project.apply bothCtx.db (.budget
        { budget := { id := ⟨s!"b-{tag}"⟩, name := "Budget.Hut", note := none, closed := false },
          realm, account := ⟨s!"acc-{tag}"⟩, label := ⟨s!"l-{tag}"⟩ })
      Project.apply bothCtx.db (.invoice
        { invoice :=
            { id := ⟨s!"i-{tag}"⟩, number := "2026-0001", issued := day "2026-04-01",
              due := day "2026-05-01", payerId := none, payerName := "Bo",
              commodity := Commodity.eur, reference := "RF18", status := .draft,
              note := none, settledTxn := none, payment := .link "https://pay.test",
              sourceAccount := none, budgetId := none, pendingTxn := none, lines := [] },
          sources := [], realm })
    writeInto Realm.selfId "here"
    writeInto sicily "there"
    let loaded ← Load.fromDb bothCtx.db
    let boRealms := loaded.parties.toList.filterMap fun (_, p) =>
      if p.name == "Bo" then some p.realm.val else none
    r := checkEq r "two realms may each record a person of one name, and both come back"
      boRealms.length 2
    r := check r "each in the realm it was written in"
      (boRealms.contains Realm.selfId.val && boRealms.contains sicily.val)
    r := checkEq r "and a label of one name"
      (loaded.labels.toList.filter (fun (_, l) => l.name == "groceries")).length 2
    r := checkEq r "and a budget of one name"
      (loaded.budgets.toList.filter (fun (_, b) => b.budget.name == "Budget.Hut")).length 2
    r := checkEq r "and an invoice of one number, which per-realm numbering makes the \
                    ordinary case rather than the accident"
      (loaded.invoices.toList.filter (fun (_, i) => i.invoice.number == "2026-0001")).length 2
    r := checkEq r "while two trips of one name are two rows the projection can now write"
      (← Db.scalarInt bothCtx.db "SELECT COUNT(*) FROM trip WHERE name = 'Sicily'") 2

    /- ## N9 — an agreement key's generation only ever goes up

    The sequencer refuses a write that lowers one, which is the wrong party to
    be relying on: it is the sequencer that would be serving the old pair. A
    client with no record of its own can be handed the consistent
    `(boxPk, signature, generation)` triple from before a member's agreement
    secret leaked for ever, because every field of it verifies and nothing in
    one record says a later one exists. So the highest seen is written down. -/
    let atZero := Node.Identity.signHex suite ident (Sync.memberBytes "home" ident.id mine 0)
    r := check r "a member record at the generation it was signed under is read"
      (← session.memberKey? ident.id mine atThree 3).isSome
    r := checkEq r "and the highest generation seen is kept in sync.json"
      ((← Node.Settings.load cfg).generationOf ident.id) 3
    r := check r "after which the same member's pair from before the rotation is not"
      (← session.memberKey? ident.id mine atZero 0).isNone
    r := check r "and the record on file is not moved backwards by having been offered one"
      (((← Node.Settings.load cfg).generationOf ident.id) == 3)

    /- ## A3 — the pin is a bootstrap, and it stops counting

    A node that has replayed nothing knows nobody, so the key its invite link
    named is the one reason it has to believe a wrapped key or a commitment. The
    moment it has replayed a realm's membership, that membership is the answer —
    otherwise the admin who sent the link stays trusted after the entry demoting
    them has been applied, and `Checkpoint.offered?` takes the highest `seq`
    among trusted authors, so one stale commitment from a demoted inviter
    outranks every honest one below it and starts a whole store from itself. -/
    let (inviterPk, inviterSk) := suite.signSeedKeypair (Sha256.hash "the inviter".toUTF8)
    let inviter := toHex inviterPk
    -- A realm this node has not replayed a word of, which is what every realm
    -- looks like between `adoptLedger` and the first pull, and a realm whose
    -- membership it has read and which does not name the inviter as an admin —
    -- which is what a demotion leaves behind.
    let bootRealm : RealmId := ⟨"realm-unread"⟩
    let readRealm : RealmId := ⟨"realm-read"⟩
    Node.Settings.pin cfg bootRealm.val inviter
    Node.Settings.pin cfg readRealm.val inviter
    discard <| ctx.commit "test"
      [.createRealm { id := readRealm, name := "read", members := [(ctx.member, .admin)] }]
      (realm := readRealm)
    r := check r "the realm this node has not read is not in its state"
      (((← ctx.state.get).realm? bootRealm).isNone)
    r := check r "while the other one names an admin, and it is not the pinned inviter"
      ((← ctx.state.get).canAdminister ctx.member readRealm
        && !(← ctx.state.get).canAdminister ⟨inviter⟩ readRealm)
    let pinned : Node.Session :=
      { ctx, suite, keys, transport := recorder "" 0, ledger := "home" }
    r := check r "a pinned inviter is believed about a realm whose admins this node cannot see"
      (← pinned.trusts bootRealm.val inviter)
    r := check r "and is not believed about one whose membership it has read"
      (!(← pinned.trusts readRealm.val inviter))
    r := check r "and a stranger is nobody anywhere"
      (!(← pinned.trusts bootRealm.val (toHex (Sha256.hash "nobody".toUTF8))))

    /- ## G7 — a realm read in part is a realm not read

    "This node's own state records an admin of that realm" is only an answer when
    the state has seen everything the realm said. A node that could not open a
    part written there has folded around whatever it said, and one of the things
    it may have said is that somebody has been demoted — so the admin set it would
    consult is one entry out of date in a direction it cannot see.
    `Checkpoint.verifyOne` already declines to compare a projection of such a
    realm; `trusts` used to read its membership as though nothing were missing.
    Falling back to the pin is the fail-closed direction: a pin names one key and
    a stale set may name several. -/
    Db.exec ctx.db s!"INSERT OR IGNORE INTO event_unreadable (seq, realm)
                      VALUES ({only}, {Db.lit readRealm.val})"
    r := check r "a realm this node folded around a part it could not open is one it has \
                  not read, so the pin counts again"
      (← pinned.trusts readRealm.val inviter)
    Db.exec ctx.db s!"DELETE FROM event_unreadable WHERE realm = {Db.lit readRealm.val}"
    r := check r "and once every part of it has been read the membership answers once more"
      (!(← pinned.trusts readRealm.val inviter))

    let realmKey ← suite.randomBytes suite.keySize
    let wrapped := suite.wrapKey ident.boxPk realmKey
    let grantFrom (realm : String) : Node.GrantRecord :=
      { realm, member := ident.id, generation := 0, role := "viewer", wrappedKey := wrapped,
        grantedBy := inviter,
        signature := toHex (suite.sign inviterSk
          (Sync.grantBytes "home" realm 0 ident.id "viewer" wrapped)) }
    r := check r "a grant from the pinned inviter stands on the realm this node has not read"
      (!wasRefused (← pinned.checkGrant (grantFrom bootRealm.val)))
    r := check r "and the same signature is refused on the realm that has demoted them"
      (wasRefused (← pinned.checkGrant (grantFrom readRealm.val)))

    -- The same question about a commitment, which is the one that starts whole
    -- stores: signed properly, sealed under a key this node holds, and opened.
    let (bootGen, bootKey) ← Node.Keys.create keys bootRealm.val
    let (readGen, readKey) ← Node.Keys.create keys readRealm.val
    let commitmentFor (realm : String) (generation : Nat) (key : ByteArray) : IO Json := do
      let bytes := Codec.encode State.init
      let nonce ← suite.randomBytes suite.nonceSize
      let sealed := suite.sealPart key nonce
        (Node.snapshotAd "home" realm generation inviter) bytes
      let unsigned : Sync.Checkpoint :=
        { ledger := "home", realm, generation, seq := 4,
          stateHash := Encode.hashState State.init, headHash := "beef", author := inviter,
          signature := "", snapshot := nonce ++ sealed }
      return { unsigned with
               signature := toHex (suite.sign inviterSk unsigned.commitmentBytes) }.toJson
    let serving (j : Json) : Node.Transport := fun _ => pure (.json 200 (Json.arr #[j]))
    r := check r "a commitment from the pinned inviter may start a store on an unread realm"
      (← Node.Checkpoint.offered? { pinned with transport := serving (← commitmentFor
        bootRealm.val bootGen bootKey) } bootRealm.val).isSome
    r := check r "and the identical one is passed over on the realm that has demoted them"
      (← Node.Checkpoint.offered? { pinned with transport := serving (← commitmentFor
        readRealm.val readGen readKey) } readRealm.val).isNone

    /- ## A2 — a store started from a commitment is anchored to something

    `seedFromOffer` replaces the whole of what a store says with a state it was
    handed, so the question of whose word that is has to be settled before it
    runs. Either this node holds the order from the entry its link named up to
    the one committed to, or the commitment is that link's own author's — and
    then the store writes down that it never saw the beginning, because it did
    not. -/
    let seedCfg := Config.atDir (root / "seeded")
    let seedCtx ← Ctx.open seedCfg
    Node.adoptLedger seedCtx
    let seedKeys ← Node.Keys.open suite (Node.Keys.pathIn seedCfg) "pass" ident
    let seeded : Node.Session :=
      { ctx := seedCtx, suite, keys := seedKeys, transport := recorder "" 0, ledger := "home" }
    let offer : Node.Checkpoint.Offer :=
      { seq := 7, headHash := "beef", state := State.init, author := inviter }
    r := check r "a commitment this node can neither link back nor put on its inviter \
                  starts nothing"
      (← refused (Node.seedFromOffer seeded "realm-seed" offer))
    r := check r "and the store it would have started is still empty"
      ((← EventLog.head seedCtx.db).1 == 0)
    Node.Settings.pin seedCfg "realm-seed" inviter

    /- ## G3 — what a commitment is its author's word about

    `Checkpoint.offered?` settles that its author is trusted *on this realm*,
    which is the only authority anybody in this system holds. What `seedFromOffer`
    then does with it is write it at position 1, and a genesis replaces
    everything — so a state carrying entities outside that realm is one member's
    word about a realm they were never in, taken as the whole truth about it, and
    `Session.trusts` would afterwards read that very state back as the reason to
    believe them. The self realm is the exception because `State.init` records it
    before a single part has been folded. -/
    let elsewhere : RealmId := ⟨"realm-elsewhere"⟩
    let strayAccount : Account :=
      { id := ⟨"acc-stray"⟩, name := "Assets.Elsewhere", kind := .asset, realm := elsewhere }
    let withStrayAccount : State :=
      { State.init with accounts := State.init.accounts.insert strayAccount.id.val strayAccount }
    let strayRealm : Realm :=
      { id := elsewhere, name := "elsewhere", members := [(⟨inviter⟩, .admin)] }
    let withStrayRealm : State :=
      { State.init with realms := State.init.realms.insert elsewhere.val strayRealm }
    let offering (st : State) : IO Bool :=
      refused (Node.seedFromOffer seeded "realm-seed" { offer with state := st })
    r := check r "a commitment whose state carries an account in another realm starts nothing"
      (← offering withStrayAccount)
    r := check r "nor does one that records another realm at all"
      (← offering withStrayRealm)
    r := check r "and neither of them left a store behind" ((← EventLog.head seedCtx.db).1 == 0)
    r := check r "the same one from the inviter the link pinned, confined to that realm, \
                  does start it"
      (!(← refused (Node.seedFromOffer seeded "realm-seed" offer)))
    r := check r "and the store records that it never saw the entry the order begins with"
      (!(← Node.Settings.load seedCfg).genesisSeen)

    /- ## G3 — and it is a first join's word and no other's

    A join always empties the store, so a second join's `seedFromOffer` looks from
    the inside exactly like a first's; what tells them apart is `sync.json`, where
    the pin of every realm this node has been let into is kept. If one names
    another realm then this node has read a realm before, and taking a snapshot on
    the second inviter's word would replace its projection of the first — `pull`
    resumes at `offer.seq + 1`, so the entries that realm's history is in are
    never read again. The second inviter would then be naming themselves the first
    realm's admin, permanently, in a realm they administer nothing in. -/
    let againCfg := Config.atDir (root / "second-join")
    let againCtx ← Ctx.open againCfg
    Node.adoptLedger againCtx
    let againKeys ← Node.Keys.open suite (Node.Keys.pathIn againCfg) "pass" ident
    let again : Node.Session :=
      { ctx := againCtx, suite, keys := againKeys, transport := recorder "" 0, ledger := "home" }
    Node.Settings.pin againCfg "realm-first" inviter
    Node.Settings.pin againCfg "realm-seed" inviter
    r := check r "a node that has been let into a realm before does not replace its books \
                  on a second inviter's word"
      (← refused (Node.seedFromOffer again "realm-seed" offer))
    r := check r "and that store is still empty too" ((← EventLog.head againCtx.db).1 == 0)

    /- ## N15 — what an error reply tells whoever asked

    A route that refuses its caller says something they can act on. Everything
    else — SQLite naming a table and a column, `IO.FS` naming a path — is the
    operator's business and nobody else's, and reflecting it back described the
    shape of the database to whoever asked in exchange for nothing. -/
    r := check r "what the database says is not a sentence written for a caller"
      (← failedInternally (Db.exec ctx.db "SELECT no_such_column FROM event"))
    r := check r "while a refusal a route wrote is"
      (!(← failedInternally (throw (IO.userError "no such account") : IO Unit)))
    let refusal ← Api.handleSafe ctx Api.bootstrapCaller
      ((Api.Req.simple "POST" ["realms"]).withJson (Json.mkObj [("name", "")]))
    r := checkEq r "a refusal meant for the caller is answered with its own words"
      (replyStr refusal "error") "a realm needs a name"
    r := checkEq r "and a 400" refusal.code 400
    let broken : Api.NodeApi :=
      { status := fun _ => throw (IO.Error.otherError 0 "no such column: secret_column") }
    let inside ← Api.handleSafe ctx Api.bootstrapCaller
      (Api.Req.simple "GET" ["sync", "status"]) broken
    r := checkEq r "a failure from underneath is a 500" inside.code 500
    r := checkEq r "that says nothing about what failed"
      (replyStr inside "error") "the request could not be completed"
    r := checkEq r "beside an eight-character correlation id to find it in the log by"
      (replyStr inside "code").length 8
    r := checkEq r "and nothing the layer underneath said is anywhere in the reply"
      ((((replyStr inside "error") ++ (replyStr inside "code")).splitOn "secret_column").length) 1

    return r
  finally
    IO.FS.removeDirAll root <|> pure ()
