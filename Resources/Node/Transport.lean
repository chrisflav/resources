import Resources.Node.Identity
import Resources.Sync.Routes

/-!
# Talking to a sequencer

A transport is one function: a request below `/seq/v2`, and the reply. That is
the same `Api.Req`/`Api.Reply` pair the sequencer's route table is written over,
which is what lets a test drive a real sequencer in the same process, through
the real routes, with no socket anywhere — and lets the node that ships talk to
one over HTTP without a second copy of the protocol.

Two implementations:

* `overCurl` shells out to `curl`, as `Cli/Client.lean` does, because `Std.Http`
  ships a server and not yet a client;
* `inProcess` calls `Sync.handleSafe` on a `Sync.Node` directly.

Sessions are handled here rather than by callers. The sequencer has no accounts:
a caller asks for a nonce, signs it, and gets a bearer token that speaks for the
key that signed. So a transport holds the token it was given, gets one the first
time it is used, and gets another if the one it holds has expired — which a
route says by answering 401, the one reply that is worth retrying.

## The origin a challenge is answered at

What a client signs to authenticate names the sequencer: `challengeBytes` puts
the deployment's public origin in front of the nonce. A signature taken for one
origin opens no session at another, which is what stops a second instance from
relaying a challenge from the real one and holding a session as whoever answered
it — *provided the client knows which origin it meant*.

That proviso is the whole of it, and version 2 missed it. `health` says what the
server calls itself and `challenge` says it again, but both of those come from
the same party: a relay at `https://evil.example` reports the real deployment's
origin from every route it serves, fetches a challenge from the real sequencer,
serves it as its own, and forwards the signature it gets back. Every string
matches, because the attacker chose all of them.

So the value that decides is the one thing the attacker did not choose: the URL
this node dialled. `sessioned` takes it, and the origin `health` reported, the
one the challenge named and the one the token came back with all have to agree
with it — as scheme, host and port, so that a trailing slash, a default port or
a capital letter in the host is not a mismatch and nothing else is a match. A
node that finds otherwise signs nothing and the session is abandoned.

## Shelling out to curl

`overCurl` is the only thing here that touches a socket, and the shape of the
call is where several small holes were. The token now travels in a `--config`
file written 0600 inside a directory created 0700, never in argv where every
local user can read it out of `ps`; the body goes the same way and the response
comes back on stdout rather than through a file with the process umask on it;
`--` ends the options, so a base URL beginning with a dash is a URL and not a
flag; `--proto` refuses a plaintext transfer unless the host is this machine;
`--max-time` bounds a sequencer that accepts a connection and then says nothing;
and every path segment is percent-encoded, so a segment carrying `?`, `#` or a
slash names a path and cannot reshape the request.

The config file's *contents* were the hole left after all of that. It is written
`header = "authorization: Bearer <token>"`, and the token is a string the server
chose: curl reads that file as directives, so a token carrying a quote and a
newline closes the header and opens `--output`, `--upload-file` or another
`--config`, which is file write and file read on the node's own machine at the
word of the party this whole design is written against. A token is now checked
against the shape a token has before it is stored, and the line is written with
its value quoted and escaped regardless.
-/

open Lean

namespace Resources
namespace Node

/-- A sequencer, as one function. -/
abbrev Transport := Api.Req → IO Api.Reply

/--
The query parameters the sequencer's routes take.

A request's query is a function, so it cannot be enumerated; a transport that
has to write a URL therefore asks for the parameters the protocol defines. The
list is short because the protocol is: a fetch says where it has got to, and
nothing else asks anything.
-/
def queryKeys : List String := ["since", "limit"]

namespace Transport

/-! ## Building requests -/

/-- A GET below `/seq/v2`. -/
def get (segments : List String) (query : List (String × String) := []) : Api.Req :=
  (Api.Req.simple "GET" segments).withQuery query

/-- A request with a JSON body. -/
def send (method : String) (segments : List String) (body : Json) : Api.Req :=
  ((Api.Req.simple method segments).withJson body).withHeaders
    [("content-type", "application/json")]

/-- A request whose body is bytes rather than JSON: how a blob's ciphertext travels. -/
def upload (method : String) (segments : List String) (body : ByteArray) : Api.Req :=
  ((Api.Req.simple method segments).withBody body).withHeaders
    [("content-type", "application/octet-stream")]

/-- The same request, carrying a bearer token. -/
private def withToken (r : Api.Req) (token : String) : Api.Req :=
  { r with header := fun k =>
      if k.toLower == "authorization" then some ("Bearer " ++ token) else r.header k }

/-! ## Reading replies -/

/-- The JSON a reply carries, or null for a binary one. -/
def payload (reply : Api.Reply) : Json := reply.json?.getD Json.null

/--
The bytes a reply carries, when it is a binary one.

`curl` has no headers here — the body is all that comes back — so `curlCall`
guesses, and bytes that happen to parse as JSON come back as JSON. Every caller
of this checks what it got against a hash it already knew, so the guess costs a
retry and never a wrong answer.
-/
def bytes? (reply : Api.Reply) : Option ByteArray :=
  match reply with
  | .bytes _ _ data _ => some data
  | .json .. => none

/-- The message a refusal carries, or its whole body when it is not one of ours. -/
def errorOf (reply : Api.Reply) : String :=
  match (payload reply).getObjValAs? String "error" with
  | .ok msg => msg
  | .error _ => s!"the sequencer answered {reply.code}"

/-- Runs a request and insists on success, raising whatever the sequencer objected to. -/
def json (t : Transport) (r : Api.Req) : IO Json := do
  let reply ← t r
  if reply.code ≥ 400 then throw <| IO.userError (errorOf reply)
  return payload reply

/-- Runs a request and hands back the status code beside the payload. -/
def result (t : Transport) (r : Api.Req) : IO (Nat × Json) := do
  let reply ← t r
  return (reply.code, payload reply)

/-! ## Reading a URL

Two questions are asked of a URL here — whether it names this machine, and which
origin it is — and both used to be answered by cutting the string up at the
first thing that looked right. `(url.splitOn "://").getLast?` reads
`https://ok/x://127.0.0.1` as loopback because the *last* `://` won, and
`takeWhile` reads `http://127.0.0.1@evil.com/` as loopback because userinfo is
not part of a host. Both answers permitted a plaintext transfer to somebody
else's server. So the authority is parsed once, properly, and everything that
has an opinion about a URL asks this.
-/

/-- Splits on the first occurrence of a separator, or `none` when there is none. -/
private def splitFirst (s sep : String) : Option (String × String) :=
  match s.splitOn sep with
  | first :: rest@(_ :: _) => some (first, String.intercalate sep rest)
  | _ => none

/-- Whether a string is a non-empty run of decimal digits. -/
private def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/--
The three parts of a URL that decide what it is and where it goes.

The port is never `none`: a URL that does not state one states it by its scheme,
and two URLs that name the same host on the same port are the same endpoint
whether or not either of them wrote `:443` down.
-/
structure Endpoint where
  /-- `http` or `https`, lowercased; this transport speaks no other. -/
  scheme : String
  /-- The host, lowercased, with an IPv6 literal keeping its brackets. -/
  host : String
  /-- The port, from the URL or from the scheme's default. -/
  port : Nat
  deriving Repr, BEq, Inhabited

/-- Whether a host is one written the way a host is written. -/
private def plainHost (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isAlphanum || c == '.' || c == '-' || c == '_'

/-- Host and port, out of an authority that has had its userinfo taken off. -/
private def hostPort? (scheme hostPort : String) : Option (String × Nat) :=
  let dflt := if scheme == "https" then 443 else 80
  if hostPort.startsWith "[" then
    match splitFirst hostPort "]" with
    | none => none
    | some (bracketed, after) =>
      let inside := (bracketed.drop 1).toString
      if inside.isEmpty || !inside.all (fun c => c.isHexDigit || c == ':' || c == '.') then none
      else if after.isEmpty then some (s!"[{inside.toLower}]", dflt)
      else if after.startsWith ":" && isDigits (after.drop 1).toString then
        some (s!"[{inside.toLower}]", (after.drop 1).toString.toNat!)
      else none
  else
    match hostPort.splitOn ":" with
    | [h] => if plainHost h then some (h.toLower, dflt) else none
    | [h, p] => if plainHost h && isDigits p then some (h.toLower, p.toNat!) else none
    | _ => none

/--
The endpoint a URL names, or `none` when it does not name one.

Strict on purpose, and in the direction that fails safe: everything that asks
this treats `none` as "not loopback" and as "not the origin I dialled", so a URL
this cannot read is a TLS transfer and a refused session rather than a guess.
-/
def endpoint? (url : String) : Option Endpoint := do
  let (scheme, rest) ← splitFirst url "://"
  let scheme := scheme.toLower
  guard (scheme == "http" || scheme == "https")
  let authority := (rest.takeWhile fun c => c != '/' && c != '?' && c != '#').toString
  -- Userinfo is everything before the last `@`, and it is not the host: the
  -- host of `http://127.0.0.1@evil.com/` is `evil.com`.
  let hostPort ← (authority.splitOn "@").getLast?
  let (host, port) ← hostPort? scheme hostPort
  return { scheme, host, port }

/--
Whether a URL names this machine.

It decides one thing: whether an unencrypted transfer is allowed. A sequencer on
loopback has no network to be watched on, and insisting on TLS there would mean
no local development; anywhere else, a `sync.json` holding an `http://` URL is a
silent downgrade and `--proto` turns it into a refusal.

`localhost`, `127.0.0.0/8` and `[::1]` are loopback and nothing else is — a host
that merely begins with `127.` is not a number, and a URL that will not parse is
not this machine.
-/
def loopbackUrl (url : String) : Bool :=
  match endpoint? url with
  | none => false
  | some e =>
    e.host == "localhost" || e.host == "[::1]" ||
      (match e.host.splitOn "." with
       | [a, b, c, d] => a == "127" && [b, c, d].all isDigits
       | _ => false)

/--
The origin a URL names: scheme, host and port, with the port written out.

This is the string two URLs are compared as. `https://Seq.Example/` and
`https://seq.example:443` are one deployment; `https://seq.example` and
`http://seq.example` are two.
-/
def originOf? (url : String) : Option String :=
  (endpoint? url).map fun e => s!"{e.scheme}://{e.host}:{e.port}"

/-- Whether two URLs name the same origin. A URL that will not parse names none. -/
def sameOrigin (a b : String) : Bool :=
  match originOf? a, originOf? b with
  | some x, some y => x == y
  | _, _ => false

/-! ## Sessions -/

/--
Wraps a raw endpoint in the challenge-and-sign handshake.

The token is kept in memory and nowhere else. It is worth one hour and nothing
after a restart, which is the sequencer's own view of it: sessions are not in
its database either.
-/
def sessioned (suite : CryptoSuite) (identity : Identity)
    (endpoint : Api.Req → IO Api.Reply) (dialled : Option String := none) : IO Transport := do
  let held ← IO.mkRef (none : Option String)
  let knownOrigin ← IO.mkRef (none : Option String)
  -- The one comparison the server is not a party to. `none` is the in-process
  -- transport, which dialled nothing: there is no socket, no relay and nothing
  -- to compare against.
  let against (route stated : String) : IO Unit := do
    let some base := dialled | pure ()
    unless sameOrigin stated base do
      throw <| IO.userError s!"this node dialled '{base}' and the server there says it is \
                              '{stated}' when it {route}; a sequencer that names an origin \
                              other than the one it was reached at is relaying somebody \
                              else's challenge, so nothing is signed and this session is \
                              abandoned"
  -- Asked once, because it is a property of the deployment rather than of a
  -- request, and a sequencer that changed its answer between the two routes is
  -- one this node declines to sign anything for.
  let originOf : IO String := do
    if let some o ← knownOrigin.get then return o
    let health ← endpoint (get ["health"])
    if health.code ≥ 400 then throw <| IO.userError (errorOf health)
    let o := Sync.strField? (payload health) "origin"
    against "is asked" o
    knownOrigin.set (some o)
    return o
  let login : IO String := do
    let expected ← originOf
    let challenged ← endpoint (send "POST" ["challenge"] (Json.mkObj [("key", identity.id)]))
    if challenged.code ≥ 400 then throw <| IO.userError (errorOf challenged)
    let stated := Sync.strField? (payload challenged) "origin"
    unless stated == expected do
      throw <| IO.userError s!"this sequencer calls itself '{expected}' when asked and \
                              '{stated}' when it hands out a challenge; this node will not \
                              sign for either"
    against "hands out a challenge" stated
    let nonce ← IO.ofExcept (Sync.strField (payload challenged) "nonce")
    let signature := Identity.signHex suite identity (Sync.challengeBytes nonce expected)
    let authenticated ← endpoint (send "POST" ["authenticate"]
      (Json.mkObj [("key", identity.id), ("signature", signature)]))
    if authenticated.code ≥ 400 then throw <| IO.userError (errorOf authenticated)
    -- The third statement of the origin, on the reply that carries the token.
    -- A relay that repeated the first two has to repeat this one as well, and
    -- it is checked against the same fixed point as the others.
    let issued := Sync.strField? (payload authenticated) "origin"
    unless issued.isEmpty do
      unless issued == expected do
        throw <| IO.userError s!"this sequencer handed out a token for origin '{issued}' \
                                after challenging for '{expected}'"
      against "hands out a token" issued
    let token ← IO.ofExcept (Sync.strField (payload authenticated) "token")
    held.set (some token)
    return token
  return fun r => do
    let token ← match ← held.get with
      | some t => pure t
      | none => login
    let reply ← endpoint (withToken r token)
    if reply.code == 401 then endpoint (withToken r (← login)) else return reply

/-! ## The two endpoints -/

/-- A sequencer running in this process: the route table, called directly. -/
def inProcess (suite : CryptoSuite) (identity : Identity) (node : Sync.Node) : IO Transport :=
  sessioned suite identity (Sync.handleSafe node)

/-! ## curl

Everything in this section is shared with `Cli/Client.lean`, which talks to the
ledger API the same way. The query encoder used to be copied into both, on the
grounds that `Node` must not depend on the command line — which is still true,
and is why the shared code lives here, below it, rather than there.
-/

/--
Percent-encodes one path segment or query value.

Only the unreserved characters survive. That is stricter than a URL needs and
deliberately so: a path segment is a *name*, and a name containing `/`, `?` or
`#` that reached the URL unencoded would be reshaping the request rather than
naming anything.
-/
def urlEncode (s : String) : String := Id.run do
  let hexDigits := "0123456789ABCDEF".toList.toArray
  let mut out := ""
  for b in s.toUTF8 do
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~' then
      out := out.push c
    else
      out := out.push '%' |>.push hexDigits[b.toNat / 16]! |>.push hexDigits[b.toNat % 16]!
  return out

/-- A path, percent-encoded segment by segment. -/
def urlPath (segments : List String) : String :=
  String.intercalate "/" (segments.map urlEncode)

/-- A query string, or the empty string when there is nothing to ask. -/
def urlQuery (query : List (String × String)) : String :=
  if query.isEmpty then ""
  else "?" ++ String.intercalate "&"
    (query.map fun (k, v) => urlEncode k ++ "=" ++ urlEncode v)

/-- One request made by shelling out to `curl`. -/
structure CurlCall where
  /-- The whole URL, already encoded. -/
  url : String
  /-- The HTTP method. -/
  method : String
  /-- Headers that are nobody's secret, passed in argv. -/
  headers : List (String × String) := []
  /-- A bearer token, passed in a file that only this user can read. -/
  token : Option String := none
  /-- The request body, if there is one. -/
  body : ByteArray := ByteArray.empty
  deriving Inhabited

/-- The longest a bearer token may be. -/
def tokenMaxLength : Nat := 512

/--
Whether a string is the shape a bearer token has.

The sequencer mints `seq_` and Crockford base32 (`Sync/Routes.lean`), and the
API's own tokens are hex, so this is wider than either. What it rules out is the
only thing that matters: a token is a credential, it travels through a file curl
reads as *directives*, and a quote, a newline or a backslash in one is somebody
writing options onto this machine rather than naming a session.
-/
def wellFormedToken (t : String) : Bool :=
  !t.isEmpty && t.length ≤ tokenMaxLength && t.all fun c =>
    c.isAlphanum || c == '.' || c == '_' || c == '-'

/--
One `key = "value"` line of a curl config file.

curl reads a quoted value with backslash escapes, so a `"` ends it and a `\\`
eats the character after it. Both are written as escapes here, which makes this
correct for any value — and it is still only ever handed values
`wellFormedToken` has already accepted, because a config file is not the place
to find out that a check was missing.
-/
def curlConfigLine (key value : String) : String :=
  let escaped := value.foldl
    (fun out c => if c == '"' || c == '\\' then (out.push '\\').push c else out.push c) ""
  s!"{key} = \"{escaped}\"\n"

/-- A directory in `$TMPDIR` that only this user may enter. -/
private def privateTempDir : IO System.FilePath := do
  let root : System.FilePath := ((← IO.getEnv "TMPDIR").getD "/tmp")
  let dir := root / s!"resources-{← freshId}"
  Files.privateDir dir
  return dir

/--
Runs one `curl` and hands back the status and the body.

The status arrives on the end of stdout, because `--write-out` writes there
after the transfer: three digits, always, so the body is everything before them.
That is what lets the response come back as bytes without a temporary file — and
without guessing, which a file with a content type nobody recorded would need.
-/
def curlFetch (c : CurlCall) : IO (Nat × ByteArray) := do
  let tmp ← privateTempDir
  try
    let mut args := #["-s", "-S", "--max-time", "60", "--no-location",
                      "--proto", (if loopbackUrl c.url then "=http,https" else "=https"),
                      "-X", c.method, "-w", "%{http_code}"]
    for (k, v) in c.headers do
      args := args ++ #["-H", k ++ ": " ++ v]
    if let some token := c.token then
      -- A header in argv is a header in `ps`, and this one is a credential. It
      -- is also a string the server chose, and this file is a list of options.
      unless wellFormedToken token do
        throw <| IO.userError s!"this is not a bearer token: 1 to {tokenMaxLength} characters \
                                 from [A-Za-z0-9._-], and what came back is not that, so it is \
                                 an instruction to curl rather than a credential"
      let rc := tmp / "curlrc"
      Files.writeSecret rc (curlConfigLine "header" s!"authorization: Bearer {token}")
      args := args ++ #["--config", rc.toString]
    if c.body.size > 0 then
      let bodyPath := tmp / "body"
      Files.writeSecretBin bodyPath c.body
      args := args ++ #["--data-binary", "@" ++ bodyPath.toString]
    -- `--` last, so that a base URL beginning with a dash is a URL.
    args := args ++ #["--", c.url]
    let child ← IO.Process.spawn
      { cmd := "curl", args, stdout := .piped, stderr := .piped }
    let out ← child.stdout.readBinToEnd
    let complaint ← child.stderr.readToEnd
    let exitCode ← child.wait
    if exitCode != 0 then
      throw <| IO.userError s!"curl failed: {complaint.trimAscii}"
    if out.size < 3 then
      throw <| IO.userError "curl came back without a status"
    let code := ((String.fromUTF8? (drop out (out.size - 3))).getD "").toNat?.getD 0
    return (code, take out (out.size - 3))
  finally
    IO.FS.removeDirAll tmp <|> pure ()

/-- Turns what `curl` handed back into a reply, reading JSON as JSON. -/
def curlReply (code : Nat) (bytes : ByteArray) : Api.Reply :=
  match String.fromUTF8? bytes with
  | some text =>
    match Json.parse text with
    | .ok j => .json code j
    | .error _ => .bytes code "text/plain" bytes
  | none => .bytes code "application/octet-stream" bytes

/-- One request over HTTP, through `curl`. -/
private def curlCall (base : String) (r : Api.Req) : IO Api.Reply := do
  let query := queryKeys.filterMap (fun k => (r.query k).map (fun v => (k, v)))
  let url := base ++ "/seq/v2/" ++ urlPath r.segments ++ urlQuery query
  let headers := ["content-type"].filterMap fun name =>
    (r.header name).map (fun v => (name, v))
  let token := (r.header "authorization").bind (Str.dropPrefix? · "Bearer ")
  let (code, bytes) ← curlFetch { url, method := r.method, headers, token, body := r.body }
  return curlReply code bytes

/-- A sequencer at a URL, over HTTP. -/
def overCurl (suite : CryptoSuite) (identity : Identity) (base : String) : IO Transport :=
  let url := (base.dropEndWhile (· == '/')).toString
  sessioned suite identity (curlCall url) (some url)

/--
The same endpoint without the handshake, for the routes that ask nothing of the
caller.

`GET health` is the only one, and it is the one `resources sync status` wants:
what a deployment says about itself — its origin, its schema and which verifier
it checks signatures with — is public, and asking for it should not need a
passphrase to sign a challenge with.
-/
def unauthenticated (base : String) : Transport :=
  curlCall (base.dropEndWhile (· == '/')).toString

end Transport

end Node
end Resources
