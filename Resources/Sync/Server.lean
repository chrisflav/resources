import Std.Http
import Resources.Sync.Routes

/-!
# Sequencer transport

The only file in the sequencer that mentions `Std.Http`, mirroring
`Resources.Api.Server`: every route lives in `Resources.Sync.Routes`, which knows
nothing about sockets, so when the young HTTP API moves this is the one file that
has to follow it.

There is no TLS here either, so the default bind address is loopback. That is a
weaker constraint than it is for the ledger API — the sequencer only ever sees
ciphertext — but a session token is still a bearer token, and handing one to
whoever is on the path is not made harmless by the payloads being opaque.

With `--web` it also serves the thin client: everything that is not `/seq/v2` is
a static file, or `index.html` for the paths the client routes on itself. One
origin for the API and the client it talks to is what makes an invite link a
single URL, and it is why cross-origin access is off unless somebody names an
origin: a browser that is served the client from here never needs it.

## What the transport decides

Three things, and they are all refusals:

* how many bytes a route will read, before it reads them, so that the expensive
  work — base64, SHA-256, the JSON parser — is never reached by a body nobody
  agreed to;
* which static paths exist at all, by a rule about segments rather than a scan
  for `..`;
* which headers every response carries, so that a browser is told what this
  origin may do before it is told anything else.
-/

open Lean Std Std.Async Std.Http

namespace Resources
namespace Sync

/-- Runtime options for the sequencer server. -/
structure ServerConfig where
  /-- Address to bind to. -/
  host : String := "127.0.0.1"
  /-- Port to listen on. -/
  port : UInt16 := 8088
  /-- Directory of built thin-client assets to serve at `/`. -/
  webRoot : Option System.FilePath := none
  /--
  The one origin allowed to call this sequencer from a browser, if any.

  `none` — the default — sends no CORS headers at all, which is right for the
  deployment the thin client is served from: same origin, nothing to allow.
  -/
  cors : Option String := none
  deriving Repr, Inhabited

/--
The headers every response carries.

They are on the API replies as well as the static files, because a 401 with a
JSON body is still something a browser can be made to fetch, and because the
cheapest way to be sure the client's own page is covered is to cover everything.
-/
def securityHeaders : List (String × String) :=
  [("x-content-type-options", "nosniff"),
   ("referrer-policy", "no-referrer"),
   ("content-security-policy",
     "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; connect-src 'self'; \
      img-src 'self' blob: data:; style-src 'self' 'unsafe-inline'; frame-ancestors 'none'; \
      base-uri 'none'; object-src 'none'; form-action 'self'")]

/-- A response builder for a status code. -/
private def builderFor : Nat → Response.Builder
  | 200 => Response.ok
  | 201 => Response.created
  | 400 => Response.badRequest
  | 401 => Response.unauthorized
  | 403 => Response.forbidden
  | 404 => Response.notFound
  | 409 => Response.conflict
  | 410 => Response.withStatus .gone
  | 413 => Response.withStatus .payloadTooLarge
  | 429 => Response.withStatus .tooManyRequests
  | 507 => Response.withStatus .insufficientStorage
  | _ => Response.internalServerError

/-- Builds an HTTP response with an explicit content type and body. -/
private def build (cfg : ServerConfig) (code : Nat) (contentType : String) (bytes : ByteArray)
    (extra : List (String × String)) : Async (Response Body.Any) := do
  let mut b := (builderFor code).header! "content-type" contentType
  for (k, v) in securityHeaders do
    b := b.header! k v
  if let some origin := cfg.cors then
    b := b.header! "access-control-allow-origin" origin
    b := b.header! "vary" "origin"
    b := b.header! "access-control-allow-headers" "authorization, content-type"
    b := b.header! "access-control-allow-methods" "GET, POST, PUT, DELETE, OPTIONS"
  for (k, v) in extra do
    b := b.header! k v
  let r ← b.fromBytes bytes
  return (r : Response Body.Any)

/-- Turns a route's `Api.Reply` into an HTTP response. -/
private def toResponse (cfg : ServerConfig) : Api.Reply → Async (Response Body.Any)
  | .json code payload =>
    build cfg code "application/json; charset=utf-8" payload.compress.toUTF8 []
  | .bytes code ct data extra => build cfg code ct data extra

/-- A JSON error response built without going through the route table. -/
private def errRes (cfg : ServerConfig) (code : Nat) (msg : String) :
    Async (Response Body.Any) :=
  toResponse cfg (.json code (Json.mkObj [("error", msg)]))

/-- The decoded, non-empty path segments of a request. -/
private def pathSegments (req : Request Body.Stream) : List String :=
  (req.line.uri.path.segments.toList.filterMap (fun s => s.decode)).filter (fun s => !s.isEmpty)

/-- One header's value, by name. -/
private def headerValue (req : Request Body.Stream) (name : String) : Option String := do
  let n ← Header.Name.ofString? name
  let v ← req.line.headers.get? n
  return v.value

/--
Where the connection this request arrived on comes from.

`Std.Http` attaches the peer's socket address to every request it hands over, so
this is the one fact about a caller that no header of theirs can change: a
`Host: localhost` from the other side of the world is still a remote socket.
What depends on it is the refusal a sequencer built for a test makes: it answers
nobody it cannot place inside this machine.

A request that arrived over a socket whose peer `Std.Http` did not state is
`unknown`, which is *not* `inProcess` and is refused with `remote`. Nothing
reaching this function is in-process — that answer belongs to a caller who
never went near a socket, and it says so by calling `handleSafe` directly.
-/
private def peerOf (req : Request Body.Stream) : Sync.Peer :=
  match req.extensions.get Server.RemoteAddr with
  | none => .unknown
  | some peer =>
    match peer.addr with
    | .v4 a => if a.addr.octets[0]! == 127 then .loopback else .remote
    | .v6 a =>
      let s := a.addr.segments
      -- `::1`, and the IPv4-mapped form `::ffff:127.0.0.0/8` that a dual-stack
      -- listener reports a loopback IPv4 connection as.
      if s[0]! == 0 && s[1]! == 0 && s[2]! == 0 && s[3]! == 0 && s[4]! == 0
          && s[5]! == 0 && s[6]! == 0 && s[7]! == 1 then .loopback
      else if s[0]! == 0 && s[1]! == 0 && s[2]! == 0 && s[3]! == 0 && s[4]! == 0
          && s[5]! == 0xffff && s[6]! >>> 8 == 127 then .loopback
      else .remote

/-- The uppercase name of a method, as `Routes` expects it. -/
private def methodName (m : Method) : String :=
  match m with
  | .get => "GET" | .post => "POST" | .put => "PUT" | .delete => "DELETE"
  | .patch => "PATCH" | .head => "HEAD" | .options => "OPTIONS"
  | _ => toString m

/--
The path below the web root a request names, or `none` if it names none.

The rule is about segments, not about the string: a segment has to be non-empty
and has to be something other than `.` or `..`, and it may not contain a
separator of either kind. Segments arrive percent-decoded, which is why the
separator check matters — `%2f` and `%5c` are exactly how a climb out of the
root is spelled once decoding is done for you — and it is why the check is on
what decoding produced rather than on what arrived.

No segments at all is the client's index.
-/
def safeRelPath (segs : List String) : Option String :=
  if segs.isEmpty then some "index.html"
  else if segs.any (fun s =>
      s.isEmpty || s == "." || s == ".." || s.contains '/' || s.contains '\\') then none
  else some (String.intercalate "/" segs)

/--
Serves a file from the web root, falling back to `index.html` for client-side
routes, as `Resources.Api.Server` does.

The fallback is what makes `/join/#…` work: an invite link is a path the client
routes on and the server has never heard of, so anything that is not a file and
not `/seq/v2` is answered with the client itself.

`safeRelPath` decides which paths exist; this then resolves what it built and
checks that the answer is still inside the root, so that a symlink planted in a
directory of built assets cannot lead out of one either.
-/
private def serveStatic (cfg : ServerConfig) (segs : List String) :
    Async (Option (Response Body.Any)) := do
  let some root := cfg.webRoot | return none
  let some rel := safeRelPath segs | return none
  let direct := root / rel
  let hit ← direct.pathExists
  let path := if hit then direct else root / "index.html"
  if !(← path.pathExists) then return none
  let realRoot := (← IO.FS.realPath root).toString
  let realPath := (← IO.FS.realPath path).toString
  if !(realPath == realRoot || realPath.startsWith (realRoot ++ "/")) then return none
  let bytes ← IO.FS.readBinFile path
  -- Vite names a built asset after the hash of its contents, so the file at one
  -- of those names can never change. Everything else — `index.html` above all,
  -- which is what names the current assets — is left to revalidate.
  let extra :=
    if hit && segs.head? == some "assets" then
      [("cache-control", "public, max-age=31536000, immutable")]
    else []
  return some (← toResponse cfg
    (.bytes 200 (Blobs.mimeOfExtension path.toString) bytes extra))

/-- Routes one request. -/
def dispatch (node : Node) (cfg : ServerConfig) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let segs := pathSegments req
  let method := methodName req.line.method
  if method == "OPTIONS" then
    return ← toResponse cfg (.bytes 200 "text/plain" ByteArray.empty)
  match segs with
  | "seq" :: "v2" :: rest =>
    -- Authentication is not done here. The session token names a public key, and
    -- which key a caller is turns out to be the only thing the routes need, so
    -- there is nothing for the transport to decide.
    --
    -- The cap is, though: it is read off the route before a byte is taken, so
    -- that a stranger's `challenge` can never cost more than four kilobytes of
    -- anything.
    let cap := bodyLimit method rest
    let body ←
      try
        req.body.readAll (α := ByteArray) (maximumSize := some cap.toUInt64)
      catch _ =>
        return ← errRes cfg 413 "the body is larger than this route accepts"
    let r : Api.Req :=
      { method, segments := rest, body
        query := fun k => (req.line.uri.query.find? k).join.bind (fun v => v.decode)
        header := fun k => headerValue req k }
    toResponse cfg (← handleSafe node r (peerOf req))
  | _ =>
    match ← serveStatic cfg segs with
    | some res => return res
    | none => errRes cfg 404 "not found"

/-- Starts the sequencer and blocks until it shuts down. -/
def serve (node : Node) (cfg : ServerConfig) : IO Unit := do
  IO.println s!"resources sequencer on http://{cfg.host}:{cfg.port}/seq/v2"
  IO.println s!"  database  {node.log.cfg.dbPath}"
  IO.println s!"  origin    {node.origin}"
  IO.println s!"  verifier  {node.verifier.name}"
  IO.println s!"  limits    {node.limits.burst} writes, refilling {node.limits.perSecond}/s, \
                  {node.limits.blobBurst} blobs at {node.limits.blobPerSecond}/s"
  match node.creators with
  | some cs => IO.println s!"  creators  {cs.size} key(s) may make a ledger"
  | none => IO.println "  creators  unrestricted"
  match cfg.webRoot with
  | some w => IO.println s!"  web root  {w}"
  | none => pure ()
  if cfg.host != "127.0.0.1" && cfg.host != "localhost" then
    IO.eprintln "warning: binding beyond loopback without TLS; put a reverse proxy in front"
  (← IO.getStdout).flush
  let some addr := Net.IPv4Addr.ofString cfg.host
    | throw <| IO.userError s!"not an IPv4 address: {cfg.host}"
  let handler := Server.Handler.ofFns
    (onRequest := fun req => dispatch node cfg req)
    (onFailure := fun e => do IO.eprintln s!"connection error: {e}")
  Async.block do
    let server ← Server.serve (.v4 { addr, port := cfg.port }) handler
    server.waitShutdown

end Sync
end Resources
