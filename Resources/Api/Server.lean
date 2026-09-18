import Std.Http
import Resources.Api.Routes

/-!
# HTTP transport

The only file in the system that mentions `Std.Http`. The server landed in Lean
4.31 and is still young, so when its API moves this is the only file that has to
change; every route lives in `Resources.Api.Routes`, which knows nothing about
sockets and is shared with the CLI's local mode.

There is no TLS anywhere in the Lean stack, so the default bind address is
loopback and widening it has to be asked for.

## What the transport decides

Four refusals, and they are the same four `Resources.Sync.Server` makes, because
the two servers face the same browser:

* how many bytes a route will read, before it reads them, so that the parser, the
  hash and the base64 are never reached by a body nobody agreed to. The number is
  `Api.bodyLimit`'s, and `Api.Routes.handle` checks it a second time for the CLI,
  which reaches the same table without a socket;
* cross-origin access is off unless somebody names an origin. `*` was the
  default, and `*` on an API that grants every scope to a request carrying no
  credentials means any page the user visits can read the ledger and mint an
  invite — which is the end-to-end encryption defeated from a drive-by page.
* the open-by-default caller applies only to a request that arrived on a
  loopback socket *and* whose `Host` header names this machine. The two rules
  close opposite directions and neither implies the other: the socket is what a
  remote caller typing `Host: localhost` cannot forge, and the header is what a
  rebound page in a browser — whose connection really is from 127.0.0.1 —
  cannot help sending wrong.
* which static paths exist at all, by a rule about segments rather than a scan
  for `..`. Segments arrive percent-decoded, so `%2f` is a slash and an absolute
  path joined onto the root replaces it: the old rule read any file on the disk.

`safeRelPath`, the header list and the resolved-path check are `Sync/Server.lean`'s,
copied rather than imported. They cannot be shared: the sequencer's route table
is written over this file's `Api.Req`, so `Sync` sits above `Api` and an import
the other way round would be a cycle. Two copies of eleven lines is the price of
that layering; if one of them changes, change both.
-/

open Lean Std Std.Async Std.Http

namespace Resources
namespace Api

/-- Runtime options for the server. -/
structure ServerConfig where
  host : String := "127.0.0.1"
  port : UInt16 := 8087
  /-- Directory of built web-client assets to serve at `/`. -/
  webRoot : Option System.FilePath := none
  /--
  The one origin allowed to call this API from a browser, if any.

  `none` — the default — sends no cross-origin headers at all, which is right
  for the deployment the web client is served from: same origin, nothing to
  allow. `--cors http://localhost:5173` is for running the Vite dev server
  beside it, and names that one origin rather than all of them.
  -/
  cors : Option String := none
  deriving Repr, Inhabited

/--
The headers every response carries.

They are on the API replies as well as the static files, because a 401 with a
JSON body is still something a browser can be made to fetch, and the cheapest
way to be sure the client's own page is covered is to cover everything.
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
  | 413 => Response.withStatus .payloadTooLarge
  | 415 => Response.withStatus .unsupportedMediaType
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
    b := b.header! "access-control-allow-headers"
           "authorization, content-type, x-profile, x-account, x-filename"
    b := b.header! "access-control-allow-methods" "GET, POST, PATCH, PUT, DELETE, OPTIONS"
  for (k, v) in extra do
    b := b.header! k v
  let r ← b.fromBytes bytes
  return (r : Response Body.Any)

/-- Turns a route's `Reply` into an HTTP response. -/
private def toResponse (cfg : ServerConfig) : Reply → Async (Response Body.Any)
  | .json code payload =>
    build cfg code "application/json; charset=utf-8" payload.compress.toUTF8 []
  | .bytes code ct data extra => build cfg code ct data extra

private def errRes (cfg : ServerConfig) (code : Nat) (msg : String) : Async (Response Body.Any) :=
  toResponse cfg (.json code (Json.mkObj [("error", msg)]))

/-- The decoded, non-empty path segments of a request. -/
private def pathSegments (req : Request Body.Stream) : List String :=
  (req.line.uri.path.segments.toList.filterMap (fun s => s.decode)).filter (fun s => !s.isEmpty)

private def headerValue (req : Request Body.Stream) (name : String) : Option String := do
  let n ← Header.Name.ofString? name
  let v ← req.line.headers.get? n
  return v.value

/--
Whether a socket address is one on this machine.

`127.0.0.0/8`, `::1`, and the IPv4-mapped form `::ffff:127.0.0.0/8` that a
dual-stack listener reports a loopback IPv4 connection as. The same rule as
`Sync.Server.peerOf`, and the same reason it is a second copy rather than an
import: `Sync` sits above `Api`, so the import would be a cycle.
-/
def loopbackAddress : Net.SocketAddress → Bool
  | .v4 a => a.addr.octets[0]! == 127
  | .v6 a =>
    let s := a.addr.segments
    (s[0]! == 0 && s[1]! == 0 && s[2]! == 0 && s[3]! == 0 && s[4]! == 0
      && s[5]! == 0 && s[6]! == 0 && s[7]! == 1)
    || (s[0]! == 0 && s[1]! == 0 && s[2]! == 0 && s[3]! == 0 && s[4]! == 0
      && s[5]! == 0xffff && s[6]! >>> 8 == 127)

/--
Whether a request arrived on a connection from this machine.

`Std.Http` attaches the peer's socket address to every request it hands over,
which makes this the one fact about a caller that no header of theirs can
change. It decides whether the API is open before a token has been minted.

A peer the transport could not name is *not* here. There is no address to look
at, so there is nothing that came from this machine, and the answer to this
question hands out `read,write,import,admin`: the only safe reading of "I could
not tell" is "somebody else".
-/
def loopbackPeer? (addr : Option Net.SocketAddress) : Bool :=
  match addr with
  | none => false
  | some a => loopbackAddress a

/-- The same question, of a request. -/
private def loopbackPeer (req : Request Body.Stream) : Bool :=
  loopbackPeer? ((req.extensions.get Server.RemoteAddr).map (·.addr))

/-- The uppercase name of a method, as `Routes` expects it. -/
private def methodName (m : Method) : String :=
  match m with
  | .get => "GET" | .post => "POST" | .put => "PUT" | .delete => "DELETE"
  | .patch => "PATCH" | .head => "HEAD" | .options => "OPTIONS"
  | _ => toString m

/--
The path below the web root a request names, or `none` if it names none.

The same rule as `Sync.safeRelPath`, and the comment there is the one that
matters: the check is on segments rather than on the joined string, because
segments arrive percent-decoded and `%2f` and `%5c` are exactly how a climb out
of the root is spelled once decoding has been done for you. An absolute segment
is worse still — `FilePath.join` drops the root when what it is joined with is
absolute — and a segment containing a separator is the only way to write one.
-/
def safeRelPath (segs : List String) : Option String :=
  if segs.isEmpty then some "index.html"
  else if segs.any (fun s =>
      s.isEmpty || s == "." || s == ".." || s.contains '/' || s.contains '\\') then none
  else some (String.intercalate "/" segs)

/--
Serves a file from the web root, falling back to `index.html` for client-side
routes.

`safeRelPath` decides which paths exist; this then resolves what it built and
checks the answer is still inside the root, so that a symlink planted in a
directory of built assets cannot lead out of one either.
-/
private def serveStatic (cfg : ServerConfig) (segs : List String) :
    Async (Option (Response Body.Any)) := do
  let some root := cfg.webRoot | return none
  let some rel := safeRelPath segs | return none
  let direct := root / rel
  let path := if ← direct.pathExists then direct else root / "index.html"
  if !(← path.pathExists) then return none
  let realRoot := (← IO.FS.realPath root).toString
  let realPath := (← IO.FS.realPath path).toString
  if !(realPath == realRoot || realPath.startsWith (realRoot ++ "/")) then return none
  let bytes ← IO.FS.readBinFile path
  return some (← toResponse cfg (.bytes 200 (Blobs.mimeOfExtension path.toString) bytes))

/-- Routes one request. -/
def dispatch (ctx : Ctx) (cfg : ServerConfig) (node : NodeApi) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let segs := pathSegments req
  let method := methodName req.line.method
  if method == "OPTIONS" then
    return ← toResponse cfg (.bytes 200 "text/plain" ByteArray.empty)
  match segs with
  | "api" :: "v1" :: rest =>
    -- A presented token is always the caller it names, whatever else is true of
    -- the store. Openness is only ever about a request that presents nothing:
    -- with no tokens at all the API is open, so the tool works out of the box on
    -- loopback, and the first `token create` locks it down.
    let caller : Option Caller ←
      match (headerValue req "authorization").bind bearerToken? with
      | some secret =>
        match ← Tokens.verify ctx secret (← Date.today) with
        | none => pure none
        | some t => pure (some { actor := t.id.val, scopes := t.scopes })
      | none =>
        -- Openness is only ever about a request that presents nothing, and
        -- only while it came from this machine. Two questions, because the
        -- attacks come from opposite sides: the socket says a remote caller is
        -- remote however they address the request, and the `Host` header says a
        -- page rebound onto 127.0.0.1 is a browser and not a person at a
        -- terminal. Neither answer covers the other, so both are required.
        let here := loopbackPeer req && loopbackHost ((headerValue req "host").getD "")
        if here && !(← Tokens.any ctx) then pure (some bootstrapCaller) else pure none
    let some caller := caller
      | return ← errRes cfg 401 "missing or invalid bearer token"
    -- The cap comes off the route before a byte is taken, exactly as the
    -- sequencer's does: one number for every path that is not a file upload, so
    -- that a request nobody has authorised cannot cost more than the JSON it
    -- claims to be.
    let body ←
      try
        req.body.readAll (α := ByteArray) (maximumSize := some (bodyLimit method rest).toUInt64)
      catch _ =>
        return ← errRes cfg 413 "the body is larger than this route accepts"
    let r : Req :=
      { method, segments := rest, body
        query := fun k => (req.line.uri.query.find? k).join.bind (fun v => v.decode)
        header := fun k => headerValue req k }
    toResponse cfg (← handleSafe ctx caller r node)
  | _ =>
    match ← serveStatic cfg segs with
    | some r => return r
    | none => errRes cfg 404 "not found"

/-- Starts the server and blocks until it shuts down. -/
def serve (ctx : Ctx) (cfg : ServerConfig) (node : NodeApi := {}) : IO Unit := do
  let locked ← Tokens.any ctx
  IO.println s!"resources api on http://{cfg.host}:{cfg.port}"
  IO.println s!"  database  {ctx.cfg.dbPath}"
  match cfg.webRoot with
  | some w => IO.println s!"  web root  {w}"
  | none => pure ()
  match cfg.cors with
  | some origin => IO.println s!"  cors      {origin}"
  | none => pure ()
  if locked then
    IO.println "  auth      bearer tokens required"
  else
    IO.println
      "  auth      OPEN on loopback - no token exists yet; 'resources token create' locks it \
       down"
  if cfg.host != "127.0.0.1" && cfg.host != "localhost" then
    IO.eprintln "warning: binding beyond loopback without TLS; put a reverse proxy in front"
    unless locked do
      IO.eprintln "warning: no token exists yet, so every request from off this machine is \
                   refused until 'resources token create' mints one"
  (← IO.getStdout).flush
  let some addr := Net.IPv4Addr.ofString cfg.host
    | throw <| IO.userError s!"not an IPv4 address: {cfg.host}"
  let handler := Server.Handler.ofFns
    (onRequest := fun req => dispatch ctx cfg node req)
    (onFailure := fun e => do IO.eprintln s!"connection error: {e}")
  Async.block do
    let server ← Server.serve (.v4 { addr, port := cfg.port }) handler
    server.waitShutdown

end Api
end Resources
