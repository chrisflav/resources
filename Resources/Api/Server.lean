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
  /-- Send permissive CORS headers, for running the Vite dev server separately. -/
  cors : Bool := true
  deriving Repr, Inhabited

/-- A response builder for a status code. -/
private def builderFor : Nat → Response.Builder
  | 200 => Response.ok
  | 201 => Response.created
  | 400 => Response.badRequest
  | 401 => Response.unauthorized
  | 403 => Response.forbidden
  | 404 => Response.notFound
  | 409 => Response.conflict
  | _ => Response.internalServerError

/-- Builds an HTTP response with an explicit content type and body. -/
private def build (cfg : ServerConfig) (code : Nat) (contentType : String) (bytes : ByteArray)
    (extra : List (String × String)) : Async (Response Body.Any) := do
  let mut b := (builderFor code).header! "content-type" contentType
  if cfg.cors then
    b := b.header! "access-control-allow-origin" "*"
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

/-- The uppercase name of a method, as `Routes` expects it. -/
private def methodName (m : Method) : String :=
  match m with
  | .get => "GET" | .post => "POST" | .put => "PUT" | .delete => "DELETE"
  | .patch => "PATCH" | .head => "HEAD" | .options => "OPTIONS"
  | _ => toString m

/-- Serves a file from the web root, falling back to `index.html` for client-side routes. -/
private def serveStatic (cfg : ServerConfig) (segs : List String) :
    Async (Option (Response Body.Any)) := do
  let some root := cfg.webRoot | return none
  let rel := if segs.isEmpty then "index.html" else String.intercalate "/" segs
  if (rel.splitOn "..").length > 1 then return none
  let direct := root / rel
  let path := if ← direct.pathExists then direct else root / "index.html"
  if !(← path.pathExists) then return none
  let bytes ← IO.FS.readBinFile path
  return some (← toResponse cfg (.bytes 200 (Blobs.mimeOfExtension path.toString) bytes))

/-- Routes one request. -/
def dispatch (ctx : Ctx) (cfg : ServerConfig) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let segs := pathSegments req
  let method := methodName req.line.method
  if method == "OPTIONS" then
    return ← toResponse cfg (.bytes 200 "text/plain" ByteArray.empty)
  match segs with
  | "api" :: "v1" :: rest =>
    -- A presented token is always the caller it names, whatever else is true of
    -- the store. Deciding that first is what keeps a share link narrow: reading
    -- the open-by-default rule earlier would hand its holder the bootstrap
    -- caller, which is the opposite of what the link is for.
    --
    -- Openness is then only about a request that presents nothing. With no
    -- token of your own the API is open, so the tool works out of the box on
    -- loopback, and the first `token create` locks it down. Share links do not
    -- count towards that: inviting somebody to one budget is not the moment you
    -- said you were ready to authenticate, and treating it as one would lock
    -- you out of your own client as a side effect of inviting a friend.
    let caller : Option Caller ←
      match (headerValue req "authorization").bind (fun a => Str.dropPrefix? a "Bearer ") with
      | some secret =>
        match ← Tokens.verify ctx secret (← Date.today) with
        | none => pure none
        | some t => pure (some { actor := t.id.val, scopes := t.scopes, guest := t.guest })
      | none =>
        if !(← Tokens.anyOwn ctx) then pure (some bootstrapCaller) else pure none
    let some caller := caller
      | return ← errRes cfg 401 "missing or invalid bearer token"
    let body ← req.body.readAll (α := ByteArray) (maximumSize := some (64 * 1024 * 1024))
    let r : Req :=
      { method, segments := rest, body
        query := fun k => (req.line.uri.query.find? k).join.bind (fun v => v.decode)
        header := fun k => headerValue req k }
    toResponse cfg (← handleSafe ctx caller r)
  | _ =>
    match ← serveStatic cfg segs with
    | some r => return r
    | none => errRes cfg 404 "not found"

/-- Starts the server and blocks until it shuts down. -/
def serve (ctx : Ctx) (cfg : ServerConfig) : IO Unit := do
  let locked ← Tokens.anyOwn ctx
  IO.println s!"resources api on http://{cfg.host}:{cfg.port}"
  IO.println s!"  database  {ctx.cfg.dbPath}"
  match cfg.webRoot with
  | some w => IO.println s!"  web root  {w}"
  | none => pure ()
  if locked then
    IO.println "  auth      bearer tokens required"
  else
    IO.println
      "  auth      OPEN - no token of your own exists yet; 'resources token create' locks it down"
  if cfg.host != "127.0.0.1" && cfg.host != "localhost" then
    IO.eprintln "warning: binding beyond loopback without TLS; put a reverse proxy in front"
  (← IO.getStdout).flush
  let some addr := Net.IPv4Addr.ofString cfg.host
    | throw <| IO.userError s!"not an IPv4 address: {cfg.host}"
  let handler := Server.Handler.ofFns
    (onRequest := fun req => dispatch ctx cfg req)
    (onFailure := fun e => do IO.eprintln s!"connection error: {e}")
  Async.block do
    let server ← Server.serve (.v4 { addr, port := cfg.port }) handler
    server.waitShutdown

end Api
end Resources
