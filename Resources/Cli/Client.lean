import Resources.Node.Realms

/-!
# CLI backends

Two transports, one command surface. Local mode opens the database and calls the
same route table the server does, so there is no second implementation to drift.
Remote mode speaks HTTP with a bearer token — via `curl`, because `Std.Http`
ships a server but not yet a client. Everything goes through `Backend.call`, so
replacing `curl` with a native client later touches one function.

The `curl` invocation itself is `Node.Transport.curlFetch`, which is also what
the node talks to its sequencer with: the token travels in a config file this
user alone can read rather than in argv, the response comes back on stdout
rather than through a world-readable temporary file, path segments are
percent-encoded, `--` ends the options and a plaintext transfer to anywhere but
this machine is refused. `config.json` holds a bearer token in the clear, so it
is written 0600 like everything else that opens a ledger.
-/

open Lean

namespace Resources
namespace Cli

/-- CLI configuration, from `~/.config/resources/config.json` and the environment. -/
structure ClientConfig where
  /-- Base URL of a remote server; when absent the CLI works on the local database. -/
  server : Option String := none
  /-- Bearer token for the remote server. -/
  token : Option String := none
  /-- Overrides the local data directory. -/
  dataDir : Option String := none
  deriving Repr, Inhabited, ToJson, FromJson

namespace ClientConfig

/-- The path of the CLI configuration file. -/
def path : IO System.FilePath := do
  match ← IO.getEnv "XDG_CONFIG_HOME" with
  | some d => return System.FilePath.mk d / "resources" / "config.json"
  | none =>
    let home := (← IO.getEnv "HOME").getD "."
    return System.FilePath.mk home / ".config" / "resources" / "config.json"

/-- Loads the configuration, with environment variables taking precedence. -/
def load : IO ClientConfig := do
  let p ← path
  let base ←
    if ← p.pathExists then
      match Json.parse (← IO.FS.readFile p) >>= fromJson? (α := ClientConfig) with
      | .ok c => pure c
      | .error e => do IO.eprintln s!"warning: bad config {p}: {e}"; pure {}
    else pure {}
  return { server := (← IO.getEnv "RESOURCES_SERVER") <|> base.server
           token := (← IO.getEnv "RESOURCES_TOKEN") <|> base.token
           dataDir := (← IO.getEnv "RESOURCES_DIR") <|> base.dataDir }

/-- Writes the configuration file, mode 0600: it holds a bearer token in the clear. -/
def save (c : ClientConfig) : IO Unit := do
  Files.writeSecret (← path) ((toJson c).pretty ++ "\n")

end ClientConfig

/-- One API call, in a transport-independent shape. -/
structure Call where
  method : String
  path : List String
  query : List (String × String) := []
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
  deriving Inhabited

namespace Call

/-- A GET. -/
def get (path : List String) (query : List (String × String) := []) : Call :=
  { method := "GET", path, query }

/-- A POST with a JSON body. -/
def post (path : List String) (j : Json) : Call :=
  { method := "POST", path, body := j.compress.toUTF8,
    headers := [("content-type", "application/json")] }

/-- A PATCH with a JSON body. -/
def patch (path : List String) (j : Json) : Call :=
  { method := "PATCH", path, body := j.compress.toUTF8,
    headers := [("content-type", "application/json")] }

/--
A DELETE.

It carries the JSON content type with no body, because the route table asks for
it on everything that changes something — see `Api.mutating`. A `DELETE` from a
browser is preflighted anyway; saying so here is what keeps the local backend and
the remote one one command surface rather than two.
-/
def delete (path : List String) : Call :=
  { method := "DELETE", path, headers := [("content-type", "application/json")] }

end Call

/-- Where CLI commands send their requests. -/
inductive Backend
  /-- Straight to the database: the same route table the server runs. -/
  | direct (ctx : Ctx)
  /-- Over HTTP to a running server. -/
  | remote (base : String) (token : Option String)

namespace Backend

/-- Opens the backend the configuration selects. -/
def open? (cfg : ClientConfig) : IO Backend := do
  match cfg.server with
  | some base => return .remote (base.dropEndWhile (· == '/')).toString cfg.token
  | none =>
    let storeCfg ←
      match cfg.dataDir with
      | some d => pure (Config.atDir (System.FilePath.mk d))
      | none => Config.default
    return .direct (← Ctx.open storeCfg)

/-- A one-line description, for `resources status`. -/
def describe : Backend → String
  | .direct ctx => s!"local {ctx.cfg.dbPath}"
  | .remote base _ => s!"remote {base}"

private def remoteCall (base : String) (token : Option String) (c : Call) : IO Api.Reply := do
  let url := base ++ "/api/v1/" ++ Node.Transport.urlPath c.path
    ++ Node.Transport.urlQuery c.query
  let (code, bytes) ← Node.Transport.curlFetch
    { url, method := c.method, headers := c.headers, token, body := c.body }
  return Node.Transport.curlReply code bytes

/-- Runs a call against this backend. -/
def call (b : Backend) (c : Call) : IO Api.Reply := do
  match b with
  | .direct ctx =>
    let caller ←
      if ← Tokens.any ctx then
        pure { actor := "cli", scopes := Scopes.ofList [.read, .write, .import, .admin]
               : Api.Caller }
      else pure Api.bootstrapCaller
    let r : Api.Req :=
      { method := c.method, segments := c.path, body := c.body
        query := fun k => (c.query.find? (·.1 == k)).map (·.2)
        header := fun k => (c.headers.find? (·.1.toLower == k.toLower)).map (·.2) }
    -- A direct backend *is* the node, so it hands the routes the node's own
    -- keys and sequencer rather than the do-nothing defaults.
    Api.handleSafe ctx caller r Node.Realms.api
  | .remote base token => remoteCall base token c

/-- Runs a call and returns its JSON, raising the API's own error message on failure. -/
def json (b : Backend) (c : Call) : IO Json := do
  match ← b.call c with
  | .json code payload =>
    if code ≥ 400 then
      let msg := (payload.getObjValAs? String "error").toOption.getD payload.compress
      throw <| IO.userError msg
    else return payload
  | .bytes code _ data _ =>
    if code ≥ 400 then
      throw <| IO.userError ((String.fromUTF8? data).getD s!"request failed with status {code}")
    else return Json.mkObj [("bytes", Json.num (JsonNumber.fromNat data.size))]

/-- Runs a call and returns its raw bytes. -/
def bytes (b : Backend) (c : Call) : IO ByteArray := do
  match ← b.call c with
  | .bytes code _ data _ =>
    if code ≥ 400 then
      throw <| IO.userError ((String.fromUTF8? data).getD s!"request failed with status {code}")
    else return data
  | .json code payload =>
    if code ≥ 400 then
      throw <| IO.userError ((payload.getObjValAs? String "error").toOption.getD payload.compress)
    else return payload.compress.toUTF8

end Backend

end Cli
end Resources
