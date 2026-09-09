import Resources.Api.Routes

/-!
# CLI backends

Two transports, one command surface. Local mode opens the database and calls the
same route table the server does, so there is no second implementation to drift.
Remote mode speaks HTTP with a bearer token — via `curl`, because `Std.Http`
ships a server but not yet a client. Everything goes through `Backend.call`, so
replacing `curl` with a native client later touches one function.
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

/-- Writes the configuration file. -/
def save (c : ClientConfig) : IO Unit := do
  let p ← path
  IO.FS.createDirAll (p.parent.getD ".")
  IO.FS.writeFile p ((toJson c).pretty ++ "\n")

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

/-- A DELETE. -/
def delete (path : List String) : Call := { method := "DELETE", path }

end Call

/-- Percent-encodes a query value. -/
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
  let query :=
    if c.query.isEmpty then ""
    else "?" ++ String.intercalate "&"
      (c.query.map fun (k, v) => urlEncode k ++ "=" ++ urlEncode v)
  let url := base ++ "/api/v1/" ++ String.intercalate "/" c.path ++ query
  let tmpRoot : System.FilePath := ((← IO.getEnv "TMPDIR").getD "/tmp")
  let nonce ← freshId
  let outPath := tmpRoot / s!"resources-out-{nonce}"
  let bodyPath := tmpRoot / s!"resources-body-{nonce}"
  let hasBody := c.body.size > 0
  if hasBody then IO.FS.writeBinFile bodyPath c.body
  let mut args := #["-s", "-S", "-X", c.method, "-o", outPath.toString, "-w", "%{http_code}"]
  for (k, v) in c.headers do
    args := args ++ #["-H", k ++ ": " ++ v]
  match token with
  | some t => args := args ++ #["-H", "authorization: Bearer " ++ t]
  | none => pure ()
  if hasBody then
    args := args ++ #["--data-binary", "@" ++ bodyPath.toString]
  args := args.push url
  try
    let res ← IO.Process.output { cmd := "curl", args }
    if res.exitCode != 0 then
      throw <| IO.userError s!"curl failed: {res.stderr}"
    let code := (res.stdout.trimAscii.toString.toNat?).getD 0
    let bytes ← IO.FS.readBinFile outPath
    match String.fromUTF8? bytes with
    | some text =>
      match Json.parse text with
      | .ok j => return .json code j
      | .error _ => return .bytes code "text/plain" bytes
    | none => return .bytes code "application/octet-stream" bytes
  finally
    if ← outPath.pathExists then IO.FS.removeFile outPath
    if ← bodyPath.pathExists then IO.FS.removeFile bodyPath

/-- Runs a call against this backend. -/
def call (b : Backend) (c : Call) : IO Api.Reply := do
  match b with
  | .direct ctx =>
    let caller ←
      if ← Tokens.anyOwn ctx then
        pure { actor := "cli", scopes := Scopes.ofList [.read, .write, .import, .admin]
               : Api.Caller }
      else pure Api.bootstrapCaller
    let r : Api.Req :=
      { method := c.method, segments := c.path, body := c.body
        query := fun k => (c.query.find? (·.1 == k)).map (·.2)
        header := fun k => (c.headers.find? (·.1.toLower == k.toLower)).map (·.2) }
    Api.handleSafe ctx caller r
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
