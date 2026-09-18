import Resources.Store.Repo

/-!
# API tokens

The database stores only `sha256(token)`, compared in constant time. The
plaintext is shown once at creation and never again. Scopes are a bitset checked
in the router before dispatch; the token's id is the actor recorded on every
revision.

A token once had a second job: a *share link*, one person on one budget,
dispatched to a route table of its own. Sharing is a realm now — an invite that
makes somebody a member with a key of their own — so a token is only ever a
caller's own credential again. The `owner_id` and `budget_id` columns are still
on the table and nothing reads them; dropping a column is a migration that
cannot be undone, and an old row saying who a retired link was for is harmless.
-/

open Lean SQLite

namespace Resources

/-- What a token is allowed to do. -/
inductive Scope
  | read | write | «import» | admin
  deriving DecidableEq, Repr, Inhabited

namespace Scope

/-- The bit this scope occupies. -/
def bit : Scope → UInt32
  | .read => 1 | .write => 2 | .import => 4 | .admin => 8

/-- The name used on the command line and in JSON. -/
def toString : Scope → String
  | .read => "read" | .write => "write" | .import => "import" | .admin => "admin"

/-- Inverse of `toString`. -/
def ofString? : String → Option Scope
  | "read" => some .read | "write" => some .write
  | "import" => some .import | "admin" => some .admin
  | _ => none

/-- Every scope, for enumeration. -/
def all : List Scope := [.read, .write, .import, .admin]

instance : ToString Scope := ⟨Scope.toString⟩

end Scope

/-- A set of scopes, stored as an integer. -/
structure Scopes where
  mask : UInt32
  deriving DecidableEq, Repr, Inhabited

namespace Scopes

/-- No permissions. -/
def none : Scopes := ⟨0⟩

/-- Builds a scope set from a list. -/
def ofList (ss : List Scope) : Scopes := ⟨ss.foldl (fun m s => m ||| s.bit) 0⟩

/-- Whether the set grants `s`. `admin` grants everything. -/
def has (x : Scopes) (s : Scope) : Bool :=
  (x.mask &&& Scope.admin.bit) != 0 || (x.mask &&& s.bit) != 0

/-- The scopes in the set. -/
def toList (x : Scopes) : List Scope := Scope.all.filter (fun s => (x.mask &&& s.bit) != 0)

instance : ToString Scopes := ⟨fun x => String.intercalate "," (x.toList.map Scope.toString)⟩

/-- Parses `read,write`. -/
def parse (s : String) : Except String Scopes := do
  let parts := (s.splitOn ",").filter (fun p => !p.isEmpty)
  let mut out : List Scope := []
  for p in parts do
    match Scope.ofString? p.trimAscii.toString with
    | some sc => out := sc :: out
    | .none => throw s!"unknown scope: {p}"
  return ofList out

end Scopes

/-- A token record. The secret itself is never stored. -/
structure ApiToken where
  id : TokenId
  name : String
  scopes : Scopes
  createdAt : String
  lastUsedAt : Option String
  expiresAt : Option String
  deriving Repr

private structure TokenRow where
  id : String
  name : String
  hash : String
  scopes : Int64
  createdAt : String
  lastUsedAt : Option String
  expiresAt : Option String
  deriving Row

namespace Tokens

private def ofRow (r : TokenRow) : ApiToken :=
  { id := ⟨r.id⟩, name := r.name, scopes := ⟨r.scopes.toInt.toNat.toUInt32⟩,
    createdAt := r.createdAt, lastUsedAt := r.lastUsedAt, expiresAt := r.expiresAt }

private def cols : String :=
  "SELECT id, name, hash, scopes, created_at, last_used_at, expires_at FROM token"

/-- Mints a token. The returned string is the only time the secret is available. -/
def create (ctx : Ctx) (name : String) (scopes : Scopes)
    (expiresAt : Option Date := .none) : IO (ApiToken × String) := do
  let secret := "rsrc_" ++ toBase32 (← IO.getRandomBytes 32)
  let id ← freshId
  let now ← nowStamp
  Db.exec ctx.db s!"INSERT INTO token
    (id, name, hash, scopes, created_at, last_used_at, expires_at)
    VALUES ({Db.lit id}, {Db.lit name}, {Db.lit (Sha256.hex secret)}, {scopes.mask.toNat},
            {Db.lit now}, NULL, {Db.litOpt (expiresAt.map (·.toIso))})"
  return ({ id := ⟨id⟩, name, scopes, createdAt := now, lastUsedAt := .none,
            expiresAt := expiresAt.map (·.toIso) }, secret)

/-- Every token, without secrets. -/
def list (ctx : Ctx) : IO (Array ApiToken) := do
  let rs ← Db.rows TokenRow ctx.db (cols ++ " ORDER BY created_at")
  return rs.map ofRow

/-- Deletes a token by id or by name. -/
def revoke (ctx : Ctx) (idOrName : String) : IO Bool := do
  let n ← Db.scalarInt ctx.db
    s!"SELECT COUNT(*) FROM token WHERE id = {Db.lit idOrName} OR name = {Db.lit idOrName}"
  Db.exec ctx.db s!"DELETE FROM token WHERE id = {Db.lit idOrName} OR name = {Db.lit idOrName}"
  return n > 0

/--
Verifies a presented secret. Compares hashes in constant time, rejects expired
tokens, and stamps `last_used_at`.
-/
def verify (ctx : Ctx) (presented : String) (today : Date) : IO (Option ApiToken) := do
  let wanted := Sha256.hex presented
  let rows ← Db.rows TokenRow ctx.db cols
  for r in rows do
    if Sha256.constantTimeEq wanted.toUTF8 r.hash.toUTF8 then
      let tok := ofRow r
      match tok.expiresAt.bind Date.ofIso? with
      | some e => if Date.lt e today then return .none
      | .none => pure ()
      let now ← nowStamp
      Db.exec ctx.db s!"UPDATE token SET last_used_at = {Db.lit now} WHERE id = {Db.lit r.id}"
      return some tok
  return .none

/--
Whether any token exists at all, which is what decides whether the API is
locked down yet.

With no tokens the API is open, so the tool works on loopback the moment it
starts, and minting your first token is how you say you are ready to lock it
down.
-/
def any (ctx : Ctx) : IO Bool := do
  return (← Db.scalarInt ctx.db "SELECT COUNT(*) FROM token") > 0

end Tokens

end Resources
