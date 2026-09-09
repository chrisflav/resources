import Resources.Store.Repo

/-!
# Contacts

Contacts are read from wherever you already keep them. This does not store
them.

That is a deliberate limit rather than a missing feature. A second copy of your
address book is a copy that goes stale, and the moment it can be edited here
there are two answers to "what is Anna's email". So there is no authoring.

The preferred source needs no configuration and no credentials: the desktop's
own contact store, Evolution Data Server, which most Linux address books sit on
top of. If it already syncs a CardDAV server then those contacts are on this
machine, kept fresh by something whose job that is, with the password in the
keyring where it belongs. Reading its cache is both less code and less
responsibility than holding another copy of your password.

Talking to CardDAV directly is still there for a machine with no desktop
session, and a directory of vCards for whatever else keeps one.

The parties table still exists and still fills up with payee strings from bank
imports, because a transaction's counterparty is ledger data. It is simply not
where people come from.
-/

open Lean

namespace Resources

/-- One contact, as read from the address book. Never written back. -/
structure Contact where
  name : String
  email : Option String := none
  iban : Option String := none
  note : Option String := none
  deriving Repr, Inhabited

/-- Where the address book lives. -/
inductive ContactSource
  /-- No source; there are no contacts to offer. -/
  | none
  /-- The desktop's own contact store. Needs nothing configured. -/
  | eds
  /-- A `.vcf` file, or a directory of them as vdirsyncer and khard keep. -/
  | files (path : String)
  /-- A CardDAV collection, read over the network. -/
  | carddav (url : String) (user : String) (passwordCommand : List String)
  deriving Repr, Inhabited

namespace Contacts

/-! ## vCard parsing -/

/-- Joins folded continuation lines, which vCard wraps with a leading space. -/
private def unfold (text : String) : List String := Id.run do
  let mut out : List String := []
  for raw in (text.replace "\r\n" "\n").splitOn "\n" do
    if raw.startsWith " " || raw.startsWith "\t" then
      match out.getLast? with
      | some prev => out := out.dropLast ++ [prev ++ (raw.drop 1).toString]
      | none => out := out ++ [raw.trimAscii.toString]
    else out := out ++ [raw]
  return out

/-- The property name of a vCard line, upper-cased and without its parameters. -/
private def propertyOf (line : String) : Option (String × String) := do
  let (head, value) ← Str.splitOnce line ':'
  let name := ((head.splitOn ";").head?.getD head).toUpper
  return (name, value.trimAscii.toString)

/-- Parses vCard text into contacts. Unknown properties are ignored. -/
def parse (text : String) : Array Contact := Id.run do
  let mut out : Array Contact := #[]
  let mut current : Option Contact := none
  for line in unfold text do
    match propertyOf line with
    | none => pure ()
    | some (name, value) =>
      match name with
      | "BEGIN" => if value.toUpper == "VCARD" then current := some { name := "" }
      | "END" =>
        match current with
        | some c => if !c.name.isEmpty then out := out.push c
        | none => pure ()
        current := none
      | _ =>
        match current with
        | none => pure ()
        | some c =>
          current := some <|
            match name with
            | "FN" => { c with name := value }
            -- `N` is surname;given;…; only used when FN is missing.
            | "N" =>
              if !c.name.isEmpty then c
              else
                let parts := (value.splitOn ";").filter (fun x => !x.isEmpty)
                { c with name := String.intercalate " " parts.reverse }
            | "EMAIL" => { c with email := c.email <|> some value }
            | "NOTE" => { c with note := c.note <|> some value }
            -- Some address books keep an IBAN in a custom field.
            | "X-IBAN" => { c with iban := c.iban <|> some (value.replace " " "") }
            | _ => c
  return out

/-! ## Reading the source -/

/-- Where Evolution Data Server caches each address book it knows about. -/
def edsCacheRoot : IO System.FilePath := do
  let home := (← IO.getEnv "HOME").getD "."
  return System.FilePath.mk home / ".cache" / "evolution" / "addressbook"

/--
Asks the source registry what each address book is called.

Books that a collection account creates — the ones a Nextcloud login brings
with it — have no file on disk, so the names are only available from the
running service. Failing to reach it is not an error: the books are still
readable, they just show as their identifiers.
-/
private def sourceRegistry : IO (Array (String × String)) := do
  try
    let res ← IO.Process.output
      { cmd := "gdbus"
        args := #["call", "--session", "--dest", "org.gnome.evolution.dataserver.Sources5",
                  "--object-path", "/org/gnome/evolution/dataserver/SourceManager",
                  "--method", "org.freedesktop.DBus.ObjectManager.GetManagedObjects"] }
    if res.exitCode != 0 then return #[]
    -- Each managed object prints its UID and the text of its description; the
    -- display name is the first line of the latter that names one.
    let mut out : Array (String × String) := #[]
    for chunk in (res.stdout.splitOn "'UID': <'").drop 1 do
      let uid := ((chunk.splitOn "'").head?).getD ""
      let name := ((chunk.splitOn "DisplayName=").drop 1).head?.map fun rest =>
        ((rest.splitOn "\\n").head?).getD ""
      match name with
      | some n => if !n.isEmpty && !(n.startsWith "[") then out := out.push (uid, n)
      | none => pure ()
    return out
  catch _ => return #[]

/-- The address books the desktop contact store holds, as (name, cache file). -/
def edsBooks : IO (Array (String × System.FilePath)) := do
  let root ← edsCacheRoot
  if !(← root.pathExists) then return #[]
  let home := (← IO.getEnv "HOME").getD "."
  let sources := System.FilePath.mk home / ".config" / "evolution" / "sources"
  let registry ← sourceRegistry
  let mut out : Array (String × System.FilePath) := #[]
  for entry in ← root.readDir do
    let db := entry.path / "cache.db"
    if !(← db.pathExists) then continue
    -- A book's display name lives in the source description beside it for local
    -- books; for ones a collection created — the CardDAV books a Nextcloud
    -- account brings with it — the registry only has it in memory, so it is
    -- asked for over the bus. A bare uid is a poor label but better than
    -- dropping the book.
    let descriptor := sources / (entry.fileName ++ ".source")
    let name ←
      if ← descriptor.pathExists then do
        let text ← IO.FS.readFile descriptor
        let named := (text.splitOn "\n").find? fun l => l.startsWith "DisplayName="
        pure ((named.map fun l => (l.drop 12).toString).getD entry.fileName)
      else pure ((registry.find? fun (uid, _) => uid == entry.fileName).map (·.2)
                  |>.getD entry.fileName)
    out := out.push (name, db)
  return out

/-- Reads the configured source, falling back to the desktop's contact store. -/
def source (ctx : Ctx) : IO ContactSource := do
  let p := ctx.cfg.dataDir / "contacts.json"
  if !(← p.pathExists) then
    -- Nothing to configure when the desktop already has an address book.
    return if (← edsBooks).isEmpty then .none else .eds
  match Json.parse (← IO.FS.readFile p) with
  | .error e => do IO.eprintln s!"warning: bad contacts.json: {e}"; return .none
  | .ok j =>
    let str (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
    match str "kind" with
    | "eds" => return .eds
    | "files" => return .files (str "path")
    | "carddav" =>
      return .carddav (str "url") (str "user")
        (((j.getObjValAs? (Array String) "passwordCommand").toOption.getD #[]).toList)
    | other =>
      IO.eprintln s!"warning: unknown contacts source {other}"
      return .none

/-- A one-line description, for showing what is configured. -/
def describe : ContactSource → String
  | .none => "none found"
  | .eds => "the desktop contact store (Evolution Data Server)"
  | .files path => s!"vCards at {path}"
  | .carddav url user _ => s!"CardDAV {url} as {user}"

private def readFiles (path : String) : IO String := do
  let p := System.FilePath.mk path
  if !(← p.pathExists) then
    throw <| IO.userError s!"no contacts at {path}"
  if ← p.isDir then
    let mut text := ""
    for entry in ← p.readDir do
      if entry.fileName.endsWith ".vcf" || entry.fileName.endsWith ".vcard" then
        text := text ++ (← IO.FS.readFile entry.path) ++ "\n"
    return text
  else IO.FS.readFile p

/-- Undoes the XML escaping a CardDAV response wraps vCards in. -/
private def unescapeXml (s : String) : String :=
  s.replace "&#13;" "" |>.replace "&lt;" "<" |>.replace "&gt;" ">"
   |>.replace "&quot;" "\"" |>.replace "&#39;" "'" |>.replace "&amp;" "&"

/--
Pulls the vCards out of a CardDAV collection.

The response is a WebDAV multistatus document with each card inside an
`address-data` element. Rather than parse XML, the cards are lifted out by
their own delimiters — they are exactly delimited, and a real XML parser would
be a lot of machinery for one field.
-/
private def readCardDav (url user : String) (passwordCommand : List String) : IO String := do
  let password ←
    match passwordCommand with
    | [] => pure ""
    | cmd :: args => do
      let res ← IO.Process.output { cmd, args := args.toArray }
      if res.exitCode != 0 then
        throw <| IO.userError s!"could not read the CardDAV password: {res.stderr}"
      pure (res.stdout.trimAscii.toString)
  let body :=
    "<?xml version=\"1.0\" encoding=\"utf-8\"?>" ++
    "<C:addressbook-query xmlns:D=\"DAV:\" xmlns:C=\"urn:ietf:params:xml:ns:carddav\">" ++
    "<D:prop><C:address-data/></D:prop></C:addressbook-query>"
  let res ← IO.Process.output
    { cmd := "curl"
      args := #["-s", "-S", "--fail-with-body", "-X", "REPORT",
                "-u", s!"{user}:{password}",
                "-H", "Depth: 1", "-H", "Content-Type: application/xml; charset=utf-8",
                "--data-binary", body, url] }
  if res.exitCode != 0 then
    throw <| IO.userError s!"CardDAV request failed: {res.stderr}"
  -- Lift the cards out by their own delimiters.
  let text := unescapeXml res.stdout
  let mut cards := ""
  for chunk in text.splitOn "BEGIN:VCARD" do
    let parts := chunk.splitOn "END:VCARD"
    if parts.length > 1 then
      cards := cards ++ "BEGIN:VCARD" ++ parts.head! ++ "END:VCARD\n"
  return cards

/--
Reads every vCard the desktop contact store has cached.

The cache is opened read-only and with a busy timeout, because the address book
service owns these files and may be writing to one while it is read.
-/
private def readEds : IO String := do
  let mut text := ""
  for (_, db) in ← edsBooks do
    try
      let conn ← SQLite.openWith db SQLite.OpenFlags.readonly (busyTimeoutMs := 2000)
      for card in ← Db.rows String conn "SELECT ECacheOBJ FROM ECacheObjects" do
        text := text ++ card ++ "\n"
    catch _ =>
      -- A book that cannot be read should not take the others down with it.
      pure ()
  return text

/-- Every contact the configured source knows about. -/
def all (ctx : Ctx) : IO (Array Contact) := do
  match ← source ctx with
  | .none => return #[]
  | .eds => return parse (← readEds)
  | .files path => return parse (← readFiles path)
  | .carddav url user pw => return parse (← readCardDav url user pw)

/-- How many contacts each desktop address book holds. -/
def edsBookCounts : IO (Array (String × Nat)) := do
  let mut out : Array (String × Nat) := #[]
  for (name, db) in ← edsBooks do
    let n ←
      try
        let conn ← SQLite.openWith db SQLite.OpenFlags.readonly (busyTimeoutMs := 2000)
        pure (← Db.scalarInt conn "SELECT COUNT(*) FROM ECacheObjects").toNat
      catch _ => pure 0
    out := out.push (name, n)
  return out

/-- Records which source to read, so nothing has to be edited by hand. -/
def saveSource (ctx : Ctx) (s : ContactSource) : IO Unit := do
  let p := ctx.cfg.dataDir / "contacts.json"
  match s with
  | .none => if ← p.pathExists then IO.FS.removeFile p
  | .eds => IO.FS.writeFile p "{\"kind\": \"eds\"}\n"
  | .files path =>
    IO.FS.writeFile p (Json.pretty (Json.mkObj [("kind", "files"), ("path", path)]) ++ "\n")
  | .carddav url user pw =>
    IO.FS.writeFile p (Json.pretty (Json.mkObj [
      ("kind", "carddav"), ("url", url), ("user", user),
      ("passwordCommand", Json.arr ((pw.map Json.str).toArray))]) ++ "\n")

/-- Looks a contact up by name. -/
def byName? (ctx : Ctx) (name : String) : IO (Option Contact) := do
  return (← all ctx).find? fun c => c.name == name

end Contacts

end Resources
