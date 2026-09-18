import Std.Sync.Mutex
import Resources.Store.Db
import Resources.Sync.Protocol

/-!
# The sequencer's store

The sequencer keeps its own SQLite file, `sequencer.db`, with its own numbered
migrations. It is deliberately not the ledger database: the two hold different
things for different people. The ledger database holds your plaintext books; this
one holds ciphertext, the order it arrived in, and the membership, grants and
pending invites that say who may add to it.

Nothing here can read a payload. A part is stored base64-encoded exactly as it
arrived, and the only questions asked of it are which realm and which key
generation it claims.

The append is the one interesting operation: the checks and the insert run inside
a single immediate transaction, so a second writer cannot slip between "your
`prevHash` matches the head" and "your entry is the head".

## One connection, one writer at a time

There is a single SQLite handle here and the HTTP server dispatches requests
onto a thread pool, so two handlers really can run at once. `BEGIN IMMEDIATE`
on a shared connection is not isolation — the second `BEGIN` fails, and the
failure path's `ROLLBACK` aborts the *first* handler's transaction, which is how
a compare-and-swap and a single-use invite stop being atomic. So the store
carries a mutex and every request holds it for its whole duration.

`Sequencer.gate` is taken in exactly one place, `Sync.handleSafe`, because the
underlying `Std.BaseMutex` is not reentrant: taking it twice on one thread is
undefined behaviour. Nothing in this file locks anything.
-/

open Lean SQLite

namespace Resources
namespace Sync

/-- Where the sequencer keeps its database. -/
structure Config where
  /-- Root directory; the database file lives inside it. -/
  dataDir : System.FilePath
  /-- The SQLite file. -/
  dbPath : System.FilePath
  deriving Repr, Inhabited

namespace Config

/-- A config rooted at an explicit directory. -/
def atDir (root : System.FilePath) : Config :=
  { dataDir := root, dbPath := root / "sequencer.db" }

/-- `$RESOURCES_SEQ_DIR`, else `$RESOURCES_DIR/sequencer`, else `~/.local/share/resources/seq`. -/
def default : IO Config := do
  match (← IO.getEnv "RESOURCES_SEQ_DIR") with
  | some d => return atDir (System.FilePath.mk d)
  | none =>
    match (← IO.getEnv "RESOURCES_DIR") with
    | some d => return atDir (System.FilePath.mk d / "sequencer")
    | none =>
      let home := (← IO.getEnv "HOME").getD "."
      return atDir (System.FilePath.mk home / ".local" / "share" / "resources" / "seq")

end Config

/-- An open sequencer database. -/
structure Sequencer where
  /-- The handle. -/
  db : SQLite
  /-- The paths it was opened from. -/
  cfg : Config
  /-- Held for the whole of a request, so that two of them never share a transaction. -/
  gate : Std.BaseMutex

/-- How an append ended. -/
inductive Appended
  /-- Accepted; the ledger's new head. -/
  | ok (head : Head)
  /-- The stated `seq`/`prevHash` no longer describe the head. The current head is returned. -/
  | conflict (head : Head)
  /-- No such ledger. -/
  | unknownLedger
  /-- The author is not a member of this ledger. -/
  | notMember
  /-- The author holds no grant on this realm at this generation. -/
  | noGrant (realm : String) (generation : Nat)
  /-- The author's grant on this realm carries a role that writes nothing. -/
  | badRole (realm : String) (role : String)
  deriving Inhabited

/-- How spending an invite ended. -/
inductive Joined
  /-- Accepted; the grant the joiner now holds. -/
  | ok (grant : Grant)
  /-- No invite by that key on this realm. A used invite is gone, so it lands here too. -/
  | unknownInvite
  /-- The offer had lapsed; the invite has been purged. -/
  | expired
  /-- The realm key has moved on since the invite was made; the invite has been purged. -/
  | staleGeneration (generation : Nat)
  deriving Inhabited

private structure EnvelopeRow where
  seq : Int64
  hash : String
  prevHash : String
  author : String
  signature : String
  deriving Row

private structure PartRow where
  seq : Int64
  idx : Int64
  realm : String
  generation : Int64
  cipherHash : String
  ciphertext : String
  deriving Row

private structure MemberRow where
  member : String
  boxPk : String
  boxPkSignature : String
  boxPkGeneration : Int64
  admin : Int64
  addedAt : String
  deriving Row

private structure RealmRow where
  realm : String
  generation : Int64
  admin : String
  deriving Row

private structure GrantRow where
  realm : String
  member : String
  generation : Int64
  wrappedKey : String
  role : String
  grantedBy : String
  signature : String
  deriving Row

private structure InviteRow where
  realm : String
  signPk : String
  boxPk : String
  wrappedKey : String
  generation : Int64
  role : String
  expires : String
  createdBy : String
  deriving Row

private structure CheckpointRow where
  author : String
  generation : Int64
  seq : Int64
  stateHash : String
  headHash : String
  signature : String
  snapshot : String
  deriving Row

namespace Log

/-! ## Schema -/

/--
Numbered migrations for `sequencer.db`. Append only: never edit a migration that
has shipped, add another one.
-/
def migrations : List (Nat × String) := [
  (1, "
-- One ledger, one total order. The sequencer can serve several.
CREATE TABLE ledger (
  id TEXT PRIMARY KEY, created_at TEXT NOT NULL);

-- Who may append, by public key. Admins may add and remove members.
CREATE TABLE member (
  ledger TEXT NOT NULL REFERENCES ledger(id) ON DELETE CASCADE,
  member TEXT NOT NULL,
  admin INTEGER NOT NULL DEFAULT 0,
  added_at TEXT NOT NULL,
  PRIMARY KEY (ledger, member));

-- A realm is one key's worth of a ledger. The generation is what makes a revoke
-- mean something: it moves forward, and every part written under the old number
-- is refused from then on.
CREATE TABLE realm (
  ledger TEXT NOT NULL REFERENCES ledger(id) ON DELETE CASCADE,
  realm TEXT NOT NULL,
  generation INTEGER NOT NULL DEFAULT 0,
  admin TEXT NOT NULL,
  created_at TEXT NOT NULL,
  PRIMARY KEY (ledger, realm));

-- The realm key wrapped to one member's public key. Opaque here: the server
-- stores it, hands it back to the member it belongs to, and cannot unwrap it.
CREATE TABLE realm_grant (
  ledger TEXT NOT NULL,
  realm TEXT NOT NULL,
  member TEXT NOT NULL,
  generation INTEGER NOT NULL,
  wrapped_key TEXT NOT NULL,
  granted_at TEXT NOT NULL,
  PRIMARY KEY (ledger, realm, member));

-- The order itself. `hash` is the canonical digest defined in Sync.Protocol and
-- is stored rather than recomputed, because it is what the next entry's
-- `prev_hash` is compared against on every append.
CREATE TABLE envelope (
  ledger TEXT NOT NULL,
  seq INTEGER NOT NULL,
  hash TEXT NOT NULL,
  prev_hash TEXT NOT NULL,
  author TEXT NOT NULL,
  signature TEXT NOT NULL,
  received_at TEXT NOT NULL,
  PRIMARY KEY (ledger, seq));

-- One realm's slice of an entry, base64 exactly as it arrived.
CREATE TABLE part (
  ledger TEXT NOT NULL,
  seq INTEGER NOT NULL,
  idx INTEGER NOT NULL,
  realm TEXT NOT NULL,
  generation INTEGER NOT NULL,
  ciphertext TEXT NOT NULL,
  PRIMARY KEY (ledger, seq, idx));

CREATE INDEX part_realm ON part(ledger, realm);

-- The latest signed commitment for a realm, with the snapshot a newcomer starts
-- from. Only the newest is kept: an older one proves nothing the newer does not.
CREATE TABLE checkpoint (
  ledger TEXT NOT NULL,
  realm TEXT NOT NULL,
  generation INTEGER NOT NULL,
  seq INTEGER NOT NULL,
  state_hash TEXT NOT NULL,
  author TEXT NOT NULL,
  signature TEXT NOT NULL,
  snapshot TEXT NOT NULL,
  written_at TEXT NOT NULL,
  PRIMARY KEY (ledger, realm));

-- Opaque bytes addressed by the hash of their ciphertext: receipts and other
-- attachments too big to sit in the order.
CREATE TABLE blob (
  ledger TEXT NOT NULL,
  hash TEXT NOT NULL,
  bytes TEXT NOT NULL,
  written_at TEXT NOT NULL,
  PRIMARY KEY (ledger, hash));
"),
  (2, "
-- A member signs with Ed25519 and is sealed to with X25519, so the record needs
-- both keys. The id stays the signing key: existing rows keep their id and gain
-- an empty agreement key until they publish one.
ALTER TABLE member ADD COLUMN box_pk TEXT NOT NULL DEFAULT '';

-- What a grant is for. The sequencer carries the role and enforces nothing with
-- it: what it enforces is the grant's existence and its generation.
ALTER TABLE realm_grant ADD COLUMN role TEXT NOT NULL DEFAULT 'viewer';

-- A pending grant. The realm key is sealed to an ephemeral X25519 key whose
-- secret half travels out of band, and redeeming it means signing the join
-- bytes with the matching Ed25519 key. One row is one join: it is deleted the moment
-- it is used, and any row whose `expires` has passed is deleted on sight.
CREATE TABLE invite (
  ledger TEXT NOT NULL REFERENCES ledger(id) ON DELETE CASCADE,
  realm TEXT NOT NULL,
  invite_sign_pk TEXT NOT NULL,
  invite_box_pk TEXT NOT NULL,
  wrapped_key TEXT NOT NULL,
  generation INTEGER NOT NULL,
  role TEXT NOT NULL,
  expires TEXT NOT NULL,
  created_by TEXT NOT NULL,
  created_at TEXT NOT NULL,
  PRIMARY KEY (ledger, realm, invite_sign_pk));

CREATE INDEX invite_expires ON invite(expires);
"),
  (3, "
-- A checkpoint now names the head it speaks about: the hash of the envelope at
-- its `seq`. It is what lets a reader who starts from a snapshot join onto the
-- chain, because it is the `prevHash` the next envelope carries. Rows written
-- before this column existed name nothing, and a client that meets one has to
-- fall back to replaying the order.
ALTER TABLE checkpoint ADD COLUMN head_hash TEXT NOT NULL DEFAULT '';
"),
  (4, "
-- Protocol v2. Four records gain the proof that was missing from them.

-- An agreement key is now a claim its own signing key made, and this is the
-- proof: the member's signature over `memberBytes`. A row written before this
-- column existed carries a key nobody signed for, so the column is empty and
-- every client treats such a key as absent.
ALTER TABLE member ADD COLUMN box_pk_signature TEXT NOT NULL DEFAULT '';

-- A grant now names who issued it and carries their signature over
-- `grantBytes`, so a client can refuse a realm key that was wrapped by
-- somebody it has no reason to trust.
ALTER TABLE realm_grant ADD COLUMN granted_by TEXT NOT NULL DEFAULT '';
ALTER TABLE realm_grant ADD COLUMN signature TEXT NOT NULL DEFAULT '';

-- A part now carries the digest of its ciphertext, which is what the envelope's
-- signature and hash are taken over. It is stored rather than recomputed
-- because it is what a filtered fetch serves in place of bytes it withholds.
ALTER TABLE part ADD COLUMN cipher_hash TEXT NOT NULL DEFAULT '';

-- A checkpoint is one member's claim about what they replayed, so there is one
-- per author rather than one per realm: keeping only the newest of them all let
-- any grant holder overwrite everybody else's, and roll the realm backwards
-- while they were at it.
CREATE TABLE checkpoint_v2 (
  ledger TEXT NOT NULL,
  realm TEXT NOT NULL,
  author TEXT NOT NULL,
  generation INTEGER NOT NULL,
  seq INTEGER NOT NULL,
  state_hash TEXT NOT NULL,
  head_hash TEXT NOT NULL DEFAULT '',
  signature TEXT NOT NULL,
  snapshot TEXT NOT NULL,
  written_at TEXT NOT NULL,
  PRIMARY KEY (ledger, realm, author));

INSERT INTO checkpoint_v2
    (ledger, realm, author, generation, seq, state_hash, head_hash, signature, snapshot,
     written_at)
  SELECT ledger, realm, author, generation, seq, state_hash, head_hash, signature, snapshot,
    written_at FROM checkpoint;

DROP TABLE checkpoint;
ALTER TABLE checkpoint_v2 RENAME TO checkpoint;
"),
  (5, "
-- An agreement key can now be replaced. The generation is inside the bytes the
-- member signs, and a publication that does not move it forward is refused, so
-- a key whose secret half has leaked stops being a valid self-attestation the
-- moment its owner publishes the next one. Rows written before this column
-- existed sit at 0, which is what a first key carries.
ALTER TABLE member ADD COLUMN box_pk_generation INTEGER NOT NULL DEFAULT 0;

-- What a blob costs the ledger it belongs to. Blobs are stored base64 and were
-- never counted, so any member of any ledger could fill the disk sixteen
-- megabytes at a time; the quota is checked against the sum of this column.
-- Existing rows are backfilled from the length of their encoding, which is the
-- decoded size to within the padding.
ALTER TABLE blob ADD COLUMN size INTEGER NOT NULL DEFAULT 0;

UPDATE blob SET size = (length(bytes) * 3) / 4;

CREATE INDEX blob_ledger ON blob(ledger);
"),
  (6, "
-- A blob is the bytes themselves rather than the text of their base64.
--
-- The encoding cost a third of the quota again on disk (a ledger allowed 256
-- MiB really held 341 MiB of file) and a decode on every read, of bytes this
-- service is never going to look inside. SQLite stores a byte string as itself
-- through a bound parameter, which is what every other binary column in this
-- project already does.
--
-- The rows are carried over by `rewriteBlobsToBinary`, in the same transaction
-- as these statements: SQLite has no base64, so the decode is Lean's to do.
CREATE TABLE blob_v2 (
  ledger TEXT NOT NULL,
  hash TEXT NOT NULL,
  bytes BLOB NOT NULL,
  size INTEGER NOT NULL DEFAULT 0,
  written_at TEXT NOT NULL,
  PRIMARY KEY (ledger, hash));
")
]

/-- Which blobs there are, which is all that is read at once. -/
private structure BlobKeyRow where
  ledger : String
  hash : String
  deriving Row

/-- One blob as version 5 stored it: the text of its base64. -/
private structure LegacyBlobRow where
  bytes : String
  writtenAt : String
  deriving Row

/--
Migration 6's other half: every blob, decoded out of its base64 and written
back as the bytes it stood for.

It is here rather than in the SQL because SQLite has no base64 function. The
names are read first and the bytes one at a time, so what this holds in memory
is one blob rather than a ledger's worth of them — the quota is 256 MiB and a
migration is not the moment to ask for all of it at once.

A row whose text is not base64 cannot have come from `putBlob`, and it would
decode to nothing on the way out whatever happened here, so it is dropped
rather than carried over as bytes it never was.
-/
private def rewriteBlobsToBinary (db : SQLite) : IO Unit := do
  let keys ← Db.rows BlobKeyRow db "SELECT ledger, hash FROM blob"
  for k in keys do
    let some row ← Db.row? LegacyBlobRow db s!"SELECT bytes, written_at FROM blob
      WHERE ledger = {Db.lit k.ledger} AND hash = {Db.lit k.hash}" | continue
    let some bytes := ofBase64? row.bytes | continue
    Db.execBlob db s!"INSERT INTO blob_v2 (ledger, hash, bytes, size, written_at)
      VALUES ({Db.lit k.ledger}, {Db.lit k.hash}, ?, {bytes.size}, {Db.lit row.writtenAt})"
      bytes
  Db.exec db "DROP TABLE blob;
    ALTER TABLE blob_v2 RENAME TO blob;
    CREATE INDEX blob_ledger ON blob(ledger);"

/-- The migrations that need more than SQL, by the version they belong to. -/
private def rewrite (db : SQLite) : Nat → IO Unit
  | 6 => rewriteBlobsToBinary db
  | _ => pure ()

/-- The schema version this binary expects. -/
def targetVersion : Nat := migrations.foldl (fun acc (v, _) => max acc v) 0

/-- Reads `PRAGMA user_version`. -/
def currentVersion (db : SQLite) : IO Nat := do
  match (← Db.row? Int64 db "PRAGMA user_version") with
  | some n => return n.toInt.toNat
  | none => return 0

/-- Applies every migration newer than the stored version. Returns how many ran. -/
def migrate (db : SQLite) : IO Nat := do
  let cur ← currentVersion db
  let pending := migrations.filter (fun (v, _) => v > cur)
  if pending.isEmpty then return 0
  for (v, sql) in pending do
    SQLite.transaction db do
      Db.exec db sql
      rewrite db v
      Db.exec db s!"PRAGMA user_version = {v}"
  return pending.length

/--
Opens (creating if needed) the sequencer database, running any pending
migrations.

The directory is made 0700 and every file the store keeps in it 0600, the way
the node's own store is (`Files` in `Resources.Store.Db`, which this file
already depends on). What is in here is ciphertext, but it is also the
membership graph — who keeps books with whom — and the audit trail names people
by the keys they are known by. The modes are set after the migrations rather
than before, because SQLite makes its journal files when it first writes and a
mode set before they exist sets nothing.
-/
def «open» (cfg : Config) : IO Sequencer := do
  Files.privateDir cfg.dataDir
  let db ← SQLite.open cfg.dbPath (busyTimeoutMs := 5000)
  Db.exec db "PRAGMA journal_mode = WAL"
  Db.exec db "PRAGMA foreign_keys = ON"
  Db.exec db "PRAGMA synchronous = NORMAL"
  discard <| migrate db
  harden cfg
  return { db, cfg, gate := ← Std.BaseMutex.new }
where
  /-- 0700 on the directory, 0600 on the database and everything WAL leaves beside it. -/
  harden (cfg : Config) : IO Unit := do
    Files.restrict cfg.dataDir Files.ownerOnlyDir
    for suffix in ["", "-wal", "-shm", "-journal"] do
      let path := System.FilePath.mk (cfg.dbPath.toString ++ suffix)
      if ← path.pathExists then
        Files.restrict path Files.ownerOnlyFile

/--
Runs `act` with the store to itself.

One connection and a thread pool make every transaction here a shared resource,
so this is what makes "inside one transaction" mean anything. It is taken in one
place only — `Sync.handleSafe` — because the lock underneath is not reentrant.
-/
def exclusively (s : Sequencer) (act : IO α) : IO α := do
  try
    s.gate.lock
    act
  finally
    s.gate.unlock

/--
Now, in UTC, in the one shape every stored timestamp is normalised to.

Not `nowStamp`, which is local naive time with no zone: an invite written by a
browser carries UTC, and comparing that with a local clock is wrong by the
offset — in the wrong direction, for half the world, every day of the year.
-/
def utcNow : IO String := do
  let ms ← nowMillis
  let seconds := ms / 1000 - (if ms % 1000 < 0 then 1 else 0)
  let days := seconds / 86400 - (if seconds % 86400 < 0 then 1 else 0)
  let secondOfDay := (seconds - days * 86400).toNat
  let (y, m, d) := civilFromDays days
  return isoCanonical y m d (secondOfDay / 3600) (secondOfDay / 60 % 60) (secondOfDay % 60)

/-- Where the audit trail is appended. -/
def auditPath (s : Sequencer) : System.FilePath := s.cfg.dataDir / "sequencer-audit.log"

/-- Where the previous trail is kept once the current one has been rotated away. -/
def auditPreviousPath (s : Sequencer) : System.FilePath :=
  System.FilePath.mk ((auditPath s).toString ++ ".1")

/-- How large the trail may grow before it is rotated: 64 MiB. -/
def auditMaxBytes : Nat := 64 * 1024 * 1024

/-- How many bytes of the current trail there are, or 0 if there is none. -/
private def auditSize (path : System.FilePath) : IO Nat :=
  (do return (← path.metadata).byteSize.toNat) <|> pure 0

/--
Appends one line to the audit trail.

An ordering service is also the record somebody reads after something has gone
wrong, and until now it wrote nothing down: who appended, who joined, who was
revoked and which authentications failed all left the process with no trace at
all. One line per mutating request, written under the same lock the request
holds, so the file is in the order the ledger is.

A trail that could fail a request would be a way to stop the service by filling
a disk, so a write that does not work is swallowed. It is a record, not a
control.

Two things the first version of this got wrong:

* **The line was written verbatim.** Path segments arrive percent-*decoded*, so
  `%0A` was a newline by the time it reached the file, and one unauthenticated
  `POST /seq/v2/x%0A…` left a second line in the trail that nothing could tell
  apart from a real entry — a forged timestamp, method, member and outcome in
  the only forensic artefact this service keeps. Every line now goes through
  `logLine`, and the fields inside it through `logField`, so a byte that is not
  printable US-ASCII is written as `%xx` and a newline can only be the one this
  function puts there.
* **It grew without bound.** A line is written for every mutating request,
  authenticated or not, so filling the disk cost nothing. The file is rotated at
  `auditMaxBytes`: the current trail is renamed to `.1`, replacing whatever was
  there, and a fresh one is started. Two files is the whole policy — an operator
  who wants more ships them somewhere.

The file lists member ids, which are public keys but are also the names of the
people who keep books here, so it is made readable by its owner alone the moment
it is created.
-/
def audit (s : Sequencer) (line : String) (maxBytes : Nat := auditMaxBytes) : IO Unit :=
  (do
    let path := auditPath s
    if (← auditSize path) ≥ maxBytes then
      try IO.FS.removeFile (auditPreviousPath s) catch _ => pure ()
      IO.FS.rename path (auditPreviousPath s)
    let fresh := !(← path.pathExists)
    let h ← IO.FS.Handle.mk path .append
    h.putStr (logLine line ++ "\n")
    h.flush
    if fresh then
      Files.restrict path Files.ownerOnlyFile) <|> pure ()

/-! ## Ledgers and membership -/

/-- Whether a ledger exists. -/
def ledgerExists (s : Sequencer) (ledger : String) : IO Bool := do
  return (← Db.scalarInt s.db
    s!"SELECT COUNT(*) FROM ledger WHERE id = {Db.lit ledger}") > 0

/-- Creates a ledger with `admin` as its first, administrating member. False if it exists. -/
def createLedger (s : Sequencer) (ledger admin : String) : IO Bool := do
  if ← ledgerExists s ledger then return false
  let now ← nowStamp
  SQLite.transaction s.db (do
    Db.exec s.db s!"INSERT INTO ledger (id, created_at) VALUES ({Db.lit ledger}, {Db.lit now})"
    Db.exec s.db s!"INSERT INTO member (ledger, member, admin, added_at)
      VALUES ({Db.lit ledger}, {Db.lit admin}, 1, {Db.lit now})") .immediate
  return true

/-- The columns a member record is read out of, in the order `MemberRow` names them. -/
private def memberCols : String :=
  "member, box_pk, box_pk_signature, box_pk_generation, admin, added_at"

/-- One row as a member. -/
private def ofMemberRow (r : MemberRow) : Member :=
  { key := r.member, boxPk := r.boxPk, boxPkSignature := r.boxPkSignature,
    keyGeneration := r.boxPkGeneration.toInt.toNat,
    admin := r.admin != (0 : Int64), addedAt := r.addedAt }

/-- Every member of a ledger. -/
def members (s : Sequencer) (ledger : String) : IO (Array Member) := do
  let rs ← Db.rows MemberRow s.db s!"SELECT {memberCols} FROM member
    WHERE ledger = {Db.lit ledger} ORDER BY added_at, member"
  return rs.map ofMemberRow

/-- One member, if they belong to the ledger. -/
def member? (s : Sequencer) (ledger key : String) : IO (Option Member) := do
  let rs ← Db.rows MemberRow s.db s!"SELECT {memberCols} FROM member
    WHERE ledger = {Db.lit ledger} AND member = {Db.lit key}"
  return (rs.map ofMemberRow)[0]?

/-- Whether a key is a member of the ledger. -/
def isMember (s : Sequencer) (ledger key : String) : IO Bool := do
  return (← member? s ledger key).isSome

/-- Whether a key administrates the ledger. -/
def isLedgerAdmin (s : Sequencer) (ledger key : String) : IO Bool := do
  return ((← member? s ledger key).map (·.admin)).getD false

/--
Adds a member, or changes whether an existing one administrates.

`admin` is an option rather than a flag because "say nothing about it" and "say
no" are different requests, and conflating them was a way to demote somebody by
re-adding them. A member arrives with no agreement key: only they can publish
one, with `setBoxPk`.
-/
def addMember (s : Sequencer) (ledger key : String) (admin : Option Bool) : IO Unit := do
  let now ← nowStamp
  let flag := if admin == some true then 1 else 0
  let keep := match admin with
    | some a => toString (if a then 1 else 0)
    | none => "admin"
  Db.exec s.db s!"INSERT INTO member (ledger, member, admin, added_at)
    VALUES ({Db.lit ledger}, {Db.lit key}, {flag}, {Db.lit now})
    ON CONFLICT(ledger, member) DO UPDATE SET admin = {keep}"

/--
Publishes a member's own agreement key, with the signature that proves it is
theirs.

The route above is the only caller, and it has already checked both that the
session speaks for this member and that the signature verifies. Storing the
signature beside the key is what lets every other client check it again without
asking anybody.

The generation is stored with it, and the route refuses one that does not move
forward, so the row always holds the newest key its owner has claimed. The
`WHERE` says so a second time — it is the transaction's own guard against two
publications racing, which cannot happen under the request lock and costs
nothing to be sure of.
-/
def setBoxPk (s : Sequencer) (ledger key boxPk signature : String)
    (keyGeneration : Nat) : IO Unit := do
  Db.exec s.db s!"UPDATE member SET box_pk = {Db.lit boxPk},
      box_pk_signature = {Db.lit signature}, box_pk_generation = {keyGeneration}
    WHERE ledger = {Db.lit ledger} AND member = {Db.lit key}
      AND box_pk_generation <= {keyGeneration}"

/-! ## Realms and grants -/

/-- Every realm of a ledger. -/
def realms (s : Sequencer) (ledger : String) : IO (Array Realm) := do
  let rs ← Db.rows RealmRow s.db s!"SELECT realm, generation, admin FROM realm
    WHERE ledger = {Db.lit ledger} ORDER BY realm"
  return rs.map fun r =>
    { name := r.realm, generation := r.generation.toInt.toNat, admin := r.admin }

/-- One realm, if it exists. -/
def realm? (s : Sequencer) (ledger realm : String) : IO (Option Realm) := do
  let rs ← Db.rows RealmRow s.db s!"SELECT realm, generation, admin FROM realm
    WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}"
  return (rs.map fun r =>
    ({ name := r.realm, generation := r.generation.toInt.toNat, admin := r.admin } : Realm))[0]?

/-- Creates a realm at generation 0 with `admin` as its administrator. False if it exists. -/
def createRealm (s : Sequencer) (ledger realm admin : String) : IO Bool := do
  if (← realm? s ledger realm).isSome then return false
  let now ← nowStamp
  Db.exec s.db s!"INSERT INTO realm (ledger, realm, generation, admin, created_at)
    VALUES ({Db.lit ledger}, {Db.lit realm}, 0, {Db.lit admin}, {Db.lit now})"
  return true

/-- The columns a grant is read out of, in the order `GrantRow` names them. -/
private def grantCols : String :=
  "realm, member, generation, wrapped_key, role, granted_by, signature"

/-- One row as a grant. -/
private def ofGrantRow (r : GrantRow) : Grant :=
  { realm := r.realm, member := r.member, generation := r.generation.toInt.toNat,
    wrappedKey := (ofBase64? r.wrappedKey).getD ByteArray.empty, role := r.role,
    grantedBy := r.grantedBy, signature := r.signature }

/-- Every grant on a realm. -/
def grants (s : Sequencer) (ledger realm : String) : IO (Array Grant) := do
  let rs ← Db.rows GrantRow s.db s!"SELECT {grantCols}
    FROM realm_grant WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}
    ORDER BY member"
  return rs.map ofGrantRow

/-- One member's grant on one realm. -/
def grant? (s : Sequencer) (ledger realm member : String) : IO (Option Grant) := do
  let rs ← Db.rows GrantRow s.db s!"SELECT {grantCols}
    FROM realm_grant WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}
      AND member = {Db.lit member}"
  return (rs.map ofGrantRow)[0]?

/-- Every grant one member holds on a ledger. This is what a fetch is filtered by. -/
def grantsOf (s : Sequencer) (ledger member : String) : IO (Array Grant) := do
  let rs ← Db.rows GrantRow s.db s!"SELECT {grantCols}
    FROM realm_grant WHERE ledger = {Db.lit ledger} AND member = {Db.lit member}
    ORDER BY realm"
  return rs.map ofGrantRow

/--
Grants a member the realm key at the realm's *current* generation.

The generation is not the caller's to choose. A grant that could name an old
generation would be a way to hand back access that a revoke had taken away —
and it is inside the signed bytes, so the route checks the signature against
the number read here rather than the one the body claims.
-/
def putGrant (s : Sequencer) (ledger realm member : String) (wrapped : ByteArray)
    (role grantedBy signature : String) : IO (Option Grant) := do
  let some r ← realm? s ledger realm | return none
  let now ← nowStamp
  let encoded := toBase64 wrapped
  Db.exec s.db s!"INSERT INTO realm_grant
      (ledger, realm, member, generation, wrapped_key, role, granted_by, signature, granted_at)
    VALUES ({Db.lit ledger}, {Db.lit realm}, {Db.lit member}, {r.generation},
            {Db.lit encoded}, {Db.lit role}, {Db.lit grantedBy}, {Db.lit signature},
            {Db.lit now})
    ON CONFLICT(ledger, realm, member) DO UPDATE SET
      generation = {r.generation}, wrapped_key = {Db.lit encoded}, role = {Db.lit role},
      granted_by = {Db.lit grantedBy}, signature = {Db.lit signature},
      granted_at = {Db.lit now}"
  return some { realm, member, generation := r.generation, wrappedKey := wrapped, role,
                grantedBy, signature }

/--
Revokes a grant and bumps the realm's generation, returning the new one.

Bumping is the whole of what a revoke is here. The server cannot make anybody
forget a key they already hold; what it can do is refuse everything written under
that key from now on, which is what the generation check on append enforces. The
members who remain are expected to be re-granted the new generation.
-/
def revokeGrant (s : Sequencer) (ledger realm member : String) : IO (Option Nat) := do
  let some r ← realm? s ledger realm | return none
  Db.exec s.db s!"DELETE FROM realm_grant WHERE ledger = {Db.lit ledger}
    AND realm = {Db.lit realm} AND member = {Db.lit member}"
  Db.exec s.db s!"UPDATE realm SET generation = generation + 1
    WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}"
  return some (r.generation + 1)

/--
Removes a member, revoking every grant they held.

Each revoked realm moves on a generation, for the same reason a single revoke
does: the departing member still has the keys they were given, and the only thing
the server can do about it is stop accepting what those keys encrypt.
-/
def removeMember (s : Sequencer) (ledger key : String) : IO Bool := do
  if !(← isMember s ledger key) then return false
  SQLite.transaction s.db (do
    for g in ← grantsOf s ledger key do
      discard <| revokeGrant s ledger g.realm key
    Db.exec s.db
      s!"DELETE FROM member WHERE ledger = {Db.lit ledger} AND member = {Db.lit key}") .immediate
  return true

/-! ## Invites -/

/--
Whether an ISO timestamp has passed.

Both sides are in the canonical UTC shape — the route normalises what a client
sends before it is stored, and `utcNow` produces the same one — and timestamps
in one fixed-width format sort the way the instants they name do, so ordering
them is a string comparison. That is what lets the lazy sweep be one `DELETE`.
-/
def elapsed (expires now : String) : Bool := decide (expires ≤ now)

/--
Deletes every invite on a ledger whose moment has passed.

Expiry is swept lazily rather than on a timer: an invite is read in exactly three
places, and purging in each of them means a lapsed invite is never *seen* even
though no clock ever goes off.
-/
def purgeExpiredInvites (s : Sequencer) (ledger : String) : IO Unit := do
  let now ← utcNow
  Db.exec s.db s!"DELETE FROM invite
    WHERE ledger = {Db.lit ledger} AND expires <= {Db.lit now}"

/-- Every live invite on a realm; lapsed ones are purged first. -/
def invites (s : Sequencer) (ledger realm : String) : IO (Array Invite) := do
  purgeExpiredInvites s ledger
  let rs ← Db.rows InviteRow s.db s!"SELECT realm, invite_sign_pk, invite_box_pk, wrapped_key,
      generation, role, expires, created_by FROM invite
    WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm} ORDER BY expires, invite_sign_pk"
  return rs.map fun r =>
    { realm := r.realm, signPk := r.signPk, boxPk := r.boxPk,
      wrappedKey := (ofBase64? r.wrappedKey).getD ByteArray.empty,
      generation := r.generation.toInt.toNat, role := r.role, expires := r.expires,
      createdBy := r.createdBy }

/-- One invite, lapsed or not. Whether its moment has passed is the caller's to decide. -/
def invite? (s : Sequencer) (ledger realm signPk : String) : IO (Option Invite) := do
  let rs ← Db.rows InviteRow s.db s!"SELECT realm, invite_sign_pk, invite_box_pk, wrapped_key,
      generation, role, expires, created_by FROM invite
    WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}
      AND invite_sign_pk = {Db.lit signPk}"
  return (rs.map fun r =>
    ({ realm := r.realm, signPk := r.signPk, boxPk := r.boxPk,
       wrappedKey := (ofBase64? r.wrappedKey).getD ByteArray.empty,
       generation := r.generation.toInt.toNat, role := r.role, expires := r.expires,
       createdBy := r.createdBy } : Invite))[0]?

/-- Records an invite. False if one is already outstanding under that key. -/
def putInvite (s : Sequencer) (ledger : String) (i : Invite) : IO Bool := do
  purgeExpiredInvites s ledger
  if (← invite? s ledger i.realm i.signPk).isSome then return false
  let now ← nowStamp
  Db.exec s.db s!"INSERT INTO invite (ledger, realm, invite_sign_pk, invite_box_pk,
      wrapped_key, generation, role, expires, created_by, created_at)
    VALUES ({Db.lit ledger}, {Db.lit i.realm}, {Db.lit i.signPk}, {Db.lit i.boxPk},
            {Db.lit (toBase64 i.wrappedKey)}, {i.generation}, {Db.lit i.role},
            {Db.lit i.expires}, {Db.lit i.createdBy}, {Db.lit now})"
  return true

/-- Withdraws an invite. False if there was none. -/
def deleteInvite (s : Sequencer) (ledger realm signPk : String) : IO Bool := do
  if (← invite? s ledger realm signPk).isNone then return false
  Db.exec s.db s!"DELETE FROM invite WHERE ledger = {Db.lit ledger}
    AND realm = {Db.lit realm} AND invite_sign_pk = {Db.lit signPk}"
  return true

/--
Spends an invite: turns it into membership and a grant, and deletes it.

Everything happens in one immediate transaction for the reason the append does:
each of "the invite is still there", "it is still live", "the realm is still on
its generation" and "this member now holds a grant" is a statement about the
ledger at the moment of the write, and an invite that could be read in one
transaction and spent in another would be a single-use offer that two people
could take.

The proof is not checked here — that is the route layer's job, as it is for an
envelope's signature, because it is the one check that does not need the database
to be consistent with itself.
-/
def spendInvite (s : Sequencer) (ledger realm signPk member : String)
    (wrapped : ByteArray) (signature : String) : IO Joined := do
  let act : IO Joined := do
    let some inv ← invite? s ledger realm signPk | return .unknownInvite
    if elapsed inv.expires (← utcNow) then
      discard <| deleteInvite s ledger realm signPk
      return .expired
    let some rl ← realm? s ledger realm | return .unknownInvite
    -- A revoke since the invite was made has re-keyed the realm, so the key
    -- sealed inside the invite no longer opens anything. Nothing can bring it
    -- back, so the invite goes too.
    if rl.generation != inv.generation then
      discard <| deleteInvite s ledger realm signPk
      return .staleGeneration rl.generation
    if !(← isMember s ledger member) then
      addMember s ledger member (some false)
    let some g ← putGrant s ledger realm member wrapped inv.role member signature
      | return .unknownInvite
    discard <| deleteInvite s ledger realm signPk
    return .ok g
  SQLite.transaction s.db act .immediate

/-! ## The order -/

/-- Where a ledger's chain has got to. An empty ledger has seq 0 and an empty hash. -/
def head (s : Sequencer) (ledger : String) : IO Head := do
  let rs ← Db.rows EnvelopeRow s.db s!"SELECT seq, hash, prev_hash, author, signature
    FROM envelope WHERE ledger = {Db.lit ledger} ORDER BY seq DESC LIMIT 1"
  match rs[0]? with
  | some r => return { seq := r.seq.toInt.toNat, hash := r.hash }
  | none => return {}

/--
Every envelope after `since`, in order, with *all* of their parts.

Filtering parts down to what a caller may see is a decision about that caller and
is made in the route layer; keeping it out of here means the store has exactly one
answer to "what happened after N" and cannot disagree with itself.
-/
def events (s : Sequencer) (ledger : String) (since : Nat) (limit : Nat := 500) :
    IO (Array Envelope) := do
  let envs ← Db.rows EnvelopeRow s.db s!"SELECT seq, hash, prev_hash, author, signature
    FROM envelope WHERE ledger = {Db.lit ledger} AND seq > {since}
    ORDER BY seq LIMIT {limit}"
  -- Bounded by the range the envelope query actually returned — they come back
  -- in order, so the last one is the top of it — or a fetch of one entry would
  -- materialise every part after `since` to find it.
  let some last := envs[envs.size - 1]? | return #[]
  let parts ← Db.rows PartRow s.db s!"SELECT seq, idx, realm, generation, cipher_hash, ciphertext
    FROM part WHERE ledger = {Db.lit ledger} AND seq > {since} AND seq <= {last.seq.toInt.toNat}
    ORDER BY seq, idx"
  return envs.map fun e =>
    { ledger, seq := e.seq.toInt.toNat, prevHash := e.prevHash, author := e.author,
      signature := e.signature, storedHash := e.hash,
      parts := (parts.filter (·.seq == e.seq)).toList.map fun p =>
        { realm := p.realm, generation := p.generation.toInt.toNat,
          ciphertext := (ofBase64? p.ciphertext).getD ByteArray.empty,
          cipherHash := p.cipherHash, visible := true } }

/--
One envelope by position, with all of its parts, or `none` if the ledger has not
reached it.

Filtering is the route layer's job here too, for the same reason: what one entry
is does not depend on who is asking.
-/
def envelope? (s : Sequencer) (ledger : String) (seq : Nat) : IO (Option Envelope) := do
  if seq == 0 then return none
  match (← events s ledger (seq - 1) 1)[0]? with
  | some e => return if e.seq == seq then some e else none
  | none => return none

/--
The stored hash of the envelope at a position.

Position 0 is the empty ledger, whose hash is the empty string, so that a
checkpoint taken before anything was appended has a head to name like any other.
-/
def hashAt (s : Sequencer) (ledger : String) (seq : Nat) : IO (Option String) := do
  if seq == 0 then return some ""
  Db.row? String s.db
    s!"SELECT hash FROM envelope WHERE ledger = {Db.lit ledger} AND seq = {seq}"

/--
Appends an envelope, if it is still the next one.

Membership, grants and the compare-and-swap on the head all happen inside one
immediate transaction, because each of them is a statement about the ledger *at
the moment of the insert*. Checking them outside would leave the gap this whole
service exists to close: two clients that both read the same head and both
believe they are writing entry n.

The signature is not checked here. That is the route layer's job, because it is
the only check that does not need the database to be consistent with itself.
-/
def append (s : Sequencer) (e : Envelope) : IO Appended := do
  -- Computed before the transaction opens: it is a digest of the entry's own
  -- fields, and nothing about the ledger can change it, so there is no reason
  -- to hold the write lock while it runs.
  let hash := e.hash
  let act : IO Appended := do
    if !(← ledgerExists s e.ledger) then return .unknownLedger
    if !(← isMember s e.ledger e.author) then return .notMember
    for p in e.parts do
      let some r ← realm? s e.ledger p.realm
        | return .noGrant p.realm p.generation
      if r.generation != p.generation then
        return .noGrant p.realm p.generation
      let some g ← grant? s e.ledger p.realm e.author
        | return .noGrant p.realm p.generation
      if g.generation != p.generation then
        return .noGrant p.realm p.generation
      -- The role is enforced, not merely carried. Both roles this sequencer
      -- knows may write — holding a realm's key is what writing in it *is* —
      -- so what this refuses is a grant in a role it has never heard of, which
      -- is the only way the field could be read as meaning less than it says.
      if !mayWrite g.role then
        return .badRole p.realm g.role
    let h ← head s e.ledger
    if e.seq != h.seq + 1 || e.prevHash != h.hash then
      return .conflict h
    let now ← nowStamp
    Db.exec s.db s!"INSERT INTO envelope
        (ledger, seq, hash, prev_hash, author, signature, received_at)
      VALUES ({Db.lit e.ledger}, {e.seq}, {Db.lit hash}, {Db.lit e.prevHash},
              {Db.lit e.author}, {Db.lit e.signature}, {Db.lit now})"
    for (p, i) in e.parts.zipIdx do
      Db.exec s.db s!"INSERT INTO part
          (ledger, seq, idx, realm, generation, cipher_hash, ciphertext)
        VALUES ({Db.lit e.ledger}, {e.seq}, {i}, {Db.lit p.realm}, {p.generation},
                {Db.lit p.cipherHash}, {Db.lit (toBase64 p.ciphertext)})"
    return .ok { seq := e.seq, hash }
  SQLite.transaction s.db act .immediate

/-! ## Checkpoints and blobs -/

/-- The columns a checkpoint is read out of, in the order `CheckpointRow` names them. -/
private def checkpointCols : String :=
  "author, generation, seq, state_hash, head_hash, signature, snapshot"

/-- One row as a checkpoint of a named realm. -/
private def ofCheckpointRow (ledger realm : String) (r : CheckpointRow) : Checkpoint :=
  { ledger, realm, author := r.author, generation := r.generation.toInt.toNat,
    seq := r.seq.toInt.toNat, stateHash := r.stateHash, headHash := r.headHash,
    signature := r.signature, snapshot := (ofBase64? r.snapshot).getD ByteArray.empty }

/--
Stores one author's newest checkpoint on a realm, replacing their older one.

There is a row per author, so publishing one is a statement about what *you*
replayed rather than a slot everybody shares. A commitment that stands before
the one already stored under the same name is refused: a checkpoint is only ever
worth something as a claim that moves forward, and a reader who bootstrapped
from a rolled-back one would be handed a state from before everything that has
happened, signed by somebody they were told to trust.
-/
def putCheckpoint (s : Sequencer) (c : Checkpoint) : IO Bool := do
  let now ← nowStamp
  let snapshot := toBase64 c.snapshot
  let act : IO Bool := do
    let previous ← Db.row? Int64 s.db s!"SELECT seq FROM checkpoint
      WHERE ledger = {Db.lit c.ledger} AND realm = {Db.lit c.realm}
        AND author = {Db.lit c.author}"
    if let some p := previous then
      if c.seq < p.toInt.toNat then return false
    Db.exec s.db s!"INSERT INTO checkpoint
        (ledger, realm, author, generation, seq, state_hash, head_hash, signature, snapshot,
         written_at)
      VALUES ({Db.lit c.ledger}, {Db.lit c.realm}, {Db.lit c.author}, {c.generation}, {c.seq},
              {Db.lit c.stateHash}, {Db.lit c.headHash},
              {Db.lit c.signature}, {Db.lit snapshot}, {Db.lit now})
      ON CONFLICT(ledger, realm, author) DO UPDATE SET
        generation = {c.generation}, seq = {c.seq}, state_hash = {Db.lit c.stateHash},
        head_hash = {Db.lit c.headHash}, signature = {Db.lit c.signature},
        snapshot = {Db.lit snapshot}, written_at = {Db.lit now}"
    return true
  SQLite.transaction s.db act .immediate

/-- Every author's newest checkpoint on a realm, furthest along first. -/
def checkpoints (s : Sequencer) (ledger realm : String) : IO (Array Checkpoint) := do
  let rs ← Db.rows CheckpointRow s.db
    s!"SELECT {checkpointCols}
       FROM checkpoint WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}
       ORDER BY seq DESC, author"
  return rs.map (ofCheckpointRow ledger realm)

/-- One author's checkpoint on a realm. -/
def checkpoint? (s : Sequencer) (ledger realm author : String) : IO (Option Checkpoint) := do
  let rs ← Db.rows CheckpointRow s.db
    s!"SELECT {checkpointCols}
       FROM checkpoint WHERE ledger = {Db.lit ledger} AND realm = {Db.lit realm}
         AND author = {Db.lit author}"
  return (rs.map (ofCheckpointRow ledger realm))[0]?

/-- How many bytes of blobs a ledger is holding. -/
def blobBytes (s : Sequencer) (ledger : String) : IO Nat := do
  let total ← Db.scalarInt s.db
    s!"SELECT COALESCE(SUM(size), 0) FROM blob WHERE ledger = {Db.lit ledger}"
  return total.toNat

/-- Whether a ledger already holds a blob under this hash. -/
def blobExists (s : Sequencer) (ledger hash : String) : IO Bool := do
  return (← Db.scalarInt s.db s!"SELECT COUNT(*) FROM blob
    WHERE ledger = {Db.lit ledger} AND hash = {Db.lit hash}") > 0

/-- How a `PUT` of a blob ended. -/
inductive Stored
  /-- Accepted, or already there; how many bytes the ledger holds now. -/
  | ok (held : Nat)
  /-- It would take the ledger past its quota; how many bytes it holds and may hold. -/
  | overQuota (held quota : Nat)
  deriving Inhabited

/--
Stores opaque bytes under the hash of their ciphertext, inside the ledger's
quota. Storing them twice is a no-op.

The quota is checked in the same transaction as the insert, because "how much
does this ledger hold" and "it holds this much more now" are one statement or
they are none: two writers who both read a figure just under the line would
otherwise both be let through. Storing the same hash again costs nothing and is
never refused — the bytes are already paid for.
-/
def putBlob (s : Sequencer) (ledger hash : String) (bytes : ByteArray) (quota : Nat) :
    IO Stored := do
  let now ← nowStamp
  let act : IO Stored := do
    if ← blobExists s ledger hash then return .ok (← blobBytes s ledger)
    let held ← blobBytes s ledger
    if held + bytes.size > quota then return .overQuota held quota
    -- Bound rather than interpolated: a ciphertext contains every byte there
    -- is, including the one that ends a string literal, which is why the
    -- column is a BLOB and this is the one statement here that is prepared.
    Db.execBlob s.db s!"INSERT INTO blob (ledger, hash, bytes, size, written_at)
      VALUES ({Db.lit ledger}, {Db.lit hash}, ?, {bytes.size}, {Db.lit now})
      ON CONFLICT(ledger, hash) DO NOTHING" bytes
    return .ok (held + bytes.size)
  SQLite.transaction s.db act .immediate

/-- The bytes stored under a hash. -/
def blob? (s : Sequencer) (ledger hash : String) : IO (Option ByteArray) := do
  Db.row? ByteArray s.db
    s!"SELECT bytes FROM blob WHERE ledger = {Db.lit ledger} AND hash = {Db.lit hash}"

/--
Removes a blob. False if there was none.

There is no garbage collector: the sequencer cannot read an entry, so it cannot
know which blobs the order still refers to. What it can do is let somebody who
*can* read the order say "that one is finished with", which is why the route
above this is for administrators rather than for whoever uploaded the bytes.

So collection is manual, by design, and the two things that make that workable
are the quota — `Limits.blobQuotaBytes`, which a deployment sets from
`--blob-quota` — and the 507 that names both figures when a ledger reaches it.
-/
def deleteBlob (s : Sequencer) (ledger hash : String) : IO Bool := do
  if !(← blobExists s ledger hash) then return false
  Db.exec s.db
    s!"DELETE FROM blob WHERE ledger = {Db.lit ledger} AND hash = {Db.lit hash}"
  return true

/-- Whether a key administrates any realm of a ledger. -/
def administersAnyRealm (s : Sequencer) (ledger key : String) : IO Bool := do
  return (← Db.scalarInt s.db s!"SELECT COUNT(*) FROM realm
    WHERE ledger = {Db.lit ledger} AND admin = {Db.lit key}") > 0

end Log

end Sync
end Resources
