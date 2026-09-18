import SQLite
import Resources.Core.State
import Resources.Crypto.Sha256

/-!
# Database connection, schema and migrations

One SQLite file plus a sibling `blobs/` directory is the entire persistent
state. Migrations are numbered and gated on `PRAGMA user_version`, applied
inside a transaction so a half-applied schema is not reachable.
-/

open Lean

namespace Resources

/-- Where the data lives. -/
structure Config where
  /-- Root directory; everything else defaults inside it. -/
  dataDir : System.FilePath
  /-- The SQLite file. -/
  dbPath : System.FilePath
  /-- Content-addressed receipt storage. -/
  blobDir : System.FilePath
  deriving Repr, Inhabited

namespace Config

/-- `$RESOURCES_DIR`, else `$XDG_DATA_HOME/resources`, else `~/.local/share/resources`. -/
def default : IO Config := do
  let root ←
    match (← IO.getEnv "RESOURCES_DIR") with
    | some d => pure (System.FilePath.mk d)
    | none =>
      match (← IO.getEnv "XDG_DATA_HOME") with
      | some d => pure (System.FilePath.mk d / "resources")
      | none =>
        let home := (← IO.getEnv "HOME").getD "."
        pure (System.FilePath.mk home / ".local" / "share" / "resources")
  return { dataDir := root, dbPath := root / "resources.db", blobDir := root / "blobs" }

/-- A config rooted at an explicit directory. -/
def atDir (root : System.FilePath) : Config :=
  { dataDir := root, dbPath := root / "resources.db", blobDir := root / "blobs" }

end Config

/--
An open store: a database handle, the paths it was opened from, and the state
those tables are a projection of.

The state is the authoritative copy. Every write applies an operation to it and
then projects what came back into SQL, so the tables can be rebuilt from the
state but never the other way round — which is what makes `Store/Load.lean`'s
round trip a test rather than a convention.

What survives a restart is the `event` table, not the projection: the state is
read out of the tables when the store opens because that is quicker than
replaying, and `Store/Replay.lean` is what says the two agree.
-/
structure Ctx where
  db : SQLite
  cfg : Config
  /-- The ledger as one value: what every operation is applied to. -/
  state : IO.Ref State
  /-- Who is writing. One member for now, and every op is applied on their behalf. -/
  member : MemberId := Member.selfId

/-! ## Files only their owner may read

Everything this program writes down is either the ledger itself or something
that opens it: the database, the receipts beside it, the encrypted identity and
keyring, the bearer token the CLI keeps. None of them is another local user's
business, and a default umask makes every one of them world-readable. So the
modes are set here, in one place, and every writer of a secret goes through
`writeSecret`.

The write is also atomic. A keyring is rewritten whole on every grant, under a
fresh salt and nonce, and a crash between truncating the old one and writing the
new one loses every realm key this node holds. Writing a sibling temporary file
and renaming it over the target cannot leave that state: the rename either
happened or it did not.
-/

namespace Files

/-- 0600: the owner reads and writes, and nobody else has any business here. -/
def ownerOnlyFile : IO.FileRight := { user := { read := true, write := true } }

/-- 0700: the owner may enter the directory, and nobody else may. -/
def ownerOnlyDir : IO.FileRight :=
  { user := { read := true, write := true, execution := true } }

/--
Sets a path's mode, and says nothing when the platform has none to set.

A file whose permissions could not be tightened is still a file the caller
asked for; refusing to write it on a system without POSIX modes would be a
worse answer than writing it.
-/
def restrict (path : System.FilePath) (mode : IO.FileRight) : IO Unit := do
  try
    IO.setAccessRights path mode
  catch _ =>
    pure ()

/-- Creates a directory, and everything above it, that only its owner may enter. -/
def privateDir (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  restrict dir ownerOnlyDir

/-- Writes bytes to a file only its owner may read, atomically. -/
def writeSecretBin (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let dir := path.parent.getD "."
  privateDir dir
  let tmp := dir / s!".{path.fileName.getD "file"}.{← freshId}.tmp"
  IO.FS.writeBinFile tmp bytes
  restrict tmp ownerOnlyFile
  try
    IO.FS.rename tmp path
  catch e =>
    try IO.FS.removeFile tmp catch _ => pure ()
    throw e
  restrict path ownerOnlyFile

/-- Writes text to a file only its owner may read, atomically. -/
def writeSecret (path : System.FilePath) (text : String) : IO Unit :=
  writeSecretBin path text.toUTF8

/--
Tightens the modes of a store's directory and everything the store keeps in it.

Called on the way out of opening a store, because that is the one moment every
one of these paths is known to exist: SQLite makes its own journal files, and a
mode set before they are there sets nothing.
-/
def harden (cfg : Config) : IO Unit := do
  restrict cfg.dataDir ownerOnlyDir
  restrict cfg.blobDir ownerOnlyDir
  let db := cfg.dbPath.toString
  for p in [db, db ++ "-wal", db ++ "-shm"] do
    let path : System.FilePath := p
    if ← path.pathExists then restrict path ownerOnlyFile

end Files

/-! ## Low-level query helpers -/

namespace Db

/--
Re-raises what the database said as something no route will repeat back.

SQLite reports its failures as `IO.userError`, which is the same constructor
every refusal this codebase writes for a caller uses — "that account does not
exist" and "no such column: realm_id" arrive as the same kind of thing, and the
API's catch-all has to answer one with a 400 carrying the sentence and the other
with a 500 carrying nothing. A message is not something to classify on, so the
kind is: anything from underneath is `otherError`, which `Api.handleSafe` treats
as nobody's business but the operator's, while the string is kept intact for the
log and for the command line.
-/
private def internal (act : IO α) : IO α := do
  try
    act
  catch
  | .userError msg => throw (IO.Error.otherError 0 msg)
  | e => throw e

/-- Runs a statement that returns no rows. Accepts multiple statements. -/
def exec (db : SQLite) (sql : String) : IO Unit := internal (SQLite.exec db sql)

/-- Runs a query and collects every row. -/
def rows (α : Type) [SQLite.Row α] (db : SQLite) (sql : String) : IO (Array α) := internal do
  let stmt ← SQLite.prepare db sql
  let mut out : Array α := #[]
  for r in stmt.resultsAs α do
    out := out.push r
  return out

/-- Runs a query expected to return at most one row. -/
def row? (α : Type) [SQLite.Row α] (db : SQLite) (sql : String) : IO (Option α) := do
  let rs ← rows α db sql
  return rs[0]?

/-- Runs a scalar `COUNT`-shaped query. -/
def scalarInt (db : SQLite) (sql : String) : IO Int := do
  match (← row? Int64 db sql) with
  | some n => return n.toInt
  | none => return 0

/--
Runs a statement whose single `?` parameter is a byte string, bound as a BLOB.

Everything else here interpolates its values into the SQL, which is fine for
text and numbers and impossible for bytes: an encoded event contains every byte
there is, including the ones that end a string literal. So this one statement is
prepared and bound, and the bytes reach SQLite as themselves.
-/
def execBlob (db : SQLite) (sql : String) (bytes : ByteArray) : IO Unit := internal do
  let stmt ← SQLite.prepare db sql
  stmt.bindBlob 1 bytes
  stmt.exec

/-- SQL string literal with quotes escaped. -/
def lit (s : String) : String := Filter.sqlLit s

/-- SQL literal for an optional string. -/
def litOpt : Option String → String
  | none => "NULL"
  | some s => lit s

end Db

/-! ## Schema -/

namespace Schema

/--
Numbered migrations. Append only: never edit a migration that has shipped,
add another one.
-/
def migrations : List (Nat × String) := [
  (1, "
CREATE TABLE commodity (
  code TEXT PRIMARY KEY, exponent INTEGER NOT NULL, name TEXT);

CREATE TABLE account (
  id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE, kind TEXT NOT NULL,
  commodity TEXT, iban TEXT, note TEXT, closed_on TEXT);

CREATE TABLE party (
  id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE, iban TEXT, email TEXT, note TEXT);

CREATE TABLE label (
  id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE, colour TEXT);

CREATE TABLE txn (
  id TEXT PRIMARY KEY, date TEXT NOT NULL, payee TEXT, narration TEXT NOT NULL,
  source TEXT NOT NULL, created_at TEXT NOT NULL, updated_at TEXT NOT NULL);

CREATE TABLE posting (
  txn_id TEXT NOT NULL REFERENCES txn(id) ON DELETE CASCADE,
  idx INTEGER NOT NULL,
  account_id TEXT NOT NULL REFERENCES account(id),
  minor INTEGER NOT NULL, commodity TEXT NOT NULL,
  party_id TEXT, note TEXT,
  PRIMARY KEY (txn_id, idx));

CREATE TABLE txn_label (
  txn_id TEXT NOT NULL REFERENCES txn(id) ON DELETE CASCADE,
  label_id TEXT NOT NULL REFERENCES label(id) ON DELETE CASCADE,
  PRIMARY KEY (txn_id, label_id));

CREATE TABLE attachment (
  sha256 TEXT PRIMARY KEY, mime TEXT NOT NULL, bytes INTEGER NOT NULL,
  orig_name TEXT, created_at TEXT NOT NULL);

CREATE TABLE txn_attachment (
  txn_id TEXT NOT NULL REFERENCES txn(id) ON DELETE CASCADE,
  sha256 TEXT NOT NULL REFERENCES attachment(sha256),
  PRIMARY KEY (txn_id, sha256));

CREATE TABLE revision (
  txn_id TEXT NOT NULL, seq INTEGER NOT NULL, at TEXT NOT NULL,
  actor TEXT NOT NULL, kind TEXT NOT NULL, patch TEXT NOT NULL,
  PRIMARY KEY (txn_id, seq));

CREATE TABLE import_batch (
  id TEXT PRIMARY KEY, profile TEXT NOT NULL, filename TEXT,
  account_id TEXT, at TEXT NOT NULL, total INTEGER NOT NULL, duplicates INTEGER NOT NULL);

CREATE TABLE staged_entry (
  id TEXT PRIMARY KEY,
  batch_id TEXT NOT NULL REFERENCES import_batch(id) ON DELETE CASCADE,
  fingerprint TEXT NOT NULL, date TEXT NOT NULL, payee TEXT, purpose TEXT,
  minor INTEGER NOT NULL, commodity TEXT NOT NULL, counter_iban TEXT, bank_ref TEXT,
  state TEXT NOT NULL, suggested_account TEXT, txn_id TEXT);

CREATE UNIQUE INDEX staged_fingerprint ON staged_entry(fingerprint);

CREATE TABLE token (
  id TEXT PRIMARY KEY, name TEXT NOT NULL, hash TEXT NOT NULL, scopes INTEGER NOT NULL,
  created_at TEXT NOT NULL, last_used_at TEXT, expires_at TEXT);

CREATE TABLE rule (
  id TEXT PRIMARY KEY, name TEXT NOT NULL, filter TEXT NOT NULL,
  set_account TEXT, add_labels TEXT, set_party TEXT, priority INTEGER NOT NULL DEFAULT 0);

CREATE TABLE invoice (
  id TEXT PRIMARY KEY, number TEXT NOT NULL UNIQUE, issued TEXT NOT NULL, due TEXT NOT NULL,
  payer_id TEXT, payer_name TEXT NOT NULL, commodity TEXT NOT NULL, reference TEXT NOT NULL,
  status TEXT NOT NULL, note TEXT, settled_txn TEXT, created_at TEXT NOT NULL,
  payment_kind TEXT NOT NULL, payment_data TEXT NOT NULL);

CREATE TABLE invoice_line (
  invoice_id TEXT NOT NULL REFERENCES invoice(id) ON DELETE CASCADE,
  idx INTEGER NOT NULL, description TEXT NOT NULL,
  qty_milli INTEGER NOT NULL, unit_minor INTEGER NOT NULL, tax_bp INTEGER NOT NULL,
  PRIMARY KEY (invoice_id, idx));

CREATE TABLE counter (name TEXT PRIMARY KEY, value INTEGER NOT NULL);

CREATE INDEX posting_account ON posting(account_id, commodity);
CREATE INDEX posting_txn ON posting(txn_id);
CREATE INDEX txn_date ON txn(date DESC);
CREATE INDEX staged_batch ON staged_entry(batch_id, state);
"),
  (2, "
-- Which source entry a posting came from, so merging two bank lines into one
-- transaction stays reversible and still maps onto the statement.
ALTER TABLE posting ADD COLUMN origin TEXT;
CREATE INDEX posting_origin ON posting(origin);
"),
  (3, "
-- What a posting *is*, independently of where it sits. A card fee stays a fee
-- after it moves into a receivable, which no account tree can express: a
-- posting lives in exactly one account, but can have several attributes.
ALTER TABLE posting ADD COLUMN tag TEXT;
CREATE INDEX posting_tag ON posting(tag);
"),
  (4, "
-- Which outlays an invoice is asking to be repaid for. Without this an invoice
-- and the spending behind it are unconnected, and 'have I invoiced this yet?'
-- has no answer.
CREATE TABLE invoice_source (
  invoice_id TEXT NOT NULL REFERENCES invoice(id) ON DELETE CASCADE,
  txn_id TEXT NOT NULL,
  PRIMARY KEY (invoice_id, txn_id));

CREATE INDEX invoice_source_txn ON invoice_source(txn_id);
"),
  (5, "
-- A trip is a named window of spending that somebody else pays for. It is
-- deliberately thin: the label groups the transactions, the receivable holds
-- what is owed, and both already exist.
CREATE TABLE trip (
  id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE,
  starts TEXT NOT NULL, ends TEXT NOT NULL,
  payer TEXT NOT NULL, note TEXT, created_at TEXT NOT NULL);

-- Extracted from a scanned receipt, so a photo can be matched to spending.
ALTER TABLE attachment ADD COLUMN merchant TEXT;
ALTER TABLE attachment ADD COLUMN doc_date TEXT;
ALTER TABLE attachment ADD COLUMN total_minor INTEGER;
ALTER TABLE attachment ADD COLUMN commodity TEXT;
ALTER TABLE attachment ADD COLUMN raw_text TEXT;
ALTER TABLE attachment ADD COLUMN extractor TEXT;
"),
  (6, "
-- The people you keep splitting things with. Saved so the same climbing
-- partners do not have to be retyped for every hut weekend.
CREATE TABLE party_group (
  name TEXT PRIMARY KEY, members TEXT NOT NULL, created_at TEXT NOT NULL);
"),
  (7, "
-- The account an invoice was raised from. Paying it moves money back there, so
-- the account nets to zero once everybody has settled.
ALTER TABLE invoice ADD COLUMN source_account TEXT;
"),
  (8, "
-- A party is two different things wearing one name: a merchant seen on a
-- statement, and a person you might invoice. Imports create hundreds of the
-- first, which makes the second impossible to pick out of a list.
ALTER TABLE party ADD COLUMN kind TEXT NOT NULL DEFAULT 'merchant';

-- Anything that already has a way to reach it was put there on purpose.
UPDATE party SET kind = 'contact' WHERE email IS NOT NULL OR iban IS NOT NULL;

CREATE INDEX party_kind ON party(kind);
"),
  (9, "
-- An auxiliary budget: money already paid out of a real account and not yet
-- attributed to anybody. Its account is equity, not an asset, because a budget
-- balance is not wealth you hold — it is wealth you have parted with and have
-- not yet decided about, and the part that turns out to be your own share is
-- never coming back. Equity keeps net worth honest for the whole window
-- between paying and deciding.
CREATE TABLE budget (
  id TEXT PRIMARY KEY, name TEXT NOT NULL UNIQUE,
  note TEXT, created_at TEXT NOT NULL, closed_at TEXT);

-- One participant's share, decided at allocation time. Yours points at an
-- expense account you chose, theirs at a receivable.
CREATE TABLE budget_share (
  budget_id TEXT NOT NULL REFERENCES budget(id) ON DELETE CASCADE,
  idx INTEGER NOT NULL,
  participant TEXT NOT NULL, mine INTEGER NOT NULL,
  account TEXT NOT NULL, minor INTEGER NOT NULL, commodity TEXT NOT NULL,
  txn_id TEXT NOT NULL,
  PRIMARY KEY (budget_id, idx));

CREATE INDEX budget_share_txn ON budget_share(txn_id);

-- Which share an invoice is the document for. An invoice never moves money;
-- the allocation already did that, and this says which part it speaks about.
ALTER TABLE invoice ADD COLUMN budget_id TEXT;
ALTER TABLE invoice ADD COLUMN share_idx INTEGER;
"),
  (10, "
-- Pots become budgets. An account gathering costs to be divided was never an
-- asset: its balance is money already paid out, and the part that turns out to
-- be your own share is never coming back. Calling it equity keeps net worth
-- true for the whole window between paying and deciding.
UPDATE account SET name = 'Budget.' || substr(name, 12), kind = 'equity'
  WHERE name LIKE 'Assets.Pot.%';

INSERT INTO budget (id, name, note, created_at, closed_at)
  SELECT upper(hex(randomblob(13))), name, NULL, datetime('now'), NULL
  FROM account
  WHERE name LIKE 'Budget.%' AND name NOT IN (SELECT name FROM budget);

-- Settling an invoice under the old machinery was an allocation in all but
-- name: it decided whose a share was. Tagging it says so, and stops it being
-- read back as a cost still waiting to be divided.
UPDATE posting SET tag = 'allocation'
  WHERE tag IS NULL
    AND txn_id IN (SELECT id FROM txn WHERE narration LIKE 'payment of invoice %');
"),
  (11, "
-- Every account belongs to somebody. The five kinds say what an account *is*;
-- they have never said whose it is, and 'asset or liability' has been standing
-- in for 'mine' in every balance-sheet query in the system. Those are two
-- different questions: Alice's bank account is a real-money account, which is
-- how it can fund a cost, and it is not mine, which is why it must never reach
-- my net worth. An owner separates them.
ALTER TABLE account ADD COLUMN owner_id TEXT REFERENCES party(id);

-- The ledger's own owner, at a fixed id so the column can be backfilled in one
-- statement and nothing has to bootstrap 'who am I' at runtime. A party called
-- 'me' that already exists is a merchant seen on a statement; conflating the
-- two is exactly the confusion this migration removes, so this one takes a
-- distinguishable name.
INSERT INTO party (id, name, iban, email, note, kind)
  SELECT '0000000000000000000000SELF',
         CASE WHEN EXISTS (SELECT 1 FROM party WHERE name = 'me')
              THEN 'me (self)' ELSE 'me' END,
         NULL, NULL, NULL, 'self';

UPDATE account SET owner_id = '0000000000000000000000SELF';

CREATE INDEX account_owner ON account(owner_id);

-- Receivables become purses. What you laid out for somebody was never an asset
-- of yours that happens to be named after them: it is their money, spent
-- through your account. Owning the account says that directly, and the sign of
-- the balance goes on meaning exactly what it meant before -- positive, they
-- owe you; negative, you owe them -- without a payable hiding in the asset
-- tree when it turns the other way.
INSERT INTO party (id, name, iban, email, note, kind)
  SELECT upper(hex(randomblob(13))), substr(name, 19), NULL, NULL, NULL, 'contact'
  FROM account
  WHERE name LIKE 'Assets.Receivable._%'
    AND substr(name, 19) NOT IN (SELECT name FROM party);

UPDATE account
  SET owner_id = (SELECT p.id FROM party p WHERE p.name = substr(account.name, 19)),
      name = 'Assets.Purse.' || substr(name, 19)
  WHERE name LIKE 'Assets.Receivable._%';
"),
  (12, "
-- A transaction that has not happened yet. Sending an invoice, or dividing a
-- budget among people who have not paid, produces a claim: a specific, dated,
-- balanced movement that is expected and may still fail to occur. Storing it as
-- a transaction in its own right is what lets a part payment reduce a *named*
-- claim instead of being aged against the oldest outlay by convention.
ALTER TABLE txn ADD COLUMN state TEXT NOT NULL DEFAULT 'posted';
CREATE INDEX txn_state ON txn(state);

-- Imaginary money must not be able to reach a balance, and there are a dozen
-- places that sum postings. Rather than add a condition to each of them and
-- hope none is ever forgotten, the base table takes a new name and `posting`
-- becomes the posted rows: every existing query stays correct without being
-- touched, and anything that wants a pending has to say `posting_all` out loud.
ALTER TABLE posting RENAME TO posting_all;

CREATE VIEW posting AS
  SELECT p.txn_id, p.idx, p.account_id, p.minor, p.commodity,
         p.party_id, p.note, p.origin, p.tag
  FROM posting_all p JOIN txn t ON t.id = p.txn_id
  WHERE t.state = 'posted';
"),
  (13, "
-- Which claim a document is about. An invoice itemises costs that have already
-- happened and asks for a payment that has not; those are two entries, and this
-- is the second one.
ALTER TABLE invoice ADD COLUMN pending_txn TEXT;

-- A share was a denormalised index over the allocation's own postings, and
-- allocation now writes the owner onto the account instead. Reading the legs
-- back is the only description of a share that cannot disagree with the ledger,
-- so the table that could disagree goes.
DROP TABLE budget_share;
ALTER TABLE invoice DROP COLUMN share_idx;

-- A share link: a token authorising one person on one budget. Sharing became a
-- realm later — an invite that hands somebody a key of their own — and nothing
-- reads these two columns any more. They stay because dropping a column is a
-- migration that cannot be undone, and an old row naming a retired link is
-- harmless.
ALTER TABLE token ADD COLUMN owner_id TEXT REFERENCES party(id);
ALTER TABLE token ADD COLUMN budget_id TEXT REFERENCES budget(id);
"),
  (14, "
-- Who a budget is divided among, said once.
--
-- A budget exists because of the gap between paying and knowing whose a cost
-- was. Naming the participants closes that gap in advance: from then on every
-- cost added is booked already divided, the budget account holds nothing, and
-- there is no allocation step to remember. What is left is the case the budget
-- was really for -- money you have paid out and genuinely have not decided
-- about -- which still goes through the account and still waits to be divided.
CREATE TABLE budget_participant (
  budget_id TEXT NOT NULL REFERENCES budget(id) ON DELETE CASCADE,
  idx INTEGER NOT NULL,
  owner_id TEXT NOT NULL REFERENCES party(id),
  account TEXT NOT NULL,
  weight INTEGER NOT NULL DEFAULT 1,
  PRIMARY KEY (budget_id, idx));
"),
  (15, "
-- The lines printed on a receipt, kept as read.
--
-- A bill is one payment but rarely one thing: a hut evening is beds, a round of
-- drinks and a tourist tax, and only the payment reaches the bank. Storing the
-- lines lets the parts be booked where they belong without pretending the bank
-- told you about them. Amounts are signed, because tills print corrections as
-- negative lines, and they are not required to sum to the total -- a service
-- charge, a fold in the paper or a torn corner all leave a remainder, which is
-- the normal case and not an error.
CREATE TABLE attachment_item (
  sha256 TEXT NOT NULL REFERENCES attachment(sha256) ON DELETE CASCADE,
  idx INTEGER NOT NULL,
  description TEXT NOT NULL,
  qty INTEGER,
  minor INTEGER NOT NULL,
  commodity TEXT NOT NULL,
  PRIMARY KEY (sha256, idx));
"),
  (16, "
-- Realms and members, and which realm each account sits in.
--
-- A realm is a set of accounts with one viewer set and one key; a member is an
-- identity that may read and write inside the realms it belongs to. There is
-- exactly one of each to begin with -- you, in your own realm -- and they get
-- tables now rather than when a second person arrives, because the state these
-- tables are a projection of already has them, and a projection cannot hold
-- what the tables cannot.
CREATE TABLE realm (id TEXT PRIMARY KEY, name TEXT NOT NULL, generation INTEGER NOT NULL);

CREATE TABLE member (id TEXT PRIMARY KEY, name TEXT NOT NULL, party_id TEXT NOT NULL);

CREATE TABLE realm_member (
  realm_id TEXT NOT NULL REFERENCES realm(id) ON DELETE CASCADE,
  member_id TEXT NOT NULL REFERENCES member(id) ON DELETE CASCADE,
  role TEXT NOT NULL,
  PRIMARY KEY (realm_id, member_id));

-- Which realm an account belongs to, whose purse it is when it is one, and who
-- else may post to it. The three facts every write right is decided from.
ALTER TABLE account ADD COLUMN realm_id TEXT;
ALTER TABLE account ADD COLUMN bridge_of TEXT;
ALTER TABLE account ADD COLUMN posters TEXT;

INSERT INTO realm (id, name, generation) VALUES ('0000000000000000000000SELF', 'me', 0);

INSERT INTO member (id, name, party_id)
  VALUES ('self', 'me', '0000000000000000000000SELF');

INSERT INTO realm_member (realm_id, member_id, role)
  VALUES ('0000000000000000000000SELF', 'self', 'admin');

UPDATE account SET realm_id = '0000000000000000000000SELF';
"),
  (17, "
-- Where each row that hangs off a transaction or an invoice sits in its list.
--
-- `txn_label`, `txn_attachment` and `invoice_source` project lists: the labels
-- a transaction carries in the order they were put on it, the receipts attached
-- in the order they arrived, the outlays an invoice bills for in the order the
-- budget lists its costs. A composite primary key is a set, and a set read back
-- comes in whatever order the table felt like -- which is a difference between
-- the tables and the state that no amount of care in the writer can close. A
-- position column closes it, exactly as `posting` has always had one.
ALTER TABLE txn_label ADD COLUMN idx INTEGER NOT NULL DEFAULT 0;
ALTER TABLE txn_attachment ADD COLUMN idx INTEGER NOT NULL DEFAULT 0;
ALTER TABLE invoice_source ADD COLUMN idx INTEGER NOT NULL DEFAULT 0;
"),
  (18, "
-- The log, and where it has got to.
--
-- Until now the tables were what survived a restart, and a write was a change to
-- them. From here the event is the write: the bytes below are the canonical
-- encoding of the operations somebody composed, hashed and chained to the event
-- before them, and every ledger table is a cache that `resources rebuild` can
-- throw away and compute again. That is what makes the tables safe to change --
-- a projection may be wrong, and being wrong costs a rebuild rather than the
-- books.
--
-- `hash` is the SHA-256 of `bytes` and `prev_hash` is the previous row's `hash`,
-- with sixty-four zeros before the first, so the chain says what order the
-- events were written in and no row can be edited without saying so.
--
-- The `revision` table stays exactly as it is, and stops growing a history of
-- its own meaning: it is frozen history from before the log, kept because it
-- records who asked for a change under which token, which the log does not yet
-- carry. New writes still append to it, as an audit trail beside the log rather
-- than a second copy of it.
CREATE TABLE event (
  seq INTEGER PRIMARY KEY,
  id TEXT NOT NULL UNIQUE,
  author TEXT NOT NULL,
  composed_at TEXT NOT NULL,
  based_on INTEGER NOT NULL,
  prev_hash TEXT NOT NULL,
  hash TEXT NOT NULL,
  bytes BLOB NOT NULL);

-- One row, holding the end of the chain, so appending does not have to scan it.
CREATE TABLE ledger_head (
  id INTEGER PRIMARY KEY CHECK (id = 1), seq INTEGER NOT NULL, hash TEXT NOT NULL);
"),
  (19, "
-- Which of the local events are on the sequencer, and where.
--
-- NULL is an event this node wrote and has not pushed yet. A positive number is
-- its position in the sequencer's order, and `remote_hash` is the hash of the
-- envelope it arrived in or was accepted as. Zero is an event from before this
-- node joined somebody else's ledger: its own prehistory, which is never pushed,
-- because the ledger it joined already has a past and this one is not it.
--
-- The two chains are different chains, and both are verified. `hash`/`prev_hash`
-- chain the bytes *this node stores*, which for an event from somebody else are
-- the parts it could read; `remote_hash` chains the envelopes the sequencer
-- ordered, which cover parts this node may never see. Neither implies the other,
-- and a node that conflated them would be claiming to have verified a digest of
-- ciphertext it cannot open.
ALTER TABLE event ADD COLUMN remote_seq INTEGER;
ALTER TABLE event ADD COLUMN remote_hash TEXT NOT NULL DEFAULT '';

CREATE INDEX event_remote_seq ON event(remote_seq);
"),
  (20, "
-- What this node has already folded, so that a rebuild does not have to fold it
-- again, and what it has published about a realm.
--
-- A row is a state in canonical bytes, the SHA-256 of those bytes, and the
-- position it stands for. The realm column says *which* state: a realm id is
-- that realm's projection -- the fold of the parts written in it, at a position
-- in the sequencer's order, which is the thing a checkpoint commits to -- and
-- the empty string is the whole of what this node can read, at a position in its
-- own log, which is what `resources rebuild --from-checkpoint` starts from.
--
-- Nothing is deleted when a checkpoint is written. The events before it stay in
-- the log, and the chain still runs through all of them: a snapshot is a shortcut
-- through history, not a replacement for it, and this phase deliberately keeps
-- the long way round available.
CREATE TABLE checkpoint (
  realm TEXT NOT NULL PRIMARY KEY,
  seq INTEGER NOT NULL,
  state_hash TEXT NOT NULL,
  bytes BLOB NOT NULL,
  written_at TEXT NOT NULL);

-- Which realms an entry carried parts for that this node could not open.
--
-- A projection is only worth comparing against another node's when this node
-- read every part of that realm, and the count of unreadable parts is not enough
-- to say so: an entry with a part in a realm this node has no key for says
-- nothing about the realm it does hold. So the realms themselves are recorded,
-- comma separated, and a checkpoint on a realm named here is one this node
-- cannot check rather than one it disagrees with.
ALTER TABLE event ADD COLUMN unreadable_realms TEXT NOT NULL DEFAULT '';

-- The same file as the sequencer holds it: the hash of the ciphertext uploaded
-- under it, and the per-blob key sealed under a realm key. Both are NULL for a
-- file that never left this machine, which is every file a local-only store has.
ALTER TABLE attachment ADD COLUMN cipher_hash TEXT;
ALTER TABLE attachment ADD COLUMN wrapped_key TEXT;
"),
  (21, "
-- The three ids a budget is keyed to, written once when it is opened: the realm
-- whose admins decide about it, the equity account that holds it, and the label
-- its claims carry. They used to be found by name, and a name is something
-- anybody who may write an account or a label can take.
--
-- Rows written before this column existed name nothing, which is what a budget
-- opened by an older binary looks like; the projection writes all three from
-- then on.
ALTER TABLE budget ADD COLUMN realm_id TEXT NOT NULL DEFAULT '';
ALTER TABLE budget ADD COLUMN account_id TEXT NOT NULL DEFAULT '';
ALTER TABLE budget ADD COLUMN label_id TEXT NOT NULL DEFAULT '';
"),
  (22, "
-- Which realm each of the remaining entities is in, and who filed a receipt.
--
-- Eight kinds of entry used to have no realm at all -- labels, people, groups,
-- trips, rules, import batches and stored receipts -- so 'an admin of the part's
-- realm' reached across every realm a reader could open: deleting a label
-- stripped it from every transaction in the ledger, a party record could be
-- rewritten from anywhere, and whoever first registered a receipt could go on
-- saying what it contained from a realm the payment had never been in. The state
-- now says where each of them lives, and the projection has to say so too, or a
-- store reopened would hand every one of them back in the realm it belongs to.
--
-- `registered_by` is the same story read from the other side: the member who
-- filed the bytes is half of who may speak about them, and it was in the state
-- and not in the tables.
--
-- Rows written before this column existed are the self realm's, which is what a
-- single-realm ledger has always been.
ALTER TABLE label ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE party ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE party_group ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE trip ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE rule ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE import_batch ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE attachment ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
ALTER TABLE attachment ADD COLUMN registered_by TEXT NOT NULL DEFAULT 'self';
"),
  (23, "
-- The realms an entry's unreadable parts were in, one row per realm.
--
-- Migration 20 wrote the same fact into `event.unreadable_realms` as a comma
-- separated list, and asked about it with
-- `(',' || unreadable_realms || ',') LIKE '%,' || realm || ',%'`. Two things are
-- wrong with that, and both turn 'this node missed a part in realm R' into a
-- silent 'it did not' -- which is precisely the flag that stops a node it was
-- revoked from raising a false checkpoint mismatch. A realm id containing a
-- comma splits into two names that are neither of them the realm; and `%` and
-- `_` are wildcards in a `LIKE` pattern, with no `ESCAPE` clause, so a realm
-- whose id contains `_` matches the name of any other realm differing in that
-- one character. Ids from `freshId` contain neither, so nothing has ever been
-- wrong in practice -- but the list is written from parts an untrusted
-- sequencer relays, and the realm ids in them are whatever a member typed.
--
-- A row per realm asks the question with `=` instead, where a realm id is a
-- value and not a pattern. `seq` is the local event's own position, the one
-- `event.seq` carries, so the join to `event.remote_seq` is what says which
-- entries of the shared order a gap falls in.
--
-- `event.unreadable_realms` stays where it is, because a migration that dropped
-- a column would rewrite the table under a store an older binary may still open,
-- and nothing reads it from here on: the rows below are the record.
CREATE TABLE event_unreadable (
  seq INTEGER NOT NULL,
  realm TEXT NOT NULL,
  PRIMARY KEY (seq, realm));

CREATE INDEX event_unreadable_realm ON event_unreadable(realm);

-- What the column already holds, split on commas. A trailing comma is appended
-- so that every name in the list ends with one, and the walk is then the same
-- step each time: take up to the first comma, keep the rest.
INSERT OR IGNORE INTO event_unreadable (seq, realm)
WITH RECURSIVE split(seq, realm, rest) AS (
  SELECT seq, '', unreadable_realms || ',' FROM event WHERE unreadable_realms <> ''
  UNION ALL
  SELECT seq, substr(rest, 1, instr(rest, ',') - 1), substr(rest, instr(rest, ',') + 1)
    FROM split WHERE rest <> '')
SELECT seq, realm FROM split WHERE realm <> '';
"),
  (24, "
-- The realm an invoice was issued in.
--
-- The last entry kind with no realm, and the per-realm invoice counter made that
-- worse rather than better: the counter is keyed by realm, so an admin of any
-- realm a reader could open could delete a draft issued somewhere else and wind
-- back their own realm's sequence -- the issuing realm kept the burnt number
-- while an unrelated one went backwards and duplicated a number already sent.
-- The same door marked any invoice in the ledger paid or void.
--
-- Rows written before this column existed are the self realm's, which is what a
-- single-realm ledger has always been.
ALTER TABLE invoice ADD COLUMN realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF';
"),
  (25, "
-- A name belongs to an account inside a realm, not across the ledger.
--
-- `account.name` has been unique over the whole table since the first
-- migration, when there was one realm and the two statements were the same
-- statement. Realms made them different, and only the state noticed:
-- `accountByNameIn?` is what every by-name lookup goes through, because a name
-- is something anybody who may write an account can take and the answer is only
-- an answer inside a realm. The projection went on refusing the second row. So a
-- realm arriving from a sequencer whose budget is called what one here is called
-- could be applied to the state and then not written down -- the commit failed
-- with `UNIQUE constraint failed: account.name`, which is a 500 about a ledger
-- that is perfectly well formed, and the tables are the copy that is allowed to
-- be rebuilt.
--
-- SQLite cannot alter a constraint, so the table is rebuilt, and the order it is
-- rebuilt in is the whole of this migration. `posting_all.account_id` references
-- `account` by name, and `PRAGMA foreign_keys` is on before the first migration
-- runs, which rules out both of the obvious orders. Renaming the old table out
-- of the way takes the postings with it -- a rename rewrites the references
-- other tables make to the table renamed -- so they end up pointing at the very
-- table that is about to be dropped. Dropping it first and renaming the new one
-- into its place leaves the postings pointing at the right name and still fails,
-- because a deferred violation is settled by a parent row arriving and not by a
-- table appearing under the name.
--
-- So the table keeps its name and the rows are what move. They are put aside in
-- a scratch table with no constraints of its own, the old table is dropped, the
-- new one is made under the same name, and the rows go back into it. Foreign
-- keys are deferred for the length of that, because `PRAGMA foreign_keys = OFF`
-- does nothing inside a transaction and the drop orphans every posting until the
-- refill -- which is what settles the check, and why it belongs in this
-- transaction rather than a migration after it.
--
-- `realm_id` becomes NOT NULL on the way through. Migration 16 filled every row
-- and the projection has written it on every row since, but NULL is a value no
-- two rows collide on, and a NULL realm would be the one way a duplicate could
-- still walk past the constraint this migration exists to add.
PRAGMA defer_foreign_keys = ON;

CREATE TABLE account_rebuild AS SELECT * FROM account;

DROP TABLE account;

CREATE TABLE account (
  id TEXT PRIMARY KEY, name TEXT NOT NULL, kind TEXT NOT NULL,
  commodity TEXT, iban TEXT, note TEXT, closed_on TEXT,
  owner_id TEXT REFERENCES party(id),
  realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF',
  bridge_of TEXT, posters TEXT,
  UNIQUE (realm_id, name));

INSERT INTO account
  (id, name, kind, commodity, iban, note, closed_on, owner_id, realm_id, bridge_of, posters)
  SELECT id, name, kind, commodity, iban, note, closed_on, owner_id,
         COALESCE(realm_id, '0000000000000000000000SELF'), bridge_of, posters
  FROM account_rebuild;

DROP TABLE account_rebuild;

CREATE INDEX account_owner ON account(owner_id);
"),
  (26, "
-- The same statement about a person: a name belongs to a party inside a realm.
--
-- Migration 25 said it about accounts and left five tables behind it, all of
-- which grew a realm in migration 22 or 24 and kept the ledger-wide `UNIQUE` the
-- first migration gave them, when there was one realm and the two statements
-- were the same statement. Nothing in `Core/Apply.lean` refuses a duplicate name
-- any more -- `ofThisRealm?` made names realm-local on purpose -- so the
-- constraint is the only thing still forcing global uniqueness, and it does it
-- from inside the projection's transaction: a realm arriving from a sequencer
-- with a party called what one here is called is applied to the state and then
-- cannot be written down, which stops the pull rather than the entry. Any member
-- of any realm this node reads can cause it by naming somebody 'Bo'.
--
-- The shape is migration 25's, and so is the order, for the reason set out
-- there: SQLite cannot alter a constraint, a rename would take the references
-- other tables make with it, and a table appearing under a name does not settle
-- a deferred violation. So the rows move and the table keeps its name -- aside
-- into a scratch table with no constraints, drop, create, refill, drop the
-- scratch -- with foreign keys deferred for the length of it, because the drop
-- orphans every account, participant and token that names a party until the
-- refill, and that refill is what settles the check.
PRAGMA defer_foreign_keys = ON;

CREATE TABLE party_rebuild AS SELECT * FROM party;

DROP TABLE party;

CREATE TABLE party (
  id TEXT PRIMARY KEY, name TEXT NOT NULL, iban TEXT, email TEXT, note TEXT,
  kind TEXT NOT NULL DEFAULT 'merchant',
  realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF',
  UNIQUE (realm_id, name));

INSERT INTO party (id, name, iban, email, note, kind, realm_id)
  SELECT id, name, iban, email, note, kind,
         COALESCE(realm_id, '0000000000000000000000SELF')
  FROM party_rebuild;

DROP TABLE party_rebuild;

CREATE INDEX party_kind ON party(kind);
"),
  (27, "
-- A label's name, the same way, and with one difference that matters.
--
-- `txn_label.label_id` references `label(id)` ON DELETE CASCADE, and a DROP
-- TABLE with foreign keys on performs an implicit DELETE FROM first -- which
-- fires that cascade and takes every transaction's labels with it.
-- `defer_foreign_keys` defers the *check* and not the *action*, so deferring is
-- no protection here. The rows that hang off the table being rebuilt are
-- therefore put aside beside it and put back afterwards, in the same
-- transaction: the parent first, then the children, so that what the cascade
-- deleted is exactly what the refill restores.
PRAGMA defer_foreign_keys = ON;

CREATE TABLE label_rebuild AS SELECT * FROM label;
CREATE TABLE txn_label_rebuild AS SELECT * FROM txn_label;

DROP TABLE label;

CREATE TABLE label (
  id TEXT PRIMARY KEY, name TEXT NOT NULL, colour TEXT,
  realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF',
  UNIQUE (realm_id, name));

INSERT INTO label (id, name, colour, realm_id)
  SELECT id, name, colour, COALESCE(realm_id, '0000000000000000000000SELF')
  FROM label_rebuild;

INSERT INTO txn_label (txn_id, label_id, idx)
  SELECT txn_id, label_id, idx FROM txn_label_rebuild;

DROP TABLE label_rebuild;
DROP TABLE txn_label_rebuild;
"),
  (28, "
-- A trip's name. Nothing references `trip`, so this is the plain form of the
-- rebuild: aside, drop, create, refill.
PRAGMA defer_foreign_keys = ON;

CREATE TABLE trip_rebuild AS SELECT * FROM trip;

DROP TABLE trip;

CREATE TABLE trip (
  id TEXT PRIMARY KEY, name TEXT NOT NULL,
  starts TEXT NOT NULL, ends TEXT NOT NULL,
  payer TEXT NOT NULL, note TEXT, created_at TEXT NOT NULL,
  realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF',
  UNIQUE (realm_id, name));

INSERT INTO trip (id, name, starts, ends, payer, note, created_at, realm_id)
  SELECT id, name, starts, ends, payer, note, created_at,
         COALESCE(realm_id, '0000000000000000000000SELF')
  FROM trip_rebuild;

DROP TABLE trip_rebuild;
"),
  (29, "
-- A budget's name, with its participants put aside: `budget_participant` hangs
-- off `budget` ON DELETE CASCADE exactly as `txn_label` hangs off `label`.
-- `token.budget_id` does not cascade and is settled by the refill instead.
--
-- `realm_id` keeps the empty default migration 21 gave it rather than the self
-- realm's id. A budget opened by a binary older than 21 names no realm, and
-- saying it named the self realm would be this migration deciding something
-- about a row it cannot know -- while the names of those rows cannot collide
-- with each other, because `name` was unique across the whole table when they
-- were written.
PRAGMA defer_foreign_keys = ON;

CREATE TABLE budget_rebuild AS SELECT * FROM budget;
CREATE TABLE budget_participant_rebuild AS SELECT * FROM budget_participant;

DROP TABLE budget;

CREATE TABLE budget (
  id TEXT PRIMARY KEY, name TEXT NOT NULL,
  note TEXT, created_at TEXT NOT NULL, closed_at TEXT,
  realm_id TEXT NOT NULL DEFAULT '', account_id TEXT NOT NULL DEFAULT '',
  label_id TEXT NOT NULL DEFAULT '',
  UNIQUE (realm_id, name));

INSERT INTO budget (id, name, note, created_at, closed_at, realm_id, account_id, label_id)
  SELECT id, name, note, created_at, closed_at,
         COALESCE(realm_id, ''), COALESCE(account_id, ''), COALESCE(label_id, '')
  FROM budget_rebuild;

INSERT INTO budget_participant (budget_id, idx, owner_id, account, weight)
  SELECT budget_id, idx, owner_id, account, weight FROM budget_participant_rebuild;

DROP TABLE budget_rebuild;
DROP TABLE budget_participant_rebuild;
"),
  (30, "
-- An invoice's *number*, which is the one of these five where the collision is
-- not an accident but the design.
--
-- The counter an invoice number is drawn from is keyed by realm, so two realms
-- mint '2026-0001' as a matter of course, and `invoice.number UNIQUE` across the
-- ledger means the second one to be projected aborts the transaction it arrives
-- in. A node reading two realms therefore stops syncing the first time both of
-- them issue their first invoice of the year.
--
-- `invoice_line` and `invoice_source` both hang off `invoice` ON DELETE CASCADE,
-- so both are put aside and put back; `invoice_source_txn` is an index on
-- `invoice_source`, which is not dropped, and survives.
PRAGMA defer_foreign_keys = ON;

CREATE TABLE invoice_rebuild AS SELECT * FROM invoice;
CREATE TABLE invoice_line_rebuild AS SELECT * FROM invoice_line;
CREATE TABLE invoice_source_rebuild AS SELECT * FROM invoice_source;

DROP TABLE invoice;

CREATE TABLE invoice (
  id TEXT PRIMARY KEY, number TEXT NOT NULL, issued TEXT NOT NULL, due TEXT NOT NULL,
  payer_id TEXT, payer_name TEXT NOT NULL, commodity TEXT NOT NULL, reference TEXT NOT NULL,
  status TEXT NOT NULL, note TEXT, settled_txn TEXT, created_at TEXT NOT NULL,
  payment_kind TEXT NOT NULL, payment_data TEXT NOT NULL, source_account TEXT,
  budget_id TEXT, pending_txn TEXT,
  realm_id TEXT NOT NULL DEFAULT '0000000000000000000000SELF',
  UNIQUE (realm_id, number));

INSERT INTO invoice
  (id, number, issued, due, payer_id, payer_name, commodity, reference, status, note,
   settled_txn, created_at, payment_kind, payment_data, source_account, budget_id,
   pending_txn, realm_id)
  SELECT id, number, issued, due, payer_id, payer_name, commodity, reference, status, note,
         settled_txn, created_at, payment_kind, payment_data, source_account, budget_id,
         pending_txn, COALESCE(realm_id, '0000000000000000000000SELF')
  FROM invoice_rebuild;

INSERT INTO invoice_line (invoice_id, idx, description, qty_milli, unit_minor, tax_bp)
  SELECT invoice_id, idx, description, qty_milli, unit_minor, tax_bp
  FROM invoice_line_rebuild;

INSERT INTO invoice_source (invoice_id, txn_id, idx)
  SELECT invoice_id, txn_id, idx FROM invoice_source_rebuild;

DROP TABLE invoice_rebuild;
DROP TABLE invoice_line_rebuild;
DROP TABLE invoice_source_rebuild;
")
]

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
      Db.exec db s!"PRAGMA user_version = {v}"
  return pending.length

end Schema

/-! ## Working with an open store

Opening one is `Store/Load.lean`: a `Ctx` carries the state the tables project,
and reading that state back out of them is what `Load.fromDb` does.
-/

namespace Ctx

/-- Runs `act` inside a database transaction. -/
def transaction (ctx : Ctx) (act : IO α) : IO α :=
  SQLite.transaction ctx.db act .immediate

/--
Runs `act` inside a database transaction, unless one is already open.

SQLite has no nested transactions, and a commit is now reached from inside
callers that had already opened one — writing an invoice ensures its payer, and
ensuring anything is a commit. Joining the transaction already in progress is
the honest reading of what those callers meant: one atomic step, whoever began
it.
-/
def atomically (ctx : Ctx) (act : IO α) : IO α := do
  if ← SQLite.inTransaction ctx.db then act else ctx.transaction act

/-- Allocates the next value of a named counter, inside the caller's transaction. -/
def nextCounter (ctx : Ctx) (name : String) : IO Int := do
  Db.exec ctx.db s!"INSERT INTO counter (name, value) VALUES ({Db.lit name}, 0)
                    ON CONFLICT(name) DO NOTHING"
  Db.exec ctx.db s!"UPDATE counter SET value = value + 1 WHERE name = {Db.lit name}"
  Db.scalarInt ctx.db s!"SELECT value FROM counter WHERE name = {Db.lit name}"

end Ctx

end Resources
