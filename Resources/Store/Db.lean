import SQLite
import Resources.Core.Filter
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

/-- An open store: a database handle plus the paths it was opened from. -/
structure Ctx where
  db : SQLite
  cfg : Config

/-! ## Low-level query helpers -/

namespace Db

/-- Runs a statement that returns no rows. Accepts multiple statements. -/
def exec (db : SQLite) (sql : String) : IO Unit := SQLite.exec db sql

/-- Runs a query and collects every row. -/
def rows (α : Type) [SQLite.Row α] (db : SQLite) (sql : String) : IO (Array α) := do
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

-- A share link. The token authorises one person on one budget, which makes the
-- reachable set of accounts a property of the token rather than a list of
-- routes somebody has to remember to keep in step.
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

/-! ## Opening the store -/

namespace Ctx

/-- Opens (creating if needed) the store at `cfg`, running any pending migrations. -/
def «open» (cfg : Config) : IO Ctx := do
  IO.FS.createDirAll cfg.dataDir
  IO.FS.createDirAll cfg.blobDir
  let db ← SQLite.open cfg.dbPath (busyTimeoutMs := 5000)
  Db.exec db "PRAGMA journal_mode = WAL"
  Db.exec db "PRAGMA foreign_keys = ON"
  Db.exec db "PRAGMA synchronous = NORMAL"
  discard <| Schema.migrate db
  return { db, cfg }

/-- Runs `act` inside a database transaction. -/
def transaction (ctx : Ctx) (act : IO α) : IO α :=
  SQLite.transaction ctx.db act .immediate

/-- Allocates the next value of a named counter, inside the caller's transaction. -/
def nextCounter (ctx : Ctx) (name : String) : IO Int := do
  Db.exec ctx.db s!"INSERT INTO counter (name, value) VALUES ({Db.lit name}, 0)
                    ON CONFLICT(name) DO NOTHING"
  Db.exec ctx.db s!"UPDATE counter SET value = value + 1 WHERE name = {Db.lit name}"
  Db.scalarInt ctx.db s!"SELECT value FROM counter WHERE name = {Db.lit name}"

end Ctx

end Resources
