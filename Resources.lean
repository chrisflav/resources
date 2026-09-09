import Resources.Util
import Resources.Crypto.Sha256
import Resources.Core.Ids
import Resources.Core.Money
import Resources.Core.Ledger
import Resources.Core.Filter
import Resources.Store.Db
import Resources.Store.Repo
import Resources.Core.Settle
import Resources.Store.Pendings
import Resources.Store.Budgets
import Resources.Store.Blob
import Resources.Store.Tokens
import Resources.Import.Csv
import Resources.Import.Profile
import Resources.Import.Staging
import Resources.Invoice.Epc
import Resources.Invoice.Invoice
import Resources.Invoice.Render
import Resources.Api.Wire
import Resources.Api.Routes
import Resources.Api.TsGen
import Resources.Api.Server
import Resources.Cli.Client
import Resources.Cli.Commands

/-!
# Resources

A double-entry ledger for money now and other resources later, built end to end
in Lean: a SQLite store, bank-export importers, an HTTP API, a CLI, receipts and
QR payment requests.

The dependency arrows only point down. `Core` is pure and knows nothing about
storage; `Store` knows nothing about HTTP; `Api.Routes` knows nothing about
sockets, which is why `Api.Server` is the only file that mentions `Std.Http` and
why the CLI's local mode runs the very same route table the server does.
-/
