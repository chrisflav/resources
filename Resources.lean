import Resources.Util
import Resources.Crypto.Sha256
import Resources.Crypto.Sodium
import Resources.Core.Ids
import Resources.Core.Money
import Resources.Core.Ledger
import Resources.Core.View
import Resources.Core.Filter
import Resources.Core.Settle
import Resources.Core.Entities
import Resources.Core.Claim
import Resources.Core.Receipt
import Resources.Core.Payment
import Resources.Core.Invoice
import Resources.Core.State
import Resources.Core.Budgets
import Resources.Core.Event
import Resources.Core.Codec
import Resources.Core.Encode
import Resources.Core.Apply
import Resources.Core.Theorems
import Resources.Core.Commute
import Resources.Store.Db
import Resources.Store.Replay
import Resources.Store.Project
import Resources.Store.Load
import Resources.Store.Commit
import Resources.Store.Repo
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
import Resources.Api.Vectors
import Resources.Api.Server
import Resources.Sync.Protocol
import Resources.Sync.Log
import Resources.Sync.Routes
import Resources.Sync.Server
import Resources.Node.Crypto
import Resources.Node.Identity
import Resources.Node.Keys
import Resources.Node.Envelope
import Resources.Node.Transport
import Resources.Node.Session
import Resources.Node.Checkpoint
import Resources.Node.Blobs
import Resources.Node.Sync
import Resources.Node.Rekey
import Resources.Node.Realms
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
