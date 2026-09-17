import Resources.Cli.Commands

/-!
# `resources`

The command tree. Every leaf delegates to a handler in `Resources.Cli.Commands`,
which in turn goes through `Backend.call` — so the same code runs whether the
CLI is working on the local database or talking to a server.
-/

open Cli Resources.Cli

/-! ## Transactions -/

def txListCmd := `[Cli|
  list VIA runTxList;
  "Lists transactions matching a filter."

  FLAGS:
    f, filter : String; "Filter expression, e.g. \"account:Assets.Bank date>=2026-01-01\"."
    s, sort : String;   "Sort key: date, -date, amount, -amount, payee, created."
    n, limit : String;  "Maximum rows to return (default 50)."
    offset : String;    "Rows to skip, for paging."
    json;               "Print the raw API response."
]

def txAddCmd := `[Cli|
  add VIA runTxAdd;
  "Records a transaction moving an amount between two accounts."

  FLAGS:
    a, amount : String;    "Amount moved, e.g. 49.90EUR or -49,90."
    "from" : String;       "Account the money leaves."
    t, to : String;        "Account the money enters. Omit to book the remainder to --into."
    into : String;         "Counter account when --to is omitted (default Expenses.Unclassified)."
    d, date : String;      "ISO date, or 'today' (the default)."
    p, payee : String;     "Who was paid, or who paid."
    m, narration : String; "What it was for."
    l, label : Array String; "Labels to attach, comma separated."
]

def txShowCmd := `[Cli|
  "show" VIA runTxShow;
  "Shows one transaction in full."

  FLAGS:
    json; "Print the raw API response."

  ARGS:
    id : String; "Transaction id."
]

def txEditCmd := `[Cli|
  edit VIA runTxEdit;
  "Changes the date, payee or narration of a transaction, leaving its postings alone."

  FLAGS:
    d, date : String;      "New ISO date."
    p, payee : String;     "New payee."
    m, narration : String; "New narration."

  ARGS:
    id : String; "Transaction id."
]

def txMoveCmd := `[Cli|
  move VIA runTxMove;
  "Recategorises a transaction by rebooking a posting into another account."

  FLAGS:
    "from" : String; "Which account to move out of. Defaults to the non-bank leg."

  ARGS:
    id : String; "Transaction id."
    to : String; "Account to move the posting into."
]

def txLabelCmd := `[Cli|
  label VIA runTxLabel;
  "Adds or removes labels on a transaction."

  FLAGS:
    a, add : Array String; "Labels to add, comma separated."
    rm : Array String;     "Labels to remove, comma separated."

  ARGS:
    id : String; "Transaction id."
]

def txMergeCmd := `[Cli|
  merge VIA runTxMerge;
  "Combines several transactions into one, for lines the bank posted separately."

  FLAGS:
    m, narration : String;    "Narration for the combined transaction."
    p, payee : String;        "Payee for the combined transaction."
    c, cancel : Array String; "Accounts whose now-redundant legs should drop out, \
                               comma separated (typically Expenses.Unclassified)."

  ARGS:
    ...ids : String; "Transaction ids to combine."
]

def txUnmergeCmd := `[Cli|
  unmerge VIA runTxUnmerge;
  "Splits a merged transaction back into the entries it was built from."

  ARGS:
    id : String; "Transaction id."
]

def txLinkCmd := `[Cli|
  link VIA runTxLink;
  "Finds fee transactions already in the ledger that belong with a purchase, \
   and combines them. Shows what it would do unless --apply is given."

  FLAGS:
    apply;                "Actually perform the merges."
    c, confidence : String; "Only apply pairs at this confidence: high or medium."
]

def txRmCmd := `[Cli|
  rm VIA runTxRm;
  "Deletes a transaction, keeping its revision history."

  ARGS:
    id : String; "Transaction id."
]

def txDivideCmd := `[Cli|
  divide VIA runTxDivide;
  "Divides a payment into the things it paid for, reading them off its receipt. \
   Each group becomes its own transaction against the account the money left; \
   whatever no group claims stays behind as a remainder, which is the usual \
   ending, since lines are read off paper and paper folds."

  FLAGS:
    g, group : Array String; "Lines and where they belong, as '1+2=Account', comma \
                              separated. A line covering several units can be \
                              divided too: '3:10' takes ten of what line 3 covers."

  ARGS:
    id : String; "Transaction id."
]

def txHistoryCmd := `[Cli|
  history VIA runTxHistory;
  "Shows the audit trail of a transaction."

  ARGS:
    id : String; "Transaction id."
]

def txCmd := `[Cli|
  tx NOOP;
  "Transactions."

  SUBCOMMANDS:
    txListCmd; txAddCmd; txShowCmd; txEditCmd; txMoveCmd; txLabelCmd;
    txMergeCmd; txUnmergeCmd; txDivideCmd; txLinkCmd; txRmCmd; txHistoryCmd
]

/-! ## Accounts, labels, parties -/

def accListCmd := `[Cli|
  list VIA runAccList;
  "Lists accounts."
]

def accAddCmd := `[Cli|
  add VIA runAccAdd;
  "Creates an account. The kind is guessed from the top-level path component. \
   An account belongs to you unless --owner says otherwise; somebody else's is \
   an ordinary asset, and the owner is the only thing keeping it out of your \
   net worth."

  FLAGS:
    k, kind : String;      "asset, liability, equity, income or expense."
    o, owner : String;     "Whose account this is, if not yours."
    i, iban : String;      "IBAN, when this mirrors a real bank account."
    c, commodity : String; "Restrict the account to one commodity."
    note : String;         "Free-form note."

  ARGS:
    name : String; "Dotted path, e.g. Assets.Bank.DKB.Giro."
]

def accMergeCmd := `[Cli|
  merge VIA runAccMerge;
  "Rebooks every posting from one account into another and removes the emptied one."

  ARGS:
    "from" : String; "Account to empty."
    into : String;   "Account to move its postings into."
]

def accBalanceCmd := `[Cli|
  balance VIA runAccBalance;
  "Shows balances. With no argument, shows every account."

  FLAGS:
    "at" : String; "Balance as of this ISO date."

  ARGS:
    ...name : String; "Account subtree, e.g. Assets."
]

def accCmd := `[Cli|
  acc NOOP;
  "Accounts and balances."

  SUBCOMMANDS:
    accListCmd; accAddCmd; accMergeCmd; accBalanceCmd
]

def labelListCmd := `[Cli| list VIA runLabelList; "Lists labels." ]

def labelAddCmd := `[Cli|
  add VIA runLabelAdd;
  "Creates a label."

  ARGS:
    name : String; "Label name."
]

def labelCmd := `[Cli|
  label NOOP;
  "Labels."

  SUBCOMMANDS:
    labelListCmd; labelAddCmd
]

def partyListCmd := `[Cli|
  list VIA runPartyList;
  "Lists the counterparties seen in the ledger."
]

def contactBooksCmd := `[Cli|
  books VIA runContactBooks;
  "Lists the address books the desktop contact store holds."
]

def contactsUseCmd := `[Cli|
  use VIA runContactsUse;
  "Chooses where contacts are read from, so nothing has to be edited by hand."

  FLAGS:
    "password-command" : String; "Command that prints the CardDAV password, \
                                  e.g. 'pass show dav'."

  ARGS:
    kind : String;    "eds, files or carddav."
    ...rest : String; "The path, or the URL and username."
]

def contactsCmd := `[Cli|
  contacts VIA runContacts;
  "Lists the contacts your address book offers. Nothing is stored here: point \
   contacts.json at a directory of vCards or a CardDAV collection."

  FLAGS:
    s, search : String; "Only show names containing this."

  SUBCOMMANDS:
    contactBooksCmd; contactsUseCmd
]

def partyCmd := `[Cli|
  party NOOP;
  "Counterparties seen in the ledger. People come from your address book."

  SUBCOMMANDS:
    partyListCmd
]

/-! ## Imports -/

def importFileCmd := `[Cli|
  file VIA runImportFile;
  "Parses a bank export and stages its rows for review."

  FLAGS:
    a, account : String; "The bank account this file belongs to."
    p, profile : String; "Bank profile name, or 'auto' to detect from the header."
    promote;             "Promote every new row immediately, without review."
    "auto-merge";        "Promote immediately, combining rows that are one event."

  ARGS:
    file : String; "Path to the export."
]

def importListCmd := `[Cli| list VIA runImportList; "Lists import batches." ]

def importStagedCmd := `[Cli|
  staged VIA runImportStaged;
  "Lists the staged rows of a batch."

  FLAGS:
    state : String; "Filter by state: new, promoted or ignored."

  ARGS:
    batch : String; "Batch id."
]

def importProposalsCmd := `[Cli|
  proposals VIA runImportProposals;
  "Shows staged rows that look like one event, such as a purchase and its fee."

  ARGS:
    batch : String; "Batch id."
]

def importSuggestCmd := `[Cli|
  suggest VIA runImportSuggest;
  "Sets the account a staged row will be booked into when promoted."

  ARGS:
    id : String;      "Staged row id."
    account : String; "Account to book it into."
]

def importPromoteCmd := `[Cli|
  promote VIA runImportPromote;
  "Turns staged rows into transactions and settles any matching invoices."

  FLAGS:
    id : Array String; "Promote only these staged ids, comma separated."
    "auto-merge";      "Promote each proposed pair as one transaction."
    "as-one";          "Merge everything named by --id into a single transaction."

  ARGS:
    batch : String; "Batch id."
]

def importIgnoreCmd := `[Cli|
  ignore VIA runImportIgnore;
  "Marks staged rows as deliberately not imported."

  ARGS:
    ...ids : String; "Staged row ids."
]

def importCmd := `[Cli|
  «import» NOOP;
  "Importing bank exports."

  SUBCOMMANDS:
    importFileCmd; importListCmd; importStagedCmd; importProposalsCmd;
    importSuggestCmd; importPromoteCmd; importIgnoreCmd
]

/-! ## Rules -/

def ruleListCmd := `[Cli| list VIA runRuleList; "Lists categorisation rules." ]

def ruleAddCmd := `[Cli|
  add VIA runRuleAdd;
  "Creates a rule that categorises matching imports."

  FLAGS:
    a, account : String;     "Account to book the counter posting into."
    l, label : Array String; "Labels to attach, comma separated."
    p, priority : String;    "Higher priority rules match first."

  ARGS:
    name : String;   "Rule name."
    filter : String; "Filter expression the rule matches on."
]

def ruleApplyCmd := `[Cli|
  apply VIA runRuleApply;
  "Runs the rules over transactions already in the ledger, rebooking whatever is \
   still uncategorised. Shows what would change unless --apply is given."

  FLAGS:
    apply; "Actually make the changes."
]

def ruleRmCmd := `[Cli|
  rm VIA runRuleRm;
  "Deletes a rule."

  ARGS:
    id : String; "Rule id or name."
]

def ruleCmd := `[Cli|
  rule NOOP;
  "Categorisation rules."

  SUBCOMMANDS:
    ruleListCmd; ruleAddCmd; ruleApplyCmd; ruleRmCmd
]

/-! ## Receipts -/

def tripNewCmd := `[Cli|
  new VIA runTripNew;
  "Starts a trip: a window of spending somebody else pays for."

  FLAGS:
    "from" : String;  "First day, ISO."
    t, to : String;   "Last day, ISO."
    p, payer : String; "Who is paying for it."

  ARGS:
    name : String; "A name for the trip."
]

def tripListCmd := `[Cli| list VIA runTripList; "Lists trips and what they have cost." ]

def tripSuggestCmd := `[Cli|
  suggest VIA runTripSuggest;
  "Shows spending inside the trip's dates that is not part of it yet."

  FLAGS:
    all; "Add everything suggested, instead of listing it."

  ARGS:
    name : String; "Trip name."
]

def tripAddCmd := `[Cli|
  add VIA runTripAdd;
  "Adds transactions to a trip and claims them against its payer."

  ARGS:
    name : String;   "Trip name."
    ...ids : String; "Transaction ids."
]

def tripDropCmd := `[Cli|
  drop VIA runTripDrop;
  "Removes transactions from a trip."

  ARGS:
    name : String;   "Trip name."
    ...ids : String; "Transaction ids."
]

def tripCmd := `[Cli|
  trip NOOP;
  "Trips: spending somebody else pays for."

  SUBCOMMANDS:
    tripNewCmd; tripListCmd; tripSuggestCmd; tripAddCmd; tripDropCmd
]

def receiptScanCmd := `[Cli|
  scan VIA runReceiptScan;
  "Reads stored receipts: merchant, date and total. Runs the configured text \
   command, which is tesseract by default and works offline."

  ARGS:
    ...shas : String; "Receipts to read. Defaults to every unattached one."
]

def receiptInboxCmd := `[Cli|
  inbox VIA runReceiptInbox;
  "Receipts that are not attached to any transaction yet."
]

def receiptMatchCmd := `[Cli|
  "match" VIA runReceiptMatch;
  "Proposes which transaction each scanned receipt is evidence for."

  FLAGS:
    apply; "Attach the proposed receipts."
]

def receiptCashCmd := `[Cli|
  cash VIA runReceiptCash;
  "Creates the cash transaction a receipt stands for, when nothing on a \
   statement matches it."

  FLAGS:
    "from" : String; "Account the cash came from (default Assets.Cash)."
    into : String;   "Account to book it to (default Expenses.Unclassified)."

  ARGS:
    sha : String; "Receipt hash."
]

def receiptAddCmd := `[Cli|
  add VIA runReceiptAdd;
  "Stores a receipt, optionally attaching it to a transaction."

  FLAGS:
    t, txn : String; "Attach to this transaction."

  ARGS:
    file : String; "File to store."
]

def receiptItemsCmd := `[Cli|
  items VIA runReceiptItems;
  "Shows the priced lines read off a receipt, numbered for 'tx divide'."

  ARGS:
    sha : String; "Receipt hash."
]

def receiptItemAddCmd := `[Cli|
  "item-add" VIA runReceiptItemAdd;
  "Adds a line a scan could not read. The lines may fall short of the receipt \
   total, but never overrun it."

  FLAGS:
    q, qty : String; "How many, when the line says so."

  ARGS:
    sha : String;         "Receipt hash."
    description : String; "What the line is, e.g. 'Rivella rot 1.5 L'."
    amount : String;      "What it cost, e.g. 12.00 or -7.00 for a correction."
]

def receiptItemRmCmd := `[Cli|
  "item-rm" VIA runReceiptItemRm;
  "Drops a line, renumbering the ones after it."

  ARGS:
    sha : String;  "Receipt hash."
    line : String; "Line number, as 'receipt items' shows it."
]

def receiptListCmd := `[Cli| list VIA runReceiptList; "Lists stored receipts." ]

def receiptGcCmd := `[Cli| gc VIA runReceiptGc; "Deletes receipts no transaction references." ]

def receiptCmd := `[Cli|
  receipt NOOP;
  "Receipts."

  SUBCOMMANDS:
    receiptAddCmd; receiptInboxCmd; receiptScanCmd; receiptItemsCmd;
    receiptItemAddCmd; receiptItemRmCmd; receiptMatchCmd;
    receiptCashCmd; receiptListCmd; receiptGcCmd
]

/-! ## Budgets -/

def budgetNewCmd := `[Cli|
  new VIA runBudgetNew;
  "Opens a budget and lends costs into it. The budget account is equity, not an \
   asset: its balance is money you have paid out and not yet decided about, and \
   the part that turns out to be your own share is never coming back."

  FLAGS:
    txn : Array String;   "Costs to lend into it straight away, comma separated."
    among : Array String; "Who shares it, as 'name=account', comma separated. \
                           Recorded now, applied when you close the budget."
    n, note : String;     "What this budget is for."

  ARGS:
    name : String; "Budget name, e.g. Zinalrothorn2026."
]

def budgetListCmd := `[Cli|
  list VIA runBudgetList;
  "Lists budgets. Anything still undivided is money you have laid out and not \
   yet attributed to anybody."
]

def budgetShowCmd := `[Cli|
  "show" VIA runBudgetShow;
  "Shows one budget: where everybody stands, and what has been asked of them."

  ARGS:
    name : String; "Budget name."
]

def budgetContributeCmd := `[Cli|
  contribute VIA runBudgetContribute;
  "Records a cost somebody else paid for out of their own account. Their \
   account is an ordinary asset that happens to belong to them, which is what \
   keeps it out of your net worth while still letting it fund a shared cost."

  FLAGS:
    who : String;       "Who paid."
    amount : String;    "How much they paid."
    "for" : String;     "What it was for."
    account : String;   "Which of their accounts, if not their purse."
    date : String;      "When (default today)."
    payee : String;     "Who it went to."
    commodity : String; "Commodity (default EUR)."

  ARGS:
    name : String; "Budget name."
]

def budgetAmongCmd := `[Cli|
  among VIA runBudgetAmong;
  "Records once who a budget is divided among. Nothing is divided here — \
   `budget close` does that, when you say the weekend is over. Each participant \
   is 'name=account', or 'name=account*weight' for unequal shares; a bare \
   '=account' is your own share, and the account you give is where the money \
   you actually consumed is booked."

  ARGS:
    name : String;      "Budget name."
    ...among : String;  "One 'name=account' per person, e.g. anna= or ben=."
]

def budgetCloseCmd := `[Cli|
  close VIA runBudgetClose;
  "Closes a budget: divides everything still waiting among its participants and \
   raises what that leaves people owing. Nobody can add to a closed budget, \
   including whoever holds a share link. Reopening and closing again writes a \
   *new* division covering only what came in since — the earlier one stands, \
   because somebody was told what they owed on the strength of it."

  FLAGS:
    commodity : String; "Commodity (default EUR)."
    through : String;   "Settle through one person instead of taking the shortest plan."

  ARGS:
    name : String;      "Budget name."
    ...among : String;  "Divide among these instead of the recorded participants."
]

def budgetReopenCmd := `[Cli|
  reopen VIA runBudgetReopen;
  "Reopens a closed budget so more costs can go in. Every division already made \
   stands, and so does every claim raised from one; until you close it again, \
   what everybody was last told remains what they were last told."

  ARGS:
    name : String; "Budget name."
]

def budgetLendCmd := `[Cli|
  lend VIA runBudgetLend;
  "Lends more costs into a budget. This rewrites each transaction in place \
   rather than adding an entry, so the bank leg still reconciles."

  FLAGS:
    txn : Array String; "Transaction ids, comma separated."
    f, filter : String; "Or a filter selecting them."

  ARGS:
    name : String; "Budget name."
]

def budgetAllocateCmd := `[Cli|
  allocate VIA runBudgetAllocate;
  "Divides what a budget is still holding without closing it. `budget close` is \
   the ordinary way in; this is for dividing part-way through, or on a split \
   that differs from the recorded participants."

  FLAGS:
    commodity : String; "Commodity (default EUR)."
    through : String;   "Settle through one person instead of taking the shortest plan."

  ARGS:
    name : String;      "Budget name."
    ...among : String;  "One 'name=account' per person; omit to use `budget among`."
]

def budgetSettleCmd := `[Cli|
  settle VIA runBudgetSettle;
  "Raises the claims that would square a budget, netting off anything already \
   asked for. Refuses while the budget still holds money nobody has been made \
   responsible for, because no set of transfers can settle that."

  FLAGS:
    commodity : String; "Commodity (default EUR)."
    through : String;   "Settle through one person instead of taking the shortest plan."

  ARGS:
    name : String; "Budget name."
]

def budgetCmd := `[Cli|
  budget NOOP;
  "Auxiliary budgets: money lent out of a paying account, divided later."

  SUBCOMMANDS:
    budgetNewCmd; budgetListCmd; budgetShowCmd; budgetAmongCmd; budgetLendCmd;
    budgetContributeCmd; budgetCloseCmd; budgetReopenCmd; budgetAllocateCmd;
    budgetSettleCmd
]

/-! ## Claims -/

def claimsListCmd := `[Cli|
  list VIA runClaimList;
  "Lists claims: transactions that have not happened yet. None of them reaches \
   a balance."

  FLAGS:
    f, filter : String; "Restrict with the filter language."
    all;                "Include claims already settled or voided."
]

def claimsCandidatesCmd := `[Cli|
  candidates VIA runClaimCandidates;
  "Shows entries in the ledger that could have met a claim. A suggestion, not \
   an action: matching on amount and timing is a guess."

  ARGS:
    id : String; "Claim id."
]

def claimsResolveCmd := `[Cli|
  resolve VIA runClaimResolve;
  "Meets a claim against the entry that performed it. A part payment reduces \
   the claim and leaves the rest outstanding."

  ARGS:
    id : String;          "Claim id."
    transaction : String; "The transaction that met it."
]

def claimsVoidCmd := `[Cli|
  void VIA runClaimVoid;
  "Retires a claim that will never be performed. The spending it was raised \
   against stays where it is: somebody consumed it, and not paying does not \
   make it yours — it makes it your loss, which --write-off books to an \
   account of your choosing."

  FLAGS:
    "write-off" : String; "Book the loss here, e.g. Expenses.BadDebt."

  ARGS:
    id : String; "Claim id."
]

def claimsCmd := `[Cli|
  claims NOOP;
  "Claims: what is expected to be paid, and by whom."

  SUBCOMMANDS:
    claimsListCmd; claimsCandidatesCmd; claimsResolveCmd; claimsVoidCmd
]

/-! ## Invoices -/

def invoiceNewCmd := `[Cli|
  new VIA runInvoiceNew;
  "Writes up a budget's outstanding claims as invoices, one per person who \
   owes you. Nothing is divided here and no money moves: `budget allocate` \
   already decided whose the spending was, and this asks for the payment. Your \
   own share gets no invoice — it is not a claim, you bore it when you paid."

  FLAGS:
    b, beneficiary : String; "Name on the SEPA transfer."
    i, iban : String;        "IBAN to be paid into."
    bic : String;            "BIC, optional for SEPA."
    link : String;           "Use a payment URL instead of a SEPA QR code."
    issued : String;         "Issue date (default today)."
    d, due : String;         "Due date (default 14 days out)."
    commodity : String;      "Commodity (default EUR)."
    n, note : String;        "Note printed on the invoice."

  ARGS:
    budget : String; "The budget whose claims to write up."
]

def invoiceListCmd := `[Cli| list VIA runInvoiceList; "Lists invoices." ]

def invoiceShowCmd := `[Cli|
  "show" VIA runInvoiceShow;
  "Shows one invoice."

  FLAGS:
    json; "Print the raw API response."

  ARGS:
    id : String; "Invoice id or number."
]

def invoiceStatusCmd := `[Cli|
  status VIA runInvoiceStatus;
  "Moves an invoice to draft, sent, paid or void."

  ARGS:
    id : String;     "Invoice id or number."
    status : String; "New status."
]

def invoiceDeleteCmd := `[Cli|
  delete VIA runInvoiceDelete;
  "Removes a draft invoice, winding the number back so the sequence has no gap. \
   An invoice already sent must be voided instead — the payer has seen the number."

  ARGS:
    id : String; "Invoice id or number."
]

def invoiceQrCmd := `[Cli|
  qr VIA runInvoiceQr;
  "Prints the payment QR code in the terminal."

  ARGS:
    id : String; "Invoice id or number."
]

def invoicePdfCmd := `[Cli|
  pdf VIA runInvoicePdf;
  "Renders the invoice to PDF."

  FLAGS:
    o, out : String; "Output path."

  ARGS:
    id : String; "Invoice id or number."
]

def invoiceHtmlCmd := `[Cli|
  html VIA runInvoiceHtml;
  "Renders the invoice to HTML on stdout."

  FLAGS:
    o, out : String; "Write to this file instead of stdout."

  ARGS:
    id : String; "Invoice id or number."
]

def invoiceMailCmd := `[Cli|
  mail VIA runInvoiceMail;
  "Builds a mailto: link with the cost overview in the body, addressed to \
   whoever owes it."

  FLAGS:
    "open"; "Hand the link to your mail client instead of printing it."

  ARGS:
    id : String; "Invoice id or number."
]

def invoiceReconcileCmd := `[Cli|
  reconcile VIA runInvoiceReconcile;
  "Settles sent invoices whose reference appears in an imported transaction."
]

def invoiceCmd := `[Cli|
  invoice NOOP;
  "Invoices and payment requests."

  SUBCOMMANDS:
    invoiceNewCmd; invoiceListCmd; invoiceShowCmd; invoiceStatusCmd; invoiceDeleteCmd;
    invoiceQrCmd; invoicePdfCmd; invoiceHtmlCmd; invoiceMailCmd;
    invoiceReconcileCmd
]

/-! ## Reports and tokens -/

def reportPeopleCmd := `[Cli|
  people VIA runReportPeople;
  "Shows what passes between you and everybody else. A positive net is money \
   they owe you; negative is money you owe them. Their accounts carry the \
   figure, so none of it was ever counted as yours."

  FLAGS:
    "open"; "Only show people you are not square with."
    items;  "List the claims that are still outstanding."
]

def reportTrialCmd := `[Cli|
  trial VIA runReportTrial;
  "Checks that every commodity sums to zero across all accounts."
]

def reportMonthlyCmd := `[Cli|
  monthly VIA runReportMonthly;
  "Monthly totals for an account subtree."

  FLAGS:
    a, account : String;   "Account subtree (default Expenses)."
    c, commodity : String; "Commodity (default EUR)."
]

def reportCmd := `[Cli|
  report NOOP;
  "Reports."

  SUBCOMMANDS:
    reportPeopleCmd; reportTrialCmd; reportMonthlyCmd
]

def tokenCreateCmd := `[Cli|
  create VIA runTokenCreate;
  "Mints an API token. The secret is printed once and never stored. With \
   --budget and --for it mints a share link instead: one person, one budget, \
   and a route table of its own, so the accounts it can reach are a property \
   of the token rather than a rule somebody has to remember."

  FLAGS:
    s, scopes : String; "Comma-separated: read, write, import, admin."
    budget : String;    "Make this a share link for one budget."
    "for" : String;     "Who the share link is for."
    expires : String;   "ISO date after which it stops working."

  ARGS:
    name : String; "A name to recognise the token by."
]

def tokenListCmd := `[Cli| list VIA runTokenList; "Lists tokens." ]

def tokenRevokeCmd := `[Cli|
  revoke VIA runTokenRevoke;
  "Revokes a token."

  ARGS:
    id : String; "Token id or name."
]

def tokenCmd := `[Cli|
  token NOOP;
  "API tokens."

  SUBCOMMANDS:
    tokenCreateCmd; tokenListCmd; tokenRevokeCmd
]

/-! ## Top level -/

def serveCmd := `[Cli|
  serve VIA runServe;
  "Runs the HTTP API, and the web client if --web points at built assets."

  FLAGS:
    p, port : String; "Port (default 8087)."
    h, host : String; "Bind address (default 127.0.0.1; anything else needs a TLS proxy)."
    w, web : String;  "Directory of built web-client assets to serve at /."
]

def moveCmd := `[Cli|
  move VIA runMove;
  "Gathers selected spending into one account, creating it if needed. That \
   account is then billable as a unit."

  FLAGS:
    f, filter : String; "Select the transactions to move, instead of listing ids."
    fund;               "Move the funding side instead of what was spent on, making \
                         the target a pot the costs were drawn against. Its balance is \
                         then what is still to be settled, and paying into it clears it."

  ARGS:
    into : String;   "Account to move them into."
    ...ids : String; "Transaction ids, if not using --filter."
]

def splitCmd := `[Cli|
  split VIA runSplit;
  "Shares costs across a group of people, booking each share into an account of \
   theirs. The shares add back to exactly what was paid. Takes ids or a \
   --filter, so a weekend of receipts is one command."

  FLAGS:
    a, among : Array String; "Who to split with, comma separated."
    g, group : String;       "A saved group to split with, instead of --among."
    f, filter : String;      "Select the transactions to split, instead of listing ids."
    "all-theirs";            "You keep no share: the whole lot was fronted for them."

  ARGS:
    ...ids : String; "Transaction ids, if not using --filter."
]

def groupNewCmd := `[Cli|
  new VIA runGroupNew;
  "Saves the people you keep splitting things with."

  FLAGS:
    m, members : Array String; "Who is in it, comma separated."

  ARGS:
    name : String; "A name for the group."
]

def groupListCmd := `[Cli| list VIA runGroupList; "Lists saved groups." ]

def groupRmCmd := `[Cli|
  rm VIA runGroupRm;
  "Deletes a group. The people and what they owe are untouched."

  ARGS:
    name : String; "Group name."
]

def groupCmd := `[Cli|
  group NOOP;
  "Groups of people you share costs with."

  SUBCOMMANDS:
    groupNewCmd; groupListCmd; groupRmCmd
]

def claimCmd := `[Cli|
  claim VIA runClaim;
  "Books transactions as somebody else's spending, into an account of theirs, \
   so they stop counting as yours. The sign of that account says which way the \
   claim runs: positive, they owe you; negative, you owe them."

  FLAGS:
    f, filter : String; "Select the transactions to claim, instead of listing ids."

  ARGS:
    who : String;    "Who owes you, e.g. UniversiteitUtrecht."
    ...ids : String; "Transaction ids, if not using --filter."
]

def tagFeesCmd := `[Cli|
  "tag-fees" VIA runTagFees;
  "Marks every posting that came from a bank fee line, so fees stay countable \
   after they move into somebody else's account."
]

def statusCmd := `[Cli| status VIA runStatus; "Shows which store the CLI is talking to." ]

def migrateCmd := `[Cli|
  migrate VIA runMigrate;
  "Opens the store, applying any pending migrations."
]

def genTypesCmd := `[Cli|
  "gen-types" VIA runGenTypes;
  "Writes TypeScript types for the API, derived from the Lean wire encoders."

  FLAGS:
    o, out : String; "Write here instead of stdout (usually web/src/types.ts)."
]

def apiCmd := `[Cli|
  api VIA runApi;
  "Calls any API route directly."

  FLAGS:
    q, query : Array String; "k=v query parameters, comma separated."
    d, data : String;        "JSON request body."

  ARGS:
    method : String; "GET, POST, PATCH, PUT or DELETE."
    path : String;   "Route below /api/v1, e.g. transactions."
]

def resourcesCmd : Cmd := `[Cli|
  resources NOOP; ["0.1.0"]
  "Administers resources — money now, other resources later — as a double-entry ledger.

   The store is a SQLite file plus a receipts directory, by default under
   $XDG_DATA_HOME/resources. Set RESOURCES_SERVER and RESOURCES_TOKEN, or write
   ~/.config/resources/config.json, to work against a running server instead."

  SUBCOMMANDS:
    txCmd; accCmd; labelCmd; partyCmd; importCmd; ruleCmd; receiptCmd;
    budgetCmd; claimsCmd; invoiceCmd; tripCmd; reportCmd; tokenCmd; moveCmd; splitCmd;
    groupCmd; contactsCmd;
    claimCmd; tagFeesCmd;
    serveCmd; statusCmd; migrateCmd;
    genTypesCmd; apiCmd
]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    resourcesCmd.printHelp
    return 0
  resourcesCmd.validate args
