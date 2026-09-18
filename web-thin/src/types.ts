/**
 * The ledger's types, hand-written from the Lean sources.
 *
 * Every declaration here mirrors one in `Resources/Core/*.lean`, field for
 * field and in declaration order, because that order *is* the canonical byte
 * format (`Resources/Core/Encode.lean`). Nothing is generated: the thin client
 * has no build-time dependency on Lean, so the only thing keeping the two in
 * step is this file, the fixed byte strings in `codec.test.ts`, and the
 * conformance vectors.
 *
 * Two conventions run through it.
 *
 * *`Nat` is `number`, `Int` is `bigint`.* A natural here is a count, a length
 * or a generation and never approaches 2^53; money is an `Int` and is `bigint`
 * throughout, because a cent lost to a float is a cent lost for good.
 *
 * *Options are `null`, not `undefined`.* `Option α` has two constructors on the
 * wire and exactly one of them is written as absence, so the decoder has to be
 * able to say "present and empty" without relying on a key being missing.
 */

/** `Resources.Date` — `Std.Time.PlainDate`, encoded as year, month, day. */
export interface Date {
  year: number
  month: number
  day: number
}

/** `Resources.Commodity`. */
export interface Commodity {
  code: string
  exponent: number
}

/** `Resources.Amount`. Minor units, exact. */
export interface Amount {
  commodity: Commodity
  minor: bigint
}

/** `Resources.AccountKind`, in declaration order: the tag is the index. */
export type AccountKind = 'asset' | 'liability' | 'equity' | 'income' | 'expense'

export const accountKinds: AccountKind[] = ['asset', 'liability', 'equity', 'income', 'expense']

/** `Resources.Account`. */
export interface Account {
  id: string
  name: string
  kind: AccountKind
  owner: string
  commodity: Commodity | null
  iban: string | null
  note: string | null
  closedOn: Date | null
  realm: string
  bridgeOf: string | null
  posters: string[]
  /**
   * The bridge account, in a realm shared with somebody, that this one mirrors.
   *
   * Set on the private account and pointing at the bridge, this is the only
   * thing that says the two are the same money.
   */
  mirrorOf: string | null
}

/** `Resources.Party`. */
export interface Party {
  id: string
  name: string
  iban: string | null
  email: string | null
  note: string | null
  kind: string
  /** Which realm this person is recorded in. */
  realm: string
}

/** `Resources.Label`. */
export interface Label {
  id: string
  name: string
  colour: string | null
  /** Which realm this label belongs to: the one whose admins decide about it. */
  realm: string
}

/** `Resources.Posting`. */
export interface Posting {
  account: string
  amount: Amount
  party: string | null
  note: string | null
  origin: string | null
  tag: string | null
}

/** `Resources.Provenance`, tagged in declaration order. */
export type Provenance =
  | { kind: 'manual'; actor: string }
  | { kind: 'imported'; batch: string; fingerprint: string }
  | { kind: 'derived'; rule: string }

/** `Resources.TxnState`, in declaration order: the tag is the index. */
export type TxnState = 'posted' | 'pending' | 'settled' | 'void'

export const txnStates: TxnState[] = ['posted', 'pending', 'settled', 'void']

/** `Resources.Transaction`. */
export interface Transaction {
  id: string
  date: Date
  payee: string | null
  narration: string
  state: TxnState
  postings: Posting[]
  labels: string[]
  source: Provenance
  attachments: string[]
  /**
   * Which of the lines printed on its receipt this transaction paid for.
   *
   * `null` is a transaction that has never been divided: whatever its receipt
   * says, it paid for all of it. A part of a division says what it took and the
   * remainder what the parts left, because after the division the receipt is
   * still one page and each part is only some of it. `[]` is therefore a real
   * answer: a remainder that keeps a service charge no line covers paid for
   * nothing that was printed.
   */
  items: LineItem[] | null
}

/** `Resources.Filter`, tagged in declaration order. */
export type Filter =
  | { kind: 'all' }
  | { kind: 'account'; under: string }
  | { kind: 'dateFrom'; d: Date }
  | { kind: 'dateTo'; d: Date }
  | { kind: 'amountFrom'; a: Amount }
  | { kind: 'amountTo'; a: Amount }
  | { kind: 'label'; name: string }
  | { kind: 'party'; name: string }
  | { kind: 'owner'; name: string }
  | { kind: 'payee'; needle: string }
  | { kind: 'text'; needle: string }
  | { kind: 'commodity'; code: string }
  | { kind: 'tag'; name: string }
  | { kind: 'and'; a: Filter; b: Filter }
  | { kind: 'or'; a: Filter; b: Filter }
  | { kind: 'not'; a: Filter }

/** `Resources.PartyGroup`. */
export interface PartyGroup {
  name: string
  members: string[]
  /** Which realm this group belongs to: the one whose admins decide about it. */
  realm: string
}

/** `Resources.Trip`. */
export interface Trip {
  id: string
  name: string
  starts: Date
  ends: Date
  payer: string
  note: string | null
  /** Which realm this trip belongs to. */
  realm: string
}

/** `Resources.Rule`. */
export interface Rule {
  id: string
  name: string
  filterSrc: string
  filter: Filter
  setAccount: string | null
  addLabels: string[]
  setParty: string | null
  priority: bigint
  /** Which realm this rule belongs to: rules drive what an import files where. */
  realm: string
}

/** `Resources.ImportBatch`. */
export interface ImportBatch {
  id: string
  profile: string
  filename: string | null
  account: string | null
  stamp: string
  total: number
  duplicates: number
  /** Which realm this import was recorded in. */
  realm: string
}

/** `Resources.Participant`. */
export interface Participant {
  owner: string
  name: string
  account: string
  weight: number
}

/** `Resources.Budget`. */
export interface Budget {
  id: string
  name: string
  note: string | null
  closed: boolean
}

/** `Resources.Standing`. */
export interface Standing {
  owner: string
  name: string
  amount: Amount
}

/** `Resources.Attachment`. */
export interface Attachment {
  sha256: string
  mime: string
  bytes: number
  origName: string | null
  createdAt: string
  /**
   * The SHA-256 of the ciphertext this file was uploaded as, if it was.
   *
   * The plaintext hash is the name the ledger uses and the name a transaction
   * attaches; this is the name the sequencer files the bytes under, because it
   * is the only one a server that cannot decrypt can check for itself.
   */
  cipherHash: string | null
  /** The per-blob key sealed under a realm key: `realm:generation:base64`. */
  wrappedKey: string | null
}

/** `Resources.LineItem`. */
export interface LineItem {
  description: string
  qty: bigint | null
  amount: Amount
}

/** `Resources.Extracted`. */
export interface Extracted {
  merchant: string | null
  date: Date | null
  total: Amount | null
  items: LineItem[]
  rawText: string
  extractor: string
}

/** `Resources.Receipts.ItemShare`. */
export interface ItemShare {
  line: number
  qty: number | null
}

/** `Resources.Receipts.ItemGroup`. */
export interface ItemGroup {
  items: ItemShare[]
  into: string
}

/** `Resources.PaymentRequest`, tagged in declaration order. */
export type PaymentRequest =
  | { kind: 'epc'; name: string; iban: string; bic: string | null }
  | { kind: 'link'; url: string }

/** `Resources.InvoiceLine`. */
export interface InvoiceLine {
  description: string
  qtyMilli: bigint
  unitPrice: Amount
  taxBp: bigint
}

/** `Resources.InvoiceStatus`, in declaration order: the tag is the index. */
export type InvoiceStatus = 'draft' | 'sent' | 'paid' | 'void'

export const invoiceStatuses: InvoiceStatus[] = ['draft', 'sent', 'paid', 'void']

/** `Resources.Invoice`. */
export interface Invoice {
  id: string
  number: string
  issued: Date
  due: Date
  payerId: string | null
  payerName: string
  commodity: Commodity
  reference: string
  status: InvoiceStatus
  note: string | null
  settledTxn: string | null
  payment: PaymentRequest
  sourceAccount: string | null
  budgetId: string | null
  pendingTxn: string | null
  lines: InvoiceLine[]
}

/** `Resources.RealmRole`, in declaration order: the tag is the index. */
export type RealmRole = 'viewer' | 'admin'

export const realmRoles: RealmRole[] = ['viewer', 'admin']

/** `Resources.Member`. */
export interface Member {
  id: string
  name: string
  party: string
}

/** `Resources.Realm`. Members are sorted by id, as `Realm.withMember` keeps them. */
export interface Realm {
  id: string
  name: string
  members: [string, RealmRole][]
  generation: number
}

/**
 * `Resources.BudgetState`.
 *
 * `realm`, `account` and `label` are written once, by `openBudget`, and every
 * question about the budget goes through them. They are ids rather than names
 * on purpose: a budget used to be found by the name of its equity account and
 * its claims by the name of its label, and a name is something anybody who may
 * write an account or a label can take. An id cannot be squatted.
 */
export interface BudgetState {
  budget: Budget
  participants: Participant[]
  /** The realm the budget lives in: the one whose admins decide about it. */
  realm: string
  /** The equity account that holds it. */
  account: string
  /** The label the claims raised for it carry, when one has been pinned. */
  label: string
}

/** `Resources.InvoiceState`. */
export interface InvoiceState {
  invoice: Invoice
  sources: string[]
  /**
   * The realm the invoice was issued in: the one whose admins decide about it.
   *
   * An invoice record used to have no realm at all, which the per-realm
   * numbering made worse rather than better. The counter is keyed by realm, so
   * an admin of any realm a reader could open could delete a draft issued
   * somewhere else and wind back *their own* realm's counter: the issuing realm
   * kept the burnt number while an unrelated sequence went backwards, and the
   * next invoice there duplicated a number somebody had already been sent. The
   * same door marked any invoice in the ledger `paid` or `void`.
   *
   * Written once, at `issueInvoice`, from the part's realm; every later word
   * about the invoice has to be said in it. Trailing, like every other realm
   * this format added, so a reader of the older shape stops exactly where the
   * newer one carries on.
   */
  realm: string
}

/** `Resources.BlobState`. */
export interface BlobState {
  file: Attachment
  extracted: Extracted
  items: LineItem[]
  /** Who registered these bytes: the member who may say what they contain. */
  registeredBy: string
  /**
   * The realm these bytes were filed in.
   *
   * `registeredBy` used to be realm-blind: whoever first filed a set of bytes
   * kept the right to rewrite what it said from a part in *any* realm they held
   * a key for, including after the receipt had been attached to a transaction in
   * a realm they could not otherwise touch. The realm is written once, at
   * registration — and moved by a `registerBlob` that re-seals a known file,
   * because a receipt filed in one realm and attached to a payment in another
   * has to be readable by the people who can read that payment.
   */
  realm: string
}

/** `Resources.State`: every map keyed by id, iterated in key order. */
export interface State {
  realms: Map<string, Realm>
  members: Map<string, Member>
  accounts: Map<string, Account>
  labels: Map<string, Label>
  parties: Map<string, Party>
  groups: Map<string, PartyGroup>
  trips: Map<string, Trip>
  rules: Map<string, Rule>
  txns: Map<string, Transaction>
  budgets: Map<string, BudgetState>
  invoices: Map<string, InvoiceState>
  blobs: Map<string, BlobState>
  batches: Map<string, ImportBatch>
  counters: Map<string, bigint>
  fingerprints: Set<string>
}

/**
 * `Resources.Op`, tagged in declaration order.
 *
 * The `tag` field is the wire tag, written out rather than derived, so that a
 * renumbering in Lean shows up here as a one-line diff instead of as a silent
 * shift of every constructor after it.
 */
export type Op =
  | { tag: 0; kind: 'createRealm'; realm: Realm }
  | { tag: 1; kind: 'putAccount'; account: Account }
  | { tag: 2; kind: 'mergeAccounts'; from: string; into: string }
  | { tag: 3; kind: 'deleteAccount'; id: string }
  | { tag: 4; kind: 'setAccountRights'; id: string; posters: string[] }
  | { tag: 5; kind: 'setAccountOwner'; id: string; owner: string }
  | { tag: 6; kind: 'putLabel'; label: Label }
  | { tag: 7; kind: 'deleteLabel'; id: string }
  | { tag: 8; kind: 'putParty'; party: Party }
  | { tag: 9; kind: 'putGroup'; group: PartyGroup }
  | { tag: 10; kind: 'deleteGroup'; name: string }
  | { tag: 11; kind: 'putTrip'; trip: Trip }
  | { tag: 12; kind: 'deleteTrip'; name: string }
  | { tag: 13; kind: 'putRule'; rule: Rule }
  | { tag: 14; kind: 'deleteRule'; idOrName: string }
  | { tag: 15; kind: 'putTransaction'; txn: Transaction }
  | { tag: 16; kind: 'deleteTransaction'; id: string }
  | { tag: 17; kind: 'splitTransaction'; id: string; targets: string[]; keepShare: boolean }
  | {
      tag: 18
      kind: 'mergeTransactions'
      ids: string[]
      newId: string
      payee: string | null
      narration: string | null
      cancelIn: string[]
    }
  | { tag: 19; kind: 'unmergeTransaction'; id: string; newIds: string[] }
  | { tag: 20; kind: 'replaceTransaction'; id: string; parts: Transaction[]; kindName: string }
  | { tag: 21; kind: 'divideByItems'; id: string; groups: ItemGroup[]; newIds: string[] }
  | { tag: 22; kind: 'raiseClaim'; txn: Transaction }
  | { tag: 23; kind: 'resolveClaim'; id: string; actual: string; splitId: string }
  | { tag: 24; kind: 'voidClaim'; id: string; writeOff: [string, string, Date] | null }
  | { tag: 25; kind: 'openBudget'; budget: Budget; account: Account }
  | { tag: 26; kind: 'setParticipants'; budget: string; among: Participant[] }
  | { tag: 27; kind: 'contribute'; budget: string; txn: Transaction }
  | {
      tag: 28
      kind: 'allocate'
      budget: string
      among: Participant[]
      commodity: Commodity
      date: Date
      hub: string | null
      txnId: string
      claimIds: string[]
      labelId: string
    }
  | {
      tag: 29
      kind: 'settle'
      budget: string
      commodity: Commodity
      hub: string | null
      due: Date
      claimIds: string[]
      labelId: string
    }
  | {
      tag: 30
      kind: 'closeBudget'
      budget: string
      among: Participant[] | null
      commodity: Commodity
      hub: string | null
      date: Date
      txnId: string
      claimIds: string[]
      labelId: string
    }
  | { tag: 31; kind: 'reopenBudget'; budget: string }
  | { tag: 32; kind: 'deleteBudget'; budget: string }
  | { tag: 33; kind: 'issueInvoice'; invoice: Invoice; sources: string[] }
  | { tag: 34; kind: 'setInvoiceStatus'; id: string; status: InvoiceStatus }
  | { tag: 35; kind: 'settleInvoice'; id: string; txn: string }
  | { tag: 36; kind: 'deleteInvoice'; id: string }
  | { tag: 37; kind: 'registerBlob'; file: Attachment }
  | { tag: 38; kind: 'attach'; txn: string; sha: string }
  | { tag: 39; kind: 'detach'; txn: string; sha: string }
  | { tag: 40; kind: 'recordExtraction'; sha: string; extracted: Extracted }
  | { tag: 41; kind: 'setReceiptLines'; sha: string; items: LineItem[] }
  | { tag: 42; kind: 'forgetBlob'; sha: string }
  | { tag: 43; kind: 'recordImportBatch'; batch: ImportBatch }
  | { tag: 44; kind: 'addMember'; member: Member }
  | { tag: 45; kind: 'removeMember'; id: string }
  | { tag: 46; kind: 'grant'; realm: string; member: string; role: RealmRole; bridge: Account }
  | { tag: 47; kind: 'revoke'; realm: string; member: string }
  | { tag: 48; kind: 'setRole'; realm: string; member: string; role: RealmRole }
  | { tag: 49; kind: 'rotateRealmKey'; realm: string }
  | { tag: 50; kind: 'snapshot'; state: State }
  | { tag: 51; kind: 'payClaim'; claim: string; payment: string; date: Date }

/** `Resources.Part`: one realm's share of an event. */
export interface Part {
  realm: string
  op: Op
}

/** `Resources.Event`: one author's set of parts. */
export interface LedgerEvent {
  id: string
  author: string
  composedAt: string
  basedOn: number
  parts: Part[]
}

/** `Resources.Change`, tagged in declaration order. */
export type Change =
  | { tag: 0; kind: 'realm'; realm: Realm }
  | { tag: 1; kind: 'member'; member: Member }
  | { tag: 2; kind: 'memberDeleted'; id: string }
  | { tag: 3; kind: 'account'; account: Account }
  | { tag: 4; kind: 'accountDeleted'; id: string }
  | { tag: 5; kind: 'label'; label: Label }
  | { tag: 6; kind: 'labelDeleted'; id: string }
  | { tag: 7; kind: 'party'; party: Party }
  | { tag: 8; kind: 'group'; group: PartyGroup }
  | { tag: 9; kind: 'groupDeleted'; name: string }
  | { tag: 10; kind: 'trip'; trip: Trip }
  | { tag: 11; kind: 'tripDeleted'; name: string }
  | { tag: 12; kind: 'rule'; rule: Rule }
  | { tag: 13; kind: 'ruleDeleted'; id: string }
  | { tag: 14; kind: 'txn'; txn: Transaction }
  | { tag: 15; kind: 'txnDeleted'; id: string }
  | { tag: 16; kind: 'budget'; budget: BudgetState }
  | { tag: 17; kind: 'budgetDeleted'; id: string }
  | { tag: 18; kind: 'invoice'; invoice: InvoiceState }
  | { tag: 19; kind: 'invoiceDeleted'; id: string }
  | { tag: 20; kind: 'blob'; blob: BlobState }
  | { tag: 21; kind: 'blobDeleted'; sha: string }
  | { tag: 22; kind: 'batch'; batch: ImportBatch }
  | { tag: 23; kind: 'counter'; name: string; value: bigint }
  | { tag: 24; kind: 'fingerprint'; fp: string }

/** `Resources.Party.selfId`. */
export const selfPartyId = '0000000000000000000000SELF'

/** `Resources.Realm.selfId`. */
export const selfRealmId = '0000000000000000000000SELF'

/** `Resources.Member.selfId`. */
export const selfMemberId = 'self'

/** The tag both legs of a claim carry: `Resources.Pendings.tag`. */
export const claimTag = 'claim'

/* ------------------------------------------------------------------ */
/* Bounds                                                              */
/* ------------------------------------------------------------------ */

/**
 * Everything an operation carries is bounded, because a reader applies what an
 * author sends it and a list whose length the author chose is a list that can
 * be made to exhaust memory. `Resources/Core/Event.lean`, name for name.
 */

/** The most postings one transaction may carry. `Resources.maxPostings`. */
export const maxPostings = 200

/** The most people a budget may be divided among. `Resources.maxParticipants`. */
export const maxParticipants = 100

/** The most lines one receipt may print. `Resources.maxLines`. */
export const maxLines = 500

/** The largest count a receipt line, or a share of one, may claim. `Resources.maxQty`. */
export const maxQty = 100000

/** The largest weight a participant's share may carry. `Resources.maxWeight`. */
export const maxWeight = 10000

/** The longest an identifier or a name may be. `Resources.maxIdLength`. */
export const maxIdLength = 200

/** The longest a narration, a note or a description may be. `Resources.maxTextLength`. */
export const maxTextLength = 2000

/** The most parts any other list an operation carries may have. `Resources.maxParts`. */
export const maxParts = 100000

/* ------------------------------------------------------------------ */
/* The three numbers nothing else bounds                               */
/* ------------------------------------------------------------------ */

/**
 * A list's length is bounded above because a reader has to allocate it. These
 * three are bounded because a reader has to *compute* with them, and each of
 * them is a number whose type says nothing at all.
 *
 * `Resources/Core/Event.lean`, name for name. They are refused in two places
 * and the two are not the same door: `checkBounds` refuses an *operation* that
 * carries one, and the `wellformed` walk in `codec.ts` refuses *bytes* that
 * decode to one — everywhere but inside an `Op`, because an operation is an
 * intent and an intent is refused part by part rather than event by event.
 */

/** The earliest year a date may name. `Resources.minYear`. */
export const minYear = -999999

/** The latest year a date may name. `Resources.maxYear`. */
export const maxYear = 999999

/** The most decimal places a commodity's minor unit may have. `Resources.maxExponent`. */
export const maxExponent = 18

/** The largest magnitude, exclusive, a count of minor units may have. `Resources.maxMinor`. */
export const maxMinor = 1n << 63n
