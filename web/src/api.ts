import type {
  Account,
  Amount,
  ApiToken,
  Attachment,
  Balance,
  ImportBatch,
  Invoice,
  Label,
  Party,
  LineItem,
  Revision,
  Rule,
  Budget,
  Claim,
  Participant,
  Standing,
  StagedEntry,
  Transaction,
  TransactionPage,
} from './types'

/** One counterparty, as `reports/people` describes them. */
export interface PeopleRow {
  party: string
  name: string
  iban: string | null
  email: string | null
  net: number
  netText: string
  accounts: Account[]
  balances: Balance[]
  claims: Claim[]
}

/** What a share link lets its holder see. */
export interface GuestView {
  budget: string
  note: string
  closed: boolean
  you: string
  total: Amount
  undivided: Amount
  costs: {
    id: string
    date: string
    what: string
    amount: Amount
    paidBy: string
    mine: boolean
  }[]
  standings: Standing[]
  claims: {
    id: string
    due: string
    state: string
    amount: Amount
    from: string | null
    to: string | null
  }[]
}

/**
 * The token is kept in localStorage rather than a cookie: the API is a plain
 * bearer-token service, and this way the same browser can point at a local
 * server with no token at all.
 */
const TOKEN_KEY = 'resources.token'

export function getToken(): string {
  try {
    return localStorage.getItem(TOKEN_KEY) ?? ''
  } catch {
    return ''
  }
}

/**
 * A token for this page only, never written to storage.
 *
 * A share link carries its secret in the fragment, and it belongs to whoever
 * opened the link rather than to the browser they opened it in — so it must not
 * outlive the page, and it must not displace the token of somebody who also
 * uses this browser as themselves.
 */
let sessionToken: string | null = null

export function useSessionToken(token: string): void {
  sessionToken = token
}

export function setToken(token: string): void {
  try {
    if (token) localStorage.setItem(TOKEN_KEY, token)
    else localStorage.removeItem(TOKEN_KEY)
  } catch {
    /* private browsing; the session just stays unauthenticated */
  }
}

export class ApiError extends Error {
  constructor(
    message: string,
    readonly status: number,
  ) {
    super(message)
  }
}

async function request<T>(
  method: string,
  path: string,
  opts: {
    query?: Record<string, string>
    body?: unknown
    raw?: BodyInit
    headers?: Record<string, string>
  } = {},
): Promise<T> {
  const query = opts.query
    ? '?' +
      Object.entries(opts.query)
        .filter(([, v]) => v !== '')
        .map(([k, v]) => `${encodeURIComponent(k)}=${encodeURIComponent(v)}`)
        .join('&')
    : ''
  const headers: Record<string, string> = { ...opts.headers }
  const token = sessionToken ?? getToken()
  if (token) headers.authorization = `Bearer ${token}`
  let body: BodyInit | undefined
  if (opts.raw !== undefined) {
    body = opts.raw
  } else if (opts.body !== undefined) {
    headers['content-type'] = 'application/json'
    body = JSON.stringify(opts.body)
  }
  const res = await fetch(`/api/v1/${path}${query}`, { method, headers, body })
  const text = await res.text()
  let payload: unknown = null
  try {
    payload = text ? JSON.parse(text) : null
  } catch {
    payload = text
  }
  if (!res.ok) {
    const message =
      payload && typeof payload === 'object' && 'error' in payload
        ? String((payload as { error: unknown }).error)
        : `request failed with status ${res.status}`
    throw new ApiError(message, res.status)
  }
  return payload as T
}

export const api = {
  health: () =>
    request<{ status: string; schema: number; actor: string; scopes: string }>('GET', 'health'),

  accounts: () => request<Account[]>('GET', 'accounts'),
  // Posting an existing name edits it: the server touches only the fields present.
  // `owner` is how somebody else's account gets into the ledger. It is an
  // ordinary asset; the owner is the only thing keeping it out of your net
  // worth, and the only thing that needs to.
  createAccount: (body: {
    name: string
    kind?: string
    owner?: string
    iban?: string
    commodity?: string
    note?: string
  }) => request<Account>('POST', 'accounts', { body }),
  deleteAccount: (id: string) => request<unknown>('DELETE', `accounts/${id}`),

  labels: () => request<Label[]>('GET', 'labels'),
  // Counterparties seen in the ledger. People come from the address book below.
  parties: () => request<Party[]>('GET', 'parties'),
  // Read straight from wherever contacts already live; nothing is stored here.
  contactBooks: () => request<{ name: string; contacts: number }[]>('GET', 'contacts/books'),
  setContactSource: (body: {
    kind: string
    path?: string
    url?: string
    user?: string
    passwordCommand?: string[]
  }) => request<{ source: string }>('POST', 'contacts/source', { body }),
  contacts: () =>
    request<{
      source: string
      configured: boolean
      items: {
        name: string
        email: string | null
        iban: string | null
        note: string | null
      }[]
    }>('GET', 'contacts'),

  transactions: (query: { filter?: string; sort?: string; limit?: string; offset?: string }) =>
    request<TransactionPage>('GET', 'transactions', {
      query: query as Record<string, string>,
    }),
  transaction: (id: string) => request<Transaction>('GET', `transactions/${id}`),
  createTransaction: (body: unknown) => request<Transaction>('POST', 'transactions', { body }),
  updateTransaction: (id: string, body: unknown) =>
    request<Transaction>('PATCH', `transactions/${id}`, { body }),
  deleteTransaction: (id: string) => request<unknown>('DELETE', `transactions/${id}`),
  revisions: (id: string) => request<Revision[]>('GET', `transactions/${id}/revisions`),
  attach: (id: string, sha256: string) =>
    request<unknown>('POST', `transactions/${id}/attachments`, {
      body: { sha256 },
    }),

  batches: () => request<ImportBatch[]>('GET', 'imports'),
  staged: (batch: string, state?: string) =>
    request<StagedEntry[]>('GET', `imports/${batch}/staged`, {
      query: state ? { state } : {},
    }),
  // Account and file names go in the query string, not in headers: HTTP header
  // values are ASCII, so a file called `Umsatzübersicht.csv` would be rejected
  // by the server's own parser before the request reached a route.
  upload: (file: File, account: string, profile: string) =>
    request<{
      batch: ImportBatch
      profile: string
      staged: StagedEntry[]
      problems: string[]
    }>('POST', 'imports', {
      raw: file,
      query: { account, profile, filename: file.name },
      headers: { 'content-type': 'text/csv' },
    }),
  promote: (batch: string, ids?: string[], merge?: 'auto' | 'true') =>
    request<{ created: string[]; merged: number; settledInvoices: string[] }>(
      'POST',
      `imports/${batch}/promote`,
      { body: { ...(ids ? { ids } : {}), ...(merge ? { merge } : {}) } },
    ),
  proposals: (batch: string) =>
    request<
      {
        parent: StagedEntry
        child: StagedEntry
        reason: string
        confidence: string
      }[]
    >('GET', `imports/${batch}/proposals`),
  mergeTransactions: (ids: string[], narration?: string) =>
    request<Transaction>('POST', 'transactions/merge', {
      body: { ids, ...(narration ? { narration } : {}) },
    }),
  unmergeTransaction: (id: string) =>
    request<Transaction[]>('POST', `transactions/${id}/unmerge`, { body: {} }),
  suggest: (staged: string, account: string) =>
    request<unknown>('POST', `staged/${staged}/suggest`, { body: { account } }),
  ignoreStaged: (ids: string[]) => request<unknown>('POST', 'staged/ignore', { body: { ids } }),

  rules: () => request<Rule[]>('GET', 'rules'),
  createRule: (body: unknown) => request<Rule>('POST', 'rules', { body }),
  deleteRule: (id: string) => request<unknown>('DELETE', `rules/${id}`),

  attachments: () => request<Attachment[]>('GET', 'attachments'),
  putAttachment: (file: File) =>
    request<Attachment>('PUT', 'attachments', {
      raw: file,
      query: { filename: file.name },
      headers: { 'content-type': file.type || 'application/octet-stream' },
    }),
  attachmentUrl: (sha: string) => `/api/v1/attachments/${sha}`,

  invoices: () => request<Invoice[]>('GET', 'invoices'),
  invoice: (id: string) => request<Invoice>('GET', `invoices/${id}`),
  // A shared payment is a loan from the paying account to an auxiliary budget,
  // divided later. Costs can be funded by anybody's money account, which is how
  // other people share one; allocation divides the whole pot and raises the
  // claims that would square it.
  budgets: () => request<Budget[]>('GET', 'budgets'),
  budget: (name: string) =>
    request<{ budget: Budget; items: Transaction[] }>('GET', `budgets/${name}`),
  createBudget: (name: string, transactions: string[], note?: string) =>
    request<{ id: string; name: string; lent: number }>('POST', 'budgets', {
      body: { name, transactions, note },
    }),
  // Records the rule only. Dividing is what closing does.
  setBudgetParticipants: (
    name: string,
    among: { name: string; account: string; weight?: number }[],
  ) =>
    request<{ budget: string; among: Participant[]; undivided: Amount }>(
      'POST',
      `budgets/${name}/among`,
      { body: { among } },
    ),
  // Closing is the moment of decision: it divides everything waiting, asks for
  // what that leaves people owing, and stops anybody adding to it — including
  // whoever holds a share link. Closing again after reopening writes a new
  // division covering only what came in since.
  closeBudget: (
    name: string,
    opts: { among?: { name: string; account: string; weight?: number }[]; through?: string } = {},
  ) =>
    request<{
      budget: string
      closed: boolean
      division: string | null
      standings: Standing[]
      claims: Claim[]
    }>('POST', `budgets/${name}/close`, { body: opts }),
  reopenBudget: (name: string) =>
    request<{ budget: string; closed: boolean }>('POST', `budgets/${name}/reopen`, { body: {} }),
  lendToBudget: (name: string, transactions: string[]) =>
    request<{ budget: string; lent: number }>('POST', `budgets/${name}/lend`, {
      body: { transactions },
    }),
  // Someone else paid for part of it, out of an account of their own.
  contributeToBudget: (
    name: string,
    body: { who: string; amount: string; narration?: string; payee?: string; date?: string },
  ) => request<Transaction>('POST', `budgets/${name}/contribute`, { body }),
  allocateBudget: (
    name: string,
    among: { name: string; account: string; weight?: number }[],
    through?: string,
  ) =>
    request<{ budget: string; txn: string; standings: Standing[]; claims: Claim[] }>(
      'POST',
      `budgets/${name}/allocate`,
      { body: { among, ...(through ? { through } : {}) } },
    ),
  // `through` routes everything via one person instead of taking the shortest
  // plan, which will otherwise ask two people who never dealt with each other
  // to pay one another.
  settleBudget: (name: string, through?: string) =>
    request<{ budget: string; standings: Standing[]; claims: Claim[] }>(
      'POST',
      `budgets/${name}/settle`,
      { body: through ? { through } : {} },
    ),
  deleteBudget: (name: string) => request<unknown>('DELETE', `budgets/${name}`),

  // A claim is a transaction that has not happened. None of them reaches a
  // balance: the server's `posting` view shows only what is posted.
  claims: (query: { filter?: string; all?: string } = {}) =>
    request<Claim[]>('GET', 'claims', { query: query as Record<string, string> }),
  claimCandidates: (id: string) => request<Transaction[]>('GET', `claims/${id}/candidates`),
  resolveClaim: (id: string, transaction: string) =>
    request<Claim>('POST', `claims/${id}/resolve`, { body: { transaction } }),
  // Without `writeOffTo` the claim simply stops being outstanding and their
  // account goes on saying they owe it. With it, the loss is booked to an
  // account of yours — which is what not being paid actually is.
  voidClaim: (id: string, writeOffTo?: string) =>
    request<Claim>('POST', `claims/${id}/void`, {
      body: writeOffTo ? { writeOffTo } : {},
    }),

  // An invoice is a document about a claim: costs already allocated, and the
  // payment that has not happened yet. It never moves money and it never
  // divides anything, so there is nothing to pass but the budget and how you
  // want to be paid.
  createInvoice: (body: unknown) =>
    request<{ count: number; budget: string; items: Invoice[] }>('POST', 'invoices', {
      body,
    }),
  setInvoiceStatus: (id: string, status: string) =>
    request<unknown>('POST', `invoices/${id}/status`, { body: { status } }),
  // Only a draft can go: a number that has been sent is voided, never removed.
  deleteInvoice: (id: string) => request<unknown>('DELETE', `invoices/${id}`),
  reconcile: () =>
    request<{ invoice: string; txn: string }[]>('POST', 'invoices/reconcile', {
      body: {},
    }),
  invoiceQrUrl: (id: string) => `/api/v1/invoices/${id}/qr.svg`,
  invoicePdfUrl: (id: string) => `/api/v1/invoices/${id}/pdf`,

  tokens: () => request<ApiToken[]>('GET', 'tokens'),
  createToken: (name: string, scopes: string) =>
    request<{ token: ApiToken; secret: string; link: string }>('POST', 'tokens', {
      body: { name, scopes },
    }),
  // A share link: one person, one budget, and a route table of its own. The
  // secret goes in the returned link's fragment, so it never reaches a server
  // log or a Referer header.
  createShareLink: (body: { name: string; budget: string; for: string; expires?: string }) =>
    request<{ token: ApiToken; secret: string; link: string }>('POST', 'tokens', { body }),
  revokeToken: (id: string) => request<{ revoked: boolean }>('DELETE', `tokens/${id}`),

  trips: () =>
    request<
      {
        name: string
        starts: string
        ends: string
        payer: string
        label: string
        members: number
        total: Amount
      }[]
    >('GET', 'trips'),
  createTrip: (body: { name: string; starts: string; ends: string; payer: string }) =>
    request<{ name: string; label: string; purse: string }>('POST', 'trips', { body }),
  tripSuggest: (name: string) => request<Transaction[]>('GET', `trips/${name}/suggest`),
  tripMembers: (name: string) => request<Transaction[]>('GET', `trips/${name}/members`),
  tripAdd: (name: string, ids: string[]) =>
    request<{ added: number }>('POST', `trips/${name}/add`, { body: { ids } }),
  tripDrop: (name: string, ids: string[]) =>
    request<{ dropped: number }>('POST', `trips/${name}/drop`, {
      body: { ids },
    }),

  receipts: () =>
    request<
      {
        sha256: string
        mime: string
        origName: string | null
        merchant: string | null
        date: string | null
        total: Amount | null
      }[]
    >('GET', 'receipts'),
  scanReceipt: (sha: string) =>
    request<{
      sha256: string
      merchant: string | null
      date: string | null
      extractor: string
    }>('POST', `receipts/${sha}/extract`),
  receiptProposals: () =>
    request<{ sha256: string; txn: Transaction; reason: string; confidence: string }[]>(
      'GET',
      'receipts/proposals',
    ),
  receiptItems: (sha: string) => request<LineItem[]>('GET', `receipts/${sha}/items`),
  receipt: (sha: string) =>
    request<{
      sha256: string
      total: Amount | null
      headroom: Amount | null
      items: LineItem[]
    }>('GET', `receipts/${sha}`),
  addReceiptItem: (sha: string, body: { description: string; qty?: number; total: string }) =>
    request<LineItem[]>('POST', `receipts/${sha}/items`, { body }),
  removeReceiptItem: (sha: string, line: number) =>
    request<LineItem[]>('DELETE', `receipts/${sha}/items/${line}`),
  divideTransaction: (
    id: string,
    groups: { items: { line: number; qty?: number }[]; into: string }[],
  ) =>
    request<Transaction[]>('POST', `transactions/${id}/divide`, {
      body: { groups },
    }),
  receiptToCash: (sha: string, from: string, into: string) =>
    request<Transaction>('POST', `receipts/${sha}/cash`, {
      body: { from, into },
    }),
  splitTransaction: (id: string, among: string[], keepShare: boolean) =>
    request<Transaction>('POST', `transactions/${id}/split`, {
      body: { among, keepShare },
    }),
  splitMany: (body: {
    ids?: string[]
    filter?: string
    among?: string[]
    group?: string
    keepShare: boolean
  }) =>
    request<{ count: number; among: string[]; items: Transaction[] }>(
      'POST',
      'transactions/split',
      { body },
    ),
  moveMany: (ids: string[], into: string, funding = false) =>
    request<{ into: string; count: number }>('POST', 'transactions/move', {
      body: { ids, into, funding },
    }),
  groups: () => request<{ name: string; members: string[] }[]>('GET', 'groups'),
  createGroup: (name: string, members: string[]) =>
    request<{ name: string; members: string[] }>('POST', 'groups', {
      body: { name, members },
    }),
  invoiceMailto: (id: string) => request<{ mailto: string }>('GET', `invoices/${id}/mailto`),

  // What passes between you and everybody else. Their own accounts carry the
  // figure and its sign says which way it runs; what is outstanding is the
  // claims, each naming one specific thing.
  people: () => request<PeopleRow[]>('GET', 'reports/people'),
  claim: (who: string, filter: string) =>
    request<{ into: string; count: number }>('POST', 'transactions/claim', {
      body: { who, filter },
    }),

  // What a share link can do, and the whole of it. Everything else the API
  // offers answers 404 to a guest token, including routes added later.
  guest: () => request<GuestView>('GET', 'guest'),
  addGuestExpense: (body: {
    amount: string
    narration?: string
    payee?: string
    date?: string
  }) => request<GuestView['costs'][number]>('POST', 'guest/expenses', { body }),
  dropGuestExpense: (id: string) => request<unknown>('DELETE', `guest/expenses/${id}`),

  balances: (at?: string) =>
    request<Balance[]>('GET', 'reports/balances', { query: at ? { at } : {} }),
  trial: () => request<Balance[]>('GET', 'reports/trial'),
  worth: () =>
    request<{ commodity: string; minor: number; text: string }>('GET', 'reports/worth'),
  monthly: (account: string, commodity: string) =>
    request<{ month: string; minor: number }[]>('GET', 'reports/monthly', {
      query: { account, commodity },
    }),
}

/** Formats exact minor units for display. Money never becomes a float. */
export function formatMinor(minor: number, exponent = 2): string {
  const negative = minor < 0
  const n = Math.abs(minor)
  const scale = 10 ** exponent
  const major = Math.floor(n / scale)
  const rest = n % scale
  const frac = exponent === 0 ? '' : '.' + String(rest).padStart(exponent, '0')
  return `${negative ? '-' : ''}${major}${frac}`
}
