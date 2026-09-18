/**
 * Accounts, postings and transactions.
 *
 * A port of the arithmetic in `Resources/Core/Ledger.lean`: a transaction is a
 * list of postings whose amounts sum to zero per commodity, and everything the
 * apply path needs to know about one is a consequence of that rule.
 */

import { commodityOfCode } from './money'
import type { Account, Amount, Date as LedgerDate, Posting, Transaction } from './types'
import { selfPartyId } from './types'

/* ------------------------------------------------------------------ */
/* Dates                                                               */
/* ------------------------------------------------------------------ */

/** Renders as `YYYY-MM-DD`, as `Date.toIso` does. */
export function dateToIso(d: LedgerDate): string {
  const year = d.year < 0 ? '-' + String(-d.year).padStart(4, '0') : String(d.year).padStart(4, '0')
  return `${year}-${String(d.month).padStart(2, '0')}-${String(d.day).padStart(2, '0')}`
}

/** Parses `YYYY-MM-DD`; `null` when it is not one. */
export function dateOfIso(s: string): LedgerDate | null {
  const m = /^(-?\d{4,})-(\d{2})-(\d{2})$/.exec(s)
  if (!m) return null
  return { year: Number(m[1]), month: Number(m[2]), day: Number(m[3]) }
}

/** Chronological comparison, as `compare` on a `PlainDate`. */
export function compareDates(a: LedgerDate, b: LedgerDate): number {
  if (a.year !== b.year) return a.year < b.year ? -1 : 1
  if (a.month !== b.month) return a.month < b.month ? -1 : 1
  if (a.day !== b.day) return a.day < b.day ? -1 : 1
  return 0
}

/* ------------------------------------------------------------------ */
/* Accounts                                                            */
/* ------------------------------------------------------------------ */

/** Whether `name` is `under` itself or one of its descendants. */
export function isUnder(name: string, under: string): boolean {
  return name === under || name.startsWith(under + '.')
}

/**
 * Whether this account holds real money — for whoever owns it.
 *
 * Deliberately blind to the owner: a friend's bank account funds a cost exactly
 * the way yours does.
 */
export function holdsMoney(a: Account): boolean {
  return a.kind === 'asset' || a.kind === 'liability'
}

/** Whether this account is your own, as opposed to a participant's. */
export function accountIsMine(a: Account): boolean {
  return a.owner === selfPartyId
}

/* ------------------------------------------------------------------ */
/* Postings and transactions                                           */
/* ------------------------------------------------------------------ */

/** This posting's contribution to the total of commodity `c`. */
export function postingNet(c: string, p: Posting): bigint {
  return p.amount.commodity.code === c ? p.amount.minor : 0n
}

/** This posting's contribution to account `a`'s balance in commodity `c`. */
export function postingNetIn(a: string, c: string, p: Posting): bigint {
  return p.account === a ? postingNet(c, p) : 0n
}

/** The commodities mentioned by this transaction, with duplicates. */
export function commodityCodes(t: Transaction): string[] {
  return t.postings.map((p) => p.amount.commodity.code)
}

/** The signed total of commodity `c` across all postings. */
export function txnNet(t: Transaction, c: string): bigint {
  let acc = 0n
  for (const p of t.postings) acc += postingNet(c, p)
  return acc
}

/** The signed total of commodity `c` landing in account `a`. */
export function txnNetIn(t: Transaction, a: string, c: string): bigint {
  let acc = 0n
  for (const p of t.postings) acc += postingNetIn(a, c, p)
  return acc
}

/** The non-zero residuals, per commodity — what an unbalanced transaction is missing. */
export function residuals(t: Transaction): [string, bigint][] {
  const seen: string[] = []
  const out: [string, bigint][] = []
  for (const c of commodityCodes(t)) {
    if (!seen.includes(c)) {
      seen.push(c)
      const n = txnNet(t, c)
      if (n !== 0n) out.push([c, n])
    }
  }
  return out
}

/** Whether the postings sum to zero in every commodity they mention. */
export function balanced(t: Transaction): boolean {
  return residuals(t).length === 0
}

/**
 * The only way into the store: rejects anything that does not balance, with
 * the same sentence `Transaction.validate` produces.
 */
export function validateTxn(t: Transaction): Transaction {
  if (balanced(t)) return t
  const detail = residuals(t)
    .map(([c, n]) => `${c} ${n}`)
    .join(', ')
  throw new Error(`transaction does not balance: ${detail}`)
}

/** The net movement on one account, as an amount. */
export function netOn(t: Transaction, a: string, c: { code: string; exponent: number }): Amount {
  return { commodity: c, minor: txnNetIn(t, a, c.code) }
}

/** Every account this transaction touches. */
export function txnAccounts(t: Transaction): string[] {
  return t.postings.map((p) => p.account)
}

/** Stamps every posting that has no origin yet, so a merge stays reversible. */
export function withOrigin(t: Transaction, origin: string): Transaction {
  return { ...t, postings: t.postings.map((p) => ({ ...p, origin: p.origin ?? origin })) }
}

/** Appends whatever postings are needed to make `t` balance, all into `account`. */
export function autoBalance(t: Transaction, account: string): Transaction {
  const extra: Posting[] = residuals(t).map(([code, n]) => ({
    account,
    amount: { commodity: commodityOfCode(code), minor: -n },
    party: null,
    note: null,
    origin: null,
    tag: null,
  }))
  return { ...t, postings: [...t.postings, ...extra] }
}

/* ------------------------------------------------------------------ */
/* Claims                                                              */
/* ------------------------------------------------------------------ */

/** The account a claim expects money to arrive in. `Pendings.receiver?`. */
export function claimReceiver(t: Transaction): string | null {
  const p = t.postings.find((x) => x.amount.minor > 0n)
  return p ? p.account : null
}

/** The account a claim expects money to leave. `Pendings.payer?`. */
export function claimPayer(t: Transaction): string | null {
  const p = t.postings.find((x) => x.amount.minor < 0n)
  return p ? p.account : null
}

/** What a claim still asks for. `Pendings.amount`. */
export function claimAmount(t: Transaction): Amount {
  const p = t.postings.find((x) => x.amount.minor > 0n)
  return p ? p.amount : { commodity: commodityOfCode('EUR'), minor: 0n }
}

/* ------------------------------------------------------------------ */
/* Merging                                                             */
/* ------------------------------------------------------------------ */

/** Combines two transactions into one by concatenating their postings. */
export function mergeWith(t: Transaction, u: Transaction): Transaction {
  return {
    ...t,
    postings: [...t.postings, ...u.postings],
    labels: [...t.labels, ...u.labels.filter((l) => !t.labels.includes(l))],
    attachments: [...t.attachments, ...u.attachments.filter((a) => !t.attachments.includes(a))],
    // Both sides' receipts come along, so both sides' lines do. One side that
    // says nothing specific — that it paid for all of whatever its receipt says
    // — makes the merge say nothing specific either, because the lines it would
    // have to name are the ones that were never written down.
    items: t.items === null || u.items === null ? null : [...t.items, ...u.items],
  }
}

/** Merges a whole list of transactions into `base`. */
export function mergeAll(base: Transaction, rest: readonly Transaction[]): Transaction {
  let out = base
  for (const u of rest) out = mergeWith(out, u)
  return out
}

/** The distinct origins present, in the order they first appear. */
export function origins(t: Transaction): string[] {
  const seen: string[] = []
  for (const p of t.postings) {
    if (p.origin !== null && !seen.includes(p.origin)) seen.push(p.origin)
  }
  return seen
}

/** The postings belonging to one origin. */
export function postingsOf(t: Transaction, origin: string): Posting[] {
  return t.postings.filter((p) => p.origin === origin)
}

/** Splits a merged transaction back into one transaction per origin. */
export function unmerge(t: Transaction, freshIds: readonly string[]): Transaction[] {
  const os = origins(t)
  const n = Math.min(os.length, freshIds.length)
  const out: Transaction[] = []
  for (let i = 0; i < n; i++) {
    out.push({ ...t, id: freshIds[i], postings: postingsOf(t, os[i]) })
  }
  return out
}

/** Removes every posting on `account`, for counter-legs a merge made redundant. */
export function dropAccount(t: Transaction, a: string): Transaction {
  return { ...t, postings: t.postings.filter((p) => p.account !== a) }
}
