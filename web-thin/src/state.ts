/**
 * The state of the ledger, as the thin client holds it.
 *
 * A port of `Resources/Core/State.lean`. Two rules travel with it, and the rest
 * of this client depends on both.
 *
 * *Nothing here knows the time or the world.* An operation that needs a date or
 * a fresh id carries it, so replaying a log tomorrow produces exactly the state
 * it produced today.
 *
 * *Iteration is sorted.* `Map` in JavaScript iterates in insertion order, which
 * is a fact about how a snapshot happened to be decoded rather than about the
 * ledger, so every fold goes through `sortedPairs`/`sortedValues` — and those
 * order by Unicode code point, the way Lean's `String` order does, not the way
 * `Array.prototype.sort` does.
 */

import { compareStrings, mergeSort } from './bytes'
import { sortedPairs, sortedValues } from './codec'
import { holdsMoney } from './ledger'
import type {
  Account,
  BudgetState,
  InvoiceState,
  Label,
  Member,
  Party,
  Realm,
  RealmRole,
  Rule,
  State,
  Transaction,
} from './types'
import { selfMemberId, selfPartyId, selfRealmId } from './types'

export { sortedPairs, sortedValues }

/** A state with nothing in it. */
export function emptyState(): State {
  return {
    realms: new Map(),
    members: new Map(),
    accounts: new Map(),
    labels: new Map(),
    parties: new Map(),
    groups: new Map(),
    trips: new Map(),
    rules: new Map(),
    txns: new Map(),
    budgets: new Map(),
    invoices: new Map(),
    blobs: new Map(),
    batches: new Map(),
    counters: new Map(),
    fingerprints: new Set(),
  }
}

/** The ledger as it starts: your realm and you, and nothing else. `State.init`. */
export function initState(): State {
  const s = emptyState()
  s.realms.set(selfRealmId, {
    id: selfRealmId,
    name: 'me',
    members: [[selfMemberId, 'admin']],
    generation: 0,
  })
  s.members.set(selfMemberId, { id: selfMemberId, name: 'me', party: selfPartyId })
  return s
}

/**
 * A shallow copy with fresh maps.
 *
 * `applyOp` is a pure function in Lean and stays one here: nothing it is handed
 * is mutated, so a rejected operation leaves the caller's state exactly as it
 * found it.
 */
export function cloneState(s: State): State {
  return {
    realms: new Map(s.realms),
    members: new Map(s.members),
    accounts: new Map(s.accounts),
    labels: new Map(s.labels),
    parties: new Map(s.parties),
    groups: new Map(s.groups),
    trips: new Map(s.trips),
    rules: new Map(s.rules),
    txns: new Map(s.txns),
    budgets: new Map(s.budgets),
    invoices: new Map(s.invoices),
    blobs: new Map(s.blobs),
    batches: new Map(s.batches),
    counters: new Map(s.counters),
    fingerprints: new Set(s.fingerprints),
  }
}

/** A realm by id. */
export function realmOfId(s: State, id: string): Realm | null {
  return s.realms.get(id) ?? null
}

/** A member by id. */
export function memberOfId(s: State, id: string): Member | null {
  return s.members.get(id) ?? null
}

/** An account by id. */
export function accountOfId(s: State, id: string): Account | null {
  return s.accounts.get(id) ?? null
}

/** A transaction by id, whatever state it is in. */
export function txnOfId(s: State, id: string): Transaction | null {
  return s.txns.get(id) ?? null
}

/** A label by id. */
export function labelOfId(s: State, id: string): Label | null {
  return s.labels.get(id) ?? null
}

/** A party by id. */
export function partyOfId(s: State, id: string): Party | null {
  return s.parties.get(id) ?? null
}

/** A budget by id. */
export function budgetOfId(s: State, id: string): BudgetState | null {
  return s.budgets.get(id) ?? null
}

/** An invoice by id. */
export function invoiceOfId(s: State, id: string): InvoiceState | null {
  return s.invoices.get(id) ?? null
}

/** Every account, ordered by id. */
export function accountsSorted(s: State): Account[] {
  return sortedValues(s.accounts)
}

/** Every transaction, ordered by id. */
export function txnsSorted(s: State): Transaction[] {
  return sortedValues(s.txns)
}

/** Every rule, ordered by id. */
export function rulesSorted(s: State): Rule[] {
  return sortedValues(s.rules)
}

/** Every realm, ordered by id. */
export function realmsSorted(s: State): Realm[] {
  return sortedValues(s.realms)
}

/**
 * An account by name inside one realm: the only way to find one by name.
 *
 * There used to be an unscoped `accountByName` beside this, taking the first
 * match in id order across every realm, and a name is something anybody who may
 * write an account can take — so a viewer who self-granted a purse called
 * `Assets.Purse.Anna` with a low id decided, for every reader, which account
 * that name meant. At format-version 6 the last caller of it went (a grant's
 * bridge), and it went with them: every lookup by name — a budget's pot, a
 * participant's share, a grant's bridge — names the realm it is asking inside.
 */
export function accountByNameIn(s: State, realm: string, name: string): Account | null {
  return accountsSorted(s).find((a) => a.name === name && a.realm === realm) ?? null
}

/** The posted transactions, ordered by id: the ledger every balance is taken over. */
export function ledgerOf(s: State): Transaction[] {
  return txnsSorted(s).filter((t) => t.state === 'posted')
}

/** The balance of an account in one commodity, over posted transactions only. */
export function balanceOf(s: State, account: string, code: string): bigint {
  let acc = 0n
  for (const t of ledgerOf(s)) {
    for (const p of t.postings) {
      if (p.account === account && p.amount.commodity.code === code) acc += p.amount.minor
    }
  }
  return acc
}

/** The accounts money is held in, ordered by id. Deliberately blind to the owner. */
export function fundingAccounts(s: State): string[] {
  return accountsSorted(s)
    .filter(holdsMoney)
    .map((a) => a.id)
}

/** Which realm an account sits in. */
export function realmOfAccount(s: State, id: string): string | null {
  const a = accountOfId(s, id)
  return a ? a.realm : null
}

/** How many postings, in any transaction, still land in this account. */
export function postingCount(s: State, id: string): number {
  let n = 0
  for (const t of txnsSorted(s)) for (const p of t.postings) if (p.account === id) n++
  return n
}

/** The role a member holds in a realm, if any. */
export function roleOf(r: Realm, m: string): RealmRole | null {
  const hit = r.members.find(([id]) => id === m)
  return hit ? hit[1] : null
}

/** Whether a member may administer this realm. */
export function isAdmin(r: Realm, m: string): boolean {
  return roleOf(r, m) === 'admin'
}

/** Whether a member may see this realm at all. */
export function isMember(r: Realm, m: string): boolean {
  return roleOf(r, m) !== null
}

/** Records a member's role, replacing any they held, keeping members sorted by id. */
export function withMember(r: Realm, m: string, role: RealmRole): Realm {
  const rest = r.members.filter(([id]) => id !== m)
  const members = mergeSort<[string, RealmRole]>([...rest, [m, role]], (a, b) =>
    compareStrings(a[0], b[0]) <= 0,
  )
  return { ...r, members }
}

/** Drops a member from this realm. */
export function withoutMember(r: Realm, m: string): Realm {
  return { ...r, members: r.members.filter(([id]) => id !== m) }
}

/**
 * Whether a member may write a posting of this size into an account.
 *
 * Four ways, and they are the whole rule: it is their own purse in this realm,
 * they were named as a poster on it, they administer the realm it belongs to,
 * or it is the equity account of a budget that is still open, they are in the
 * realm that budget lives in, and the leg they are writing puts money *into*
 * the pot.
 *
 * The fourth is what makes a contribution an ordinary transaction. Somebody the
 * budget is divided among has to be able to say "I paid for this too", and the
 * only account they need for it besides their own purse is the budget's. Two
 * things bound it, and both were missing. It is keyed on the budget's own
 * account id, not on a name anybody could give an account of their own; and it
 * is a right to contribute rather than a right to write, because a pot that
 * everybody may take out of is not a pot. A closed budget is a decided one, so
 * the right ends with it either way.
 */
export function canPostLeg(s: State, m: string, a: Account, minor: bigint): boolean {
  if (a.bridgeOf === m) return true
  if (a.posters.includes(m)) return true
  const r = realmOfId(s, a.realm)
  if (r === null) return false
  if (isAdmin(r, m)) return true
  return isMember(r, m) && openBudgetAccount(s, a.id) && minor > 0n
}

/**
 * Whether a member may write into an account at all.
 *
 * `canPostLeg` with the most generous leg there is, which is what the
 * operations that move a whole account rather than a posting — a merge, a
 * deletion — ask.
 */
export function canPost(s: State, m: string, a: Account): boolean {
  return canPostLeg(s, m, a, 1n)
}

/** Whether an open budget is held in the account with this id. */
export function openBudgetAccount(s: State, id: string): boolean {
  for (const b of sortedValues(s.budgets)) {
    if (!b.budget.closed && b.account === id) return true
  }
  return false
}

/** Whether a member administers a realm. */
export function canAdminister(s: State, m: string, realm: string): boolean {
  const r = realmOfId(s, realm)
  return r !== null && isAdmin(r, m)
}

/** Whether a member may see a realm at all. */
export function isMemberOf(s: State, m: string, realm: string): boolean {
  const r = realmOfId(s, realm)
  return r !== null && isMember(r, m)
}

/**
 * Who this state records as administering a realm, in the order it holds them.
 *
 * Empty means the state says nothing about the realm — it has no record of it at
 * all, or nobody in it is an admin, or the only one is `self`. That distinction
 * is what turns the pinned inviter from a permanent root of trust into a
 * bootstrap: it is honoured while this list is empty and not afterwards.
 *
 * `self` does not count, which is the clause `Node/Session.lean`'s `trusts`
 * spells `m != Member.selfId`. It is the member a ledger belongs to before there
 * is a key to sign with, it is in `State.init` from the start, and it cannot
 * have signed anything — so a realm administered by nobody else is a realm this
 * reader has not read yet, and the pin is what it has.
 */
export function realmAdmins(s: State, realm: string): string[] {
  const r = realmOfId(s, realm)
  if (r === null) return []
  return r.members
    .filter(([id, role]) => role === 'admin' && id !== selfMemberId)
    .map(([id]) => id)
}
