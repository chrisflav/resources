/**
 * Reading a budget.
 *
 * A port of `Resources/Core/Budgets.lean`: what is still undivided, what has
 * already been handed to whom, where each person stands, and what would square
 * them up. Every figure is taken over the *posted* transactions only, because a
 * claim is a transaction that has not happened, and every order is chosen and
 * written down rather than inherited from a hash map.
 */

import { clamp, eraseDups, mergeSort, stringLe, trimAscii } from './bytes'
import { sortedValues } from './codec'
import {
  claimAmount,
  claimPayer,
  claimReceiver,
  compareDates,
  dateToIso,
  holdsMoney,
  isUnder,
  txnNetIn,
  validateTxn,
} from './ledger'
import { biproportional, render, shareOut, sum } from './money'
import * as Settle from './settle'
import {
  accountByNameIn,
  accountOfId,
  accountsSorted,
  balanceOf,
  ledgerOf,
  memberOfId,
  partyOfId,
  txnsSorted,
} from './state'
import type {
  Account,
  Amount,
  Budget,
  Commodity,
  Date as LedgerDate,
  Participant,
  Posting,
  Standing,
  State,
  Transaction,
} from './types'
import { claimTag } from './types'

/* ------------------------------------------------------------------ */
/* Naming                                                              */
/* ------------------------------------------------------------------ */

/** How one cost is described on an allocation leg and on an invoice line. */
export function describe(t: Transaction): string {
  const what = trimAscii(t.payee ?? '')
  return what === ''
    ? `${dateToIso(t.date)} — ${clamp(t.narration, 60)}`
    : `${dateToIso(t.date)} — ${clamp(what, 60)}`
}

/** The account name a budget lives in. A bare name is placed under `Budget`. */
export function budgetAccountName(name: string): string {
  return name.startsWith('Budget.') ? name : 'Budget.' + name
}

/** The short name, without the `Budget.` prefix. */
export function shortName(b: Budget): string {
  return b.name.startsWith('Budget.') ? b.name.slice(7) : b.name
}

/** The label the claims raised for this budget carry. */
export function budgetLabel(b: Budget): string {
  return 'budget:' + shortName(b)
}

/** The account name a person's own money lives in. */
export function purseName(person: string): string {
  return person.startsWith('Assets.') ? person : 'Assets.Purse.' + person
}

/**
 * The budget's own equity account, when the state still has it.
 *
 * By id, out of the budget's own record. It used to be by name, and the first
 * account in id order won: anybody who could write an account could create one
 * called `Budget.Hut` with a lower id and become the pot for every reader — the
 * balance read zero, settling found nothing to do, and every member of the
 * realm acquired post rights on the impostor.
 */
export function budgetAccount(b: Budget, s: State): Account | null {
  const bs = s.budgets.get(b.id)
  if (bs === undefined) return null
  return accountOfId(s, bs.account)
}

/* ------------------------------------------------------------------ */
/* Order                                                               */
/* ------------------------------------------------------------------ */

/** Oldest first, ties broken by id: the order the entries of a budget are read in. */
function olderFirst(a: Transaction, b: Transaction): boolean {
  const c = compareDates(a.date, b.date)
  if (c < 0) return true
  if (c > 0) return false
  return stringLe(a.id, b.id)
}

/** Newest first, ties broken by id: the order claims are read in. */
function newerFirst(a: Transaction, b: Transaction): boolean {
  const c = compareDates(a.date, b.date)
  if (c > 0) return true
  if (c < 0) return false
  return stringLe(b.id, a.id)
}

/** The first element with the largest score, in the order given. `pickMax`. */
function pickMax<T>(xs: readonly T[], score: (x: T) => bigint): T | null {
  let best: T | null = null
  for (const x of xs) {
    if (best === null) best = x
    else if (score(x) > score(best)) best = x
  }
  return best
}

/* ------------------------------------------------------------------ */
/* What a budget is made of                                            */
/* ------------------------------------------------------------------ */

/** Everything a budget is made of: its costs and the divisions of them. */
export function entries(b: Budget, s: State): Transaction[] {
  const hits = ledgerOf(s).filter((t) =>
    t.postings.some((p) => {
      const a = accountOfId(s, p.account)
      return a !== null && isUnder(a.name, b.name)
    }),
  )
  return mergeSort(hits, olderFirst)
}

/** The posted transactions with a leg in the budget's own account. */
function touching(s: State, acc: string): Transaction[] {
  return ledgerOf(s).filter((t) => t.postings.some((p) => p.account === acc))
}

/** What the budget still holds, and so what is still undecided. */
export function budgetBalance(b: Budget, s: State, c: Commodity): Amount {
  const acc = budgetAccount(b, s)
  if (acc === null) return { commodity: c, minor: 0n }
  return { commodity: c, minor: balanceOf(s, acc.id, c.code) }
}

/** What this budget has already given one person, whatever account it landed in. */
export function dividedTo(b: Budget, s: State, owner: string, c: Commodity): bigint {
  const acc = budgetAccount(b, s)
  if (acc === null) return 0n
  let out = 0n
  for (const t of touching(s, acc.id)) {
    for (const p of t.postings) {
      if (p.account === acc.id) continue
      if (p.amount.minor <= 0n) continue
      if (p.amount.commodity.code !== c.code) continue
      const a = accountOfId(s, p.account)
      if (a !== null && a.owner === owner) out += p.amount.minor
    }
  }
  return out
}

/** The costs a budget was lent, as opposed to the entries that divided them. */
export function costs(b: Budget, s: State): Transaction[] {
  const acc = budgetAccount(b, s)
  if (acc === null) return []
  return entries(b, s).filter((t) =>
    t.postings.some((p) => p.account === acc.id && p.tag !== 'allocation'),
  )
}

/** What each cost still has undivided, so allocating twice divides only the rest. */
export function remaining(b: Budget, s: State, c: Commodity): [Transaction, bigint][] {
  const acc = budgetAccount(b, s)
  if (acc === null) return []
  const everything = entries(b, s)
  const takenAgainst = (id: string): bigint => {
    let out = 0n
    for (const t of everything) {
      for (const p of t.postings) {
        if (
          p.account === acc.id &&
          p.tag === 'allocation' &&
          p.origin === id &&
          p.amount.commodity.code === c.code
        ) {
          out += p.amount.minor
        }
      }
    }
    return out
  }
  let rows: [Transaction, bigint][] = costs(b, s).map((t) => [
    t,
    txnNetIn(t, acc.id, c.code) + takenAgainst(t.id),
  ])
  // Whatever the per-cost figures do not account for is spread oldest first.
  const attributed = sum(rows.map(([, n]) => n))
  let slack = attributed - budgetBalance(b, s, c).minor
  if (slack !== 0n) {
    const out: [Transaction, bigint][] = []
    for (const [t, n] of rows) {
      // Only ever take from a cost in the direction it actually points, and
      // never past zero: a cost cannot be more than fully divided.
      const cut =
        slack > 0n
          ? n > 0n
            ? slack < n
              ? slack
              : n
            : 0n
          : n < 0n
            ? slack > n
              ? slack
              : n
            : 0n
      slack -= cut
      out.push([t, n - cut])
    }
    rows = out
  }
  return rows.filter(([, n]) => n !== 0n)
}

/* ------------------------------------------------------------------ */
/* Standing and settlement                                             */
/* ------------------------------------------------------------------ */

/** Where each person stands, the budget's own account excluded. */
export function standings(b: Budget, s: State, c: Commodity): Standing[] {
  const acc = budgetAccount(b, s)
  if (acc === null) return []
  const rows: [string, bigint][] = []
  for (const t of touching(s, acc.id)) {
    for (const p of t.postings) {
      if (p.account === acc.id || p.amount.commodity.code !== c.code) continue
      const a = accountOfId(s, p.account)
      if (a === null) continue
      const hit = rows.find(([owner]) => owner === a.owner)
      if (hit) hit[1] += p.amount.minor
      else rows.push([a.owner, p.amount.minor])
    }
  }
  const named: Standing[] = []
  for (const [owner, minor] of rows) {
    if (minor === 0n) continue
    named.push({
      owner,
      name: partyOfId(s, owner)?.name ?? owner,
      amount: { commodity: c, minor },
    })
  }
  return mergeSort(named, (x, y) =>
    x.name === y.name ? stringLe(x.owner, y.owner) : stringLe(x.name, y.name),
  )
}

/** The claims carrying one label: outstanding and already met, but not voided. */
export function claimsLabelled(s: State, label: string): Transaction[] {
  const hits = txnsSorted(s).filter(
    (t) => t.labels.includes(label) && (t.state === 'pending' || t.state === 'settled'),
  )
  return mergeSort(hits, newerFirst)
}

/**
 * The claims raised for this budget.
 *
 * By the label id pinned on the budget, not by a label of the budget's name: a
 * label is another entry anybody could write, and the first one of that name in
 * id order used to decide which claims a budget could see.
 */
export function claims(b: Budget, s: State): Transaction[] {
  const bs = s.budgets.get(b.id)
  if (bs === undefined || bs.label === '') return []
  return claimsLabelled(s, bs.label)
}

/** Whether a claim has been written up as an invoice that still stands. */
export function spokenFor(s: State, t: Transaction): boolean {
  return sortedValues(s.invoices).some(
    (i) => i.invoice.pendingTxn === t.id && i.invoice.status !== 'void',
  )
}

/** A claim, read as the movement it would make between two owners. */
export function transferOf(accounts: readonly Account[], t: Transaction): Settle.Transfer | null {
  const recv = claimReceiver(t)
  const pay = claimPayer(t)
  if (recv === null || pay === null) return null
  const to = accounts.find((a) => a.id === recv)
  const from = accounts.find((a) => a.id === pay)
  if (!to || !from) return null
  return { from_: from.owner, to: to.owner, minor: claimAmount(t).minor }
}

/**
 * The account a person settles through: the one of theirs this budget already
 * moved the most money across.
 *
 * Whoever fronted a cost gets paid back into the account they fronted it from,
 * which is both what a person expects and the only choice that needs no
 * configuring. Somebody who only owes has no such leg, so it falls back to the
 * account of theirs this ledger sees most, and then to their purse.
 *
 * All three readings are taken inside the budget's own realm. Without that
 * filter the candidates were every account of theirs anywhere, and a settlement
 * is written by `checkPostings`, which refuses a leg outside the part's realm —
 * so somebody who held an asset account of their own in any other realm this
 * reader could see made every settlement of this budget fail with "is not in
 * this realm", and getting it back needed an admin to close or rename an account
 * in a realm that had nothing to do with the budget.
 */
export function settlementAccount(b: Budget, s: State, owner: string, c: Commodity): string {
  const bs = s.budgets.get(b.id)
  if (bs === undefined) throw new Error(`no such budget: ${b.id}`)
  const theirs = accountsSorted(s).filter((a) => a.owner === owner && a.realm === bs.realm)
  const acc = budgetAccount(b, s)
  const inBudget: [string, bigint][] = []
  if (acc !== null) {
    for (const a of theirs.filter(holdsMoney)) {
      const moved: Posting[] = []
      for (const t of touching(s, acc.id)) {
        for (const p of t.postings) {
          if (p.account === a.id && p.amount.commodity.code === c.code) moved.push(p)
        }
      }
      if (moved.length > 0) inBudget.push([a.id, sum(moved.map((p) => p.amount.minor))])
    }
  }
  const best = pickMax(inBudget, ([, n]) => (n < 0n ? -n : n))
  if (best !== null) return best[0]
  const anywhere: [string, bigint][] = []
  for (const a of theirs.filter((x) => x.kind === 'asset')) {
    let n = 0n
    for (const t of ledgerOf(s)) for (const p of t.postings) if (p.account === a.id) n += 1n
    if (n !== 0n) anywhere.push([a.id, n])
  }
  const anyBest = pickMax(anywhere, ([, n]) => n)
  if (anyBest !== null) return anyBest[0]
  const party = partyOfId(s, owner)
  if (party === null) throw new Error(`no such person: ${owner}`)
  const purse =
    theirs.find((a) => a.bridgeOf !== null) ?? theirs.find((a) => a.name === purseName(party.name))
  if (purse) return purse.id
  throw new Error(`${party.name} has no account to settle through`)
}

/* ------------------------------------------------------------------ */
/* Dividing                                                            */
/* ------------------------------------------------------------------ */

/**
 * Each participant's account, resolved up front and checked for ownership.
 *
 * Two things are asked of every row, and both used to be missing. The lookup is
 * *in this realm*: it was the first account of that name in id order across
 * every realm, and an account of any name can be minted by anybody about
 * themselves — so a share could be pointed at a stranger's account, and while
 * the ownership check stopped the money going there, it stopped the division for
 * ever instead. And "an account of theirs" has two readings: the party the share
 * is for owns it, or it is the purse a member of that party holds here. A bridge
 * belongs to the member it is for, and a member's spending lands on their party.
 */
export function targetsOf(
  s: State,
  realm: string,
  among: readonly Participant[],
): string[] {
  const owners = among.map((p) => p.owner)
  if (eraseDups(owners).length !== owners.length) {
    throw new Error('somebody appears twice; give each person one share')
  }
  const out: string[] = []
  for (const p of among) {
    if (p.account === '') throw new Error(`${p.name} has no account for their share`)
    const target = accountByNameIn(s, realm, p.account)
    if (target === null) throw new Error(`no such account in this realm: ${p.account}`)
    const bridgeMember = target.bridgeOf === null ? null : memberOfId(s, target.bridgeOf)
    const bridgeParty = bridgeMember === null ? null : bridgeMember.party
    if (target.owner !== p.owner && bridgeParty !== p.owner) {
      throw new Error(
        `${p.account} belongs to somebody else, so ${p.name} cannot have a share there`,
      )
    }
    out.push(target.id)
  }
  return out
}

/**
 * The transaction that divides what the budget holds among the participants, or
 * `null` when there is nothing left to divide.
 *
 * Each cost is divided separately, and each person is *topped up* to the share
 * they are supposed to end up with rather than handed a slice of the remainder
 * — which is the only rule that is right both for a budget divided one person
 * at a time and for the ordinary case where the two agree exactly.
 */
export function divisionOf(
  b: Budget,
  s: State,
  realm: string,
  among: readonly Participant[],
  c: Commodity,
  date: LedgerDate,
  id: string,
  actor: string,
): Transaction | null {
  if (among.length === 0) throw new Error('say who to divide this among')
  const acc = budgetAccount(b, s)
  if (acc === null) throw new Error(`${shortName(b)} has no account of its own`)
  const pending = remaining(b, s, c)
  if (pending.length === 0) return null
  const targets = targetsOf(s, realm, among)
  const already = among.map((p) => dividedTo(b, s, p.owner, c))
  const toDivide = sum(pending.map(([, n]) => n))
  const owed = shareOut(sum(already) + toDivide, among)
  const topUps = owed.map((target, i) => target - already[i])
  const over = topUps.findIndex((n) => n < 0n)
  if (over >= 0) {
    throw new Error(
      `${among[over].name} has already been given ` +
        `${render({ commodity: c, minor: -topUps[over] })} more than this division leaves them; ` +
        `withdraw a division before dividing again`,
    )
  }
  // Every cost, split into the kinds of leg it is made of, so a card fee is
  // borne in the same proportion as the purchase beside it.
  const pieces: [string, string | null, bigint][] = []
  const seen: string[] = []
  for (const [t, held] of pending) {
    const base = describe(t)
    const clash = seen.filter((d) => d === base).length
    seen.push(base)
    const line = clash === 0 ? base : `${base} (${clash + 1})`
    const kinds: [string | null, bigint][] = []
    for (const p of t.postings) {
      if (p.account === acc.id && p.amount.commodity.code === c.code) {
        const hit = kinds.find(([g]) => g === p.tag)
        if (hit) hit[1] += p.amount.minor
        else kinds.push([p.tag, p.amount.minor])
      }
    }
    const split: [string | null, bigint][] =
      sum(kinds.map(([, n]) => n)) === held ? kinds : [[null, held]]
    for (const [kind, piece] of split) {
      pieces.push([kind === null ? line : `${line} (${kind})`, kind, piece])
    }
  }
  // Each person gets their top-up exactly, and each piece is fully divided.
  const grid = biproportional(
    topUps,
    pieces.map(([, , n]) => n),
  )
  const postings: Posting[] = []
  const totals = among.map(() => 0n)
  for (let i = 0; i < Math.min(grid.length, targets.length); i++) {
    const row = grid[i]
    for (let j = 0; j < Math.min(row.length, pieces.length); j++) {
      const share = row[j]
      if (share === 0n) continue
      postings.push({
        account: targets[i],
        amount: { commodity: c, minor: share },
        party: null,
        note: pieces[j][0],
        origin: null,
        tag: pieces[j][1],
      })
      totals[i] += share
    }
  }
  // One budget leg per cost, carrying that cost's id, so a later division can
  // tell what is left of it.
  for (const [t, held] of pending) {
    if (held === 0n) continue
    postings.push({
      account: acc.id,
      amount: { commodity: c, minor: -held },
      party: null,
      note: describe(t),
      origin: t.id,
      tag: 'allocation',
    })
  }
  if (sum(totals) === 0n) return null
  const divided: Transaction = {
    id,
    date,
    payee: null,
    narration: `allocation of ${shortName(b)}`,
    state: 'posted',
    postings,
    labels: [],
    source: { kind: 'manual', actor },
    attachments: [],
    items: null,
  }
  try {
    return validateTxn(divided)
  } catch (e) {
    throw new Error(`allocation would not balance: ${(e as Error).message}`)
  }
}

/**
 * The claims that would square the budget: the ones to raise, the ones to
 * revise, and the ones the facts have overtaken.
 *
 * A claim that has been met, or that an invoice speaks for, is netted off; a
 * claim that is merely outstanding is a request made on facts that may have
 * changed, so it is revised or withdrawn rather than left standing beside a
 * contradicting one. Returns only what changed.
 */
export function settlementOf(
  b: Budget,
  s: State,
  c: Commodity,
  hub: string | null,
  due: LedgerDate,
  claimIds: readonly string[],
  label: string,
  actor: string,
): Transaction[] {
  const held = budgetBalance(b, s, c)
  if (held.minor !== 0n) {
    throw new Error(
      `${shortName(b)} still holds ${render(held)} undivided; allocate it before settling`,
    )
  }
  const stand = standings(b, s, c)
  if (stand.length === 0) return []
  const accounts = accountsSorted(s)
  // What is already true, and what is merely still being asked.
  const fixed: Transaction[] = []
  let asking: Transaction[] = []
  for (const t of claimsLabelled(s, label)) {
    if (t.state !== 'pending' || spokenFor(s, t)) fixed.push(t)
    else asking.push(t)
  }
  const known: Settle.Transfer[] = []
  for (const t of fixed) {
    const tr = transferOf(accounts, t)
    if (tr !== null) known.push(tr)
  }
  const toPlan = Settle.residual(
    stand.map((x) => ({ who: x.owner, minor: x.amount.minor })),
    known,
  )
  const plan = hub !== null ? Settle.star(hub, toPlan) : Settle.greedy(toPlan)
  const checked = Settle.validate(toPlan, plan)
  const nameOf = (id: string): string => stand.find((x) => x.owner === id)?.name ?? id
  const ownerOf = (a: string): string | null => accountOfId(s, a)?.owner ?? null
  // A claim between the same two people is the same request, so it keeps its id.
  let ids = claimIds.slice()
  const out: Transaction[] = []
  for (const t of checked) {
    if (t.minor === 0n) continue
    const samePair = (x: Transaction): boolean => {
      const payer = claimPayer(x)
      const receiver = claimReceiver(x)
      return (
        payer !== null &&
        receiver !== null &&
        ownerOf(payer) === t.from_ &&
        ownerOf(receiver) === t.to
      )
    }
    const i = asking.findIndex(samePair)
    if (i >= 0) {
      const existing = asking[i]
      asking = asking.filter((x) => x.id !== existing.id)
      if (claimAmount(existing).minor === t.minor) continue
      const revised: Transaction = {
        ...existing,
        postings: existing.postings.map((p) => ({
          ...p,
          amount: { commodity: c, minor: p.amount.minor > 0n ? t.minor : -t.minor },
        })),
      }
      try {
        out.push(validateTxn(revised))
      } catch (e) {
        throw new Error(`revising a claim would not balance: ${(e as Error).message}`)
      }
    } else {
      const payer = settlementAccount(b, s, t.from_, c)
      const receiver = settlementAccount(b, s, t.to, c)
      if (payer === receiver) {
        throw new Error('a claim between one account and itself asks for nothing')
      }
      const id = ids[0]
      if (id === undefined) {
        throw new Error(
          `squaring up ${shortName(b)} needs more claim ids than the ${claimIds.length} given`,
        )
      }
      ids = ids.slice(1)
      const claim: Transaction = {
        id,
        date: due,
        payee: null,
        narration: `${nameOf(t.from_)} → ${nameOf(t.to)} for ${shortName(b)}`,
        state: 'pending',
        postings: [
          {
            account: receiver,
            amount: { commodity: c, minor: t.minor },
            party: null,
            note: null,
            origin: null,
            tag: claimTag,
          },
          {
            account: payer,
            amount: { commodity: c, minor: -t.minor },
            party: null,
            note: null,
            origin: null,
            tag: claimTag,
          },
        ],
        labels: [label],
        source: { kind: 'manual', actor },
        attachments: [],
        items: null,
      }
      try {
        out.push(validateTxn(claim))
      } catch (e) {
        throw new Error(`the claim would not balance: ${(e as Error).message}`)
      }
    }
  }
  // Whatever the new plan has no use for was a request the facts have overtaken.
  for (const x of asking) out.push({ ...x, state: 'void' })
  return out
}
