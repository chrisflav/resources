/**
 * Applying operations to a realm a participant can see.
 *
 * The shape of every test below is the same: build a realm, apply the operation
 * an ordinary weekend produces, and look at what a participant would then be
 * shown — the costs, the standings and the claims. What is checked is not that
 * the code ran but that the figures are the ones the ledger's own rules give.
 */

import { describe, expect, it } from 'vitest'
import { applyOp, genesisOf, replay, stepAt } from './apply'
import {
  budgetBalance,
  claims as budgetClaims,
  costs as budgetCosts,
  remaining,
  standings,
} from './budgets'
import { settlementAccount } from './budgets'
import { claimAmount, claimPayer, claimReceiver } from './ledger'
import { eur, render } from './money'
import { emptyState } from './state'
import type { Account, LedgerEvent, Op, Posting, State, Transaction } from './types'

const ADMIN = 'admin-m'
const ANNA = 'anna-m'
const REALM = 'flat'
const day = { year: 2026, month: 3, day: 9 }

const blank = { party: null, note: null, origin: null, tag: null }

function account(over: Partial<Account> & Pick<Account, 'id' | 'name' | 'kind'>): Account {
  return {
    owner: 'p-me',
    commodity: null,
    iban: null,
    note: null,
    closedOn: null,
    realm: REALM,
    bridgeOf: null,
    posters: [],
    mirrorOf: null,
    ...over,
  }
}

function posting(account: string, minor: bigint): Posting {
  return { account, amount: { commodity: eur, minor }, ...blank }
}

function txn(id: string, payee: string, postings: Posting[]): Transaction {
  return {
    id,
    date: day,
    payee,
    narration: payee,
    state: 'posted',
    postings,
    labels: [],
    source: { kind: 'manual', actor: 'test' },
    attachments: [],
    items: null,
  }
}

/** A realm with a budget, two people and a purse each. */
function realm(): State {
  const s = emptyState()
  s.realms.set(REALM, {
    id: REALM,
    name: 'the flat',
    members: [
      [ADMIN, 'admin'],
      [ANNA, 'viewer'],
    ],
    generation: 0,
  })
  s.members.set(ADMIN, { id: ADMIN, name: 'Me', party: 'p-me' })
  s.members.set(ANNA, { id: ANNA, name: 'Anna', party: 'p-anna' })
  s.parties.set('p-me', {
    id: 'p-me',
    name: 'Me',
    iban: null,
    email: null,
    note: null,
    kind: 'contact',
    realm: REALM,
  })
  s.parties.set('p-anna', {
    id: 'p-anna',
    name: 'Anna',
    iban: null,
    email: null,
    note: null,
    kind: 'contact',
    realm: REALM,
  })
  s.accounts.set(
    'acc-budget',
    account({ id: 'acc-budget', name: 'Budget.Hut', kind: 'equity', posters: [ANNA] }),
  )
  s.accounts.set(
    'acc-me',
    account({ id: 'acc-me', name: 'Assets.Purse.Me', kind: 'asset', bridgeOf: ADMIN }),
  )
  s.accounts.set(
    'acc-anna',
    account({
      id: 'acc-anna',
      name: 'Assets.Purse.Anna',
      kind: 'asset',
      owner: 'p-anna',
      bridgeOf: ANNA,
    }),
  )
  s.accounts.set('acc-share-me', account({ id: 'acc-share-me', name: 'Expenses.Me', kind: 'expense' }))
  s.accounts.set(
    'acc-share-anna',
    account({ id: 'acc-share-anna', name: 'Expenses.Anna', kind: 'expense', owner: 'p-anna' }),
  )
  s.labels.set('lab', { id: 'lab', name: 'budget:Hut', colour: null, realm: REALM })
  s.budgets.set('bud', {
    budget: { id: 'bud', name: 'Budget.Hut', note: null, closed: false },
    participants: [],
    realm: REALM,
    account: 'acc-budget',
    label: 'lab',
  })
  return s
}

const budgetOf = (s: State) => s.budgets.get('bud')!.budget

/** Applies and insists it worked, so a test failure names the sentence that stopped it. */
function ok(s: State, author: string, op: Op): State {
  const r = applyOp(s, author, REALM, op)
  if (r.kind === 'error') throw new Error(r.message)
  return r.state
}

const among = [
  { owner: 'p-me', name: 'Me', account: 'Expenses.Me', weight: 1 },
  { owner: 'p-anna', name: 'Anna', account: 'Expenses.Anna', weight: 1 },
]

const cost = txn('cost-1', 'the hut', [posting('acc-budget', 10000n), posting('acc-anna', -10000n)])

describe('putTransaction', () => {
  it('writes a cost a participant paid for out of their own purse', () => {
    const s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    expect(budgetCosts(budgetOf(s), s)).toHaveLength(1)
    expect(render(budgetBalance(budgetOf(s), s, eur))).toBe('100.00 EUR')
    expect(remaining(budgetOf(s), s, eur).map(([, n]) => n)).toEqual([10000n])
  })

  it('refuses a transaction that does not balance', () => {
    const bad = txn('bad', 'x', [posting('acc-budget', 10000n), posting('acc-anna', -9999n)])
    const r = applyOp(realm(), ANNA, REALM, { tag: 15, kind: 'putTransaction', txn: bad })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/does not balance/)
  })

  it('lets a member post to an open budget even when nobody named them a poster', () => {
    const s = realm()
    s.accounts.set('acc-budget', { ...s.accounts.get('acc-budget')!, posters: [] })
    const after = ok(s, ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    expect(budgetCosts(budgetOf(after), after)).toHaveLength(1)
  })

  it('takes that right away again when the budget is closed', () => {
    const s = realm()
    s.accounts.set('acc-budget', { ...s.accounts.get('acc-budget')!, posters: [] })
    const bs = s.budgets.get('bud')!
    s.budgets.set('bud', { ...bs, budget: { ...bs.budget, closed: true } })
    const r = applyOp(s, ANNA, REALM, { tag: 15, kind: 'putTransaction', txn: cost })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/may not post to Budget.Hut/)
  })

  it('refuses a posting into an account the author may not write to', () => {
    const s = realm()
    const other = { ...s.accounts.get('acc-anna')!, id: 'acc-bob', name: 'Assets.Purse.Bob' }
    s.accounts.set('acc-bob', { ...other, bridgeOf: null, posters: [] })
    const theirs = txn('t', 'x', [posting('acc-budget', 10000n), posting('acc-bob', -10000n)])
    const r = applyOp(s, ANNA, REALM, { tag: 15, kind: 'putTransaction', txn: theirs })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/may not post to Assets.Purse.Bob/)
  })

  it('refuses a posting into a closed account', () => {
    const s = realm()
    s.accounts.set('acc-budget', { ...s.accounts.get('acc-budget')!, closedOn: day })
    const r = applyOp(s, ANNA, REALM, { tag: 15, kind: 'putTransaction', txn: cost })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/is closed/)
  })

  it('refuses a posting into another realm', () => {
    const s = realm()
    s.accounts.set('acc-anna', { ...s.accounts.get('acc-anna')!, realm: 'elsewhere' })
    const r = applyOp(s, ADMIN, REALM, { tag: 15, kind: 'putTransaction', txn: cost })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/is not in this realm/)
  })
})

describe('deleteTransaction', () => {
  it('withdraws a cost that is still undivided', () => {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ANNA, { tag: 16, kind: 'deleteTransaction', id: 'cost-1' })
    expect(budgetCosts(budgetOf(s), s)).toHaveLength(0)
    expect(budgetBalance(budgetOf(s), s, eur).minor).toBe(0n)
  })

  it('refuses a transaction that is not there', () => {
    const r = applyOp(realm(), ANNA, REALM, { tag: 16, kind: 'deleteTransaction', id: 'nope' })
    expect(r).toMatchObject({ kind: 'error' })
  })
})

describe('setParticipants', () => {
  it('records who a budget is divided among', () => {
    const s = ok(realm(), ADMIN, {
      tag: 26,
      kind: 'setParticipants',
      budget: 'bud',
      among,
    })
    expect(s.budgets.get('bud')!.participants.map((p) => p.owner)).toEqual(['p-me', 'p-anna'])
  })

  it('refuses a weight outside the range a share may carry', () => {
    // A weight is how many consecutive parts of the division somebody takes, so
    // it is a count of parts the author chose the size of: zero is not a share
    // and a thousand million is a list nobody can hold.
    for (const weight of [0, 10001]) {
      const r = applyOp(realm(), ADMIN, REALM, {
        tag: 26,
        kind: 'setParticipants',
        budget: 'bud',
        among: [{ owner: 'p-me', name: 'Me', account: 'Expenses.Me', weight }],
      })
      expect(r).toMatchObject({ kind: 'error' })
      if (r.kind === 'error') expect(r.message).toMatch(/weight has to be between 1 and 10000/)
    }
  })

  it('refuses more participants than a budget may be divided among', () => {
    const many = Array.from({ length: 101 }, (_, i) => ({
      owner: `p-${i}`,
      name: `P${i}`,
      account: 'Expenses.Me',
      weight: 1,
    }))
    const r = applyOp(realm(), ADMIN, REALM, {
      tag: 26,
      kind: 'setParticipants',
      budget: 'bud',
      among: many,
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/at most 100 are allowed/)
  })

  it('is refused for somebody who does not administer the realm', () => {
    const r = applyOp(realm(), ANNA, REALM, {
      tag: 26,
      kind: 'setParticipants',
      budget: 'bud',
      among,
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/only an admin/)
  })
})

describe('contribute', () => {
  it('records a cost somebody paid for directly into the budget', () => {
    const s = ok(realm(), ADMIN, { tag: 27, kind: 'contribute', budget: 'bud', txn: cost })
    expect(budgetCosts(budgetOf(s), s)).toHaveLength(1)
  })

  it('refuses something that took nothing out of anybody', () => {
    const nothing = txn('n', 'x', [posting('acc-budget', -10000n), posting('acc-anna', 10000n)])
    const r = applyOp(realm(), ADMIN, REALM, {
      tag: 27,
      kind: 'contribute',
      budget: 'bud',
      txn: nothing,
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/has to be an amount that was spent/)
  })
})

describe('allocate', () => {
  /** A hut somebody paid a hundred for, divided in two. */
  function divided(): State {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among,
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    return s
  }

  it('divides the cost and leaves the budget holding nothing', () => {
    const s = divided()
    const alloc = s.txns.get('alloc-1')!
    expect(alloc.narration).toBe('allocation of Hut')
    const shares = new Map(alloc.postings.map((p) => [p.account, p.amount.minor]))
    expect(shares.get('acc-share-me')).toBe(5000n)
    expect(shares.get('acc-share-anna')).toBe(5000n)
    expect(shares.get('acc-budget')).toBe(-10000n)
    // The budget leg carries the id of the cost it discharges.
    expect(alloc.postings.find((p) => p.account === 'acc-budget')!.origin).toBe('cost-1')
    expect(budgetBalance(budgetOf(s), s, eur).minor).toBe(0n)
    expect(remaining(budgetOf(s), s, eur)).toHaveLength(0)
  })

  it('leaves each person standing at what they bear less what they put in', () => {
    const s = divided()
    expect(standings(budgetOf(s), s, eur)).toEqual([
      { owner: 'p-anna', name: 'Anna', amount: { commodity: eur, minor: -5000n } },
      { owner: 'p-me', name: 'Me', amount: { commodity: eur, minor: 5000n } },
    ])
  })

  it('raises the claim that squares them up, through the accounts they used', () => {
    const s = divided()
    const raised = budgetClaims(budgetOf(s), s)
    expect(raised).toHaveLength(1)
    const claim = raised[0]
    expect(claim.id).toBe('claim-1')
    expect(claim.state).toBe('pending')
    expect(claim.narration).toBe('Me → Anna for Hut')
    expect(claimReceiver(claim)).toBe('acc-anna')
    expect(claimPayer(claim)).toBe('acc-me')
    expect(claimAmount(claim).minor).toBe(5000n)
  })

  it('divides only what is left when a second cost turns up', () => {
    let s = divided()
    const late = txn('cost-2', 'the taxi', [
      posting('acc-budget', 2000n),
      posting('acc-me', -2000n),
    ])
    s = ok(s, ADMIN, { tag: 15, kind: 'putTransaction', txn: late })
    expect(remaining(budgetOf(s), s, eur).map(([t, n]) => [t.id, n])).toEqual([['cost-2', 2000n]])
    s = ok(s, ADMIN, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among,
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-2',
      claimIds: ['claim-2'],
      labelId: 'lab',
    })
    const second = s.txns.get('alloc-2')!
    const shares = new Map(second.postings.map((p) => [p.account, p.amount.minor]))
    expect(shares.get('acc-share-me')).toBe(1000n)
    expect(shares.get('acc-share-anna')).toBe(1000n)
    // Anna is owed 50 for the hut less the 10 she now bears of the taxi she did
    // not pay for; the earlier claim is revised rather than left standing.
    const open = budgetClaims(budgetOf(s), s).filter((c) => c.state === 'pending')
    expect(open).toHaveLength(1)
    expect(open[0].id).toBe('claim-1')
    expect(claimAmount(open[0]).minor).toBe(4000n)
  })

  it('refuses to divide a share into an account belonging to somebody else', () => {
    const s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    const r = applyOp(s, ADMIN, REALM, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among: [
        { owner: 'p-me', name: 'Me', account: 'Expenses.Me', weight: 1 },
        { owner: 'p-anna', name: 'Anna', account: 'Expenses.Me', weight: 1 },
      ],
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/belongs to somebody else/)
  })

  it('divides unequal shares to the cent', () => {
    let s = ok(realm(), ANNA, {
      tag: 15,
      kind: 'putTransaction',
      txn: txn('cost-1', 'the hut', [posting('acc-budget', 10n), posting('acc-anna', -10n)]),
    })
    s = ok(s, ADMIN, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among: [
        { owner: 'p-me', name: 'Me', account: 'Expenses.Me', weight: 2 },
        { owner: 'p-anna', name: 'Anna', account: 'Expenses.Anna', weight: 1 },
      ],
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    const shares = new Map(s.txns.get('alloc-1')!.postings.map((p) => [p.account, p.amount.minor]))
    expect(shares.get('acc-share-me')! + shares.get('acc-share-anna')!).toBe(10n)
    expect(shares.get('acc-share-me')).toBe(6n)
    expect(shares.get('acc-share-anna')).toBe(4n)
  })
})

describe('settle', () => {
  it('refuses to plan while the budget still holds something undivided', () => {
    const s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    const r = applyOp(s, ADMIN, REALM, {
      tag: 29,
      kind: 'settle',
      budget: 'bud',
      commodity: eur,
      hub: null,
      due: day,
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/still holds .* undivided/)
  })

  it('says nothing new the second time', () => {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among,
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    const before = budgetClaims(budgetOf(s), s).map((c) => c.id)
    s = ok(s, ADMIN, {
      tag: 29,
      kind: 'settle',
      budget: 'bud',
      commodity: eur,
      hub: null,
      due: day,
      claimIds: ['claim-2'],
      labelId: 'lab',
    })
    expect(budgetClaims(budgetOf(s), s).map((c) => c.id)).toEqual(before)
  })
})

describe('resolveClaim', () => {
  function withClaim(): State {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among,
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    return s
  }

  it('settles a claim the payment covers in full', () => {
    let s = withClaim()
    const payment = txn('pay-1', 'settling up', [
      posting('acc-anna', 5000n),
      posting('acc-me', -5000n),
    ])
    s = ok(s, ADMIN, { tag: 15, kind: 'putTransaction', txn: payment })
    s = ok(s, ADMIN, {
      tag: 23,
      kind: 'resolveClaim',
      id: 'claim-1',
      actual: 'pay-1',
      splitId: 'split-1',
    })
    expect(s.txns.get('claim-1')!.state).toBe('settled')
    // The met claim points at the entry that discharged it.
    expect(s.txns.get('claim-1')!.postings.every((p) => p.origin === 'pay-1')).toBe(true)
    expect(s.txns.has('split-1')).toBe(false)
  })

  it('splits a claim a part payment only partly covers', () => {
    let s = withClaim()
    const payment = txn('pay-1', 'settling up', [
      posting('acc-anna', 2000n),
      posting('acc-me', -2000n),
    ])
    s = ok(s, ADMIN, { tag: 15, kind: 'putTransaction', txn: payment })
    s = ok(s, ADMIN, {
      tag: 23,
      kind: 'resolveClaim',
      id: 'claim-1',
      actual: 'pay-1',
      splitId: 'split-1',
    })
    expect(s.txns.get('split-1')!.state).toBe('settled')
    expect(claimAmount(s.txns.get('split-1')!).minor).toBe(2000n)
    expect(s.txns.get('claim-1')!.state).toBe('pending')
    expect(claimAmount(s.txns.get('claim-1')!).minor).toBe(3000n)
    // What has been asked for is still the sum of both halves.
    expect(
      claimAmount(s.txns.get('split-1')!).minor + claimAmount(s.txns.get('claim-1')!).minor,
    ).toBe(5000n)
  })

  it('refuses a payment that brings nothing into the account the claim names', () => {
    let s = withClaim()
    const elsewhere = txn('pay-1', 'a different payment', [
      posting('acc-me', 5000n),
      posting('acc-anna', -5000n),
    ])
    s = ok(s, ADMIN, { tag: 15, kind: 'putTransaction', txn: elsewhere })
    const r = applyOp(s, ADMIN, REALM, {
      tag: 23,
      kind: 'resolveClaim',
      id: 'claim-1',
      actual: 'pay-1',
      splitId: 'split-1',
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/brings nothing into/)
  })

  it('lets the receiver meet a claim without post rights on the debtor’s purse', () => {
    // The right the table grants the receiver used to be unreachable: settling
    // writes the claim back, and the claim's paying leg is the *debtor's* purse,
    // which the receiver cannot post to. Every test that passed did so because
    // its author happened to administer the realm.
    let s = realm()
    const claim: Transaction = {
      ...txn('claim-x', 'me owes anna', []),
      state: 'pending',
      postings: [
        { ...posting('acc-anna', 5000n), tag: 'claim' },
        { ...posting('acc-me', -5000n), tag: 'claim' },
      ],
    }
    s = ok(s, ADMIN, { tag: 22, kind: 'raiseClaim', txn: claim })
    const payment = txn('pay-x', 'settling up', [
      posting('acc-anna', 5000n),
      posting('acc-me', -5000n),
    ])
    s = ok(s, ADMIN, { tag: 15, kind: 'putTransaction', txn: payment })
    // Anna is a viewer; the purse the claim is owed into is hers.
    const r = applyOp(s, ANNA, REALM, {
      tag: 23,
      kind: 'resolveClaim',
      id: 'claim-x',
      actual: 'pay-x',
      splitId: 'split-x',
    })
    expect(r).toMatchObject({ kind: 'ok' })
    if (r.kind === 'ok') expect(r.state.txns.get('claim-x')!.state).toBe('settled')
  })

  it('refuses to meet a claim twice', () => {
    let s = withClaim()
    const payment = txn('pay-1', 'settling up', [
      posting('acc-anna', 5000n),
      posting('acc-me', -5000n),
    ])
    s = ok(s, ADMIN, { tag: 15, kind: 'putTransaction', txn: payment })
    s = ok(s, ADMIN, {
      tag: 23,
      kind: 'resolveClaim',
      id: 'claim-1',
      actual: 'pay-1',
      splitId: 'split-1',
    })
    const r = applyOp(s, ADMIN, REALM, {
      tag: 23,
      kind: 'resolveClaim',
      id: 'claim-1',
      actual: 'pay-1',
      splitId: 'split-2',
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/already settled/)
  })
})

describe('closing and reopening', () => {
  it('divides what is left and then closes', () => {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, { tag: 26, kind: 'setParticipants', budget: 'bud', among })
    s = ok(s, ADMIN, {
      tag: 30,
      kind: 'closeBudget',
      budget: 'bud',
      among: null,
      commodity: eur,
      hub: null,
      date: day,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    expect(s.budgets.get('bud')!.budget.closed).toBe(true)
    expect(budgetBalance(budgetOf(s), s, eur).minor).toBe(0n)
    expect(budgetClaims(budgetOf(s), s)).toHaveLength(1)
  })

  it('will not close twice, and reopens without undoing anything', () => {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, { tag: 26, kind: 'setParticipants', budget: 'bud', among })
    s = ok(s, ADMIN, {
      tag: 30,
      kind: 'closeBudget',
      budget: 'bud',
      among: null,
      commodity: eur,
      hub: null,
      date: day,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    const again = applyOp(s, ADMIN, REALM, {
      tag: 30,
      kind: 'closeBudget',
      budget: 'bud',
      among: null,
      commodity: eur,
      hub: null,
      date: day,
      txnId: 'alloc-2',
      claimIds: [],
      labelId: 'lab',
    })
    expect(again).toMatchObject({ kind: 'error' })
    s = ok(s, ADMIN, { tag: 31, kind: 'reopenBudget', budget: 'bud' })
    expect(s.budgets.get('bud')!.budget.closed).toBe(false)
    expect(budgetClaims(budgetOf(s), s)).toHaveLength(1)
    expect(applyOp(s, ADMIN, REALM, { tag: 31, kind: 'reopenBudget', budget: 'bud' })).toMatchObject(
      { kind: 'error' },
    )
  })

  it('refuses a cost while it is closed', () => {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, { tag: 26, kind: 'setParticipants', budget: 'bud', among })
    s = ok(s, ADMIN, {
      tag: 30,
      kind: 'closeBudget',
      budget: 'bud',
      among: null,
      commodity: eur,
      hub: null,
      date: day,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    const late = txn('cost-2', 'the taxi', [posting('acc-budget', 2000n), posting('acc-me', -2000n)])
    const r = applyOp(s, ADMIN, REALM, { tag: 27, kind: 'contribute', budget: 'bud', txn: late })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/is closed; reopen it/)
  })
})

describe('registerBlob', () => {
  const till = {
    sha256: 'a'.repeat(64),
    mime: 'image/jpeg',
    bytes: 8192,
    origName: 'till.jpg',
    createdAt: '2026-03-01T10:00:00',
    cipherHash: null as string | null,
    wrappedKey: null as string | null,
  }

  /** The realm, with the file already known and nothing said about a copy of it. */
  function withBlob(): State {
    const s = realm()
    return ok(s, ADMIN, { tag: 37, kind: 'registerBlob', file: till })
  }

  it('takes the sealing a second registration carries, and nothing else', () => {
    const read = ok(withBlob(), ADMIN, {
      tag: 40,
      kind: 'recordExtraction',
      sha: till.sha256,
      extracted: {
        merchant: 'the hut',
        date: day,
        total: { commodity: eur, minor: 10000n },
        items: [],
        rawText: 'till',
        extractor: 'test',
      },
    })
    const s = ok(read, ADMIN, {
      tag: 37,
      kind: 'registerBlob',
      file: {
        ...till,
        // What a re-sealing may not quietly rewrite: the bytes are the same bytes.
        bytes: 1,
        origName: 'renamed.jpg',
        cipherHash: 'b'.repeat(64),
        wrappedKey: 'other:0:a2V5',
      },
    })
    const b = s.blobs.get(till.sha256)!
    expect(b.file.cipherHash).toBe('b'.repeat(64))
    expect(b.file.wrappedKey).toBe('other:0:a2V5')
    expect(b.file.bytes).toBe(8192)
    expect(b.file.origName).toBe('till.jpg')
    // What was read off the file survives the re-registration.
    expect(b.extracted.merchant).toBe('the hut')
  })

  it('leaves a sealing in place when the registration carries none', () => {
    const wrapped = ok(withBlob(), ADMIN, {
      tag: 37,
      kind: 'registerBlob',
      file: { ...till, cipherHash: 'b'.repeat(64), wrappedKey: 'flat:0:a2V5' },
    })
    const s = ok(wrapped, ADMIN, { tag: 37, kind: 'registerBlob', file: till })
    const b = s.blobs.get(till.sha256)!
    expect(b.file.cipherHash).toBe('b'.repeat(64))
    expect(b.file.wrappedKey).toBe('flat:0:a2V5')
  })
})

describe('everything else', () => {
  it('is understood too, and leaves the state it was handed alone', () => {
    const s = realm()
    const others: Op[] = [
      { tag: 1, kind: 'putAccount', account: account({ id: 'x', name: 'X', kind: 'asset' }) },
      { tag: 44, kind: 'addMember', member: { id: 'm', name: 'M', party: 'p' } },
      { tag: 49, kind: 'rotateRealmKey', realm: REALM },
      { tag: 32, kind: 'deleteBudget', budget: 'bud' },
    ]
    for (const op of others) {
      expect(applyOp(s, ADMIN, REALM, op).kind).toBe('ok')
    }
    // `applyOp` is pure: every case builds a fresh state rather than writing
    // into the one it was given, which is what makes a refusal cost nothing.
    expect(s.accounts.size).toBe(5)
    expect(s.budgets.size).toBe(1)
    expect(s.realms.get(REALM)!.generation).toBe(0)
  })
})

describe('addMember and grant', () => {
  const nils = { id: 'nils-m', name: 'Nils', party: 'p-nils' }
  const purse = account({ id: 'acc-nils', name: 'Members.Nils', kind: 'asset', owner: 'p-me' })

  it('writes the party a newcomer names, because nothing else would', () => {
    const r = applyOp(realm(), ADMIN, REALM, { tag: 44, kind: 'addMember', member: nils })
    expect(r.kind).toBe('ok')
    if (r.kind !== 'ok') return
    expect(r.state.parties.get('p-nils')).toEqual({
      realm: REALM,
      id: 'p-nils',
      name: 'Nils',
      iban: null,
      email: null,
      note: null,
      kind: 'contact',
    })
    // The party comes first: a reader projecting the changes in order never
    // holds a member pointing at a party it has not seen.
    expect(r.changes.map((c) => c.kind)).toEqual(['party', 'member'])
  })

  it('leaves a party that is already there exactly as it was', () => {
    const known = { ...nils, party: 'p-anna' }
    const r = applyOp(realm(), ADMIN, REALM, { tag: 44, kind: 'addMember', member: known })
    expect(r.kind).toBe('ok')
    if (r.kind !== 'ok') return
    expect(r.state.parties.get('p-anna')!.name).toBe('Anna')
    expect(r.changes.map((c) => c.kind)).toEqual(['member'])
  })

  it('lets nobody but an admin write somebody else in', () => {
    const r = applyOp(realm(), ANNA, REALM, { tag: 44, kind: 'addMember', member: nils })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') {
      expect(r.message).toBe('only an admin of that realm may do that for somebody else')
    }
  })

  it('says which member is missing, and what to do about it', () => {
    const r = applyOp(realm(), ADMIN, REALM, {
      tag: 46,
      kind: 'grant',
      realm: REALM,
      member: 'nils-m',
      role: 'viewer',
      bridge: purse,
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') {
      expect(r.message).toBe('cannot grant an unknown member: add nils-m first')
    }
  })

  it('points the purse at the member record, not at what the operation asked for', () => {
    let s = ok(realm(), ADMIN, { tag: 44, kind: 'addMember', member: nils })
    s = ok(s, ADMIN, {
      tag: 46,
      kind: 'grant',
      realm: REALM,
      member: 'nils-m',
      role: 'viewer',
      bridge: purse,
    })
    expect(s.accounts.get('acc-nils')).toMatchObject({
      owner: 'p-nils',
      realm: REALM,
      bridgeOf: 'nils-m',
      mirrorOf: null,
    })
  })

  it('lets a member attest their own view of the realm, and nothing stronger', () => {
    const s = ok(realm(), ADMIN, { tag: 44, kind: 'addMember', member: nils })
    const asking = (role: 'viewer' | 'admin'): Op => ({
      tag: 46,
      kind: 'grant',
      realm: REALM,
      member: 'nils-m',
      role,
      bridge: purse,
    })
    expect(applyOp(s, 'nils-m', REALM, asking('viewer')).kind).toBe('ok')
    const seized = applyOp(s, 'nils-m', REALM, asking('admin'))
    expect(seized).toMatchObject({ kind: 'error' })
    if (seized.kind === 'error') {
      expect(seized.message).toBe('only an admin of that realm may do that for somebody else')
    }
  })
})

describe('payClaim', () => {
  /** A realm where Anna fronted the hut and the division has asked Me for half. */
  function withClaim(): State {
    let s = ok(realm(), ANNA, { tag: 15, kind: 'putTransaction', txn: cost })
    s = ok(s, ADMIN, {
      tag: 28,
      kind: 'allocate',
      budget: 'bud',
      among,
      commodity: eur,
      date: day,
      hub: null,
      txnId: 'alloc-1',
      claimIds: ['claim-1'],
      labelId: 'lab',
    })
    return s
  }

  const pay: Op = { tag: 51, kind: 'payClaim', claim: 'claim-1', payment: 'pay-1', date: day }

  it('writes the payment and settles the claim, for the member being paid', () => {
    // Anna is a viewer, and the leg that lands in Me's purse is one she may not
    // ordinarily write; the claim is what entitles her to it.
    const s = ok(withClaim(), ANNA, pay)
    const payment = s.txns.get('pay-1')!
    expect(payment.state).toBe('posted')
    expect(payment.narration).toBe(`payment of ${withClaim().txns.get('claim-1')!.narration}`)
    expect(payment.postings.map((p) => [p.account, p.amount.minor, p.tag])).toEqual([
      ['acc-me', -5000n, 'claim'],
      ['acc-anna', 5000n, 'claim'],
    ])
    expect(s.txns.get('claim-1')!.state).toBe('settled')
    // The met claim points at the entry that discharged it.
    expect(s.txns.get('claim-1')!.postings.every((p) => p.origin === 'pay-1')).toBe(true)
    // Nothing is asked for any more, and the purses moved by exactly the claim.
    expect(budgetClaims(budgetOf(s), s).filter((c) => c.state === 'pending')).toHaveLength(0)
  })

  it('lets an admin of the realm the two purses sit in record it too', () => {
    const s = ok(withClaim(), ADMIN, pay)
    expect(s.txns.get('claim-1')!.state).toBe('settled')
  })

  it('refuses the member who owes: a receipt they wrote themselves is not one', () => {
    // Me owes this claim, and is also the realm's admin, so the debtor has to
    // be somebody who is only the debtor. Carl takes over the purse that owes.
    const s = withClaim()
    const r = s.realms.get(REALM)!
    s.realms.set(REALM, { ...r, members: [...r.members, ['carl-m', 'viewer']] })
    const mine = s.accounts.get('acc-me')!
    s.accounts.set('acc-me', { ...mine, bridgeOf: 'carl-m' })
    const out = applyOp(s, 'carl-m', REALM, pay)
    expect(out).toMatchObject({ kind: 'error' })
    if (out.kind === 'error') {
      expect(out.message).toMatch(/only the receiver or an admin of that realm/)
    }
  })

  it('refuses somebody neither end of the claim belongs to', () => {
    const s = withClaim()
    const r = s.realms.get(REALM)!
    s.realms.set(REALM, { ...r, members: [...r.members, ['carl-m', 'viewer']] })
    const out = applyOp(s, 'carl-m', REALM, pay)
    expect(out).toMatchObject({ kind: 'error' })
    if (out.kind === 'error') {
      expect(out.message).toMatch(/only the receiver or an admin of that realm/)
    }
  })

  it('refuses a claim that has already been met', () => {
    const s = ok(withClaim(), ANNA, pay)
    const out = applyOp(s, ANNA, REALM, {
      tag: 51,
      kind: 'payClaim',
      claim: 'claim-1',
      payment: 'pay-2',
      date: day,
    })
    expect(out).toMatchObject({ kind: 'error' })
    if (out.kind === 'error') expect(out.message).toMatch(/that claim is already settled/)
  })
})

/* ------------------------------------------------------------------ */
/* Every entity has a realm                                            */
/* ------------------------------------------------------------------ */

/**
 * A part may only speak about an entry of the realm it names.
 *
 * Eight kinds of entry used to have no realm at all — labels, people, groups,
 * trips, rules, import batches, stored receipts and the invoice counter — so
 * "an admin of the part's realm" reached across every realm a reader could
 * open. That is a right anybody can manufacture: create a realm, make yourself
 * its admin, hand somebody a key, and from inside it delete a label out of
 * every transaction they hold, rewrite any person in their books, install the
 * rules that drive what their imports file where, forget their receipts and
 * move their invoice numbering.
 */
describe('which realm an entry is in', () => {
  const OTHER = 'somewhere-else'

  /** The realm, plus a second one this author also administers. */
  function two(): State {
    const s = realm()
    s.realms.set(OTHER, {
      id: OTHER,
      name: 'the other one',
      members: [[ADMIN, 'admin']],
      generation: 0,
    })
    return s
  }

  it('refuses a label that belongs to another realm', () => {
    const s = two()
    s.labels.set('lab-x', { id: 'lab-x', name: 'x', colour: null, realm: OTHER })
    const r = applyOp(s, ADMIN, REALM, {
      tag: 6,
      kind: 'putLabel',
      label: { id: 'lab-x', name: 'y', colour: null, realm: REALM },
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/is not in this realm/)
  })

  it('creates a new entry in the realm the part names, whatever the entry says', () => {
    const s = ok(two(), ADMIN, {
      tag: 6,
      kind: 'putLabel',
      label: { id: 'lab-new', name: 'new', colour: null, realm: OTHER },
    })
    expect(s.labels.get('lab-new')!.realm).toBe(REALM)
  })

  it('refuses a group, a trip, a rule and an import filed elsewhere', () => {
    const s = two()
    s.groups.set('flat', { name: 'flat', members: ['a'], realm: OTHER })
    s.trips.set('zin', {
      id: 't',
      name: 'zin',
      starts: day,
      ends: day,
      payer: 'p-me',
      note: null,
      realm: OTHER,
    })
    s.rules.set('r-1', {
      id: 'r-1',
      name: 'groceries',
      filterSrc: '',
      filter: { kind: 'all' },
      setAccount: null,
      addLabels: [],
      setParty: null,
      priority: 0n,
      realm: OTHER,
    })
    s.batches.set('b-1', {
      id: 'b-1',
      profile: 'dkb',
      filename: null,
      account: null,
      stamp: '',
      total: 0,
      duplicates: 0,
      realm: OTHER,
    })
    const refused: Op[] = [
      { tag: 9, kind: 'putGroup', group: { name: 'flat', members: ['b'], realm: REALM } },
      { tag: 10, kind: 'deleteGroup', name: 'flat' },
      { tag: 12, kind: 'deleteTrip', name: 'zin' },
      {
        tag: 13,
        kind: 'putRule',
        rule: { ...s.rules.get('r-1')!, name: 'other', realm: REALM },
      },
      { tag: 43, kind: 'recordImportBatch', batch: { ...s.batches.get('b-1')!, realm: REALM } },
    ]
    for (const op of refused) {
      const r = applyOp(s, ADMIN, REALM, op)
      expect(r).toMatchObject({ kind: 'error' })
      if (r.kind === 'error') expect(r.message).toMatch(/is not in this realm/)
    }
  })

  it('removes a rule only from the realm it drives imports in', () => {
    const s = two()
    s.rules.set('r-1', {
      id: 'r-1',
      name: 'groceries',
      filterSrc: '',
      filter: { kind: 'all' },
      setAccount: null,
      addLabels: [],
      setParty: null,
      priority: 0n,
      realm: OTHER,
    })
    const r = applyOp(s, ADMIN, REALM, { tag: 14, kind: 'deleteRule', idOrName: 'groceries' })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/no such rule/)
    const there = applyOp(s, ADMIN, OTHER, { tag: 14, kind: 'deleteRule', idOrName: 'groceries' })
    expect(there).toMatchObject({ kind: 'ok' })
    if (there.kind === 'ok') expect(there.state.rules.size).toBe(0)
  })

  it('refuses to strip a label off a transaction with no leg in this realm', () => {
    const s = two()
    s.accounts.set(
      'acc-there',
      account({ id: 'acc-there', name: 'Assets.There', kind: 'asset', realm: OTHER }),
    )
    s.accounts.set(
      'acc-there-2',
      account({ id: 'acc-there-2', name: 'Expenses.There', kind: 'expense', realm: OTHER }),
    )
    s.txns.set('t-there', {
      ...txn('t-there', 'over there', [posting('acc-there', 10000n), posting('acc-there-2', -10000n)]),
      labels: ['lab'],
    })
    // Deleting the label here would leave that transaction carrying a label id
    // nothing resolves — which is how a budget's settled claims were made
    // invisible, so the settlement asked a second time for money already moved.
    const r = applyOp(s, ADMIN, REALM, { tag: 7, kind: 'deleteLabel', id: 'lab' })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/no leg in this realm/)
    expect(s.labels.has('lab')).toBe(true)
  })

  it('keys the invoice counter by realm, so one realm cannot move another’s numbering', () => {
    const s = ok(realm(), ADMIN, {
      tag: 33,
      kind: 'issueInvoice',
      invoice: {
        id: 'inv-1',
        number: '',
        issued: day,
        due: day,
        payerId: 'p-anna',
        payerName: 'Anna',
        commodity: eur,
        reference: '',
        status: 'draft',
        note: null,
        settledTxn: null,
        payment: { kind: 'link', url: 'https://example.org/pay' },
        sourceAccount: null,
        budgetId: null,
        pendingTxn: null,
        lines: [],
      },
      sources: [],
    })
    expect([...s.counters.keys()]).toEqual([`${REALM}:invoice:2026`])
    expect(s.invoices.get('inv-1')!.invoice.number).toBe('2026-0001')
  })

  it('lets a member revise the party their own spending lands on, and nobody else’s', () => {
    const s = realm()
    const mine = { ...s.parties.get('p-anna')!, iban: 'DE02' }
    const after = ok(s, ANNA, { tag: 8, kind: 'putParty', party: mine })
    expect(after.parties.get('p-anna')!.iban).toBe('DE02')
    // And the record keeps the realm it was introduced in.
    expect(after.parties.get('p-anna')!.realm).toBe(REALM)
    const theirs = { ...s.parties.get('p-me')!, iban: 'DE03' }
    const r = applyOp(s, ANNA, REALM, { tag: 8, kind: 'putParty', party: theirs })
    expect(r).toMatchObject({ kind: 'error' })
  })

  it('moves a receipt into the realm a re-sealing names, and only for its own people', () => {
    const OTHERS = 'somewhere-else'
    const s = two()
    const file = {
      sha256: 'c'.repeat(64),
      mime: 'image/jpeg',
      bytes: 10,
      origName: null,
      createdAt: '',
      cipherHash: null as string | null,
      wrappedKey: null as string | null,
    }
    const filed = ok(s, ADMIN, { tag: 37, kind: 'registerBlob', file })
    expect(filed.blobs.get(file.sha256)!.realm).toBe(REALM)
    // A receipt filed in one realm and attached to a payment in another is
    // sealed again under that realm's key, and the record follows.
    const moved = ok(filed, ADMIN, {
      tag: 37,
      kind: 'registerBlob',
      file: { ...file, cipherHash: 'd'.repeat(64), wrappedKey: `${OTHERS}:0:a2V5` },
    })
    expect(moved.blobs.get(file.sha256)!.realm).toBe(REALM)
    // Somebody who neither filed it nor administers the realm it is in cannot.
    const r = applyOp(moved, ANNA, REALM, { tag: 37, kind: 'registerBlob', file })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/may register it again/)
  })

  it('refuses to say what a receipt of another realm contains', () => {
    const s = two()
    const file = {
      sha256: 'e'.repeat(64),
      mime: 'image/jpeg',
      bytes: 10,
      origName: null,
      createdAt: '',
      cipherHash: null as string | null,
      wrappedKey: null as string | null,
    }
    const filed = ok(s, ADMIN, { tag: 37, kind: 'registerBlob', file })
    const r = applyOp(filed, ADMIN, OTHER, {
      tag: 41,
      kind: 'setReceiptLines',
      sha: file.sha256,
      items: [],
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/that receipt is not in this realm/)
  })
})

/* ------------------------------------------------------------------ */
/* Format-version 6: the invoice's realm, and the last by-name lookups */
/* ------------------------------------------------------------------ */

/**
 * The kind `Core/State.lean` gave a realm at format-version 6, and the four
 * lookups the same version scoped.
 *
 * An invoice record had no realm at all, which the per-realm counter made worse
 * rather than better: an admin of any realm a reader could open deleted a draft
 * issued somewhere else and wound back *their own* realm's sequence, so the
 * issuing realm kept the burnt number while an unrelated one went backwards and
 * the next invoice there duplicated a number somebody had already been sent. And
 * a name is something anybody who may write an entry can take, so a lookup by
 * name across every realm is a lookup an outsider chooses the answer to.
 */
describe('an invoice belongs to the realm it was issued in', () => {
  const OTHER = 'somewhere-else'

  const invoice = {
    id: 'inv-1',
    number: '',
    issued: day,
    due: day,
    payerId: null as string | null,
    payerName: 'Anna',
    commodity: eur,
    reference: '',
    status: 'draft' as const,
    note: null,
    settledTxn: null,
    payment: { kind: 'link' as const, url: 'https://example.org/pay' },
    sourceAccount: null,
    budgetId: null,
    pendingTxn: null,
    lines: [],
  }

  const issue = (over: Partial<typeof invoice> = {}): Op => ({
    tag: 33,
    kind: 'issueInvoice',
    invoice: { ...invoice, ...over },
    sources: [],
  })

  /** The realm, plus a second one this author also administers. */
  function two(): State {
    const s = realm()
    s.realms.set(OTHER, {
      id: OTHER,
      name: 'the other one',
      members: [[ADMIN, 'admin']],
      generation: 0,
    })
    return s
  }

  it('records the part’s realm on the invoice it raises', () => {
    const s = ok(realm(), ADMIN, issue())
    expect(s.invoices.get('inv-1')!.realm).toBe(REALM)
  })

  it('resolves the payer among the parties of this realm and no other', () => {
    // `putParty`'s self door lets any member set the name of their own party to
    // anything at all, from any realm they are in, and the old lookup was the
    // first party of that name in id order across every realm — so a member
    // whose party id sorted low renamed it to a customer's name and every
    // invoice afterwards issued to that name was addressed to them instead.
    const s = two()
    s.parties.set('aaa-impostor', {
      id: 'aaa-impostor',
      name: 'Anna',
      iban: null,
      email: null,
      note: null,
      kind: 'contact',
      realm: OTHER,
    })
    const after = ok(s, ADMIN, issue())
    expect(after.invoices.get('inv-1')!.invoice.payerId).toBe('p-anna')
  })

  it('creates a payer nobody knows in the realm the invoice was issued in', () => {
    const after = ok(two(), ADMIN, issue({ payerName: 'Acme Ltd', payerId: 'p-acme' }))
    expect(after.parties.get('p-acme')!.realm).toBe(REALM)
    expect(after.invoices.get('inv-1')!.invoice.payerId).toBe('p-acme')
  })

  it('says so when nobody of that name is in this realm and no id was given', () => {
    const r = applyOp(realm(), ADMIN, REALM, issue({ payerName: 'Acme Ltd' }))
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/nobody called Acme Ltd in this realm/)
  })

  it('refuses the three later words about it from any other realm', () => {
    const s = ok(two(), ADMIN, issue())
    s.txns.set(cost.id, cost)
    const elsewhere: Op[] = [
      { tag: 34, kind: 'setInvoiceStatus', id: 'inv-1', status: 'void' },
      { tag: 35, kind: 'settleInvoice', id: 'inv-1', txn: cost.id },
      { tag: 36, kind: 'deleteInvoice', id: 'inv-1' },
    ]
    for (const op of elsewhere) {
      const r = applyOp(s, ADMIN, OTHER, op)
      expect(r).toMatchObject({ kind: 'error' })
      if (r.kind === 'error') expect(r.message).toMatch(/invoice 2026-0001 is not in this realm/)
    }
    // And each of them is fine from the realm that issued it.
    expect(applyOp(s, ADMIN, REALM, elsewhere[0])).toMatchObject({ kind: 'ok' })
    expect(applyOp(s, ADMIN, REALM, elsewhere[1])).toMatchObject({ kind: 'ok' })
    expect(applyOp(s, ADMIN, REALM, elsewhere[2])).toMatchObject({ kind: 'ok' })
  })

  it('winds back the counter the issuing realm handed the number out of', () => {
    const issued = ok(realm(), ADMIN, issue())
    expect(issued.counters.get(`${REALM}:invoice:2026`)).toBe(1n)
    const gone = ok(issued, ADMIN, { tag: 36, kind: 'deleteInvoice', id: 'inv-1' })
    // The invoice's own realm, not the part's — which for a refused cross-realm
    // delete would have been somebody else's sequence going backwards.
    expect(gone.counters.get(`${REALM}:invoice:2026`)).toBe(0n)
    expect([...gone.counters.keys()]).toEqual([`${REALM}:invoice:2026`])
  })
})

describe('the last three lookups that went by name', () => {
  const OTHER = 'somewhere-else'

  function two(): State {
    const s = realm()
    s.realms.set(OTHER, {
      id: OTHER,
      name: 'the other one',
      members: [[ADMIN, 'admin']],
      generation: 0,
    })
    return s
  }

  it('grants a bridge of a name another realm has already taken', () => {
    // `Members.<name>` is a name any member can mint about themselves through
    // the attest door, in any realm they may write in, and the unscoped lookup
    // found the first account of that name anywhere and then refused the grant
    // because it was elsewhere — so one member could block an admin from
    // granting a bridge of that name in every other realm, for ever.
    const s = two()
    s.accounts.set(
      'acc-block',
      account({ id: 'acc-block', name: 'Members.Bob', kind: 'asset', realm: OTHER }),
    )
    s.members.set('bob-m', { id: 'bob-m', name: 'Bob', party: 'p-bob' })
    const after = ok(s, ADMIN, {
      tag: 46,
      kind: 'grant',
      realm: REALM,
      member: 'bob-m',
      role: 'viewer',
      bridge: account({ id: 'acc-bob', name: 'Members.Bob', kind: 'asset', owner: 'p-bob' }),
    })
    expect(after.accounts.get('acc-bob')).toMatchObject({ realm: REALM, bridgeOf: 'bob-m' })
    expect(after.accounts.get('acc-block')!.realm).toBe(OTHER)
  })

  it('pins the label of the budget’s name that is in the budget’s realm', () => {
    // The label pinned here is what a budget's claims are read out of, so a
    // label of that name written in any realm a reader could open used to decide
    // which claims a budget could see.
    const s = two()
    s.labels.set('lab-far', { id: 'lab-far', name: 'budget:Ski', colour: null, realm: OTHER })
    s.labels.set('lab-near', { id: 'lab-near', name: 'budget:Ski', colour: null, realm: REALM })
    const after = ok(s, ADMIN, {
      tag: 25,
      kind: 'openBudget',
      budget: { id: 'bud-ski', name: 'Ski', note: null, closed: false },
      account: account({ id: 'acc-ski', name: 'Budget.Ski', kind: 'equity' }),
    })
    expect(after.budgets.get('bud-ski')!.label).toBe('lab-near')
  })

  it('pins nothing when the only label of that name is in another realm', () => {
    const s = two()
    s.labels.set('lab-far', { id: 'lab-far', name: 'budget:Ski', colour: null, realm: OTHER })
    const after = ok(s, ADMIN, {
      tag: 25,
      kind: 'openBudget',
      budget: { id: 'bud-ski', name: 'Ski', note: null, closed: false },
      account: account({ id: 'acc-ski', name: 'Budget.Ski', kind: 'equity' }),
    })
    expect(after.budgets.get('bud-ski')!.label).toBe('')
  })

  it('settles through an account of theirs in the budget’s realm', () => {
    // A settlement is written by `checkPostings`, which refuses a leg outside
    // the part's realm — so an asset account of their own in any other realm
    // this reader could see made every settlement of this budget fail with "is
    // not in this realm", and getting it back needed an admin to close or rename
    // an account in a realm that had nothing to do with the budget.
    const s = two()
    s.accounts.set(
      'aaa-far',
      account({
        id: 'aaa-far',
        name: 'Assets.Elsewhere',
        kind: 'asset',
        owner: 'p-anna',
        realm: OTHER,
      }),
    )
    s.txns.set(
      't-far',
      txn('t-far', 'over there', [posting('aaa-far', 100n), posting('aaa-far', -100n)]),
    )
    expect(settlementAccount(budgetOf(s), s, 'p-anna', eur)).toBe('acc-anna')
  })

  it('says there is no such budget rather than reading one that is not there', () => {
    const s = realm()
    const orphan = { id: 'bud-gone', name: 'Budget.Gone', note: null, closed: false }
    expect(() => settlementAccount(orphan, s, 'p-anna', eur)).toThrow(/no such budget/)
  })
})

/* ------------------------------------------------------------------ */
/* The attest door, and the pot it cannot squat                        */
/* ------------------------------------------------------------------ */

describe('a grant somebody writes for themselves', () => {
  it('makes one purse, named after them, and nothing they chose', () => {
    const s = realm()
    s.accounts.delete('acc-anna')
    const after = ok(s, ANNA, {
      tag: 46,
      kind: 'grant',
      realm: REALM,
      member: ANNA,
      role: 'viewer',
      bridge: account({
        id: 'acc-minted',
        name: 'Budget.Hut.Mine',
        kind: 'equity',
        posters: [ANNA, ADMIN],
        iban: 'DE99',
      }),
    })
    expect(after.accounts.get('acc-minted')).toMatchObject({
      name: 'Members.Anna',
      kind: 'asset',
      owner: 'p-anna',
      realm: REALM,
      bridgeOf: ANNA,
      posters: [],
      mirrorOf: null,
      iban: null,
    })
  })

  it('adopts nothing: a name or an id already spoken for is a refusal', () => {
    const s = realm()
    s.accounts.delete('acc-anna')
    s.accounts.set(
      'acc-taken',
      account({ id: 'acc-taken', name: 'Members.Anna', kind: 'asset' }),
    )
    const r = applyOp(s, ANNA, REALM, {
      tag: 46,
      kind: 'grant',
      realm: REALM,
      member: ANNA,
      role: 'viewer',
      bridge: account({ id: 'acc-fresh', name: 'x', kind: 'asset' }),
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/already an account in that realm/)
  })
})

describe('openBudget', () => {
  const openSki: Op = {
    tag: 25,
    kind: 'openBudget',
    budget: { id: 'bud-ski', name: 'Ski', note: null, closed: false },
    account: account({ id: 'acc-ski', name: 'Budget.Ski', kind: 'equity' }),
  }

  /** The realm with an account of the pot's name already standing in it. */
  function squatted(over: Partial<Account>): State {
    const s = realm()
    s.accounts.set(
      'acc-squat',
      account({ id: 'acc-squat', name: 'Budget.Ski', kind: 'equity', ...over }),
    )
    return s
  }

  it('refuses an account of the budget’s name that is not what a pot is', () => {
    // The attest door mints accounts with a name of the author's choosing, so a
    // viewer who self-granted a purse called `Budget.Ski` before the admin
    // opened `Ski` had the pot adopted as their own bridge — which they may post
    // to in either direction. Three questions say an account is a pot.
    const wrongKind = applyOp(squatted({ kind: 'asset' }), ADMIN, REALM, openSki)
    expect(wrongKind).toMatchObject({ kind: 'error' })
    if (wrongKind.kind === 'error') {
      expect(wrongKind.message).toMatch(/already an account of another kind/)
    }
    const purse = applyOp(squatted({ bridgeOf: ANNA }), ADMIN, REALM, openSki)
    expect(purse).toMatchObject({ kind: 'error' })
    if (purse.kind === 'error') expect(purse.message).toMatch(/somebody's purse in this realm/)
    const posted = applyOp(squatted({ posters: [ANNA] }), ADMIN, REALM, openSki)
    expect(posted).toMatchObject({ kind: 'error' })
    if (posted.kind === 'error') expect(posted.message).toMatch(/already names its own posters/)
  })

  it('adopts one that is', () => {
    const after = ok(squatted({}), ADMIN, openSki)
    expect(after.budgets.get('bud-ski')!.account).toBe('acc-squat')
    expect(after.accounts.has('acc-ski')).toBe(false)
  })

  it('opens a fresh pot when the name is free', () => {
    const after = ok(realm(), ADMIN, {
      tag: 25,
      kind: 'openBudget',
      budget: { id: 'bud-ski', name: 'Ski', note: null, closed: false },
      account: account({ id: 'acc-ski', name: 'anything', kind: 'asset' }),
    })
    expect(after.accounts.get('acc-ski')).toMatchObject({
      name: 'Budget.Ski',
      kind: 'equity',
      realm: REALM,
      bridgeOf: null,
    })
    expect(after.budgets.get('bud-ski')!.account).toBe('acc-ski')
  })
})

/* ------------------------------------------------------------------ */
/* Claims, bounds and where a log starts                               */
/* ------------------------------------------------------------------ */

describe('putTransaction over a claim', () => {
  it('refuses an id whose stored transaction is not posted', () => {
    const s = realm()
    const claim: Transaction = {
      ...txn('claim-1', 'anna owes', [posting('acc-me', 5000n), posting('acc-anna', -5000n)]),
      state: 'pending',
      postings: [
        { ...posting('acc-me', 5000n), tag: 'claim' },
        { ...posting('acc-anna', -5000n), tag: 'claim' },
      ],
    }
    s.txns.set('claim-1', claim)
    const r = applyOp(s, ADMIN, REALM, {
      tag: 15,
      kind: 'putTransaction',
      txn: { ...claim, state: 'posted' },
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') {
      expect(r.message).toMatch(/is pending; a claim is met or withdrawn, not overwritten/)
    }
  })
})

describe('the bounds an operation carries', () => {
  it('refuses a date outside the years this ledger keeps books in', () => {
    const r = applyOp(realm(), ADMIN, REALM, {
      tag: 11,
      kind: 'putTrip',
      trip: {
        id: 't',
        name: 'far',
        starts: { year: 1000000, month: 1, day: 1 },
        ends: day,
        payer: 'p-me',
        note: null,
        realm: REALM,
      },
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/a year has to be between/)
  })

  it('refuses a commodity nothing can scale', () => {
    const fine = { code: 'XAU', exponent: 19 }
    const bad = txn('bad-1', 'x', [
      { account: 'acc-budget', amount: { commodity: fine, minor: 1n }, ...blank },
      { account: 'acc-anna', amount: { commodity: fine, minor: -1n }, ...blank },
    ])
    const r = applyOp(realm(), ADMIN, REALM, { tag: 15, kind: 'putTransaction', txn: bad })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/at most 18 decimal places/)
  })

  it('refuses a result of more postings than an operation may carry', () => {
    // `checkBounds` bounds what an author *sent*; this is the bound on what an
    // intent *computed*, and it is the only place a result can be bounded.
    const s = realm()
    const targets: string[] = []
    for (let i = 0; i < 205; i++) {
      const id = `acc-t${i}`
      s.accounts.set(id, account({ id, name: `Expenses.T${i}`, kind: 'expense' }))
      targets.push(id)
    }
    s.txns.set('cost-1', cost)
    const r = applyOp(s, ADMIN, REALM, {
      tag: 17,
      kind: 'splitTransaction',
      id: 'cost-1',
      targets,
      keepShare: false,
    })
    expect(r).toMatchObject({ kind: 'error' })
    if (r.kind === 'error') expect(r.message).toMatch(/and at most 200 are allowed/)
  })
})

describe('where a log starts', () => {
  it('refuses a snapshot wherever a part carries one, including on an empty ledger', () => {
    const g = realm()
    for (const s of [emptyState(), realm()]) {
      const r = applyOp(s, ADMIN, REALM, { tag: 50, kind: 'snapshot', state: g })
      expect(r).toMatchObject({ kind: 'error' })
      if (r.kind === 'error') expect(r.message).toMatch(/a snapshot is where a log starts/)
    }
  })

  it('reads the genesis off the first event of a log, and nowhere else', () => {
    const g = realm()
    const snapshot: Op = { tag: 50, kind: 'snapshot', state: g }
    const event = (id: string, ops: Op[]): LedgerEvent => ({
      id,
      author: ADMIN,
      composedAt: '',
      basedOn: 0,
      parts: ops.map((op) => ({ realm: REALM, op })),
    })
    expect(genesisOf(event('e1', [snapshot]))).not.toBeNull()
    // A snapshot beside something else is not a beginning at all.
    expect(genesisOf(event('e1', [snapshot, { tag: 49, kind: 'rotateRealmKey', realm: REALM }])))
      .toBeNull()
    // Position 1 takes it; every other position is `step`, which refuses it.
    expect(stepAt(1, emptyState(), event('e1', [snapshot])).state.accounts.size).toBe(5)
    expect(stepAt(2, emptyState(), event('e1', [snapshot])).state.accounts.size).toBe(0)
    expect(replay([event('e1', [snapshot])]).accounts.size).toBe(5)
    expect(replay([event('e0', []), event('e1', [snapshot])]).accounts.size).toBe(0)
    // An empty log is the ledger as `initState` leaves it.
    expect(replay([]).realms.size).toBe(1)
  })
})
