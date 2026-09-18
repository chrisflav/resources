/**
 * The encoding, checked twice over.
 *
 * The round trips are a sanity net: a wrong tuple in a structure or a field
 * left out shows up as a value that does not come back.
 *
 * The fixed byte strings are the other half, and they are the ones that matter.
 * A round trip says decoding inverts encoding; it says nothing about *which*
 * bytes were written, so a renumbered tag or a reordered field would pass every
 * round trip while changing every checkpoint hash in the world. Every literal
 * below is copied verbatim from `Test/Encode.lean`. If one of them fails, the
 * format changed: decide whether that was meant, and if it was, change it in
 * both places in the same commit.
 */

import { beforeAll, describe, expect, it } from 'vitest'
import { fromHex, toHex } from './bytes'
import {
  CodecError,
  Writer,
  accountCodec,
  accountKindCodec,
  amountCodec,
  attachmentCodec,
  blobStateCodec,
  budgetCodec,
  budgetStateCodec,
  changeCodec,
  commodityCodec,
  dateCodec,
  decode,
  encode,
  eventCodec,
  extractedCodec,
  filterCodec,
  importBatchCodec,
  intCodec,
  invoiceCodec,
  invoiceLineCodec,
  invoiceStateCodec,
  invoiceStatusCodec,
  itemGroupCodec,
  itemShareCodec,
  labelCodec,
  lineItemCodec,
  memberCodec,
  opCodec,
  partCodec,
  participantCodec,
  partyCodec,
  partyGroupCodec,
  paymentRequestCodec,
  postingCodec,
  provenanceCodec,
  realmCodec,
  realmRoleCodec,
  ruleCodec,
  sortedKeys,
  sortedPairs,
  stateCodec,
  stringCodec,
  transactionCodec,
  tripCodec,
  txnStateCodec,
} from './codec'
import type { Codec } from './codec'
import { ready, sha256Hex } from './crypto'
import { commodityOfCode, eur } from './money'
import { emptyState, initState } from './state'
import type {
  Account,
  Attachment,
  Budget,
  Change,
  Extracted,
  Filter,
  ImportBatch,
  Invoice,
  ItemGroup,
  Label,
  LedgerEvent,
  LineItem,
  Member,
  Op,
  Participant,
  Party,
  PartyGroup,
  Posting,
  Realm,
  Rule,
  State,
  Transaction,
  Trip,
} from './types'
import { selfPartyId, selfRealmId } from './types'

beforeAll(async () => {
  await ready()
})

/** Round-trips a value and checks that what comes back writes the same bytes. */
function trip<T>(codec: Codec<T>, x: T): void {
  const bytes = encode(codec, x)
  const back = decode(codec, bytes)
  expect(toHex(encode(codec, back))).toBe(toHex(bytes))
}

/** Pins the exact bytes a value encodes to. */
function bytesAre<T>(codec: Codec<T>, x: T, hex: string): void {
  expect(toHex(encode(codec, x))).toBe(hex)
}

/* ------------------------------------------------------------------ */
/* The values being encoded, as `Test/Encode.lean` builds them         */
/* ------------------------------------------------------------------ */

const day = { year: 2026, month: 3, day: 9 }
const otherDay = { year: 2025, month: 12, day: 31 }

const account: Account = {
  id: 'acc-giro',
  name: 'Assets.Bank.DKB.Giro',
  kind: 'asset',
  owner: selfPartyId,
  commodity: eur,
  iban: 'DE02120300000000202051',
  note: 'the everyday one',
  closedOn: otherDay,
  realm: selfRealmId,
  bridgeOf: 'self',
  posters: ['self', 'anna'],
  mirrorOf: 'acc-bridge',
}

const party: Party = {
  id: 'party-anna',
  name: 'Anna',
  iban: 'DE89370400440532013000',
  email: 'anna@example.org',
  note: null,
  kind: 'contact',
  realm: selfRealmId,
}

const label: Label = { id: 'lab-trip', name: 'trip', colour: '#ff8800', realm: selfRealmId }

const posting: Posting = {
  account: 'acc-giro',
  amount: { commodity: eur, minor: -4990n },
  party: 'party-anna',
  note: 'half of dinner',
  origin: 'csv:17',
  tag: 'fee',
}

const txn: Transaction = {
  id: 'tx-0001',
  date: day,
  payee: 'Ristorante',
  narration: 'dinner',
  state: 'pending',
  postings: [
    posting,
    {
      account: 'acc-food',
      amount: { commodity: eur, minor: 4990n },
      party: null,
      note: null,
      origin: null,
      tag: null,
    },
  ],
  labels: ['lab-trip'],
  source: { kind: 'imported', batch: 'batch-7', fingerprint: 'fp-abc' },
  attachments: ['sha-1', 'sha-2'],
}

const filter: Filter = {
  kind: 'and',
  a: {
    kind: 'or',
    a: { kind: 'account', under: 'Assets' },
    b: { kind: 'not', a: { kind: 'label', name: 'private' } },
  },
  b: {
    kind: 'and',
    a: { kind: 'dateFrom', d: day },
    b: { kind: 'amountTo', a: { commodity: eur, minor: 10000n } },
  },
}

const rule: Rule = {
  id: 'rule-1',
  name: 'groceries',
  filterSrc: 'payee:REWE',
  filter,
  setAccount: 'Expenses.Food',
  addLabels: ['food', 'weekly'],
  setParty: null,
  priority: -3n,
  realm: selfRealmId,
}

const group: PartyGroup = { name: 'flat', members: ['anna', 'ben'], realm: selfRealmId }

const trip_: Trip = {
  id: 'trip-zin',
  name: 'Zinalrothorn',
  starts: otherDay,
  ends: day,
  payer: 'party-anna',
  note: 'hut booked',
  realm: selfRealmId,
}

const batch: ImportBatch = {
  id: 'batch-7',
  profile: 'dkb',
  filename: 'export.csv',
  account: 'acc-giro',
  stamp: '2026-03-09T10:00:00',
  total: 42,
  duplicates: 3,
  realm: selfRealmId,
}

const participant: Participant = {
  owner: selfPartyId,
  name: 'me',
  account: 'Expenses.Travel',
  weight: 2,
}

const budget: Budget = {
  id: 'bud-1',
  name: 'Budget.Zinalrothorn2026',
  note: 'the hut trip',
  closed: false,
}

const attachment: Attachment = {
  sha256: 'aabbcc',
  mime: 'image/jpeg',
  bytes: 91234,
  origName: 'till.jpg',
  createdAt: '2026-03-09T10:00:00',
  cipherHash: null,
  wrappedKey: null,
}

/** The same file as a synced node knows it: uploaded, and sealed under a realm key. */
const uploaded: Attachment = {
  ...attachment,
  cipherHash: 'ddeeff',
  wrappedKey: '0000000000000000000000SELF:1:AAEC',
}

const lineItem: LineItem = {
  description: '18 FORFAIT 1/2 PENSION',
  qty: 18n,
  amount: { commodity: eur, minor: 122400n },
}

const extracted: Extracted = {
  merchant: 'Cabane',
  date: day,
  total: { commodity: eur, minor: 122400n },
  items: [],
  rawText: '18 FORFAIT…',
  extractor: 'tesseract',
}

const itemGroup: ItemGroup = {
  items: [
    { line: 1, qty: 6 },
    { line: 2, qty: null },
  ],
  into: 'acc-food',
}

const invoice: Invoice = {
  id: 'inv-1',
  number: '2026-0007',
  issued: otherDay,
  due: day,
  payerId: 'party-anna',
  payerName: 'Anna',
  commodity: eur,
  reference: 'RF18539007547034',
  status: 'sent',
  note: 'hut share',
  settledTxn: null,
  payment: { kind: 'epc', name: 'Christian', iban: 'DE0212030000', bic: 'GENODEF1XXX' },
  sourceAccount: 'Budget.Zinalrothorn2026',
  budgetId: 'bud-1',
  pendingTxn: 'tx-0002',
  lines: [
    {
      description: 'nights',
      qtyMilli: 18000n,
      unitPrice: { commodity: eur, minor: 6800n },
      taxBp: 1900n,
    },
  ],
}

const member: Member = { id: 'anna', name: 'Anna', party: 'party-anna' }

const realm: Realm = {
  id: 'realm-1',
  name: 'flat',
  members: [
    ['anna', 'admin'],
    ['ben', 'viewer'],
  ],
  generation: 3,
}

const blobState = {
  file: attachment,
  extracted,
  items: [lineItem],
  registeredBy: 'anna',
  realm: selfRealmId,
}

const budgetState = {
  budget,
  participants: [participant],
  realm: 'realm-1',
  account: 'acc-budget',
  label: 'lab-trip',
}

/** A state with something in most of its maps. */
function sampleState(): State {
  const s = initState()
  s.accounts.set('acc-giro', account)
  s.accounts.set('acc-food', {
    id: 'acc-food',
    name: 'Expenses.Food',
    kind: 'expense',
    owner: selfPartyId,
    commodity: null,
    iban: null,
    note: null,
    closedOn: null,
    realm: selfRealmId,
    bridgeOf: null,
    posters: [],
    mirrorOf: null,
  })
  s.parties.set('party-anna', party)
  s.labels.set('lab-trip', label)
  s.groups.set('flat', group)
  s.trips.set(trip_.name, trip_)
  s.rules.set('rule-1', rule)
  s.txns.set('tx-0001', txn)
  s.budgets.set('bud-1', budgetState)
  s.invoices.set('inv-1', { invoice, sources: ['tx-0001'], realm: selfRealmId })
  s.blobs.set('aabbcc', blobState)
  s.batches.set('batch-7', batch)
  s.counters.set(`${selfRealmId}:invoice:2026`, 7n)
  s.fingerprints.add('fp-abc')
  s.fingerprints.add('fp-def')
  return s
}

/** The same state, with every map filled in the opposite order. */
function shuffledState(): State {
  const s = sampleState()
  const giro = s.accounts.get('acc-giro')!
  const food = s.accounts.get('acc-food')!
  s.accounts = new Map([
    ['acc-food', food],
    ['acc-giro', giro],
  ])
  s.fingerprints = new Set(['fp-def', 'fp-abc'])
  return s
}

const ops: [string, Op][] = [
  ['createRealm', { tag: 0, kind: 'createRealm', realm }],
  ['putAccount', { tag: 1, kind: 'putAccount', account }],
  ['mergeAccounts', { tag: 2, kind: 'mergeAccounts', from: 'a', into: 'b' }],
  ['setAccountRights', { tag: 4, kind: 'setAccountRights', id: 'a', posters: ['anna'] }],
  ['putRule', { tag: 13, kind: 'putRule', rule }],
  ['putTransaction', { tag: 15, kind: 'putTransaction', txn }],
  [
    'mergeTransactions',
    {
      tag: 18,
      kind: 'mergeTransactions',
      ids: ['t1', 't2'],
      newId: 't3',
      payee: 'p',
      narration: null,
      cancelIn: ['a'],
    },
  ],
  [
    'divideByItems',
    { tag: 21, kind: 'divideByItems', id: 't1', groups: [itemGroup], newIds: ['t2', 't3'] },
  ],
  ['voidClaim', { tag: 24, kind: 'voidClaim', id: 't1', writeOff: ['a', 't9', day] }],
  [
    'allocate',
    {
      tag: 28,
      kind: 'allocate',
      budget: 'bud-1',
      among: [participant],
      commodity: eur,
      date: day,
      hub: selfPartyId,
      txnId: 't1',
      claimIds: ['t2'],
      labelId: 'lab-trip',
    },
  ],
  [
    'closeBudget',
    {
      tag: 30,
      kind: 'closeBudget',
      budget: 'bud-1',
      among: [participant],
      commodity: eur,
      hub: null,
      date: day,
      txnId: 't1',
      claimIds: [],
      labelId: 'lab-trip',
    },
  ],
  ['issueInvoice', { tag: 33, kind: 'issueInvoice', invoice, sources: ['tx-0001'] }],
  ['recordExtraction', { tag: 40, kind: 'recordExtraction', sha: 'aabbcc', extracted }],
  ['forgetBlob', { tag: 42, kind: 'forgetBlob', sha: 'aabbcc' }],
  [
    'grant',
    { tag: 46, kind: 'grant', realm: selfRealmId, member: 'anna', role: 'viewer', bridge: account },
  ],
  ['rotateRealmKey', { tag: 49, kind: 'rotateRealmKey', realm: selfRealmId }],
  ['snapshot', { tag: 50, kind: 'snapshot', state: sampleState() }],
  ['payClaim', { tag: 51, kind: 'payClaim', claim: 'c-1', payment: 'p-1', date: day }],
]

const changes: [string, Change][] = [
  ['realm', { tag: 0, kind: 'realm', realm }],
  ['accountDeleted', { tag: 4, kind: 'accountDeleted', id: 'a' }],
  ['rule', { tag: 12, kind: 'rule', rule }],
  ['txn', { tag: 14, kind: 'txn', txn }],
  ['blob', { tag: 20, kind: 'blob', blob: blobState }],
  ['counter', { tag: 23, kind: 'counter', name: `${selfRealmId}:invoice:2026`, value: 7n }],
  ['fingerprint', { tag: 24, kind: 'fingerprint', fp: 'fp-abc' }],
]

const event: LedgerEvent = {
  id: 'ev-1',
  author: 'anna',
  composedAt: '2026-03-09T10:00:00',
  basedOn: 12,
  parts: [
    { realm: selfRealmId, op: { tag: 1, kind: 'putAccount', account } },
    { realm: 'realm-1', op: { tag: 50, kind: 'snapshot', state: sampleState() } },
  ],
}

/* ------------------------------------------------------------------ */
/* Round trips                                                         */
/* ------------------------------------------------------------------ */

describe('round trips', () => {
  it('naturals, integers, strings and options', () => {
    for (const n of [0n, 127n, 128n, 300n, 123456789012345n, -300n, 1250n]) trip(intCodec, n)
    for (const s of ['', 'hello', 'Zinalrothorn · 3562 m — Wallis']) trip(stringCodec, s)
  })

  it('dates', () => {
    for (const d of [day, otherDay, { year: 1970, month: 1, day: 1 }, { year: 1, month: 1, day: 1 }]) {
      trip(dateCodec, d)
    }
  })

  it('money', () => {
    trip(commodityCodec, eur)
    trip(commodityCodec, commodityOfCode('JPY'))
    trip(amountCodec, { commodity: eur, minor: -4990n })
  })

  it('the ledger', () => {
    trip(accountKindCodec, 'expense')
    trip(accountCodec, account)
    trip(partyCodec, party)
    trip(labelCodec, label)
    trip(postingCodec, posting)
    trip(provenanceCodec, { kind: 'manual', actor: 'cli' })
    trip(provenanceCodec, { kind: 'imported', batch: 'batch-7', fingerprint: 'fp-abc' })
    trip(provenanceCodec, { kind: 'derived', rule: 'rule-1' })
    trip(txnStateCodec, 'pending')
    trip(transactionCodec, txn)
  })

  it('filters', () => {
    trip(filterCodec, { kind: 'all' })
    trip(filterCodec, { kind: 'commodity', code: 'EUR' })
    trip(filterCodec, filter)
    trip(filterCodec, {
      kind: 'not',
      a: {
        kind: 'not',
        a: {
          kind: 'not',
          a: {
            kind: 'and',
            a: { kind: 'all' },
            b: {
              kind: 'or',
              a: { kind: 'text', needle: 'a' },
              b: { kind: 'not', a: { kind: 'tag', name: 'b' } },
            },
          },
        },
      },
    })
  })

  it('entities', () => {
    trip(partyGroupCodec, group)
    trip(tripCodec, trip_)
    trip(ruleCodec, rule)
    trip(importBatchCodec, batch)
    trip(participantCodec, participant)
    trip(budgetCodec, budget)
  })

  it('receipts', () => {
    trip(attachmentCodec, attachment)
    trip(attachmentCodec, uploaded)
    trip(lineItemCodec, lineItem)
    trip(extractedCodec, extracted)
    trip(itemShareCodec, { line: 3, qty: 2 })
    trip(itemGroupCodec, itemGroup)
  })

  it('invoices', () => {
    trip(paymentRequestCodec, { kind: 'epc', name: 'C', iban: 'DE02', bic: 'GENO' })
    trip(paymentRequestCodec, { kind: 'link', url: 'https://example.org/pay' })
    trip(invoiceLineCodec, {
      description: 'nights',
      qtyMilli: 18000n,
      unitPrice: { commodity: eur, minor: 6800n },
      taxBp: 1900n,
    })
    trip(invoiceStatusCodec, 'paid')
    trip(invoiceCodec, invoice)
  })

  it('members, realms and the state’s parts', () => {
    trip(realmRoleCodec, 'admin')
    trip(memberCodec, member)
    trip(realmCodec, realm)
    trip(budgetStateCodec, budgetState)
    trip(invoiceStateCodec, { invoice, sources: ['tx-0001'], realm: selfRealmId })
    trip(blobStateCodec, blobState)
  })

  it('every operation', () => {
    for (const [, op] of ops) trip(opCodec, op)
  })

  it('every change', () => {
    for (const [, c] of changes) trip(changeCodec, c)
  })

  it('parts, events and states', () => {
    trip(partCodec, { realm: selfRealmId, op: { tag: 1, kind: 'putAccount', account } })
    trip(eventCodec, event)
    trip(stateCodec, sampleState())
    trip(stateCodec, emptyState())
    trip(stateCodec, initState())
  })

  it('a decoded state holds what the original held', () => {
    const s = sampleState()
    const back = decode(stateCodec, encode(stateCodec, s))
    expect(back.accounts.size).toBe(s.accounts.size)
    expect(back.txns.get('tx-0001')?.postings.length).toBe(2)
    expect(back.counters.get(`${selfRealmId}:invoice:2026`)).toBe(7n)
    expect([...back.fingerprints].sort()).toEqual(['fp-abc', 'fp-def'])
  })

  it('insertion order does not reach the bytes', () => {
    expect(toHex(encode(stateCodec, shuffledState()))).toBe(
      toHex(encode(stateCodec, sampleState())),
    )
  })

  it('two different states hash differently', () => {
    expect(sha256Hex(encode(stateCodec, sampleState()))).not.toBe(
      sha256Hex(encode(stateCodec, emptyState())),
    )
  })

  it('a signature over one event does not cover another', () => {
    expect(sha256Hex(encode(eventCodec, event))).not.toBe(
      sha256Hex(encode(eventCodec, { ...event, basedOn: 13 })),
    )
  })

  it('refuses trailing bytes and bad tags', () => {
    expect(() => decode(stringCodec, new Uint8Array([0x01, 0x61, 0x00]))).toThrow()
    expect(() => decode(accountKindCodec, new Uint8Array([0x09]))).toThrow()
    expect(() => decode(dateCodec, encode(dateCodec, { year: 2026, month: 2, day: 30 }))).toThrow()
  })
})

/* ------------------------------------------------------------------ */
/* Fixed bytes: the format itself                                      */
/* ------------------------------------------------------------------ */

describe('fixed bytes, copied from Test/Encode.lean', () => {
  it('naturals and integers', () => {
    // `Nat` is not a codec of its own here; the LEB128 it is built from shows
    // through the sign-plus-magnitude of an `Int` and the length of a `String`.
    bytesAre(intCodec, 300n, '00ac02')
    bytesAre(intCodec, -300n, '01ac02')
    bytesAre(intCodec, 0n, '0000')
  })

  it('LEB128 lengths', () => {
    // "Nat 0" = 00, "Nat 127" = 7f, "Nat 128" = 8001, "Nat 300" = ac02, seen
    // through a string of that many bytes.
    expect(toHex(encode(stringCodec, '')).slice(0, 2)).toBe('00')
    expect(toHex(encode(stringCodec, 'x'.repeat(127))).slice(0, 2)).toBe('7f')
    expect(toHex(encode(stringCodec, 'x'.repeat(128))).slice(0, 4)).toBe('8001')
    expect(toHex(encode(stringCodec, 'x'.repeat(300))).slice(0, 4)).toBe('ac02')
  })

  it('strings and options', () => {
    bytesAre(stringCodec, '', '00')
    bytesAre(stringCodec, 'hi', '026869')
    bytesAre(stringCodec, 'é', '02c3a9')
    const optionalString: Codec<string | null> = {
      write: (w, x) => w.option(x, (w2, s) => w2.str(s)),
      read: (r) => r.option((r2) => r2.str()),
    }
    bytesAre(optionalString, null, '00')
    bytesAre(optionalString, 'hi', '01026869')
    const natList: Codec<number[]> = {
      write: (w, xs) => w.list(xs, (w2, n) => w2.nat(n)),
      read: (r) => r.list((r2) => r2.nat()),
    }
    bytesAre(natList, [1, 2, 300], '030102ac02')
    const pair: Codec<[string, number]> = {
      write: (w, [s, n]) => {
        w.str(s)
        w.nat(n)
      },
      read: (r) => [r.str(), r.nat()],
    }
    bytesAre(pair, ['hi', 7], '02686907')
  })

  it('money and dates', () => {
    bytesAre(commodityCodec, eur, '0345555202')
    bytesAre(amountCodec, { commodity: eur, minor: -1250n }, '034555520201e209')
    bytesAre(dateCodec, day, '00ea0f00030009')
  })

  it('enumerations', () => {
    bytesAre(accountKindCodec, 'expense', '04')
    bytesAre(txnStateCodec, 'pending', '01')
    bytesAre(invoiceStatusCodec, 'paid', '02')
    bytesAre(realmRoleCodec, 'admin', '01')
  })

  it('tagged sums', () => {
    bytesAre(provenanceCodec, { kind: 'manual', actor: 'x' }, '000178')
    bytesAre(paymentRequestCodec, { kind: 'link', url: 'u' }, '010175')
    bytesAre(filterCodec, { kind: 'all' }, '00')
    bytesAre(filterCodec, { kind: 'not', a: { kind: 'label', name: 'x' } }, '0f060178')
    bytesAre(opCodec, { tag: 10, kind: 'deleteGroup', name: 'g' }, '0a0167')
    bytesAre(changeCodec, { tag: 24, kind: 'fingerprint', fp: 'f' }, '180166')
  })

  it('structures', () => {
    // The realm is the trailing field every entity gained at format-version 5:
    // written last, so a port that reads the old shape stops exactly where the
    // new one carries on. The long run is `Realm.selfId`.
    bytesAre(
      labelCodec,
      { id: 'l', name: 'n', colour: null, realm: selfRealmId },
      '016c016e00' + '1a3030303030303030303030303030303030303030303053454c46',
    )
    // An `Account` with nothing but the three fields that have no default: the
    // rest are Lean's defaults, which is what pins their order and their
    // encoding — the two long runs are `Party.selfId` and `Realm.selfId`.
    bytesAre(
      accountCodec,
      {
        id: 'a',
        name: 'n',
        kind: 'asset',
        owner: selfPartyId,
        commodity: null,
        iban: null,
        note: null,
        closedOn: null,
        realm: selfRealmId,
        bridgeOf: null,
        posters: [],
        mirrorOf: null,
      },
      '0161016e001a3030303030303030303030303030303030303030303053454c4600000000' +
        '1a3030303030303030303030303030303030303030303053454c46000000',
    )
    // The last two fields are the ones a synced node fills in: the hash of the
    // ciphertext it uploaded, and the per-blob key sealed under a realm key. A
    // local-only store writes two `none` bytes there, which is what a port that
    // does not sync still has to write.
    bytesAre(
      attachmentCodec,
      attachment,
      '066161626263630a696d6167652f6a706567e2c805010874696c6c2e6a7067' +
        '13323032362d30332d30395431303a30303a30300000',
    )
    bytesAre(
      attachmentCodec,
      uploaded,
      '066161626263630a696d6167652f6a706567e2c805010874696c6c2e6a7067' +
        '13323032362d30332d30395431303a30303a3030010664646565666601' +
        '213030303030303030303030303030303030303030303053454c463a313a41414543',
    )
  })

  it('the record that grew at format-version 6', () => {
    // `Test/Encode.lean`'s `InvoiceState bare`, byte for byte. An invoice knows
    // the realm it was issued in, and it is written last, after the outlays it
    // bills for — so a reader of the format-version 5 shape stops exactly where
    // this one carries on. The long run is `Realm.selfId`.
    bytesAre(
      invoiceStateCodec,
      {
        invoice: {
          id: 'i',
          number: 'n',
          issued: { year: 2026, month: 3, day: 9 },
          due: { year: 2026, month: 3, day: 9 },
          payerId: null,
          payerName: '',
          commodity: { code: 'EUR', exponent: 2 },
          reference: '',
          status: 'draft',
          note: null,
          settledTxn: null,
          payment: { kind: 'link', url: '' },
          sourceAccount: null,
          budgetId: null,
          pendingTxn: null,
          lines: [],
        },
        sources: [],
        realm: selfRealmId,
      },
      '0169016e' +
        '00ea0f0003000900ea0f00030009' +
        '0000' +
        '0345555202' +
        '00000000' +
        '0100' +
        '00000000' +
        '00' +
        '1a3030303030303030303030303030303030303030303053454c46',
    )
  })

  it('the records that grew at format-version 4 and 5', () => {
    // Their new fields are written last, so a port that reads the old shape
    // stops exactly where the new one carries on; these pin where "last" is.
    bytesAre(
      budgetStateCodec,
      {
        budget: { id: 'b', name: 'n', note: null, closed: false },
        participants: [],
        realm: selfRealmId,
        account: '',
        label: '',
      },
      '0162016e000000' + '1a3030303030303030303030303030303030303030303053454c4600' + '00',
    )
    bytesAre(
      blobStateCodec,
      {
        file: {
          sha256: 's',
          mime: 'm',
          bytes: 0,
          origName: null,
          createdAt: '',
          cipherHash: null,
          wrappedKey: null,
        },
        extracted: {
          merchant: null,
          date: null,
          total: null,
          items: [],
          rawText: '',
          extractor: '',
        },
        items: [],
        registeredBy: 'self',
        realm: selfRealmId,
      },
      '0173016d0000000000' +
        '000000000000' +
        '00' +
        '0473656c66' +
        '1a3030303030303030303030303030303030303030303053454c46',
    )
  })

  it('every record that gained a realm at format-version 5 writes it last', () => {
    // Not a literal from `Test/Encode.lean` — the two above are — but the same
    // statement made about the other five, which the conformance vectors cover
    // between them: the field is trailing, so an old reader stops exactly where
    // the new writer carries on.
    const mark = 'realm-1'
    const tail = toHex(encode(stringCodec, mark))
    expect(toHex(encode(partyCodec, { ...party, realm: mark })).endsWith(tail)).toBe(true)
    expect(toHex(encode(labelCodec, { ...label, realm: mark })).endsWith(tail)).toBe(true)
    expect(toHex(encode(partyGroupCodec, { ...group, realm: mark })).endsWith(tail)).toBe(true)
    expect(toHex(encode(tripCodec, { ...trip_, realm: mark })).endsWith(tail)).toBe(true)
    expect(toHex(encode(ruleCodec, { ...rule, realm: mark })).endsWith(tail)).toBe(true)
    expect(toHex(encode(importBatchCodec, { ...batch, realm: mark })).endsWith(tail)).toBe(true)
    expect(toHex(encode(blobStateCodec, { ...blobState, realm: mark })).endsWith(tail)).toBe(true)
  })

  it('the empty state hashes to what Lean says it does', () => {
    // The strongest single check in this file: it exercises every field of
    // `StateWire`, in order, through SHA-256.
    expect(sha256Hex(encode(stateCodec, emptyState()))).toBe(
      '5322fecfc92a5e3248a297a3df3eddfb9bd9049504272e4f572b87fa36d4b3bd',
    )
  })
})

/* ------------------------------------------------------------------ */
/* Bytes that must be refused                                          */
/* ------------------------------------------------------------------ */

/**
 * A decoder that takes more than the writer produces is a decoder that gives
 * one value two names, and a checkpoint is a name.
 *
 * `Core/Codec.lean` states this as `CanonicalCodec`: anything the reader
 * accepts is exactly what the writer would have written. It is proved there for
 * the primitives and every combinator over them; here it can only be tested, so
 * these are the spellings that used to be accepted.
 */
describe('the strict decoder, from the refusals in Test/Encode.lean', () => {
  /** The bytes of a hex string the test itself wrote. */
  function bytes(hex: string): Uint8Array {
    const bs = fromHex(hex)
    expect(bs).not.toBeNull()
    return bs as Uint8Array
  }

  function refuses<T>(codec: Codec<T>, hex: string): void {
    expect(() => decode(codec, bytes(hex))).toThrow(CodecError)
  }

  const natCodec: Codec<number> = {
    write: (w, n) => w.nat(n),
    read: (r) => r.nat(),
  }

  it('refuses overlong LEB128', () => {
    refuses(natCodec, '8000')
    refuses(natCodec, '8100')
    refuses(natCodec, '808000')
    // A canonical zero is still read, and so is a genuinely two-byte number.
    expect(decode(natCodec, bytes('00'))).toBe(0)
    expect(decode(natCodec, bytes('8001'))).toBe(128)
  })

  it('refuses negative zero', () => {
    refuses(intCodec, '0100')
    expect(decode(intCodec, bytes('0000'))).toBe(0n)
  })

  it('refuses trailing bytes', () => {
    refuses(intCodec, '00007f')
  })

  it('refuses an overlong length prefix', () => {
    refuses(stringCodec, '820068690000')
  })

  it('refuses numbers no ledger carries', () => {
    // Two bounds this port keeps and the core does not yet: a year a `number`
    // cannot hold exactly, and a commodity whose `scale` would be a bigint with
    // a million digits. Both are refusals rather than values, because a date
    // that is `Infinity` here and exact in Lean is a state the two would order
    // and hash differently, and the second is a stall on every load for ever.
    const far =
      toHex(encode(intCodec, 10n ** 30n)) +
      toHex(encode(intCodec, 2n)) +
      toHex(encode(intCodec, 2n))
    refuses(dateCodec, far)
    refuses(commodityCodec, '0345555214')
    // And the widest ones either will read are still read.
    expect(decode(dateCodec, bytes('00ea0f00030009'))).toEqual(day)
    expect(decode(commodityCodec, bytes('0345555212')).exponent).toBe(18)
  })

  it('refuses a state whose entries are not sorted', () => {
    const s = sampleState()
    s.labels.set('lab-a', { id: 'lab-a', name: 'a', colour: null, realm: selfRealmId })
    const out = sortedPairs(s.labels).reverse()
    expect(out.length).toBeGreaterThan(1)
    expect(() => decode(stateCodec, encodeWithLabels(s, out))).toThrow(CodecError)
  })

  it('refuses a state with a key twice, and one filed under a key that is not its id', () => {
    const s = sampleState()
    const doubled = encodeWithLabels(s, [
      ['lab-trip', s.labels.get('lab-trip')!],
      ['lab-trip', s.labels.get('lab-trip')!],
    ])
    expect(() => decode(stateCodec, doubled)).toThrow(CodecError)
    const misfiled = encodeWithLabels(s, [['not-its-id', s.labels.get('lab-trip')!]])
    expect(() => decode(stateCodec, misfiled)).toThrow(CodecError)
    // And the state it was made from is not refused.
    expect(() => decode(stateCodec, encode(stateCodec, s))).not.toThrow()
  })
})

/**
 * A state written with its label map spelled out entry by entry, so that a test
 * can write the orders and the duplicates a `Map` cannot hold.
 */
function encodeWithLabels(s: State, labels: readonly [string, Label][]): Uint8Array {
  const w = new Writer()
  writeStateWith(w, s, labels)
  return w.finish()
}

/** `stateCodec.write`, with the label section handed in rather than sorted. */
function writeStateWith(w: Writer, s: State, labels: readonly [string, Label][]): void {
  const section = <T,>(m: Map<string, T>, codec: Codec<T>): void => {
    const ps = sortedPairs(m)
    w.nat(ps.length)
    for (const [k, v] of ps) {
      w.str(k)
      codec.write(w, v)
    }
  }
  section(s.realms, realmCodec)
  section(s.members, memberCodec)
  section(s.accounts, accountCodec)
  w.nat(labels.length)
  for (const [k, v] of labels) {
    w.str(k)
    labelCodec.write(w, v)
  }
  section(s.parties, partyCodec)
  section(s.groups, partyGroupCodec)
  section(s.trips, tripCodec)
  section(s.rules, ruleCodec)
  section(s.txns, transactionCodec)
  section(s.budgets, budgetStateCodec)
  section(s.invoices, invoiceStateCodec)
  section(s.blobs, blobStateCodec)
  section(s.batches, importBatchCodec)
  section(s.counters, intCodec)
  w.list(sortedKeys(s.fingerprints), (w2, f) => w2.str(f))
}
