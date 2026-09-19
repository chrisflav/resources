/**
 * Applying an operation.
 *
 * A port of `Resources/Core/Apply.lean`, in full: every constructor of `Op` is
 * interpreted here, because the conformance vectors exercise every one of them
 * and a client that skipped some would be unable to reproduce the state a
 * checkpoint commits to. What the *user interface* offers is a much smaller
 * set — `appliedOps` — but that is a question about what a participant is
 * invited to do, not about what this file understands.
 *
 * Three rules from the Lean file run through every case below, and they are the
 * reason this is safe to run on a partial view. Nothing balances by accident —
 * every transaction goes through `validateTxn`. Nothing is implied — an
 * operation returns the full new value of every entity it touched. Nobody
 * writes where they may not — `canPost` is checked for every account involved,
 * and the operations that change a realm check that the author administers it.
 *
 * Failure is a sentence, and it is the same sentence Lean produces: a refused
 * operation writes nothing and its part of the event is skipped, never failing
 * the parts beside it.
 */

import {
  budgetAccount,
  budgetAccountName,
  budgetBalance,
  budgetLabel,
  divisionOf,
  settlementOf,
  shortName,
} from './budgets'
import {
  accountIsMine,
  claimAmount,
  claimPayer,
  claimReceiver,
  commodityCodes,
  compareDates,
  dropAccount,
  holdsMoney,
  mergeAll,
  origins,
  txnNetIn,
  unmerge,
  validateTxn,
  withOrigin,
} from './ledger'
import { eraseDups } from './bytes'
import { commodityInRange, dateInRange, filterInRange, sortedKeys } from './codec'
import { render, splitParts, sum } from './money'
import {
  accountByNameIn,
  accountOfId,
  budgetOfId,
  canAdminister,
  canPost,
  canPostLeg,
  cloneState,
  fundingAccounts,
  initState,
  invoiceOfId,
  isMember,
  isMemberOf,
  memberOfId,
  partyOfId,
  postingCount,
  realmOfAccount,
  realmOfId,
  rulesSorted,
  sortedPairs,
  sortedValues,
  txnOfId,
  txnsSorted,
  withMember,
  withoutMember,
} from './state'
import type {
  Account,
  Amount,
  BlobState,
  BudgetState,
  Change,
  Commodity,
  Date as LedgerDate,
  Filter,
  ImportBatch,
  Label,
  LedgerEvent,
  LineItem,
  Op,
  Part,
  Participant,
  Party,
  PartyGroup,
  Posting,
  Rule,
  State,
  Transaction,
  Trip,
} from './types'
import {
  claimTag,
  maxExponent,
  maxIdLength,
  maxClaims,
  maxLines,
  maxParticipants,
  maxParts,
  maxPostings,
  maxQty,
  maxTextLength,
  maxWeight,
  maxYear,
  minYear,
  selfMemberId,
  selfPartyId,
} from './types'

/** What applying one part came to. */
export type ApplyResult =
  /** Understood and applied: the new state and the entities it touched. */
  | { kind: 'ok'; state: State; changes: Change[] }
  /** Understood and refused, with the sentence saying why. */
  | { kind: 'error'; message: string }

/**
 * The operations this client offers to compose.
 *
 * Not the operations it understands — it understands all of them — but the ones
 * a participant is given a button for. Everything else arrives from somebody
 * else's node and is applied on the way past.
 */
export const appliedOps = [
  'putTransaction',
  'deleteTransaction',
  'resolveClaim',
  'payClaim',
  'setParticipants',
  'contribute',
  'allocate',
  'settle',
  'closeBudget',
  'reopenBudget',
] as const

/** Whether this client offers an operation in its own interface. */
export function isApplied(op: Op): boolean {
  return (appliedOps as readonly string[]).includes(op.kind)
}

/* ------------------------------------------------------------------ */
/* Reading what an operation names                                     */
/* ------------------------------------------------------------------ */

function accountOf(s: State, id: string): Account {
  const a = accountOfId(s, id)
  if (a === null) throw new Error(`no such account: ${id}`)
  return a
}

function txnOf(s: State, id: string): Transaction {
  const t = txnOfId(s, id)
  if (t === null) throw new Error(`no such transaction: ${id}`)
  return t
}

/** The import fingerprint a transaction carries, when it came off a bank line. */
function fingerprintOf(t: Transaction): string | null {
  return t.source.kind === 'imported' ? t.source.fingerprint : null
}

/** A posting with nothing but an account and an amount, as Lean's defaults leave it. */
function posting(account: string, amount: Amount, extra: Partial<Posting> = {}): Posting {
  return { account, amount, party: null, note: null, origin: null, tag: null, ...extra }
}

/* ------------------------------------------------------------------ */
/* Who may do this                                                     */
/* ------------------------------------------------------------------ */

/**
 * The baseline right an operation needs, before anything else it asks for.
 * `Resources.Rights`.
 */
export type Rights =
  /** The author has to be a member of this ledger; the realm is the one being made. */
  | 'known'
  /**
   * An admin of the part's realm, or the author speaking about themselves alone.
   *
   * Three operations have this door and all three are the same situation:
   * somebody who joined through an invite, whose admin was a link in a browser
   * rather than a node composing events. `addMember` writes their own record,
   * `grant` attests their own viewer role, and `putParty` revises the party
   * record their own spending lands on — the one entity a member owns outright,
   * and the reason they may revise it from any realm they are in.
   */
  | 'attest'
  /** Any member of the part's realm. */
  | 'member'
  /** An admin of the part's realm. */
  | 'admin'

/**
 * Who may perform each operation. `Op.rights`, case for case.
 *
 * The shape of the table is the decision: anything that changes who may read or
 * write — realms, members, accounts and the rights on them — is an admin's; so
 * is anything realm-wide that nothing else can undo, which is why the shared
 * vocabulary (labels, parties, groups, trips, rules, batches) and every budget
 * and invoice verb are admin's too. What a member may do on their own is write
 * transactions, and every one of those is checked leg by leg against
 * `canPostLeg` afterwards.
 *
 * It is total on purpose: an operation added without a rule does not compile.
 */
export function rightsOf(op: Op): Rights {
  switch (op.kind) {
    // Structure
    case 'createRealm':
      return 'known'
    case 'putAccount':
    case 'mergeAccounts':
    case 'deleteAccount':
    case 'setAccountRights':
    case 'setAccountOwner':
    case 'putLabel':
    case 'deleteLabel':
    case 'putGroup':
    case 'deleteGroup':
    case 'putTrip':
    case 'deleteTrip':
    case 'putRule':
    case 'deleteRule':
      return 'admin'
    // Transactions
    case 'putTransaction':
    case 'deleteTransaction':
    case 'splitTransaction':
    case 'mergeTransactions':
    case 'unmergeTransaction':
    case 'replaceTransaction':
    case 'divideByItems':
      return 'member'
    // Claims
    case 'raiseClaim':
      return 'admin'
    case 'resolveClaim':
    case 'voidClaim':
    case 'payClaim':
      return 'member'
    // Budgets
    case 'openBudget':
    case 'setParticipants':
    case 'contribute':
    case 'allocate':
    case 'settle':
    case 'closeBudget':
    case 'reopenBudget':
    case 'deleteBudget':
      return 'admin'
    // Taking a cost and giving it back are what everybody in the realm is there
    // to do, and the case itself checks that they take it for themselves.
    case 'claimCost':
    case 'releaseCost':
      return 'member'
    // Invoices
    case 'issueInvoice':
    case 'setInvoiceStatus':
    case 'settleInvoice':
    case 'deleteInvoice':
      return 'admin'
    // Attachments
    case 'registerBlob':
    case 'attach':
    case 'detach':
    case 'recordExtraction':
    case 'setReceiptLines':
      return 'member'
    case 'forgetBlob':
      return 'admin'
    // Import
    case 'recordImportBatch':
      return 'admin'
    // Members and realms
    case 'addMember':
    case 'grant':
      return 'attest'
    case 'removeMember':
    case 'revoke':
    case 'setRole':
    case 'rotateRealmKey':
      return 'admin'
    case 'putParty':
      return 'attest'
    // Genesis. Never consulted: `checkRights` refuses a snapshot before it reads
    // this table, because where a snapshot may be applied is a fact about the
    // reader's position in the log rather than about who wrote it. The strictest
    // rule there is stands here so that the table stays total and says nothing
    // weaker than the refusal.
    case 'snapshot':
      return 'admin'
  }
}

/**
 * Enforces `rightsOf`, once, before any of the state is read for effect.
 *
 * A grant, a revoke, a role and a rotation each name a realm of their own. The
 * only evidence anybody has that the author may speak at all is the grant the
 * sequencer holds for them on the realm the *part* names, so that is the only
 * realm they may speak about: a viewer of one realm writing themselves into
 * somebody else's was a door with nothing behind it.
 */
export function checkRights(s: State, author: string, realm: string, op: Op): void {
  // A snapshot is not an operation. It is what a log *starts from*, and where a
  // log starts is a fact about the reader's position in the order rather than
  // about the state the reader has managed to fold: a client that holds one
  // generation's key skips everything written under every other one and arrives
  // at a fresh-looking state part way along, from which one snapshot by anybody
  // still in the realm replaced the whole of it. So no part may carry one, ever,
  // and `replay` reads the genesis off position 1 instead.
  if (op.kind === 'snapshot') {
    throw new Error('a snapshot is where a log starts, not something a part may say')
  }
  if (
    op.kind === 'grant' ||
    op.kind === 'revoke' ||
    op.kind === 'setRole' ||
    op.kind === 'rotateRealmKey'
  ) {
    if (op.realm !== realm) throw new Error('a part can only change the realm it names')
  }
  switch (rightsOf(op)) {
    case 'known':
      if (memberOfId(s, author) === null) {
        throw new Error(`${author} is not a member of this ledger`)
      }
      return
    case 'attest': {
      // The self door, and the whole of it: your own record, your own view, or
      // the party your own spending lands on.
      const selfDoor =
        op.kind === 'addMember'
          ? op.member.id === author
          : op.kind === 'grant'
            ? op.member === author && op.role === 'viewer'
            : op.kind === 'putParty'
              ? (memberOfId(s, author)?.party ?? null) === op.party.id
              : false
      if (!(canAdminister(s, author, realm) || selfDoor)) {
        throw new Error('only an admin of that realm may do that for somebody else')
      }
      return
    }
    case 'member':
      if (!isMemberOf(s, author, realm)) throw new Error('you are not in that realm')
      return
    case 'admin':
      if (!canAdminister(s, author, realm)) {
        throw new Error('only an admin of that realm may do that')
      }
      return
  }
}

/* ------------------------------------------------------------------ */
/* How much of it                                                      */
/* ------------------------------------------------------------------ */

/**
 * Every list and every string an operation carries is bounded.
 *
 * A reader applies what an author sends it, and one short event naming a
 * quantity of a thousand million used to make every node and every browser
 * replaying the log allocate a list of that length. `Core/Apply.lean`'s
 * `checkBounds`, with the numbers of `Core/Event.lean`.
 */

/** Lean's `String.length`: code points, not UTF-16 units. */
function codePoints(v: string): number {
  let n = 0
  for (const _ of v) n++
  return n
}

function boundedName(what: string, v: string): void {
  if (codePoints(v) > maxIdLength) {
    throw new Error(`${what} is longer than ${maxIdLength} characters`)
  }
}

function boundedText(what: string, v: string): void {
  if (codePoints(v) > maxTextLength) {
    throw new Error(`${what} is longer than ${maxTextLength} characters`)
  }
}

function boundedNameOpt(what: string, v: string | null): void {
  if (v !== null) boundedName(what, v)
}

function boundedTextOpt(what: string, v: string | null): void {
  if (v !== null) boundedText(what, v)
}

function boundedList(what: string, xs: readonly unknown[], limit: number = maxParts): void {
  if (xs.length > limit) throw new Error(`${what}: at most ${limit} are allowed`)
}

/**
 * Refuses a date outside the years the ledger will take.
 *
 * Lean's `Date` is `PlainDate`, whose month and day are already a date by their
 * own types; only the year is an `Int` with nothing over it. A port whose date
 * is three numbers checks all four, and the other three are checked by
 * `dateCodec` as the bytes are read.
 */
function boundedDate(what: string, d: LedgerDate): void {
  if (!dateInRange(d)) {
    throw new Error(
      `${what} names the year ${d.year}, and a year has to be between ${minYear} and ${maxYear}`,
    )
  }
}

/** Refuses an optional date that is out of range. */
function boundedDateOpt(what: string, d: LedgerDate | null): void {
  if (d !== null) boundedDate(what, d)
}

/**
 * Refuses a commodity nothing can compute in.
 *
 * `scale` is `10 ** exponent`, so an exponent is the one field in an operation
 * that turns six bytes on the wire into a number with millions of digits.
 * Eighteen places is more than any currency has ever had.
 */
function boundedCommodity(c: Commodity): void {
  boundedName('a commodity code', c.code)
  if (!commodityInRange(c)) {
    throw new Error(
      `a commodity has at most ${maxExponent} decimal places, and ${c.code} claims ${c.exponent}`,
    )
  }
}

/** Refuses an optional commodity that is out of range. */
function boundedCommodityOpt(c: Commodity | null): void {
  if (c !== null) boundedCommodity(c)
}

/**
 * Refuses an amount whose commodity is one nothing can compute in.
 *
 * The count of minor units is deliberately *not* asked about here, exactly as
 * `boundedAmount` in `Core/Apply.lean` does not ask: it is bounded while the
 * bytes are read, by `amountCodec`'s `wf`, because it is a number a *state* may
 * not hold rather than a size an intent may not name.
 */
function boundedAmount(a: Amount): void {
  boundedCommodity(a.commodity)
}

/** Refuses an optional amount whose commodity is out of range. */
function boundedAmountOpt(a: Amount | null): void {
  if (a !== null) boundedAmount(a)
}

/** Refuses a filter comparing against a date or an amount that is out of range. */
function boundedFilter(what: string, f: Filter): void {
  if (!filterInRange(f)) {
    throw new Error(`${what} names a date or an amount outside what this ledger carries`)
  }
}

/** Everything a transaction carries, bounded. */
function boundedTxn(t: Transaction): void {
  boundedList("a transaction's postings", t.postings, maxPostings)
  boundedName('a transaction id', t.id)
  boundedDate("a transaction's date", t.date)
  boundedText('a narration', t.narration)
  boundedTextOpt('a payee', t.payee)
  boundedList("a transaction's labels", t.labels)
  boundedList("a transaction's attachments", t.attachments)
  if (t.items !== null) boundedItems(t.items)
  for (const l of t.labels) boundedName('a label id', l)
  for (const a of t.attachments) boundedName('an attachment hash', a)
  for (const p of t.postings) {
    boundedName('an account id', p.account)
    boundedAmount(p.amount)
    boundedTextOpt('a posting note', p.note)
    boundedNameOpt('a posting origin', p.origin)
    boundedNameOpt('a posting tag', p.tag)
  }
}

/** Everything an account carries, bounded. */
function boundedAccount(a: Account): void {
  boundedName('an account id', a.id)
  boundedName('an account name', a.name)
  boundedNameOpt('an iban', a.iban)
  boundedTextOpt('an account note', a.note)
  boundedList("an account's posters", a.posters)
  boundedDateOpt("an account's closing date", a.closedOn)
  boundedCommodityOpt(a.commodity)
}

/** The people a budget is divided among, bounded, weights included. */
function boundedParticipants(among: readonly Participant[]): void {
  boundedList("a budget's participants", among, maxParticipants)
  for (const p of among) {
    boundedName("a participant's account", p.account)
    boundedName("a participant's name", p.name)
    if (!Number.isInteger(p.weight) || p.weight < 1 || p.weight > maxWeight) {
      throw new Error(`a share's weight has to be between 1 and ${maxWeight}`)
    }
  }
  // The weights add up to how many parts `shareOut` cuts the money into, so the
  // sum is bounded as well as each of them.
  let total = 0
  for (const p of among) total += Math.max(p.weight, 1)
  if (total > maxParts) {
    throw new Error(`the weights of a division add up to more than ${maxParts}`)
  }
}

/** The lines printed on a receipt, bounded, quantities included. */
function boundedItems(items: readonly LineItem[]): void {
  boundedList("a receipt's lines", items, maxLines)
  for (const i of items) {
    boundedText("a line's description", i.description)
    boundedAmount(i.amount)
    if (i.qty !== null) {
      const abs = i.qty < 0n ? -i.qty : i.qty
      if (abs > BigInt(maxQty)) throw new Error(`a line covers at most ${maxQty} units`)
    }
  }
}

/** Everything an operation carries, bounded: the one place a size is refused. */
export function checkBounds(op: Op): void {
  switch (op.kind) {
    case 'createRealm':
      boundedName('a realm id', op.realm.id)
      boundedName('a realm name', op.realm.name)
      boundedList("a realm's members", op.realm.members)
      return
    case 'putAccount':
      boundedAccount(op.account)
      return
    case 'mergeAccounts':
      boundedName('an account id', op.from)
      boundedName('an account id', op.into)
      return
    case 'deleteAccount':
      boundedName('an account id', op.id)
      return
    case 'setAccountRights':
      boundedName('an account id', op.id)
      boundedList("an account's posters", op.posters)
      return
    case 'setAccountOwner':
      boundedName('an account id', op.id)
      boundedName('a party id', op.owner)
      return
    case 'putLabel':
      boundedName('a label id', op.label.id)
      boundedName('a label name', op.label.name)
      boundedNameOpt('a colour', op.label.colour)
      return
    case 'deleteLabel':
      boundedName('a label id', op.id)
      return
    case 'putParty':
      boundedName('a party id', op.party.id)
      boundedName('a party name', op.party.name)
      boundedNameOpt('an iban', op.party.iban)
      boundedNameOpt('an email', op.party.email)
      boundedTextOpt('a party note', op.party.note)
      return
    case 'putGroup':
      boundedName('a group name', op.group.name)
      boundedList("a group's members", op.group.members)
      for (const m of op.group.members) boundedName('a group member', m)
      return
    case 'deleteGroup':
      boundedName('a group name', op.name)
      return
    case 'putTrip':
      boundedName('a trip id', op.trip.id)
      boundedName('a trip name', op.trip.name)
      boundedName('a payer', op.trip.payer)
      boundedTextOpt('a trip note', op.trip.note)
      boundedDate("a trip's first day", op.trip.starts)
      boundedDate("a trip's last day", op.trip.ends)
      return
    case 'deleteTrip':
      boundedName('a trip name', op.name)
      return
    case 'putRule':
      boundedName('a rule id', op.rule.id)
      boundedName('a rule name', op.rule.name)
      boundedText('a filter', op.rule.filterSrc)
      boundedFilter("a rule's filter", op.rule.filter)
      boundedNameOpt('an account name', op.rule.setAccount)
      boundedNameOpt('a party', op.rule.setParty)
      boundedList("a rule's labels", op.rule.addLabels)
      for (const l of op.rule.addLabels) boundedName('a label', l)
      return
    case 'deleteRule':
      boundedName('a rule name', op.idOrName)
      return
    case 'putTransaction':
    case 'raiseClaim':
      boundedTxn(op.txn)
      return
    case 'contribute':
      boundedTxn(op.txn)
      return
    case 'deleteTransaction':
      boundedName('a transaction id', op.id)
      return
    case 'splitTransaction':
      boundedName('a transaction id', op.id)
      boundedList("a split's targets", op.targets)
      for (const a of op.targets) boundedName('an account id', a)
      return
    case 'mergeTransactions':
      boundedList("a merge's sources", op.ids)
      boundedName('a transaction id', op.newId)
      boundedTextOpt('a payee', op.payee)
      boundedTextOpt('a narration', op.narration)
      boundedList("a merge's cancellations", op.cancelIn)
      return
    case 'unmergeTransaction':
      boundedName('a transaction id', op.id)
      boundedList("an unmerge's fresh ids", op.newIds)
      return
    case 'replaceTransaction':
      boundedName('a transaction id', op.id)
      boundedList("a division's parts", op.parts)
      boundedName("a division's kind", op.kindName)
      for (const t of op.parts) boundedTxn(t)
      return
    case 'divideByItems':
      boundedName('a transaction id', op.id)
      boundedList("a division's groups", op.groups)
      boundedList("a division's fresh ids", op.newIds)
      for (const g of op.groups) {
        boundedName('an account id', g.into)
        boundedList("a group's lines", g.items, maxLines)
        for (const sh of g.items) {
          if ((sh.qty ?? 0) > maxQty) throw new Error(`a share covers at most ${maxQty} units`)
        }
      }
      return
    case 'resolveClaim':
      boundedName('a transaction id', op.id)
      boundedName('a transaction id', op.actual)
      boundedName('a transaction id', op.splitId)
      return
    case 'voidClaim':
      boundedName('a transaction id', op.id)
      if (op.writeOff !== null) {
        boundedName('an account id', op.writeOff[0])
        boundedName('a transaction id', op.writeOff[1])
        boundedDate("a write-off's date", op.writeOff[2])
      }
      return
    case 'openBudget':
      boundedName('a budget id', op.budget.id)
      boundedName('a budget name', op.budget.name)
      boundedTextOpt('a budget note', op.budget.note)
      boundedAccount(op.account)
      return
    case 'setParticipants':
      boundedName('a budget id', op.budget)
      boundedParticipants(op.among)
      return
    case 'allocate':
      boundedName('a budget id', op.budget)
      boundedParticipants(op.among)
      boundedCommodity(op.commodity)
      boundedDate("a division's date", op.date)
      boundedName('a transaction id', op.txnId)
      boundedList("a division's claim ids", op.claimIds)
      boundedName('a label id', op.labelId)
      return
    case 'settle':
      boundedName('a budget id', op.budget)
      boundedCommodity(op.commodity)
      boundedDate("a settlement's due date", op.due)
      boundedList("a settlement's claim ids", op.claimIds)
      boundedName('a label id', op.labelId)
      return
    case 'closeBudget':
      boundedName('a budget id', op.budget)
      boundedParticipants(op.among ?? [])
      boundedCommodity(op.commodity)
      boundedDate("a close's date", op.date)
      boundedName('a transaction id', op.txnId)
      boundedList("a close's claim ids", op.claimIds)
      boundedName('a label id', op.labelId)
      return
    case 'reopenBudget':
    case 'deleteBudget':
      boundedName('a budget id', op.budget)
      return
    case 'claimCost':
      boundedName('a budget id', op.budget)
      boundedName('a transaction id', op.txn)
      return
    case 'releaseCost':
      boundedName('a budget id', op.budget)
      boundedName('a transaction id', op.txn)
      boundedName('a member id', op.member)
      return
    case 'issueInvoice':
      boundedName('an invoice id', op.invoice.id)
      boundedName('an invoice number', op.invoice.number)
      boundedName('a payer', op.invoice.payerName)
      boundedTextOpt('an invoice note', op.invoice.note)
      boundedList("an invoice's lines", op.invoice.lines)
      boundedList("an invoice's sources", op.sources)
      boundedDate("an invoice's issue date", op.invoice.issued)
      boundedDate("an invoice's due date", op.invoice.due)
      boundedCommodity(op.invoice.commodity)
      for (const l of op.invoice.lines) {
        boundedText("a line's description", l.description)
        boundedAmount(l.unitPrice)
      }
      return
    case 'setInvoiceStatus':
      boundedName('an invoice id', op.id)
      return
    case 'settleInvoice':
      boundedName('an invoice id', op.id)
      boundedName('a transaction id', op.txn)
      return
    case 'deleteInvoice':
      boundedName('an invoice id', op.id)
      return
    case 'registerBlob':
      boundedName('a content hash', op.file.sha256)
      boundedName('a media type', op.file.mime)
      boundedNameOpt('a file name', op.file.origName)
      boundedName('a timestamp', op.file.createdAt)
      boundedNameOpt('a ciphertext hash', op.file.cipherHash)
      boundedTextOpt('a wrapped key', op.file.wrappedKey)
      return
    case 'attach':
    case 'detach':
      boundedName('a transaction id', op.txn)
      boundedName('a content hash', op.sha)
      return
    case 'recordExtraction':
      boundedName('a content hash', op.sha)
      boundedNameOpt('a merchant', op.extracted.merchant)
      boundedText('the text read off a receipt', op.extracted.rawText)
      boundedName('an extractor', op.extracted.extractor)
      boundedDateOpt("a receipt's date", op.extracted.date)
      boundedAmountOpt(op.extracted.total)
      boundedItems(op.extracted.items)
      return
    case 'setReceiptLines':
      boundedName('a content hash', op.sha)
      boundedItems(op.items)
      return
    case 'forgetBlob':
      boundedName('a content hash', op.sha)
      return
    case 'recordImportBatch':
      boundedName('a batch id', op.batch.id)
      boundedName('a profile', op.batch.profile)
      boundedNameOpt('a file name', op.batch.filename)
      boundedName('a timestamp', op.batch.stamp)
      return
    case 'addMember':
      boundedName('a member id', op.member.id)
      boundedName('a member name', op.member.name)
      boundedName('a party id', op.member.party)
      return
    case 'removeMember':
      boundedName('a member id', op.id)
      return
    case 'grant':
      boundedName('a realm id', op.realm)
      boundedName('a member id', op.member)
      boundedAccount(op.bridge)
      return
    case 'revoke':
    case 'setRole':
      boundedName('a realm id', op.realm)
      boundedName('a member id', op.member)
      return
    case 'rotateRealmKey':
      boundedName('a realm id', op.realm)
      return
    case 'snapshot':
      return
    case 'payClaim':
      boundedName('a transaction id', op.claim)
      boundedName('a transaction id', op.payment)
      boundedDate("a payment's date", op.date)
      return
  }
}

/* ------------------------------------------------------------------ */
/* Which realm an entry belongs to                                     */
/* ------------------------------------------------------------------ */

/**
 * Refuses an entry that belongs to another realm.
 *
 * Every entity the ledger keeps says which realm it is in, and the rule is one
 * line: a part may only speak about an entry of the realm it names. It used to
 * be that eight kinds of entry — labels, parties, groups, trips, rules, import
 * batches, stored receipts, and the invoice counter — had no realm at all, so
 * "an admin of the part's realm" reached across every realm a reader could open.
 * Anybody can manufacture that right: they create a realm, make themselves its
 * admin, hand you a key, and from inside it delete a label out of every
 * transaction you hold, rewrite any person in your books, install rules that
 * drive what your imports file where, and forget your receipts.
 */
function ofThisRealm(what: string, realm: string, entry: string): void {
  if (entry !== realm) throw new Error(`${what} is not in this realm`)
}

/**
 * The same, asked of an entry that may not be there yet.
 *
 * A key nothing is filed under is nobody's, so a `put` that names one is
 * creating it here rather than reaching into somewhere else.
 */
function ofThisRealmOpt<T>(
  name: (x: T) => string,
  of: (x: T) => string,
  realm: string,
  entry: T | undefined | null,
): void {
  if (entry === undefined || entry === null) return
  ofThisRealm(name(entry), realm, of(entry))
}

/* ------------------------------------------------------------------ */
/* Writing                                                             */
/* ------------------------------------------------------------------ */

/**
 * Checks that these postings may be written here: the account exists and
 * belongs to this realm, it is open, and the author may post to it.
 *
 * `allowed` names the accounts the caller has already established a right to,
 * which is how `payClaim` writes the two legs of a claim between purses neither
 * of which is the author's alone. It never excuses the other two checks: an
 * account named there still has to exist, be open, and be in this realm.
 */
function checkPostings(
  s: State,
  author: string,
  realm: string,
  ps: readonly Posting[],
  allowed: readonly string[] = [],
): void {
  for (const p of ps) {
    const a = accountOf(s, p.account)
    if (a.realm !== realm) throw new Error(`${a.name} is not in this realm`)
    if (a.closedOn !== null) throw new Error(`${a.name} is closed; it cannot take new postings`)
    if (!allowed.includes(p.account) && !canPostLeg(s, author, a, p.amount.minor)) {
      throw new Error(`you may not post to ${a.name}`)
    }
  }
}

/**
 * Checks that these legs are this realm's and that the author may write them.
 *
 * The check `checkPostings` makes about a part it is *writing*, asked about
 * legs that are already there: a transaction is not somebody's to retire, to
 * divide or to hang a receipt on unless every leg of it is in the realm the
 * part names and every one of them is a leg they could have written themselves.
 * Closure is left out on purpose — an account closed since is still an account
 * whose entries its own people may tidy up.
 */
function checkOwnLegs(
  s: State,
  author: string,
  realm: string,
  ps: readonly Posting[],
): void {
  for (const p of ps) {
    const a = accountOf(s, p.account)
    if (a.realm !== realm) throw new Error(`${a.name} is not in this realm`)
    if (!canPostLeg(s, author, a, p.amount.minor)) {
      throw new Error(`you may not post to ${a.name}`)
    }
  }
}

/**
 * The guard a rewrite makes about the transaction it is replacing.
 *
 * A `putTransaction` that names an id the ledger already has is a rewrite, and
 * the legs it is rewriting are this realm's. There have to be some — a part
 * with no leg here has nothing of this realm's to replace, and writing one
 * anyway was how the metadata of any transaction in the ledger, in any realm,
 * could be rewritten from a realm that had never seen it — and they have to be
 * legs this author could have written.
 */
function putGuard(s: State, author: string, realm: string, t: Transaction): void {
  const old = txnOfId(s, t.id)
  if (old === null) return
  // A claim is changed by a claim verb. `resolveClaim` and `voidClaim` both ask
  // who the claim is owed to; plain `putTransaction` asked nothing about what it
  // was replacing, so an author who could post both legs of a stored claim could
  // rewrite it as a posted transaction — which takes it out of the settlement
  // arithmetic and puts its amounts into every balance — without going through
  // either verb. The same door reached a settled claim, and so booked money that
  // had already moved a second time.
  if (old.state !== 'posted') {
    throw new Error(`${t.id} is ${old.state}; a claim is met or withdrawn, not overwritten`)
  }
  const here = old.postings.filter((p) => realmOfAccount(s, p.account) === realm)
  if (here.length === 0) throw new Error('that transaction has no leg in this realm')
  checkOwnLegs(s, author, realm, here)
}

/**
 * Whether this author may say what a stored receipt contains.
 *
 * Three ways, and they are the same person read three ways: the member who
 * filed the bytes, somebody who may post the transaction the receipt is hanging
 * on, or an admin of the realm. What a receipt says is what `divideByItems`
 * divides by, so rewriting one is rewriting a division that has not happened.
 */
function checkReceipt(
  s: State,
  author: string,
  realm: string,
  sha: string,
  b: BlobState,
): void {
  // The realm first, and before the three doors below: the second of them used
  // to ask nothing at all about where the bytes were filed, so whoever first
  // registered a receipt kept the right to rewrite what it said from a part in
  // any realm they held a key for — including after it had been attached to a
  // transaction in a realm they could not otherwise touch.
  ofThisRealm('that receipt', realm, b.realm)
  if (canAdminister(s, author, realm) || b.registeredBy === author) return
  const attached = txnsSorted(s).filter((t) => t.attachments.includes(sha))
  const entitled = attached.some((t) => {
    if (t.postings.length === 0) return false
    try {
      checkOwnLegs(s, author, realm, t.postings)
      return true
    } catch {
      return false
    }
  })
  if (!entitled) {
    throw new Error(
      'only the member who registered that receipt, somebody who may post what it ' +
        'belongs to, or an admin of that realm, may say what it contains',
    )
  }
}

/** Whether this author may speak about a claim: the member it is owed to, or an admin. */
function checkClaimParty(
  s: State,
  author: string,
  realm: string,
  claim: Transaction,
  verb: string,
): void {
  if (canAdminister(s, author, realm)) return
  const recv = claimReceiver(claim)
  if (recv === null) throw new Error('this claim has no receiving leg')
  const acc = accountOfId(s, recv)
  if (acc === null) throw new Error('the receiving account is gone')
  if (acc.bridgeOf !== author) {
    throw new Error(
      `only the member who is owed, or an admin of that realm, may ${verb} this claim`,
    )
  }
}

/** Puts a transaction into state, as the full new value of that entity. */
function written(s: State, t: Transaction): [State, Change] {
  const next = cloneState(s)
  next.txns.set(t.id, t)
  return [next, { tag: 14, kind: 'txn', txn: t }]
}

/** Takes a transaction out of state. */
function removed(s: State, id: string): [State, Change] {
  const next = cloneState(s)
  next.txns.delete(id)
  return [next, { tag: 15, kind: 'txnDeleted', id }]
}

/**
 * Writes one realm's legs of a transaction.
 *
 * The legs of `t.id` that sit in this realm are replaced and the metadata is
 * replaced wholesale; legs in other realms are kept, because they belong to a
 * part this author may not even be able to read.
 */
function putTxn(
  s: State,
  author: string,
  realm: string,
  txn: Transaction,
  allowed: readonly string[] = [],
): [State, Change[]] {
  checkPostings(s, author, realm, txn.postings, allowed)
  const t = validateTxn(txn)
  // A claim is exactly two legs: one account owes and one is owed, and
  // `claimAmount` reads what is asked for off the positive one. A pending
  // transaction with three balanced legs would be ambiguous about all three, so
  // it is refused here — this is the one door every transaction comes through.
  if (t.state === 'pending' && t.postings.length !== 2) {
    throw new Error('a claim is exactly two legs')
  }
  const old = txnOfId(s, t.id)
  // Other realms' legs are none of this part's business, so they stay.
  const kept = (old?.postings ?? []).filter((p) => realmOfAccount(s, p.account) !== realm)
  // The bound again, on what is about to be written rather than on what the
  // operation carried. `checkBounds` refuses a *submitted* transaction of more
  // than `maxPostings` legs; it says nothing about one an intent *computed*, and
  // a split across a hundred thousand targets, a merge of a hundred thousand
  // sources or a division into a hundred thousand parts each produce
  // transactions far larger than anything anybody sent. This is the one door
  // every written transaction comes through, so it is the one place a result can
  // be bounded at all.
  if (kept.length + t.postings.length > maxPostings) {
    throw new Error(
      `that would write a transaction of ${kept.length + t.postings.length} postings, ` +
        `and at most ${maxPostings} are allowed`,
    )
  }
  let st = s
  const changes: Change[] = []
  const fp = fingerprintOf(t)
  if (fp !== null) {
    if (st.fingerprints.has(fp) && (old === null ? null : fingerprintOf(old)) !== fp) {
      throw new Error(`this bank line has already been imported: ${fp}`)
    }
    if (!st.fingerprints.has(fp)) {
      st = cloneState(st)
      st.fingerprints.add(fp)
      changes.push({ tag: 24, kind: 'fingerprint', fp })
    }
  }
  const [st2, change] = written(st, { ...t, postings: [...kept, ...t.postings] })
  changes.push(change)
  return [st2, changes]
}

/**
 * Replaces a transaction with the parts it was divided into.
 *
 * Dividing is not unmerging: the parts may book their spending wherever they
 * belong. What may not differ is the funding — together they must take exactly
 * what the original took, out of exactly the accounts it took it from.
 */
function replaceParts(
  s: State,
  author: string,
  realm: string,
  id: string,
  parts: readonly Transaction[],
): [State, Change[]] {
  const t = txnOf(s, id)
  checkOwnLegs(s, author, realm, t.postings)
  if (parts.length === 0) throw new Error('a division has to leave something behind')
  for (const part of parts) {
    if (part.id === id) {
      throw new Error('a part cannot reuse the id of the transaction being divided')
    }
    try {
      validateTxn(part)
    } catch (e) {
      throw new Error(`a part does not balance: ${(e as Error).message}`)
    }
  }
  const codes = eraseDups([...commodityCodes(t), ...parts.flatMap(commodityCodes)])
  const accounts = eraseDups(
    [...t.postings, ...parts.flatMap((p) => p.postings)].map((p) => p.account),
  )
  for (const c of codes) {
    for (const a of accounts) {
      const before = txnNetIn(t, a, c)
      const after = sum(parts.map((p) => txnNetIn(p, a, c)))
      if ((before < 0n || after < 0n) && before !== after) {
        throw new Error(`the parts do not take the same money out of ${a} as the original did`)
      }
    }
  }
  const [s1, gone] = removed(s, id)
  let st = s1
  const changes: Change[] = [gone]
  for (const part of parts) {
    const [st2, cs] = putTxn(st, author, realm, part)
    st = st2
    changes.push(...cs)
  }
  return [st, changes]
}

/* ------------------------------------------------------------------ */
/* Budgets                                                             */
/* ------------------------------------------------------------------ */

function budgetOf(s: State, id: string): BudgetState {
  const b = budgetOfId(s, id)
  if (b === null) throw new Error(`no such budget: ${id}`)
  return b
}

/**
 * Checks that this author may decide things about a budget.
 *
 * A budget belongs to one realm, written down when it was opened, and the
 * people who may say what happens to it are the ones who administer that realm.
 * The part has to name it too: a decision about a budget reaches the people who
 * share it only if it is written under the key they hold.
 */
function checkBudget(s: State, author: string, realm: string, b: BudgetState): void {
  if (b.realm !== realm) throw new Error(`${shortName(b.budget)} is not in this realm`)
  if (!canAdminister(s, author, b.realm)) {
    throw new Error(`only an admin of that realm may decide about ${shortName(b.budget)}`)
  }
}

/**
 * Records the label a budget's claims are being raised under.
 *
 * `openBudget` pins it when the ledger already has a label of the budget's
 * name; otherwise the first division or settlement that raises claims says
 * which label they carry, and that is the one every later reading uses.
 */
function pinLabel(s: State, id: string, label: string): [State, Change[]] {
  const bs = s.budgets.get(id)
  if (bs === undefined) return [s, []]
  if (bs.label === label || label === '') return [s, []]
  const pinned: BudgetState = { ...bs, label }
  const st = cloneState(s)
  st.budgets.set(id, pinned)
  return [st, [{ tag: 16, kind: 'budget', budget: pinned }]]
}

/** Writes every transaction an intent produced, in order. */
function writeAll(
  s: State,
  author: string,
  realm: string,
  ts: readonly Transaction[],
  allowed: readonly string[] = [],
): [State, Change[]] {
  let st = s
  const changes: Change[] = []
  for (const t of ts) {
    const [st2, cs] = putTxn(st, author, realm, t, allowed)
    st = st2
    changes.push(...cs)
  }
  return [st, changes]
}

/** Raises, revises and withdraws the claims that square a budget up. */
function squareUp(
  s: State,
  author: string,
  realm: string,
  b: BudgetState,
  c: Commodity,
  hub: string | null,
  due: LedgerDate,
  claimIds: readonly string[],
  label: string,
): [State, Change[]] {
  return writeAll(s, author, realm, settlementOf(b.budget, s, c, hub, due, claimIds, label, author))
}

/** Divides what a budget holds and asks for what that leaves people owing. */
function divideUp(
  s: State,
  author: string,
  realm: string,
  b: BudgetState,
  among: readonly Participant[],
  c: Commodity,
  date: LedgerDate,
  txnId: string,
  hub: string | null,
  claimIds: readonly string[],
  label: string,
): [State, Change[], boolean] {
  const t = divisionOf(b.budget, s, realm, among, c, date, txnId, author)
  if (t === null) return [s, [], false]
  const [st, cs] = putTxn(s, author, realm, t)
  const [st2, cs2] = squareUp(st, author, realm, b, c, hub, date, claimIds, label)
  return [st2, [...cs, ...cs2], true]
}

/* ------------------------------------------------------------------ */
/* Invoice numbering                                                   */
/* ------------------------------------------------------------------ */

/** `Str.padLeft`: left-pads with `c` to at least `n` characters. */
function padLeft(s: string, n: number, c: string): string {
  const cs = Array.from(s)
  return cs.length >= n ? s : c.repeat(n - cs.length) + s
}

/** `Rf.sanitise`: the characters ISO 11649 allows, at most twenty-one of them. */
function rfSanitise(s: string): string {
  const upper = s.replace(/[a-z]/g, (c) => c.toUpperCase())
  return Array.from(upper)
    .filter((c) => /[A-Za-z0-9]/.test(c))
    .join('')
    .slice(0, 21)
}

/** `Rf.mod97`: `n mod 97` over the ISO 7064 expansion of a string. */
function rfMod97(s: string): number | null {
  let acc = 0
  for (const ch of s) {
    let v: number
    if (ch >= '0' && ch <= '9') v = ch.charCodeAt(0) - 48
    else if (ch >= 'A' && ch <= 'Z') v = ch.charCodeAt(0) - 65 + 10
    else return null
    acc = (acc * (v < 10 ? 10 : 100) + v) % 97
  }
  return acc
}

/** `Rf.make`: an ISO 11649 creditor reference, `RF` plus two check digits. */
function rfMake(base: string): string {
  const b = rfSanitise(base)
  const m = rfMod97(b + 'RF00')
  if (m === null) return 'RF00' + b
  return 'RF' + padLeft(String(98 - m), 2, '0') + b
}

/* ------------------------------------------------------------------ */
/* Applying                                                            */
/* ------------------------------------------------------------------ */

/**
 * Applies one operation, inside one realm, on behalf of one member.
 *
 * Either the whole effect or none of it: nothing is written when a check fails,
 * because every case below builds its new state before returning it.
 */
export function applyOp(s: State, author: string, realm: string, op: Op): ApplyResult {
  try {
    // Three steps, always in this order, and the first two are total functions
    // of the operation and of who wrote it. Nothing in `run` re-derives who may
    // act; what it adds is the part of a rule that depends on what the
    // operation *names* — the legs it writes, the claim it speaks about, the
    // receipt it rewrites.
    checkRights(s, author, realm, op)
    checkBounds(op)
    const [state, changes] = run(s, author, realm, op)
    return { kind: 'ok', state, changes }
  } catch (e) {
    return { kind: 'error', message: e instanceof Error ? e.message : String(e) }
  }
}

/** Applies one part of an event: its operation, in the realm it names. */
export function applyPart(s: State, author: string, p: Part): ApplyResult {
  return applyOp(s, author, p.realm, p.op)
}

/** What folding a whole event came to. `Resources.step`. */
export interface StepResult {
  state: State
  changes: Change[]
  /** The indices of the parts that were refused, and so skipped. */
  rejected: number[]
}

/**
 * Applies an event, part by part.
 *
 * Parts are independent, which is what makes a part the unit of sharing: a
 * reader who cannot read one realm's part goes on applying the others. An
 * invalid part is skipped for the same reason — it is a fact about that part,
 * not about the event — so this cannot fail.
 */
export function step(s: State, e: LedgerEvent): StepResult {
  let state = s
  const changes: Change[] = []
  const rejected: number[] = []
  e.parts.forEach((p, i) => {
    const result = applyPart(state, e.author, p)
    if (result.kind === 'ok') {
      state = result.state
      changes.push(...result.changes)
    } else {
      rejected.push(i)
    }
  })
  return { state, changes, rejected }
}

function run(s: State, author: string, realm: string, op: Op): [State, Change[]] {
  switch (op.kind) {
    /* ---------------- structure ---------------- */

    case 'createRealm': {
      if (realmOfId(s, op.realm.id) !== null) {
        throw new Error(`a realm with that id already exists: ${op.realm.id}`)
      }
      // The membership list is not the author's to choose. A realm created with
      // somebody else already inside it — or with a generation that says keys
      // have been rotated — is a realm whose history starts with a lie.
      const only = op.realm.members
      if (only.length !== 1 || only[0][0] !== author || only[0][1] !== 'admin') {
        throw new Error('a realm is created with its author as its only admin')
      }
      if (op.realm.generation !== 0) throw new Error('a new realm starts at generation 0')
      const st = cloneState(s)
      st.realms.set(op.realm.id, op.realm)
      return [st, [{ tag: 0, kind: 'realm', realm: op.realm }]]
    }

    case 'putAccount': {
      // An account that already exists keeps its owner, its realm and what it
      // mirrors: retagging somebody's account by mentioning its name in passing
      // is exactly the confusion an owner exists to prevent, moving it between
      // realms would move money out from under a key, and a mirror that could be
      // repointed afterwards would say two accounts are one balance when they
      // never were.
      const old = accountOfId(s, op.account.id)
      if (old !== null && old.realm !== realm) {
        throw new Error(`${old.name} is not in this realm`)
      }
      const merged: Account =
        old === null
          ? { ...op.account, realm }
          : {
              ...op.account,
              owner: old.owner,
              realm: old.realm,
              bridgeOf: old.bridgeOf,
              posters: old.posters,
              mirrorOf: old.mirrorOf,
            }
      const st = cloneState(s)
      st.accounts.set(merged.id, merged)
      return [st, [{ tag: 3, kind: 'account', account: merged }]]
    }

    case 'mergeAccounts': {
      if (op.from === op.into) throw new Error('an account cannot be merged into itself')
      const src = accountOf(s, op.from)
      const dst = accountOf(s, op.into)
      if (src.realm !== realm || dst.realm !== realm) {
        throw new Error('both accounts have to be in this realm')
      }
      // Both sides, not just the destination. A merge empties the account it
      // names and rebooks every posting that landed there, so asking only about
      // the destination let anybody pour somebody else's balance into their own.
      if (!canPost(s, author, src)) throw new Error(`you may not post to ${src.name}`)
      if (!canPost(s, author, dst)) throw new Error(`you may not post to ${dst.name}`)
      let st = s
      const changes: Change[] = []
      // Balance is untouched: each posting keeps its amount and only changes
      // which account it lands in.
      for (const t of txnsSorted(s)) {
        if (t.postings.some((p) => p.account === op.from)) {
          const moved: Transaction = {
            ...t,
            postings: t.postings.map((p) =>
              p.account === op.from ? { ...p, account: op.into } : p,
            ),
          }
          const [st2, c] = written(st, moved)
          st = st2
          changes.push(c)
        }
      }
      st = cloneState(st)
      st.accounts.delete(op.from)
      changes.push({ tag: 4, kind: 'accountDeleted', id: op.from })
      // A rule that filed things into the emptied account now files them into
      // the one that absorbed it.
      for (const r of rulesSorted(s)) {
        if (r.setAccount === op.from) {
          const moved = { ...r, setAccount: op.into }
          st = cloneState(st)
          st.rules.set(moved.id, moved)
          changes.push({ tag: 12, kind: 'rule', rule: moved })
        }
      }
      return [st, changes]
    }

    case 'deleteAccount': {
      const a = accountOf(s, op.id)
      if (a.realm !== realm) throw new Error(`${a.name} is not in this realm`)
      const n = postingCount(s, op.id)
      if (n > 0) throw new Error(`account still has ${n} postings; move them first`)
      const st = cloneState(s)
      st.accounts.delete(op.id)
      return [st, [{ tag: 4, kind: 'accountDeleted', id: op.id }]]
    }

    case 'setAccountRights': {
      const a = accountOf(s, op.id)
      if (a.realm !== realm) throw new Error(`${a.name} is not in this realm`)
      if (!canAdminister(s, author, a.realm)) {
        throw new Error(`only an admin of that realm may say who posts to ${a.name}`)
      }
      const opened: Account = { ...a, posters: op.posters }
      const st = cloneState(s)
      st.accounts.set(op.id, opened)
      return [st, [{ tag: 3, kind: 'account', account: opened }]]
    }

    case 'setAccountOwner': {
      const a = accountOf(s, op.id)
      if (a.realm !== realm) throw new Error(`${a.name} is not in this realm`)
      if (!canAdminister(s, author, a.realm)) {
        throw new Error(`only an admin of that realm may hand ${a.name} to somebody else`)
      }
      const handed: Account = { ...a, owner: op.owner }
      const st = cloneState(s)
      st.accounts.set(op.id, handed)
      return [st, [{ tag: 3, kind: 'account', account: handed }]]
    }

    case 'putLabel': {
      ofThisRealmOpt(
        (l: Label) => l.name,
        (l: Label) => l.realm,
        realm,
        s.labels.get(op.label.id),
      )
      const written_: Label = { ...op.label, realm }
      const st = cloneState(s)
      st.labels.set(op.label.id, written_)
      return [st, [{ tag: 5, kind: 'label', label: written_ }]]
    }

    case 'deleteLabel': {
      // A label nothing is filed under is nobody's, so deleting one is the no-op
      // it always was; one that is there is its realm's.
      ofThisRealmOpt((l: Label) => l.name, (l: Label) => l.realm, realm, s.labels.get(op.id))
      // The label is gone from the transactions that carried it too; a label id
      // nothing can resolve is worse than no label at all. Only from this realm's
      // transactions, though: the rewrite used to reach every transaction in
      // every realm the reader held, and deleting a budget's label that way made
      // its settled claims invisible, so the settlement asked a second time for
      // money that had already moved. A transaction with no leg here is not this
      // part's to rewrite, so rather than leave a label id nothing resolves, the
      // deletion is refused and the label stays.
      const stranded = txnsSorted(s).some(
        (t) =>
          t.labels.includes(op.id) &&
          !t.postings.some((p) => realmOfAccount(s, p.account) === realm),
      )
      if (stranded) {
        throw new Error(`${op.id} is on a transaction with no leg in this realm`)
      }
      let st = cloneState(s)
      st.labels.delete(op.id)
      const changes: Change[] = [{ tag: 6, kind: 'labelDeleted', id: op.id }]
      for (const t of txnsSorted(s)) {
        if (t.labels.includes(op.id)) {
          const stripped = { ...t, labels: t.labels.filter((l) => l !== op.id) }
          const [st2, c] = written(st, stripped)
          st = st2
          changes.push(c)
        }
      }
      return [st, changes]
    }

    case 'putParty': {
      // A member owns the record their own spending lands on, and holds it from
      // wherever they are: the party keeps the realm it was introduced in, and
      // the rule that let them write it is `checkRights`'s self door. Anybody
      // else's is an admin's, of the realm that person is recorded in.
      const old = partyOfId(s, op.party.id)
      if ((memberOfId(s, author)?.party ?? null) !== op.party.id) {
        ofThisRealmOpt((x: Party) => x.name, (x: Party) => x.realm, realm, old)
      }
      const written_: Party = { ...op.party, realm: old === null ? realm : old.realm }
      const st = cloneState(s)
      st.parties.set(op.party.id, written_)
      return [st, [{ tag: 7, kind: 'party', party: written_ }]]
    }

    case 'putGroup': {
      if (op.group.members.length === 0) throw new Error('a group needs at least one member')
      ofThisRealmOpt(
        (g: PartyGroup) => g.name,
        (g: PartyGroup) => g.realm,
        realm,
        s.groups.get(op.group.name),
      )
      const written_: PartyGroup = { ...op.group, realm }
      const st = cloneState(s)
      st.groups.set(op.group.name, written_)
      return [st, [{ tag: 8, kind: 'group', group: written_ }]]
    }

    case 'deleteGroup': {
      ofThisRealmOpt(
        (g: PartyGroup) => g.name,
        (g: PartyGroup) => g.realm,
        realm,
        s.groups.get(op.name),
      )
      const st = cloneState(s)
      st.groups.delete(op.name)
      return [st, [{ tag: 9, kind: 'groupDeleted', name: op.name }]]
    }

    case 'putTrip': {
      ofThisRealmOpt(
        (t: Trip) => t.name,
        (t: Trip) => t.realm,
        realm,
        s.trips.get(op.trip.name),
      )
      const written_: Trip = { ...op.trip, realm }
      const st = cloneState(s)
      st.trips.set(op.trip.name, written_)
      return [st, [{ tag: 10, kind: 'trip', trip: written_ }]]
    }

    case 'deleteTrip': {
      ofThisRealmOpt((t: Trip) => t.name, (t: Trip) => t.realm, realm, s.trips.get(op.name))
      const st = cloneState(s)
      st.trips.delete(op.name)
      return [st, [{ tag: 11, kind: 'tripDeleted', name: op.name }]]
    }

    case 'putRule': {
      ofThisRealmOpt((r: Rule) => r.name, (r: Rule) => r.realm, realm, s.rules.get(op.rule.id))
      const written_: Rule = { ...op.rule, realm }
      const st = cloneState(s)
      st.rules.set(op.rule.id, written_)
      return [st, [{ tag: 12, kind: 'rule', rule: written_ }]]
    }

    case 'deleteRule': {
      // This realm's rules of that name or id, and no others: a rule is removed
      // from the realm it drives imports in.
      const hits = rulesSorted(s).filter(
        (r) => (r.id === op.idOrName || r.name === op.idOrName) && r.realm === realm,
      )
      if (hits.length === 0) throw new Error(`no such rule: ${op.idOrName}`)
      const st = cloneState(s)
      const changes: Change[] = []
      for (const r of hits) {
        st.rules.delete(r.id)
        changes.push({ tag: 13, kind: 'ruleDeleted', id: r.id })
      }
      return [st, changes]
    }

    /* ---------------- transactions ---------------- */

    case 'putTransaction': {
      // An empty posting list is vacuously balanced, which used to make this the
      // way to rewrite the metadata of any transaction anywhere — including
      // voiding it, and so taking it out of every balance for every reader.
      if (op.txn.postings.length === 0) throw new Error('a transaction needs postings')
      // A transaction is written as something that happened. The three other
      // states belong to claims, and claims have their own verbs, each of which
      // asks who is entitled to say the thing it says.
      if (op.txn.state !== 'posted') {
        throw new Error('a transaction is written as posted; a claim is raised, met or withdrawn')
      }
      putGuard(s, author, realm, op.txn)
      return putTxn(s, author, realm, op.txn)
    }

    case 'deleteTransaction': {
      const t = txnOf(s, op.id)
      // Every leg, not merely the ones in this realm: a transaction that reaches
      // past this realm is not this part's to retire, and one inside it is only
      // retired by somebody who could have written it.
      checkOwnLegs(s, author, realm, t.postings)
      const [st, c] = removed(s, op.id)
      return [st, [c]]
    }

    /* ---------------- arithmetic intents ---------------- */

    case 'splitTransaction': {
      if (op.targets.length === 0) throw new Error('say who to split this with')
      const t = txnOf(s, op.id)
      checkOwnLegs(s, author, realm, t.postings)
      const funding = fundingAccounts(s)
      const shareCount = op.targets.length + (op.keepShare ? 1 : 0)
      const postings: Posting[] = []
      // Each leg is split separately, which keeps a card fee tagged as a fee
      // inside every share rather than smearing it into the principal.
      for (const p of t.postings) {
        if (funding.includes(p.account)) {
          postings.push(p)
          continue
        }
        const parts = splitParts(p.amount.minor, shareCount)
        const mine = op.keepShare ? parts.slice(0, 1) : []
        const theirs = op.keepShare ? parts.slice(1) : parts
        for (const m of mine) {
          if (m !== 0n) postings.push({ ...p, amount: { commodity: p.amount.commodity, minor: m } })
        }
        theirs.forEach((share, i) => {
          const target = op.targets[i]
          if (target !== undefined && share !== 0n) {
            postings.push({
              ...p,
              account: target,
              amount: { commodity: p.amount.commodity, minor: share },
            })
          }
        })
      }
      let split: Transaction
      try {
        split = validateTxn({ ...t, postings })
      } catch (e) {
        throw new Error(`splitting would not balance: ${(e as Error).message}`)
      }
      return putTxn(s, author, realm, split)
    }

    case 'mergeTransactions': {
      if (op.ids.length < 2) throw new Error('merging needs at least two transactions')
      const sources = op.ids.map((id) => {
        const src = txnOf(s, id)
        checkOwnLegs(s, author, realm, src.postings)
        return src
      })
      // A source's own postings may already carry origins from an earlier
      // import; anything unstamped is attributed to the transaction it came
      // from.
      const stamped = sources.map((t) => withOrigin(t, t.id))
      const head = stamped[0]
      const merged = mergeAll(head, stamped.slice(1))
      const weight = (t: Transaction): bigint =>
        sum(t.postings.map((p) => (p.amount.minor < 0n ? -p.amount.minor : p.amount.minor)))
      // The "principal" source is the one carrying the largest movement; its
      // payee and narration describe the combined event best.
      let principal = head
      for (const t of stamped) if (weight(t) > weight(principal)) principal = t
      let date = head.date
      for (const t of stamped) if (compareDates(t.date, date) < 0) date = t.date
      let result: Transaction = {
        ...merged,
        id: op.newId,
        date,
        payee: op.payee ?? principal.payee,
        narration: op.narration ?? principal.narration,
      }
      // The `Unclassified` legs auto-balancing created on both halves of a
      // transfer cancel once the halves are in one transaction.
      for (const a of op.cancelIn) result = dropAccount(result, a)
      let checked: Transaction
      try {
        checked = validateTxn(result)
      } catch (e) {
        throw new Error(`merge would not balance: ${(e as Error).message}`)
      }
      let st = s
      const changes: Change[] = []
      // The sources go first, so merging into an id one of them held still writes.
      for (const t of sources) {
        const [st2, c] = removed(st, t.id)
        st = st2
        changes.push(c)
      }
      const [st3, cs] = putTxn(st, author, realm, checked)
      return [st3, [...changes, ...cs]]
    }

    case 'unmergeTransaction': {
      const t = txnOf(s, op.id)
      checkOwnLegs(s, author, realm, t.postings)
      const os = origins(t)
      if (os.length < 2) {
        throw new Error('this transaction came from a single entry; there is nothing to unmerge')
      }
      if (t.postings.some((p) => p.origin === null)) {
        throw new Error('some postings have no origin; unmerging would lose them')
      }
      if (op.newIds.length < os.length) {
        throw new Error(
          `unmerging this needs ${os.length} new ids, and ${op.newIds.length} were given`,
        )
      }
      const parts = unmerge(t, op.newIds.slice(0, os.length))
      for (const part of parts) {
        try {
          validateTxn(part)
        } catch (e) {
          throw new Error(`unmerging would leave an unbalanced part: ${(e as Error).message}`)
        }
      }
      const [s1, gone] = removed(s, op.id)
      let st = s1
      const changes: Change[] = [gone]
      for (const part of parts) {
        const [st2, cs] = putTxn(st, author, realm, part)
        st = st2
        changes.push(...cs)
      }
      return [st, changes]
    }

    case 'replaceTransaction':
      return replaceParts(s, author, realm, op.id, op.parts)

    case 'divideByItems':
      return divideByItems(s, author, realm, op.id, op.groups, op.newIds)

    /* ---------------- claims ---------------- */

    case 'raiseClaim': {
      const t = op.txn
      if (t.state !== 'pending') {
        throw new Error('a claim is a transaction that has not happened; raise it as pending')
      }
      const asked = claimAmount(t)
      if (asked.minor <= 0n) throw new Error('a claim has to ask for something')
      const recv = claimReceiver(t)
      if (recv === null) throw new Error('this claim has no receiving leg')
      const pay = claimPayer(t)
      if (pay === null) throw new Error('this claim has no paying leg')
      if (recv === pay) throw new Error('a claim between one account and itself asks for nothing')
      // Both legs are tagged, so a claim is recognisable leg by leg wherever it sits.
      const tagged: Transaction = {
        ...t,
        postings: t.postings.map((p) => ({ ...p, tag: p.tag ?? claimTag })),
      }
      return putTxn(s, author, realm, tagged)
    }

    case 'resolveClaim': {
      const claim = txnOfId(s, op.id)
      if (claim === null) throw new Error(`no such claim: ${op.id}`)
      // Whose decision it is that a claim has been met: the person who would
      // have seen the money arrive, or an admin. The debtor saying so is a
      // receipt they wrote themselves.
      checkClaimParty(s, author, realm, claim, 'meet')
      // The two legs are the claim's own and the right to meet it was settled
      // above, so the poster check is that authorisation rather than `canPost` —
      // exactly as `voidClaim` and `payClaim` already do it. Without this the
      // right the table grants the receiver was unreachable: settling writes the
      // claim back, and the claim's paying leg is the *debtor's* purse, which the
      // receiver cannot post to.
      const allowed = [claimPayer(claim), claimReceiver(claim)].filter(
        (a): a is string => a !== null,
      )
      return settleClaim(s, author, realm, op.id, op.actual, op.splitId, allowed)
    }

    case 'payClaim':
      return payClaim(s, author, realm, op.claim, op.payment, op.date)

    case 'voidClaim': {
      const claim = txnOfId(s, op.id)
      if (claim === null) throw new Error(`no such claim: ${op.id}`)
      // Only an outstanding one. Withdrawing a claim that has been *met* used to
      // take the payment it recorded out of the settlement arithmetic, so the
      // same money was asked for a second time.
      if (claim.state !== 'pending') {
        throw new Error('only an outstanding claim can be withdrawn')
      }
      // Withdrawing is the creditor's decision. The debtor withdrawing the claim
      // against them is simply not paying.
      checkClaimParty(s, author, realm, claim, 'withdraw')
      let st = s
      const changes: Change[] = []
      // The spending stays where the division put it: somebody consumed it, and
      // their not paying turns it into your loss rather than your consumption.
      if (op.writeOff !== null) {
        const [into, entryId, date] = op.writeOff
        const payAcc = claimPayer(claim)
        if (payAcc === null) throw new Error('this claim has no paying leg to write off')
        const loss = accountOf(s, into)
        if (!accountIsMine(loss)) {
          throw new Error(`${loss.name} is not yours, so the loss cannot land there`)
        }
        const amount = claimAmount(claim)
        const entry: Transaction = {
          id: entryId,
          date,
          payee: claim.payee,
          narration: `written off: ${claim.narration}`,
          state: 'posted',
          postings: [
            posting(loss.id, amount),
            posting(payAcc, { commodity: amount.commodity, minor: -amount.minor }),
          ],
          labels: claim.labels,
          source: { kind: 'manual', actor: author },
          attachments: [],
          items: null,
        }
        let checked: Transaction
        try {
          checked = validateTxn(entry)
        } catch (e) {
          throw new Error(`the write-off would not balance: ${(e as Error).message}`)
        }
        const [st2, cs] = putTxn(st, author, realm, checked)
        st = st2
        changes.push(...cs)
      }
      // The two legs are the claim's own and the right to withdraw it was
      // settled above, so the poster check here is that authorisation rather
      // than `canPost` — a claim between two purses belongs to neither alone.
      const allowed = [claimPayer(claim), claimReceiver(claim)].filter(
        (a): a is string => a !== null,
      )
      const [st3, cs] = putTxn(st, author, realm, { ...claim, state: 'void' }, allowed)
      return [st3, [...changes, ...cs]]
    }

    /* ---------------- budgets ---------------- */

    case 'openBudget': {
      const full = budgetAccountName(op.budget.name)
      // Opening a budget that is already open says nothing new.
      const already = sortedValues(s.budgets).find(
        (x) => x.budget.id === op.budget.id || (x.realm === realm && x.budget.name === full),
      )
      if (already !== undefined) return [s, [{ tag: 16, kind: 'budget', budget: already }]]
      // Equity, deliberately: a budget balance is not wealth you hold. You have
      // already parted with it, and the part that turns out to be your own share
      // is never coming back.
      //
      // An account of that name in this realm is adopted, and only if it is what
      // a pot is. Reaching across realms for it would put the pot under a key the
      // realm opening it does not hold; adopting whatever is there was worse,
      // because the attest door mints accounts with a name of the author's
      // choosing — so a viewer who self-granted a purse called `Budget.Hut`
      // before the admin opened `Hut` had the pot adopted as their own bridge,
      // which they may post to in either direction. Three questions say an
      // account is a pot and nobody's purse, and an account of that name that
      // fails any of them is a refusal rather than an adoption.
      const standing = accountByNameIn(s, realm, full)
      let acc: Account
      if (standing !== null) {
        if (standing.kind !== 'equity') {
          throw new Error(`${full} is already an account of another kind in this realm`)
        }
        if (standing.bridgeOf !== null) {
          throw new Error(`${full} is somebody's purse in this realm; a budget cannot be held in it`)
        }
        if (standing.posters.length > 0) {
          throw new Error(`${full} already names its own posters; a budget cannot be held in it`)
        }
        acc = standing
      } else {
        if (accountOfId(s, op.account.id) !== null) {
          throw new Error(`an account with that id already exists: ${op.account.id}`)
        }
        acc = { ...op.account, name: full, kind: 'equity', realm, bridgeOf: null }
      }
      // The label is pinned by id here when this realm already has one of the
      // budget's name; when it does not, the first division or settlement says
      // which label its claims carry, and that one is recorded then.
      //
      // In this realm, like every other lookup that still goes by name. The
      // label pinned here is what `claims` reads the budget's claims out of, so
      // a label of the budget's name written in any realm a reader could open
      // used to decide which claims a budget could see.
      const lbl =
        sortedValues(s.labels).find(
          (l) => l.name === budgetLabel(op.budget) && l.realm === realm,
        ) ?? null
      const opened: BudgetState = {
        budget: { ...op.budget, name: full, closed: false },
        participants: [],
        claims: [],
        realm,
        account: acc.id,
        label: lbl === null ? '' : lbl.id,
      }
      const st = cloneState(s)
      st.accounts.set(acc.id, acc)
      st.budgets.set(op.budget.id, opened)
      return [
        st,
        [
          { tag: 3, kind: 'account', account: acc },
          { tag: 16, kind: 'budget', budget: opened },
        ],
      ]
    }

    case 'setParticipants': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      // Costs already booked keep the division they were booked under.
      const weighed = op.among.map((p) => ({ ...p, weight: Math.max(p.weight, 1) }))
      const named: BudgetState = { ...bs, participants: weighed }
      const st = cloneState(s)
      st.budgets.set(op.budget, named)
      return [st, [{ tag: 16, kind: 'budget', budget: named }]]
    }

    case 'contribute': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      if (bs.budget.closed) {
        throw new Error(`${shortName(bs.budget)} is closed; reopen it to add costs`)
      }
      const acc = budgetAccount(bs.budget, s)
      if (acc === null) throw new Error(`${shortName(bs.budget)} has no account of its own`)
      const spent = eraseDups(commodityCodes(op.txn)).some(
        (code) => txnNetIn(op.txn, acc.id, code) > 0n,
      )
      if (!spent) throw new Error('a contribution has to be an amount that was spent')
      return putTxn(s, author, realm, op.txn)
    }

    case 'allocate': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      const [st, changes] = divideUp(
        s,
        author,
        realm,
        bs,
        op.among,
        op.commodity,
        op.date,
        op.txnId,
        op.hub,
        op.claimIds,
        op.labelId,
      )
      const [st2, pinned] = pinLabel(st, op.budget, op.labelId)
      return [st2, [...changes, ...pinned]]
    }

    case 'settle': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      const [st, changes] = squareUp(
        s,
        author,
        realm,
        bs,
        op.commodity,
        op.hub,
        op.due,
        op.claimIds,
        op.labelId,
      )
      const [st2, pinned] = pinLabel(st, op.budget, op.labelId)
      return [st2, [...changes, ...pinned]]
    }

    case 'closeBudget': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      if (bs.budget.closed) throw new Error(`${shortName(bs.budget)} is already closed`)
      const people = op.among ?? bs.participants
      if (people.length === 0) {
        throw new Error(
          `say who shares ${shortName(bs.budget)} first: budget among ${shortName(bs.budget)} anna= …`,
        )
      }
      // eslint-disable-next-line prefer-const
      let [st, changes, divided] = divideUp(
        s,
        author,
        realm,
        bs,
        people,
        op.commodity,
        op.date,
        op.txnId,
        op.hub,
        op.claimIds,
        op.labelId,
      )
      // Dividing settles as it goes; with nothing left to divide there is still
      // the chance that a claim was written off or an invoice voided since.
      if (!divided && budgetBalance(bs.budget, st, op.commodity).minor === 0n) {
        const [st2, cs] = squareUp(
          st,
          author,
          realm,
          bs,
          op.commodity,
          op.hub,
          op.date,
          op.claimIds,
          op.labelId,
        )
        st = st2
        changes = [...changes, ...cs]
      }
      // Closed last on purpose: a failure between dividing and closing leaves
      // the budget open, and closing again divides only what is still waiting.
      const closed: BudgetState = {
        ...bs,
        budget: { ...bs.budget, closed: true },
        label: op.labelId === '' ? bs.label : op.labelId,
      }
      const next = cloneState(st)
      next.budgets.set(op.budget, closed)
      return [next, [...changes, { tag: 16, kind: 'budget', budget: closed }]]
    }

    case 'reopenBudget': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      if (!bs.budget.closed) throw new Error(`${shortName(bs.budget)} is already open`)
      // Nothing that was decided is undone.
      const opened: BudgetState = { ...bs, budget: { ...bs.budget, closed: false } }
      const st = cloneState(s)
      st.budgets.set(op.budget, opened)
      return [st, [{ tag: 16, kind: 'budget', budget: opened }]]
    }

    case 'deleteBudget': {
      const bs = budgetOf(s, op.budget)
      checkBudget(s, author, realm, bs)
      // The transactions it touched are left alone: what was decided stays decided.
      const st = cloneState(s)
      st.budgets.delete(op.budget)
      return [st, [{ tag: 17, kind: 'budgetDeleted', id: bs.budget.id }]]
    }

    case 'claimCost': {
      const bs = budgetOf(s, op.budget)
      ofThisRealm('that budget', realm, bs.realm)
      // Membership rather than `checkBudget`: taking a cost is what everybody in
      // the realm is there to do, and it is the one thing about a budget that is
      // not an admin's.
      if (!isMemberOf(s, author, realm)) {
        throw new Error('only somebody in that realm may take a cost of its budget')
      }
      if (bs.budget.closed) {
        throw new Error(`${shortName(bs.budget)} is closed; what everybody bore is decided`)
      }
      const t = txnOf(s, op.txn)
      // A cost *of this budget*: something with a leg on its account.
      if (!t.postings.some((p) => p.account === bs.account)) {
        throw new Error('that is not a cost in this budget')
      }
      if (bs.claims.some((c) => c.txn === op.txn && c.member === author)) {
        throw new Error('you have taken that one already')
      }
      if (bs.claims.length >= maxClaims) {
        throw new Error(`a budget carries at most ${maxClaims} claims`)
      }
      const taken: BudgetState = {
        ...bs,
        claims: [...bs.claims, { txn: op.txn, member: author }],
      }
      const st = cloneState(s)
      st.budgets.set(op.budget, taken)
      return [st, [{ tag: 16, kind: 'budget', budget: taken }]]
    }

    case 'releaseCost': {
      const bs = budgetOf(s, op.budget)
      ofThisRealm('that budget', realm, bs.realm)
      if (!isMemberOf(s, author, realm)) {
        throw new Error('only somebody in that realm may give back a cost of its budget')
      }
      if (bs.budget.closed) {
        throw new Error(`${shortName(bs.budget)} is closed; what everybody bore is decided`)
      }
      // Your own, or anybody's if you run the budget.
      if (op.member !== author && !canAdminister(s, author, realm)) {
        throw new Error(
          'only the person who took a cost, or an admin of that realm, may give it back',
        )
      }
      if (!bs.claims.some((c) => c.txn === op.txn && c.member === op.member)) {
        throw new Error('there is nothing of theirs on that cost to give back')
      }
      const given: BudgetState = {
        ...bs,
        claims: bs.claims.filter((c) => !(c.txn === op.txn && c.member === op.member)),
      }
      const st = cloneState(s)
      st.budgets.set(op.budget, given)
      return [st, [{ tag: 16, kind: 'budget', budget: given }]]
    }

    /* ---------------- invoices ---------------- */

    case 'issueInvoice': {
      const inv = op.invoice
      if (invoiceOfId(s, inv.id) !== null) {
        throw new Error(`an invoice with that id already exists: ${inv.id}`)
      }
      // Gapless, per year, and allocated here rather than by the caller: a gap
      // in invoice numbers is a question an auditor asks and nobody can answer
      // afterwards.
      // Keyed by realm. One counter for the whole ledger meant that an admin of
      // any realm a reader could open moved the ledger owner's invoice sequence:
      // burning numbers with `issueInvoice` or winding it back with
      // `deleteInvoice`.
      const year = Math.max(0, inv.issued.year)
      const counter = `${realm}:invoice:${year}`
      const n = (s.counters.get(counter) ?? 0n) + 1n
      const number = `${year}-` + padLeft(String(n), 4, '0')
      // The payer is looked up by name, so an invoice to somebody you already
      // know is addressed to the person rather than to a second record of them.
      //
      // In this realm, and nowhere else. The lookup used to be the first party
      // of that name in id order across every realm a reader could open, and a
      // member may set the name of their own party to anything at all from any
      // realm they are in (`putParty` goes through the attest door). So a member
      // whose party id sorted low renamed it to a customer's name, and every
      // invoice the ledger owner afterwards issued to that name was addressed to
      // them instead: the `payerId`, the reference, and the receivable in every
      // standing. Nothing was refused and nothing looked wrong.
      const known =
        sortedValues(s.parties).find((p) => p.name === inv.payerName && p.realm === realm) ?? null
      const payer = known !== null ? known.id : inv.payerId
      if (payer === null) {
        throw new Error(
          `there is nobody called ${inv.payerName} in this realm; give the invoice a payer id`,
        )
      }
      const st = cloneState(s)
      const changes: Change[] = []
      if (known === null && !s.parties.has(payer)) {
        // Created here, like every other new entry: a party introduced by an
        // invoice belongs to the realm the invoice was issued in.
        const p: Party = {
          id: payer,
          name: inv.payerName,
          iban: null,
          email: null,
          note: null,
          kind: 'merchant',
          realm,
        }
        st.parties.set(payer, p)
        changes.push({ tag: 7, kind: 'party', party: p })
      }
      const raised = {
        invoice: {
          ...inv,
          number,
          payerId: payer,
          reference: rfMake(number.split('-').join('')),
        },
        sources: op.sources,
        realm,
      }
      st.invoices.set(inv.id, raised)
      st.counters.set(counter, n)
      return [
        st,
        [
          ...changes,
          { tag: 23, kind: 'counter', name: counter, value: n },
          { tag: 18, kind: 'invoice', invoice: raised },
        ],
      ]
    }

    case 'setInvoiceStatus': {
      const inv = invoiceOfId(s, op.id)
      if (inv === null) throw new Error(`no such invoice: ${op.id}`)
      // An invoice is a document one realm sent to somebody, so what it says it
      // is now is that realm's to say. Without this an admin of any realm a
      // reader could open marked any invoice in the ledger `paid` or `void`.
      ofThisRealm(`invoice ${inv.invoice.number}`, realm, inv.realm)
      const moved = { ...inv, invoice: { ...inv.invoice, status: op.status } }
      const st = cloneState(s)
      st.invoices.set(op.id, moved)
      return [st, [{ tag: 18, kind: 'invoice', invoice: moved }]]
    }

    case 'settleInvoice': {
      const inv = invoiceOfId(s, op.id)
      if (inv === null) throw new Error(`no such invoice: ${op.id}`)
      ofThisRealm(`invoice ${inv.invoice.number}`, realm, inv.realm)
      txnOf(s, op.txn)
      const paid = {
        ...inv,
        invoice: { ...inv.invoice, status: 'paid' as const, settledTxn: op.txn },
      }
      const st = cloneState(s)
      st.invoices.set(op.id, paid)
      return [st, [{ tag: 18, kind: 'invoice', invoice: paid }]]
    }

    case 'deleteInvoice': {
      const inv = invoiceOfId(s, op.id)
      if (inv === null) throw new Error(`no such invoice: ${op.id}`)
      // The realm that handed the number out is the one that may give it back.
      // The counter is keyed by realm, so a part from somewhere else deleting
      // this invoice wound back a sequence that had never issued it: the issuing
      // realm kept the burnt number, and the next invoice in the other realm
      // duplicated one already sent.
      ofThisRealm(`invoice ${inv.invoice.number}`, realm, inv.realm)
      // Only a draft may go: once a number has been sent to somebody it has to
      // be voided instead, because they have seen it.
      if (inv.invoice.status !== 'draft') {
        throw new Error(
          `invoice ${inv.invoice.number} is ${inv.invoice.status}; ` +
            'void it rather than deleting it',
        )
      }
      const st = cloneState(s)
      st.invoices.delete(op.id)
      const changes: Change[] = [{ tag: 19, kind: 'invoiceDeleted', id: op.id }]
      // The year's counter goes back when the number that is going was the last
      // one it handed out, so removing an invoice raised by mistake leaves no hole.
      const bits = inv.invoice.number.split('-')
      if (bits.length === 2) {
        const [year, seqNo] = bits
        const counter = `${inv.realm}:invoice:${year}`
        const held = st.counters.get(counter) ?? 0n
        if (/^\d+$/.test(seqNo) && BigInt(seqNo) === held) {
          st.counters.set(counter, held - 1n)
          changes.push({ tag: 23, kind: 'counter', name: counter, value: held - 1n })
        }
      }
      return [st, changes]
    }

    /* ---------------- attachments ---------------- */

    case 'registerBlob': {
      // Storing the same bytes twice is one file and one record, so a second
      // registration says nothing new about the file itself — not its size, not
      // its name, and never what was read off it.
      //
      // Two fields are the exception, and they are the two that are not about
      // the bytes but about where a copy of them is kept: the hash of the
      // ciphertext and the key that opens it. A receipt filed in one realm and
      // then attached to a transaction in another is sealed again under that
      // realm's key, and the re-registration is how the new sealing reaches
      // everybody who can read the second realm. A registration that carries
      // neither leaves both as they were, which is what makes storing the same
      // bytes twice a no-op still.
      const old = s.blobs.get(op.file.sha256)
      if (old !== undefined) {
        // Re-sealing somebody else's file is a decision about where their bytes
        // are kept and which key opens them, so it is theirs or an admin's — and
        // an admin of the realm the record is *in*, rather than of the realm the
        // part names. That is what the second door used to be missing: it asked
        // nothing at all about where the bytes had been filed, so an admin of any
        // realm a reader could open could re-seal any receipt in the ledger.
        //
        // The record then moves to the realm the part names, and this is the one
        // operation that may move one. A receipt is filed in whichever realm it
        // was scanned in and attached to a payment that may be in another, and
        // everybody who can read that payment has to be able to read the paper
        // behind it — so the re-seal and the attachment are one event, in the
        // payment's realm. The receipt follows the payment, and with it the right
        // to say what it contains.
        if (old.registeredBy !== author && !canAdminister(s, author, old.realm)) {
          throw new Error(
            'only the member who registered that file, or an admin of the realm it was ' +
              'filed in, may register it again',
          )
        }
        const rewrapped: BlobState = {
          ...old,
          realm,
          file: {
            ...old.file,
            cipherHash: op.file.cipherHash ?? old.file.cipherHash,
            wrappedKey: op.file.wrappedKey ?? old.file.wrappedKey,
          },
        }
        const st = cloneState(s)
        st.blobs.set(op.file.sha256, rewrapped)
        return [st, [{ tag: 20, kind: 'blob', blob: rewrapped }]]
      }
      const b: BlobState = {
        file: op.file,
        extracted: {
          merchant: null,
          date: null,
          total: null,
          items: [],
          rawText: '',
          extractor: '',
        },
        items: [],
        registeredBy: author,
        realm,
      }
      const st = cloneState(s)
      st.blobs.set(op.file.sha256, b)
      return [st, [{ tag: 20, kind: 'blob', blob: b }]]
    }

    case 'attach': {
      const t = txnOf(s, op.txn)
      checkOwnLegs(s, author, realm, t.postings)
      if (!s.blobs.has(op.sha)) throw new Error(`no such receipt: ${op.sha}`)
      if (t.attachments.includes(op.sha)) return [s, [{ tag: 14, kind: 'txn', txn: t }]]
      const [st, c] = written(s, { ...t, attachments: [...t.attachments, op.sha] })
      return [st, [c]]
    }

    case 'detach': {
      const t = txnOf(s, op.txn)
      checkOwnLegs(s, author, realm, t.postings)
      const [st, c] = written(s, {
        ...t,
        attachments: t.attachments.filter((a) => a !== op.sha),
      })
      return [st, [c]]
    }

    case 'recordExtraction': {
      const b = s.blobs.get(op.sha)
      if (b === undefined) throw new Error(`no such receipt: ${op.sha}`)
      checkReceipt(s, author, realm, op.sha, b)
      const read = {
        ...b,
        extracted: { ...op.extracted, items: [] },
        items: op.extracted.items,
      }
      const st = cloneState(s)
      st.blobs.set(op.sha, read)
      return [st, [{ tag: 20, kind: 'blob', blob: read }]]
    }

    case 'setReceiptLines': {
      const b = s.blobs.get(op.sha)
      if (b === undefined) throw new Error(`no such receipt: ${op.sha}`)
      checkReceipt(s, author, realm, op.sha, b)
      // Lines are allowed to fall short of the total — paper folds, and a
      // service charge is nobody's line — but never to overrun it.
      const stated = b.extracted.total
      if (stated !== null && stated.minor !== 0n) {
        const used = sum(op.items.map((l) => l.amount.minor))
        const magnitude = used < 0n ? -used : used
        const limit = stated.minor < 0n ? -stated.minor : stated.minor
        if (magnitude > limit) {
          throw new Error(`that would take the lines past the ${render(stated)} on this receipt`)
        }
      }
      const lined = { ...b, items: op.items }
      const st = cloneState(s)
      st.blobs.set(op.sha, lined)
      return [st, [{ tag: 20, kind: 'blob', blob: lined }]]
    }

    case 'forgetBlob': {
      // Forgetting is not detaching: the bytes are already gone from the store
      // by the time this is applied, so only somebody who administers the realm
      // may do it.
      if (!canAdminister(s, author, realm)) {
        throw new Error('only an admin of that realm may forget a receipt')
      }
      const gone = s.blobs.get(op.sha)
      if (gone === undefined) throw new Error(`no such receipt: ${op.sha}`)
      ofThisRealm('that receipt', realm, gone.realm)
      const st = cloneState(s)
      st.blobs.delete(op.sha)
      return [st, [{ tag: 21, kind: 'blobDeleted', sha: op.sha }]]
    }

    /* ---------------- import ---------------- */

    case 'recordImportBatch': {
      ofThisRealmOpt(
        (b: ImportBatch) => `the import ${b.id}`,
        (b: ImportBatch) => b.realm,
        realm,
        s.batches.get(op.batch.id),
      )
      const written_: ImportBatch = { ...op.batch, realm }
      const st = cloneState(s)
      st.batches.set(op.batch.id, written_)
      return [st, [{ tag: 22, kind: 'batch', batch: written_ }]]
    }

    /* ---------------- members and realms ---------------- */

    case 'addMember': {
      // Two ways somebody gets into the books. An admin of this realm writes
      // them in, which is how you record a person you are about to let in; or a
      // member introduces themselves, which is the only way somebody who joined
      // through an invite ever reaches the log at all — the admin's node was not
      // there. The sequencer took their part for this realm only because it
      // already holds a grant for them here, so the log may take their word for
      // who they are, and for nothing else.
      //
      // "Who they are" is the whole of it, and the party is part of who they
      // are. A self-introduction naming somebody else's party — or the ledger's
      // own — would attribute the newcomer's spending to that person in every
      // budget standing and every invoice, so a newcomer may only name a party
      // nobody has yet, or the one already recorded for them.
      if (!canAdminister(s, author, realm)) {
        const existing = memberOfId(s, op.member.id)
        if (existing !== null) {
          // Somebody the ledger already knows is saying so again, which is what
          // the owner of a ledger does when they open a second realm. The party
          // is the one thing they may not revise.
          if (existing.party !== op.member.party) {
            throw new Error('a member cannot change the party their spending lands on')
          }
        } else {
          // A newcomer. `selfPartyId` is what `accountIsMine` tests, so taking
          // it would make their spending the ledger owner's; taking somebody
          // else's would attribute it to that person in every budget standing.
          if (op.member.party === selfPartyId) {
            throw new Error('a member cannot introduce themselves as the ledger\'s own party')
          }
          if (sortedValues(s.members).some((x) => x.party === op.member.party)) {
            throw new Error('that party is already somebody else\'s')
          }
          if (partyOfId(s, op.member.party) !== null) {
            throw new Error('that party is already in the books; an admin has to write you in')
          }
        }
      }
      const st = cloneState(s)
      st.members.set(op.member.id, op.member)
      if (partyOfId(s, op.member.party) !== null) {
        return [st, [{ tag: 1, kind: 'member', member: op.member }]]
      }
      // A member names the party their own spending lands on, and a remote
      // reader has no other record of a newcomer. Writing the party here is what
      // keeps that reference from dangling for everybody downstream.
      // A member names the party their own spending lands on, and it is written
      // in the realm the part names — the one everybody who can read this can
      // read.
      const party: Party = {
        id: op.member.party,
        name: op.member.name,
        iban: null,
        email: null,
        note: null,
        kind: 'contact',
        realm,
      }
      st.parties.set(party.id, party)
      return [
        st,
        [
          { tag: 7, kind: 'party', party },
          { tag: 1, kind: 'member', member: op.member },
        ],
      ]
    }

    case 'removeMember': {
      if (op.id === selfMemberId) {
        throw new Error('the member this ledger belongs to cannot be removed')
      }
      if (memberOfId(s, op.id) === null) throw new Error(`no such member: ${op.id}`)
      // What an admin of one realm may do is put somebody out of *that* realm.
      // The identity itself is shared with every other realm they are in, so it
      // goes only when nothing is left pointing at it.
      const st = cloneState(s)
      const changes: Change[] = []
      const r = realmOfId(s, realm)
      if (r !== null && isMember(r, op.id)) {
        const closed = withoutMember(r, op.id)
        st.realms.set(realm, closed)
        changes.push({ tag: 0, kind: 'realm', realm: closed })
      }
      if (!sortedValues(st.realms).some((x) => isMember(x, op.id))) {
        st.members.delete(op.id)
        changes.push({ tag: 2, kind: 'memberDeleted', id: op.id })
      }
      return [st, changes]
    }

    case 'grant': {
      // An admin lets somebody in; or a member attests their own viewer grant,
      // which is what a joiner does once an invite has been spent. The sequencer
      // accepted a part for this realm from them only because it already holds a
      // grant for them here, so the claim is one somebody has checked. It buys a
      // view and nothing else: a self-granted admin role would be a realm taken
      // over by the person writing the takeover down.
      const r = realmOfId(s, op.realm)
      if (r === null) throw new Error(`no such realm: ${op.realm}`)
      const m = memberOfId(s, op.member)
      if (m === null) throw new Error(`cannot grant an unknown member: add ${op.member} first`)
      const opened = withMember(r, op.member, op.role)
      if (canAdminister(s, author, op.realm)) {
        // An admin's grant, which is the ordinary one. An account that is already
        // there stays exactly as it is: a grant hands out a purse; it is not a
        // way to move somebody's account between realms, which would move money
        // out from under a key while transactions still point at it.
        // By name *in this realm*. The unscoped lookup found the first account
        // of that name in any realm and then refused the grant because it was
        // elsewhere — and `Members.<name>` is a name any member can mint about
        // themselves through the attest door, in any realm they may write in. So
        // one member could block an admin from granting a bridge of that name in
        // every other realm, for ever. It failed closed, so it was a denial
        // rather than a capture; it is still not a rule anybody would write down.
        const old = accountOfId(s, op.bridge.id) ?? accountByNameIn(s, op.realm, op.bridge.name)
        if (old !== null) {
          if (old.realm !== op.realm) {
            throw new Error(`${old.name} is in another realm; a grant cannot move it`)
          }
          const st = cloneState(s)
          st.realms.set(op.realm, opened)
          return [st, [{ tag: 0, kind: 'realm', realm: opened }]]
        }
        // The bridge is how they hold a balance here: it is theirs, in this
        // realm, and it is the one account they may always post to. Whose it is
        // comes from the member record rather than from the operation.
        const purse: Account = {
          ...op.bridge,
          owner: m.party,
          realm: op.realm,
          bridgeOf: op.member,
          mirrorOf: null,
        }
        const st = cloneState(s)
        st.realms.set(op.realm, opened)
        st.accounts.set(purse.id, purse)
        return [
          st,
          [
            { tag: 0, kind: 'realm', realm: opened },
            { tag: 3, kind: 'account', account: purse },
          ],
        ]
      }
      // The attest door, and the whole of what it may make: one purse, named
      // after the member it belongs to, of the one kind money is held in, with
      // nobody else on it and mirroring nothing.
      //
      // Everything else in `bridge` is ignored, and that is the fix. The door is
      // open to any member about themselves, and it used to write the operation's
      // `name`, `kind`, `posters`, `iban` and `note` verbatim — so a viewer could
      // mint an account per grant, of any name and kind, in a realm they merely
      // read, postable by them without limit. Nothing is adopted here either: a
      // name or an id that is already spoken for in this realm is a refusal,
      // because a joiner taking over an account that is already there is the same
      // hole read backwards.
      const name = `Members.${m.name}`
      if (accountOfId(s, op.bridge.id) !== null) {
        throw new Error(`an account with that id already exists: ${op.bridge.id}`)
      }
      if (accountByNameIn(s, op.realm, name) !== null) {
        throw new Error(`${name} is already an account in that realm; an admin has to let you in`)
      }
      const attested: Account = {
        id: op.bridge.id,
        name,
        kind: 'asset',
        owner: m.party,
        commodity: null,
        iban: null,
        note: null,
        closedOn: null,
        realm: op.realm,
        bridgeOf: op.member,
        posters: [],
        mirrorOf: null,
      }
      const st = cloneState(s)
      st.realms.set(op.realm, opened)
      st.accounts.set(attested.id, attested)
      return [
        st,
        [
          { tag: 0, kind: 'realm', realm: opened },
          { tag: 3, kind: 'account', account: attested },
        ],
      ]
    }

    case 'revoke': {
      const r = realmOfId(s, op.realm)
      if (r === null) throw new Error(`no such realm: ${op.realm}`)
      // The generation moves, because what they have already seen they have
      // seen; what is written from here on is under a key they do not hold.
      const closed = { ...withoutMember(r, op.member), generation: r.generation + 1 }
      const st = cloneState(s)
      st.realms.set(op.realm, closed)
      return [st, [{ tag: 0, kind: 'realm', realm: closed }]]
    }

    case 'setRole': {
      const r = realmOfId(s, op.realm)
      if (r === null) throw new Error(`no such realm: ${op.realm}`)
      if (r.members.find(([id]) => id === op.member) === undefined) {
        throw new Error(`${op.member} is not in that realm`)
      }
      const changed = withMember(r, op.member, op.role)
      const st = cloneState(s)
      st.realms.set(op.realm, changed)
      return [st, [{ tag: 0, kind: 'realm', realm: changed }]]
    }

    case 'rotateRealmKey': {
      const r = realmOfId(s, op.realm)
      if (r === null) throw new Error(`no such realm: ${op.realm}`)
      const rotated = { ...r, generation: r.generation + 1 }
      const st = cloneState(s)
      st.realms.set(op.realm, rotated)
      return [st, [{ tag: 0, kind: 'realm', realm: rotated }]]
    }

    /* ---------------- genesis ---------------- */

    case 'snapshot':
      // Unreachable: `checkRights` refuses a snapshot before `run` is called at
      // all. It is refused here too so that the two doors say the same thing,
      // and so that nothing reaches a whole state through this one.
      throw new Error('a snapshot is where a log starts, not something a part may say')
  }
}

/* ------------------------------------------------------------------ */
/* Genesis, and where a log starts                                     */
/* ------------------------------------------------------------------ */

/**
 * Everything a whole state amounts to, as changes, in sorted order.
 *
 * The list a store projects to hold exactly this state, however its tables are
 * keyed — and the one list that cannot leave an entity out, which is why a
 * rebuild and a genesis are the same statement made to two different places.
 * `Resources.snapshotChanges`.
 */
export function snapshotChanges(g: State): Change[] {
  return [
    ...sortedValues(g.realms).map((r): Change => ({ tag: 0, kind: 'realm', realm: r })),
    ...sortedValues(g.members).map((m): Change => ({ tag: 1, kind: 'member', member: m })),
    ...sortedValues(g.accounts).map((a): Change => ({ tag: 3, kind: 'account', account: a })),
    ...sortedValues(g.labels).map((l): Change => ({ tag: 5, kind: 'label', label: l })),
    ...sortedValues(g.parties).map((p): Change => ({ tag: 7, kind: 'party', party: p })),
    ...sortedValues(g.groups).map((x): Change => ({ tag: 8, kind: 'group', group: x })),
    ...sortedValues(g.trips).map((t): Change => ({ tag: 10, kind: 'trip', trip: t })),
    ...sortedValues(g.rules).map((r): Change => ({ tag: 12, kind: 'rule', rule: r })),
    ...sortedValues(g.txns).map((t): Change => ({ tag: 14, kind: 'txn', txn: t })),
    ...sortedValues(g.budgets).map((b): Change => ({ tag: 16, kind: 'budget', budget: b })),
    ...sortedValues(g.invoices).map((i): Change => ({ tag: 18, kind: 'invoice', invoice: i })),
    ...sortedValues(g.blobs).map((b): Change => ({ tag: 20, kind: 'blob', blob: b })),
    ...sortedValues(g.batches).map((b): Change => ({ tag: 22, kind: 'batch', batch: b })),
    ...sortedPairs(g.counters).map(
      ([name, value]): Change => ({ tag: 23, kind: 'counter', name, value }),
    ),
    ...sortedKeys(g.fingerprints).map((fp): Change => ({ tag: 24, kind: 'fingerprint', fp })),
  ]
}

/**
 * The state this event is the genesis of, when it is one. `Event.genesis?`.
 *
 * Genesis is a *position*, not a permission: an event whose whole content is one
 * snapshot is what a log starts from, and it counts as genesis only when it is
 * the first event of the fold. Anywhere else it is an ordinary event whose one
 * part `applyOp` refuses, which is a no-op.
 *
 * "Exactly one part, and that part a snapshot" is the whole test. An event with
 * a snapshot beside something else is not a beginning: the something else would
 * have to apply either before or after a state that replaced everything, and
 * neither reading is one two implementations would agree on.
 */
export function genesisOf(e: LedgerEvent): State | null {
  const only = e.parts.length === 1 ? e.parts[0] : null
  return only !== null && only.op.kind === 'snapshot' ? only.op.state : null
}

/**
 * Applying one event at a known position in the order. `Resources.stepAt`.
 *
 * Position 1 is the only place a genesis is read, and `genesisOf` is the only
 * shape that counts as one. Everywhere else this is `step`, and a part carrying
 * a snapshot is refused like any other invalid part.
 */
export function stepAt(pos: number, s: State, e: LedgerEvent): StepResult {
  if (pos === 1) {
    const g = genesisOf(e)
    if (g !== null) return { state: g, changes: snapshotChanges(g), rejected: [] }
  }
  return step(s, e)
}

/**
 * Replays a log from the beginning. The same log always gives the same state.
 *
 * The first event is the genesis when it is one event of one snapshot part;
 * otherwise the fold starts from `initState` and the first event is applied like
 * any other. Nothing later in the log can be a genesis, wherever it appears in
 * whatever order.
 *
 * It used to be that `applyOp` took a snapshot whenever the state it landed on
 * looked untouched — which is a fact about what the reader had managed to fold,
 * not about where the reader stood. A browser holds one generation's key while a
 * node holds every generation, so after any revoke or key rotation a browser
 * replaying from the beginning skips every part written before the rotation and
 * arrives, part way along, at a state that looks exactly like a new ledger. One
 * snapshot by anybody still in the realm then replaced the whole of what that
 * browser displayed — balances, standings, who administers the realm — and since
 * the snapshot could name its author an admin, every checkpoint they published
 * afterwards was trusted too.
 */
export function replay(log: readonly LedgerEvent[]): State {
  const head = log[0]
  if (head === undefined) return initState()
  const g = genesisOf(head)
  const rest = g === null ? log : log.slice(1)
  let state = g ?? initState()
  for (const e of rest) state = step(state, e).state
  return state
}

/* ------------------------------------------------------------------ */
/* Dividing a payment by the lines on its receipt                      */
/* ------------------------------------------------------------------ */

/**
 * Divides a payment by the lines printed on its receipt.
 *
 * The whole division is checked before any of it is written: no line may be
 * claimed for more than it covers, or the same money would be booked twice and
 * the remainder would absorb the difference in silence.
 *
 * Every part carries away the lines it claimed and the remainder the units they
 * left, so no line is ever offered twice: a part of an earlier division is
 * divided by what it was left with, not by the page again. The receipt itself is
 * untouched, because what it says is a fact about the paper rather than about
 * who ended up paying for which half of it.
 */
function divideByItems(
  s: State,
  author: string,
  realm: string,
  id: string,
  groups: readonly { items: readonly { line: number; qty: number | null }[]; into: string }[],
  newIds: readonly string[],
): [State, Change[]] {
  if (groups.length === 0) throw new Error('say which lines go together: --group 1+2=Account')
  const t = txnOf(s, id)
  const parts = itemParts(t, linesOf(s, t), groups, newIds)
  return replaceParts(s, author, realm, id, parts)
}

/**
 * The lines a payment is divisible by: the ones it was left with when it is
 * itself a part of a division, and its receipt's otherwise.
 */
function linesOf(s: State, t: Transaction): readonly LineItem[] {
  if (t.items !== null) {
    if (t.items.length === 0) {
      throw new Error(
        'every line on that receipt already belongs to one of the parts this was divided ' +
          'into; there is nothing left here to divide',
      )
    }
    return t.items
  }
  const sha = t.attachments[0]
  if (sha === undefined) throw new Error('this transaction has no receipt to take lines from')
  const blob = s.blobs.get(sha)
  if (blob === undefined) throw new Error(`no such receipt: ${sha}`)
  return blob.items
}

/**
 * The parts a payment divides into, as the lines group them. `Core.itemParts`.
 *
 * Nothing here touches the state: the parts are handed to `replaceParts`, which
 * is what writes them, so a division that cannot be carried out is a sentence
 * rather than a half-written ledger.
 */
function itemParts(
  t: Transaction,
  lines: readonly LineItem[],
  groups: readonly { items: readonly { line: number; qty: number | null }[]; into: string }[],
  newIds: readonly string[],
): Transaction[] {
  if (lines.length === 0) {
    throw new Error("no lines were read off that receipt; run 'resources receipt scan' on it first")
  }
  // A line's printed quantity is what its total is cut into, and a receipt filed
  // before these bounds existed can carry any number at all — which is how one
  // short event used to make every reader allocate a list of a thousand million.
  for (const l of lines) {
    if (l.qty !== null) {
      const abs = l.qty < 0n ? -l.qty : l.qty
      if (abs > BigInt(maxQty)) {
        throw new Error(
          `a line covering ${l.qty} units is more than a receipt prints; at most ${maxQty}`,
        )
      }
    }
  }
  const commodity = lines[0].amount.commodity
  const code = commodity.code
  // How many units a line covers, and how its total divides between them.
  const unitsOf = (n: number): number => {
    const q = lines[n - 1].qty
    const abs = q === null ? 1 : Number(q < 0n ? -q : q)
    return Math.max(1, abs)
  }
  const partsOf = (n: number): bigint[] => splitParts(lines[n - 1].amount.minor, unitsOf(n))
  // Some of a line, as a line of its own: what it is called, how many of its
  // units these are, and exactly the money carved for them. All of it is the
  // line as printed, count and all, because a part that took everything a line
  // covers paid for precisely what the bill says. A count a till printed
  // negative stays negative: a correction taken in part is still a correction.
  const shareLine = (n: number, want: number, amount: bigint): LineItem => {
    const line = lines[n - 1]
    if (want === unitsOf(n)) return line
    const count = (line.qty ?? 1n) < 0n ? BigInt(-want) : BigInt(want)
    return { ...line, qty: count, amount: { commodity, minor: amount } }
  }

  const taken = lines.map(() => 0)
  for (const g of groups) {
    for (const sh of g.items) {
      if (sh.line < 1 || sh.line > lines.length) {
        throw new Error(`there is no line ${sh.line}; this receipt has ${lines.length}`)
      }
      const units = unitsOf(sh.line)
      const want = sh.qty ?? Math.max(0, units - taken[sh.line - 1])
      if (want < 1) throw new Error(`line ${sh.line}: a share has to be at least one`)
      if (taken[sh.line - 1] + want > units) {
        throw new Error(
          `line ${sh.line} covers ${units}, and ${taken[sh.line - 1] + want} are spoken for`,
        )
      }
      taken[sh.line - 1] += want
    }
  }
  // The lines are priced in the receipt's currency, and the parts have to be
  // booked in the payment's; nothing here knows the rate a bank used.
  if (!commodityCodes(t).includes(code)) {
    throw new Error(
      `this payment moved ${eraseDups(commodityCodes(t)).join(', ')}, but the receipt ` +
        `is priced in ${code}; dividing needs them to agree`,
    )
  }
  // One account the money left, one it landed in.
  const accounts = eraseDups(t.postings.map((p) => p.account))
  const moving = accounts.filter((a) => txnNetIn(t, a, code) !== 0n)
  const src = moving.find((a) => txnNetIn(t, a, code) < 0n)
  if (src === undefined) throw new Error(`nothing in ${code} leaves this transaction`)
  const dst = moving.find((a) => txnNetIn(t, a, code) > 0n)
  if (dst === undefined) throw new Error(`nothing in ${code} arrives in this transaction`)
  if (moving.length !== 2) {
    throw new Error(
      'dividing by lines needs one account the money left and one it landed in; ' +
        'this transaction touches more, so unmerge it first',
    )
  }
  // Carve from the largest leg on each side, leaving fees and the rest alone.
  const biggest = (a: string, sign: bigint): number => {
    let best = 0
    let bestMag = -1n
    t.postings.forEach((p, i) => {
      if (p.account === a && p.amount.commodity.code === code && sign * p.amount.minor > bestMag) {
        best = i
        bestMag = sign * p.amount.minor
      }
    })
    return best
  }
  const srcIdx = biggest(src, -1n)
  const dstIdx = biggest(dst, 1n)
  const srcPost = t.postings[srcIdx]
  const dstPost = t.postings[dstIdx]
  const parts: Transaction[] = []
  let carved = 0n
  // Hand the units out in order, so two groups claiming the same line get
  // different slices of it and together take exactly what the line came to.
  const cursor = lines.map(() => 0)
  groups.forEach((g, gi) => {
    let amount = 0n
    const names: string[] = []
    const mine: LineItem[] = []
    for (const sh of g.items) {
      const units = unitsOf(sh.line)
      const from = cursor[sh.line - 1]
      const want = sh.qty ?? Math.max(0, units - from)
      const share = sum(partsOf(sh.line).slice(from, from + want))
      amount += share
      cursor[sh.line - 1] = from + want
      const desc = lines[sh.line - 1].description
      names.push(want === units ? desc : `${want} × ${desc}`)
      mine.push(shareLine(sh.line, want, share))
    }
    const nid = newIds[gi]
    if (nid === undefined) {
      throw new Error(
        `dividing this needs ${groups.length + 1} new ids, and ${newIds.length} were given`,
      )
    }
    carved += amount
    parts.push({
      ...t,
      id: nid,
      narration: names.join(', '),
      items: mine,
      postings: [
        { ...srcPost, amount: { commodity, minor: -amount } },
        { ...dstPost, account: g.into, amount: { commodity, minor: amount } },
      ],
    })
  })
  if (carved > -srcPost.amount.minor) {
    throw new Error(
      `those lines come to more than the ${render({
        commodity,
        minor: -srcPost.amount.minor,
      })} this payment moved`,
    )
  }
  // What no group claimed stays where it was, carrying the legs nobody divided.
  const rest = t.postings.map((p, i) =>
    i === srcIdx
      ? { ...p, amount: { commodity, minor: p.amount.minor + carved } }
      : i === dstIdx
        ? { ...p, amount: { commodity, minor: p.amount.minor - carved } }
        : p,
  )
  // ...and so do the lines: one nobody claimed as it was printed, one claimed in
  // part shrunk to the units still on it, and one claimed in full gone
  // altogether. A remainder listing the whole bill would offer a second division
  // the lines the first one already spent.
  const left: LineItem[] = []
  const leftNames: string[] = []
  lines.forEach((line, i) => {
    const units = unitsOf(i + 1)
    const from = cursor[i]
    if (from === 0) {
      left.push(line)
      leftNames.push(line.description)
    } else if (from < units) {
      left.push(shareLine(i + 1, units - from, sum(partsOf(i + 1).slice(from, units))))
      leftNames.push(`${units - from} × ${line.description}`)
    }
  })
  // What the remainder is called. A payment's own words are the payment's —
  // 'cash receipt', the payee, whatever the bank said — and they still describe
  // what is left of it. A part's are a list the last division wrote, and a list
  // still naming what has gone to the siblings describes the wrong money, so a
  // part's remainder is named the way a part is: by its lines.
  const narration = t.items === null ? t.narration : leftNames.join(', ')
  if (rest.some((p) => p.amount.minor !== 0n)) {
    const rid = newIds[groups.length]
    if (rid === undefined) {
      throw new Error(
        `dividing this needs ${groups.length + 1} new ids, and ${newIds.length} were given`,
      )
    }
    parts.push({ ...t, id: rid, narration, postings: rest, items: left })
  }
  return parts
}

/* ------------------------------------------------------------------ */
/* Meeting a claim                                                     */
/* ------------------------------------------------------------------ */

/**
 * Settles a claim against the transaction that performed it.
 *
 * Meeting a claim is one piece of arithmetic with two doors into it:
 * `resolveClaim` points an existing transaction at the claim it discharged,
 * `payClaim` writes that transaction itself and then walks this very same path.
 *
 * What the claim contributes to the real transaction is *who the money was
 * from*: every non-funding leg is rebooked onto the payer's account. Anything
 * the payment overpays goes to the same place, which leaves their purse owing
 * them the difference. A part payment splits the claim rather than shrinking
 * it, so that what has been asked for stays the sum of both halves.
 *
 * `allowed` is handed straight to `putTxn`: `payClaim` has already established
 * that the author may move money between the claim's two accounts, and the legs
 * written here are on no others.
 */
function settleClaim(
  s: State,
  author: string,
  realm: string,
  id: string,
  actual: string,
  splitId: string,
  allowed: readonly string[] = [],
): [State, Change[]] {
  const claim = txnOfId(s, id)
  if (claim === null) throw new Error(`no such claim: ${id}`)
  if (claim.state !== 'pending') throw new Error(`that claim is already ${claim.state}`)
  const act = txnOf(s, actual)
  if (act.state !== 'posted') {
    throw new Error('a claim can only be met by a transaction that actually happened')
  }
  const recv = claimReceiver(claim)
  if (recv === null) throw new Error('this claim has no receiving leg')
  const payAcc = claimPayer(claim)
  if (payAcc === null) throw new Error('this claim has no paying leg')
  const asked = claimAmount(claim)
  const arrived = txnNetIn(act, recv, asked.commodity.code)
  if (arrived <= 0n) {
    const acc = accountOfId(s, recv)
    if (acc === null) throw new Error('the receiving account is gone')
    throw new Error(`${actual} brings nothing into ${acc.name}`)
  }
  const payer = accountOfId(s, payAcc)
  if (payer === null) throw new Error('the paying account is gone')
  const matched = arrived < asked.minor ? arrived : asked.minor
  const left = asked.minor - matched
  let st = s
  let changes: Change[] = []
  const funding = fundingAccounts(s)
  const moved: Transaction = {
    ...act,
    postings: act.postings.map((p) =>
      funding.includes(p.account) ? p : { ...p, account: payer.id },
    ),
  }
  const samePostings = moved.postings.every((p, i) => p.account === act.postings[i].account)
  if (!samePostings) {
    let bt: Transaction
    try {
      bt = validateTxn(moved)
    } catch (e) {
      throw new Error(`claiming ${actual} would not balance: ${(e as Error).message}`)
    }
    const [st2, cs] = putTxn(st, author, realm, bt, allowed)
    st = st2
    changes = [...changes, ...cs]
  }
  // A met claim is stamped the way a merge stamps its sources.
  const stamp = (t: Transaction): Transaction => ({
    ...t,
    postings: t.postings.map((p) => ({ ...p, origin: p.origin ?? actual })),
  })
  const resize = (n: bigint, t: Transaction): Transaction => ({
    ...t,
    postings: t.postings.map((p) => ({
      ...p,
      amount: { commodity: p.amount.commodity, minor: p.amount.minor > 0n ? n : -n },
    })),
  })
  if (left === 0n) {
    const [st2, cs] = putTxn(st, author, realm, stamp({ ...claim, state: 'settled' }), allowed)
    return [st2, [...changes, ...cs]]
  }
  const met = stamp(resize(matched, { ...claim, id: splitId, date: act.date, state: 'settled' }))
  const [st1, cs1] = putTxn(st, author, realm, met, allowed)
  const [st2, cs2] = putTxn(st1, author, realm, resize(left, claim), allowed)
  return [st2, [...changes, ...cs1, ...cs2]]
}

/**
 * Paying a claim: the payment and the settlement, as one decision.
 *
 * Marking a claim met used to be two operations in one event — write the
 * payment, then resolve against it — and that composition asked the writer for
 * rights they do not have, because one leg of the payment lands in the other
 * person's account. This op is the single decision instead: either side of the
 * claim may take it, and what makes that safe is that nothing about the payment
 * is theirs to choose. The amount is the claim's, both accounts are the claim's,
 * and the only thing the author supplies is the date and two identifiers.
 */
function payClaim(
  s: State,
  author: string,
  realm: string,
  claimId: string,
  paymentId: string,
  date: LedgerDate,
): [State, Change[]] {
  const claim = txnOfId(s, claimId)
  if (claim === null) throw new Error(`no such claim: ${claimId}`)
  if (claim.state !== 'pending') throw new Error(`that claim is already ${claim.state}`)
  if (txnOfId(s, paymentId) !== null) {
    throw new Error(`a transaction with that id already exists: ${paymentId}`)
  }
  const recvId = claimReceiver(claim)
  if (recvId === null) throw new Error('this claim has no receiving leg')
  const payId = claimPayer(claim)
  if (payId === null) throw new Error('this claim has no paying leg')
  const payerAcc = accountOf(s, payId)
  const receiver = accountOf(s, recvId)
  // Both legs have to be able to hold a balance. A claim whose receiving leg is
  // an equity account was settled by a payment `settleClaim` then rewrote onto
  // the paying account alone, so the claim came out met and no money had gone
  // anywhere.
  if (!holdsMoney(payerAcc) || !holdsMoney(receiver)) {
    throw new Error('a claim is paid between two accounts that can hold money')
  }
  // Who may say a claim was met: whoever's purse is owed, or somebody who
  // administers the realm the two of them sit in. Not the payer: the amount
  // being the claim's stops them inventing the *size* of a payment, and stops
  // nothing about inventing the payment itself.
  if (receiver.bridgeOf !== author && !canAdminister(s, author, realm)) {
    throw new Error('only the receiver or an admin of that realm may say this claim was paid')
  }
  const asked = claimAmount(claim)
  const entry: Transaction = {
    id: paymentId,
    date,
    payee: null,
    narration: `payment of ${claim.narration}`,
    state: 'posted',
    postings: [
      posting(payId, { commodity: asked.commodity, minor: -asked.minor }, { tag: claimTag }),
      posting(recvId, asked, { tag: claimTag }),
    ],
    labels: [],
    source: { kind: 'manual', actor: author },
    attachments: [],
    items: null,
  }
  // The two legs are the claim's own, so the poster check is the authorisation
  // above rather than `canPost`; the accounts still have to exist, be open and
  // be in this realm, which is what `putTxn` checks.
  const allowed = [payId, recvId]
  const [st, cs] = putTxn(s, author, realm, entry, allowed)
  // The claim is met in full by construction — the payment is exactly what it
  // asked for — so the part id below never names anything.
  const splitId = `${paymentId}:part`
  const [st2, cs2] = settleClaim(st, author, realm, claimId, paymentId, splitId, allowed)
  return [st2, [...cs, ...cs2]]
}
