/**
 * The canonical binary encoding, byte for byte.
 *
 * A port of `Resources/Core/Codec.lean` (the primitives and combinators) and
 * `Resources/Core/Encode.lean` (the instance for every type the ledger holds).
 * Both halves matter and they fail differently: a wrong combinator makes
 * nothing decode, a wrong field order or a renumbered tag decodes perfectly and
 * silently changes every checkpoint hash in the world. The fixed byte strings
 * in `codec.test.ts` are copied from `Test/Encode.lean` for exactly that
 * reason.
 *
 * The format, restated so it can be checked against this file without opening
 * the other one:
 *
 * - naturals are LEB128, seven bits per byte, little-endian, high bit set on
 *   every byte but the last;
 * - an integer is a LEB128 sign — `0` non-negative, `1` negative — then the
 *   LEB128 magnitude;
 * - `Bool` is a LEB128 `0` or `1`, `UInt8` is itself;
 * - strings, byte arrays and lists carry a LEB128 length first, strings as
 *   their UTF-8 bytes;
 * - `Option` is a `0` tag, or a `1` tag and a value;
 * - a product is its halves in order, a structure its fields in declaration
 *   order, a sum a LEB128 constructor tag and the payload;
 * - a `Date` is its year, month and day as integers;
 * - a hash map is its entries in key order, and a hash set its elements in
 *   order, because a bucket order is a fact about a hash function and not
 *   about the ledger.
 */

import { compareStrings, fromUtf8, mergeSort, utf8 } from './bytes'
import type {
  Account,
  AccountKind,
  Amount,
  Attachment,
  BlobState,
  Budget,
  BudgetState,
  Change,
  Commodity,
  Date as LedgerDate,
  Extracted,
  Filter,
  ImportBatch,
  Invoice,
  InvoiceLine,
  InvoiceState,
  InvoiceStatus,
  ItemGroup,
  ItemShare,
  Label,
  LedgerEvent,
  LineItem,
  Member,
  Op,
  Part,
  Participant,
  Party,
  PartyGroup,
  PaymentRequest,
  Posting,
  Provenance,
  Realm,
  RealmRole,
  Rule,
  State,
  Transaction,
  Trip,
  TxnState,
} from './types'
import {
  accountKinds,
  invoiceStatuses,
  maxExponent,
  maxMinor,
  maxYear,
  minYear,
  realmRoles,
  txnStates,
} from './types'

/** Anything the reader refuses, and anything the writer cannot represent. */
export class CodecError extends Error {}

/* ------------------------------------------------------------------ */
/* The writer                                                          */
/* ------------------------------------------------------------------ */

/** A growable byte buffer with one method per primitive of the format. */
export class Writer {
  private buf = new Uint8Array(1024)
  private len = 0

  private room(n: number): void {
    if (this.len + n <= this.buf.length) return
    let size = this.buf.length * 2
    while (size < this.len + n) size *= 2
    const next = new Uint8Array(size)
    next.set(this.buf.subarray(0, this.len))
    this.buf = next
  }

  byte(b: number): void {
    this.room(1)
    this.buf[this.len++] = b & 0xff
  }

  raw(bs: Uint8Array): void {
    this.room(bs.length)
    this.buf.set(bs, this.len)
    this.len += bs.length
  }

  /** LEB128. */
  nat(n: number): void {
    if (!Number.isInteger(n) || n < 0) throw new CodecError(`not a natural: ${n}`)
    this.natBig(BigInt(n))
  }

  /** LEB128 over a `bigint`, for magnitudes a `number` could not hold exactly. */
  natBig(n: bigint): void {
    if (n < 0n) throw new CodecError(`not a natural: ${n}`)
    let v = n
    while (v >= 128n) {
      this.byte(Number(v % 128n) + 128)
      v /= 128n
    }
    this.byte(Number(v))
  }

  /** A sign byte — `0` non-negative, `1` negative — and the magnitude. */
  int(i: bigint): void {
    if (i < 0n) {
      this.nat(1)
      this.natBig(-i)
    } else {
      this.nat(0)
      this.natBig(i)
    }
  }

  bool(b: boolean): void {
    this.nat(b ? 1 : 0)
  }

  str(s: string): void {
    const bs = utf8(s)
    this.nat(bs.length)
    this.raw(bs)
  }

  bytes(bs: Uint8Array): void {
    this.nat(bs.length)
    this.raw(bs)
  }

  list<T>(xs: readonly T[], write: (w: Writer, x: T) => void): void {
    this.nat(xs.length)
    for (const x of xs) write(this, x)
  }

  option<T>(x: T | null, write: (w: Writer, x: T) => void): void {
    if (x === null) {
      this.nat(0)
    } else {
      this.nat(1)
      write(this, x)
    }
  }

  finish(): Uint8Array {
    return this.buf.slice(0, this.len)
  }
}

/* ------------------------------------------------------------------ */
/* The reader                                                          */
/* ------------------------------------------------------------------ */

/** A cursor over bytes with one method per primitive of the format. */
export class Reader {
  pos = 0

  constructor(private readonly bs: Uint8Array) {}

  get done(): boolean {
    return this.pos >= this.bs.length
  }

  byte(): number {
    if (this.pos >= this.bs.length) throw new CodecError('ran out of bytes')
    return this.bs[this.pos++]
  }

  raw(n: number): Uint8Array {
    if (this.bs.length - this.pos < n) throw new CodecError('ran out of bytes')
    const out = this.bs.slice(this.pos, this.pos + n)
    this.pos += n
    return out
  }

  /**
   * LEB128, and only the canonical spelling of it.
   *
   * `decNat` in `Core/Codec.lean` refuses an overlong encoding: a continuation
   * byte has to contribute something, so what follows it may not decode to
   * zero — which, unrolled, is "the last byte of a multi-byte run is not
   * `0x00`". A reader that accepted `[0x80, 0x00]` as `0` gave every natural,
   * every constructor tag and every length prefix unboundedly many spellings,
   * and a format whose whole job is content addressing cannot have two byte
   * strings for one value.
   */
  natBig(): bigint {
    let shift = 1n
    let out = 0n
    let bytes = 0
    for (;;) {
      const b = this.byte()
      bytes++
      if (b < 128) {
        if (bytes > 1 && b === 0) throw new CodecError('overlong LEB128')
        return out + BigInt(b) * shift
      }
      out += BigInt(b - 128) * shift
      shift *= 128n
      if (shift > 1n << 256n) throw new CodecError('LEB128 natural is absurdly long')
    }
  }

  nat(): number {
    const n = this.natBig()
    if (n > BigInt(Number.MAX_SAFE_INTEGER)) throw new CodecError(`natural too large: ${n}`)
    return Number(n)
  }

  /**
   * A LEB128 sign byte and the magnitude, with negative zero refused.
   *
   * `[0x01, 0x00]` and `[0x00, 0x00]` both meant `0`, so an amount had two
   * encodings and a transaction carrying it had two hashes. `decInt` refuses
   * the first, and so does this.
   */
  int(): bigint {
    const sign = this.nat()
    const magnitude = this.natBig()
    if (sign === 0) return magnitude
    if (sign === 1) {
      if (magnitude === 0n) throw new CodecError('negative zero')
      return -magnitude
    }
    throw new CodecError(`not an integer sign: ${sign}`)
  }

  bool(): boolean {
    const n = this.nat()
    if (n === 0) return false
    if (n === 1) return true
    throw new CodecError(`not a boolean: ${n}`)
  }

  str(): string {
    const n = this.nat()
    return fromUtf8(this.raw(n))
  }

  bytes(): Uint8Array {
    return this.raw(this.nat())
  }

  list<T>(read: (r: Reader) => T): T[] {
    const n = this.nat()
    const out: T[] = []
    for (let i = 0; i < n; i++) out.push(read(this))
    return out
  }

  option<T>(read: (r: Reader) => T): T | null {
    const t = this.nat()
    if (t === 0) return null
    if (t === 1) return read(this)
    throw new CodecError(`not an option tag: ${t}`)
  }
}

/**
 * A codec: a writer, a reader, and what the reader will take back.
 *
 * `wf` is `Wellformed` from `Core/Codec.lean`, and it is the second half of the
 * decoder rather than an afterthought. Three numbers in this format have no type
 * over them — a date's year, a commodity's exponent and a count of minor units —
 * and a reader that takes them as they come turns six bytes into a computation
 * nobody asked for. They are refused here, while decoding, wherever a value is
 * read *for itself*: a `Date`, a `Commodity`, an `Amount`, anything holding one,
 * and above all a `State`, which is what a checkpoint commits to.
 *
 * It is consulted by `decode`, which reads a whole byte string, and by nothing
 * else — so a value read as part of a larger one is bounded by the larger one's
 * `wf` and not by its own. That is what makes the `Op` exception below possible.
 */
export interface Codec<T> {
  write(w: Writer, x: T): void
  read(r: Reader): T
  /** Whether a decoded value is one this format carries. Absent means "always". */
  wf?(x: T): boolean
}

/** The canonical bytes of a value. */
export function encode<T>(codec: Codec<T>, x: T): Uint8Array {
  const w = new Writer()
  codec.write(w, x)
  return w.finish()
}

/**
 * Reads a value out of bytes, insisting that it accounts for every one of them
 * and that what comes back is a value this format carries.
 *
 * `Codec.decode` in `Core/Codec.lean`: the reader, the whole-byte-string rule,
 * and then `Wellformed.wf`.
 */
export function decode<T>(codec: Codec<T>, bs: Uint8Array): T {
  const r = new Reader(bs)
  const x = codec.read(r)
  if (!r.done) throw new CodecError(`${bs.length - r.pos} trailing bytes`)
  if (codec.wf !== undefined && !codec.wf(x)) {
    throw new CodecError('these bytes decode to a value outside what this format carries')
  }
  return x
}

/* ------------------------------------------------------------------ */
/* Dates, identifiers, money                                           */
/* ------------------------------------------------------------------ */

const daysInMonth = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

/**
 * The widest year this port can hold exactly.
 *
 * Not a rule of the format — that is `maxYear`, and it is checked by `wf` below
 * — but a fact about `number`: a year above 2^53 loses precision and one around
 * 1e309 becomes `Infinity`, and a date that is `Infinity` in a browser and exact
 * in Lean is a state the two would order, render and hash differently. Every
 * year the format carries is six digits, so this is four hundred million times
 * wider than anything a conforming writer produces.
 */
const representableYear = BigInt(Number.MAX_SAFE_INTEGER)

/** Whether a year, month and day name a day that exists. */
export function validDate(d: LedgerDate): boolean {
  if (d.month < 1 || d.month > 12) return false
  if (d.day < 1 || d.day > 31) return false
  const leap = (d.year % 4 === 0 && d.year % 100 !== 0) || d.year % 400 === 0
  const limit = d.month === 2 && leap ? 29 : daysInMonth[d.month - 1]
  return d.day <= limit
}

/**
 * A date the ledger will take: one whose year is between `minYear` and
 * `maxYear`. `Wellformed Date` in `Core/Encode.lean`.
 *
 * The month and the day are not asked about here because they are already
 * refused while the bytes are being read — `Date.ofTriple` puts them through
 * 1-12 and 1-31 and then through `PlainDate.ofYearMonthDay?`, which is what
 * rules out the thirty-first of February. Lean's `PlainDate` carries the proof;
 * a port whose date is three numbers makes all three checks itself, and
 * `dateCodec.read` below is where it makes them.
 */
export function dateInRange(d: LedgerDate): boolean {
  return d.year >= minYear && d.year <= maxYear
}

/** Whether an optional date is in range. Nothing is in range. */
function dateOptInRange(d: LedgerDate | null): boolean {
  return d === null || dateInRange(d)
}

/** A commodity whose minor unit has few enough places that `10 ^ exponent` is a number. */
export function commodityInRange(c: Commodity): boolean {
  return c.exponent <= maxExponent
}

/** An amount in a usable commodity, counted in a number that fits a 64-bit column. */
export function amountInRange(a: Amount): boolean {
  const magnitude = a.minor < 0n ? -a.minor : a.minor
  return commodityInRange(a.commodity) && magnitude < maxMinor
}

/** Whether an optional amount is in range. */
function amountOptInRange(a: Amount | null): boolean {
  return a === null || amountInRange(a)
}

export const dateCodec: Codec<LedgerDate> = {
  write(w, d) {
    w.int(BigInt(d.year))
    w.int(BigInt(d.month))
    w.int(BigInt(d.day))
  },
  read(r) {
    // A year is read as a `bigint` and only then narrowed, because
    // `Number(10n ** 400n)` is `Infinity` and `Infinity % 4` is `NaN`, which
    // `validDate` would have waved through as a non-leap year.
    const y = r.int()
    if (y < -representableYear || y > representableYear) {
      throw new CodecError(`a year of ${y} is not a number this port can hold`)
    }
    const year = Number(y)
    const month = Number(r.int())
    const day = Number(r.int())
    const d = { year, month, day }
    // `Date.ofTriple` refuses a month, a day or a combination that is not one.
    // Whether the *year* is one the ledger takes is `wf`'s question, not this
    // one: a date inside an operation is refused by `checkBounds` when the part
    // is applied, and refusing the bytes would cost every other realm's part in
    // the same event.
    if (!validDate(d)) throw new CodecError(`not a date: ${year}-${month}-${day}`)
    return d
  },
  wf: dateInRange,
}

/** A string-backed identifier: the string, and nothing else. */
export const idCodec: Codec<string> = {
  write(w, s) {
    w.str(s)
  },
  read(r) {
    return r.str()
  },
}

export const stringCodec = idCodec

/** A bare integer, for the counters map. */
export const intCodec: Codec<bigint> = {
  write(w, v) {
    w.int(v)
  },
  read(r) {
    return r.int()
  },
}

export const commodityCodec: Codec<Commodity> = {
  write(w, c) {
    w.str(c.code)
    w.nat(c.exponent)
  },
  read(r) {
    return { code: r.str(), exponent: r.nat() }
  },
  wf: commodityInRange,
}

export const amountCodec: Codec<Amount> = {
  write(w, a) {
    commodityCodec.write(w, a.commodity)
    w.int(a.minor)
  },
  read(r) {
    return { commodity: commodityCodec.read(r), minor: r.int() }
  },
  wf: amountInRange,
}

/** An enumeration carried into `Nat` by its declaration order. */
function enumCodec<T extends string>(values: readonly T[], what: string): Codec<T> {
  return {
    write(w, x) {
      const i = values.indexOf(x)
      if (i < 0) throw new CodecError(`not a ${what}: ${x}`)
      w.nat(i)
    },
    read(r) {
      const i = r.nat()
      if (i >= values.length) throw new CodecError(`not a ${what} tag: ${i}`)
      return values[i]
    },
  }
}

export const accountKindCodec: Codec<AccountKind> = enumCodec(accountKinds, 'account kind')
export const txnStateCodec: Codec<TxnState> = enumCodec(txnStates, 'transaction state')
export const invoiceStatusCodec: Codec<InvoiceStatus> = enumCodec(invoiceStatuses, 'invoice status')
export const realmRoleCodec: Codec<RealmRole> = enumCodec(realmRoles, 'realm role')

/* ------------------------------------------------------------------ */
/* The ledger                                                          */
/* ------------------------------------------------------------------ */

export const accountCodec: Codec<Account> = {
  write(w, a) {
    w.str(a.id)
    w.str(a.name)
    accountKindCodec.write(w, a.kind)
    w.str(a.owner)
    w.option(a.commodity, (w2, c) => commodityCodec.write(w2, c))
    w.option(a.iban, (w2, s) => w2.str(s))
    w.option(a.note, (w2, s) => w2.str(s))
    w.option(a.closedOn, (w2, d) => dateCodec.write(w2, d))
    w.str(a.realm)
    w.option(a.bridgeOf, (w2, s) => w2.str(s))
    w.list(a.posters, (w2, s) => w2.str(s))
    w.option(a.mirrorOf, (w2, s) => w2.str(s))
  },
  read(r) {
    return {
      id: r.str(),
      name: r.str(),
      kind: accountKindCodec.read(r),
      owner: r.str(),
      commodity: r.option((r2) => commodityCodec.read(r2)),
      iban: r.option((r2) => r2.str()),
      note: r.option((r2) => r2.str()),
      closedOn: r.option((r2) => dateCodec.read(r2)),
      realm: r.str(),
      bridgeOf: r.option((r2) => r2.str()),
      posters: r.list((r2) => r2.str()),
      mirrorOf: r.option((r2) => r2.str()),
    }
  },
  wf: (a) =>
    dateOptInRange(a.closedOn) && (a.commodity === null || commodityInRange(a.commodity)),
}

export const partyCodec: Codec<Party> = {
  write(w, p) {
    w.str(p.id)
    w.str(p.name)
    w.option(p.iban, (w2, s) => w2.str(s))
    w.option(p.email, (w2, s) => w2.str(s))
    w.option(p.note, (w2, s) => w2.str(s))
    w.str(p.kind)
    w.str(p.realm)
  },
  read(r) {
    return {
      id: r.str(),
      name: r.str(),
      iban: r.option((r2) => r2.str()),
      email: r.option((r2) => r2.str()),
      note: r.option((r2) => r2.str()),
      kind: r.str(),
      realm: r.str(),
    }
  },
}

export const labelCodec: Codec<Label> = {
  write(w, l) {
    w.str(l.id)
    w.str(l.name)
    w.option(l.colour, (w2, s) => w2.str(s))
    w.str(l.realm)
  },
  read(r) {
    return {
      id: r.str(),
      name: r.str(),
      colour: r.option((r2) => r2.str()),
      realm: r.str(),
    }
  },
}

export const postingCodec: Codec<Posting> = {
  write(w, p) {
    w.str(p.account)
    amountCodec.write(w, p.amount)
    w.option(p.party, (w2, s) => w2.str(s))
    w.option(p.note, (w2, s) => w2.str(s))
    w.option(p.origin, (w2, s) => w2.str(s))
    w.option(p.tag, (w2, s) => w2.str(s))
  },
  read(r) {
    return {
      account: r.str(),
      amount: amountCodec.read(r),
      party: r.option((r2) => r2.str()),
      note: r.option((r2) => r2.str()),
      origin: r.option((r2) => r2.str()),
      tag: r.option((r2) => r2.str()),
    }
  },
  wf: (p) => amountInRange(p.amount),
}

export const provenanceCodec: Codec<Provenance> = {
  write(w, p) {
    switch (p.kind) {
      case 'manual':
        w.nat(0)
        w.str(p.actor)
        return
      case 'imported':
        w.nat(1)
        w.str(p.batch)
        w.str(p.fingerprint)
        return
      case 'derived':
        w.nat(2)
        w.str(p.rule)
        return
    }
  },
  read(r) {
    const t = r.nat()
    switch (t) {
      case 0:
        return { kind: 'manual', actor: r.str() }
      case 1:
        return { kind: 'imported', batch: r.str(), fingerprint: r.str() }
      case 2:
        return { kind: 'derived', rule: r.str() }
      default:
        throw new CodecError(`not a provenance tag: ${t}`)
    }
  },
}

export const transactionCodec: Codec<Transaction> = {
  write(w, t) {
    w.str(t.id)
    dateCodec.write(w, t.date)
    w.option(t.payee, (w2, s) => w2.str(s))
    w.str(t.narration)
    txnStateCodec.write(w, t.state)
    w.list(t.postings, (w2, p) => postingCodec.write(w2, p))
    w.list(t.labels, (w2, s) => w2.str(s))
    provenanceCodec.write(w, t.source)
    w.list(t.attachments, (w2, s) => w2.str(s))
    w.option(t.items, (w2, its) => w2.list(its, (w3, l) => lineItemCodec.write(w3, l)))
  },
  read(r) {
    return {
      id: r.str(),
      date: dateCodec.read(r),
      payee: r.option((r2) => r2.str()),
      narration: r.str(),
      state: txnStateCodec.read(r),
      postings: r.list((r2) => postingCodec.read(r2)),
      labels: r.list((r2) => r2.str()),
      source: provenanceCodec.read(r),
      attachments: r.list((r2) => r2.str()),
      items: r.option((r2) => r2.list((r3) => lineItemCodec.read(r3))),
    }
  },
  wf: (t) =>
    dateInRange(t.date) &&
    t.postings.every((p) => amountInRange(p.amount)) &&
    (t.items ?? []).every((l) => amountInRange(l.amount)),
}

/* ------------------------------------------------------------------ */
/* Filters                                                             */
/* ------------------------------------------------------------------ */

export const filterCodec: Codec<Filter> = {
  write(w, f) {
    switch (f.kind) {
      case 'all':
        w.nat(0)
        return
      case 'account':
        w.nat(1)
        w.str(f.under)
        return
      case 'dateFrom':
        w.nat(2)
        dateCodec.write(w, f.d)
        return
      case 'dateTo':
        w.nat(3)
        dateCodec.write(w, f.d)
        return
      case 'amountFrom':
        w.nat(4)
        amountCodec.write(w, f.a)
        return
      case 'amountTo':
        w.nat(5)
        amountCodec.write(w, f.a)
        return
      case 'label':
        w.nat(6)
        w.str(f.name)
        return
      case 'party':
        w.nat(7)
        w.str(f.name)
        return
      case 'owner':
        w.nat(8)
        w.str(f.name)
        return
      case 'payee':
        w.nat(9)
        w.str(f.needle)
        return
      case 'text':
        w.nat(10)
        w.str(f.needle)
        return
      case 'commodity':
        w.nat(11)
        w.str(f.code)
        return
      case 'tag':
        w.nat(12)
        w.str(f.name)
        return
      case 'and':
        w.nat(13)
        filterCodec.write(w, f.a)
        filterCodec.write(w, f.b)
        return
      case 'or':
        w.nat(14)
        filterCodec.write(w, f.a)
        filterCodec.write(w, f.b)
        return
      case 'not':
        w.nat(15)
        filterCodec.write(w, f.a)
        return
    }
  },
  read(r): Filter {
    const t = r.nat()
    switch (t) {
      case 0:
        return { kind: 'all' }
      case 1:
        return { kind: 'account', under: r.str() }
      case 2:
        return { kind: 'dateFrom', d: dateCodec.read(r) }
      case 3:
        return { kind: 'dateTo', d: dateCodec.read(r) }
      case 4:
        return { kind: 'amountFrom', a: amountCodec.read(r) }
      case 5:
        return { kind: 'amountTo', a: amountCodec.read(r) }
      case 6:
        return { kind: 'label', name: r.str() }
      case 7:
        return { kind: 'party', name: r.str() }
      case 8:
        return { kind: 'owner', name: r.str() }
      case 9:
        return { kind: 'payee', needle: r.str() }
      case 10:
        return { kind: 'text', needle: r.str() }
      case 11:
        return { kind: 'commodity', code: r.str() }
      case 12:
        return { kind: 'tag', name: r.str() }
      case 13: {
        const a = filterCodec.read(r)
        const b = filterCodec.read(r)
        return { kind: 'and', a, b }
      }
      case 14: {
        const a = filterCodec.read(r)
        const b = filterCodec.read(r)
        return { kind: 'or', a, b }
      }
      case 15:
        return { kind: 'not', a: filterCodec.read(r) }
      default:
        throw new CodecError(`not a filter tag: ${t}`)
    }
  },
  wf: filterInRange,
}

/** Whether every date and every amount a filter compares against is in range. */
export function filterInRange(f: Filter): boolean {
  switch (f.kind) {
    case 'dateFrom':
    case 'dateTo':
      return dateInRange(f.d)
    case 'amountFrom':
    case 'amountTo':
      return amountInRange(f.a)
    case 'and':
    case 'or':
      return filterInRange(f.a) && filterInRange(f.b)
    case 'not':
      return filterInRange(f.a)
    default:
      return true
  }
}

/* ------------------------------------------------------------------ */
/* Groups, trips, rules, batches, budgets                              */
/* ------------------------------------------------------------------ */

export const partyGroupCodec: Codec<PartyGroup> = {
  write(w, g) {
    w.str(g.name)
    w.list(g.members, (w2, s) => w2.str(s))
    w.str(g.realm)
  },
  read(r) {
    return { name: r.str(), members: r.list((r2) => r2.str()), realm: r.str() }
  },
}

export const tripCodec: Codec<Trip> = {
  write(w, t) {
    w.str(t.id)
    w.str(t.name)
    dateCodec.write(w, t.starts)
    dateCodec.write(w, t.ends)
    w.str(t.payer)
    w.option(t.note, (w2, s) => w2.str(s))
    w.str(t.realm)
  },
  read(r) {
    return {
      id: r.str(),
      name: r.str(),
      starts: dateCodec.read(r),
      ends: dateCodec.read(r),
      payer: r.str(),
      note: r.option((r2) => r2.str()),
      realm: r.str(),
    }
  },
  wf: (t) => dateInRange(t.starts) && dateInRange(t.ends),
}

export const ruleCodec: Codec<Rule> = {
  write(w, x) {
    w.str(x.id)
    w.str(x.name)
    w.str(x.filterSrc)
    filterCodec.write(w, x.filter)
    w.option(x.setAccount, (w2, s) => w2.str(s))
    w.list(x.addLabels, (w2, s) => w2.str(s))
    w.option(x.setParty, (w2, s) => w2.str(s))
    w.int(x.priority)
    w.str(x.realm)
  },
  read(r) {
    return {
      id: r.str(),
      name: r.str(),
      filterSrc: r.str(),
      filter: filterCodec.read(r),
      setAccount: r.option((r2) => r2.str()),
      addLabels: r.list((r2) => r2.str()),
      setParty: r.option((r2) => r2.str()),
      priority: r.int(),
      realm: r.str(),
    }
  },
  wf: (x) => filterInRange(x.filter),
}

export const importBatchCodec: Codec<ImportBatch> = {
  write(w, b) {
    w.str(b.id)
    w.str(b.profile)
    w.option(b.filename, (w2, s) => w2.str(s))
    w.option(b.account, (w2, s) => w2.str(s))
    w.str(b.stamp)
    w.nat(b.total)
    w.nat(b.duplicates)
    w.str(b.realm)
  },
  read(r) {
    return {
      id: r.str(),
      profile: r.str(),
      filename: r.option((r2) => r2.str()),
      account: r.option((r2) => r2.str()),
      stamp: r.str(),
      total: r.nat(),
      duplicates: r.nat(),
      realm: r.str(),
    }
  },
}

export const participantCodec: Codec<Participant> = {
  write(w, p) {
    w.str(p.owner)
    w.str(p.name)
    w.str(p.account)
    w.nat(p.weight)
  },
  read(r) {
    return { owner: r.str(), name: r.str(), account: r.str(), weight: r.nat() }
  },
}

export const budgetCodec: Codec<Budget> = {
  write(w, b) {
    w.str(b.id)
    w.str(b.name)
    w.option(b.note, (w2, s) => w2.str(s))
    w.bool(b.closed)
  },
  read(r) {
    return { id: r.str(), name: r.str(), note: r.option((r2) => r2.str()), closed: r.bool() }
  },
}

/* ------------------------------------------------------------------ */
/* Receipts                                                            */
/* ------------------------------------------------------------------ */

/**
 * `Attachment`, whose last two fields are the ones a synced node fills in.
 *
 * A store that never uploads anything writes two `none` bytes there and is
 * still writing the same format: they were added in wire format 3, and a file
 * that has only ever lived on one machine carries them empty.
 */
export const attachmentCodec: Codec<Attachment> = {
  write(w, a) {
    w.str(a.sha256)
    w.str(a.mime)
    w.nat(a.bytes)
    w.option(a.origName, (w2, s) => w2.str(s))
    w.str(a.createdAt)
    w.option(a.cipherHash, (w2, s) => w2.str(s))
    w.option(a.wrappedKey, (w2, s) => w2.str(s))
  },
  read(r) {
    return {
      sha256: r.str(),
      mime: r.str(),
      bytes: r.nat(),
      origName: r.option((r2) => r2.str()),
      createdAt: r.str(),
      cipherHash: r.option((r2) => r2.str()),
      wrappedKey: r.option((r2) => r2.str()),
    }
  },
}

export const lineItemCodec: Codec<LineItem> = {
  write(w, l) {
    w.str(l.description)
    w.option(l.qty, (w2, q) => w2.int(q))
    amountCodec.write(w, l.amount)
  },
  read(r) {
    return {
      description: r.str(),
      qty: r.option((r2) => r2.int()),
      amount: amountCodec.read(r),
    }
  },
  wf: (l) => amountInRange(l.amount),
}

export const extractedCodec: Codec<Extracted> = {
  write(w, e) {
    w.option(e.merchant, (w2, s) => w2.str(s))
    w.option(e.date, (w2, d) => dateCodec.write(w2, d))
    w.option(e.total, (w2, a) => amountCodec.write(w2, a))
    w.list(e.items, (w2, l) => lineItemCodec.write(w2, l))
    w.str(e.rawText)
    w.str(e.extractor)
  },
  read(r) {
    return {
      merchant: r.option((r2) => r2.str()),
      date: r.option((r2) => dateCodec.read(r2)),
      total: r.option((r2) => amountCodec.read(r2)),
      items: r.list((r2) => lineItemCodec.read(r2)),
      rawText: r.str(),
      extractor: r.str(),
    }
  },
  wf: extractedInRange,
}

/** Everything an extraction carries, bounded. */
function extractedInRange(e: Extracted): boolean {
  return (
    dateOptInRange(e.date) &&
    amountOptInRange(e.total) &&
    e.items.every((l) => amountInRange(l.amount))
  )
}

export const itemShareCodec: Codec<ItemShare> = {
  write(w, s) {
    w.nat(s.line)
    w.option(s.qty, (w2, q) => w2.nat(q))
  },
  read(r) {
    return { line: r.nat(), qty: r.option((r2) => r2.nat()) }
  },
}

export const itemGroupCodec: Codec<ItemGroup> = {
  write(w, g) {
    w.list(g.items, (w2, s) => itemShareCodec.write(w2, s))
    w.str(g.into)
  },
  read(r) {
    return { items: r.list((r2) => itemShareCodec.read(r2)), into: r.str() }
  },
}

/* ------------------------------------------------------------------ */
/* Payment requests and invoices                                       */
/* ------------------------------------------------------------------ */

export const paymentRequestCodec: Codec<PaymentRequest> = {
  write(w, p) {
    if (p.kind === 'epc') {
      w.nat(0)
      w.str(p.name)
      w.str(p.iban)
      w.option(p.bic, (w2, s) => w2.str(s))
    } else {
      w.nat(1)
      w.str(p.url)
    }
  },
  read(r) {
    const t = r.nat()
    if (t === 0) {
      return { kind: 'epc', name: r.str(), iban: r.str(), bic: r.option((r2) => r2.str()) }
    }
    if (t === 1) return { kind: 'link', url: r.str() }
    throw new CodecError(`not a payment request tag: ${t}`)
  },
}

export const invoiceLineCodec: Codec<InvoiceLine> = {
  write(w, l) {
    w.str(l.description)
    w.int(l.qtyMilli)
    amountCodec.write(w, l.unitPrice)
    w.int(l.taxBp)
  },
  read(r) {
    return {
      description: r.str(),
      qtyMilli: r.int(),
      unitPrice: amountCodec.read(r),
      taxBp: r.int(),
    }
  },
  wf: (l) => amountInRange(l.unitPrice),
}

export const invoiceCodec: Codec<Invoice> = {
  write(w, i) {
    w.str(i.id)
    w.str(i.number)
    dateCodec.write(w, i.issued)
    dateCodec.write(w, i.due)
    w.option(i.payerId, (w2, s) => w2.str(s))
    w.str(i.payerName)
    commodityCodec.write(w, i.commodity)
    w.str(i.reference)
    invoiceStatusCodec.write(w, i.status)
    w.option(i.note, (w2, s) => w2.str(s))
    w.option(i.settledTxn, (w2, s) => w2.str(s))
    paymentRequestCodec.write(w, i.payment)
    w.option(i.sourceAccount, (w2, s) => w2.str(s))
    w.option(i.budgetId, (w2, s) => w2.str(s))
    w.option(i.pendingTxn, (w2, s) => w2.str(s))
    w.list(i.lines, (w2, l) => invoiceLineCodec.write(w2, l))
  },
  read(r) {
    return {
      id: r.str(),
      number: r.str(),
      issued: dateCodec.read(r),
      due: dateCodec.read(r),
      payerId: r.option((r2) => r2.str()),
      payerName: r.str(),
      commodity: commodityCodec.read(r),
      reference: r.str(),
      status: invoiceStatusCodec.read(r),
      note: r.option((r2) => r2.str()),
      settledTxn: r.option((r2) => r2.str()),
      payment: paymentRequestCodec.read(r),
      sourceAccount: r.option((r2) => r2.str()),
      budgetId: r.option((r2) => r2.str()),
      pendingTxn: r.option((r2) => r2.str()),
      lines: r.list((r2) => invoiceLineCodec.read(r2)),
    }
  },
  wf: invoiceInRange,
}

/** Everything an invoice carries, bounded. */
function invoiceInRange(i: Invoice): boolean {
  return (
    dateInRange(i.issued) &&
    dateInRange(i.due) &&
    commodityInRange(i.commodity) &&
    i.lines.every((l) => amountInRange(l.unitPrice))
  )
}

/* ------------------------------------------------------------------ */
/* Members, realms and the state's parts                               */
/* ------------------------------------------------------------------ */

export const memberCodec: Codec<Member> = {
  write(w, m) {
    w.str(m.id)
    w.str(m.name)
    w.str(m.party)
  },
  read(r) {
    return { id: r.str(), name: r.str(), party: r.str() }
  },
}

export const realmCodec: Codec<Realm> = {
  write(w, x) {
    w.str(x.id)
    w.str(x.name)
    w.list(x.members, (w2, [id, role]) => {
      w2.str(id)
      realmRoleCodec.write(w2, role)
    })
    w.nat(x.generation)
  },
  read(r) {
    return {
      id: r.str(),
      name: r.str(),
      members: r.list((r2): [string, RealmRole] => [r2.str(), realmRoleCodec.read(r2)]),
      generation: r.nat(),
    }
  },
}

export const budgetStateCodec: Codec<BudgetState> = {
  write(w, b) {
    budgetCodec.write(w, b.budget)
    w.list(b.participants, (w2, p) => participantCodec.write(w2, p))
    w.str(b.realm)
    w.str(b.account)
    w.str(b.label)
  },
  read(r) {
    return {
      budget: budgetCodec.read(r),
      participants: r.list((r2) => participantCodec.read(r2)),
      realm: r.str(),
      account: r.str(),
      label: r.str(),
    }
  },
}

export const invoiceStateCodec: Codec<InvoiceState> = {
  write(w, i) {
    invoiceCodec.write(w, i.invoice)
    w.list(i.sources, (w2, s) => w2.str(s))
    // Last, after the outlays it bills for: the field format-version 6 added.
    w.str(i.realm)
  },
  read(r) {
    return {
      invoice: invoiceCodec.read(r),
      sources: r.list((r2) => r2.str()),
      realm: r.str(),
    }
  },
  wf: (i) => invoiceInRange(i.invoice),
}

export const blobStateCodec: Codec<BlobState> = {
  write(w, b) {
    attachmentCodec.write(w, b.file)
    extractedCodec.write(w, b.extracted)
    w.list(b.items, (w2, l) => lineItemCodec.write(w2, l))
    w.str(b.registeredBy)
    w.str(b.realm)
  },
  read(r) {
    return {
      file: attachmentCodec.read(r),
      extracted: extractedCodec.read(r),
      items: r.list((r2) => lineItemCodec.read(r2)),
      registeredBy: r.str(),
      realm: r.str(),
    }
  },
  wf: (b) => extractedInRange(b.extracted) && b.items.every((l) => amountInRange(l.amount)),
}

/* ------------------------------------------------------------------ */
/* The state                                                           */
/* ------------------------------------------------------------------ */

/** A map's entries in key order: `Resources.sortedPairs`. */
export function sortedPairs<T>(m: Map<string, T>): [string, T][] {
  return mergeSort([...m.entries()], (a, b) => compareStrings(a[0], b[0]) <= 0)
}

/** A map's values in key order: `Resources.sortedValues`. */
export function sortedValues<T>(m: Map<string, T>): T[] {
  return sortedPairs(m).map(([, v]) => v)
}

/** A set's elements in order, as `State.wire` writes the fingerprints. */
export function sortedKeys(s: Set<string>): string[] {
  return mergeSort([...s], (a, b) => compareStrings(a, b) <= 0)
}

function writeMap<T>(w: Writer, m: Map<string, T>, codec: Codec<T>): void {
  const ps = sortedPairs(m)
  w.nat(ps.length)
  for (const [k, v] of ps) {
    w.str(k)
    codec.write(w, v)
  }
}

/**
 * Reads a map, and refuses the two shapes the writer never produces.
 *
 * *Unsorted or repeated keys.* The entries used to be folded back in with
 * `insert`, so a list in any order, with any duplicates, rebuilt a map that
 * re-encoded to different bytes — and a checkpoint is the hash of those bytes.
 * `ascending` rules out both at once.
 *
 * *A key that is not the entity's own id.* Nothing stopped a decoded state
 * holding `accounts["A"] = { id: "B", … }`, which no operation can produce and
 * which makes "the account with this id" a question with two answers.
 *
 * `StateWire.canonical` in `Core/Encode.lean`, checked entry by entry as the
 * entries arrive rather than afterwards.
 */
function readMap<T>(r: Reader, codec: Codec<T>, idOf: (x: T) => string): Map<string, T> {
  const n = r.nat()
  const m = new Map<string, T>()
  let previous: string | null = null
  for (let i = 0; i < n; i++) {
    const k = r.str()
    if (previous !== null && compareStrings(previous, k) >= 0) {
      throw new CodecError(`map entries are not strictly ascending by key: ${previous}, ${k}`)
    }
    previous = k
    const v = codec.read(r)
    if (idOf(v) !== k) {
      throw new CodecError(`an entry filed under '${k}' carries the id '${idOf(v)}'`)
    }
    m.set(k, v)
  }
  return m
}

/** The same, for the one map whose values carry no id of their own. */
function readCounters(r: Reader): Map<string, bigint> {
  const n = r.nat()
  const m = new Map<string, bigint>()
  let previous: string | null = null
  for (let i = 0; i < n; i++) {
    const k = r.str()
    if (previous !== null && compareStrings(previous, k) >= 0) {
      throw new CodecError(`counters are not strictly ascending by key: ${previous}, ${k}`)
    }
    previous = k
    m.set(k, intCodec.read(r))
  }
  return m
}

/** The fingerprint set: names in order, with none of them twice. */
function readFingerprints(r: Reader): Set<string> {
  const names = r.list((r2) => r2.str())
  for (let i = 1; i < names.length; i++) {
    if (compareStrings(names[i - 1], names[i]) >= 0) {
      throw new CodecError('fingerprints are not strictly ascending')
    }
  }
  return new Set(names)
}

export const stateCodec: Codec<State> = {
  write(w, s) {
    writeMap(w, s.realms, realmCodec)
    writeMap(w, s.members, memberCodec)
    writeMap(w, s.accounts, accountCodec)
    writeMap(w, s.labels, labelCodec)
    writeMap(w, s.parties, partyCodec)
    writeMap(w, s.groups, partyGroupCodec)
    writeMap(w, s.trips, tripCodec)
    writeMap(w, s.rules, ruleCodec)
    writeMap(w, s.txns, transactionCodec)
    writeMap(w, s.budgets, budgetStateCodec)
    writeMap(w, s.invoices, invoiceStateCodec)
    writeMap(w, s.blobs, blobStateCodec)
    writeMap(w, s.batches, importBatchCodec)
    writeMap(w, s.counters, intCodec)
    w.list(sortedKeys(s.fingerprints), (w2, f) => w2.str(f))
  },
  read(r) {
    return {
      realms: readMap(r, realmCodec, (x) => x.id),
      members: readMap(r, memberCodec, (x) => x.id),
      accounts: readMap(r, accountCodec, (x) => x.id),
      labels: readMap(r, labelCodec, (x) => x.id),
      parties: readMap(r, partyCodec, (x) => x.id),
      groups: readMap(r, partyGroupCodec, (x) => x.name),
      trips: readMap(r, tripCodec, (x) => x.name),
      rules: readMap(r, ruleCodec, (x) => x.id),
      txns: readMap(r, transactionCodec, (x) => x.id),
      budgets: readMap(r, budgetStateCodec, (x) => x.budget.id),
      invoices: readMap(r, invoiceStateCodec, (x) => x.invoice.id),
      blobs: readMap(r, blobStateCodec, (x) => x.file.sha256),
      batches: readMap(r, importBatchCodec, (x) => x.id),
      counters: readCounters(r),
      fingerprints: readFingerprints(r),
    }
  },
  wf: stateInRange,
}

/**
 * Everything a state holds, bounded.
 *
 * This is the door that matters, and it is the reason the walk exists at all: a
 * checkpoint is the hash of a state's canonical encoding, and a state is a value
 * the ledger *believes* rather than an intent it applies, so nothing else ever
 * asks about the numbers inside one. `Wellformed State` in `Core/Encode.lean`,
 * map for map in the order they are written.
 */
export function stateInRange(s: State): boolean {
  const every = <T,>(m: Map<string, T>, ok: (x: T) => boolean): boolean => {
    for (const v of m.values()) if (!ok(v)) return false
    return true
  }
  return (
    every(
      s.accounts,
      (a) => dateOptInRange(a.closedOn) && (a.commodity === null || commodityInRange(a.commodity)),
    ) &&
    every(s.trips, (t) => dateInRange(t.starts) && dateInRange(t.ends)) &&
    every(s.rules, (x) => filterInRange(x.filter)) &&
    every(
      s.txns,
      (t) => dateInRange(t.date) && t.postings.every((p) => amountInRange(p.amount)),
    ) &&
    every(s.invoices, (i) => invoiceInRange(i.invoice)) &&
    every(
      s.blobs,
      (b) => extractedInRange(b.extracted) && b.items.every((l) => amountInRange(l.amount)),
    )
  )
}

/* ------------------------------------------------------------------ */
/* Operations                                                          */
/* ------------------------------------------------------------------ */

const strList: Codec<string[]> = {
  write: (w, xs) => w.list(xs, (w2, s) => w2.str(s)),
  read: (r) => r.list((r2) => r2.str()),
}

export const opCodec: Codec<Op> = {
  write(w, op) {
    w.nat(op.tag)
    switch (op.kind) {
      case 'createRealm':
        return realmCodec.write(w, op.realm)
      case 'putAccount':
        return accountCodec.write(w, op.account)
      case 'mergeAccounts':
        w.str(op.from)
        return w.str(op.into)
      case 'deleteAccount':
        return w.str(op.id)
      case 'setAccountRights':
        w.str(op.id)
        return strList.write(w, op.posters)
      case 'setAccountOwner':
        w.str(op.id)
        return w.str(op.owner)
      case 'putLabel':
        return labelCodec.write(w, op.label)
      case 'deleteLabel':
        return w.str(op.id)
      case 'putParty':
        return partyCodec.write(w, op.party)
      case 'putGroup':
        return partyGroupCodec.write(w, op.group)
      case 'deleteGroup':
        return w.str(op.name)
      case 'putTrip':
        return tripCodec.write(w, op.trip)
      case 'deleteTrip':
        return w.str(op.name)
      case 'putRule':
        return ruleCodec.write(w, op.rule)
      case 'deleteRule':
        return w.str(op.idOrName)
      case 'putTransaction':
        return transactionCodec.write(w, op.txn)
      case 'deleteTransaction':
        return w.str(op.id)
      case 'splitTransaction':
        w.str(op.id)
        strList.write(w, op.targets)
        return w.bool(op.keepShare)
      case 'mergeTransactions':
        strList.write(w, op.ids)
        w.str(op.newId)
        w.option(op.payee, (w2, s) => w2.str(s))
        w.option(op.narration, (w2, s) => w2.str(s))
        return strList.write(w, op.cancelIn)
      case 'unmergeTransaction':
        w.str(op.id)
        return strList.write(w, op.newIds)
      case 'replaceTransaction':
        w.str(op.id)
        w.list(op.parts, (w2, t) => transactionCodec.write(w2, t))
        return w.str(op.kindName)
      case 'divideByItems':
        w.str(op.id)
        w.list(op.groups, (w2, g) => itemGroupCodec.write(w2, g))
        return strList.write(w, op.newIds)
      case 'raiseClaim':
        return transactionCodec.write(w, op.txn)
      case 'resolveClaim':
        w.str(op.id)
        w.str(op.actual)
        return w.str(op.splitId)
      case 'voidClaim':
        w.str(op.id)
        return w.option(op.writeOff, (w2, [into, entry, date]) => {
          w2.str(into)
          w2.str(entry)
          dateCodec.write(w2, date)
        })
      case 'openBudget':
        budgetCodec.write(w, op.budget)
        return accountCodec.write(w, op.account)
      case 'setParticipants':
        w.str(op.budget)
        return w.list(op.among, (w2, p) => participantCodec.write(w2, p))
      case 'contribute':
        w.str(op.budget)
        return transactionCodec.write(w, op.txn)
      case 'allocate':
        w.str(op.budget)
        w.list(op.among, (w2, p) => participantCodec.write(w2, p))
        commodityCodec.write(w, op.commodity)
        dateCodec.write(w, op.date)
        w.option(op.hub, (w2, s) => w2.str(s))
        w.str(op.txnId)
        strList.write(w, op.claimIds)
        return w.str(op.labelId)
      case 'settle':
        w.str(op.budget)
        commodityCodec.write(w, op.commodity)
        w.option(op.hub, (w2, s) => w2.str(s))
        dateCodec.write(w, op.due)
        strList.write(w, op.claimIds)
        return w.str(op.labelId)
      case 'closeBudget':
        w.str(op.budget)
        w.option(op.among, (w2, ps) => w2.list(ps, (w3, p) => participantCodec.write(w3, p)))
        commodityCodec.write(w, op.commodity)
        w.option(op.hub, (w2, s) => w2.str(s))
        dateCodec.write(w, op.date)
        w.str(op.txnId)
        strList.write(w, op.claimIds)
        return w.str(op.labelId)
      case 'reopenBudget':
        return w.str(op.budget)
      case 'deleteBudget':
        return w.str(op.budget)
      case 'issueInvoice':
        invoiceCodec.write(w, op.invoice)
        return strList.write(w, op.sources)
      case 'setInvoiceStatus':
        w.str(op.id)
        return invoiceStatusCodec.write(w, op.status)
      case 'settleInvoice':
        w.str(op.id)
        return w.str(op.txn)
      case 'deleteInvoice':
        return w.str(op.id)
      case 'registerBlob':
        return attachmentCodec.write(w, op.file)
      case 'attach':
        w.str(op.txn)
        return w.str(op.sha)
      case 'detach':
        w.str(op.txn)
        return w.str(op.sha)
      case 'recordExtraction':
        w.str(op.sha)
        return extractedCodec.write(w, op.extracted)
      case 'setReceiptLines':
        w.str(op.sha)
        return w.list(op.items, (w2, l) => lineItemCodec.write(w2, l))
      case 'forgetBlob':
        return w.str(op.sha)
      case 'recordImportBatch':
        return importBatchCodec.write(w, op.batch)
      case 'addMember':
        return memberCodec.write(w, op.member)
      case 'removeMember':
        return w.str(op.id)
      case 'grant':
        w.str(op.realm)
        w.str(op.member)
        realmRoleCodec.write(w, op.role)
        return accountCodec.write(w, op.bridge)
      case 'revoke':
        w.str(op.realm)
        return w.str(op.member)
      case 'setRole':
        w.str(op.realm)
        w.str(op.member)
        return realmRoleCodec.write(w, op.role)
      case 'rotateRealmKey':
        return w.str(op.realm)
      case 'snapshot':
        return stateCodec.write(w, op.state)
      case 'payClaim':
        w.str(op.claim)
        w.str(op.payment)
        return dateCodec.write(w, op.date)
    }
  },
  read(r): Op {
    const t = r.nat()
    switch (t) {
      case 0:
        return { tag: 0, kind: 'createRealm', realm: realmCodec.read(r) }
      case 1:
        return { tag: 1, kind: 'putAccount', account: accountCodec.read(r) }
      case 2:
        return { tag: 2, kind: 'mergeAccounts', from: r.str(), into: r.str() }
      case 3:
        return { tag: 3, kind: 'deleteAccount', id: r.str() }
      case 4:
        return { tag: 4, kind: 'setAccountRights', id: r.str(), posters: strList.read(r) }
      case 5:
        return { tag: 5, kind: 'setAccountOwner', id: r.str(), owner: r.str() }
      case 6:
        return { tag: 6, kind: 'putLabel', label: labelCodec.read(r) }
      case 7:
        return { tag: 7, kind: 'deleteLabel', id: r.str() }
      case 8:
        return { tag: 8, kind: 'putParty', party: partyCodec.read(r) }
      case 9:
        return { tag: 9, kind: 'putGroup', group: partyGroupCodec.read(r) }
      case 10:
        return { tag: 10, kind: 'deleteGroup', name: r.str() }
      case 11:
        return { tag: 11, kind: 'putTrip', trip: tripCodec.read(r) }
      case 12:
        return { tag: 12, kind: 'deleteTrip', name: r.str() }
      case 13:
        return { tag: 13, kind: 'putRule', rule: ruleCodec.read(r) }
      case 14:
        return { tag: 14, kind: 'deleteRule', idOrName: r.str() }
      case 15:
        return { tag: 15, kind: 'putTransaction', txn: transactionCodec.read(r) }
      case 16:
        return { tag: 16, kind: 'deleteTransaction', id: r.str() }
      case 17:
        return {
          tag: 17,
          kind: 'splitTransaction',
          id: r.str(),
          targets: strList.read(r),
          keepShare: r.bool(),
        }
      case 18:
        return {
          tag: 18,
          kind: 'mergeTransactions',
          ids: strList.read(r),
          newId: r.str(),
          payee: r.option((r2) => r2.str()),
          narration: r.option((r2) => r2.str()),
          cancelIn: strList.read(r),
        }
      case 19:
        return { tag: 19, kind: 'unmergeTransaction', id: r.str(), newIds: strList.read(r) }
      case 20:
        return {
          tag: 20,
          kind: 'replaceTransaction',
          id: r.str(),
          parts: r.list((r2) => transactionCodec.read(r2)),
          kindName: r.str(),
        }
      case 21:
        return {
          tag: 21,
          kind: 'divideByItems',
          id: r.str(),
          groups: r.list((r2) => itemGroupCodec.read(r2)),
          newIds: strList.read(r),
        }
      case 22:
        return { tag: 22, kind: 'raiseClaim', txn: transactionCodec.read(r) }
      case 23:
        return { tag: 23, kind: 'resolveClaim', id: r.str(), actual: r.str(), splitId: r.str() }
      case 24:
        return {
          tag: 24,
          kind: 'voidClaim',
          id: r.str(),
          writeOff: r.option((r2): [string, string, LedgerDate] => [
            r2.str(),
            r2.str(),
            dateCodec.read(r2),
          ]),
        }
      case 25:
        return { tag: 25, kind: 'openBudget', budget: budgetCodec.read(r), account: accountCodec.read(r) }
      case 26:
        return {
          tag: 26,
          kind: 'setParticipants',
          budget: r.str(),
          among: r.list((r2) => participantCodec.read(r2)),
        }
      case 27:
        return { tag: 27, kind: 'contribute', budget: r.str(), txn: transactionCodec.read(r) }
      case 28:
        return {
          tag: 28,
          kind: 'allocate',
          budget: r.str(),
          among: r.list((r2) => participantCodec.read(r2)),
          commodity: commodityCodec.read(r),
          date: dateCodec.read(r),
          hub: r.option((r2) => r2.str()),
          txnId: r.str(),
          claimIds: strList.read(r),
          labelId: r.str(),
        }
      case 29:
        return {
          tag: 29,
          kind: 'settle',
          budget: r.str(),
          commodity: commodityCodec.read(r),
          hub: r.option((r2) => r2.str()),
          due: dateCodec.read(r),
          claimIds: strList.read(r),
          labelId: r.str(),
        }
      case 30:
        return {
          tag: 30,
          kind: 'closeBudget',
          budget: r.str(),
          among: r.option((r2) => r2.list((r3) => participantCodec.read(r3))),
          commodity: commodityCodec.read(r),
          hub: r.option((r2) => r2.str()),
          date: dateCodec.read(r),
          txnId: r.str(),
          claimIds: strList.read(r),
          labelId: r.str(),
        }
      case 31:
        return { tag: 31, kind: 'reopenBudget', budget: r.str() }
      case 32:
        return { tag: 32, kind: 'deleteBudget', budget: r.str() }
      case 33:
        return { tag: 33, kind: 'issueInvoice', invoice: invoiceCodec.read(r), sources: strList.read(r) }
      case 34:
        return { tag: 34, kind: 'setInvoiceStatus', id: r.str(), status: invoiceStatusCodec.read(r) }
      case 35:
        return { tag: 35, kind: 'settleInvoice', id: r.str(), txn: r.str() }
      case 36:
        return { tag: 36, kind: 'deleteInvoice', id: r.str() }
      case 37:
        return { tag: 37, kind: 'registerBlob', file: attachmentCodec.read(r) }
      case 38:
        return { tag: 38, kind: 'attach', txn: r.str(), sha: r.str() }
      case 39:
        return { tag: 39, kind: 'detach', txn: r.str(), sha: r.str() }
      case 40:
        return { tag: 40, kind: 'recordExtraction', sha: r.str(), extracted: extractedCodec.read(r) }
      case 41:
        return {
          tag: 41,
          kind: 'setReceiptLines',
          sha: r.str(),
          items: r.list((r2) => lineItemCodec.read(r2)),
        }
      case 42:
        return { tag: 42, kind: 'forgetBlob', sha: r.str() }
      case 43:
        return { tag: 43, kind: 'recordImportBatch', batch: importBatchCodec.read(r) }
      case 44:
        return { tag: 44, kind: 'addMember', member: memberCodec.read(r) }
      case 45:
        return { tag: 45, kind: 'removeMember', id: r.str() }
      case 46:
        return {
          tag: 46,
          kind: 'grant',
          realm: r.str(),
          member: r.str(),
          role: realmRoleCodec.read(r),
          bridge: accountCodec.read(r),
        }
      case 47:
        return { tag: 47, kind: 'revoke', realm: r.str(), member: r.str() }
      case 48:
        return { tag: 48, kind: 'setRole', realm: r.str(), member: r.str(), role: realmRoleCodec.read(r) }
      case 49:
        return { tag: 49, kind: 'rotateRealmKey', realm: r.str() }
      case 50:
        return { tag: 50, kind: 'snapshot', state: stateCodec.read(r) }
      case 51:
        return {
          tag: 51,
          kind: 'payClaim',
          claim: r.str(),
          payment: r.str(),
          date: dateCodec.read(r),
        }
      default:
        throw new CodecError(`not an operation tag: ${t}`)
    }
  },
  wf: opInRange,
}

/**
 * What a decoded operation is checked for, which is one thing: the state a
 * `snapshot` carries.
 *
 * The other fifty-one carry an *intent* — a transaction to write, a budget to
 * divide, a receipt's lines — and the door an intent goes through is
 * `checkBounds`, which `applyOp` runs over every one of them before it reads
 * any of it for effect. That door is the right one, and the reason is the rule
 * this whole client is built around: **an invalid part is skipped rather than
 * failing its neighbours.** An event is one author's set of parts, each in a
 * realm of its own, and a reader who cannot use one applies the others.
 * Refusing the *bytes* would throw all of them away — one part naming a silly
 * exponent would cost a reader every other realm's part in the same event,
 * decided by whoever composed it. Refusing the *part* costs exactly the part
 * that is wrong.
 *
 * A `snapshot` is the exception because it is the exception in `checkBounds`
 * too: it carries a whole `State`, and a state is a value the ledger holds
 * rather than an intent — and every value the ledger holds is bounded here,
 * because nothing checks a state before it is believed.
 */
export function opInRange(op: Op): boolean {
  return op.kind === 'snapshot' ? stateInRange(op.state) : true
}

/* ------------------------------------------------------------------ */
/* Parts, events and changes                                           */
/* ------------------------------------------------------------------ */

export const partCodec: Codec<Part> = {
  write(w, p) {
    w.str(p.realm)
    opCodec.write(w, p.op)
  },
  read(r) {
    return { realm: r.str(), op: opCodec.read(r) }
  },
  wf: (p) => opInRange(p.op),
}

export const eventCodec: Codec<LedgerEvent> = {
  write(w, e) {
    w.str(e.id)
    w.str(e.author)
    w.str(e.composedAt)
    w.nat(e.basedOn)
    w.list(e.parts, (w2, p) => partCodec.write(w2, p))
  },
  read(r) {
    return {
      id: r.str(),
      author: r.str(),
      composedAt: r.str(),
      basedOn: r.nat(),
      parts: r.list((r2) => partCodec.read(r2)),
    }
  },
  wf: (e) => e.parts.every((p) => opInRange(p.op)),
}

export const changeCodec: Codec<Change> = {
  write(w, c) {
    w.nat(c.tag)
    switch (c.kind) {
      case 'realm':
        return realmCodec.write(w, c.realm)
      case 'member':
        return memberCodec.write(w, c.member)
      case 'memberDeleted':
        return w.str(c.id)
      case 'account':
        return accountCodec.write(w, c.account)
      case 'accountDeleted':
        return w.str(c.id)
      case 'label':
        return labelCodec.write(w, c.label)
      case 'labelDeleted':
        return w.str(c.id)
      case 'party':
        return partyCodec.write(w, c.party)
      case 'group':
        return partyGroupCodec.write(w, c.group)
      case 'groupDeleted':
        return w.str(c.name)
      case 'trip':
        return tripCodec.write(w, c.trip)
      case 'tripDeleted':
        return w.str(c.name)
      case 'rule':
        return ruleCodec.write(w, c.rule)
      case 'ruleDeleted':
        return w.str(c.id)
      case 'txn':
        return transactionCodec.write(w, c.txn)
      case 'txnDeleted':
        return w.str(c.id)
      case 'budget':
        return budgetStateCodec.write(w, c.budget)
      case 'budgetDeleted':
        return w.str(c.id)
      case 'invoice':
        return invoiceStateCodec.write(w, c.invoice)
      case 'invoiceDeleted':
        return w.str(c.id)
      case 'blob':
        return blobStateCodec.write(w, c.blob)
      case 'blobDeleted':
        return w.str(c.sha)
      case 'batch':
        return importBatchCodec.write(w, c.batch)
      case 'counter':
        w.str(c.name)
        return w.int(c.value)
      case 'fingerprint':
        return w.str(c.fp)
    }
  },
  read(r): Change {
    const t = r.nat()
    switch (t) {
      case 0:
        return { tag: 0, kind: 'realm', realm: realmCodec.read(r) }
      case 1:
        return { tag: 1, kind: 'member', member: memberCodec.read(r) }
      case 2:
        return { tag: 2, kind: 'memberDeleted', id: r.str() }
      case 3:
        return { tag: 3, kind: 'account', account: accountCodec.read(r) }
      case 4:
        return { tag: 4, kind: 'accountDeleted', id: r.str() }
      case 5:
        return { tag: 5, kind: 'label', label: labelCodec.read(r) }
      case 6:
        return { tag: 6, kind: 'labelDeleted', id: r.str() }
      case 7:
        return { tag: 7, kind: 'party', party: partyCodec.read(r) }
      case 8:
        return { tag: 8, kind: 'group', group: partyGroupCodec.read(r) }
      case 9:
        return { tag: 9, kind: 'groupDeleted', name: r.str() }
      case 10:
        return { tag: 10, kind: 'trip', trip: tripCodec.read(r) }
      case 11:
        return { tag: 11, kind: 'tripDeleted', name: r.str() }
      case 12:
        return { tag: 12, kind: 'rule', rule: ruleCodec.read(r) }
      case 13:
        return { tag: 13, kind: 'ruleDeleted', id: r.str() }
      case 14:
        return { tag: 14, kind: 'txn', txn: transactionCodec.read(r) }
      case 15:
        return { tag: 15, kind: 'txnDeleted', id: r.str() }
      case 16:
        return { tag: 16, kind: 'budget', budget: budgetStateCodec.read(r) }
      case 17:
        return { tag: 17, kind: 'budgetDeleted', id: r.str() }
      case 18:
        return { tag: 18, kind: 'invoice', invoice: invoiceStateCodec.read(r) }
      case 19:
        return { tag: 19, kind: 'invoiceDeleted', id: r.str() }
      case 20:
        return { tag: 20, kind: 'blob', blob: blobStateCodec.read(r) }
      case 21:
        return { tag: 21, kind: 'blobDeleted', sha: r.str() }
      case 22:
        return { tag: 22, kind: 'batch', batch: importBatchCodec.read(r) }
      case 23:
        return { tag: 23, kind: 'counter', name: r.str(), value: r.int() }
      case 24:
        return { tag: 24, kind: 'fingerprint', fp: r.str() }
      default:
        throw new CodecError(`not a change tag: ${t}`)
    }
  },
  wf: (c) => {
    switch (c.kind) {
      case 'account':
        return (
          dateOptInRange(c.account.closedOn) &&
          (c.account.commodity === null || commodityInRange(c.account.commodity))
        )
      case 'trip':
        return dateInRange(c.trip.starts) && dateInRange(c.trip.ends)
      case 'rule':
        return filterInRange(c.rule.filter)
      case 'txn':
        return dateInRange(c.txn.date) && c.txn.postings.every((p) => amountInRange(p.amount))
      case 'invoice':
        return invoiceInRange(c.invoice.invoice)
      case 'blob':
        return (
          extractedInRange(c.blob.extracted) &&
          c.blob.items.every((l) => amountInRange(l.amount))
        )
      default:
        return true
    }
  },
}

/* ------------------------------------------------------------------ */
/* What a part's plaintext is                                          */
/* ------------------------------------------------------------------ */

/**
 * What travels inside one encrypted part.
 *
 * The spec's product `(eventId, composedAt, basedOn, part)`: the per-event
 * fields ride in every part's plaintext, so a reader who can open one part can
 * rebuild an `Event` out of it, and readers who can open several check that
 * they agree.
 */
export interface PartPlaintext {
  eventId: string
  composedAt: string
  basedOn: number
  part: Part
}

export const partPlaintextCodec: Codec<PartPlaintext> = {
  write(w, p) {
    w.str(p.eventId)
    w.str(p.composedAt)
    w.nat(p.basedOn)
    partCodec.write(w, p.part)
  },
  read(r) {
    return {
      eventId: r.str(),
      composedAt: r.str(),
      basedOn: r.nat(),
      part: partCodec.read(r),
    }
  },
  wf: (p) => opInRange(p.part.op),
}
