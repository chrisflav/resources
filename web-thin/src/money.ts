/**
 * Commodities, amounts and the two ways a total is divided without losing a
 * minor unit.
 *
 * A port of `Resources/Core/Money.lean`. Everything is `bigint`: there are no
 * floating point numbers anywhere in this system, and a cent lost to one is
 * lost for good.
 *
 * The one subtlety is which integer division Lean means. `/` on `Int` in Lean 4
 * is `Int.ediv` — Euclidean, so the remainder is never negative, which for a
 * positive divisor is floor division and for a negative one rounds the other
 * way. `splitParts` and `biproportional` are both built out of it, and getting
 * it wrong would move a cent between two people in exactly the cases the
 * telescoping argument is there to rule out.
 */

import type { Amount, Commodity, Participant } from './types'

/** Euclidean division, which is what `/` on `Int` means in Lean 4. */
export function ediv(a: bigint, b: bigint): bigint {
  if (b === 0n) return 0n
  const q = a / b
  const r = a % b
  if (r < 0n) return b > 0n ? q - 1n : q + 1n
  return q
}

/** Commodities whose exponent differs from the default of 2. */
const knownExponents = new Map<string, number>([
  ['JPY', 0],
  ['KRW', 0],
  ['ISK', 0],
  ['CLP', 0],
  ['BHD', 3],
  ['KWD', 3],
  ['TND', 3],
])

/** Looks up a commodity by code. Unknown commodities get two decimal places. */
export function commodityOfCode(code: string): Commodity {
  const c = code.toUpperCase()
  return { code: c, exponent: knownExponents.get(c) ?? 2 }
}

/** The euro. */
export const eur: Commodity = commodityOfCode('EUR')

/** 10 ^ exponent, the number of minor units in one major unit. */
export function scale(c: Commodity): bigint {
  return 10n ** BigInt(c.exponent)
}

/** Renders the numeric part only, e.g. `-49.90`. */
export function digits(a: Amount): string {
  const s = scale(a.commodity)
  const negative = a.minor < 0n
  const n = negative ? -a.minor : a.minor
  const major = n / s
  const minor = n % s
  const frac =
    a.commodity.exponent === 0 ? '' : '.' + minor.toString().padStart(a.commodity.exponent, '0')
  return (negative ? '-' : '') + major.toString() + frac
}

/** Renders as `-49.90 EUR`. */
export function render(a: Amount): string {
  return digits(a) + ' ' + a.commodity.code
}

/** Whether two commodities are the same value. */
export function sameCommodity(a: Commodity, b: Commodity): boolean {
  return a.code === b.code && a.exponent === b.exponent
}

/** The `i`-th cut point of `total` divided `n` ways. */
function cut(total: bigint, n: number, i: number): bigint {
  return ediv(total * BigInt(i), BigInt(n))
}

/**
 * Splits `total` into `n` parts that differ by at most one minor unit and sum
 * back to exactly `total`.
 */
export function splitParts(total: bigint, n: number): bigint[] {
  const out: bigint[] = []
  for (let i = 0; i < n; i++) out.push(cut(total, n, i + 1) - cut(total, n, i))
  return out
}

/** Running totals of a list, starting at zero: `[0, x₀, x₀+x₁, …]`. */
function prefixSums(xs: readonly bigint[]): bigint[] {
  const out: bigint[] = [0n]
  for (const x of xs) out.push(out[out.length - 1] + x)
  return out
}

/**
 * Splits a total across a grid so that **both** the row sums and the column
 * sums come out exactly right.
 *
 * Every cell is a second difference of one monotone function of the two running
 * totals, so summing along either axis telescopes down to that axis's own
 * total.
 */
export function biproportional(rows: readonly bigint[], cols: readonly bigint[]): bigint[][] {
  const total = sum(rows)
  const rs = prefixSums(rows)
  const cs = prefixSums(cols)
  const corner = (a: bigint, b: bigint): bigint => (total === 0n ? 0n : ediv(a * b, total))
  const out: bigint[][] = []
  for (let i = 0; i < rows.length; i++) {
    const row: bigint[] = []
    for (let j = 0; j < cols.length; j++) {
      row.push(corner(rs[i + 1], cs[j + 1]) - corner(rs[i], cs[j + 1]) - corner(rs[i + 1], cs[j]) + corner(rs[i], cs[j]))
    }
    out.push(row)
  }
  return out
}

/** The sum of a list of integers. */
export function sum(xs: readonly bigint[]): bigint {
  let acc = 0n
  for (const x of xs) acc += x
  return acc
}

/**
 * Each participant's part of an amount, to the minor unit.
 *
 * `Budget.shareOut`: a participant's weight is a run of consecutive parts, so
 * unequal shares cost nothing in accuracy.
 */
export function shareOut(minor: bigint, among: readonly Participant[]): bigint[] {
  const weights = among.map((p) => Math.max(p.weight, 1))
  let totalWeight = 0
  for (const w of weights) totalWeight += w
  const parts = splitParts(minor, totalWeight)
  const out: bigint[] = []
  let at = 0
  for (const w of weights) {
    out.push(sum(parts.slice(at, at + w)))
    at += w
  }
  return out
}

/**
 * Parses a decimal quantity for a commodity: `1234.56`, `1.234,56`, `-49,90`
 * and `+7`, i.e. both European and Anglo conventions, with optional thousands
 * separators. A cut-down `Amount.parseDigits`, which is all a browser form
 * needs; the full parser lives in `Core/Money.lean`.
 */
export function parseAmount(input: string, c: Commodity = eur): Amount {
  const s = input.trim().replace(/[\s ]/g, '')
  if (s === '') throw new Error('empty amount')
  const sign = s.startsWith('-') ? -1n : 1n
  const body = s.startsWith('-') || s.startsWith('+') ? s.slice(1) : s
  const dots = body.split('.').length - 1
  const commas = body.split(',').length - 1
  let intPart: string
  let fracPart: string
  // The last separator present is the decimal point; earlier ones group digits.
  if (commas > 0 && (dots === 0 || (body.split(',').pop() ?? '').length <= 2)) {
    const parts = body.split(',')
    fracPart = parts.pop() ?? ''
    intPart = parts.join('').replace(/\./g, '')
  } else if (dots > 0) {
    const parts = body.split('.')
    fracPart = parts.pop() ?? ''
    intPart = parts.join('').replace(/,/g, '')
  } else {
    intPart = body.replace(/[,.]/g, '')
    fracPart = ''
  }
  if (!/^\d*$/.test(intPart) || !/^\d*$/.test(fracPart)) {
    throw new Error(`not a number: ${input}`)
  }
  if (fracPart.length > c.exponent) {
    throw new Error(`too many decimal places for ${c.code}: ${input}`)
  }
  const frac = fracPart.padEnd(c.exponent, '0')
  const whole = BigInt(intPart === '' ? '0' : intPart) * scale(c)
  const minor = frac === '' ? 0n : BigInt(frac)
  return { commodity: c, minor: sign * (whole + minor) }
}
