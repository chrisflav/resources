/**
 * The arithmetic, on its own.
 *
 * Both obligations of a division are checked directly: every cost is fully
 * divided and every person receives exactly the share the weights say. Rounding
 * each cost independently satisfies the first and drifts on the second;
 * rounding each person's total independently does the reverse. Nothing here
 * would notice the difference between the two if it only checked one.
 */

import { describe, expect, it } from 'vitest'
import { biproportional, ediv, eur, parseAmount, render, shareOut, splitParts, sum } from './money'
import { greedy, residual, star, validate } from './settle'
import type { Participant } from './types'

const person = (name: string, weight: number): Participant => ({
  owner: `p-${name}`,
  name,
  account: `Expenses.${name}`,
  weight,
})

describe('integer division', () => {
  it('is Euclidean, which is floor for a positive divisor', () => {
    expect(ediv(7n, 2n)).toBe(3n)
    expect(ediv(-7n, 2n)).toBe(-4n)
    expect(ediv(7n, -2n)).toBe(-3n)
    expect(ediv(-7n, -2n)).toBe(4n)
    expect(ediv(6n, 3n)).toBe(2n)
    expect(ediv(-6n, 3n)).toBe(-2n)
  })
})

describe('splitParts', () => {
  it('adds back to exactly what was paid', () => {
    for (const total of [0n, 1n, 100n, 1234n, -1n, -100n, -4999n, 10n ** 12n]) {
      for (const n of [1, 2, 3, 7, 13]) {
        const parts = splitParts(total, n)
        expect(parts).toHaveLength(n)
        expect(sum(parts)).toBe(total)
      }
    }
  })

  it('leaves the parts within one minor unit of each other', () => {
    const parts = splitParts(100n, 3)
    expect(parts).toEqual([33n, 33n, 34n])
    expect(splitParts(-100n, 3)).toEqual([-34n, -33n, -33n])
  })
})

describe('shareOut', () => {
  it('gives a weight a run of consecutive parts', () => {
    expect(shareOut(100n, [person('a', 1), person('b', 3)])).toEqual([25n, 75n])
    expect(shareOut(10n, [person('a', 1), person('b', 1), person('c', 1)])).toEqual([3n, 3n, 4n])
  })

  it('treats a weight below one as one', () => {
    expect(shareOut(10n, [person('a', 0), person('b', 1)])).toEqual(
      shareOut(10n, [person('a', 1), person('b', 1)]),
    )
  })

  it('always adds back to the total' , () => {
    expect(sum(shareOut(9999n, [person('a', 2), person('b', 3), person('c', 5)]))).toBe(9999n)
  })
})

describe('biproportional', () => {
  const check = (rows: bigint[], cols: bigint[]): void => {
    const grid = biproportional(rows, cols)
    expect(grid).toHaveLength(rows.length)
    // Each person receives exactly their row total.
    grid.forEach((row, i) => expect(sum(row)).toBe(rows[i]))
    // Each cost is exactly fully divided — as long as the two axes agree on
    // the total, which is the precondition the caller checks.
    if (sum(rows) === sum(cols)) {
      cols.forEach((_, j) => expect(sum(grid.map((row) => row[j]))).toBe(cols[j]))
    }
  }

  it('gets both axes right at once', () => {
    check([5000n, 5000n], [10000n])
    check([3333n, 3333n, 3334n], [1000n, 9000n])
    check([1n, 1n, 1n], [1n, 1n, 1n])
    check([7n, 11n, 13n], [5n, 9n, 17n])
  })

  it('is all zeroes when there is nothing to divide', () => {
    expect(biproportional([0n, 0n], [0n])).toEqual([[0n], [0n]])
  })
})

describe('settling', () => {
  it('zeroes everybody, greedily', () => {
    const ps = [
      { who: 'a', minor: 5000n },
      { who: 'b', minor: -3000n },
      { who: 'c', minor: -2000n },
    ]
    const plan = greedy(ps)
    expect(residual(ps, plan).every((p) => p.minor === 0n)).toBe(true)
    expect(plan.length).toBeLessThanOrEqual(ps.length)
  })

  it('routes everything through a hub when one is named', () => {
    const ps = [
      { who: 'hub', minor: 0n },
      { who: 'b', minor: -3000n },
      { who: 'c', minor: 3000n },
    ]
    const plan = star('hub', ps)
    expect(plan).toEqual([
      { from_: 'hub', to: 'b', minor: 3000n },
      { from_: 'c', to: 'hub', minor: 3000n },
    ])
    expect(residual(ps, plan).every((p) => p.minor === 0n)).toBe(true)
  })

  it('refuses a plan that would leave somebody out of pocket', () => {
    const ps = [
      { who: 'a', minor: 100n },
      { who: 'b', minor: -50n },
    ]
    expect(() => validate(ps, [])).toThrow(/do not sum to zero/)
    const square = [
      { who: 'a', minor: 100n },
      { who: 'b', minor: -100n },
    ]
    expect(() => validate(square, [])).toThrow(/would leave/)
    expect(validate(square, [{ from_: 'a', to: 'b', minor: 100n }])).toHaveLength(1)
  })
})

describe('amounts', () => {
  it('renders minor units the way Lean does', () => {
    expect(render({ commodity: eur, minor: -4990n })).toBe('-49.90 EUR')
    expect(render({ commodity: eur, minor: 0n })).toBe('0.00 EUR')
    expect(render({ commodity: { code: 'JPY', exponent: 0 }, minor: 1200n })).toBe('1200 JPY')
  })

  it('parses both conventions', () => {
    expect(parseAmount('42.50').minor).toBe(4250n)
    expect(parseAmount('42,50').minor).toBe(4250n)
    expect(parseAmount('1.234,56').minor).toBe(123456n)
    expect(parseAmount('1,234.56').minor).toBe(123456n)
    expect(parseAmount('-49,90').minor).toBe(-4990n)
    expect(parseAmount('+7').minor).toBe(700n)
    expect(() => parseAmount('')).toThrow()
    expect(() => parseAmount('4.567')).toThrow(/decimal places/)
    expect(() => parseAmount('nope')).toThrow(/not a number/)
  })
})
