/**
 * Settling up.
 *
 * A port of `Resources/Core/Settle.lean`. A *plan* is a list of transfers; its
 * one obligation is that performing it leaves everybody at zero, and that is
 * checked before a single claim is written. Nothing here decides who *should*
 * pay whom — `greedy` and `star` are two defensible answers and the caller
 * picks.
 */

/** One party's net position. Positive means they owe the group. */
export interface Position {
  who: string
  minor: bigint
}

/** One payment in a plan: `minor` moves from `from_` to `to`. */
export interface Transfer {
  from_: string
  to: string
  minor: bigint
}

/** The total of a list of positions. Zero exactly when there is nothing left over. */
export function total(ps: readonly Position[]): bigint {
  let acc = 0n
  for (const p of ps) acc += p.minor
  return acc
}

/** One transfer's effect on a position. */
export function applyOne(t: Transfer, p: Position): Position {
  if (p.who === t.from_) return { who: p.who, minor: p.minor - t.minor }
  if (p.who === t.to) return { who: p.who, minor: p.minor + t.minor }
  return p
}

/** What the positions become once every transfer has been performed. */
export function residual(ps: readonly Position[], ts: readonly Transfer[]): Position[] {
  let out = ps.slice()
  for (const t of ts) out = out.map((p) => applyOne(t, p))
  return out
}

/** A plan settles these positions when it leaves every one of them at zero. */
export function settles(ps: readonly Position[], ts: readonly Transfer[]): boolean {
  return residual(ps, ts).every((p) => p.minor === 0n)
}

/**
 * The largest debtor and the largest creditor, and the most that can pass
 * between them without overshooting either.
 */
export function step(ps: readonly Position[]): Transfer | null {
  let debtor: Position | null = null
  for (const p of ps) {
    if (debtor === null) {
      if (p.minor > 0n) debtor = p
    } else if (p.minor > debtor.minor) {
      debtor = p
    }
  }
  let creditor: Position | null = null
  for (const p of ps) {
    if (creditor === null) {
      if (p.minor < 0n) creditor = p
    } else if (p.minor < creditor.minor) {
      creditor = p
    }
  }
  if (debtor === null || creditor === null) return null
  if (debtor.minor > 0n && creditor.minor < 0n) {
    const size = debtor.minor < -creditor.minor ? debtor.minor : -creditor.minor
    return { from_: debtor.who, to: creditor.who, minor: size }
  }
  return null
}

/** `greedy`, with an explicit bound on how many transfers may be produced. */
export function greedyFuel(fuel: number, ps: readonly Position[]): Transfer[] {
  if (fuel === 0) return []
  const t = step(ps)
  if (t === null) return []
  return [t, ...greedyFuel(fuel - 1, ps.map((p) => applyOne(t, p)))]
}

/**
 * Repeatedly settle the largest debtor against the largest creditor. Shortest,
 * and quite willing to tell somebody to pay a person they never dealt with.
 */
export function greedy(ps: readonly Position[]): Transfer[] {
  return greedyFuel(ps.length, ps)
}

/** Everybody settles with one person: whoever holds the budget. */
export function star(hub: string, ps: readonly Position[]): Transfer[] {
  const out: Transfer[] = []
  for (const p of ps) {
    if (p.who === hub || p.minor === 0n) continue
    if (p.minor > 0n) out.push({ from_: p.who, to: hub, minor: p.minor })
    else out.push({ from_: hub, to: p.who, minor: -p.minor })
  }
  return out
}

/**
 * Checks a plan before anything is written down, with the same two sentences
 * `Settle.validate` produces.
 */
export function validate(ps: readonly Position[], ts: readonly Transfer[]): Transfer[] {
  if (settles(ps, ts)) return ts.slice()
  const left = residual(ps, ts).filter((p) => p.minor !== 0n)
  const detail = left.map((p) => `${p.who} ${p.minor}`).join(', ')
  if (total(ps) !== 0n) {
    throw new Error(`these positions do not sum to zero, so nothing can settle them: ${detail}`)
  }
  throw new Error(`the plan would leave: ${detail}`)
}
