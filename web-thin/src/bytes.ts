/**
 * Bytes, text and order.
 *
 * The small things every other module needs and that have to agree with Lean
 * exactly: how a string is compared, how a stable sort behaves, and the
 * `seg` framing `Sync/Protocol.lean` builds every signed byte string from.
 */

const encoder = new TextEncoder()
const decoder = new TextDecoder('utf-8', { fatal: true })

/** UTF-8 bytes of a string, as `String.toUTF8` gives them. */
export function utf8(s: string): Uint8Array {
  return encoder.encode(s)
}

/** A string from UTF-8 bytes; throws on invalid UTF-8, as `String.fromUTF8?` refuses it. */
export function fromUtf8(bs: Uint8Array): string {
  return decoder.decode(bs)
}

/** Concatenates byte arrays. */
export function concat(...parts: Uint8Array[]): Uint8Array {
  let n = 0
  for (const p of parts) n += p.length
  const out = new Uint8Array(n)
  let at = 0
  for (const p of parts) {
    out.set(p, at)
    at += p.length
  }
  return out
}

/** Lowercase hex, as `Resources.toHex`. */
export function toHex(bs: Uint8Array): string {
  let out = ''
  for (const b of bs) out += b.toString(16).padStart(2, '0')
  return out
}

/** Hex in either case; `null` unless the string is an even run of hex digits. */
export function fromHex(s: string): Uint8Array | null {
  if (s.length % 2 !== 0) return null
  const out = new Uint8Array(s.length / 2)
  for (let i = 0; i < out.length; i++) {
    const byte = Number.parseInt(s.slice(2 * i, 2 * i + 2), 16)
    if (!/^[0-9a-fA-F]{2}$/.test(s.slice(2 * i, 2 * i + 2))) return null
    out[i] = byte
  }
  return out
}

/** Standard base64 with `=` padding: how ciphertext travels. */
export function toBase64(bs: Uint8Array): string {
  let s = ''
  for (const b of bs) s += String.fromCharCode(b)
  return btoa(s)
}

/** Decodes standard base64, tolerating whitespace and missing padding. */
export function fromBase64(s: string): Uint8Array {
  const clean = s.replace(/[\s=]/g, '')
  const padded = clean + '='.repeat((4 - (clean.length % 4)) % 4)
  const raw = atob(padded)
  const out = new Uint8Array(raw.length)
  for (let i = 0; i < raw.length; i++) out[i] = raw.charCodeAt(i)
  return out
}

/** base64url, without padding: how an invite secret rides in a fragment. */
export function toBase64Url(bs: Uint8Array): string {
  return toBase64(bs).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '')
}

/** Decodes base64url. */
export function fromBase64Url(s: string): Uint8Array {
  return fromBase64(s.replace(/-/g, '+').replace(/_/g, '/'))
}

/**
 * One length-prefixed segment: the byte length in ASCII decimal, a colon, then
 * the bytes. `Sync.seg`.
 */
export function seg(bs: Uint8Array): Uint8Array {
  return concat(utf8(String(bs.length)), utf8(':'), bs)
}

/** A string as one segment of its UTF-8. `Sync.segStr`. */
export function segStr(s: string): Uint8Array {
  return seg(utf8(s))
}

/** A number as one segment of its ASCII decimal digits. `Sync.segNat`. */
export function segNat(n: number): Uint8Array {
  return segStr(String(n))
}

/**
 * Lean's order on strings: lexicographic by Unicode code point.
 *
 * Not JavaScript's `<`, which compares UTF-16 code units and therefore puts
 * every astral character before `U+E000`–`U+FFFF`. Every sorted iteration in
 * `Core` goes through this, and a checkpoint hash depends on it.
 */
export function compareStrings(a: string, b: string): number {
  if (a === b) return 0
  const as = Array.from(a)
  const bs = Array.from(b)
  const n = Math.min(as.length, bs.length)
  for (let i = 0; i < n; i++) {
    const x = as[i].codePointAt(0)!
    const y = bs[i].codePointAt(0)!
    if (x !== y) return x < y ? -1 : 1
  }
  return as.length === bs.length ? 0 : as.length < bs.length ? -1 : 1
}

/** `a ≤ b` on strings, Lean's order. */
export function stringLe(a: string, b: string): boolean {
  return compareStrings(a, b) <= 0
}

/**
 * A stable merge sort driven by a `≤` predicate, which is the shape
 * `List.mergeSort` takes and the shape every comparator in `Core` is written
 * in. Ties keep their original order, so the result is the same list Lean
 * produces.
 */
export function mergeSort<T>(xs: readonly T[], le: (a: T, b: T) => boolean): T[] {
  if (xs.length <= 1) return xs.slice()
  const mid = xs.length >> 1
  const left = mergeSort(xs.slice(0, mid), le)
  const right = mergeSort(xs.slice(mid), le)
  const out: T[] = []
  let i = 0
  let j = 0
  while (i < left.length && j < right.length) {
    if (le(left[i], right[j])) out.push(left[i++])
    else out.push(right[j++])
  }
  while (i < left.length) out.push(left[i++])
  while (j < right.length) out.push(right[j++])
  return out
}

/** `Str.clamp`: at most `n` code points. */
export function clamp(s: string, n: number): string {
  const cs = Array.from(s)
  return cs.length <= n ? s : cs.slice(0, n).join('')
}

/** `String.trimAscii`: drops ASCII whitespace at both ends. */
export function trimAscii(s: string): string {
  return s.replace(/^[\t\n\v\f\r ]+/, '').replace(/[\t\n\v\f\r ]+$/, '')
}

/** Keeps the first occurrence of each element, in order: `List.eraseDups`. */
export function eraseDups<T>(xs: readonly T[]): T[] {
  const seen = new Set<T>()
  const out: T[] = []
  for (const x of xs) {
    if (!seen.has(x)) {
      seen.add(x)
      out.push(x)
    }
  }
  return out
}
