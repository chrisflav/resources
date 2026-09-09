import Std.Time

/-!
# Small utilities

String, byte and date helpers shared by every layer. Nothing here knows about
the ledger; nothing here performs IO except the clock and the RNG.
-/

namespace Resources

/-! ## Bytes and text encodings -/

/-- Lowercase hex encoding of a byte array. -/
def toHex (bs : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for b in bs do
    out := out.push digits[(b.toNat >>> 4)]! |>.push digits[(b.toNat &&& 0xf)]!
  return out

/-- Crockford base32, used for identifiers and API tokens: no `I`, `L`, `O` or `U`. -/
def toBase32 (bs : ByteArray) : String := Id.run do
  let alphabet := "0123456789ABCDEFGHJKMNPQRSTVWXYZ".toList.toArray
  let mut out := ""
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  for b in bs do
    acc := (acc <<< 8) ||| b.toNat
    bits := bits + 8
    while bits >= 5 do
      bits := bits - 5
      out := out.push alphabet[(acc >>> bits) &&& 0x1f]!
  if bits > 0 then
    out := out.push alphabet[(acc <<< (5 - bits)) &&& 0x1f]!
  return out

/-- Encodes a `Nat` in Crockford base32, left-padded to `width` characters. -/
def natToBase32 (n : Nat) (width : Nat) : String := Id.run do
  let alphabet := "0123456789ABCDEFGHJKMNPQRSTVWXYZ".toList.toArray
  let mut out : List Char := []
  let mut n := n
  for _ in [0:width] do
    out := alphabet[n % 32]! :: out
    n := n / 32
  return String.ofList out

/-! ## String helpers -/

namespace Str

/-- Removes `prefix` from the front of `s`, if present. -/
def dropPrefix? (s p : String) : Option String :=
  if s.startsWith p then some (s.drop p.length).toString else none

/-- Splits on the first occurrence of `sep`. -/
def splitOnce (s : String) (sep : Char) : Option (String × String) :=
  match s.splitOn (String.singleton sep) with
  | [] => none
  | [_] => none
  | a :: rest => some (a, String.intercalate (String.singleton sep) rest)

/-- Left-pads with `c` to at least `n` characters. -/
def padLeft (s : String) (n : Nat) (c : Char := ' ') : String :=
  if s.length >= n then s else String.ofList (List.replicate (n - s.length) c) ++ s

/-- Right-pads with `c` to at least `n` characters. -/
def padRight (s : String) (n : Nat) (c : Char := ' ') : String :=
  if s.length >= n then s else s ++ String.ofList (List.replicate (n - s.length) c)

/-- Truncates to at most `n` characters. -/
def clamp (s : String) (n : Nat) : String :=
  if s.length <= n then s else (s.take n).toString

/-- Case-insensitive substring test. -/
def containsCI (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else
    let h := haystack.toLower
    let n := needle.toLower
    (h.splitOn n).length > 1

end Str

/-! ## Dates -/

open Std.Time

/-- ISO-8601 calendar date, `YYYY-MM-DD`. This is how dates are stored and exchanged. -/
abbrev Date := PlainDate

namespace Date

/-- Renders as `YYYY-MM-DD`. -/
def toIso (d : Date) : String := PlainDate.toLeanDateString d

/-- Parses `YYYY-MM-DD`. -/
def ofIso? (s : String) : Option Date :=
  match PlainDate.fromLeanDateString s with
  | .ok d => some d
  | .error _ => none

/-- Today, in the local time zone. -/
def today : IO Date := PlainDate.now

instance : Ord Date := inferInstanceAs (Ord PlainDate)

/-- Chronological comparison. -/
def le (a b : Date) : Bool := (compare a b) != .gt

/-- Strict chronological comparison. -/
def lt (a b : Date) : Bool := (compare a b) == .lt

/-- Moves `n` days forward. -/
def plusDays (d : Date) (n : Int) : Date := PlainDate.addDays d (Std.Time.Day.Offset.ofInt n)

end Date

/-- Milliseconds since the Unix epoch. -/
def nowMillis : IO Int := do
  let t ← Timestamp.now
  return t.toMillisecondsSinceUnixEpoch.val

/-- An RFC-3339-ish timestamp used for audit columns. -/
def nowStamp : IO String := do
  let dt ← PlainDateTime.now
  return dt.format "uuuu-MM-dd'T'HH:mm:ss"

end Resources
