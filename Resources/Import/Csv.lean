import Resources.Core.Ledger

/-!
# CSV and date parsing

German bank exports are reliably latin-1, semicolon-separated, `1.234,56` for
numbers and `dd.MM.yyyy` for dates, with a few lines of preamble before the
header. All four of those are profile settings rather than assumptions.
-/

namespace Resources

/-- Text encodings a bank export might arrive in. -/
inductive Encoding
  | utf8 | latin1
  deriving DecidableEq, Repr, Inhabited

namespace Encoding

/--
The 0x80–0x9F range of Windows-1252. Banks label their exports ISO-8859-1 and
then emit cp1252 anyway — the euro sign at 0x80 is the one that matters.
-/
private def cp1252High : Array Nat := #[
  0x20AC, 0x0081, 0x201A, 0x0192, 0x201E, 0x2026, 0x2020, 0x2021,
  0x02C6, 0x2030, 0x0160, 0x2039, 0x0152, 0x008D, 0x017D, 0x008F,
  0x0090, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2013, 0x2014,
  0x02DC, 0x2122, 0x0161, 0x203A, 0x0153, 0x009D, 0x017E, 0x0178]

/-- Decodes bytes to text. Total: invalid UTF-8 falls back to the single-byte path. -/
partial def decode : Encoding → ByteArray → String
  | .utf8, bs => (String.fromUTF8? bs).getD (Encoding.decode .latin1 bs)
  | .latin1, bs => Id.run do
    let mut s := ""
    for b in bs do
      let n := b.toNat
      s := s.push (Char.ofNat (if n ≥ 0x80 && n ≤ 0x9F then cp1252High[n - 0x80]! else n))
    return s

/-- Parses an encoding name. -/
def ofString? : String → Option Encoding
  | "utf8" | "utf-8" | "UTF-8" => some .utf8
  | "latin1" | "latin-1" | "iso-8859-1" | "cp1252" => some .latin1
  | _ => none

/-- The name used in profile JSON. -/
def toString : Encoding → String
  | .utf8 => "utf8" | .latin1 => "latin1"

end Encoding

/-- Strips a UTF-8 byte-order mark, which Excel-produced exports often carry. -/
def stripBom (s : String) : String :=
  if s.startsWith "﻿" then (s.drop 1).toString else s

/--
Splits CSV text into rows of fields, honouring RFC-4180 quoting: fields may be
wrapped in `"`, and `""` inside a quoted field is a literal quote.
-/
def parseCsv (delim : Char) (text : String) : Array (Array String) := Id.run do
  let mut rows : Array (Array String) := #[]
  let mut row : Array String := #[]
  let mut cur := ""
  let mut inQuote := false
  let mut prevQuote := false
  for ch in (stripBom text).toList do
    if inQuote then
      if ch == '"' then
        if prevQuote then cur := cur.push '"'; prevQuote := false
        else prevQuote := true
      else
        if prevQuote then inQuote := false; prevQuote := false
        if ch == delim then row := row.push cur; cur := ""
        else if ch == '\n' then
          row := row.push cur; cur := ""
          rows := rows.push row; row := #[]
        else if ch != '\r' then cur := cur.push ch
    else
      if ch == '"' && cur.isEmpty then inQuote := true
      else if ch == delim then row := row.push cur; cur := ""
      else if ch == '\n' then
        row := row.push cur; cur := ""
        rows := rows.push row; row := #[]
      else if ch != '\r' then cur := cur.push ch
  if !cur.isEmpty || !row.isEmpty then
    row := row.push cur
    rows := rows.push row
  return rows.filter (fun r => !(r.size == 1 && r[0]!.trimAscii.isEmpty))

/-- Normalises a header cell for matching: trimmed, lowercased, quotes removed. -/
def normHeader (s : String) : String :=
  s.trimAscii.toString.replace "\"" "" |>.toLower

/-- Left-pads a natural number with zeroes. -/
private def pad0 (n w : Nat) : String := Str.padLeft (toString n) w '0'

/--
Parses a date against a simple format string: `dd.MM.yyyy`, `yyyy-MM-dd`,
`dd/MM/yyyy`, `MM/dd/yyyy`, `dd.MM.yy`. The separator is taken from the format.
-/
def parseDateWith (fmt : String) (input : String) : Option Date := do
  let s := input.trimAscii.toString
  if fmt == "yyyy-MM-dd" || fmt == "uuuu-MM-dd" then
    Date.ofIso? s
  else
    let sep ← fmt.toList.find? (fun c => !c.isAlpha)
    let sepStr := String.singleton sep
    let fparts := fmt.splitOn sepStr
    let sparts := (s.take 10).toString.splitOn sepStr
    if fparts.length != sparts.length then none else
    Id.run do
      let mut y : Nat := 0
      let mut m : Nat := 0
      let mut d : Nat := 0
      let mut ok := true
      for (fp, sp) in fparts.zip sparts do
        match sp.trimAscii.toString.toNat? with
        | none => ok := false
        | some n =>
          match fp with
          | "yyyy" | "uuuu" => y := n
          | "yy" => y := 2000 + n
          | "MM" | "M" => m := n
          | "dd" | "d" => d := n
          | _ => ok := false
      -- Exports labelled `dd.MM.yyyy` routinely carry two-digit years anyway.
      if y < 100 then y := 2000 + y
      if !ok || y == 0 || m == 0 || d == 0 then return none
      return Date.ofIso? s!"{pad0 y 4}-{pad0 m 2}-{pad0 d 2}"

end Resources
