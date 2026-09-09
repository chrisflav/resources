import Resources.Util
import Lean.Data.Json

/-!
# Commodities and amounts

A quantity is an exact integer count of minor units of a *commodity*. EUR is a
commodity with exponent 2; so is `HOURS`. Nothing in this file mentions money
specifically, which is what lets the same ledger track time later.

There are no floating point numbers anywhere in this system.
-/

open Lean

namespace Resources

/-- A unit of account. `exponent` is the number of decimal places in its minor unit. -/
structure Commodity where
  /-- The short code, e.g. `EUR`. Always upper case. -/
  code : String
  /-- Decimal places: EUR has 2 (cents), JPY has 0, HOURS has 2 (centihours). -/
  exponent : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable, ToJson, FromJson

namespace Commodity

/-- Commodities whose exponent differs from the default of 2. -/
private def knownExponents : List (String × Nat) :=
  [("JPY", 0), ("KRW", 0), ("ISK", 0), ("CLP", 0), ("BHD", 3), ("KWD", 3), ("TND", 3)]

/-- Looks up a commodity by code. Unknown commodities get two decimal places. -/
def ofCode (code : String) : Commodity :=
  let c := code.toUpper
  { code := c, exponent := (knownExponents.lookup c).getD 2 }

/-- The euro. -/
def eur : Commodity := ofCode "EUR"

/-- Hours, tracked to a hundredth. The point of calling this a commodity and not a currency. -/
def hours : Commodity := ofCode "HOURS"

instance : ToString Commodity := ⟨Commodity.code⟩

/-- 10 ^ exponent, the number of minor units in one major unit. -/
def scale (c : Commodity) : Nat := 10 ^ c.exponent

end Commodity

/-- An exact quantity of a commodity, counted in minor units. -/
structure Amount where
  /-- What is being counted. -/
  commodity : Commodity
  /-- How many minor units. Negative means the account is credited. -/
  minor : Int
  deriving DecidableEq, Repr, Inhabited, ToJson, FromJson

namespace Amount

instance : Inhabited Amount := ⟨⟨Commodity.eur, 0⟩⟩

/-- Zero of a given commodity. -/
def zero (c : Commodity) : Amount := ⟨c, 0⟩

/-- Negation. -/
def neg (a : Amount) : Amount := { a with minor := -a.minor }

instance : Neg Amount := ⟨neg⟩

/-- Addition, defined only for matching commodities. -/
def add? (a b : Amount) : Option Amount :=
  if a.commodity = b.commodity then some ⟨a.commodity, a.minor + b.minor⟩ else none

/-- Whether the amount is zero. -/
def isZero (a : Amount) : Bool := a.minor == 0

/-- Renders the numeric part only, e.g. `-49.90`. -/
def digits (a : Amount) : String :=
  let s := a.commodity.scale
  let neg := a.minor < 0
  let n := a.minor.natAbs
  let major := n / s
  let minor := n % s
  let frac :=
    if a.commodity.exponent == 0 then ""
    else "." ++ Str.padLeft (toString minor) a.commodity.exponent '0'
  (if neg then "-" else "") ++ toString major ++ frac

/-- Renders as `-49.90 EUR`. -/
def render (a : Amount) : String := a.digits ++ " " ++ a.commodity.code

instance : ToString Amount := ⟨render⟩

/--
Parses a decimal quantity for a given commodity. Accepts `1234.56`, `1.234,56`,
`-49,90` and `+7`, i.e. both European and Anglo conventions, with optional
thousands separators.
-/
def parseDigits (c : Commodity) (input : String) : Except String Amount := do
  let s := input.trimAscii.replace " " "" |>.replace " " ""
  if s.isEmpty then throw "empty amount"
  let (sign, s) :=
    if s.startsWith "-" then (-1, (s.drop 1).toString)
    else if s.startsWith "+" then (1, (s.drop 1).toString)
    else (1, s)
  -- The last separator present is the decimal point; earlier ones group digits.
  let lastDot := (s.splitOn ".").length - 1
  let lastComma := (s.splitOn ",").length - 1
  let (intPart, fracPart) :=
    if lastComma > 0 && (lastDot == 0 || (s.splitOn ",").getLast!.length ≤ 2) then
      let parts := s.splitOn ","
      (String.intercalate "" (parts.dropLast) |>.replace "." "", parts.getLast!)
    else if lastDot > 0 then
      let parts := s.splitOn "."
      (String.intercalate "" (parts.dropLast) |>.replace "," "", parts.getLast!)
    else
      (s.replace "," "" |>.replace "." "", "")
  let digitsOnly (x : String) : Bool := x.all Char.isDigit
  if !digitsOnly intPart || !digitsOnly fracPart then
    throw s!"not a number: {input}"
  let frac := Str.padRight fracPart c.exponent '0'
  if frac.length > c.exponent then
    throw s!"too many decimal places for {c.code}: {input}"
  let intVal : Nat := (intPart.foldl (fun acc ch => acc * 10 + (ch.toNat - 48)) 0)
  let fracVal : Nat := (frac.foldl (fun acc ch => acc * 10 + (ch.toNat - 48)) 0)
  return ⟨c, sign * (Int.ofNat (intVal * c.scale + fracVal))⟩

/-- Parses `-49.90EUR`, `-49,90 EUR` or `-49.90` (defaulting to `dflt`). -/
def parse (input : String) (dflt : Commodity := Commodity.eur) : Except String Amount := do
  let s := input.trimAscii.toString
  let letters := s.toList.reverse.takeWhile (fun c => c.isAlpha)
  if letters.isEmpty then
    parseDigits dflt s
  else
    let code := String.ofList letters.reverse
    let num := (s.take (s.length - code.length)).toString
    parseDigits (Commodity.ofCode code) num

end Amount

/-! ## Splitting without losing a cent -/

/-- The `i`-th cut point of `total` divided `n` ways. -/
private def cut (total : Int) (n : Nat) (i : Nat) : Int := (total * i) / n

private theorem sum_telescope (f : Nat → Int) :
    ∀ n : Nat, ((List.range n).map (fun i => f (i + 1) - f i)).sum = f n - f 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_telescope f n]
    simp
    omega

/--
Splits `total` into `n` parts that differ by at most one minor unit and sum
back to exactly `total`. This is where cents go missing in other tools: invoice
tax lines and shared-expense splits both route through here.
-/
def splitParts (total : Int) (n : Nat) : List Int :=
  (List.range n).map (fun i => cut total n (i + 1) - cut total n i)

theorem splitParts_length (total : Int) (n : Nat) : (splitParts total n).length = n := by
  simp [splitParts]

theorem splitParts_sum (total : Int) (n : Nat) (hn : n ≠ 0) : (splitParts total n).sum = total := by
  have h := sum_telescope (fun i => cut total n i) n
  simp only [splitParts]
  rw [h]
  have hn' : (n : Int) ≠ 0 := Int.natCast_ne_zero.mpr hn
  simp [cut, Int.mul_ediv_cancel _ hn']

/-- Running totals of a list, starting at zero: `[0, x₀, x₀+x₁, …]`. -/
private def prefixSums (xs : List Int) : List Int :=
  xs.foldl (fun acc x => acc ++ [acc.getLastD 0 + x]) [0]

/--
Splits a total across a grid so that **both** the row sums and the column sums
come out exactly right.

This is the two-dimensional version of `splitParts`, and it exists because a
division has two obligations at once. Each cost must be fully divided — that is
the columns — and each person must receive exactly the share the weights say —
that is the rows. Rounding each cost independently satisfies the first and
drifts on the second; rounding each person's total independently does the
reverse.

Both hold here because every cell is a second difference of one monotone
function of the two running totals, so summing along either axis telescopes down
to that axis's own total. Monotonicity is also why no cell comes out negative,
given non-negative rows and columns.
-/
def biproportional (rows cols : List Int) : List (List Int) :=
  let total := rows.sum
  let rs := prefixSums rows
  let cs := prefixSums cols
  let corner (a b : Int) : Int := if total == 0 then 0 else a * b / total
  (List.range rows.length).map fun i =>
    (List.range cols.length).map fun j =>
      corner rs[i + 1]! cs[j + 1]! - corner rs[i]! cs[j + 1]!
        - corner rs[i + 1]! cs[j]! + corner rs[i]! cs[j]!

/-- Splits an amount into `n` parts that sum back to it exactly. -/
def Amount.splitEvenly (a : Amount) (n : Nat) :
    { xs : List Amount // xs.length = n ∧ (xs.map (·.minor)).sum = a.minor ∨ n = 0 } :=
  if h : n = 0 then ⟨[], Or.inr h⟩
  else
    ⟨(splitParts a.minor n).map (fun m => ⟨a.commodity, m⟩), by
      refine Or.inl ⟨?_, ?_⟩
      · simp [splitParts_length]
      · simp [List.map_map, Function.comp_def, splitParts_sum a.minor n h]⟩

end Resources
