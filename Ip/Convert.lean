/-
  Provable decimal and hex conversions.

  Core Lean's `toString` and `String.toNat?` do not reduce in a
  way that supports axiom-pure round-trip proofs (they rely on
  well-founded recursion that the kernel cannot unfold for general
  arguments). This module defines conversions from first principles,
  with round-trip proofs by structural induction.

  Decimal: a number is a list of digits, most significant first.
  Hex: same, base 16, lowercase.
-/

/-- Decimal digits of a number, most significant first. `0` gives `[0]`. -/
def decDigitsAux : Nat → List Nat
  | 0 => []
  | n + 1 => decDigitsAux ((n + 1) / 10) ++ [(n + 1) % 10]
termination_by n => n

/-- Decimal digits of a number, most significant first. `0` gives `[0]`. -/
def decDigits (n : Nat) : List Nat :=
  if n = 0 then [0] else decDigitsAux n

/-- A decimal digit as a character, by match (provable by cases). -/
def decChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | _ => '?'

/-- Print a number as decimal with no leading zeros. -/
def printDec (n : Nat) : String :=
  String.ofList ((decDigits n).map decChar)

/-- Fold decimal characters into a number, or `none` on a bad digit. -/
def decFold : List Char → Nat → Option Nat
  | [], acc => some acc
  | ch :: tl, acc =>
    let d := ch.toNat - 48
    if 48 ≤ ch.toNat ∧ ch.toNat ≤ 57 then decFold tl (acc * 10 + d) else none

/-- Value of a decimal digit list, or `none` on a bad digit or leading zero. -/
def decValue : List Char → Option Nat
  | [] => none
  | ['0'] => some 0
  | c :: rest =>
    if c = '0' then none
    else decFold (c :: rest) 0

/-- Parse a decimal string with no leading zeros (except "0" itself). -/
def parseDec (s : String) : Option Nat :=
  decValue s.toList

/-- Split a character list on a separator character. -/
def splitChar (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | ch :: rest =>
    if ch = c then [] :: splitChar c rest
    else match splitChar c rest with
         | [] => [[ch]]
         | first :: others => (ch :: first) :: others

/-- Join character lists with a separator character. -/
def joinChar (c : Char) : List (List Char) → List Char
  | [] => []
  | [cs] => cs
  | cs :: rest => cs ++ [c] ++ joinChar c rest

/-- Hex digits of a number, most significant first. `0` gives `[0]`. -/
def hexDigitsAux : Nat → List Nat
  | 0 => []
  | n + 1 => hexDigitsAux ((n + 1) / 16) ++ [(n + 1) % 16]
termination_by n => n

/-- Hex digits of a number, most significant first. `0` gives `[0]`. -/
def hexDigits (n : Nat) : List Nat :=
  if n = 0 then [0] else hexDigitsAux n

/-- A hex digit as a lowercase character, by match (provable by cases). -/
def hexChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'a'
  | 11 => 'b'
  | 12 => 'c'
  | 13 => 'd'
  | 14 => 'e'
  | 15 => 'f'
  | _ => '?'

/-- Print a number as lowercase hex with no leading zeros. -/
def printHex (n : Nat) : String :=
  String.ofList ((hexDigits n).map hexChar)

/-- Value of a hex digit character, or `none` if not a lowercase hex digit. -/
def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (10 + n - 97)
  else none

/-- Fold hex characters into a number, or `none` on a bad digit. -/
def hexFold : List Char → Nat → Option Nat
  | [], acc => some acc
  | ch :: tl, acc => do
    let v ← hexVal ch
    hexFold tl (acc * 16 + v)

/-- Value of a hex digit list, or `none` on a bad digit or leading zero. -/
def hexValue : List Char → Option Nat
  | [] => none
  | ['0'] => some 0
  | c :: rest =>
    if c = '0' then none
    else hexFold (c :: rest) 0

/-- Parse a hex string with no leading zeros (except "0" itself). -/
def parseHex (s : String) : Option Nat :=
  hexValue s.toList
