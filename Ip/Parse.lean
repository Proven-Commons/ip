/-
  Minimal reference parsers, used only to state and prove the
  printer round trip. The full parser is a separate PR (issue #1);
  this file exists so `Verify` can state `parse (print a) = a`.

  IPv4: four decimal numbers separated by dots, each below 256,
  no leading zeros (the printer never produces them).

  IPv6: eight hex groups separated by colons, with at most one
  `::` compressing a run of two or more zero groups. Groups are
  lowercase hex with no leading zeros, as the printer produces.
-/

import Ip.Addr
import Ip.Convert

/-- Split a string on a character, via the provable `splitChar`. -/
def splitOn (c : Char) (s : String) : List String :=
  (splitChar c s.toList).map String.ofList

/-- Parse an IPv4 address from dotted decimal. -/
def parseIPv4 (s : String) : Option IPv4 := do
  let parts := splitOn '.' s
  match parts with
  | [s0, s1, s2, s3] =>
    let b0 ← parseDec s0
    let b1 ← parseDec s1
    let b2 ← parseDec s2
    let b3 ← parseDec s3
    if h : b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 then
      some ⟨b0, h.1, b1, h.2.1, b2, h.2.2.1, b3, h.2.2.2⟩
    else none
  | _ => none

/-- Parse a list of hex groups, each below 65536. -/
def parseHexGroups : List String → Option (List Nat)
  | [] => some []
  | s :: rest => do
    let n ← parseHex s
    if n < 65536 then
      let tail ← parseHexGroups rest
      some (n :: tail)
    else none

/--
  Parse an IPv6 address. Handles at most one `::`.
  Returns the eight groups, or `none`.
-/
def parseIPv6Groups (s : String) : Option (List Nat) := do
  -- Split on "::" first: at most one occurrence allowed.
  let dblParts := s.splitOn "::"
  match dblParts with
  | [only] =>
    -- No compression: exactly eight groups.
    let gs ← parseHexGroups (splitOn ':' only)
    if gs.length = 8 then some gs else none
  | [left, right] =>
    -- One compression: left + zeros + right = 8 groups.
    let lg ← if left = "" then some [] else parseHexGroups (splitOn ':' left)
    let rg ← if right = "" then some [] else parseHexGroups (splitOn ':' right)
    let total := lg.length + rg.length
    if total < 8 then
      some (lg ++ List.replicate (8 - total) 0 ++ rg)
    else none
  | _ => none

/-- Parse an IPv6 address from canonical text. -/
def parseIPv6 (s : String) : Option IPv6 := do
  let gs ← parseIPv6Groups s
  match gs with
  | [g0, g1, g2, g3, g4, g5, g6, g7] =>
    if h : g0 < 65536 ∧ g1 < 65536 ∧ g2 < 65536 ∧ g3 < 65536 ∧
       g4 < 65536 ∧ g5 < 65536 ∧ g6 < 65536 ∧ g7 < 65536 then
      some ⟨g0, h.1, g1, h.2.1, g2, h.2.2.1, g3, h.2.2.2.1,
            g4, h.2.2.2.2.1, g5, h.2.2.2.2.2.1, g6, h.2.2.2.2.2.2.1, g7, h.2.2.2.2.2.2.2⟩
    else none
  | _ => none
