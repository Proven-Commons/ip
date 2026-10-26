/-
  Canonical printers for IP addresses.

  IPv4: dotted decimal, no leading zeros. `printDec` produces no
  leading zeros by construction.

  IPv6: RFC 5952 canonical form.
    - Lowercase hex, no leading zeros in any group.
    - The longest run of consecutive zero groups, if it has length
      two or more, is compressed to `::`. On a tie the first run wins.
    - A single zero group is never compressed.
    - `::` appears at most once.
    - The all-zeros address prints as `::`, loopback as `::1`.
-/

import Ip.Addr
import Ip.Convert

/-- Print an IPv4 address as dotted decimal. -/
def printIPv4 (a : IPv4) : String :=
  printDec a.b0 ++ "." ++ printDec a.b1 ++ "." ++ printDec a.b2 ++ "." ++ printDec a.b3

/--
  Find the longest run of zeros in a list, with length at least 2.
  Returns `(start, length)` of the first longest run, or `none`.
-/
def findZeroRun (groups : List Nat) : Option (Nat × Nat) :=
  let rec scan (gs : List Nat) (idx : Nat) (curStart curLen : Nat)
      (best : Option (Nat × Nat)) : Option (Nat × Nat) :=
    match gs with
    | [] =>
      -- End: flush the current run if it beats the best.
      match best with
      | none => if 2 ≤ curLen then some (curStart, curLen) else none
      | some (_, blen) => if blen < curLen then some (curStart, curLen) else best
    | g :: rest =>
      if g = 0 then
        let (ns, nl) := if curLen = 0 then (idx, 1) else (curStart, curLen + 1)
        scan rest (idx + 1) ns nl best
      else
        -- End of a run: record it if it beats the best, then reset.
        let best' := match best with
          | none => if 2 ≤ curLen then some (curStart, curLen) else none
          | some (_, blen) => if blen < curLen then some (curStart, curLen) else best
        scan rest (idx + 1) idx 0 best'
  scan groups 0 0 0 none

/-- Join a list of strings with a separator. -/
def joinWith (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ joinWith sep rest

/-- Print an IPv6 address in RFC 5952 canonical form. -/
def printIPv6 (a : IPv6) : String :=
  let groups := a.groups
  match findZeroRun groups with
  | none => joinWith ":" (groups.map printHex)
  | some (start, len) =>
    let before := (groups.take start).map printHex
    let after := (groups.drop (start + len)).map printHex
    let b := joinWith ":" before
    let af := joinWith ":" after
    match before.isEmpty, after.isEmpty with
    | true, true => "::"
    | true, false => "::" ++ af
    | false, true => b ++ "::"
    | false, false => b ++ "::" ++ af
