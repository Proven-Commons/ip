/-
  The IP parser. It reads text and returns an address or a prefix,
  or `none` when the text sits outside the grammar.

  IPv4: four decimal parts separated by dots. Each part is one to
  three digits, no leading zero unless the part is exactly "0", and
  below 256. Exactly four parts: a fifth part is rejected, and so
  is a missing one.

  IPv6: eight hex groups separated by colons, with at most one
  `::` compressing a run of one or more zero groups. Each group is
  one to four hex digits in either case. The last group may instead
  be an IPv4 address in dotted decimal, which counts as two groups
  (for example `::ffff:192.0.2.1`). An empty group outside `::`
  is rejected, and so is a second `::`.

  CIDR: an address, a slash, and a prefix length in decimal with
  no leading zero unless it is exactly "0". The length must not
  exceed the address size: 32 for IPv4, 128 for IPv6.

  No DNS lookup anywhere: parsing is purely syntactic.

  Everything is written on `List Char` with plain structural
  recursion, so the parser computes in the kernel and the proofs in
  `Proofs` can decide concrete cases. The `String` entry points
  only convert with `toList`. In particular this file never uses
  `String.splitOn`, which does not reduce in the kernel.

  The parsers are split into a shape step (split the text and match
  on the exact part count) and a validation step, so the proofs in
  `Proofs` can case on the shape. `parseIPv4Parts` and friends
  take already-split parts; `parseIPv4` and friends split first.
-/

import Ip.Addr

namespace Ip

/-- A decimal digit, as a test. -/
def isDigit (c : Char) : Bool :=
  decide ('0' ≤ c ∧ c ≤ '9')

/-- The value of one decimal digit. -/
def digitVal (c : Char) : Nat :=
  c.toNat - 48

/-- A hex digit in either case, as a test. -/
def isHexDigit (c : Char) : Bool :=
  decide (('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F'))

/-- The value of one hex digit, in either case. -/
def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (10 + n - 97)
  else if 65 ≤ n ∧ n ≤ 70 then some (10 + n - 65)
  else none

/-- All characters satisfy a test. -/
def allChars (p : Char → Bool) : List Char → Bool
  | [] => true
  | c :: cs => p c && allChars p cs

/-- Split a character list on a separator character. -/
def splitChar : Char → List Char → List (List Char)
  | _, [] => [[]]
  | sep, c :: cs =>
    if c = sep then [] :: splitChar sep cs
    else match splitChar sep cs with
    | [] => [[c]]
    | g :: gs => (c :: g) :: gs

/-- Split a character list on the two-character sequence `::`. -/
def splitDoubleColon : List Char → List (List Char)
  | [] => [[]]
  | [c] => [[c]]
  | c :: d :: cs =>
    if c = ':' ∧ d = ':' then [] :: splitDoubleColon cs
    else match splitDoubleColon (d :: cs) with
    | [] => [[c]]
    | g :: gs => (c :: g) :: gs

/-- Parse a run of decimal digits to a Nat. Empty or non-digit input fails. -/
def parseDecNat (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ =>
    if allChars isDigit cs then
      some (cs.foldl (fun acc c => acc * 10 + digitVal c) 0)
    else none

/-- A decimal part with no leading zero unless it is exactly "0". -/
def noLeadingZero : List Char → Bool
  | [] => false
  | ['0'] => true
  | c :: _ => c != '0'

/-- Parse one IPv4 octet: digits, no leading zero, below 256. -/
def parseOctet (cs : List Char) : Option Nat :=
  if !noLeadingZero cs then none
  else match parseDecNat cs with
  | some n => if n < 256 then some n else none
  | none => none

/-- Build an IPv4 address from four validated octets. -/
def mkIPv4 (o0 o1 o2 o3 : Nat)
    (h0 : o0 < 256) (h1 : o1 < 256) (h2 : o2 < 256) (h3 : o3 < 256) : IPv4 :=
  ⟨o0, h0, o1, h1, o2, h2, o3, h3⟩

/-- Parse an IPv4 address from four already-split parts. -/
def parseIPv4Parts : List (List Char) → Option IPv4
  | [s0, s1, s2, s3] => do
    let o0 ← parseOctet s0
    let o1 ← parseOctet s1
    let o2 ← parseOctet s2
    let o3 ← parseOctet s3
    if h : o0 < 256 ∧ o1 < 256 ∧ o2 < 256 ∧ o3 < 256 then
      some (mkIPv4 o0 o1 o2 o3 h.1 h.2.1 h.2.2.1 h.2.2.2)
    else none
  | _ => none

/-- Parse an IPv4 address from dotted decimal text. -/
def parseIPv4 (s : String) : Option IPv4 :=
  parseIPv4Parts (splitChar '.' s.toList)

/-- Parse one hex group: one to four hex digits, either case. -/
def parseHexGroup (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ =>
    if cs.length ≤ 4 && allChars isHexDigit cs then
      cs.foldl (fun acc c => do
        let v ← hexVal c
        let n ← acc
        some (n * 16 + v)) (some 0)
    else none

/-- Does this part contain a dot (an IPv4 tail marker)? -/
def hasDot (cs : List Char) : Bool :=
  cs.contains '.'

/-- Parse a list of hex groups; a part containing a dot fails here. -/
def parseHexGroups : List (List Char) → Option (List Nat)
  | [] => some []
  | s :: rest => do
    if hasDot s then none
    else
      let n ← parseHexGroup s
      let tail ← parseHexGroups rest
      some (n :: tail)

/--
  Parse the groups on the final side of an address. The last part
  may be an IPv4 address, which counts as two groups. Any other
  part containing a dot fails.
-/
def parseSideGroups : List (List Char) → Option (List Nat)
  | [] => some []
  | parts =>
    match parts.getLast? with
    | none => some []
    | some last =>
      if hasDot last then do
        -- IPv4 tail: all but the last part are hex groups.
        let init := parts.dropLast
        let hg ← parseHexGroups init
        let v4 ← parseIPv4Parts (splitChar '.' last)
        some (hg ++ [v4.toNat / 65536, v4.toNat % 65536])
      else parseHexGroups parts

/-- Build an IPv6 address from eight validated groups. -/
def mkIPv6 (g0 g1 g2 g3 g4 g5 g6 g7 : Nat)
    (h0 : g0 < 65536) (h1 : g1 < 65536) (h2 : g2 < 65536) (h3 : g3 < 65536)
    (h4 : g4 < 65536) (h5 : g5 < 65536) (h6 : g6 < 65536) (h7 : g7 < 65536) : IPv6 :=
  ⟨g0, h0, g1, h1, g2, h2, g3, h3, g4, h4, g5, h5, g6, h6, g7, h7⟩

/-- Build an IPv6 address from a list of exactly eight groups. -/
def mkIPv6OfList : List Nat → Option IPv6
  | [g0, g1, g2, g3, g4, g5, g6, g7] =>
    if h : g0 < 65536 ∧ g1 < 65536 ∧ g2 < 65536 ∧ g3 < 65536 ∧
       g4 < 65536 ∧ g5 < 65536 ∧ g6 < 65536 ∧ g7 < 65536 then
      some (mkIPv6 g0 g1 g2 g3 g4 g5 g6 g7 h.1 h.2.1 h.2.2.1 h.2.2.2.1
        h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)
    else none
  | _ => none

/-- Parse an IPv6 address from already-split `::` parts. -/
def parseIPv6Parts : List (List Char) → Option IPv6
  | [only] => do
    -- No compression: the groups must total exactly eight.
    let gs ← parseSideGroups (splitChar ':' only)
    if gs.length = 8 then mkIPv6OfList gs else none
  | [left, right] => do
    -- One compression: left + zeros + right = eight groups.
    -- An IPv4 tail may only sit at the very end, so the left side
    -- takes plain hex groups and the right side may carry the tail.
    let lg ← if left = [] then some [] else parseHexGroups (splitChar ':' left)
    let rg ← if right = [] then some [] else parseSideGroups (splitChar ':' right)
    let total := lg.length + rg.length
    if total < 8 then
      mkIPv6OfList (lg ++ List.replicate (8 - total) 0 ++ rg)
    else none
  | _ => none

/-- Parse an IPv6 address from text, with at most one `::`. -/
def parseIPv6 (s : String) : Option IPv6 :=
  parseIPv6Parts (splitDoubleColon s.toList)

/-- Parse an address of either version from characters. IPv4 is tried first. -/
def parseAddrList (cs : List Char) : Option IPAddr :=
  match parseIPv4Parts (splitChar '.' cs) with
  | some a => some (IPAddr.v4 a)
  | none =>
    match parseIPv6Parts (splitDoubleColon cs) with
    | some a => some (IPAddr.v6 a)
    | none => none

/-- Parse an address of either version. IPv4 is tried first. -/
def parseAddr (s : String) : Option IPAddr :=
  parseAddrList s.toList

/-- Parse a prefix length: digits, no leading zero unless exactly "0". -/
def parsePrefixLen (cs : List Char) : Option Nat := do
  if !noLeadingZero cs then none
  else parseDecNat cs

/-- Build a prefix when the length fits the address size, else fail. -/
def mkPrefix (a : IPAddr) (len : Nat) : Option Prefix :=
  if h : len ≤ a.bits then some ⟨a, len, h⟩ else none

/-- Parse a CIDR prefix from already-split slash parts. -/
def parsePrefixParts : List (List Char) → Option Prefix
  | [addrText, lenText] =>
    match parsePrefixLen lenText, parseAddrList addrText with
    | some len, some a => mkPrefix a len
    | _, _ => none
  | _ => none

/-- Parse a CIDR prefix from text: address, slash, length. -/
def parsePrefix (s : String) : Option Prefix :=
  parsePrefixParts (splitChar '/' s.toList)

end Ip
