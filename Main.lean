/-
  Command line front end for the IP printer first slice.

    ip print4 <b0> <b1> <b2> <b3>
      Print the IPv4 address in dotted decimal, or `error`.

    ip print6 <g0> ... <g7>
      Print the IPv6 address in RFC 5952 canonical form, or `error`.
      Groups are decimal numbers below 65536.

    ip batch <file>
      Read one command per line, print one result per line.
      Used by the differential test harness.
-/

import Ip

def parseNat (s : String) : Option Nat := s.toNat?

def runPrint4 (args : List String) : String :=
  match args with
  | [s0, s1, s2, s3] =>
    match parseNat s0, parseNat s1, parseNat s2, parseNat s3 with
    | some b0, some b1, some b2, some b3 =>
      if h : b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 then
        printIPv4 ⟨b0, h.1, b1, h.2.1, b2, h.2.2.1, b3, h.2.2.2⟩
      else "error"
    | _, _, _, _ => "error"
  | _ => "error"

def runPrint6 (args : List String) : String :=
  match args with
  | [s0, s1, s2, s3, s4, s5, s6, s7] =>
    match parseNat s0, parseNat s1, parseNat s2, parseNat s3,
          parseNat s4, parseNat s5, parseNat s6, parseNat s7 with
    | some g0, some g1, some g2, some g3,
      some g4, some g5, some g6, some g7 =>
      if h : g0 < 65536 ∧ g1 < 65536 ∧ g2 < 65536 ∧ g3 < 65536 ∧
             g4 < 65536 ∧ g5 < 65536 ∧ g6 < 65536 ∧ g7 < 65536 then
        printIPv6 ⟨g0, h.1, g1, h.2.1, g2, h.2.2.1, g3, h.2.2.2.1,
                    g4, h.2.2.2.2.1, g5, h.2.2.2.2.2.1, g6, h.2.2.2.2.2.2.1, g7, h.2.2.2.2.2.2.2⟩
      else "error"
    | _, _, _, _, _, _, _, _ => "error"
  | _ => "error"

def runToks (toks : List String) : String :=
  match toks with
  | "print4" :: args => runPrint4 args
  | "print6" :: args => runPrint6 args
  | _ => "error"

def runBatch (file : String) : IO UInt32 := do
  let content ← IO.FS.readFile file
  for line in content.splitOn "\n" do
    let toks := (line.splitOn " ").filter (fun t => t ≠ "" ∧ t ≠ "\r")
    if !toks.isEmpty then IO.println (runToks toks)
  return 0

def usage : IO UInt32 := do
  IO.eprintln "usage: ip print4 <b0> <b1> <b2> <b3>"
  IO.eprintln "       ip print6 <g0> <g1> <g2> <g3> <g4> <g5> <g6> <g7>"
  IO.eprintln "       ip batch <file>"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "print4" :: rest =>
    let out := runPrint4 rest
    IO.println out
    return (if out = "error" then 1 else 0)
  | "print6" :: rest =>
    let out := runPrint6 rest
    IO.println out
    return (if out = "error" then 1 else 0)
  | ["batch", file] => runBatch file
  | _ => usage
