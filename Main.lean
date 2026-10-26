/-
  Command line front end for the IP parser first slice, used by the
  tests. Reads one request per line and prints one answer per line.

  A request is an operation and its input:

    parse4 192.168.0.1      prints  ok
    parse4 1.2.3.4.5        prints  none
    parse6 2001:db8::1      prints  ok
    parse6 1::2::3          prints  none
    prefix 10.0.0.0/8       prints  ok
    prefix 10.0.0.0/33      prints  none

  The answer is `ok` when the text parses and `none` when it is
  rejected. A malformed request prints `error`. A line may end in
  LF or CR LF; nothing else around a request is ignored.

  The parsing here calls `Ip.parseIPv4`, `Ip.parseIPv6`, and
  `Ip.parsePrefix` directly. The line handling is covered by the
  tests, not by a proof.
-/

import Ip

def runRequest (line : String) : String :=
  match line.splitOn " " with
  | ["parse4", s] => if (Ip.parseIPv4 s).isSome then "ok" else "none"
  | ["parse6", s] => if (Ip.parseIPv6 s).isSome then "ok" else "none"
  | ["prefix", s] => if (Ip.parsePrefix s).isSome then "ok" else "none"
  | _ => "error"

def stripCR (line : String) : String :=
  if line.endsWith "\r" then (line.take (line.length - 1)).toString else line

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] => do
    let content ← IO.FS.readFile file
    let mut out := ""
    for line in content.splitOn "\n" do
      let line := stripCR line
      if line = "" then continue
      out := out ++ runRequest line ++ "\n"
    IO.print out
    pure 0
  | _ => do
    IO.eprintln "usage: ip <file>"
    pure 1
