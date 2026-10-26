# ip

Lean IP address parser and canonical printer.

This PR adds the **printer**: canonical text forms for IPv4 and IPv6
addresses, with round-trip proofs. The parser is a separate PR
(issue #1).

## What is in it

- **IPv4 printer**: dotted decimal, no leading zeros
  (`127.0.0.1`, `192.168.1.1`).
- **IPv6 printer**: RFC 5952 canonical form — lowercase hex, longest
  zero run of two or more compressed to `::`, single zero never
  compressed, `::` at most once (`::1`, `::`, `2000::1`, `fe80::1`).
- **CLI**: `ip print4 <b0> <b1> <b2> <b3>`,
  `ip print6 <g0>...<g7>`, `ip batch <file>`.
- **Reference parsers** (`Ip/Parse.lean`): minimal, used only to state
  the round-trip theorems. The full parser is issue #1.

## What is proved

In `Ip/Verify.lean`, using only the standard axioms, no `sorry`:

- `parseDec (printDec n) = some n` and `parseHex (printHex n) = some n`
  (numeric round-trips).
- `parseIPv4 (printIPv4 a) = some a` (full IPv4 string round-trip).

## What is tested, not proved

- `parseIPv6 (printIPv6 a) = some a`: covered by differential tests
  (`tests/run_tests.py`, 32 cases against Python's `ipaddress`
  module, all passing), not by a Lean proof. The `::`
  compression/expansion reasoning is not yet formalized; the numeric
  hex round-trip underneath it is proved.

## Build and test

Requires Lean 4.35.0 (via elan) and Lake 5.0.0.

```
lake build
python3 tests/run_tests.py .lake/build/bin/ip
```

See `SPEC.md` for the full specification and `tests/TEST-RESULTS.md`
for test results.

## Layout

- `Ip.lean` — library root (imports all modules).
- `Ip/Addr.lean` — address structs.
- `Ip/Convert.lean` — decimal/hex conversions, split/join.
- `Ip/Printer.lean` — canonical printers.
- `Ip/Parse.lean` — reference parsers for round-trip statements.
- `Ip/Verify.lean` — proofs.
- `Main.lean` — CLI.
- `tests/run_tests.py` — differential tests vs Python `ipaddress`.
