# Specification: canonical IP address printer

This PR adds the printer half of the `ip` library. The parser half
is a separate PR (issue #1); this PR includes only minimal reference
parsers in `Ip/Parse.lean`, used to state the round-trip theorems.

## What the printer does

Takes a parsed address representation (`IPv4` or `IPv6`, structs of
bounded numbers) and produces its canonical text form as a `String`.

### IPv4: dotted decimal

Four decimal numbers separated by dots. No leading zeros: `5` prints
as `"5"`, never `"05"`; `0` prints as `"0"`. Examples: `127.0.0.1`,
`192.168.1.1`, `255.255.255.255`, `0.0.0.0`.

### IPv6: RFC 5952 canonical form

- Lowercase hex, no leading zeros in any group: `0xa`, never `0x0a`
  or `0X0A`.
- The longest run of two or more consecutive zero groups is
  compressed to `::`. On a tie the first run wins.
- A single zero group is never compressed.
- `::` appears at most once.
- All zeros prints as `::`; loopback prints as `::1`.
- Examples: `2000::1`, `2000:1::1`, `1:2:3:4:5:6:7:8`,
  `ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff`, `fe80::1`.

## Structure

- `Ip/Addr.lean` — `IPv4` (4 bytes, each < 256) and `IPv6`
  (8 groups, each < 65536), with proofs carried in the structs.
- `Ip/Convert.lean` — decimal/hex digit conversions defined from
  first principles (`decDigits`, `hexDigits`, `printDec`, `printHex`,
  `decChar`, `hexChar`, `splitChar`, `joinChar`). Core Lean string
  functions (`toString`, `String.toNat?`, `String.splitOn`) do not
  reduce in a way that supports axiom-pure proofs, so the conversions
  are built here instead of on top of them.
- `Ip/Printer.lean` — `printIPv4`, `printIPv6`, `findZeroRun`,
  `joinWith`.
- `Ip/Parse.lean` — minimal reference parsers (`parseIPv4`,
  `parseIPv6`, `parseDec`, `parseHex`), used only to state round-trip
  theorems. The full parser is issue #1.
- `Ip/Verify.lean` — proofs.
- `Main.lean` — CLI: `ip print4 <b0> <b1> <b2> <b3>`,
  `ip print6 <g0>...<g7>`, `ip batch <file>`.

## What is proved

All proofs in `Ip/Verify.lean`, using only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound` — verified with
`#print axioms`). No `sorry` anywhere.

- `parseDec (printDec n) = some n` — decimal numeric round-trip.
- `parseHex (printHex n) = some n` — hex numeric round-trip.
- `parseIPv4 (printIPv4 a) = some a` — full IPv4 string round-trip:
  printing then parsing returns the original address.
- Supporting lemmas: digit folding (`foldDigits` over `decDigits` /
  `hexDigits` returns the number), character correspondence
  (`decChar`, `hexChar`), digit bounds and first-digit-nonzero,
  and `splitChar` / `joinChar` round-trip (split after join is the
  identity for separator-free parts).

## What is tested, not proved

- `parseIPv6 (printIPv6 a) = some a` — the IPv6 string round-trip
  is covered by differential tests (`tests/run_tests.py`, 20 IPv6
  cases against Python's `ipaddress` module, all passing), not by a
  Lean proof. The `::` compression/expansion reasoning is not yet
  formalized. The numeric hex round-trip underneath it is proved.

## Strictness decisions

- The printer never produces leading zeros, uppercase hex, or a
  second `::`, so its output is always the unique canonical form.
- The reference parsers reject leading zeros (except `"0"` itself)
  and out-of-range values, matching what the printer produces.
- No DNS lookup, no CIDR handling in this PR — those belong to the
  parser PR (issue #1).
