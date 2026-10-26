# Specification: ip

A Lean parser for IP addresses and CIDR prefixes, following the
address formats of RFC 791 (IPv4), RFC 4291 (IPv6), and RFC 4632
(CIDR). A reviewer who did not write this specification approves
it, together with any statement file a reviewer adds later. No such
file exists yet, so nothing here counts toward the verified bar yet.

Text is `String`. The parser never does a DNS lookup: parsing is
purely syntactic.

## Addresses

One address type per version:

- `IPv4`: four bytes, each below 256, carried with bound proofs.
  Its numeric value is big-endian: `b0 * 2^24 + b1 * 2^16 +
  b2 * 2^8 + b3`, below 2^32.
- `IPv6`: eight groups, each below 65536, carried with bound
  proofs. Its numeric value is big-endian over the eight groups,
  below 2^128.
- `IPAddr`: either version. `bits` is 32 for IPv4, 128 for IPv6.
- `Prefix`: an address plus a length, with a proof that the length
  does not exceed the address size.

## IPv4 parsing

Four decimal parts separated by dots:

- Each part is one to three digits, no leading zero unless the
  part is exactly "0", and below 256.
- Exactly four parts: a fifth part is rejected, and so is a
  missing one. An empty part is rejected.

## IPv6 parsing

Eight hex groups separated by colons, with at most one `::`:

- Each group is one to four hex digits in either case.
- `::` compresses a run of one or more zero groups. It may appear
  at most once, and it must compress at least one group: the
  groups on both sides total fewer than eight.
- The last group may instead be an IPv4 address in dotted decimal,
  which counts as two groups (for example `::ffff:192.0.2.1`).
  An IPv4 part anywhere else is rejected.
- An empty group outside `::` is rejected. A group over four
  digits is rejected.

## CIDR parsing

An address, a slash, and a prefix length:

- The length is decimal digits with no leading zero unless it is
  exactly "0".
- The length must not exceed the address size: 32 for IPv4, 128
  for IPv6. A length past the size is rejected, and so is a
  missing or malformed length or a second slash.

## Membership

An address is inside a prefix exactly when its top `len` bits
match the prefix address's top `len` bits. The implementation
compares the values shifted right by the host-bit count, and only
ever matches addresses of the same version. Membership is
preserved when a prefix widens: matching on more bits implies
matching on fewer.

## Proved claims

- Every IPv4 value is below 2^32; every IPv6 value below 2^128.
- A parsed octet is below 256.
- A successful IPv4 parse consumes exactly four dot-separated
  parts.
- A successful prefix parse respects the address size.
- Membership is equality of the shifted values for same-version
  addresses, false across versions, and preserved under widening.
- Parsing is deterministic: it is a function, so the same input
  gives the same result.
- A battery of concrete acceptance and rejection cases, decided
  by computation: extra parts, out-of-range octets, leading
  zeros, double compression, bad hex, over-long groups, empty
  groups, misplaced IPv4 tails, and over-long or malformed
  prefix lengths.

## Printer

The printer half of the `ip` library. `Ip/Parse.lean` now holds
both the full parser (namespace `Ip`) and the minimal reference
parsers (root level) used only to state the printer round-trip
theorems in `Ip/Verify.lean`. The reference parsers do not replace
the full parser.

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
