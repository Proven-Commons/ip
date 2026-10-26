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
