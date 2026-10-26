# Test Results

Run: `python3 tests/run_tests.py .lake/build/bin/ip`

Date: 2026-10-26. Lean 4.35.0, Lake 5.0.0. Oracle: Python `ipaddress`
module (RFC 5952 canonical form for IPv6).

## Differential tests: 32/32 passed

IPv4 (12 cases): loopback, all zeros, broadcast, private /24, /8, /12,
public DNS, sequential, single digits (leading-zero check), mixed widths,
almost all zeros, alternating. All match `ipaddress.IPv4Address`.

IPv6 (20 cases): loopback `::1`, all zeros `::`, leading run, trailing
run, middle run, no zeros, all ones, two runs (longest wins), tie
(first run wins), single zero (never compressed, three positions),
run of 2 vs run of 1, link-local, multicast, documentation range,
mixed hex digits, single hex digit group, leading run of 3, trailing
run of 7. All match `ipaddress.IPv6Address`.

## Lean build

`lake build` succeeds with no errors and no `sorry` in any file.
Verified theorems (see `Ip/Verify.lean`): numeric decimal and hex
round-trips, split/join lemmas, and the full IPv4 string round-trip
`parseIPv4 (printIPv4 a) = some a`.

## What is tested, not proved

The IPv6 string round-trip `parseIPv6 (printIPv6 a) = some a` is
covered by the differential tests above, not by a Lean proof: the
`::` compression/expansion reasoning (finding the longest zero run,
then expanding it back) is not yet formalized. The numeric hex
round-trip underneath it is proved (`parseHex_printHex`).
