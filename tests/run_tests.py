#!/usr/bin/env python3
"""Differential tests for the IP printer against Python's ipaddress module.

Runs the Lean CLI on representative addresses and compares the output
against Python's canonical form (which follows RFC 5952 for IPv6).

Usage: python3 tests/run_tests.py [path-to-ip-binary]
"""

import ipaddress
import subprocess
import sys

# (kind, numeric parts, description)
IPV4_CASES = [
    ([127, 0, 0, 1], "loopback"),
    ([0, 0, 0, 0], "all zeros"),
    ([255, 255, 255, 255], "broadcast"),
    ([192, 168, 1, 1], "private /24"),
    ([10, 0, 0, 1], "private /8"),
    ([172, 16, 0, 1], "private /12"),
    ([8, 8, 8, 8], "public DNS"),
    ([1, 2, 3, 4], "sequential"),
    ([5, 5, 5, 5], "single digits (leading-zero check)"),
    ([100, 200, 50, 25], "mixed widths"),
    ([0, 0, 0, 1], "almost all zeros"),
    ([255, 0, 255, 0], "alternating"),
]

# (kind, numeric groups, description)
IPV6_CASES = [
    ([0, 0, 0, 0, 0, 0, 0, 1], "loopback ::1"),
    ([0, 0, 0, 0, 0, 0, 0, 0], "all zeros ::"),
    ([0x2000, 0, 0, 0, 0, 0, 0, 1], "leading run"),
    ([0x2000, 0, 0, 0, 0, 0, 0, 0], "trailing run"),
    ([0x2000, 1, 0, 0, 0, 0, 0, 1], "middle run"),
    ([1, 2, 3, 4, 5, 6, 7, 8], "no zeros, no compression"),
    ([0xFFFF] * 8, "all ones"),
    ([0x2000, 0, 0, 1, 0, 0, 0, 1], "two runs, longest wins"),
    ([0, 0, 1, 0, 0, 1, 0, 0], "tie: first run wins"),
    ([1, 0, 2, 3, 4, 5, 6, 7], "single zero, never compressed"),
    ([0, 1, 2, 3, 4, 5, 6, 7], "single leading zero"),
    ([1, 2, 3, 4, 5, 6, 7, 0], "single trailing zero"),
    ([0x2000, 0, 1, 0, 0, 1, 0, 1], "run of 2 vs run of 1"),
    ([0xFE80, 0, 0, 0, 0, 0, 0, 1], "link-local"),
    ([0xFF02, 0, 0, 0, 0, 0, 0, 1], "multicast"),
    ([0x2001, 0xDB8, 0, 0, 0, 0, 0, 1], "documentation range"),
    ([0xABCD, 0xEF01, 0x2345, 0x6789, 0xABCD, 0xEF01, 0x2345, 0x6789], "mixed hex digits"),
    ([10, 0, 0, 0, 0, 0, 0, 1], "0xa group (single hex digit)"),
    ([0, 0, 0, 1, 0, 0, 0, 1], "leading run of 3"),
    ([1, 0, 0, 0, 0, 0, 0, 0], "trailing run of 7"),
]


def run_cli(binary, args):
    result = subprocess.run(
        [binary] + args, capture_output=True, text=True, timeout=10
    )
    return result.stdout.strip(), result.returncode


def main():
    binary = sys.argv[1] if len(sys.argv) > 1 else ".lake/build/bin/ip"
    failures = 0
    total = 0

    print("=== IPv4 differential tests ===")
    for parts, desc in IPV4_CASES:
        total += 1
        expected = str(ipaddress.IPv4Address(bytes(parts)))
        out, rc = run_cli(binary, ["print4"] + [str(p) for p in parts])
        status = "OK" if (rc == 0 and out == expected) else "FAIL"
        if status == "FAIL":
            failures += 1
        print(f"[{status}] {desc}: got {out!r}, expected {expected!r}")

    print("\n=== IPv6 differential tests ===")
    for groups, desc in IPV6_CASES:
        total += 1
        expected = str(ipaddress.IPv6Address(sum(g << (112 - 16 * i) for i, g in enumerate(groups))))
        out, rc = run_cli(binary, ["print6"] + [str(g) for g in groups])
        status = "OK" if (rc == 0 and out == expected) else "FAIL"
        if status == "FAIL":
            failures += 1
        print(f"[{status}] {desc}: got {out!r}, expected {expected!r}")

    print(f"\n{total - failures}/{total} passed, {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
