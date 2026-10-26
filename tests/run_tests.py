#!/usr/bin/env python3
"""Combined tests for the Lean IP parser and printer.

Parser suite: fixed cases plus a differential run against Python's
`ipaddress` module, seed 20261026, run through the single-file
parser mode (`ip <file>`).
Printer suite: 32 differential cases against Python's `ipaddress`
module, run through `ip print4` / `ip print6`.
Both suites run, and this script writes tests/TEST-RESULTS.md
summarising both. Exit code is 1 if either suite fails.
"""

import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EXE = os.path.join(ROOT, ".lake", "build", "bin", "ip")

CASES = [
    # IPv4 acceptance
    ("parse4 0.0.0.0", "ok"),
    ("parse4 255.255.255.255", "ok"),
    ("parse4 192.168.0.1", "ok"),
    ("parse4 127.0.0.1", "ok"),
    ("parse4 10.0.0.0", "ok"),
    # IPv4 rejection
    ("parse4 1.2.3.4.5", "none"),
    ("parse4 1.2.3", "none"),
    ("parse4 256.0.0.1", "none"),
    ("parse4 01.2.3.4", "none"),
    ("parse4 1.2.3.", "none"),
    ("parse4 .1.2.3", "none"),
    ("parse4 1..2.3", "none"),
    ("parse4 1.2.3.4 ", "error"),
    ("parse4 abc", "none"),
    ("parse4 ", "none"),
    # IPv6 acceptance
    ("parse6 ::", "ok"),
    ("parse6 ::1", "ok"),
    ("parse6 1::", "ok"),
    ("parse6 2001:db8::1", "ok"),
    ("parse6 2001:0db8:85a3:0000:0000:8a2e:0370:7334", "ok"),
    ("parse6 2001:DB8::1", "ok"),
    ("parse6 fe80::1", "ok"),
    ("parse6 ::ffff:192.0.2.1", "ok"),
    ("parse6 2001:db8:0:0:0:0:2:1", "ok"),
    ("parse6 ffff:ffff:ffff:ffff:ffff:ffff:ffff:ffff", "ok"),
    # IPv6 rejection
    ("parse6 1::2::3", "none"),
    ("parse6 1:2:3:4:5:6:7:8:9", "none"),
    ("parse6 1:2:3:4:5:6:7", "none"),
    ("parse6 gggg::1", "none"),
    ("parse6 12345::1", "none"),
    ("parse6 1:2:3:4:5:6:7:", "none"),
    ("parse6 :1:2:3:4:5:6:7", "none"),
    ("parse6 1.2.3.4::5", "none"),
    ("parse6 1:2:3:4:5:6:7:8::", "none"),
    ("parse6 :::", "none"),
    ("parse6 :", "none"),
    ("parse6 ::ffff:192.0.2.256", "none"),
    ("parse6 ::ffff:192.0.2", "none"),
    # CIDR acceptance
    ("prefix 10.0.0.0/8", "ok"),
    ("prefix 0.0.0.0/0", "ok"),
    ("prefix 255.255.255.255/32", "ok"),
    ("prefix 2001:db8::/32", "ok"),
    ("prefix ::/0", "ok"),
    ("prefix ::1/128", "ok"),
    ("prefix ::ffff:192.0.2.0/120", "ok"),
    # CIDR rejection
    ("prefix 1.2.3.4/33", "none"),
    ("prefix 2001:db8::1/129", "none"),
    ("prefix 1.2.3.4/", "none"),
    ("prefix 1.2.3.4/24/5", "none"),
    ("prefix 1.2.3.4/-1", "none"),
    ("prefix 1.2.3.4/024", "none"),
    ("prefix 1.2.3.4/abc", "none"),
    ("prefix 1.2.3.4.5/24", "none"),
    ("prefix /24", "none"),
    # malformed requests
    ("parse 1.2.3.4", "error"),
    ("parse4", "error"),
    ("parse4 1.2.3.4 extra", "error"),
]


def run_fixed_cases():
    req_path = os.path.join(HERE, "requests.txt")
    with open(req_path, "w") as f:
        for req, _ in CASES:
            f.write(req + "\n")
    out = subprocess.run([EXE, req_path], capture_output=True, text=True)
    if out.returncode != 0:
        return [f"executable failed: {out.stderr}"]
    got = out.stdout.strip().split("\n")
    errors = []
    if len(got) != len(CASES):
        errors.append(f"expected {len(CASES)} answers, got {len(got)}")
    for (req, want), answer in zip(CASES, got):
        if answer != want:
            errors.append(f"{req}: expected {want}, got {answer}")
    return errors


def run_differential(seed=20261026):
    import ipaddress

    rng = random.Random(seed)
    reqs = []
    wants = []

    def expect(req, want):
        reqs.append(req)
        wants.append(want)

    # Valid addresses from Python, must be accepted by Lean.
    for _ in range(200):
        if rng.random() < 0.5:
            addr = ".".join(str(rng.randrange(256)) for _ in range(4))
            expect(f"parse4 {addr}", "ok")
            expect(f"prefix {addr}/{rng.randrange(33)}", "ok")
        else:
            groups = [rng.randrange(65536) for _ in range(8)]
            addr = ipaddress.IPv6Address(int.from_bytes(
                b"".join(g.to_bytes(2, "big") for g in groups), "big"))
            expect(f"parse6 {addr.compressed}", "ok")
            expect(f"parse6 {addr.exploded}", "ok")
            expect(f"prefix {addr.compressed}/{rng.randrange(129)}", "ok")

    # Mutations: flip one character; both sides must agree.
    base = ["192.168.0.1", "10.0.0.0/8", "2001:db8::1",
            "2001:db8::/32", "::1", "::ffff:192.0.2.1"]
    chars = "0123456789abcdefABCDEF.:/%x"
    for _ in range(200):
        s = rng.choice(base)
        i = rng.randrange(len(s))
        t = s[:i] + rng.choice(chars) + s[i + 1:]
        op = "prefix" if "/" in t else ("parse6" if ":" in t else "parse4")
        try:
            if op == "parse4":
                ipaddress.IPv4Address(t)
                want = "ok"
            elif op == "parse6":
                ipaddress.IPv6Address(t)
                want = "ok"
            else:
                ipaddress.ip_network(t, strict=False)
                want = "ok"
        except ValueError:
            want = "none"
        # Named differences: Lean rejects leading-zero octets and
        # zone IDs outright; skip those so the oracle stays honest.
        if "%" in t:
            continue
        expect(f"{op} {t}", want)

    req_path = os.path.join(HERE, "diff-requests.txt")
    with open(req_path, "w") as f:
        for req in reqs:
            f.write(req + "\n")
    out = subprocess.run([EXE, req_path], capture_output=True, text=True)
    if out.returncode != 0:
        return [f"differential run failed: {out.stderr}"]
    got = out.stdout.strip().split("\n")
    errors = []
    if len(got) != len(reqs):
        errors.append(f"differential: expected {len(reqs)} answers, got {len(got)}")
    for req, want, answer in zip(reqs, wants, got):
        if answer != want:
            errors.append(f"differential {req}: expected {want}, got {answer}")
    return errors



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



def run_printer_tests():
    binary = EXE
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
    print(f"\n{total - failures}/{total} printer cases passed, {failures} failed")
    return failures, total


def main():
    parser_errors = run_fixed_cases()
    parser_errors += run_differential()
    printer_failures, printer_total = run_printer_tests()
    results_path = os.path.join(HERE, "TEST-RESULTS.md")
    with open(results_path, "w") as f:
        f.write("# Test results\n\n")
        f.write("## Parser\n\n")
        if parser_errors:
            f.write(f"{len(parser_errors)} failures:\n\n")
            for e in parser_errors:
                f.write(f"- {e}\n")
        else:
            f.write(f"All {len(CASES)} fixed cases and the differential run (seed 20261026) pass.\n")
        f.write("\n## Printer\n\n")
        f.write(f"{printer_total - printer_failures}/{printer_total} differential cases pass, {printer_failures} failed.\n")
    if parser_errors:
        for e in parser_errors[:20]:
            print("FAIL:", e, file=sys.stderr)
    if parser_errors or printer_failures:
        return 1
    print("All tests pass.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
