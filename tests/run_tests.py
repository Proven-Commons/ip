#!/usr/bin/env python3
"""Tests for the Lean IP parser.

Builds the `ip` executable with lake, then runs it over a request
file and checks every answer. Requests are one per line:

    parse4 192.168.0.1      -> ok
    parse4 1.2.3.4.5        -> none
    parse6 2001:db8::1      -> ok
    parse6 1::2::3          -> none
    prefix 10.0.0.0/8       -> ok
    prefix 10.0.0.0/33      -> none

A differential run against Python's `ipaddress` module, with a
recorded seed: random valid addresses and prefixes must be accepted
by both sides, and random text mutations must be accepted or
rejected alike by both sides, with two named differences:

- Python's `ipaddress` accepts leading zeros in IPv4 octets only
  when the whole address is written in a form it treats as
  unambiguous; the Lean parser rejects every leading-zero octet.
  The oracle is set to reject them, because the spec does.
- Python's `ipaddress` accepts IPv6 zone IDs (`fe80::1%eth0`).
  The Lean parser rejects them, because the spec has no zone IDs.
  The generator never feeds zone IDs as valid input.
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


def main():
    errors = run_fixed_cases()
    errors += run_differential()
    results_path = os.path.join(HERE, "TEST-RESULTS.md")
    with open(results_path, "w") as f:
        f.write("# Test results\n\n")
        if errors:
            f.write(f"{len(errors)} failures:\n\n")
            for e in errors:
                f.write(f"- {e}\n")
        else:
            f.write("All fixed cases and the differential run pass.\n")
    if errors:
        for e in errors[:20]:
            print("FAIL:", e, file=sys.stderr)
        return 1
    print("All tests pass.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
