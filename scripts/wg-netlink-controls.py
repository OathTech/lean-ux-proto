#!/usr/bin/env python3
"""Netlink endpoint-layout controls (docs/2026-10-13-audit-netlink.md, F1):
`set_peer` (netlink.c:441-446) reads a WGPEER_A_ENDPOINT's bytes as a
`sockaddr_in` or a `sockaddr_in6` by `len` and `sa_family` alone, so a
trace whose `af` and `len` present one family's bytes under the other
layout would be stored by the kernel as something the mirror's parsed
fields cannot express. The validator refuses those two combinations;
every trace of corpus/netlink-controls must be rejected with the stated
reason, never admitted. Run from the repository root:
    scripts/in-bundle python3 scripts/wg-netlink-controls.py
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness.trace import InvalidTrace, validate_trace   # noqa: E402

EXPECTED = {
    # family-4 bytes (sin_family, sin_port, sin_addr, zeros) with af 10 and len 28:
    # the kernel reads a sockaddr_in6 ([::]:port, flowinfo = the v4 address)
    "n1_endpoint_v4_bytes_as_v6": "af 10 with len 28 presents family-4 bytes under the sockaddr_in6 layout",
    # family-6 bytes (sin6_family, sin6_port, sin6_flowinfo, ...) with af 2 and len 16:
    # the kernel reads a sockaddr_in (sin_addr = the flowinfo bytes)
    "n1_endpoint_v6_bytes_as_v4": "af 2 with len 16 presents family-6 bytes under the sockaddr_in layout",
}


MODEL = ROOT / ".lake/build/bin/leanux-model"
# Pre-release review finding 6 (docs/2026-10-14-pre-release-review.md, section
# 6): the guest refuses wg_delete while a stepped dump is pending (guest.c,
# "wg_delete_with_dump_pending"), and the mirror's dump cursor does not carry
# the device reference the kernel's does, so the mirror alone
# (`leanux-model --domain`) must place the composition outside its domain
# with the stated reason, never accept it (the campaign's stale-cursor
# witness was such an accepted replay).
DOMAIN_EXPECTED = {
    "n6_delete_with_dump_pending": "a delete with a stepped dump pending",
}


def domain_check(name, reason):
    if not MODEL.is_file():
        raise SystemExit(f"{MODEL} is missing: run `lake build leanux-model` first")
    trace = json.loads((ROOT / "corpus/netlink-controls" / f"{name}.json").read_text())
    import subprocess
    proc = subprocess.run([str(MODEL), "--domain"], input=(json.dumps(trace) + "\n").encode(),
                          capture_output=True, timeout=120)
    rows = [json.loads(line) for line in proc.stdout.decode().splitlines() if line.strip()]
    row = rows[0] if rows else {}
    ok = row.get("in_domain") is False and reason in json.dumps(row)
    print(f"{name}: {'outside the domain as expected' if ok else 'UNEXPECTED'}: {json.dumps(row)[:200]} "
          f"{proc.stderr.decode()[-200:].strip()}")
    return ok


def main():
    failures = 0
    for name, reason in DOMAIN_EXPECTED.items():
        failures += not domain_check(name, reason)
    for name, reason in EXPECTED.items():
        trace = json.loads((ROOT / "corpus/netlink-controls" / f"{name}.json").read_text())
        try:
            validate_trace(trace)
            print(f"{name}: UNEXPECTED: admitted by the validator")
            failures += 1
        except InvalidTrace as exc:
            ok = reason in str(exc)
            print(f"{name}: {'rejected as expected' if ok else 'UNEXPECTED reason'}: {exc}")
            failures += not ok
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
