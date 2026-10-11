#!/usr/bin/env python3
"""W4 boundary domain controls (docs/2026-10-06-w4-w7-transmit-bulk.md,
sections 8 and 16): the mirror alone (`leanux-model --domain`, placeholders)
must place each trace of corpus/w47-controls outside its domain with the
stated reason, so an exclusion beyond the WireGuard boundary is a fail-noisy
`unsupported`, never a prediction. Run from the repository root after
`lake build leanux-model`:
    scripts/in-bundle python3 scripts/wg-w47-controls.py
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODEL = ROOT / ".lake/build/bin/leanux-model"
EXPECTED = {
    "wc_gso_ipv6": "IPv6 UDP GSO: beyond the WireGuard boundary",
    "wc_gso_short_last": "a short last segment",
    "wc_probe_ipv6": "IPV6_PMTUDISC_PROBE: beyond the WireGuard boundary",
}


def main():
    if not MODEL.is_file():
        raise SystemExit(f"{MODEL} is missing: run `lake build leanux-model` first")
    failures = 0
    for name, reason in EXPECTED.items():
        trace = json.loads((ROOT / "corpus/w47-controls" / f"{name}.json").read_text())
        proc = subprocess.run([str(MODEL), "--domain"], input=(json.dumps(trace) + "\n").encode(),
                              capture_output=True, timeout=120)
        rows = [json.loads(line) for line in proc.stdout.decode().splitlines() if line.strip()]
        row = rows[0] if rows else {}
        ok = row.get("in_domain") is False and reason in json.dumps(row)
        print(f"{name}: {'rejected as expected' if ok else 'UNEXPECTED'}: {json.dumps(row)[:200]} "
              f"{proc.stderr.decode()[-200:].strip()}")
        failures += not ok
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
