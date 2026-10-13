#!/usr/bin/env python3
"""W9 re-entry domain control (docs/2026-10-06-w8-w9-netns-routing.md, section
2.6, W9.5): the mirror alone (`leanux-model --domain`) must place each trace
of corpus/w9-controls outside its domain with the stated reason, so a datagram
routed back into wg0 is a fail-noisy `unsupported` until W9-R models the
nested wg_xmit, never a silent delivery. Run from the repository root after
`lake build leanux-model`:
    scripts/in-bundle python3 scripts/wg-w9-controls.py
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODEL = ROOT / ".lake/build/bin/leanux-model"
EXPECTED = {
    # the endpoint 192.0.2.1 routes into wg0 once the up's routes exist: the
    # transmission's initiation re-enters wg_xmit, which finds no peer
    "w9_reentry_no_peer": "a datagram routed back into wg0",
}


def main():
    if not MODEL.is_file():
        raise SystemExit(f"{MODEL} is missing: run `lake build leanux-model` first")
    failures = 0
    for name, reason in EXPECTED.items():
        trace = json.loads((ROOT / "corpus/w9-controls" / f"{name}.json").read_text())
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
