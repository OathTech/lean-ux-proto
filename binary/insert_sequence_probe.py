#!/usr/bin/env python3
"""Run retained-heap insertion sequences after the four function comparisons.

Use sequence_probe.py and insert_probe.py first. This combines their decoded
inputs, retaining the insertion recording as the source-prefix origin.
"""
import argparse
import json
from pathlib import Path
import subprocess
import time

from census import ROOT
from pin import verify_pin
from sequence_probe import merge_inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-input", type=Path, required=True)
    parser.add_argument("--insert-input", type=Path, required=True)
    args = parser.parse_args()
    kraken = verify_pin(ROOT)
    combined = merge_inputs([json.loads(args.base_input.read_text()),
                             json.loads(args.insert_input.read_text())])
    out = ROOT / ".tmp/binary-insert-sequence"
    out.mkdir(parents=True, exist_ok=True)
    path = out / "input.json"
    path.write_text(json.dumps(combined) + "\n")
    started = time.monotonic()
    completed = subprocess.run([str(ROOT / "binary/.lake/build/bin/binary-pair-insert-sequence"), str(path)],
                               cwd=ROOT, text=True, capture_output=True)
    if completed.returncode:
        raise RuntimeError(f"paired insertion sequence failed ({completed.returncode}): {completed.stderr}")
    if completed.stderr:
        raise ValueError(completed.stderr)
    result = json.loads(completed.stdout)
    result.update(kraken=kraken, paired_seconds=round(time.monotonic() - started, 3))
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    calls = [call for case in result["runs"] for call in case["run"]["calls"]]
    print(json.dumps(dict(status=result["status"], sequences=len(result["runs"]), calls=len(calls),
                         instructions=sum(c["instructions"] for c in calls),
                         paired_seconds=result["paired_seconds"]), indent=2))


if __name__ == "__main__":
    main()
