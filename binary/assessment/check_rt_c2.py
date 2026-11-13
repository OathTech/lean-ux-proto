#!/usr/bin/env python3
"""Check RtC2Statement.Kept's exact preempt-count equation on captured visits.

Input is visits.jsonl from the archived rt_c2_capture.py. This checks one
conjunct, not the whole theorem or its memory frame. Unlike RtC2Captured.lean,
it does not accept a cleared need-resched bit as an alternative result.
"""
import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("visits", type=Path)
    args = parser.parse_args()
    failures = []
    visits = 0
    for line in args.visits.read_text().splitlines():
        row = json.loads(line)
        words = [bytes.fromhex(row[side]["preempt"]) for side in ("entry", "exit")]
        if any(len(word) != 4 for word in words):
            raise ValueError("preempt count must contain exactly four captured bytes")
        before, after = (int.from_bytes(word, "little") for word in words)
        expected = (before + 512) % 2**32
        if after != expected:
            failures.append(dict(visit=visits, before=hex(before), expected=hex(expected), actual=hex(after)))
        visits += 1
    if not visits:
        raise ValueError("capture contains no visits")
    print(json.dumps(dict(status="fail" if failures else "pass", visits=visits,
                          predicate="Rt.C2.Kept.count", failures=failures)))
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
