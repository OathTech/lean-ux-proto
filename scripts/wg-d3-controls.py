#!/usr/bin/env python3
"""Negative controls for D3's time control (docs/2026-10-05-d3-timers.md,
section 8): every trace in corpus/timer-controls must fail, in the stated
way, each run with its guest variant.

    LEANUX_KERNEL_DIR=... scripts/in-bundle python3 scripts/wg-d3-controls.py

- tc_advance_wait0, with the guest variant advance-wait-0 (harness/linux.py
  GUEST_VARIANTS): the advance returns before its absorbing tick, so the
  keepalive timer's section and its workers land in the wg_get after it
  (not an idle point: the mirror meets an unexpected section, a hidden
  mismatch), or after the trace's last readout (opened but not recorded).
(The between zone, an expiry inside the advance's window whose wheel bucket
is not, is not a control: the mirror follows the sections and agrees;
corpus/wireguard/d3_between_zone.json.)
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# trace -> (guest variant, accepted ways to fail: an outcome, or a problem)
EXPECTED = {
    'tc_advance_wait0': ('advance-wait-0', {'hidden_mismatch', 'dispatch sections opened but not recorded'}),
}


def main():
    results, ok = {}, True
    for trace_id, (variant, accepted) in EXPECTED.items():
        out = ROOT / f'.artifacts/check/timer-controls-{trace_id}'
        subprocess.run(['rm', '-rf', str(out)], check=True)
        command = [sys.executable, '-m', 'evaluator.check', '--suite', 'timer-controls', '--trace', trace_id,
                   '--no-build', '--out', str(out)] + (['--guest-variant', variant] if variant else [])
        subprocess.run(command, cwd=ROOT, capture_output=True)
        report = json.loads((out / 'report.json').read_text())
        if report.get('aborted') or report['traces'] != 1:
            results[trace_id] = dict(error='the control did not run', aborted=report.get('aborted'))
            ok = False
            continue
        failure = next(iter(report['failures']), None)
        found = set() if failure is None else \
            {failure['outcome']} | {p['problem'] for p in failure.get('problems', [])}
        # the interface's stubs stop every D3 trace `unsupported`: not a verdict
        stub = 'D3 stream M: not yet' in (failure or {}).get('detail', '')
        rejected = bool(found & accepted) and not stub
        ok &= rejected
        results[trace_id] = dict(rejected=rejected, stub=stub, variant=variant, found=sorted(found),
                                 detail=(failure or {}).get('detail', '')[-300:])
    print(json.dumps(results, indent=1))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
