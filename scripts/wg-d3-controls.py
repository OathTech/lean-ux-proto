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
  Since the kernel keeps interrupts off from the jump to its kind-304
  record and the guest no longer starts the advance just after a tick
  (D3 integration), the absorbing tick may also land between the advance's
  readout and the next operation's reset of the remote area: the sections'
  records are lost, the mirror misses the keepalive, and the first verdict
  is a semantic mismatch. That outcome counts only with the lost-records
  signature in Linux's own rows (`lost_sections`: more sections opened than
  section-start records reached the trace), the opened-but-not-recorded
  problem the check reports only on an agreeing trace.
(The between zone, an expiry inside the advance's window whose wheel bucket
is not, is not a control: the mirror follows the sections and agrees;
corpus/wireguard/d3_between_zone.json.)
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SECTION_START = 300


def lost_sections(out, trace_id):
    """For each guest child, sections the kernel opened beyond the
    section-start records that reached the trace (Linux's rows only)."""
    opened, recorded = {}, {}
    for chunk in sorted(out.glob('chunk-*/linux')):
        if not (chunk / 'sections.jsonl').exists() or not (chunk / 'hidden.jsonl').exists():
            continue
        for line in (chunk / 'sections.jsonl').read_text().splitlines():
            row = json.loads(line)
            if row['id'] == trace_id:
                opened[row['mode']] = row['opened']
        for line in (chunk / 'hidden.jsonl').read_text().splitlines():
            row = json.loads(line)
            if row['id'] == trace_id:
                recorded[row['mode']] = recorded.get(row['mode'], 0) + sum(
                    1 for r in row['records'] if r[0] & 0x7fff == SECTION_START)
    return {mode: opened[mode] - recorded.get(mode, 0) for mode in opened if opened[mode] > recorded.get(mode, 0)}
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
        lost = lost_sections(out, trace_id)
        if failure is not None and failure['outcome'] == 'semantic_mismatch' and lost:
            found.add('dispatch sections opened but not recorded')
        # the interface's stubs stop every D3 trace `unsupported`: not a verdict
        stub = 'D3 stream M: not yet' in (failure or {}).get('detail', '')
        rejected = bool(found & accepted) and not stub
        ok &= rejected
        results[trace_id] = dict(rejected=rejected, stub=stub, variant=variant, found=sorted(found), lost_sections=lost,
                                 detail=(failure or {}).get('detail', '')[-300:])
    print(json.dumps(results, indent=1))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
