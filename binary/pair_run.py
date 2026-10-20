#!/usr/bin/env python3
"""Run inside capped. Regenerate a recorded probe input, then run paired cases.

The existing probe retains the independent kernel/result/decision comparison.
Input and output JSON are ephemeral; only the command and conclusion belong
in a report. This constructs entry heaps, it does not capture them from Linux.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

from census import ROOT
from pin import verify_pin


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trace', choices=['d1_second_response',
                                           'd1_wrong_receiver_index_same_bucket'], required=True)
    parser.add_argument('--check', type=Path,
                        help='Reuse a successful differential check with raw binary coverage')
    args = parser.parse_args()
    out = ROOT / '.tmp' / 'binary-pair' / args.trace
    out.mkdir(parents=True, exist_ok=True)
    command = [sys.executable, '-B', str(ROOT / 'binary/run.py'), '--trace', args.trace,
               '--out', str(out)]
    if args.check:
        command += ['--check', str(args.check.resolve())]
    print('Running independent kernel/result/decision comparison', flush=True)
    with (out / 'three-way.log').open('w') as log:
        subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    kraken = verify_pin(ROOT)
    subprocess.run(['lake', 'build', 'binary-pair-runner'], cwd=ROOT / 'binary', check=True)
    # The existing extractor validates the ELF hash, DWARF and relative-branch
    # displacements, writing directly into this case's private directory.
    input_path = out / 'input.json'
    started = time.monotonic()
    with (out / 'result.json').open('w') as log:
        subprocess.run([str(ROOT / 'binary/.lake/build/bin/binary-pair-runner'), str(input_path)],
                       cwd=ROOT, stdout=log, check=True)
    elapsed = time.monotonic() - started
    result = json.loads((out / 'result.json').read_text())
    calls = [call for case in result['cases'] for run in case['runs'] for call in run['calls']]
    summary = dict(status=result['status'], trace=args.trace, kraken=kraken,
                   cases=len(result['cases']), calls=len(calls),
                   headers=sum(c['loop_headers'] for c in calls),
                   instructions=sum(c['instructions'] for c in calls),
                   negative_controls=len(result['negative_controls']),
                   paired_seconds=round(elapsed, 3), entry_origin=result['entry_origin'])
    summary['checkout'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    summary['working_tree_modified'] = bool(subprocess.check_output(
        ['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip())
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
