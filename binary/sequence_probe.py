#!/usr/bin/env python3
"""Run the three function comparisons before a retained-heap mixed sequence.

Recordings and generated heaps remain separate from actual captured entries.
Run this command under the project's resource cap.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

from census import ROOT
from pin import verify_pin


def merge_inputs(inputs):
    result = dict(inputs[-1])
    for key in ('offsets', 'preempt'):
        if any(item[key] != result[key] for item in inputs):
            raise ValueError(f'incompatible input {key}')
    for key in ('instructions', 'labels', 'hooks'):
        merged = {}
        for item in inputs:
            for value in item[key]:
                address = value['pc'] if key == 'instructions' else value[0]
                if address in merged and merged[address] != value:
                    raise ValueError(f'conflicting {key} at {address}')
                merged[address] = value
        result[key] = list(merged.values())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lookup-check', type=Path, required=True)
    parser.add_argument('--remove-check', type=Path, required=True)
    parser.add_argument('--replace-check', type=Path, required=True)
    args = parser.parse_args()
    out = ROOT / '.tmp/binary-sequence'
    out.mkdir(parents=True, exist_ok=True)
    kraken = verify_pin(ROOT)
    commands = [
        ['pair_run.py', '--trace', 'd1_second_response', '--check', str(args.lookup_check.resolve())],
        ['remove_probe.py', '--check', str(args.remove_check.resolve())],
        ['replace_probe.py', '--check', str(args.replace_check.resolve())],
    ]
    for command in commands:
        print(f'function comparison: {command[0]}', flush=True)
        with (out / (command[0] + '.log')).open('w') as log:
            subprocess.run([sys.executable, '-B', str(ROOT / 'binary' / command[0]), *command[1:]],
                           cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    inputs = [json.loads((ROOT / name).read_text()) for name in (
        '.tmp/binary-pair/d1_second_response/input.json', '.tmp/binary-remove/input.json',
        '.tmp/binary-replace/input.json')]
    path = out / 'input.json'
    path.write_text(json.dumps(merge_inputs(inputs)) + '\n')
    started = time.monotonic()
    completed = subprocess.run([str(ROOT / 'binary/.lake/build/bin/binary-pair-sequence'), str(path)],
                               cwd=ROOT, text=True, capture_output=True, check=True)
    if completed.stderr:
        raise ValueError(completed.stderr)
    result = json.loads(completed.stdout)
    result.update(kraken=kraken, paired_seconds=round(time.monotonic() - started, 3),
                  three_way='all three function comparisons passed before sequence execution')
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    calls = [call for case in result['runs'] for call in case['run']['calls']]
    print(json.dumps(dict(status=result['status'], sequences=len(result['runs']), calls=len(calls),
                         instructions=sum(c['instructions'] for c in calls),
                         paired_seconds=result['paired_seconds'], three_way=result['three_way']), indent=2))


if __name__ == '__main__':
    main()
