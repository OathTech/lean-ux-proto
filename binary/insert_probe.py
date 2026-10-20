#!/usr/bin/env python3
"""Compare insertion's supplied-service probe with the independent recording."""
import argparse
import json
from pathlib import Path
import subprocess
import time

from census import ROOT
from remove_probe import prepare


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', type=Path, required=True)
    args = parser.parse_args()
    out = ROOT / '.tmp/binary-insert'
    path, chunk = prepare(args.check.resolve(), out, 'wg_index_hashtable_insert',
                          1, 's2_index_collision')
    rows = [json.loads(line.removeprefix('LEANUX_BINARY_PCS '))
            for line in (chunk / 'linux/boot.log').read_text().splitlines()
            if line.startswith('LEANUX_BINARY_PCS ')]
    kernel_pcs = [int(pc, 16) for row in rows for pc in row['pcs']]
    [model] = [json.loads(s) for s in (chunk / 'model/model.stdout').read_text().splitlines()]
    decisions = [b['label'] for b in model['branches']
                 if b['label'].startswith('wg_index_hashtable_insert.')]
    started = time.monotonic()
    completed = subprocess.run([str(ROOT / 'binary/.lake/build/bin/binary-pair-insert'), str(path)],
                               capture_output=True, text=True)
    if completed.returncode:
        raise RuntimeError(f'paired insertion failed ({completed.returncode}): {completed.stderr}')
    if completed.stderr:
        raise ValueError(completed.stderr)
    result = json.loads(completed.stdout)
    for run in result['cases'][0]['runs']:
        actual = [pc for call in run['calls'] for pc in call['coverage']]
        source = [decision for call in run['calls'] for decision in call['decisions']]
        if actual != kernel_pcs or source != decisions:
            raise ValueError(f'three-way insertion mismatch: {actual}, {kernel_pcs}, {source}, {decisions}')
    result.update(three_way='pass', kernel_coverage=kernel_pcs, mirror_decisions=decisions,
                  comparison_scope='selected source-derived insertion calls, with supplied random returns; callers and random body are not executed',
                  paired_seconds=round(time.monotonic() - started, 3))
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], three_way=result['three_way'],
                         cases=len(result['cases']), paired_seconds=result['paired_seconds'],
                         execution_scope=result['execution_scope']), indent=2))


if __name__ == '__main__':
    main()
