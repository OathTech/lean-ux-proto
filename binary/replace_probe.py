#!/usr/bin/env python3
"""Replacement replay with independent kernel coverage and mirror decisions.

The first case reconstructs the old index projection from the completed
recorded operation; it is not a captured entry or execution of its callers.
"""
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
    out = ROOT / '.tmp/binary-replace'
    path, chunk = prepare(args.check.resolve(), out, 'wg_index_hashtable_replace', 3)
    rows = [json.loads(line.removeprefix('LEANUX_BINARY_PCS '))
            for line in (chunk / 'linux/boot.log').read_text().splitlines()
            if line.startswith('LEANUX_BINARY_PCS ')]
    [kernel] = [r for r in rows if r['index'] == 2 and r['stream'] == 'remote']
    if any(r['pcs'] for r in rows if r is not kernel):
        raise ValueError('unexpected replacement coverage outside the selected remote operation')
    kernel_pcs = [int(pc, 16) for pc in kernel['pcs']]
    [model] = [json.loads(s) for s in (chunk / 'model/model.stdout').read_text().splitlines()]
    decisions = [b['label'] for b in model['branches'] if b['index'] == 2 and
                 b['label'].startswith('wg_index_hashtable_replace.unhashed=')]
    if decisions != ['wg_index_hashtable_replace.unhashed=0']:
        raise ValueError(f'expected one successful replacement decision: {decisions}')
    started = time.monotonic()
    completed = subprocess.run([str(ROOT / 'binary/.lake/build/bin/binary-pair-replace'), str(path)],
                               capture_output=True, text=True, check=True)
    if completed.stderr:
        raise ValueError(completed.stderr)
    result = json.loads(completed.stdout)
    for run in result['cases'][0]['runs']:
        call = run['calls'][0]
        source = [f'wg_index_hashtable_replace.unhashed={int(not call["answer"])}']
        if call['coverage'] != kernel_pcs or source != decisions:
            raise ValueError(f'three-way replacement mismatch: {call}, {kernel_pcs}, {decisions}')
    result.update(three_way='pass',
                  comparison_scope='one record-derived index projection; not captured arguments or intervening caller execution',
                  kernel_coverage=kernel_pcs, mirror_decisions=decisions,
                  paired_seconds=round(time.monotonic() - started, 3))
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
