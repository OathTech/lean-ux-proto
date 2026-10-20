#!/usr/bin/env python3
"""Replay a captured lookup under capped; snapshots and reports stay ephemeral.

The source prefix consumes records from this capture's boot, resolved by the
existing campaign code. It never supplies bytes to the captured machine state.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

from census import ROOT, ORACLE
from pin import verify_pin
from run import prepare, compare

sys.path.insert(0, str(ROOT))
from evaluator.check import (load_hidden_sites, pair_sections, resolve_choices,
                             SECTION_START, SECTION_STOP, ALLOC_KIND, alloc_chain)
from evaluator.coverage import symbolize
from harness.linux import DISPATCH_SYMBOLS, dispatch_addresses


def source_prefix(probe, boot):
    """Resolve exactly the completed PC-mode prefix, with no fabricated rows."""
    trace, count = probe['trace'], probe['operation']
    rows = {}
    for line in boot.read_text().splitlines():
        for tag, stream in [('LEANUX_HIDDEN ', 'task'), ('LEANUX_RHIDDEN ', 'remote')]:
            if not line.startswith(tag):
                continue
            row = json.loads(line[len(tag):])
            if set(row) != {'id', 'index', 'mode', 'records'} or row['id'] != trace['id'] or row['mode'] != 'pc':
                raise ValueError('unexpected capture prefix record')
            key = row['index'], stream
            if key in rows or not 0 <= row['index'] < count:
                raise ValueError('duplicate or out-of-prefix capture record')
            for r in row['records']:
                if len(r) != 5 or len(bytes.fromhex(r[4])) != min(r[3], 40):
                    raise ValueError('malformed capture hidden input')
            rows[key] = row['records']
    if set(rows) != {(i, s) for i in range(count) for s in ('task', 'remote')}:
        raise ValueError('capture lacks a completed prefix task/remote record row')
    ops = []
    for i in range(count):
        task = rows[i, 'task']
        if any(r[0] in (SECTION_START, SECTION_STOP) for r in task):
            raise ValueError('dispatch section in task stream')
        records = [r + [None] for r in task] + pair_sections(rows[i, 'remote'])
        records.sort(key=lambda r: r[2])
        if len({r[2] for r in records}) != len(records):
            raise ValueError('duplicate prefix sequence number')
        ops.append(records)
    addresses = sorted({r[1] for op in ops for r in op} |
                       {a for op in ops for r in op if r[0] & 0x7fff == ALLOC_KIND for a in alloc_chain(r[4])})
    locations = symbolize([{'pcs': addresses}], ORACLE)['locations'] if addresses else {}
    dispatch = dict(zip(dispatch_addresses(ORACLE.parent), DISPATCH_SYMBOLS))
    resolved, problems, _, _ = resolve_choices(
        {(trace['id'], 'pc'): ops}, load_hidden_sites(), locations, dispatch)
    if problems:
        raise ValueError(f'capture prefix choice resolution failed: {problems}')
    # The following operation locates the call; replayPrefix executes only the
    # preceding operations. The standalone lookup itself consumes no records.
    current = dict(trace, ops=trace['ops'][:count+1], hidden=resolved[trace['id'], 'pc'] + [[]])
    return dict(probe, trace=current)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path, required=True)
    parser.add_argument('--check', type=Path, required=True,
                        help='Successful independent recording used to prepare this capture')
    args = parser.parse_args()
    capture = args.capture.resolve()
    snapshot_path = capture/'snapshot.json'
    snapshot = json.loads(snapshot_path.read_text())
    kraken = verify_pin(ROOT)
    if snapshot['kraken'] != kraken or snapshot['image_sha256'] != hashlib.sha256(ORACLE.read_bytes()).hexdigest():
        raise ValueError('capture image/dependency pin differs from replay')
    subprocess.run(['lake', 'build', 'binary-probe', 'binary-pair-capture'], cwd=ROOT/'binary', check=True)
    out = capture/'probe'
    out.mkdir(exist_ok=True)
    # Keep the independent recorded kernel/result/decision test before the
    # captured experiment; its source records remain distinct from this boot.
    input_path, functions, chunk = prepare(args.check.resolve(), out, snapshot['trace'])
    with (capture/'three-way.log').open('w') as log:
        from contextlib import redirect_stdout
        with redirect_stdout(log):
            compare(input_path, functions, chunk)
    probe = source_prefix(json.loads(input_path.read_text()), capture/'boot.log')
    replay = capture/'replay-input.json'
    replay.write_text(json.dumps(probe)+'\n')
    started = time.monotonic()
    result_path = capture/'replay-result.json'
    with result_path.open('w') as log:
        subprocess.run([str(ROOT/'binary/.lake/build/bin/binary-pair-capture'), str(replay),
                        str(snapshot_path), str(out/'layouts.json')], stdout=log, check=True)
    result = json.loads(result_path.read_text())
    result.update(source_records='same captured boot; completed operation prefix',
                  kraken=kraken, replay_seconds=round(time.monotonic()-started, 3))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
