#!/usr/bin/env python3
"""Three-way baseline followed by paired replay of captured allowed-IPs bytes.

Run through capped with a Python interpreter providing pyelftools. The mirror
prefix consumes this capture's records; the independent check remains separate.
"""
import argparse
from contextlib import redirect_stdout
import hashlib
import json
from pathlib import Path
import subprocess
import time

from allowedips_probe import prepare, compare
from census import ROOT, ORACLE
from pair_capture import source_prefix
from pin import verify_pin


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path, required=True)
    parser.add_argument('--check', type=Path, required=True)
    args = parser.parse_args()
    capture = args.capture.resolve()
    snapshot_path = capture/'snapshot.json'
    snapshot = json.loads(snapshot_path.read_text())
    pin = verify_pin(ROOT)
    if snapshot['kraken'] != pin or snapshot['image_sha256'] != hashlib.sha256(ORACLE.read_bytes()).hexdigest():
        raise ValueError('capture image/dependency pin differs from replay')
    subprocess.run(['lake', 'build', 'binary-probe', 'binary-pair-allowedips-capture'], cwd=ROOT/'binary', check=True)
    out = capture/'probe'
    out.mkdir(exist_ok=True)
    path, anchors, chunk = prepare(args.check.resolve(), out, snapshot['operation'], snapshot['instructionBudget'])
    with (capture/'three-way.log').open('w') as log, redirect_stdout(log):
        compare(path, anchors, chunk, snapshot['operation'])
    probe = source_prefix(json.loads(path.read_text()), capture/'boot.log')
    replay = capture/'replay-input.json'
    replay.write_text(json.dumps(probe)+'\n')
    started = time.monotonic()
    result_path = capture/'replay-result.json'
    with result_path.open('w') as log:
        subprocess.run([str(ROOT/'binary/.lake/build/bin/binary-pair-allowedips-capture'), str(replay),
                        str(snapshot_path), str(capture/'layouts.json')], stdout=log, check=True)
    result = json.loads(result_path.read_text())
    result.update(source_records='same captured boot; completed operation prefix', kraken=pin,
                  replay_seconds=round(time.monotonic()-started, 3))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
