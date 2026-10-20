#!/usr/bin/env python3
"""Replay insertion only after checking the capture against current pins."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from binary.census import ORACLE
from binary.pin import verify_pin
from binary.target import pins, verify_image
from harness.linux import verify_kernel


def validate_identity(snapshot, kernel, image_sha256, kraken):
    captured = snapshot.get('kernel')
    if not isinstance(captured, dict) or captured.get('checked') is not True or any(
            captured.get(field) != kernel[field] for field in ('expected', 'actual')):
        raise ValueError('capture identity mismatch or missing field: kernel')
    for field, expected in [('image_sha256', image_sha256), ('kraken', kraken)]:
        if field not in snapshot or snapshot[field] != expected:
            raise ValueError(f'capture identity mismatch or missing field: {field}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('snapshot', type=Path)
    parser.add_argument('layouts', type=Path)
    args = parser.parse_args()
    kraken = verify_pin(ROOT)
    kernel = verify_kernel(ORACLE.parent, expected=pins()[0])
    image = verify_image()
    with args.snapshot.open() as stream:
        snapshot = json.load(stream)
    validate_identity(snapshot, kernel, image, kraken)
    del snapshot
    subprocess.run([str(ROOT/'binary/.lake/build/bin/binary-pair-insert-capture'),
                    str(args.input), str(args.snapshot), str(args.layouts)], check=True)


if __name__ == '__main__':
    main()
