#!/usr/bin/env python3
"""Restore missing local toolchains from their verified offline snapshots."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
(ROOT / ".tools").mkdir(exist_ok=True)
for row in json.loads((ROOT / "dependencies/toolchains.lock.json").read_text()):
    destination = ROOT / row["destination"]
    if destination.exists():
        print(f"Present, left untouched: {destination}")
        continue
    archive = ROOT / row["archive"]
    with archive.open("rb") as stream:
        actual = hashlib.file_digest(stream, "sha256").hexdigest()
    if actual != row["sha256"]:
        raise SystemExit(f"Checksum mismatch: {archive}")
    subprocess.run(["tar", "--zstd", "--no-same-owner", "-xf", str(archive),
                    "-C", str(ROOT / ".tools")], check=True)
    print(f"Restored {destination}")
