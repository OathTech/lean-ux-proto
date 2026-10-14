#!/usr/bin/env python3
"""Restore missing local toolchains.

Each toolchain comes from its verified offline snapshot when present. A row
with `upstream_url` and `upstream_sha256` can instead be fetched from its
official release when the snapshot is absent (a fresh clone); the release's
top-level directory becomes the destination. Lean 4.33.1's release was
compared file by file with the snapshot on 2026-09-30: identical (17,493
files). `--only NAME[,NAME]` restores a subset (the check needs `lean`).
Several rows may share a name (one per Lean version); each restores its own
destination, `.tools/lean` for 4.33.1 and `.tools/lean-<version>` after it,
and `scripts/in-bundle` picks the one a checkout's `lean-toolchain` names.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--only")
args = parser.parse_args()
rows = json.loads((ROOT / "dependencies/toolchains.lock.json").read_text())
names = {row["name"] for row in rows}
only = set(args.only.split(",")) if args.only else names
if not only <= names:
    raise SystemExit(f"Unknown toolchains: {sorted(only - names)}")
(ROOT / ".tools").mkdir(exist_ok=True)
for row in rows:
    if row["name"] not in only:
        continue
    destination = ROOT / row["destination"]
    if destination.exists():
        print(f"Present, left untouched: {destination}")
        continue
    archive = ROOT / row["archive"]
    if archive.exists():
        if sha256(archive) != row["sha256"]:
            raise SystemExit(f"Checksum mismatch: {archive}")
        subprocess.run(["tar", "--zstd", "--no-same-owner", "-xf", str(archive),
                        "-C", str(ROOT / ".tools")], check=True)
        print(f"Restored {destination} from its snapshot")
        continue
    if "upstream_url" not in row:
        raise SystemExit(f"No snapshot and no upstream release for {row['name']}: {archive}")
    download = ROOT / ".deps/downloads" / Path(row["upstream_url"]).name
    download.parent.mkdir(parents=True, exist_ok=True)
    if not download.exists():
        partial = download.with_name(download.name + ".partial")
        subprocess.run(["curl", "--fail", "--location", "--silent", "--show-error", "--retry", "3",
                        "--max-time", "1800", row["upstream_url"], "--output", str(partial)], check=True)
        partial.rename(download)
    if sha256(download) != row["upstream_sha256"]:
        raise SystemExit(f"Checksum mismatch: {download}")
    staging = destination.with_name(destination.name + ".extracting")
    if staging.exists():
        shutil.rmtree(staging)
    staging.mkdir(parents=True)
    subprocess.run(["tar", "--zstd", "--no-same-owner", "-xf", str(download), "-C", str(staging)], check=True)
    children = list(staging.iterdir())
    if len(children) != 1 or not children[0].is_dir():
        raise SystemExit(f"Unexpected release layout: {download}")
    children[0].rename(destination)
    staging.rmdir()
    print(f"Restored {destination} from its upstream release")
