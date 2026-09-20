#!/usr/bin/env python3
"""Verify staged download/documentation hashes without network access."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
checks = {}
def include(path, expected):
    if path in checks and checks[path] != expected:
        raise RuntimeError(f"conflicting checksums for {path}")
    checks[path] = expected

for row in json.loads((ROOT / "dependencies/packages.lock.json").read_text()):
    include(".deps/downloads/debs/" + row["filename"], row["sha256"])
for name in ("sources", "toolchains"):
    for row in json.loads((ROOT / f"dependencies/{name}.lock.json").read_text()):
        include(row["archive"], row["sha256"])
for row in json.loads((ROOT / "dependencies/documentation.lock.json").read_text()):
    include(row["path"], row["sha256"])
for row in json.loads((ROOT / "dependencies/lean-manual.lock.json").read_text()):
    include(row["path"], row["local_sha256"])
proposal = json.loads((ROOT / "docs/resource-proposal.json").read_text())
for row in proposal["source_files_inspected"]:
    include(f".deps/{row['source']}/{row['path']}", row["sha256"])
for name, expected in checks.items():
    with (ROOT / name).open("rb") as stream:
        actual = hashlib.file_digest(stream, "sha256").hexdigest()
    if actual != expected:
        raise SystemExit(f"FAIL: checksum mismatch: {name}")
print(f"PASS: {len(checks)} staged archives, reference files, and source samples verified.")
print("This checks the locked files; kernel/guest and tool execution have separate probes.")
