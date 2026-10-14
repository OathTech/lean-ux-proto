#!/usr/bin/env python3
"""Snapshot the staged local tool copies for offline restoration."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
# The stages and the download cache are the main checkout's (shared by every
# worktree, docs/worktree-practices.md); the lock is this checkout's.
SHARED = ROOT
if (ROOT / ".git").is_file():
    common = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                            capture_output=True, text=True, check=True).stdout.strip()
    SHARED = Path(common).parent
LOCK = ROOT / "dependencies/toolchains.lock.json"
# Fields the lock carries that this script does not compute (an upstream
# release's URL and hash, its equivalence note) are kept from the existing row.
existing = {(row["name"], row["version"]): row for row in json.loads(LOCK.read_text())} if LOCK.exists() else {}
records = []
# (name, version, origin, staged directory under .tools). Lean 4.33.1 was
# staged as `.tools/lean`; later Lean toolchains are staged as `lean-<version>`
# so that checkouts on different toolchains share one .tools (scripts/in-bundle
# picks the one each checkout's lean-toolchain names).
for name, version, origin, staged in (
    ("lean", "4.33.1", "/home/dev/.elan/toolchains/leanprover--lean4---v4.33.1", "lean"),
    ("lean", "4.35.0", "/home/dev/.elan/toolchains/leanprover--lean4---v4.35.0", "lean-4.35.0"),
    ("go", "1.26.5", "/usr/local/go", "go"),
    ("lean-lsp", "0.29.0", "/home/dev/.local/share/uv/tools/lean-lsp-mcp", "lean-lsp"),
):
    archive = SHARED / ".deps/downloads" / f"{name}-{version}-local-snapshot.tar.zst"
    if not archive.exists():
        if not (SHARED / ".tools" / staged).is_dir():
            raise SystemExit(f"Not staged, nothing to snapshot: {SHARED / '.tools' / staged}")
        temporary = archive.with_suffix(archive.suffix + ".partial")
        tar = subprocess.Popen(["tar", "-C", str(SHARED / ".tools"), "-cf", "-", staged],
                                stdout=subprocess.PIPE)
        assert tar.stdout is not None
        try:
            subprocess.run(["zstd", "-q", "-T2", "-3", "-o", str(temporary)],
                            stdin=tar.stdout, check=True)
        finally:
            tar.stdout.close()
        if tar.wait() != 0:
            raise RuntimeError(f"archiving {name} failed")
        temporary.rename(archive)
    with archive.open("rb") as stream:
        checksum = hashlib.file_digest(stream, "sha256").hexdigest()
    record = dict(existing.get((name, version), {}))
    record.update({"name": name, "version": version, "origin": origin,
                   "provenance": "independent local copy; no shared hardlinks",
                   "archive": str(archive.relative_to(SHARED)),
                   "sha256": checksum, "size_bytes": archive.stat().st_size,
                   "destination": f".tools/{staged}"})
    records.append(record)
    print(f"Cached {name} {version}", flush=True)
LOCK.write_text(json.dumps(records, indent=2) + "\n")
