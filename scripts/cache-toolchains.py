#!/usr/bin/env python3
"""Snapshot the staged local tool copies for offline restoration."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
records = []
for name, version, origin in (
    ("lean", "4.33.1", "/home/dev/.elan/toolchains/leanprover--lean4---v4.33.1"),
    ("go", "1.26.5", "/usr/local/go"),
    ("lean-lsp", "0.29.0", "/home/dev/.local/share/uv/tools/lean-lsp-mcp"),
):
    archive = ROOT / ".deps/downloads" / f"{name}-{version}-local-snapshot.tar.zst"
    if not archive.exists():
        temporary = archive.with_suffix(archive.suffix + ".partial")
        tar = subprocess.Popen(["tar", "-C", str(ROOT / ".tools"), "-cf", "-", name],
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
    records.append({"name": name, "version": version, "origin": origin,
                    "provenance": "independent local copy; no shared hardlinks",
                    "archive": str(archive.relative_to(ROOT)),
                    "sha256": checksum, "size_bytes": archive.stat().st_size,
                    "destination": f".tools/{name}"})
    print(f"Cached {name} {version}", flush=True)
(ROOT / "dependencies/toolchains.lock.json").write_text(json.dumps(records, indent=2) + "\n")
