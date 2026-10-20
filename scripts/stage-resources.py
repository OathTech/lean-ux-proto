#!/usr/bin/env python3
"""Download/extract pinned resources locally. Never installs system packages.

Run with network access for initial staging. Existing downloads are hash-checked.
Package versions and checksums come from dependencies/packages.lock.json.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
DOWNLOADS = ROOT / ".deps/downloads"
# archive.ubuntu.com drops superseded updates from its pool (8 of the 222
# locked packages were gone by 2026-09-30). The dated snapshot serves every
# locked package unchanged; the lock's sha256 is enforced either way.
UBUNTU_ARCHIVE = "https://archive.ubuntu.com/ubuntu/"
UBUNTU_SNAPSHOT = "https://snapshot.ubuntu.com/ubuntu/20260920T000000Z/"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def fetch(url, path, expected=None):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        if expected and digest(path) != expected:
            raise RuntimeError(f"checksum mismatch: {path}")
        return digest(path)
    temporary = path.with_name(path.name + ".partial")
    subprocess.run([
        "curl", "--fail", "--location", "--silent", "--show-error",
        "--retry", "3", "--connect-timeout", "20", "--max-time", "900",
        url, "--output", str(temporary),
    ], check=True)
    actual = digest(temporary)
    if expected and actual != expected:
        raise RuntimeError(f"checksum mismatch: {url}: {actual}")
    temporary.rename(path)
    return actual


def unpack(archive, destination):
    marker = destination / ".leanux-archive-sha256"
    checksum = digest(archive)
    if marker.exists():
        if marker.read_text().strip() != checksum:
            raise RuntimeError(f"existing source differs: {destination}")
        return
    if destination.exists() and any(destination.iterdir()):
        raise RuntimeError(f"refusing to overwrite populated directory: {destination}")
    staging = destination.with_name(destination.name + ".extracting")
    staging.mkdir(parents=True, exist_ok=False)
    with tarfile.open(archive) as stream:
        # data filter rejects links escaping the extraction root and special files.
        stream.extractall(staging, filter="data")
    children = list(staging.iterdir())
    if len(children) != 1 or not children[0].is_dir():
        raise RuntimeError(f"unexpected archive layout: {archive}")
    children[0].rename(destination)
    staging.rmdir()
    marker.write_text(checksum + "\n")


def sources(names=None):
    """Fetch and unpack the locked sources, verifying each archive against
    dependencies/sources.lock.json (URL and sha256). The lock is never
    rewritten: a mismatch fails. `names` selects a subset (the check needs
    only `linux`)."""
    lock = json.loads((ROOT / "dependencies/sources.lock.json").read_text())
    known = {entry["name"] for entry in lock}
    if names is not None and not set(names) <= known:
        raise RuntimeError(f"unknown sources {sorted(set(names) - known)}")
    selected = [entry for entry in lock if names is None or entry["name"] in names]
    for entry in selected:
        if entry.get("consumer") == "binary":
            if names is not None:
                raise RuntimeError(f"{entry['name']} is an opt-in Git dependency: run "
                                   "python3 binary/run.py --bootstrap-only to clone its upstream and apply the locked patches")
            print(f"Not staged in the base bundle: {entry['name']} (binary/run.py dependency)", flush=True)
            continue
        archive = ROOT / entry["archive"]
        fetch(entry["url"], archive, entry["sha256"])
        unpack(archive, ROOT / ".deps" / entry["name"])
        print(f"Staged source: {entry['name']}", flush=True)
    proposal = json.loads((ROOT / "docs/resource-proposal.json").read_text())
    for item in proposal["source_files_inspected"]:
        if item["source"] not in {entry["name"] for entry in selected}:
            continue
        path = ROOT / ".deps" / item["source"] / item["path"]
        if digest(path) != item["sha256"]:
            raise RuntimeError(f"source pin audit failed: {path}")


def packages():
    lock = ROOT / "dependencies/packages.lock.json"
    entries = json.loads(lock.read_text())
    def download(entry):
        path = DOWNLOADS / "debs" / entry["filename"]
        if not entry["url"].startswith(UBUNTU_ARCHIVE):
            raise RuntimeError(f"unexpected package origin: {entry['url']}")
        fetch(UBUNTU_SNAPSHOT + entry["url"][len(UBUNTU_ARCHIVE):], path, entry["sha256"])
        return path
    with ThreadPoolExecutor(max_workers=4) as pool:
        archives = list(pool.map(download, entries))
    sysroot = ROOT / ".tools/sysroot"
    sysroot.mkdir(parents=True, exist_ok=True)
    marker = sysroot / ".leanux-packages-sha256"
    if marker.exists():
        if marker.read_text().strip() != digest(lock):
            raise RuntimeError("existing sysroot uses a different package lock")
        print("Package bundle already staged and locked", flush=True)
        return
    extracted = sysroot / ".leanux-extracted-sha256"
    if extracted.exists():
        if extracted.read_text().strip() != digest(lock):
            raise RuntimeError("extracted sysroot uses a different package lock")
    else:
        if any(sysroot.iterdir()):
            raise RuntimeError("refusing to overwrite an incomplete/unrecognized sysroot")
        for archive in archives:
            # Extraction only: no dpkg database, maintainer scripts, or host installation.
            subprocess.run(["dpkg-deb", "--extract", str(archive), str(sysroot)], check=True)
        extracted.write_text(digest(lock) + "\n")
    # Package extraction does not run Ubuntu's usrmerge or alternatives hooks.
    # Complete their required layout only inside this private sysroot.
    def merge(source, destination):
        destination.mkdir(parents=True, exist_ok=True)
        for child in source.iterdir():
            target = destination / child.name
            if not target.exists() and not target.is_symlink():
                child.rename(target)
            elif child.is_dir() and not child.is_symlink() and target.is_dir():
                merge(child, target)
            elif child.is_symlink() and target.is_symlink() and child.readlink() == target.readlink():
                child.unlink()
            elif child.is_file() and target.is_file() and digest(child) == digest(target):
                child.unlink()
            else:
                raise RuntimeError(f"usrmerge collision: {child}")
        source.rmdir()
    for name in ("bin", "sbin", "lib", "lib64"):
        path = sysroot / name
        if path.exists() and not path.is_symlink():
            merge(path, sysroot / "usr" / name)
        if not path.is_symlink():
            path.symlink_to("usr/" + name)
    for alias, target in {"gcc": "gcc-13", "cc": "gcc-13", "g++": "g++-13",
                          "c++": "g++-13", "cpp": "cpp-13", "clang": "clang-19",
                          "clang++": "clang++-19", "clang-format": "clang-format-19",
                          "awk": "gawk"}.items():
        path = sysroot / "usr/bin" / alias
        if not path.exists():
            if path.is_symlink():
                path.unlink()
            path.symlink_to(target)
    for directory in ("proc", "dev", "tmp", "run", str(ROOT).lstrip("/")):
        (sysroot / directory).mkdir(parents=True, exist_ok=True)
    localtime = sysroot / "etc/localtime"
    if not localtime.exists() and not localtime.is_symlink():
        localtime.symlink_to("../usr/share/zoneinfo/Etc/UTC")
    marker.write_text(digest(lock) + "\n")
    print(f"Staged {len(archives)} packages into {sysroot}", flush=True)


def documentation():
    pages = {
        "lean-lake.html": "https://lean-lang.org/doc/reference/4.33.0/Build-Tools-and-Distribution/Lake/",
        "lean-language.html": "https://lean-lang.org/doc/reference/4.33.0/",
        "qemu-invocation.html": "https://www.qemu.org/docs/master/system/invocation.html",
        "qemu-security.html": "https://www.qemu.org/docs/master/system/security.html",
        "kernel-kcov.html": "https://docs.kernel.org/6.12/dev-tools/kcov.html",
    }
    for page in ("eventfd.2", "dup.2", "fcntl.2", "close.2", "read.2", "write.2", "seccomp.2"):
        pages[page + ".html"] = f"https://man7.org/linux/man-pages/man2/{page}.html"
    records = []
    for filename, url in pages.items():
        path = ROOT / ".deps/docs" / filename
        checksum = fetch(url, path)
        records.append({"path": str(path.relative_to(ROOT)), "url": url, "sha256": checksum})
    (ROOT / "dependencies/documentation.lock.json").write_text(json.dumps(records, indent=2) + "\n")
    print(f"Staged {len(records)} documentation pages", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("sources", "packages", "docs", "all"))
    parser.add_argument("--sources", help="comma-separated subset of the locked sources, e.g. linux")
    args = parser.parse_args()
    (ROOT / "dependencies").mkdir(exist_ok=True)
    if args.phase in ("sources", "all"):
        sources(args.sources.split(",") if args.sources else None)
    if args.phase in ("packages", "all"):
        packages()
    if args.phase in ("docs", "all"):
        documentation()
