#!/usr/bin/env python3
"""Capture configured source using recorded Kbuild commands, without rebuilding.

Run with scripts/in-bundle. Outputs go only under LEANUX_ARTIFACTS. The original
kernel build and source tree are read-only inputs. No shell is used to execute
the saved command. The compiler invocation retains semantic options and removes
only dependency/object output options before adding -E and a private output.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tarfile

UNITS = ("fs/eventfd", "fs/file", "fs/open", "fs/read_write", "fs/fcntl",
         "fs/anon_inodes", "fs/file_table", "lib/iov_iter")
MARKER = re.compile(r'^# (\d+) "([^"\n]+)"(?: (.*))?$')


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def identity(path: Path) -> dict:
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha(path)}


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def adapt(saved: str, output: Path) -> tuple[list[str], list[str], str]:
    # Kbuild's trailing objtool invocation is not part of preprocessing.
    compiler, separator, postprocess = saved.partition(" ; ")
    argv = shlex.split(compiler)
    if not argv or argv[0] != "gcc":
        raise ValueError("expected the pinned GCC command")
    retained = [argv[0]]
    removed = []
    i = 1
    while i < len(argv):
        arg = argv[i]
        if arg in ("-o", "-MF", "-MT", "-MQ"):
            removed.extend(argv[i:i + 2])
            i += 2
        elif arg in ("-c", "-MD", "-MMD", "-MP") or arg.startswith("-Wp,-MMD,"):
            removed.append(arg)
            i += 1
        else:
            if arg in (";", "&&", "||", "|") or arg.startswith("@"):
                raise ValueError("unexpected command structure")
            retained.append(arg)
            i += 1
    if "-c" not in removed or "-o" not in removed:
        raise ValueError("not the expected object compilation command")
    return retained + ["-E", "-o", str(output)], removed, postprocess if separator else ""


def source_name(path: Path, source: Path, build: Path) -> str:
    resolved = path.resolve()
    for prefix, root in (("linux/", source), ("kernel-build/", build)):
        if resolved.is_relative_to(root):
            return prefix + str(resolved.relative_to(root))
    return str(resolved)


def compare_archive(archive: Path, source: Path, paths: set[Path]) -> dict:
    wanted = {str(p.relative_to(source)): p for p in paths if p.is_relative_to(source)}
    checked = []
    changed = []
    with tarfile.open(archive, "r|xz") as stream:
        for member in stream:
            relative = member.name.partition("/")[2]
            if relative not in wanted:
                continue
            if not member.isfile():
                raise ValueError(f"expected regular archive input: {relative}")
            original = stream.extractfile(member)
            digest = hashlib.sha256()
            for chunk in iter(lambda: original.read(1024 * 1024), b""):
                digest.update(chunk)
            current = sha(wanted.pop(relative))
            record = {"path": relative, "archive_sha256": digest.hexdigest(),
                      "source_sha256": current}
            checked.append(record)
            if record["archive_sha256"] != current:
                changed.append(record)
    if wanted:
        raise ValueError("captured source inputs absent from pinned archive: " + ", ".join(wanted))
    return {"scope": "captured include closure and selected source anchors only",
            "checked_members": sorted(checked, key=lambda r: r["path"]),
            "modified_members": changed}


def line_map(path: Path, source: Path, build: Path) -> tuple[list[dict], list[Path]]:
    segments = []
    includes: set[Path] = set()
    for number, text in enumerate(path.read_text().splitlines(), 1):
        match = MARKER.fullmatch(text)
        if not match:
            continue
        src_line, filename, flags = match.groups()
        if filename.endswith("//"):
            # GCC with -g emits its working directory as a special marker.
            normalized = "<working-directory:" + filename + ">"
        elif filename.startswith("<"):
            normalized = filename
        else:
            include = Path(filename)
            if not include.is_absolute():
                include = build / include
            include = include.resolve()
            if not include.is_file():
                raise ValueError(f"missing preprocessed source input: {include}")
            includes.add(include)
            normalized = source_name(include, source, build)
        segments.append({"preprocessed_line": number + 1,
                         "source": normalized, "source_line": int(src_line),
                         "flags": [int(x) for x in flags.split()] if flags else []})
    return segments, sorted(includes)


def verify(manifest: Path) -> None:
    data = json.loads(manifest.read_text())
    records = data["source_inputs"] + data["fixed_inputs"]
    for unit in data["translation_units"]:
        records.extend(unit["outputs"].values())
    failures = []
    for item in records:
        path = Path(item["path"])
        if not path.is_absolute():
            path = manifest.parent / path
        if not path.is_file() or sha(path) != item["sha256"]:
            failures.append(str(path))
    if failures:
        raise ValueError("changed or missing captured inputs: " + ", ".join(failures))
    print(json.dumps({"status": "verified", "identities": len(records),
                      "manifest_sha256": sha(manifest)}))


def check_records(root: Path, shared: Path, model: Path) -> None:
    inventory_path = root / "correspondence/helpers-v1.json"
    bindings_path = root / "correspondence/model-bindings-v1.json"
    testability_path = root / "correspondence/testability-v1.json"
    inventory = json.loads(inventory_path.read_text())
    mappings = json.loads(bindings_path.read_text())
    testability = json.loads(testability_path.read_text())
    helpers = inventory["helper_records"]
    ids = {h["id"] for h in helpers}
    if len(ids) != len(helpers):
        raise ValueError("duplicate helper record")
    external_ids = {e["id"] for e in testability["external_contracts"]}
    anchors = []
    branches = {}
    for helper in helpers:
        path = shared / ".deps/linux" / helper["source"]["file"]
        lines = path.read_text().splitlines()
        hits = [i + 1 for i, line in enumerate(lines) if helper["source"]["anchor"] in line]
        if not hits:
            raise ValueError(f"missing source anchor: {helper['id']}")
        anchors.append({"helper": helper["id"], "source": identity(path), "lines": hits})
        if not set(helper["external"]) <= external_ids:
            raise ValueError(f"undefined external contract: {helper['id']}")
        for branch in helper["branches"]:
            if branch["id"] in branches or branch["classification"] not in inventory["classification_values"]:
                raise ValueError("duplicate branch or undefined classification")
            branches[branch["id"]] = branch
    definition = re.compile(r"^(?:private )?(?:partial )?def ([\w.]+)", re.MULTILINE)
    bound = {}
    for binding in mappings["bindings"]:
        key = (binding["file"], binding["declaration"])
        if key in bound or not set(binding["records"]) <= ids | external_ids:
            raise ValueError(f"invalid binding: {key}")
        bound[key] = binding
    actual = set()
    texts = []
    model_inputs = []
    for filename in sorted({b["file"] for b in mappings["bindings"]}):
        path = model / filename
        text = path.read_text()
        texts.append(text)
        model_inputs.append(identity(path))
        actual.update((filename, declaration) for declaration in definition.findall(text))
    if actual != set(bound):
        raise ValueError(f"unmatched model helpers: missing={actual - set(bound)}, extra={set(bound) - actual}")
    labels = {record["label"] for record in mappings["branch_labels"]}
    if len(labels) != len(mappings["branch_labels"]):
        raise ValueError("duplicate branch label")
    text = "\n".join(texts)
    for record in mappings["branch_labels"]:
        if json.dumps(record["label"]) not in text or not set(record["source_branch_ids"]) <= set(branches):
            raise ValueError(f"missing label or source branch: {record['label']}")
    emitted = set(re.findall(r'"([a-z_][a-z_0-9]*\.[a-z_0-9]+)"', text)) | {"fd_install"}
    if emitted != labels:
        raise ValueError(f"unmatched labels: {emitted ^ labels}")
    if {o["op"] for o in testability["operations"]} != {"eventfd2", "dup", "dup3", "close", "read", "write", "fcntl"}:
        raise ValueError("incomplete operation testability")
    counts = {kind: sum(b["classification"] == kind for b in branches.values())
              for kind in inventory["classification_values"]}
    print(json.dumps({"status": "verified", "helper_records": len(helpers),
                      "model_definitions": len(bound), "branch_labels": len(labels),
                      "source_branch_classes": counts,
                      "record_inputs": [identity(p) for p in (inventory_path, bindings_path, testability_path)],
                      "model_inputs": model_inputs, "source_anchors": anchors}, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--kernel-build", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--check-records", action="store_true")
    parser.add_argument("--model-root", type=Path)
    args = parser.parse_args()
    if args.verify:
        verify(args.verify.resolve())
        return
    root = Path(os.environ["LEANUX_ROOT"]).resolve()
    shared = Path(os.environ["LEANUX_SHARED_ROOT"]).resolve()
    if args.check_records:
        check_records(root, shared, (args.model_root or root).resolve())
        return
    artifacts = Path(os.environ["LEANUX_ARTIFACTS"]).resolve()
    source = shared / ".deps/linux"
    source_lock = json.loads((shared / "dependencies/sources.lock.json").read_text())
    pinned_source = next(entry for entry in source_lock if entry["name"] == "linux")
    source_archive = shared / pinned_source["archive"]
    archive_identity = identity(source_archive)
    if archive_identity["sha256"] != pinned_source["sha256"]:
        raise ValueError("staged Linux archive differs from dependency lock")
    build = (args.kernel_build or shared / ".artifacts/kernel-active-sandbox").resolve()
    output = (args.output or artifacts / "correspondence").resolve()
    if not output.is_relative_to(artifacts) or output == artifacts:
        raise ValueError("output must be a private subdirectory of LEANUX_ARTIFACTS")
    output.mkdir(parents=True, exist_ok=False)
    # Snapshot small launcher inputs so task-worktree cleanup loses no evidence.
    snapshots = output / "capture-inputs"
    snapshots.mkdir()
    for name in ("scripts/bundle-tool", "scripts/in-bundle", "scripts/capture-correspondence.py"):
        shutil.copy2(root / name, snapshots / Path(name).name)
    fixed = [build / ".config", build / "include/generated/autoconf.h",
             build / "include/config/auto.conf", build / "include/generated/utsrelease.h",
             build / "arch/x86/boot/bzImage", build / "vmlinux",
             shared / ".tools/sysroot/usr/bin/x86_64-linux-gnu-gcc-13",
             shared / ".tools/sysroot/usr/libexec/gcc/x86_64-linux-gnu/13/cc1"]
    fixed.extend(sorted((shared / "dependencies").glob("*.lock.json")))
    fixed_ids = [identity(p) for p in fixed] + [archive_identity]
    fixed_ids += [{**identity(p), "path": str(p.relative_to(output))}
                  for p in sorted(snapshots.iterdir())]
    units = []
    all_inputs: set[Path] = set()
    for unit in UNITS:
        directory, name = unit.rsplit("/", 1)
        cmdfile = build / directory / f".{name}.o.cmd"
        command = cmdfile.read_text().splitlines()[0].split(" := ", 1)[1]
        destination = output / (unit.replace("/", "_") + ".i")
        argv, removed, postprocess = adapt(command, destination)
        before = identity(cmdfile)
        log = output / (unit.replace("/", "_") + ".stderr")
        with log.open("wb") as stderr:
            subprocess.run(argv, cwd=build, stdin=subprocess.DEVNULL,
                           stdout=subprocess.DEVNULL, stderr=stderr, check=True,
                           timeout=120)
        if identity(cmdfile) != before:
            raise ValueError("recorded build command changed during capture")
        mapping, includes = line_map(destination, source, build)
        all_inputs.update(includes)
        all_inputs.add(cmdfile)
        mapped = destination.with_suffix(".lines.json")
        write_json(mapped, mapping)
        units.append({"source": unit + ".c", "original_command": command,
                      "original_command_file": before,
                      "cwd": str(build), "preprocess_argv": argv,
                      "removed_output_options": removed,
                      "omitted_postprocessing": postprocess,
                      "include_closure": [source_name(p, source, build) for p in includes],
                      "outputs": {kind: {**identity(p), "path": p.name}
                                  for kind, p in (("preprocessed", destination),
                                                  ("source_map", mapped), ("stderr", log))}})
        print(f"captured {unit}.c ({len(includes)} source inputs)", flush=True)
    all_inputs.add(source / "arch/x86/entry/syscalls/syscall_64.tbl")
    source_comparison = compare_archive(source_archive, source, all_inputs)
    comparison_path = output / "source-archive-comparison.json"
    write_json(comparison_path, source_comparison)
    fixed_ids.append({**identity(comparison_path), "path": comparison_path.name})
    data = {"version": 1, "category": "configured-source-capture",
            "linux_commit": pinned_source["commit"],
            "commit_provenance": "staged dependency lock; source is an extracted release archive, not a Git checkout",
            "source_archive_members_checked": len(source_comparison["checked_members"]),
            "modified_source_members": source_comparison["modified_members"],
            "architecture": "x86_64", "capture_jobs": 1,
            "source_root": str(source), "kernel_build_root": str(build),
            "compiler_wrapper": str(Path(shutil.which("gcc")).resolve()),
            "compiler_version": subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0],
            "fixed_inputs": fixed_ids,
            "source_inputs": [{**identity(p), "logical_path": source_name(p, source, build)}
                              for p in sorted(all_inputs)],
            "translation_units": units,
            "limitations": ["Line directives map preprocessed text; they are not an AST or control-flow proof.",
                            "The reviewed C-to-Lean source bridge remains unproved."]}
    manifest = output / "manifest.json"
    write_json(manifest, data)
    verify(manifest)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"source capture failed: {error}", file=sys.stderr)
        sys.exit(1)
