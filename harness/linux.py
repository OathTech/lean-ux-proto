"""Compile the guest runner and collect observations from the pinned Linux VM.

Run with scripts/in-bundle python3 -m harness.linux INPUT.jsonl --out PATH.
No experimental trace operation is ever executed on the host.
"""
import argparse
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import time

from .trace import InvalidTrace, loads_trace, serialize_wire, validate_trace

ROOT = Path(__file__).resolve().parents[1]
SHARED = Path(os.environ.get("LEANUX_SHARED_ROOT", ROOT)).resolve()
ARTIFACTS = Path(os.environ.get("LEANUX_ARTIFACTS", ROOT / ".artifacts")).resolve()
KERNEL = SHARED / ".artifacts/kernel-active-sandbox"
OUTPUT_LIMIT = 16 * 1024 * 1024


class LinuxRunError(RuntimeError):
    def __init__(self, kind, message, outdir):
        super().__init__(message)
        self.kind, self.outdir = kind, Path(outdir)


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _jsonl(path, values):
    with path.open("w") as output:
        for value in values:
            output.write(json.dumps(value, separators=(",", ":"), sort_keys=True) + "\n")


def _decode_json(text):
    def pairs(entries):
        result = {}
        for key, value in entries:
            if key in result:
                raise ValueError(f"duplicate member {key}")
            result[key] = value
        return result
    def constant(value):
        raise ValueError(f"nonfinite JSON {value}")
    return json.loads(text, object_pairs_hook=pairs, parse_constant=constant)


def _bounded_process(command, output, timeout, limit):
    """Capture at most limit bytes and reap our own process group on failure."""
    started = time.monotonic()
    written = 0
    with output.open("wb") as log:
        try:
            process = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, start_new_session=True)
        except OSError as exc:
            raise LinuxRunError("environment_failure", str(exc), output.parent) from exc
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                while selector.get_map():
                    remaining = timeout - (time.monotonic() - started)
                    if remaining <= 0:
                        raise LinuxRunError("timeout", f"Process exceeded {timeout} seconds", output.parent)
                    for key, _ in selector.select(min(remaining, 1)):
                        data = os.read(key.fd, 65536)
                        if not data:
                            selector.unregister(key.fileobj)
                            continue
                        allowed = min(len(data), limit - written)
                        log.write(data[:allowed])
                        written += allowed
                        if allowed != len(data):
                            raise LinuxRunError("output_limit", f"Captured output exceeded {limit} bytes", output.parent)
                remaining = timeout - (time.monotonic() - started)
                if remaining <= 0:
                    raise LinuxRunError("timeout", f"Process exceeded {timeout} seconds", output.parent)
                try:
                    return process.wait(timeout=remaining)
                except subprocess.TimeoutExpired as exc:
                    raise LinuxRunError("timeout", f"Process exceeded {timeout} seconds", output.parent) from exc
        finally:
            # This group was created for this invocation; never target other agents.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            process.stdout.close()


def _check_observation(result, trace):
    if type(result) is not dict or set(result) != {"version", "id", "observations", "branches"}:
        raise ValueError("observation envelope fields")
    if type(result["version"]) is not int or result["version"] != 1 or result["id"] != trace["id"] or result["branches"] != []:
        raise ValueError("observation envelope identity")
    observations = result["observations"]
    if type(observations) is not list or len(observations) != len(trace["ops"]):
        raise ValueError("observation count")
    for i, (observation, op) in enumerate(zip(observations, trace["ops"])):
        if type(observation) is not dict or set(observation) != {"index", "ret", "errno", "bytes"}:
            raise ValueError("operation observation fields")
        ret, error, data = observation["ret"], observation["errno"], observation["bytes"]
        if type(observation["index"]) is not int or observation["index"] != i or type(ret) is not int or not -4095 <= ret < 2**63:
            raise ValueError("operation index or return value")
        if ret < 0:
            if type(error) is not int or error != -ret:
                raise ValueError("inconsistent errno")
        elif error is not None:
            raise ValueError("errno on success")
        if type(data) is not str or not re.fullmatch(r"(?:[0-9a-f]{2}){0,16}", data):
            raise ValueError("read output encoding")
        expected = ret if op["op"] == "read" and ret >= 0 else 0
        if len(data) != 2 * expected or expected > op.get("count", 16):
            raise ValueError("read output byte count")


def _collect(outdir, traces, process_returncode):
    results, coverage, fixtures, errors, child_failures, completed, kernels = [], [], [], [], [], [], []
    comparisons, comparison_results = [], []
    for line in (outdir / "boot.log").read_text(errors="strict").splitlines():
        line = line.rstrip("\r")
        for prefix, target in (("LEANUX_RESULT ", results), ("LEANUX_COVERAGE ", coverage),
                               ("LEANUX_FIXTURE ", fixtures), ("LEANUX_ERROR ", errors),
                               ("LEANUX_CHILD_FAILURE ", child_failures), ("LEANUX_CMP ", comparisons),
                               ("LEANUX_CMP_RESULT ", comparison_results)):
            if line.startswith(prefix):
                try:
                    target.append(_decode_json(line[len(prefix):]))
                except (ValueError, RecursionError) as exc:
                    raise LinuxRunError("invalid_output", f"Malformed guest record: {exc}", outdir) from exc
                break
        if line.startswith("LEANUX_BATCH_DONE "):
            completed.append(line)
        if line.startswith("LEANUX_KERNEL "):
            kernels.append(line.removeprefix("LEANUX_KERNEL "))
    _jsonl(outdir / "observations.jsonl", results)
    _jsonl(outdir / "coverage.jsonl", coverage)
    _jsonl(outdir / "comparisons.jsonl", comparisons)
    _jsonl(outdir / "guest-errors.jsonl", errors + child_failures)
    (outdir / "fixture.json").write_text(json.dumps({
        "roles": {"0": "console stdin", "1": "console stdout", "2": "console stderr", "3": "KCOV", "4-7": "/dev/null filler"},
        "per_trace": fixtures, "kernel_releases": kernels,
    }, indent=2) + "\n")
    if errors or child_failures:
        kind = errors[0].get("kind", "environment_failure") if errors else "crash"
        raise LinuxRunError(kind, "Guest trace failed; inspect guest-errors.jsonl", outdir)
    if process_returncode or completed != [f"LEANUX_BATCH_DONE traces={len(traces)} failures=0"] or len(kernels) != 1:
        raise LinuxRunError("crash", "Guest did not complete exactly one batch", outdir)
    boot = (outdir / "boot.log").read_text()
    if len(re.findall(r"^LEANUX_GUEST_EXIT=0\r?$", boot, re.MULTILINE)) != 1:
        raise LinuxRunError("crash", "Missing successful guest exit", outdir)
    if len(results) != len(traces) or len(fixtures) != len(traces) or len(comparison_results) != len(traces):
        raise LinuxRunError("invalid_output", "Missing or extra trace results/fixtures", outdir)
    expected_coverage = [(trace["id"], i) for trace in traces for i in range(len(trace["ops"]))]
    if len(coverage) != len(expected_coverage):
        raise LinuxRunError("missing_coverage", "Missing or extra per-operation coverage", outdir)
    try:
        for result, trace, fixture in zip(results, traces, fixtures):
            _check_observation(result, trace)
            if fixture != {"id": trace["id"], "reserved": list(range(8)), "free": [8, 31], "rlimit": [32, 32]}:
                raise ValueError("fixture mismatch")
        for row, (identifier, index) in zip(coverage, expected_coverage):
            if type(row) is not dict or set(row) != {"id", "index", "count", "pcs"} or row["id"] != identifier or type(row["index"]) is not int or row["index"] != index:
                raise ValueError("coverage identity or order")
            pcs = row["pcs"]
            if type(row["count"]) is not int or not 1 <= row["count"] < 65535 or type(pcs) is not list or not 1 <= len(pcs) <= row["count"]:
                raise ValueError("coverage count")
            if any(type(pc) is not str or not re.fullmatch(r"0x[0-9a-f]{1,16}", pc) for pc in pcs) or len(set(pcs)) != len(pcs):
                raise ValueError("coverage addresses")
        if len(comparisons) != len(expected_coverage):
            raise ValueError("comparison records per operation")
        for row, (identifier, index) in zip(comparisons, expected_coverage):
            if type(row) is not dict or set(row) != {"id", "index", "count", "records"} or row["id"] != identifier or row["index"] != index:
                raise ValueError("comparison identity or order")
            if type(row["count"]) is not int or not 1 <= row["count"] < 65536 or not 1 <= len(row["records"]) <= row["count"]:
                raise ValueError("comparison record count")
            if len({tuple(r) for r in row["records"]}) != len(row["records"]):
                raise ValueError("duplicate comparison records")
            if type(row["records"]) is not list or not all(
                    type(r) is list and len(r) == 4 and type(r[0]) is int and 0 <= r[0] < 8
                    and all(type(x) is str and re.fullmatch(r"0x[0-9a-f]{1,16}", x) for x in r[1:]) for r in row["records"]):
                raise ValueError("comparison records")
    except (ValueError, TypeError, KeyError) as exc:
        raise LinuxRunError("invalid_output", str(exc), outdir) from exc
    # The comparison child reruns each trace independently; its results must
    # be identical, or the comparison records do not describe this run.
    for result, again in zip(results, comparison_results):
        if again != {"id": result["id"], "rets": [o["ret"] for o in result["observations"]],
                     "bytes": [o["bytes"] for o in result["observations"]]}:
            raise LinuxRunError("environment_failure", f"Nondeterministic rerun of {result['id']}", outdir)
    unexpected_errors = {4, 12, 23, 512, 513, 514, 516}
    if any(row["errno"] in unexpected_errors for result in results for row in result["observations"]):
        raise LinuxRunError("environment_failure", "Unexpected interruption or allocator resource failure", outdir)
    return results


def run_linux(traces, outdir, *, timeout=120):
    """Return ordered observations; preserve evidence and raise on execution failures.

    `outdir` must be a fresh/empty directory within the task's artifact root.
    One VM executes the batch, forking a fresh child for every trace. Independent
    calls boot fresh VMs. The project-wide advisory lock prevents overlapping VMs.
    """
    traces = [validate_trace(trace) for trace in traces]
    wire = serialize_wire(traces)
    outdir = Path(outdir).resolve()
    if not outdir.is_relative_to(ARTIFACTS):
        raise ValueError(f"outdir must be within task artifact root {ARTIFACTS}")
    outdir.mkdir(parents=True, exist_ok=True)
    if any(outdir.iterdir()):
        raise ValueError(f"outdir must be empty: {outdir}")
    _jsonl(outdir / "inputs.jsonl", traces)
    (outdir / "wire.txt").write_text(wire)
    lockpath = SHARED / ".artifacts/runs/qemu.lock"
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open("a+") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise LinuxRunError("resource_busy", "Another project guest owns the QEMU slot", outdir) from exc
        return _run_locked(traces, outdir, timeout)


def _run_locked(traces, outdir, timeout):
    build = ["gcc", "-static", "-O2", "-Wall", "-Wextra", "-Werror", "-std=c11", str(ROOT / "harness/guest.c"), "-o", str(outdir / "guest-runner")]
    started = time.monotonic()
    build_returncode = _bounded_process(build, outdir / "build.log", 60, OUTPUT_LIMIT)
    if build_returncode:
        raise LinuxRunError("build_failure", "Guest compilation failed; inspect build.log", outdir)
    (outdir / "init").write_text(
        "#!/bin/sh\n"
        "/bin/busybox mount -t devtmpfs devtmpfs /dev\n"
        "/bin/busybox mount -t proc proc /proc\n"
        "/bin/busybox mount -t sysfs sysfs /sys\n"
        "/bin/busybox mount -t debugfs debugfs /sys/kernel/debug\n"
        "/guest-runner /wire.txt\n"
        "result=$?\n"
        "echo LEANUX_GUEST_EXIT=$result\n"
        "/bin/busybox reboot -f\n"
        "while :; do /bin/busybox sleep 1; done\n"
    )
    spec = ["dir /bin 755 0 0", "dir /dev 755 0 0", "dir /proc 755 0 0", "dir /sys 755 0 0", "dir /tmp 1777 0 0", "nod /dev/console 600 0 0 c 5 1", "nod /dev/null 666 0 0 c 1 3", "slink /bin/sh busybox 777 0 0"]
    for target, source, mode in (("/init", outdir / "init", "755"), ("/guest-runner", outdir / "guest-runner", "755"), ("/wire.txt", outdir / "wire.txt", "444"), ("/bin/busybox", SHARED / ".tools/sysroot/usr/bin/busybox", "755")):
        if any(c.isspace() for c in str(source)):
            raise LinuxRunError("environment_failure", "initramfs source path contains whitespace", outdir)
        spec.append(f"file {target} {source} {mode} 0 0")
    (outdir / "initramfs.list").write_text("\n".join(spec) + "\n")
    cpio_command = [str(KERNEL / "usr/gen_init_cpio"), "-t", "0", str(outdir / "initramfs.list")]
    cpio = subprocess.check_output(cpio_command, timeout=30)
    (outdir / "initramfs.cpio.gz").write_bytes(gzip.compress(cpio, mtime=0))
    command = ["qemu-system-x86_64", "-accel", "tcg,thread=single", "-machine", "pc-i440fx-8.2", "-cpu", "qemu64", "-smp", "1", "-m", "256", "-display", "none", "-monitor", "none", "-serial", "stdio", "-nic", "none", "-no-reboot", "-kernel", str(KERNEL / "arch/x86/boot/bzImage"), "-initrd", str(outdir / "initramfs.cpio.gz"), "-append", "console=ttyS0 panic=1 nokaslr loglevel=3"]
    identities = [ROOT / "harness/guest.c", ROOT / "harness/linux.py", ROOT / "harness/trace.py", ROOT / "contracts/trace-v1.md", ROOT / "contracts/trace.schema.json", ROOT / "contracts/observation.schema.json", ROOT / "scripts/in-bundle", ROOT / "scripts/bundle-tool", KERNEL / ".config", KERNEL / "arch/x86/boot/bzImage", KERNEL / "vmlinux", KERNEL / "usr/gen_init_cpio", SHARED / ".tools/sysroot/usr/bin/busybox", outdir / "guest-runner", outdir / "init", outdir / "wire.txt", outdir / "initramfs.cpio.gz"]
    provenance = {"schema_version": 1, "build_command": build, "cpio_command": cpio_command, "qemu_command": command, "timeout_seconds": timeout, "captured_output_limit_bytes": OUTPUT_LIMIT, "inputs": {str(path): sha256(path) for path in identities}, "compiler": subprocess.check_output(["gcc", "--version"], text=True), "qemu": subprocess.check_output(["qemu-system-x86_64", "--version"], text=True)}
    (outdir / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    (outdir / "qemu-command.json").write_text(json.dumps(command, indent=2) + "\n")
    try:
        returncode = _bounded_process(command, outdir / "boot.log", timeout,
                                      OUTPUT_LIMIT - (outdir / "build.log").stat().st_size)
        observations = _collect(outdir, traces, returncode)
    except LinuxRunError as exc:
        (outdir / "run-status.json").write_text(json.dumps({"kind": exc.kind, "detail": str(exc), "elapsed_seconds": time.monotonic() - started}) + "\n")
        raise
    except UnicodeError as exc:
        raise LinuxRunError("invalid_output", "Guest output is not UTF-8", outdir) from exc
    (outdir / "run-status.json").write_text(json.dumps({"kind": "complete", "traces": len(traces), "operations": sum(len(t['ops']) for t in traces), "elapsed_seconds": time.monotonic() - started, "qemu_returncode": returncode}, indent=2) + "\n")
    return observations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--timeout", default=120, type=float)
    args = parser.parse_args()
    try:
        traces = [loads_trace(line) for line in args.input.read_text().splitlines()]
        observations = run_linux(traces, args.out, timeout=args.timeout)
    except (InvalidTrace, LinuxRunError, ValueError) as exc:
        parser.exit(1, f"{getattr(exc, 'kind', 'invalid_input')}: {exc}\n")
    for observation in observations:
        print(json.dumps(observation, separators=(",", ":")))


if __name__ == "__main__":
    main()
