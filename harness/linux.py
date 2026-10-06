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
import sys
import subprocess
import time

from .trace import uses_wireguard, InvalidTrace, loads_trace, serialize_wire, validate_trace
from .wg import decode_dump

ROOT = Path(__file__).resolve().parents[1]
SHARED = Path(os.environ.get("LEANUX_SHARED_ROOT", ROOT)).resolve()
ARTIFACTS = Path(os.environ.get("LEANUX_ARTIFACTS", ROOT / ".artifacts")).resolve()
# The accepted oracle kernel, or another kernel build selected by
# LEANUX_KERNEL_DIR (it must lie inside the shared or task artifact roots).
KERNEL = Path(os.environ.get("LEANUX_KERNEL_DIR", SHARED / ".artifacts/kernel-net-choice")).resolve()
if not (KERNEL.is_relative_to(SHARED / ".artifacts") or KERNEL.is_relative_to(ARTIFACTS)):
    raise SystemExit(f"LEANUX_KERNEL_DIR outside the artifact roots: {KERNEL}")
OUTPUT_LIMIT = 16 * 1024 * 1024
# The dispatch set (docs/2026-10-03-choice-stream-strategy.md, section 4.4):
# the deferred units whose dispatch opens a KCOV section in a network trace.
# Work items by their function (process_one_work); the NET_RX vector by
# net_rx_action (handle_softirqs). Everything else dispatched while a trace
# runs (vmstat, RCU, netns cleanup) is not the trace's and records nothing.
# D3 (docs/2026-10-05-d3-timers.md, section 3.1): WireGuard's five timer
# callbacks (call_timer_fn) and the zero-key work item.
DISPATCH_SYMBOLS = ("wg_packet_handshake_send_worker", "wg_packet_handshake_receive_worker",
                    "wg_packet_encrypt_worker", "wg_packet_tx_worker", "net_rx_action",
                    "wg_packet_decrypt_worker",
                    "wg_expired_retransmit_handshake", "wg_expired_send_keepalive", "wg_expired_new_handshake",
                    "wg_expired_zero_key_material", "wg_queued_expired_zero_key_material",
                    "wg_expired_send_persistent_keepalive")
# Whether the kernel writes the kind-303 arm records at mod_timer for the
# dispatch set's timers (D3, section 3.3). Off until the mirror consumes
# them: an unconsumed record is a choice from an undeclared consumer.
ARM_RECORDS = False
# The oracle is the kernel build booted with these parameters (D3, option
# C-jiffies: the timekeeper is pinned to refined-jiffies, which the virtual
# time advance requires; each batch checks it at start and end).
EXPECTED_CLOCKSOURCE = "refined-jiffies"
BOOT_PARAMETERS = f"console=ttyS0 panic=1 nokaslr loglevel=3 clocksource={EXPECTED_CLOCKSOURCE}"


def dispatch_addresses(kernel=None, symbols=DISPATCH_SYMBOLS):
    """Each dispatch symbol's address in the kernel's System.map (nokaslr):
    exactly one text symbol of that name, or the run fails."""
    found = {}
    for line in (Path(kernel or KERNEL) / "System.map").read_text().splitlines():
        address, kind, name = line.split()[:3]
        if name in symbols:
            if kind not in ("t", "T") or name in found:
                raise ValueError(f"dispatch symbol {name} is not one text symbol")
            found[name] = int(address, 16)
    if set(found) != set(symbols):
        raise ValueError(f"dispatch symbols missing: {sorted(set(symbols) - set(found))}")
    return [found[name] for name in symbols]


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
        # A successful wg_get also carries the decoded device state.
        fields = {"index", "ret", "errno", "bytes"}
        if op["op"] == "wg_get" and type(observation) is dict and observation.get("ret") == 0:
            fields = fields | {"device"}
        if op["op"] == "wg_observe":
            fields = fields | {"datagrams", "replies", "stats"}
        if type(observation) is not dict or set(observation) != fields:
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


def attach_devices(results, traces, records):
    """Each successful wg_get has exactly one dump record; its payloads are
    decoded (coalesced) into the observation's canonical `device`."""
    by_trace = {result["id"]: result for result in results}
    seen = set()
    for record in records:
        if type(record) is not dict or set(record) != {"id", "index", "payloads"} or record["id"] not in by_trace:
            raise ValueError("wireguard record fields or identity")
        key = (record["id"], record["index"])
        observations = by_trace[record["id"]]["observations"]
        if key in seen or type(record["index"]) is not int or not 0 <= record["index"] < len(observations):
            raise ValueError("duplicate or out-of-range wireguard record")
        seen.add(key)
        if type(record["payloads"]) is not list or not all(type(p) is str for p in record["payloads"]):
            raise ValueError("wireguard payloads")
        observations[record["index"]]["device"] = decode_dump(record["payloads"])
    for trace in traces:
        for index, op in enumerate(trace["ops"]):
            expected = op["op"] == "wg_get" and by_trace[trace["id"]]["observations"][index]["ret"] == 0
            if expected != ((trace["id"], index) in seen):
                raise ValueError("missing or unexpected wireguard dump record")


def attach_observed(results, traces, records):
    """Each wg_observe has exactly one record: the datagrams the fixture's
    listeners received (family, length, message type), sorted, since arrival
    order across peers is not determined; the datagrams the sender received,
    with their recvfrom sources, sorted; and wg0's transmit counters and
    receive error counters."""
    by_trace = {result["id"]: result for result in results}
    seen = set()
    for record in records:
        if type(record) is not dict or set(record) != {"id", "index", "datagrams", "replies", "stats"} or record["id"] not in by_trace:
            raise ValueError("wg_observe record fields or identity")
        key = (record["id"], record["index"])
        observations = by_trace[record["id"]]["observations"]
        if key in seen or type(record["index"]) is not int or not 0 <= record["index"] < len(observations):
            raise ValueError("duplicate or out-of-range wg_observe record")
        seen.add(key)
        datagrams = record["datagrams"]
        def hex_bytes(entry, length):
            return (type(entry[-1]) is str and len(entry[-1]) == 2 * length
                    and all(c in "0123456789abcdef" for c in entry[-1]))
        if type(datagrams) is not list or not all(
                type(d) is list and len(d) == 4 and d[0] in (4, 6)
                and all(type(x) is int and x >= 0 for x in d[:3]) and hex_bytes(d, d[1])
                for d in datagrams):
            raise ValueError("wg_observe datagrams")
        # what the sender received: recvfrom's source (the IPv6 socket's
        # family, the address as 32 hex digits, an IPv4 source v4-mapped, the
        # port), then length, message type, receiver index and bytes
        replies = record["replies"]
        if type(replies) is not list or not all(
                type(r) is list and len(r) == 7 and r[0] == 10
                and type(r[1]) is str and re.fullmatch(r"[0-9a-f]{32}", r[1]) is not None
                and all(type(x) is int and x >= 0 for x in r[2:6]) and r[2] < 65536 and hex_bytes(r, r[3])
                for r in replies):
            raise ValueError("wg_observe replies")
        stats = record["stats"]
        if type(stats) is not dict or set(stats) != {"tx_errors", "tx_dropped", "rx_frame_errors", "rx_length_errors"} \
                or not all(type(v) is int and v >= 0 for v in stats.values()):
            raise ValueError("wg_observe stats")
        # sorted as the mirror sorts them: by compact JSON
        compact = lambda x: json.dumps(x, separators=(",", ":"))
        observations[record["index"]]["datagrams"] = sorted(datagrams, key=compact)
        observations[record["index"]]["stats"] = stats
        observations[record["index"]]["replies"] = sorted(replies, key=compact)
    for trace in traces:
        for index, op in enumerate(trace["ops"]):
            if (op["op"] == "wg_observe") != ((trace["id"], index) in seen):
                raise ValueError("missing or unexpected wg_observe record")


def merge_remote(rows, remote, traces, key):
    """Network traces carry a second, remote stream per operation (the
    dispatch sections of the trace's deferred units, collected under the
    trace's KCOV common handle). Exactly one remote record per network operation is
    appended to that operation's row: task entries first, then remote ones,
    each deduplicated in first-execution order."""
    net = {trace["id"] for trace in traces if uses_wireguard(trace)}
    by_key = {}
    for record in remote:
        if type(record) is not dict or set(record) != {"id", "index", "count", key} or record["id"] not in net:
            raise ValueError("remote record fields or identity")
        k = (record["id"], record["index"])
        if k in by_key or type(record[key]) is not list:
            raise ValueError("duplicate remote record")
        by_key[k] = record
    merged, used = [], set()
    for row in rows:
        k = (row.get("id"), row.get("index")) if type(row) is dict else None
        if k and k[0] in net:
            record = by_key.get(k)
            if record is None:
                raise ValueError(f"missing remote record for {k}")
            used.add(k)
            row = dict(row)
            seen = {json.dumps(x) for x in row[key]}
            row[key] = row[key] + [x for x in record[key] if json.dumps(x) not in seen]
            if type(record["count"]) is not int or record["count"] < 0:
                raise ValueError("remote record count")
            row["count"] = row["count"] + record["count"]
        merged.append(row)
    if used != set(by_key):
        raise ValueError("remote records without an operation")
    return merged


def _collect(outdir, traces, process_returncode, alloc=None):
    results, coverage, fixtures, errors, child_failures, completed, kernels = [], [], [], [], [], [], []
    comparisons, comparison_results, wireguard, observed = [], [], [], []
    remote_coverage, remote_comparisons = [], []
    hidden, remote_hidden, steering, sections, clocksources = [], [], [], [], []
    alloc_status, alloc_tsc = [], []
    for line in (outdir / "boot.log").read_text(errors="strict").splitlines():
        line = line.rstrip("\r")
        for prefix, target in (("LEANUX_RESULT ", results), ("LEANUX_COVERAGE ", coverage),
                               ("LEANUX_FIXTURE ", fixtures), ("LEANUX_ERROR ", errors),
                               ("LEANUX_CHILD_FAILURE ", child_failures), ("LEANUX_CMP ", comparisons),
                               ("LEANUX_CMP_RESULT ", comparison_results), ("LEANUX_WG ", wireguard),
                               ("LEANUX_WGOBS ", observed), ("LEANUX_RCOVERAGE ", remote_coverage),
                               ("LEANUX_RCMP ", remote_comparisons), ("LEANUX_HIDDEN ", hidden),
                               ("LEANUX_RHIDDEN ", remote_hidden), ("LEANUX_STEER ", steering),
                               ("LEANUX_SECTIONS ", sections), ("LEANUX_CLOCKSOURCE ", clocksources),
                               ("LEANUX_ALLOC ", alloc_status), ("LEANUX_ALLOC_TSC ", alloc_tsc)):
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
    # The timekeeper's clocksource at batch start and end (D3): both the
    # expected one, or the batch is not a run of the oracle.
    _jsonl(outdir / "clocksource.jsonl", clocksources)
    if (len(clocksources) != 2 or [r.get("at") if type(r) is dict else None for r in clocksources] != ["start", "end"]
            or any(set(r) != {"at", "current", "available"} or r["current"] != EXPECTED_CLOCKSOURCE for r in clocksources)):
        raise LinuxRunError("environment_failure", f"Timekeeper clocksource is not {EXPECTED_CLOCKSOURCE} at batch start and end", outdir)
    try:
        coverage = merge_remote(coverage, remote_coverage, traces, "pcs")
        comparisons = merge_remote(comparisons, remote_comparisons, traces, "records")
    except ValueError as exc:
        raise LinuxRunError("invalid_output", f"Remote coverage: {exc}", outdir) from exc
    _jsonl(outdir / "coverage.jsonl", coverage)
    # Choices (docs/2026-10-03-choice-stream-strategy.md): one task row and,
    # with remote coverage, one remote row per network operation and child;
    # each record is [kind, call site, sequence number, length, value hex].
    for row in hidden + remote_hidden:
        if (type(row) is not dict or set(row) != {"id", "index", "mode", "records"} or row["mode"] not in ("pc", "cmp")
                or type(row["records"]) is not list
                or any(type(r) is not list or len(r) != 5 or type(r[0]) is not int or type(r[1]) is not str
                       or type(r[2]) is not int or type(r[3]) is not int or type(r[4]) is not str
                       or len(r[4]) != 2 * min(r[3], 40)
                       for r in row["records"])):
            raise LinuxRunError("invalid_output", "Malformed hidden-input record", outdir)
    _jsonl(outdir / "hidden.jsonl", [dict(r, stream="task") for r in hidden] + [dict(r, stream="remote") for r in remote_hidden])
    # Steering status per steered trace and child: entries left, mismatches.
    steered = {t["id"] for t in traces if "steer" in t}
    if (any(type(r) is not dict or set(r) != {"id", "mode", "remaining", "mismatches"} or r["id"] not in steered
            or r["mode"] not in ("pc", "cmp") for r in steering)
            or sorted((r["id"], r["mode"]) for r in steering) != sorted((i, m) for i in steered for m in ("pc", "cmp"))):
        raise LinuxRunError("invalid_output", "Steering status rows missing or malformed", outdir)
    _jsonl(outdir / "steering.jsonl", steering)
    # Dispatch sections per network trace and child: none dropped (the guest
    # fails a trace with a dropped section; this checks it reported).
    net = {t["id"] for t in traces if uses_wireguard(t)}
    if (any(type(r) is not dict or set(r) != {"id", "mode", "dropped", "opened"} or r["id"] not in net
            or r["mode"] not in ("pc", "cmp") or type(r["dropped"]) is not int or type(r["opened"]) is not int
            for r in sections)
            or sorted((r["id"], r["mode"]) for r in sections) != sorted((i, m) for i in net for m in ("pc", "cmp"))):
        raise LinuxRunError("invalid_output", "Section status rows missing or malformed", outdir)
    _jsonl(outdir / "sections.jsonl", sections)
    # The allocation set (A): armed batches report, per trace and child, the
    # kind-305 records and unwinds since the load, and the TSC rate once;
    # disarmed batches report nothing.
    armed = bool(alloc and (alloc["flags"] or alloc["ranges"]))
    if (any(type(r) is not dict or set(r) != {"id", "mode", "records", "unwinds", "cycles"}
            or r["mode"] not in ("pc", "cmp") or not all(type(r[k]) is int and r[k] >= 0 for k in ("records", "unwinds", "cycles"))
            for r in alloc_status)
            or sorted((r["id"], r["mode"]) for r in alloc_status)
            != (sorted((t["id"], m) for t in traces for m in ("pc", "cmp")) if armed else [])
            or len(alloc_tsc) != int(armed) or any(set(r) != {"mhz"} for r in alloc_tsc)):
        raise LinuxRunError("invalid_output", "Allocation status rows missing or malformed", outdir)
    if armed:
        _jsonl(outdir / "alloc.jsonl", alloc_tsc + alloc_status)
    _jsonl(outdir / "comparisons.jsonl", comparisons)
    _jsonl(outdir / "guest-errors.jsonl", errors + child_failures)
    (outdir / "fixture.json").write_text(json.dumps({
        "roles": {"0": "console stdin", "1": "console stdout", "2": "console stderr", "3": "KCOV", "4-7": "/dev/null filler; in network traces 4-5 UDP listeners, 6 UDP sender, 7 generic netlink"},
        "per_trace": fixtures, "kernel_releases": kernels,
    }, indent=2) + "\n")
    if errors or child_failures:
        # (a dropped section is a guest error: coverage_failure, dropped_sections)
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
        attach_devices(results, traces, wireguard)
        attach_observed(results, traces, observed)
        for result, trace, fixture in zip(results, traces, fixtures):
            _check_observation(result, trace)
            limit = trace.get("rlimit_nofile", 32)
            if fixture != {"id": trace["id"], "reserved": list(range(8)), "free": [8, limit - 1], "rlimit": [limit, limit]}:
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
    except (ValueError, TypeError, KeyError, IndexError) as exc:
        raise LinuxRunError("invalid_output", str(exc), outdir) from exc
    # The comparison child reruns each trace independently; its results must
    # be identical, or the comparison records do not describe this run.
    for result, again in zip(results, comparison_results):
        if again != {"id": result["id"], "rets": [o["ret"] for o in result["observations"]],
                     "bytes": [o["bytes"] for o in result["observations"]]}:
            raise LinuxRunError("environment_failure", f"Nondeterministic rerun of {result['id']}", outdir)
    unexpected_errors = {4, 12, 23, 512, 513, 514, 516}
    # A2: a trace under the declared failslab-style extension forces
    # task-context allocation failures, so its ENOMEM is the expected result
    # of the schedule (compared with the mirror, evaluator/protocol.py), not
    # allocator pressure. Every other trace still fails on it.
    forced = {12}
    if any(row["errno"] in unexpected_errors - (forced if trace.get("domain_extension") == "failslab" else set())
           for result, trace in zip(results, traces) for row in result["observations"]):
        raise LinuxRunError("environment_failure", "Unexpected interruption or allocator resource failure", outdir)
    return results


def run_linux(traces, outdir, *, timeout=120, steer_wire=None, arm_records=ARM_RECORDS, alloc=None):
    """Return ordered observations; preserve evidence and raise on execution failures.

    `outdir` must be a fresh/empty directory within the task's artifact root.
    One VM executes the batch, forking a fresh child for every trace. Independent
    calls boot fresh VMs. The project-wide advisory lock prevents overlapping VMs.
    """
    traces = [validate_trace(trace) for trace in traces]
    dispatch = dispatch_addresses() if any(uses_wireguard(t) for t in traces) else []
    wire = serialize_wire(traces, steer_wire, dispatch, arm_records, alloc)
    outdir = Path(outdir).resolve()
    if not outdir.is_relative_to(ARTIFACTS):
        raise ValueError(f"outdir must be within task artifact root {ARTIFACTS}")
    outdir.mkdir(parents=True, exist_ok=True)
    if any(outdir.iterdir()):
        raise ValueError(f"outdir must be empty: {outdir}")
    _jsonl(outdir / "inputs.jsonl", traces)
    (outdir / "wire.txt").write_text(wire)
    # QEMU_SLOTS guests may run at once, project-wide (each worktree's checks
    # share these lock files in the main checkout). Slot 0 is the historic
    # single lock file, so a worktree on older code still excludes slot 0.
    # Wait for any free slot, up to QEMU_LOCK_WAIT seconds, then fail.
    runs = SHARED / ".artifacts/runs"
    runs.mkdir(parents=True, exist_ok=True)
    paths = [runs / ("qemu.lock" if i == 0 else f"qemu.lock.{i}") for i in range(QEMU_SLOTS)]
    deadline = time.monotonic() + QEMU_LOCK_WAIT
    waited = False
    while True:
        for path in paths:
            lock = path.open("a+")
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                lock.close()
                continue
            with lock:
                return _run_locked(traces, outdir, timeout, arm_records, alloc)
        if time.monotonic() >= deadline:
            raise LinuxRunError("resource_busy", f"Other guests held all {QEMU_SLOTS} QEMU slots for {QEMU_LOCK_WAIT} s", outdir)
        if not waited:
            print(f"waiting for one of {QEMU_SLOTS} QEMU slots ({runs}), up to {QEMU_LOCK_WAIT} s", file=sys.stderr, flush=True)
            waited = True
        time.sleep(2)


QEMU_LOCK_WAIT = 3600
# Concurrent guests (single-threaded TCG, 256 MiB each); LEANUX_QEMU_SLOTS overrides.
QEMU_SLOTS = int(os.environ.get("LEANUX_QEMU_SLOTS", "3"))


def _run_locked(traces, outdir, timeout, arm_records, alloc=None):
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
    command = ["qemu-system-x86_64", "-accel", "tcg,thread=single", "-machine", "pc-i440fx-8.2", "-cpu", "qemu64", "-smp", "1", "-m", "256", "-display", "none", "-monitor", "none", "-serial", "stdio", "-nic", "none", "-no-reboot", "-kernel", str(KERNEL / "arch/x86/boot/bzImage"), "-initrd", str(outdir / "initramfs.cpio.gz"), "-append", BOOT_PARAMETERS]
    identities = [ROOT / "harness/guest.c", ROOT / "harness/linux.py", ROOT / "harness/trace.py", ROOT / "contracts/trace-v1.md", ROOT / "contracts/trace.schema.json", ROOT / "contracts/observation.schema.json", ROOT / "scripts/in-bundle", ROOT / "scripts/bundle-tool", KERNEL / ".config", KERNEL / "arch/x86/boot/bzImage", KERNEL / "vmlinux", KERNEL / "usr/gen_init_cpio", SHARED / ".tools/sysroot/usr/bin/busybox", outdir / "guest-runner", outdir / "init", outdir / "wire.txt", outdir / "initramfs.cpio.gz"]
    provenance = {"schema_version": 1, "expected_clocksource": EXPECTED_CLOCKSOURCE, "arm_records": arm_records, "alloc": alloc or {"flags": 0, "ranges": []}, "build_command": build, "cpio_command": cpio_command, "qemu_command": command, "timeout_seconds": timeout, "captured_output_limit_bytes": OUTPUT_LIMIT, "inputs": {str(path): sha256(path) for path in identities}, "compiler": subprocess.check_output(["gcc", "--version"], text=True), "qemu": subprocess.check_output(["qemu-system-x86_64", "--version"], text=True)}
    (outdir / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    (outdir / "qemu-command.json").write_text(json.dumps(command, indent=2) + "\n")
    try:
        returncode = _bounded_process(command, outdir / "boot.log", timeout,
                                      OUTPUT_LIMIT - (outdir / "build.log").stat().st_size)
        observations = _collect(outdir, traces, returncode, alloc)
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
