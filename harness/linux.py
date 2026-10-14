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

from .trace import KCOV_CAPACITY, KCOV_TASK_CMP_CAPACITY, OPCODES, is_stepped, uses_wireguard, InvalidTrace, loads_trace, serialize_wire, validate_trace
from .wg import decode_dump, decode_messages

ROOT = Path(__file__).resolve().parents[1]
SHARED = Path(os.environ.get("LEANUX_SHARED_ROOT", ROOT)).resolve()
ARTIFACTS = Path(os.environ.get("LEANUX_ARTIFACTS", ROOT / ".artifacts")).resolve()
# The accepted oracle kernel, or another kernel build selected by
# LEANUX_KERNEL_DIR (it must lie inside the shared or task artifact roots).
KERNEL = Path(os.environ.get("LEANUX_KERNEL_DIR", SHARED / ".artifacts/kernel-net-choice")).resolve()
if not (KERNEL.is_relative_to(SHARED / ".artifacts") or KERNEL.is_relative_to(ARTIFACTS)):
    raise SystemExit(f"LEANUX_KERNEL_DIR outside the artifact roots: {KERNEL}")
# The approved oracle kernel (kernel/identity-x86_64-net-choice.txt): its first
# non-comment line is scripts/kernel-identity.py's path-independent identity.
# Every guest boot checks the selected build against it before taking a QEMU
# slot (verify_kernel). Without the check a run on another build is not
# noticed: the pre-D3 build left in the default directory failed the D3
# traces as environment_failure beside spurious hidden mismatches (D3
# evidence, S2), and nearly ran the 2026-10-11 baseline [USER 2026-10-11:
# add the validation]. LEANUX_KERNEL_IDENTITY names another expected identity
# (a control kernel, never the oracle); "unchecked" boots any build, with a
# warning, and the provenance and report record it.
IDENTITY_FILE = ROOT / "kernel/identity-x86_64-net-choice.txt"
IDENTITY = re.compile(r"[0-9a-f]{64}")


def approved_kernel_identity(path=IDENTITY_FILE):
    lines = [line.strip() for line in path.read_text().splitlines() if line.strip() and not line.startswith("#")]
    if not lines or not IDENTITY.fullmatch(lines[0]):
        raise ValueError(f"{path}: the first non-comment line is not a 64-digit identity")
    return lines[0]


def kernel_identity(kernel=None):
    """scripts/kernel-identity.py on a build directory (about 0.3 s)."""
    kernel = Path(kernel or KERNEL)
    if not (kernel / "vmlinux").is_file():
        raise LinuxRunError("kernel_mismatch", f"no vmlinux in {kernel}", ARTIFACTS)
    out = subprocess.check_output([sys.executable, str(ROOT / "scripts/kernel-identity.py"), str(kernel)], text=True, timeout=300)
    value = out.split()[0] if out.split() else ""
    if not IDENTITY.fullmatch(value):
        raise LinuxRunError("kernel_mismatch", f"kernel-identity.py gave no identity for {kernel}: {out[-200:]!r}", ARTIFACTS)
    return value


def verify_kernel(kernel=None, expected=None, outdir=None):
    """The identity check before a boot. Returns the record for the provenance
    and the report; raises LinuxRunError("kernel_mismatch") on any other build.
    `expected`: an identity, "unchecked", or None for LEANUX_KERNEL_IDENTITY,
    else the approved identity."""
    kernel = Path(kernel or KERNEL)
    setting = os.environ.get("LEANUX_KERNEL_IDENTITY") if expected is None else expected
    actual = kernel_identity(kernel)
    if setting == "unchecked":
        print(f"harness: WARNING: kernel identity UNCHECKED (LEANUX_KERNEL_IDENTITY=unchecked): {kernel} is {actual}",
              file=sys.stderr, flush=True)
        return {"kernel": str(kernel), "checked": False, "expected": None, "actual": actual, "source": "unchecked"}
    source = "LEANUX_KERNEL_IDENTITY" if setting else IDENTITY_FILE.name
    expected = setting or approved_kernel_identity()
    if not IDENTITY.fullmatch(expected):
        raise LinuxRunError("kernel_mismatch", f"{source}: {expected!r} is not a 64-digit identity or 'unchecked'", outdir or ARTIFACTS)
    if actual != expected:
        raise LinuxRunError("kernel_mismatch",
                            f"{kernel} has identity {actual}, expected {expected} ({source}): select the approved build "
                            "with LEANUX_KERNEL_DIR, or name this build's identity with LEANUX_KERNEL_IDENTITY",
                            outdir or ARTIFACTS)
    return {"kernel": str(kernel), "checked": True, "expected": expected, "actual": actual, "source": source}
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
                    "wg_expired_send_persistent_keepalive",
                    # W8 (docs/2026-10-06-w8-w9-netns-routing.md 3.2): the creating
                    # namespace's teardown (netns_wq) and the linkwatch run its
                    # carrier change queues (system_unbound_wq); armed per trace
                    "cleanup_net", "linkwatch_event")


def arm_masks(traces, symbols=DISPATCH_SYMBOLS):
    """W8, per-trace arming (design 3.2, audit C1): the subset of the dispatch
    set each trace arms, a bit per symbol. Every network trace arms the
    WireGuard set; only a foreign-creator trace arms `cleanup_net`, so a plain
    run never sees a stale teardown's section; `linkwatch_event` is armed by
    no trace yet (W8b: its delay depends on the global `linkwatch_nextevent`).
    An FS trace arms nothing."""
    masks = {}
    for trace in traces:
        mask = 0
        if uses_wireguard(trace):
            for i, name in enumerate(symbols):
                if name == "linkwatch_event":
                    continue
                if name == "cleanup_net" and trace.get("net_fixture") != "foreign-creator":
                    continue
                mask |= 1 << i
        masks[trace["id"]] = mask
    return masks
# Whether the kernel writes the kind-303 arm records at mod_timer for the
# dispatch set's timers (D3, section 3.3). On since the mirror consumes them
# at every arm site (stream M); evaluator/check.py passes the same value to
# the kernel and the mirror. Off, the kernel writes none and the mirror
# consumes none; a record present anyway is left unconsumed, a mismatch.
# Dispatch order (docs/2026-10-11-dispatch-order.md): the same flag gates
# the kind-307 queue record at __queue_work; a section start carries the
# dispatched unit, an arm record the timer's address.
ARM_RECORDS = True
# The oracle is the kernel build booted with these parameters (D3, option
# C-jiffies: the timekeeper is pinned to refined-jiffies, which the virtual
# time advance requires; each batch checks it at start and end).
EXPECTED_CLOCKSOURCE = "refined-jiffies"
# W5 (docs/2026-10-06-w5-w6-receive.md, section 6; D2 [USER 2026-10-07]): the
# network fixture's facts the guest sets per network namespace and reads back
# into its LEANUX_FIXTURE row: `net.ipv6.auto_flowlabels`,
# `net.ipv4.icmp_ratelimit` and `net.ipv6.icmp.ratelimit` at 0, and the
# link-local address fe80::ffff:1/128 on lo (the scoped-source injections;
# not fe80::1, a transmit destination of existing traces).
EXPECTED_NET_FIXTURE = {"auto_flowlabels": 0, "icmp_ratelimit": 0, "icmp6_ratelimit": 0, "lo_link_local": "fe80::ffff:1"}
BOOT_PARAMETERS = f"console=ttyS0 panic=1 nokaslr loglevel=3 clocksource={EXPECTED_CLOCKSOURCE}"
# epoll stream R (docs/2026-10-12-epoll-design.md, 3.4): fs/eventpoll.c's
# max_user_watches, computed at boot from the memory the kernel manages when
# eventpoll_init runs (the QEMU memory above, less the kernel's and the
# initramfs's reserved pages, so a rebuilt oracle or a larger initramfs can
# move it) and an operand of every EPOLL_CTL_ADD. The guest reads it back
# once per boot (LEANUX_EPOLL, with its warm-up ADD, 3.5); a batch whose
# value differs is not a run of the fixture the mirror assumes
# (Leanux/Env.lean carries the same constant) and fails as an environment
# failure naming both sides. Measured on the W9 oracle (313c2cc9) with the
# guest of this commit; re-measured at every oracle change: unchanged on the
# e1 oracle (7c2b436b, the kind-308 hook) [stream T, 2026-10-12].
EXPECTED_MAX_USER_WATCHES = 53092
# Guest build variants for negative controls only (never the oracle): the
# compiler definitions each adds. `advance-wait-0` (D3, section 8): wg_advance
# neither waits for the absorbing tick nor sleeps, so the timer sections land
# in the next operation, which the mirror must reject.
GUEST_VARIANTS = {"advance-wait-0": ("-DADVANCE_WAIT_US=0", "-DADVANCE_ABSORB=0")}


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


# A read's observation: the hex of its first READ_HEAD bytes and the
# BLAKE2s-256 digest of all of them (P design section 6).
READ_HEAD = 64
EPOLL_EVENT_SIZE = 12   # epoll R: sizeof(struct epoll_event) on x86-64 (packed)


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
        if op["op"] == "wg_get_recv" and type(observation) is dict and observation.get("ret") == 0:
            fields = fields | {"messages"}   # W2: the messages of one receive
        if op["op"] == "wg_observe":
            fields = fields | {"datagrams", "replies", "stats"}
        if op["op"] == "wg_batch":
            fields = fields | {"cqes"}   # W7: the completions at io_uring_enter's return
        # P design section 6: a read's digest, a write's sigpipe, a pipe2's fds; epoll's
        # wait digest; seccomp W (design 6.1): a probe's sigsys and child records
        fields = fields | {"read": {"digest"}, "epoll_wait": {"digest"}, "write": {"sigpipe"}, "pipe2": {"fds"},
                           "seccomp_probe": {"sigsys", "child"}}.get(op["op"], set())
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
        if type(data) is not str or not re.fullmatch(r"(?:[0-9a-f]{2}){0,%d}" % READ_HEAD, data):
            raise ValueError("read output encoding")
        if op["op"] in ("read", "write") and ret > op["count"]:
            raise ValueError("read or write returned more than its count")
        # epoll R: an epoll_wait returns ret events of EPOLL_EVENT_SIZE bytes
        # through the read channel (contracts/trace-v1.md, Epoll)
        if op["op"] == "epoll_wait" and ret > op["maxevents"]:
            raise ValueError("epoll_wait returned more events than maxevents")
        observed = ret if op["op"] == "read" and ret >= 0 else \
            ret * EPOLL_EVENT_SIZE if op["op"] == "epoll_wait" and ret >= 0 else 0
        if len(data) != 2 * min(observed, READ_HEAD):
            raise ValueError("read output byte count")
        if op["op"] in ("read", "epoll_wait"):
            digest = observation["digest"]
            if observed <= 0:
                if digest is not None:
                    raise ValueError("digest of an empty or failed read")
            elif type(digest) is not str or not re.fullmatch(r"[0-9a-f]{64}", digest):
                raise ValueError("read digest encoding")
            # every bytes in the clear: the guest's BLAKE2s against hashlib's
            elif observed <= READ_HEAD and digest != hashlib.blake2s(bytes.fromhex(data)).hexdigest():
                raise ValueError("read digest disagrees with hashlib.blake2s over its bytes")
        if op["op"] == "write" and (type(observation["sigpipe"]) is not int or observation["sigpipe"] not in (0, 1)):
            raise ValueError("write sigpipe")
        if op["op"] == "seccomp_probe":
            sigsys, child = observation["sigsys"], observation["child"]
            if sigsys is not None and (type(sigsys) is not dict or set(sigsys) != {"nr", "data", "arch"}
                                       or any(type(v) is not int for v in sigsys.values())):
                raise ValueError("seccomp probe sigsys record")
            if (op["where"] == "child") != (child is not None):
                raise ValueError("seccomp child record presence")
            if child is not None and (type(child) is not dict or (set(child) - {"strict_ret"}) not in ({"ret"}, {"exited"}, {"signal"})
                                      or any(type(v) is not int for v in child.values())
                                      or ("strict_ret" in child) != ("strict" in op)):
                raise ValueError("seccomp child record")
            if child is not None and "ret" in child and ret != 0:
                raise ValueError("seccomp child probe's own result")
        if op["op"] == "pipe2":
            fds = observation["fds"]
            limit = trace.get("rlimit_nofile", 32)
            if ret == 0:
                if (type(fds) is not list or len(fds) != 2 or any(type(fd) is not int or not 0 <= fd < limit for fd in fds)
                        or fds[0] == fds[1]):
                    raise ValueError("pipe2 descriptors")
            elif fds is not None:
                raise ValueError("pipe2 descriptors after a failure")


def attach_devices(results, traces, records):
    """Each successful wg_get and wg_get_recv has exactly one record of its
    messages (W2 4.5): a wg_get's are coalesced into the observation's
    canonical `device`; a wg_get_recv's are its `messages`, as decoded."""
    by_trace = {result["id"]: result for result in results}
    traced = {trace["id"]: trace for trace in traces}
    seen = set()
    for record in records:
        if type(record) is not dict or set(record) != {"id", "index", "messages"} or record["id"] not in by_trace:
            raise ValueError("wireguard record fields or identity")
        key = (record["id"], record["index"])
        observations = by_trace[record["id"]]["observations"]
        if key in seen or type(record["index"]) is not int or not 0 <= record["index"] < len(observations):
            raise ValueError("duplicate or out-of-range wireguard record")
        seen.add(key)
        messages = decode_messages(record["messages"])
        if traced[record["id"]]["ops"][record["index"]]["op"] == "wg_get_recv":
            observations[record["index"]]["messages"] = messages
        else:
            observations[record["index"]]["device"] = decode_dump(messages)
    for trace in traces:
        for index, op in enumerate(trace["ops"]):
            expected = op["op"] in ("wg_get", "wg_get_recv") and by_trace[trace["id"]]["observations"][index]["ret"] == 0
            if expected != ((trace["id"], index) in seen):
                raise ValueError("missing or unexpected wireguard dump record")


def attach_batches(results, traces, records):
    """W7: each wg_batch has exactly one record, the completions present when
    its io_uring_enter returned, by item: the send's result (its length or
    -errno), or null for an item without a completion yet."""
    by_trace = {result["id"]: result for result in results}
    seen = set()
    for record in records:
        if type(record) is not dict or set(record) != {"id", "index", "cqes"} or record["id"] not in by_trace:
            raise ValueError("wg_batch record fields or identity")
        key = (record["id"], record["index"])
        observations = by_trace[record["id"]]["observations"]
        if key in seen or type(record["index"]) is not int or not 0 <= record["index"] < len(observations):
            raise ValueError("duplicate or out-of-range wg_batch record")
        seen.add(key)
        cqes = record["cqes"]
        if type(cqes) is not list or not all(c is None or (type(c) is int and -4095 <= c < 2**31) for c in cqes):
            raise ValueError("wg_batch cqes")
        observations[record["index"]]["cqes"] = cqes
    for trace in traces:
        for index, op in enumerate(trace["ops"]):
            if (op["op"] == "wg_batch") != ((trace["id"], index) in seen):
                raise ValueError("missing or unexpected wg_batch record")


def message_index(hex_bytes):
    """The WireGuard message's index word at byte 4 (little-endian), 0 for a
    message too short to carry one."""
    return int.from_bytes(bytes.fromhex(hex_bytes[8:16]), "little") if len(hex_bytes) >= 16 else 0


def datagram_peer_key(datagram):
    """A listener datagram's peer key: [family, length, type, tos, bytes]."""
    return (datagram[0], message_index(datagram[4]))


def reply_peer_key(reply):
    """A sender-side reply's peer key: its source address and port and the
    message's index word ([10, addr, port, scope, tos, dst, length, type,
    word8, bytes])."""
    return (reply[1], reply[2], message_index(reply[9]))


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
        # W5: each datagram carries the TOS / traffic class its receiver's
        # cmsg reported (IP_RECVTOS, IPV6_RECVTCLASS; -1 without one):
        # [family, length, type, tos, bytes]; W8: null after wg_netns_close
        # (the listeners are gone; the mirror says null too)
        if datagrams is not None and (type(datagrams) is not list or not all(
                type(d) is list and len(d) == 5 and d[0] in (4, 6)
                and all(type(x) is int and x >= 0 for x in d[:3]) and type(d[3]) is int and -1 <= d[3] <= 255
                and hex_bytes(d, d[1])
                for d in datagrams)):
            raise ValueError("wg_observe datagrams")
        # what the sender received: recvmsg's source (the IPv6 socket's
        # family, the address as 32 hex digits, an IPv4 source v4-mapped, the
        # port, the scope id), the TOS, the destination IPV6_PKTINFO reported
        # (32 hex digits, zero for an IPv4 datagram), then length, message
        # type, receiver index and bytes (W5)
        replies = record["replies"]
        if type(replies) is not list or not all(
                type(r) is list and len(r) == 10 and r[0] == 10
                and type(r[1]) is str and re.fullmatch(r"[0-9a-f]{32}", r[1]) is not None
                and type(r[2]) is int and 0 <= r[2] < 65536 and type(r[3]) is int and r[3] >= 0
                and type(r[4]) is int and -1 <= r[4] <= 255
                and type(r[5]) is str and re.fullmatch(r"[0-9a-f]{32}", r[5]) is not None
                and all(type(x) is int and x >= 0 for x in r[6:9]) and hex_bytes(r, r[6])
                for r in replies):
            raise ValueError("wg_observe replies")
        # null: no wg0 (L; the guest maps exactly ENODEV to null). W5: the
        # device's tstats (rx_packets, rx_bytes; tx_* are constant 0).
        stats = record["stats"]
        if stats is not None and (type(stats) is not dict
                                  or set(stats) != {"tx_errors", "tx_dropped", "rx_frame_errors", "rx_length_errors",
                                                    "rx_packets", "rx_bytes", "tx_packets", "tx_bytes"}
                                  or not all(type(v) is int and v >= 0 for v in stats.values())):
            raise ValueError("wg_observe stats")
        # Ordered as the mirror orders them (Leanux/Env.lean, wg_observe): a
        # stable sort by the datagram's peer key, so that arrival order is
        # kept within a peer's session (the listener's family and the
        # message's index word at byte 4: the receiver index of a data or
        # cookie message, the sender index of a handshake message) while
        # the interleaving across peers, which the fixture does not
        # determine, is free (pre-release review, finding 5; before this a
        # global sort by compact JSON also lost within-peer order).
        observations[record["index"]]["datagrams"] = (sorted(datagrams, key=datagram_peer_key)
                                                      if datagrams is not None else None)
        observations[record["index"]]["stats"] = stats
        observations[record["index"]]["replies"] = sorted(replies, key=reply_peer_key)
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
    required = {(row["id"], row["index"]) for row in rows if type(row) is dict and row.get("id") in net}
    return merge_stream(rows, remote, required, key)


def merge_stream(rows, extra, required, key):
    """Append a second stream's record to each operation row in `required`
    ((id, index) keys), exactly one per such operation and none elsewhere:
    the row's entries first, then the stream's, deduplicated in
    first-execution order; the counts add. The remote stream (merge_remote)
    and the sandboxed child's stream (seccomp W) both merge this way."""
    by_key = {}
    for record in extra:
        if type(record) is not dict or set(record) != {"id", "index", "count", key}:
            raise ValueError("stream record fields")
        k = (record["id"], record["index"])
        if k not in required:
            raise ValueError(f"stream record for an operation without one: {k}")
        if k in by_key or type(record[key]) is not list:
            raise ValueError("duplicate stream record")
        by_key[k] = record
    merged, used = [], set()
    for row in rows:
        k = (row.get("id"), row.get("index")) if type(row) is dict else None
        if k and k in required:
            record = by_key.get(k)
            if record is None:
                raise ValueError(f"missing stream record for {k}")
            used.add(k)
            row = dict(row)
            seen = {json.dumps(x) for x in row[key]}
            row[key] = row[key] + [x for x in record[key] if json.dumps(x) not in seen]
            if type(record["count"]) is not int or record["count"] < 0:
                raise ValueError("remote record count")
            row["count"] = row["count"] + record["count"]
        merged.append(row)
    if used != set(by_key):
        raise ValueError("stream records without an operation")
    return merged


def _collect(outdir, traces, process_returncode, alloc=None):
    results, coverage, fixtures, errors, child_failures, completed, kernels = [], [], [], [], [], [], []
    comparisons, comparison_results, wireguard, observed = [], [], [], []
    batches = []   # W7: LEANUX_WGBATCH rows
    remote_coverage, remote_comparisons = [], []
    hidden, remote_hidden, steering, sections, clocksources, timing = [], [], [], [], [], []
    alloc_status, alloc_tsc = [], []
    epoll_rows = []   # epoll R: the warm-up and max_user_watches, once per boot
    child_coverage, child_comparisons, child_hidden = [], [], []   # seccomp W: the sandboxed child's streams
    for line in (outdir / "boot.log").read_text(errors="strict").splitlines():
        line = line.rstrip("\r")
        for prefix, target in (("LEANUX_RESULT ", results), ("LEANUX_COVERAGE ", coverage),
                               ("LEANUX_FIXTURE ", fixtures), ("LEANUX_ERROR ", errors),
                               ("LEANUX_CHILD_FAILURE ", child_failures), ("LEANUX_CMP ", comparisons),
                               ("LEANUX_CMP_RESULT ", comparison_results), ("LEANUX_WG ", wireguard),
                               ("LEANUX_WGOBS ", observed), ("LEANUX_WGBATCH ", batches), ("LEANUX_RCOVERAGE ", remote_coverage),
                               ("LEANUX_RCMP ", remote_comparisons), ("LEANUX_HIDDEN ", hidden),
                               ("LEANUX_RHIDDEN ", remote_hidden), ("LEANUX_STEER ", steering),
                               ("LEANUX_SECTIONS ", sections), ("LEANUX_CLOCKSOURCE ", clocksources),
                               ("LEANUX_TIMING ", timing),
                               ("LEANUX_ALLOC ", alloc_status), ("LEANUX_ALLOC_TSC ", alloc_tsc),
                               ("LEANUX_EPOLL ", epoll_rows),
                               ("LEANUX_CCOVERAGE ", child_coverage), ("LEANUX_CCMP ", child_comparisons),
                               ("LEANUX_CHIDDEN ", child_hidden)):
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
    _jsonl(outdir / "timing.jsonl", timing)
    # The timekeeper's clocksource at batch start and end (D3): both the
    # expected one, or the batch is not a run of the oracle.
    _jsonl(outdir / "clocksource.jsonl", clocksources)
    if (len(clocksources) != 2 or [r.get("at") if type(r) is dict else None for r in clocksources] != ["start", "end"]
            or any(set(r) != {"at", "current", "available"} or r["current"] != EXPECTED_CLOCKSOURCE for r in clocksources)):
        raise LinuxRunError("environment_failure", f"Timekeeper clocksource is not {EXPECTED_CLOCKSOURCE} at batch start and end", outdir)
    # epoll R: exactly one fixture row per boot, the warm-up done and
    # max_user_watches the value the mirror assumes (fail-closed, like the
    # clocksource and the kernel identity)
    _jsonl(outdir / "epoll-fixture.jsonl", epoll_rows)
    if len(epoll_rows) != 1 or type(epoll_rows[0]) is not dict or set(epoll_rows[0]) != {"max_user_watches", "warmup"} \
            or epoll_rows[0]["warmup"] != 1 or type(epoll_rows[0]["max_user_watches"]) is not int:
        raise LinuxRunError("invalid_output", "epoll fixture row missing or malformed", outdir)
    if epoll_rows[0]["max_user_watches"] != EXPECTED_MAX_USER_WATCHES:
        raise LinuxRunError("environment_failure", f"max_user_watches is {epoll_rows[0]['max_user_watches']} in this boot, "
                            f"not the {EXPECTED_MAX_USER_WATCHES} the mirror assumes (harness/linux.py EXPECTED_MAX_USER_WATCHES)", outdir)
    try:
        coverage = merge_remote(coverage, remote_coverage, traces, "pcs")
        comparisons = merge_remote(comparisons, remote_comparisons, traces, "records")
        # seccomp W (design 6.2 rule 2): a child probe's operation carries the
        # sandboxed child's stream too (its own KCOV area), merged like the
        # remote stream: exactly one child row per child-probe operation
        child_ops = {(t["id"], i) for t in traces for i, op in enumerate(t["ops"])
                     if op["op"] == "seccomp_probe" and op["where"] == "child"}
        coverage = merge_stream(coverage, child_coverage, child_ops, "pcs")
        comparisons = merge_stream(comparisons, child_comparisons, child_ops, "records")
    except ValueError as exc:
        raise LinuxRunError("invalid_output", f"Remote or child coverage: {exc}", outdir) from exc
    _jsonl(outdir / "coverage.jsonl", coverage)
    # Choices (docs/2026-10-03-choice-stream-strategy.md): one task row and,
    # with remote coverage, one remote row per network operation and child;
    # each record is [kind, call site, sequence number, length, value hex].
    for row in hidden + remote_hidden + child_hidden:
        if (type(row) is not dict or set(row) != {"id", "index", "mode", "records"} or row["mode"] not in ("pc", "cmp")
                or type(row["records"]) is not list
                or any(type(r) is not list or len(r) != 5 or type(r[0]) is not int or type(r[1]) is not str
                       or type(r[2]) is not int or type(r[3]) is not int or type(r[4]) is not str
                       or len(r[4]) != 2 * min(r[3], 40)
                       for r in row["records"])):
            raise LinuxRunError("invalid_output", "Malformed hidden-input record", outdir)
    if sorted((r["id"], r["index"], r["mode"]) for r in child_hidden) != sorted((i, k, m) for i, k in child_ops for m in ("pc", "cmp")):
        raise LinuxRunError("invalid_output", "Child choice rows missing, extra or repeated", outdir)
    _jsonl(outdir / "hidden.jsonl", [dict(r, stream="task") for r in hidden] + [dict(r, stream="remote") for r in remote_hidden]
           + [dict(r, stream="child") for r in child_hidden])
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
    _jsonl(outdir / "timing.jsonl", timing)
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
        "roles": {"0": "console stdin", "1": "console stdout", "2": "console stderr", "3": "KCOV", "4-7": "/dev/null filler; in network traces 4-5 UDP listeners, 6 UDP sender, 7 generic netlink", "8+": "wg_create/wg_delete: a temporary rtnetlink socket at the lowest free descriptor, open only around the operation"},
        "per_trace": fixtures, "kernel_releases": kernels,
        "epoll": epoll_rows[0],   # epoll R: the boot's warm-up and max_user_watches
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
    # W5 (D2 [USER 2026-10-07]): the network fixture's sysctls and the
    # link-local address on lo, read back by the guest per network trace; a
    # trace run against another fixture is an environment failure, not a
    # silent change of verdicts.
    net_ids = {t["id"] for t in traces if uses_wireguard(t)}
    for row in fixtures:
        if type(row) is not dict or "id" not in row:
            raise LinuxRunError("invalid_output", "Malformed fixture row", outdir)
        if (row["id"] in net_ids) != ("net" in row) or ("net" in row and row["net"] != EXPECTED_NET_FIXTURE):
            raise LinuxRunError("environment_failure", f"Network fixture facts differ from {EXPECTED_NET_FIXTURE}: {row}", outdir)
    # L: the wall time of each lifecycle operation (wg_create, wg_down,
    # wg_delete), one row per child (timing.jsonl; checked once the batch
    # completed, so a failed trace reports its own error).
    # D3: the per-child margin to the rekey bound (`since_up_ns`, a child that
    # brought wg0 up), at most one row per trace and child [AGENT, int-dl
    # merge: both streams write LEANUX_TIMING rows; each kind is checked].
    margins = [r for r in timing if type(r) is dict and "since_up_ns" in r]
    timing = [r for r in timing if not (type(r) is dict and "since_up_ns" in r)]
    ids = {t["id"] for t in traces}
    if (any(set(r) != {"id", "mode", "since_up_ns"} or r["id"] not in ids or r["mode"] not in ("pc", "cmp")
            or type(r["since_up_ns"]) is not int for r in margins)
            or len({(r["id"], r["mode"]) for r in margins}) != len(margins)):
        raise LinuxRunError("invalid_output", "Rekey-bound margin rows malformed or repeated", outdir)
    lifecycle = {OPCODES[name]: name for name in ("wg_create", "wg_down", "wg_delete")}
    expected_timing = sorted((t["id"], i, m) for t in traces for i, op in enumerate(t["ops"])
                             if op["op"] in lifecycle.values() for m in ("pc", "cmp"))
    if (any(type(r) is not dict or set(r) != {"id", "index", "mode", "op", "ns"} or r["op"] not in lifecycle
            or type(r["ns"]) is not int or r["ns"] < 0 for r in timing)
            or sorted((r["id"], r["index"], r["mode"]) for r in timing) != expected_timing
            or any(next(t for t in traces if t["id"] == r["id"])["ops"][r["index"]]["op"] != lifecycle[r["op"]]
                   for r in timing)):
        raise LinuxRunError("invalid_output", "Lifecycle timing rows missing or malformed", outdir)
    expected_coverage = [(trace["id"], i) for trace in traces for i in range(len(trace["ops"]))]
    if len(coverage) != len(expected_coverage):
        raise LinuxRunError("missing_coverage", "Missing or extra per-operation coverage", outdir)
    try:
        attach_devices(results, traces, wireguard)
        attach_observed(results, traces, observed)
        attach_batches(results, traces, batches)
        for result, trace, fixture in zip(results, traces, fixtures):
            _check_observation(result, trace)
            limit = trace.get("rlimit_nofile", 32)
            # W8: the foreign-creator fixture adds the injector (8) and the pin (9);
            # W2: a stepped dump's socket is 8; seccomp W: the child fixture's KCOV
            # descriptor is 8 (the validator keeps the two apart)
            reserved = 10 if trace.get("net_fixture") == "foreign-creator" \
                else 9 if is_stepped(trace) or trace.get("seccomp_child") else 8
            expected = {"id": trace["id"], "reserved": list(range(reserved)), "free": [reserved, limit - 1], "rlimit": [limit, limit]}
            if uses_wireguard(trace):
                expected["net"] = EXPECTED_NET_FIXTURE   # W5: the network namespace's facts
            if fixture != expected:
                raise ValueError("fixture mismatch")
        for row, (identifier, index) in zip(coverage, expected_coverage):
            if type(row) is not dict or set(row) != {"id", "index", "count", "pcs"} or row["id"] != identifier or type(row["index"]) is not int or row["index"] != index:
                raise ValueError("coverage identity or order")
            pcs = row["pcs"]
            # a network row adds the remote stream's count; each stream stays
            # below CAPACITY - 1 (the guest fails a full area)
            if type(row["count"]) is not int or not 1 <= row["count"] < 2 * (KCOV_CAPACITY - 1) or type(pcs) is not list or not 1 <= len(pcs) <= row["count"]:
                raise ValueError("coverage count")
            if any(type(pc) is not str or not re.fullmatch(r"0x[0-9a-f]{1,16}", pc) for pc in pcs) or len(set(pcs)) != len(pcs):
                raise ValueError("coverage addresses")
        if len(comparisons) != len(expected_coverage):
            raise ValueError("comparison records per operation")
        for row, (identifier, index) in zip(comparisons, expected_coverage):
            if type(row) is not dict or set(row) != {"id", "index", "count", "records"} or row["id"] != identifier or row["index"] != index:
                raise ValueError("comparison identity or order")
            # a merged row is the task stream (its area twice the size, B1) and
            # the remote stream, each below its own limit (the guest fails a
            # full area), so the sum is below the sum of the limits
            if type(row["count"]) is not int or not 1 <= row["count"] < (KCOV_TASK_CMP_CAPACITY - 1) // 4 + (KCOV_CAPACITY - 1) // 4 \
                    or not 1 <= len(row["records"]) <= row["count"]:
                raise ValueError("comparison record count")
            if len({tuple(r) for r in row["records"]}) != len(row["records"]):
                raise ValueError("duplicate comparison records")
            # a remote record carries the dispatch-section blocks it occurred
            # in as a fifth element, ranges of block numbers (W7 stream H,
            # docs/2026-10-06-w4-w7-transmit-bulk.md 13.2 (ii)); a task
            # record has none
            if type(row["records"]) is not list or not all(
                    type(r) is list and len(r) in (4, 5) and type(r[0]) is int and 0 <= r[0] < 8
                    and all(type(x) is str and re.fullmatch(r"0x[0-9a-f]{1,16}", x) for x in r[1:4])
                    and (len(r) == 4 or (type(r[4]) is str and re.fullmatch(r"[1-9][0-9]*(-[1-9][0-9]*)?(,[1-9][0-9]*(-[1-9][0-9]*)?)*", r[4])))
                    for r in row["records"]):
                raise ValueError("comparison records")
    except (ValueError, TypeError, KeyError, IndexError) as exc:
        raise LinuxRunError("invalid_output", str(exc), outdir) from exc
    # The comparison child reruns each trace independently; its results must
    # be identical, or the comparison records do not describe this run.
    for result, again in zip(results, comparison_results):
        observations = result["observations"]
        if again != {"id": result["id"], "rets": [o["ret"] for o in observations],
                     "bytes": [o["bytes"] for o in observations], "fds": [o.get("fds") for o in observations],
                     "digest": [o.get("digest") for o in observations],
                     "sigpipe": [o.get("sigpipe") for o in observations],
                     "sigsys": [o.get("sigsys") for o in observations],   # seccomp W
                     "child": [o.get("child") for o in observations]}:
            raise LinuxRunError("environment_failure", f"Nondeterministic rerun of {result['id']}", outdir)
    unexpected_errors = {4, 12, 23, 512, 513, 514, 516}
    # A2: a trace under the declared failslab-style extension forces
    # task-context allocation failures, so its ENOMEM is the expected result
    # of the schedule (compared with the mirror, evaluator/protocol.py), not
    # allocator pressure; so is pipe2's ENFILE (a forced alloc_pipe_info
    # failure, A section 19.6). Every other trace still fails on them.
    forced = {12, 23}
    # seccomp W (design 2.4): an install's ENOMEM is the path budget
    # (MAX_INSNS_PER_PATH), a semantic result the mirror predicts; a real
    # allocation failure there shows as a mirror mismatch, not as pressure
    # pre-release review finding 11: EINTR, ENOMEM, ENFILE and the restart
    # codes are ordinary seccomp policy results; a self probe's errno is the
    # policy's when an earlier install in the trace can return it (a RET
    # ERRNO with that data), which is provenance, not a tolerance
    if any(row["errno"] in unexpected_errors - (forced if trace.get("domain_extension") == "failslab" else set())
           - ({12} if trace["ops"][row["index"]]["op"] == "seccomp_install" else set())
           and not _seccomp_policy_errno(trace, row["index"], row["errno"])
           for result, trace in zip(results, traces) for row in result["observations"]):
        raise LinuxRunError("environment_failure", "Unexpected interruption or allocator resource failure", outdir)
    return results


def _seccomp_policy_errno(trace, index, errno):
    """Whether ops[index] is a seccomp probe whose errno an earlier install's
    program can return (a RET K with SECCOMP_RET_ERRNO and that data): then
    the errno is the filter's answer, not the guest failing."""
    ops = trace["ops"]
    if ops[index]["op"] != "seccomp_probe":
        return False
    return any(insn[0] == 0x06 and insn[3] & 0xffff0000 == 0x00050000 and insn[3] & 0xffff == errno
               for op in ops[:index] if op["op"] == "seccomp_install" and op.get("filter")
               for insn in op["filter"])


def run_linux(traces, outdir, *, timeout=120, steer_wire=None, arm_records=ARM_RECORDS, guest_variant=None, alloc=None):
    """Return ordered observations; preserve evidence and raise on execution failures.

    `outdir` must be a fresh/empty directory within the task's artifact root.
    One VM executes the batch, forking a fresh child for every trace. Independent
    calls boot fresh VMs. The project-wide advisory lock prevents overlapping VMs.
    """
    if guest_variant is not None and guest_variant not in GUEST_VARIANTS:
        raise ValueError(f"unknown guest variant {guest_variant!r}")
    traces = [validate_trace(trace) for trace in traces]
    dispatch = dispatch_addresses() if any(uses_wireguard(t) for t in traces) else []
    wire = serialize_wire(traces, steer_wire, dispatch, arm_records, alloc, arm_masks(traces))
    outdir = Path(outdir).resolve()
    if not outdir.is_relative_to(ARTIFACTS):
        raise ValueError(f"outdir must be within task artifact root {ARTIFACTS}")
    outdir.mkdir(parents=True, exist_ok=True)
    if any(outdir.iterdir()):
        raise ValueError(f"outdir must be empty: {outdir}")
    _jsonl(outdir / "inputs.jsonl", traces)
    (outdir / "wire.txt").write_text(wire)
    identity = verify_kernel(outdir=outdir)   # before a slot is taken: no boot of another build
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
                return _run_locked(traces, outdir, timeout, arm_records, guest_variant, alloc, identity)
        if time.monotonic() >= deadline:
            raise LinuxRunError("resource_busy", f"Other guests held all {QEMU_SLOTS} QEMU slots for {QEMU_LOCK_WAIT} s", outdir)
        if not waited:
            print(f"waiting for one of {QEMU_SLOTS} QEMU slots ({runs}), up to {QEMU_LOCK_WAIT} s", file=sys.stderr, flush=True)
            waited = True
        time.sleep(2)


QEMU_LOCK_WAIT = 3600
# Concurrent guests (single-threaded TCG, 256 MiB each); LEANUX_QEMU_SLOTS overrides.
QEMU_SLOTS = int(os.environ.get("LEANUX_QEMU_SLOTS", "8"))


def _run_locked(traces, outdir, timeout, arm_records, guest_variant=None, alloc=None, kernel_identity=None):
    build = ["gcc", "-static", "-O2", "-Wall", "-Wextra", "-Werror", "-std=c11", *GUEST_VARIANTS.get(guest_variant, ()), str(ROOT / "harness/guest.c"), "-o", str(outdir / "guest-runner")]
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
    # The run's inputs that decide its verdict: the kernel (its identity, checked
    # before the boot), the guest build and boot commands, the budgets. No
    # certificate beyond that: the mirror, the harness and the tools are git state.
    provenance = {"schema_version": 2, "expected_clocksource": EXPECTED_CLOCKSOURCE, "arm_records": arm_records, "guest_variant": guest_variant, "alloc": alloc or {"flags": 0, "ranges": []}, "kernel_identity": kernel_identity, "build_command": build, "cpio_command": cpio_command, "qemu_command": command, "timeout_seconds": timeout, "captured_output_limit_bytes": OUTPUT_LIMIT}
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
