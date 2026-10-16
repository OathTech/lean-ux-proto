"""Strict, dependency-free validation and guest serialization of trace v1."""
from copy import deepcopy
import json
import struct
import re

from .wg import InvalidConfig, encode_get, encode_packet, encode_set, validate_config, validate_device, validate_packet


class InvalidTrace(ValueError):
    kind = "invalid_input"


class UnsupportedTrace(InvalidTrace):
    kind = "unsupported_input"


PRODUCERS = {"eventfd2", "dup", "dup3", "epoll_create1"}   # epoll R: a set is a descriptor producer
FIELDS = {
    "eventfd2": {"op", "init", "flags"}, "dup": {"op", "fd"},
    "dup3": {"op", "fd", "newfd", "flags"}, "close": {"op", "fd"},
    "read": {"op", "fd", "count"}, "write": {"op", "fd", "count", "value"},
    "fcntl": {"op", "fd", "cmd", "arg"},
    # WireGuard configuration of the fixture's `wg0` (harness/wg.py)
    "wg_set": {"op", "config"}, "wg_get": {"op"},
    # W2 (docs/2026-10-06-w1-w2-netlink.md 4.2): the stepped dump on the
    # fixture's second generic-netlink socket (fd 8): the request (+ optional
    # "device" selector) and one recvmsg of one chunk or acknowledgement
    "wg_get_start": {"op"}, "wg_get_recv": {"op"},
    # Stage B1: bring wg0 up, send a packet into it, observe what it emitted
    "wg_up": {"op"}, "wg_xmit": {"op", "packet"}, "wg_observe": {"op"},
    # Stage B2: a raw WireGuard message sent to wg0's listen port
    "wg_inject": {"op", "family", "port", "message"},   # + optional "to" (W9), validated below
    # D3: the virtual time advance by `ticks` jiffies (docs/2026-10-05-d3-timers.md, 4.3)
    "wg_advance": {"op", "ticks"},
    # E-B: an io_uring flood of `count` invalid-MAC1 initiations to wg0's
    # `port`, to cross the under_load threshold (docs/2026-10-05-e-dos.md §8).
    # `messages` (optional, 0 or 1 entry) bundles a valid initiation into the
    # same io_uring batch, for the merged-injection negative control.
    "wg_flood": {"op", "count", "port"},
    # L: wg0's lifecycle (docs/2026-10-05-l-lifecycle.md section 6): RTM_NEWLINK,
    # SIOCSIFFLAGS without IFF_UP, RTM_DELLINK
    "wg_create": {"op"}, "wg_down": {"op"}, "wg_delete": {"op"},
    # W9 (docs/2026-10-06-w8-w9-netns-routing.md 4.3): RTM_DELADDR of wg0's
    # fixture address and RTM_DELROUTE of the default route via wg0, per
    # family, over L's temporary rtnetlink socket; the result is the ACK
    "wg_deladdr": {"op", "family"}, "wg_delroute": {"op", "family"},
    # Lane C (docs/2026-10-15-design-c-fib-trie.md, 10): over the same socket,
    # RTM_NEWROUTE of an IPv4 route (type unicast via `oif` wg0 or lo, or
    # unreachable, blackhole, prohibit without a device; optional metric, mtu
    # and the NLM_F_ flags excl, replace, append as `nlflags`) and RTM_NEWADDR of another
    # IPv4 address on wg0; wg_delroute takes an optional destination with its
    # prefix, oif, type and metric (without them, the default route via wg0).
    # The result is the acknowledgement's error; the trie's shape follows.
    "wg_addroute": {"op", "family", "dst", "plen", "type"}, "wg_addaddr": {"op", "addr", "plen"},
    # W8 (docs/2026-10-06-w8-w9-netns-routing.md 3.2): in the foreign-creator
    # fixture, close the creating namespace's holders (the injector, the
    # listeners, then the pin) and wait for its teardown; the result is 0
    "wg_netns_close": {"op"},
    # P (pipes, docs/2026-10-05-p-pipes.md section 6)
    "pipe2": {"op", "flags"},
    # W4 (docs/2026-10-06-w4-w7-transmit-bulk.md section 6): SIOCSIFMTU on wg0
    "wg_set_mtu": {"op", "mtu"},
    # W7 (section 5.5): one io_uring_enter of `items` (injects to wg0's port
    # and transmits into wg0) from the fixture's sender; `wait_ms` optional
    "wg_batch": {"op", "items"},
    # epoll stream R (docs/2026-10-12-epoll-design.md section 6; contracts/trace-v1.md):
    # a set (a producer); an item operation on set `epfd` for target `fd`
    # (cmd 1 ADD, 2 DEL, 3 MOD, any u32; events u32; data a u64 decimal
    # string); a wait of 1-16 events with timeout 0 (tier 1: no sleep record)
    "epoll_create1": {"op", "flags"},
    "epoll_ctl": {"op", "epfd", "cmd", "fd", "events", "data"},
    "epoll_wait": {"op", "epfd", "maxevents", "timeout"},
    # seccomp stream W (docs/2026-10-12-seccomp-design.md section 6.1;
    # contracts/trace-v1.md, Seccomp): a filter install through seccomp(2) or
    # prctl; a probe call in the trace process or a sandboxed child; the
    # no-new-privs and mode queries; the CAP_SYS_ADMIN drop; the two
    # seccomp(2) queries. Optional fields: SECCOMP_OPTIONAL.
    "seccomp_install": {"op", "via", "flags", "filter"},
    "seccomp_probe": {"op", "nr", "where"},
    "seccomp_prctl": {"op", "cmd"},
    "seccomp_capdrop": {"op"},
    "seccomp_query": {"op", "cmd"},
}
SECCOMP_OPTIONAL = {"seccomp_install": {"len", "bad", "mode"}, "seccomp_probe": {"args", "strict"},
                    "seccomp_prctl": {"arg2", "arg3", "arg4", "arg5"}, "seccomp_query": {"action", "flags"}}
SECCOMP_OPS = set(SECCOMP_OPTIONAL) | {"seccomp_capdrop"}
# the install's flags by name (the kernel's SECCOMP_FILTER_FLAG_*); an
# integer element is a raw bit for the flag-mask arm
SECCOMP_FLAGS = {"tsync": 1, "log": 2, "spec_allow": 4, "new_listener": 8, "tsync_esrch": 16, "wait_killable_recv": 32}
SECCOMP_BAD = {"fprog": 1, "insns": 2}       # bad 3 is the NULL instruction pointer (filter null)
SECCOMP_VIA = {"seccomp": 0, "prctl": 1}
SECCOMP_WHERE = {"self": 0, "child": 1}
SECCOMP_STRICT = {"seccomp": 1, "prctl": 2}
SECCOMP_PRCTL = {"set_no_new_privs": 0, "get_no_new_privs": 1, "get_seccomp": 2}
SECCOMP_QUERY = {"get_action_avail": 0, "get_notif_sizes": 1}
BPF_MAXINSNS = 4096
# The self-sandboxing rule (design 6.2 rule 1): a filter may restrict only
# the probe set, so the harness's own calls are constant-allowed cache
# hits; a strict child may probe exit (60), the one call it reports through
SECCOMP_PROBE_SET = {102, 104, 107, 108, 1000, 335}
# seccomp X (design 5): the prefill fixture's bound; the ninth copy of the
# 3990-instruction program would itself exceed MAX_INSNS_PER_PATH
SECCOMP_PREFILL_MAX = 8
SECCOMP_STRICT_PROBE_SET = SECCOMP_PROBE_SET | {60}
# the return actions the kill scan (design 6.1) accepts for a self probe:
# ALLOW, LOG, TRACE (no tracer: -ENOSYS), ERRNO, TRAP (a handler)
SECCOMP_RET_ACTION_FULL = 0xffff0000
SECCOMP_SAFE_ACTIONS = {0x7fff0000, 0x7ffc0000, 0x7ff00000, 0x00050000, 0x00030000}
BPF_RET_K, BPF_RET_A, BPF_DIV_X = 0x06, 0x16, 0x3c


def filter_may_kill(instructions):
    """The validator's conservative scan (design 6.1): a RET|K whose action
    is not one of the five safe ones (KILL_THREAD, KILL_PROCESS, USER_NOTIF
    or a non-canonical action), a RET|A (the accumulator may hold anything,
    0 included), or a DIV|X (a zero X returns 0 = KILL_THREAD through the
    translation's guard). MOD is not scanned: seccomp_check_filter rejects
    MOD|X and MOD|K at the install (kernel/seccomp.c:280-347 lists DIV, not
    MOD), so such a program never runs."""
    for code, _jt, _jf, k in instructions or ():
        if code == BPF_RET_K and (k & SECCOMP_RET_ACTION_FULL) not in SECCOMP_SAFE_ACTIONS:
            return True
        if code in (BPF_RET_A, BPF_DIV_X):
            return True
    return False
EPOLL_MAXEVENTS = (1, 16)   # tier 1's bound on epoll_wait's maxevents (the kernel's is EP_MAX_EVENTS)
LIFECYCLE_OPS = ("wg_create", "wg_down", "wg_delete")
WG_OPS = {"wg_set", "wg_get", "wg_up", "wg_xmit", "wg_observe", "wg_inject", "wg_advance",
          "wg_flood", "wg_set_mtu", "wg_batch", "wg_deladdr", "wg_delroute", "wg_netns_close",
          "wg_addroute", "wg_addaddr",
          "wg_get_start", "wg_get_recv"} | set(LIFECYCLE_OPS)
STEPPED_OPS = ("wg_get_start", "wg_get_recv")
# W9: `wg_inject`'s optional destination ("to"): the fixture's loopback
# address (the default, 127.0.0.1 / ::1), wg0's own fixture address
# (10.255.254.1 / fd00:ffff::1, reached over the local route: wg0 learns an
# endpoint at that address), or the loopback alias 127.0.0.2 (IPv4 only: a
# local address that is not configured, so wg0's reply source check fails).
# The wire carries the code in bits 9-10 of the operation's value field
# (bits 0-7 the TOS and bit 8 the link-local source, W5).
INJECT_DESTINATIONS = {"loopback": 0, "wg0": 1, "loopback-alias": 2}
# Wire opcodes: an explicit table, not FIELDS' order (a positional derivation
# gave P's pipe2 and D3's wg_advance the same code, 14). harness/guest.c
# mirrors it as OP_* #defines; harness/test_trace.py checks that the codes
# are distinct and that the guest's agree. [AGENT, coordinator, D3 merge]
# L's operations take their reserved codes 15-17 [AGENT, coordinator's
# table, int-dl merge]; E-B's wg_flood takes its reserved code 18 [AGENT,
# int-e merge].
OPCODES = {
    "eventfd2": 1, "dup": 2, "dup3": 3, "close": 4, "read": 5, "write": 6, "fcntl": 7,
    "wg_set": 8, "wg_get": 9, "wg_up": 10, "wg_xmit": 11, "wg_observe": 12, "wg_inject": 13,
    "pipe2": 14,
    "wg_create": 15, "wg_down": 16, "wg_delete": 17,
    "wg_flood": 18,
    "wg_advance": 19,
    "wg_get_start": 20, "wg_get_recv": 21,   # W2
    "wg_netns_close": 22,   # W8
    "wg_deladdr": 23, "wg_delroute": 24,   # W9
    "wg_addroute": 35, "wg_addaddr": 36,   # lane C (docs/2026-10-15-design-c-fib-trie.md, 10)
    # W4+W7: allocated by the coordinator (docs/2026-10-11-interface.md)
    "wg_set_mtu": 25,
    "wg_batch": 26,
    # epoll R: allocated by the coordinator (docs/2026-10-11-interface.md, next targets)
    "epoll_create1": 27, "epoll_ctl": 28, "epoll_wait": 29,
    # seccomp W: allocated by the coordinator (docs/2026-10-11-interface.md, next targets)
    "seccomp_install": 30, "seccomp_probe": 31, "seccomp_prctl": 32, "seccomp_capdrop": 33, "seccomp_query": 34,
}
# Reserved wire opcodes (the interface commit, docs/2026-10-11-interface.md),
# allocated by the coordinator so the W streams' worktrees cannot clash. A
# reserved code names no operation: traces carry names, so no such code
# reaches the wire from here; the guest fails one as invalid_input
# (harness/guest.c, the opcode switch's default) and the mirror as an
# unknown operation. A stream moves its codes into OPCODES when it lands.
RESERVED_OPCODES = {}   # W2 took 20-21, W8 22, W9 23-24, W4 25, W7 26
if set(OPCODES.values()) & set(RESERVED_OPCODES):
    raise AssertionError(f"reserved opcodes in use: {set(OPCODES.values()) & set(RESERVED_OPCODES)}")
if set(OPCODES) != set(FIELDS):
    raise AssertionError(f"OPCODES and FIELDS name different operations: {set(OPCODES) ^ set(FIELDS)}")
# The guest's KCOV area in words, task and remote (harness/guest.c CAPACITY):
# KCOV stops at CAPACITY - 1 PCs or (CAPACITY - 1) // 4 comparison records,
# and the guest fails an operation whose area filled. The comparison child's
# task area is twice that (guest.c TASK_CMP_CAPACITY; B1, a flood past the
# handshake ring's 4096 slots has about 1.41 M task-side comparison records):
# its limit is (KCOV_TASK_CMP_CAPACITY - 1) // 4 records, and a merged
# comparison row (task and remote) stays below the sum of the two limits.
KCOV_CAPACITY = 4 * 1024 * 1024
KCOV_TASK_CMP_CAPACITY = 8 * 1024 * 1024
# Only a trace with a flood of more than this many sends gets the larger
# area (guest.c task_capacity): the mapping is shared with every process the
# trace forks, and fork copies its page tables, work the comparison child
# records as one distinct comparison per page, which at twice the pages took
# the seccomp probes' rows past the captured-output limit.
FLOOD_BIG_AREA_SENDS = 2048


def task_cmp_capacity(trace):
    """The comparison child's task area for this trace, in words (B1,
    guest.c task_capacity): KCOV_TASK_CMP_CAPACITY when a flood's sends (its
    count, leading valids and control) exceed FLOOD_BIG_AREA_SENDS, else
    KCOV_CAPACITY."""
    for op in trace["ops"]:
        if op["op"] == "wg_flood" and \
                op["count"] + len(op.get("messages", ())) + (1 if op.get("control") else 0) > FLOOD_BIG_AREA_SENDS:
            return KCOV_TASK_CMP_CAPACITY
    return KCOV_CAPACITY
# The optional top-level `net_fixture` (L): "bare" starts a network trace
# without wg0; absent, the fixture creates a down wg0. W8: "foreign-creator"
# creates wg0 from a second namespace C (its creating namespace), which holds
# the listeners (4, 5), an injector (8) and a pin (9); the trace's one
# `wg_netns_close` drops them (docs/2026-10-06-w8-w9-netns-routing.md 3.1).
# W4: an object {"routes": [{"family", "dst", "mtu"}]} keeps wg0 and adds, at
# every wg_up, a host route into wg0 with that MTU for each destination (1-8).
NET_FIXTURES = ("bare", "foreign-creator")
MAX_FIXTURE_ROUTES = 8
# fcntl commands: the wire carries the command number itself
# (F_LINUX_SPECIFIC_BASE = 1024: F_SETPIPE_SZ = 1031, F_GETPIPE_SZ = 1032)
FCNTL = {"F_GETFD": 1, "F_SETFD": 2, "F_GETFL": 3, "F_SETFL": 4, "F_SETPIPE_SZ": 1031, "F_GETPIPE_SZ": 1032}

# The pipes trace contract (P design section 6). A descriptor argument is
# {"literal": n}, {"ref": i} naming an eventfd2/dup/dup3, or {"pipe": i,
# "end": e} naming end e of the pipe2 at index i (0: fd[0], the read end; 1:
# fd[1], the write end). A failed producer resolves to -1. Wire kinds:
FD_KIND_LITERAL, FD_KIND_REF, FD_KIND_PIPE_READ, FD_KIND_PIPE_WRITE = 0, 1, 2, 3
PIPE_PRODUCERS = {"pipe2"}
# read/write byte counts: 17 pages, so one write overfills the default ring
MAX_IO = 69632
# Any operation may carry "pause_ms" (1-20): the guest sleeps that long before
# the operation's coverage reset (a ninth wire field, 0 when absent); the
# mirror ignores it.
# W5 (docs/2026-10-06-w5-w6-receive.md, section 6): `tos` (0-255) on
# `wg_inject` (the outer DS field of the injection, set on the sender before
# the operation) and `wg_xmit` (the inner TOS of the transmitted packet);
# `from: "ll"` on an IPv6 `wg_inject`: the sender transmits from the
# link-local address fe80::1 on lo (IPV6_PKTINFO), so wg0 learns a scoped
# endpoint.
OPTIONAL_OP_FIELDS = {"pause_ms", "tos", "from"}
# Lane C: a route's optional device, metric, MTU and NLM_F_ flags; a
# delroute's optional named route
ROUTING_OPTIONAL = {"wg_addroute": {"oif", "metric", "mtu", "nlflags"},
                    "wg_delroute": {"dst", "plen", "oif", "type", "metric"}}
ROUTE_TYPES = {"unicast": 1, "unreachable": 7, "blackhole": 6, "prohibit": 8}   # RTN_*
ROUTE_OIFS = {"lo": 1, "wg0": 2}   # the wire's device code (the guest knows wg0's ifindex)
ROUTE_FLAGS = {"excl": 1, "replace": 2, "append": 4}
SENDER_TOS = (0, 255)
PAUSE_MS = (1, 20)
# W1 (docs/2026-10-06-w1-w2-netlink.md, 3.1): the optional device selector
# of the netlink operations ({"ifname": s} | {"ifindex": n} | both | {};
# absent means wg0 by name), validated by harness/wg.py.
DEVICE_OPS = {"wg_set", "wg_get", "wg_get_start"}
# The guest (harness/guest.c) implements the pipes contract: pipe2, the pipe
# descriptor kinds, F_SETPIPE_SZ/F_GETPIPE_SZ, pause_ms and counts up to
# MAX_IO (stream P1). With this off, such traces are rejected as unsupported
# (fail closed), counts stay within the old guest's 16-byte buffer, and the
# wire has no ninth field.
GUEST_PIPES = True
LEGACY_IO = 16


def _hex_addr4(value, where):
    if type(value) is not str or not re.fullmatch(r"[0-9a-f]{8}", value, re.ASCII):
        raise InvalidTrace(f"{where}: expected 8 lowercase hex digits")


def _validate_route(op, where, add):
    """Lane C: a route's destination and prefix (host bits clear: the trie
    keys a prefix), type, device, metric, MTU and flags. A unicast route
    names its device, a reject type none (the kernel refuses one)."""
    _hex_addr4(op["dst"], f"{where}.dst")
    _integer(op["plen"], 0, 32, f"{where}.plen")
    dst, plen = int(op["dst"], 16), op["plen"]
    if plen < 32 and dst & ((1 << (32 - plen)) - 1):
        raise InvalidTrace(f"{where}.dst: host bits set for /{plen}")
    if "type" in op and op["type"] not in ROUTE_TYPES:
        raise InvalidTrace(f"{where}.type: expected one of {list(ROUTE_TYPES)}")
    if "oif" in op and op["oif"] not in ROUTE_OIFS:
        raise InvalidTrace(f"{where}.oif: expected wg0 or lo")
    if add:
        if op["type"] == "unicast" and "oif" not in op:
            raise InvalidTrace(f"{where}: a unicast route needs oif")
        if op["type"] != "unicast" and "oif" in op:
            raise InvalidTrace(f"{where}: a {op['type']} route takes no oif")
        if "mtu" in op:
            _integer(op["mtu"], 68, 65535, f"{where}.mtu")
        flags = op.get("nlflags", [])
        if type(flags) is not list or any(f not in ROUTE_FLAGS for f in flags) or len(set(flags)) != len(flags):
            raise InvalidTrace(f"{where}.nlflags: expected distinct names among {list(ROUTE_FLAGS)}")
    if "metric" in op:
        _integer(op["metric"], 0, 2**32 - 1, f"{where}.metric")


def _integer(value, low, high, where):
    if type(value) is not int or not low <= value <= high:
        raise InvalidTrace(f"{where}: expected integer in [{low}, {high}]")


BATCH_MAX = 1025   # the full-ring tier's size (W7 section 6); the guest's BATCH_MAX


def validate_batch(op, where):
    """W7: `items`, 1-1025 of `{kind: "inject", family, port, message}` or
    `{kind: "xmit", packet}` (a wg_xmit packet without the GSO and pmtudisc
    options: a batch item beyond that is refused here, fail-noisy), and
    `wait_ms` 1-4000, the guest's wait after the submission."""
    items = op["items"]
    if type(items) is not list or not 1 <= len(items) <= BATCH_MAX:
        raise InvalidTrace(f"{where}.items: expected 1-{BATCH_MAX} items")
    for k, item in enumerate(items):
        if type(item) is not dict or item.get("kind") not in ("inject", "xmit"):
            raise InvalidTrace(f"{where}.items[{k}]: expected an inject or xmit item")
        if item["kind"] == "inject":
            if set(item) != {"kind", "family", "port", "message"}:
                raise InvalidTrace(f"{where}.items[{k}]: expected kind, family, port, message")
            if item["family"] not in (4, 6):
                raise InvalidTrace(f"{where}.items[{k}].family: expected 4 or 6")
            _integer(item["port"], 1, 65535, f"{where}.items[{k}].port")
            message = item["message"]
            if type(message) is not str or not re.fullmatch(r"(?:[0-9a-f]{2}){1,1400}", message, re.ASCII):
                raise InvalidTrace(f"{where}.items[{k}].message: expected 1-1400 bytes of lowercase hex")
        else:
            if set(item) != {"kind", "packet"}:
                raise InvalidTrace(f"{where}.items[{k}]: expected kind, packet")
            packet = item["packet"]
            if type(packet) is not dict or "gso_size" in packet or "pmtudisc" in packet:
                raise InvalidTrace(f"{where}.items[{k}].packet: a batch transmit takes no gso_size or pmtudisc")
            try:
                validate_packet(packet, f"{where}.items[{k}].packet")
            except InvalidConfig as exc:
                raise InvalidTrace(str(exc)) from exc
    if "wait_ms" in op:
        _integer(op["wait_ms"], 1, 4000, f"{where}.wait_ms")


def encode_batch(op):
    """The wire payload: per item a kind byte (1 inject, 2 xmit), a 16-bit
    big-endian body length, and the body: family(1) port(2) message for an
    inject; the 16-byte v4-mapped destination then the payload for a
    transmit (as wg_xmit's wire)."""
    out = b""
    for item in op["items"]:
        if item["kind"] == "inject":
            body = bytes([item["family"]]) + item["port"].to_bytes(2, "big") + bytes.fromhex(item["message"])
            kind = 1
        else:
            _, body = encode_packet(item["packet"])
            kind = 2
        out += bytes([kind]) + len(body).to_bytes(2, "big") + body
    return out


def _fields(value, keys, where):
    if type(value) is not dict or set(value) != keys:
        raise InvalidTrace(f"{where}: expected exactly {sorted(keys)}")


def validate_trace(trace):
    """Return a detached valid trace; reject all inputs outside trace v1."""
    if type(trace) is not dict or not {"version", "id", "ops"} <= set(trace) <= {"version", "id", "ops", "rlimit_nofile", "steer", "expect", "net_fixture", "domain_extension", "seccomp_child", "seccomp_prefill"}:
        raise InvalidTrace("trace: expected exactly ['id', 'ops', 'version'] and optionally 'rlimit_nofile', 'steer', 'expect', 'net_fixture', 'domain_extension', 'seccomp_child', 'seccomp_prefill'")
    # seccomp X (design 5; [USER 2026-10-12]): the prefill fixture installs N
    # copies of a fixed program in the trace process before the window; it is
    # the trace process's own state, never with a network fixture or a
    # steering schedule
    if "seccomp_prefill" in trace:
        _integer(trace["seccomp_prefill"], 1, SECCOMP_PREFILL_MAX, "seccomp_prefill")
        if trace.get("net_fixture") or "steer" in trace:
            raise InvalidTrace("seccomp_prefill: never with a network fixture or a steering schedule")
    # seccomp W (design 5, 6.2 rule 2): the child fixture holds the sandboxed
    # child's KCOV descriptor at 8; declared explicitly, required by a child
    # probe, never with a network fixture or a steering schedule
    if "seccomp_child" in trace and trace["seccomp_child"] is not True:
        raise InvalidTrace("seccomp_child: expected true")
    # A steering schedule (choice-stream strategy, step 2): [site label, value
    # hex or "draw"] in encounter order; the expected decision outcomes that
    # the steering is for. Sites, lengths and domains are checked when the
    # schedule is resolved against the kernel (harness/steer.py).
    if "steer" in trace:
        steer = trace["steer"]
        if type(steer) is not list or not 1 <= len(steer) <= 64 or any(
                type(e) is not list or len(e) != 2 or type(e[0]) is not str or type(e[1]) is not str
                or not (e[1] == "draw" or re.fullmatch(r"(?:[0-9a-f]{2}){1,40}", e[1])) for e in steer):
            raise InvalidTrace("steer: expected 1–64 [site, hex or 'draw'] entries")
    # D3: `fired:<callback>` expects that a timer callback ran in a section
    # the mirror's environment accepted (docs/2026-10-05-d3-timers.md, 7).
    if "expect" in trace:
        expect = trace["expect"]
        if type(expect) is not list or not 1 <= len(expect) <= 16 or any(
                type(e) is not str or not re.fullmatch(r"[A-Za-z0-9_.]+=[01]|fired:wg_expired_[a-z_]{1,40}", e)
                for e in expect):
            raise InvalidTrace("expect: expected 1–16 'decision=0|1' or 'fired:wg_expired_*' labels")
        # W2 (4.8): an unsteered trace may state expected outcomes too (a
        # boundary-targeting trace is self-verifying); the check enforces
        # them on any agreeing trace.
    # The declared failslab-style extension (docs/2026-10-05-a-alloc.md,
    # section 3, [USER 2026-10-06]): the trace forces a task-context
    # (b-task) allocation failure; the forced trace as a whole is not a
    # possible Linux execution. harness/steer.py enables that class only for
    # such a trace and refuses the marker on a trace that forces none.
    if "domain_extension" in trace:
        if trace["domain_extension"] != "failslab":
            raise InvalidTrace("domain_extension: expected 'failslab'")
        if "steer" not in trace:
            raise InvalidTrace("domain_extension: only a steered trace declares it")
    if "rlimit_nofile" in trace:
        _integer(trace["rlimit_nofile"], 8, 1024, "rlimit_nofile")
    _integer(trace["version"], 1, 1, "version")
    if not isinstance(trace["id"], str) or not re.fullmatch(r"[A-Za-z0-9_.-]{1,80}", trace["id"], re.ASCII):
        raise InvalidTrace("id: expected 1–80 ASCII identifier characters")
    ops = trace["ops"]
    if type(ops) is not list or not 1 <= len(ops) <= 64:
        raise InvalidTrace("ops: expected 1–64 operations")
    for i, op in enumerate(ops):
        if type(op) is not dict or type(op.get("op")) is not str:
            raise InvalidTrace(f"ops[{i}]: expected operation object")
        name = op["op"]
        if name not in FIELDS:
            raise UnsupportedTrace(f"ops[{i}]: unsupported operation {name!r}")
        if name == "wg_flood":
            # E-B: `messages` (leading valid initiations the mirror checks) and
            # `control` (one mid-flood valid the mirror must not model) optional
            if not FIELDS[name] <= set(op) <= FIELDS[name] | {"family", "messages", "control"}:
                raise InvalidTrace(f"ops[{i}]: expected {sorted(FIELDS[name])} and optionally family, messages, control")
            # the flood's destination family (default 4, the v4-mapped 127.0.0.1; 6 is
            # ::1, the ratelimiter's /64 table, 2026-10-14)
            if op.get("family", 4) not in (4, 6):
                raise InvalidTrace(f"ops[{i}].family: expected 4 or 6")
            pipes = False
        elif name == "wg_batch":
            if not FIELDS[name] <= set(op) <= FIELDS[name] | {"wait_ms"}:
                raise InvalidTrace(f"ops[{i}]: expected {sorted(FIELDS[name])} and optionally wait_ms")
            pipes = False
            validate_batch(op, f"ops[{i}]")
        else:
            optional = OPTIONAL_OP_FIELDS | ({"device"} if name in DEVICE_OPS else set()) \
                | ({"to"} if name == "wg_inject" else set()) \
                | SECCOMP_OPTIONAL.get(name, set()) \
                | ROUTING_OPTIONAL.get(name, set())   # W1: the device selector; W9: the destination; seccomp W; lane C
            _fields({k: v for k, v in op.items() if k not in optional}, FIELDS[name], f"ops[{i}]")
            pipes = name in PIPE_PRODUCERS
        if "device" in op:
            try:
                validate_device(op["device"], f"ops[{i}].device")
            except InvalidConfig as exc:
                raise InvalidTrace(str(exc)) from exc
        if "pause_ms" in op:
            _integer(op["pause_ms"], *PAUSE_MS, f"ops[{i}].pause_ms")
            pipes = True
        if "tos" in op:
            if name not in ("wg_inject", "wg_xmit"):
                raise InvalidTrace(f"ops[{i}].tos: only wg_inject and wg_xmit take a TOS")
            _integer(op["tos"], *SENDER_TOS, f"ops[{i}].tos")
        if "from" in op:
            if name != "wg_inject" or op.get("family") != 6 or op["from"] != "ll":
                raise InvalidTrace(f"ops[{i}].from: only an IPv6 wg_inject may be sent from \"ll\"")
        for field in ("init", "flags", "arg"):
            if field in op and name != "seccomp_install":   # seccomp W: an install's flags are a list of names
                _integer(op[field], 0, 2**32 - 1, f"ops[{i}].{field}")
        for field in ("fd", "newfd", "epfd"):   # epfd: epoll R, the set
            if field not in op:
                continue
            fd = op[field]
            if type(fd) is not dict or set(fd) not in ({"literal"}, {"ref"}, {"pipe", "end"}):
                raise InvalidTrace(f"ops[{i}].{field}: expected literal, ref or pipe end")
            if "pipe" in fd:
                _integer(fd["pipe"], 0, i - 1, f"ops[{i}].{field}.pipe")
                _integer(fd["end"], 0, 1, f"ops[{i}].{field}.end")
                if ops[fd["pipe"]]["op"] not in PIPE_PRODUCERS:
                    raise InvalidTrace(f"ops[{i}].{field}: pipe end must name a pipe2")
                pipes = True
            elif "literal" in fd:
                _integer(fd["literal"], -(2**31), 2**31 - 1, f"ops[{i}].{field}.literal")
                if 0 <= fd["literal"] < 8:
                    raise InvalidTrace(f"ops[{i}].{field}: reserved fixture descriptor")
            else:
                _integer(fd["ref"], 0, i - 1, f"ops[{i}].{field}.ref")
                if ops[fd["ref"]]["op"] not in PRODUCERS:
                    raise InvalidTrace(f"ops[{i}].{field}: reference must name FD producer")
        if "count" in op and name != "wg_flood":
            _integer(op["count"], 0, MAX_IO, f"ops[{i}].count")
            if op["count"] > LEGACY_IO:
                pipes = True
        if name == "write":
            value = op["value"]
            if type(value) is not str or not re.fullmatch(r"0|[1-9][0-9]{0,19}", value, re.ASCII) or int(value) >= 2**64:
                raise InvalidTrace(f"ops[{i}].value: expected canonical uint64 decimal string")
        if name == "fcntl":
            if type(op["cmd"]) is not str or op["cmd"] not in FCNTL:
                raise UnsupportedTrace(f"ops[{i}].cmd: unsupported fcntl command")
            if op["cmd"] in ("F_SETPIPE_SZ", "F_GETPIPE_SZ"):
                pipes = True
        if pipes and not GUEST_PIPES:
            raise UnsupportedTrace(f"ops[{i}]: the pipes contract is not implemented by the guest yet (P1)")
        if name == "wg_set":
            try:
                validate_config(op["config"], f"ops[{i}].config")
            except InvalidConfig as exc:
                raise InvalidTrace(str(exc)) from exc
        if name == "wg_inject":
            _integer(op["family"], 4, 6, f"ops[{i}].family")
            if op["family"] == 5:
                raise InvalidTrace(f"ops[{i}].family: expected 4 or 6")
            _integer(op["port"], 1, 65535, f"ops[{i}].port")
            message = op["message"]
            if type(message) is not str or not re.fullmatch(r"(?:[0-9a-f]{2}){1,1400}", message, re.ASCII):
                raise InvalidTrace(f"ops[{i}].message: expected 1-1400 bytes of lowercase hex")
            if "to" in op:
                if op["to"] not in INJECT_DESTINATIONS:
                    raise InvalidTrace(f"ops[{i}].to: expected one of {list(INJECT_DESTINATIONS)}")
                if op["to"] == "loopback-alias" and op["family"] != 4:
                    raise InvalidTrace(f"ops[{i}].to: loopback-alias is IPv4 only")
        if name in ("wg_deladdr", "wg_delroute"):
            _integer(op["family"], 4, 6, f"ops[{i}].family")
            if op["family"] == 5:
                raise InvalidTrace(f"ops[{i}].family: expected 4 or 6")
            if name == "wg_delroute" and set(op) & ROUTING_OPTIONAL["wg_delroute"]:   # lane C: a named route
                if op["family"] != 4 or "dst" not in op or "plen" not in op:
                    raise InvalidTrace(f"ops[{i}]: a named route is IPv4 with dst and plen")
                _validate_route(op, f"ops[{i}]", add=False)
        if name == "wg_addroute":
            _integer(op["family"], 4, 4, f"ops[{i}].family")   # IPv4 (IPv6 keeps the environment's rule, the design note U2)
            _validate_route(op, f"ops[{i}]", add=True)
        if name == "wg_addaddr":
            _hex_addr4(op["addr"], f"ops[{i}].addr")
            _integer(op["plen"], 1, 32, f"ops[{i}].plen")
        if name == "wg_advance":
            _integer(op["ticks"], 1, 2**31, f"ops[{i}].ticks")
        if name == "wg_flood":
            # B4 (2.4): the flood runs exactly in the mirror; the handshake ring
            # holds MAX_QUEUED_INCOMING_HANDSHAKES = 4096, so a count at the ring's
            # size (B1's twins: 4096 invalid and one leading valid, the last send
            # dropped at a full slot) is the largest that adds an arm, and the
            # report's MAX_BRANCHES bounds the labels (about 65 a packet with
            # lane C's lookup per send);
            # Leanux/Runner.lean has the same bound
            _integer(op["count"], 1, 4096, f"ops[{i}].count")
            _integer(op["port"], 1, 65535, f"ops[{i}].port")
            # the leading valids and the optional control are 148-byte (296-hex)
            # handshake initiations (the guest submits them as fixed-size slots)
            messages = op.get("messages", [])
            if type(messages) is not list or len(messages) > 8 or any(
                    type(m) is not str or not re.fullmatch(r"(?:[0-9a-f]{2}){148}", m, re.ASCII)
                    for m in messages):
                raise InvalidTrace(f"ops[{i}].messages: expected 0-8 leading 148-byte initiations (hex)")
            if "control" in op and (type(op["control"]) is not str
                                    or not re.fullmatch(r"(?:[0-9a-f]{2}){148}", op["control"], re.ASCII)):
                raise InvalidTrace(f"ops[{i}].control: expected a 148-byte initiation (hex)")
        if name == "wg_xmit":
            try:
                validate_packet(op["packet"], f"ops[{i}].packet")
            except InvalidConfig as exc:
                raise InvalidTrace(str(exc)) from exc
        if name == "wg_set_mtu":
            # the guest writes `(int)op->a` into ifr_mtu (guest.c), so the field
            # is a u32 whose values at or above 2^31 reach the kernel negative
            if type(op["mtu"]) is not int or not 0 <= op["mtu"] <= 0xFFFFFFFF:
                raise InvalidTrace(f"ops[{i}].mtu: expected an integer 0-4294967295")
        if name == "wg_batch":
            validate_batch(op, f"ops[{i}]")
        # epoll R (design section 6): cmd and events are u32 like flags, data
        # the u64 the kernel copies back verbatim; tier 1 waits with timeout 0
        # for 1-16 events, the rest is explicitly unsupported until a sleep
        # record exists (design 9.1)
        if name == "epoll_ctl":
            _integer(op["cmd"], 0, 2**32 - 1, f"ops[{i}].cmd")
            _integer(op["events"], 0, 2**32 - 1, f"ops[{i}].events")
            data = op["data"]
            if type(data) is not str or not re.fullmatch(r"0|[1-9][0-9]{0,19}", data, re.ASCII) or int(data) >= 2**64:
                raise InvalidTrace(f"ops[{i}].data: expected canonical uint64 decimal string")
        if name == "epoll_wait":
            _integer(op["maxevents"], 0, 2**31 - 1, f"ops[{i}].maxevents")
            _integer(op["timeout"], -(2**31), 2**31 - 1, f"ops[{i}].timeout")
            if not EPOLL_MAXEVENTS[0] <= op["maxevents"] <= EPOLL_MAXEVENTS[1]:
                raise UnsupportedTrace(f"ops[{i}].maxevents: tier 1 waits for {EPOLL_MAXEVENTS[0]}-{EPOLL_MAXEVENTS[1]} events")
            if op["timeout"] != 0:
                raise UnsupportedTrace(f"ops[{i}].timeout: tier 1 waits with timeout 0 only (no sleep record)")
        if name in SECCOMP_OPS:
            validate_seccomp_op(op, i, ops, trace)
    if "net_fixture" in trace:
        fixture = trace["net_fixture"]
        if type(fixture) is dict:
            validate_fixture_routes(fixture)
        elif type(fixture) is not str or fixture not in NET_FIXTURES:
            raise InvalidTrace(f"net_fixture: expected one of {list(NET_FIXTURES)} or {{'routes': [...]}}")
        if not uses_wireguard(trace):
            raise InvalidTrace("net_fixture: only a network trace has a network fixture")
    # seccomp W: the child fixture's shape (design 5, 6.1, 6.2)
    child_probes = [i for i, op in enumerate(ops) if op["op"] == "seccomp_probe" and op["where"] == "child"]
    if trace.get("seccomp_child"):
        if not child_probes:
            raise InvalidTrace("seccomp_child: declared by a trace without a child probe")
        if uses_wireguard(trace):
            raise InvalidTrace("seccomp_child: never with a network fixture (descriptor 8 is the fixture's)")
        if "steer" in trace:
            raise InvalidTrace("seccomp_child: a steered trace has no child probe (the child loads no schedule)")
        if trace.get("rlimit_nofile", 32) < 9:
            raise InvalidTrace("seccomp_child: rlimit_nofile below 9 (the fixture holds descriptor 8)")
        for i, op in enumerate(ops):
            for field in ("fd", "newfd", "epfd"):
                if field in op and op[field].get("literal") == 8:
                    raise InvalidTrace(f"ops[{i}].{field}: descriptor 8 is the child fixture's")
    elif child_probes:
        raise InvalidTrace(f"ops[{child_probes[0]}].where: a child probe needs the trace to declare seccomp_child")
    # W8: the foreign-creator fixture's shape (design 3.1, 3.4)
    closes = [i for i, op in enumerate(trace["ops"]) if op["op"] == "wg_netns_close"]
    if trace.get("net_fixture") == "foreign-creator":
        if len(closes) != 1:
            raise InvalidTrace("net_fixture foreign-creator: exactly one wg_netns_close (the namespace exits inside the trace)")
        if trace.get("rlimit_nofile", 32) < 10:
            raise InvalidTrace("net_fixture foreign-creator: rlimit_nofile below 10 (the fixture holds descriptors 4-9)")
        if any(op["op"] == "wg_inject" and op.get("to", "loopback") == "wg0" for op in trace["ops"]):
            raise InvalidTrace("wg_inject to: wg0 is unroutable from the creating namespace")
        if any(op["op"] == "wg_inject" for op in trace["ops"][closes[0]:]):
            raise InvalidTrace("wg_inject after wg_netns_close: no socket in the creating namespace")
    elif closes:
        raise InvalidTrace("wg_netns_close: only in the foreign-creator fixture")
    # W2 (design 4.2, 8.1): a stepped dump holds the fixture's second
    # generic-netlink socket at descriptor 8, so it needs rlimit 9 (10 with a
    # lifecycle operation, whose temporary socket takes 9) and excludes the
    # foreign-creator fixture, whose descriptors 8-9 are the namespace's.
    if is_stepped(trace):
        if trace.get("net_fixture") == "foreign-creator":
            raise InvalidTrace("wg_get_start/wg_get_recv: the stepped dump and the foreign-creator fixture both need descriptor 8")
        need = 10 if any(op["op"] in LIFECYCLE_OPS for op in trace["ops"]) else 9
        if trace.get("rlimit_nofile", 32) < need:
            raise InvalidTrace(f"wg_get_start/wg_get_recv: rlimit_nofile below {need} (the dump socket is descriptor 8)")
    return deepcopy(trace)


def validate_seccomp_op(op, i, ops, trace):
    """seccomp W (design 6.1): the fields and the validator's rules. A self
    probe is rejected once an earlier install's filter may kill (the
    conservative scan, filter_may_kill); strict is child-only; a probe's nr
    is in the probe set (6.2 rule 1); a filter has at most BPF_MAXINSNS
    instructions (the length arms use `len`). The flags, actions and numbers
    the mirror stops on (TSYNC, NEW_LISTENER, USER_NOTIF, a CTX load of
    offsets 8..15) are valid inputs: the control suite runs them and expects
    the mirror's unsupported stop, so the validator does not reject them."""
    name, where = op["op"], f"ops[{i}]"
    if name == "seccomp_install":
        if op["via"] not in SECCOMP_VIA:
            raise InvalidTrace(f"{where}.via: expected one of {list(SECCOMP_VIA)}")
        flags = op["flags"]
        if type(flags) is not list or any(not (f in SECCOMP_FLAGS or (type(f) is int and 0 <= f <= 0xffff)) for f in flags):
            raise InvalidTrace(f"{where}.flags: expected a list of {list(SECCOMP_FLAGS)} or raw bits 0-65535")
        if op["via"] == "prctl" and flags:
            raise InvalidTrace(f"{where}.flags: prctl passes no flags")
        if "mode" in op:
            if op["via"] != "prctl":
                raise InvalidTrace(f"{where}.mode: only a prctl install names the mode")
            _integer(op["mode"], 0, 255, f"{where}.mode")
        program = op["filter"]
        if program is not None:
            if type(program) is not list or not 1 <= len(program) <= BPF_MAXINSNS or any(
                    type(insn) is not list or len(insn) != 4 or any(type(x) is not int for x in insn)
                    or not 0 <= insn[0] <= 0xffff or not 0 <= insn[1] <= 0xff or not 0 <= insn[2] <= 0xff
                    or not 0 <= insn[3] <= 0xffffffff for insn in program):
                raise InvalidTrace(f"{where}.filter: expected null or 1-{BPF_MAXINSNS} [code, jt, jf, k] instructions")
        if "len" in op:
            _integer(op["len"], 0, 0xffff, f"{where}.len")
        if "bad" in op and op["bad"] not in SECCOMP_BAD:
            raise InvalidTrace(f"{where}.bad: expected one of {list(SECCOMP_BAD)}")
        if "bad" in op and program is None:
            raise InvalidTrace(f"{where}.bad: a null filter is the NULL-pointer arm already")
    if name == "seccomp_probe":
        if op["where"] not in SECCOMP_WHERE:
            raise InvalidTrace(f"{where}.where: expected one of {list(SECCOMP_WHERE)}")
        strict = op.get("strict")
        if strict is not None:
            if strict not in SECCOMP_STRICT:
                raise InvalidTrace(f"{where}.strict: expected one of {list(SECCOMP_STRICT)}")
            if op["where"] != "child":
                raise InvalidTrace(f"{where}.strict: strict mode is child-only (the trace process could not report)")
        _integer(op["nr"], 0, 2**31 - 1, f"{where}.nr")
        allowed = SECCOMP_STRICT_PROBE_SET if strict else SECCOMP_PROBE_SET
        if op["nr"] not in allowed:
            raise InvalidTrace(f"{where}.nr: outside the probe set {sorted(allowed)} (design 6.2 rule 1)")
        args = op.get("args", [0] * 6)
        if type(args) is not list or len(args) != 6 or any(type(a) is not int or not 0 <= a < 2**64 for a in args):
            raise InvalidTrace(f"{where}.args: expected six integers 0-2^64-1")
        if op["where"] == "self" and any(
                earlier["op"] == "seccomp_install" and filter_may_kill(earlier["filter"]) for earlier in ops[:i]):
            raise InvalidTrace(f"{where}.where: a self probe after a filter that may kill (design 6.1: run it in a child)")
        # seccomp X (design 6.3): with no mode set the syscall entry never
        # reaches __secure_computing, so a probe before any install covers
        # nothing in the anchored files and the check fails it; a strict child
        # sets its own mode. Installs that the kernel rejects leave no mode
        # either: the check catches those (fail-closed), the corpus avoids them.
        if not strict and not trace.get("seccomp_prefill") and not any(earlier["op"] == "seccomp_install" for earlier in ops[:i]):
            raise InvalidTrace(f"{where}: a probe before any install covers nothing anchored (design 6.3: install first, "
                               "or probe from a strict child)")
    if name == "seccomp_prctl":
        if op["cmd"] not in SECCOMP_PRCTL:
            raise InvalidTrace(f"{where}.cmd: expected one of {list(SECCOMP_PRCTL)}")
        for field in ("arg2", "arg3", "arg4", "arg5"):
            if field in op:
                _integer(op[field], 0, 2**64 - 1, f"{where}.{field}")
    if name == "seccomp_query":
        if op["cmd"] not in SECCOMP_QUERY:
            raise InvalidTrace(f"{where}.cmd: expected one of {list(SECCOMP_QUERY)}")
        if (op["cmd"] == "get_action_avail") != ("action" in op):
            raise InvalidTrace(f"{where}.action: exactly get_action_avail names an action")
        if "action" in op:
            _integer(op["action"], 0, 2**32 - 1, f"{where}.action")
        if "flags" in op:
            _integer(op["flags"], 0, 2**32 - 1, f"{where}.flags")


def is_stepped(trace):
    """W2: whether the trace drives a dump step by step (wg_get_start /
    wg_get_recv), which gives the fixture its second generic-netlink socket
    at descriptor 8."""
    return any(op["op"] in STEPPED_OPS for op in trace["ops"])


def uses_wireguard(trace):
    """Traces with WireGuard operations get the network fixture: a fresh
    network namespace with `lo` up and a down `wg0`; UDP listeners on
    127.0.0.1 and ::1 at descriptors 4 and 5, a dual-stack UDP sender at 6,
    and the generic-netlink socket at 7, in place of the /dev/null fillers.
    `wg_up` also adds an address and a default route on `wg0` per family.
    With `"net_fixture": "bare"` there is no `wg0` until a `wg_create`."""
    return any(op["op"] in WG_OPS for op in trace["ops"])


def net_mode(trace):
    """The wire's `net` field: 0 no network fixture, 1 with a down wg0, 2 bare,
    3 foreign-creator (W8)."""
    if not uses_wireguard(trace):
        return 0
    fixture = trace.get("net_fixture")
    if type(fixture) is dict:   # W4: {"routes": [...]} keeps the plain fixture (mode 1) and adds routes
        return 1
    return {"bare": 2, "foreign-creator": 3}.get(fixture, 1)


def validate_fixture_routes(fixture):
    """W4: `net_fixture` as {"routes": [{"family": 4|6, "dst": hex, "mtu": n}]}."""
    if set(fixture) != {"routes"} or type(fixture["routes"]) is not list \
            or not 1 <= len(fixture["routes"]) <= MAX_FIXTURE_ROUTES:
        raise InvalidTrace(f"net_fixture: expected {{'routes': [1-{MAX_FIXTURE_ROUTES} routes]}}")
    for k, route in enumerate(fixture["routes"]):
        if type(route) is not dict or set(route) != {"family", "dst", "mtu"} or route["family"] not in (4, 6):
            raise InvalidTrace(f"net_fixture.routes[{k}]: expected family (4 or 6), dst, mtu")
        digits = 8 if route["family"] == 4 else 32
        if type(route["dst"]) is not str or not re.fullmatch(f"[0-9a-f]{{{digits}}}", route["dst"]):
            raise InvalidTrace(f"net_fixture.routes[{k}].dst: expected {digits} lowercase hex digits")
        if type(route["mtu"]) is not int or not 68 <= route["mtu"] <= 65535:
            raise InvalidTrace(f"net_fixture.routes[{k}].mtu: expected 68-65535")


def fixture_routes(trace):
    fixture = trace.get("net_fixture")
    return fixture["routes"] if type(fixture) is dict else []


def loads_trace(line):
    """JSON loading also rejects duplicate object members and nonfinite values."""
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise InvalidTrace(f"duplicate JSON member: {key}")
            result[key] = value
        return result
    def constant(value):
        raise InvalidTrace(f"invalid JSON constant: {value}")
    try:
        return validate_trace(json.loads(line, object_pairs_hook=object_pairs, parse_constant=constant))
    except (json.JSONDecodeError, RecursionError) as exc:
        raise InvalidTrace(f"invalid JSON: {exc}") from exc


ALLOC_INVENTORY = 1      # the allocation load's inventory flag (A, docs/2026-10-05-a-alloc.md 4.3)
# Control-kernel load flags (net-choice-actl only; the oracle's load rejects
# them, which fails the trace): a forced failure records ok = 1 (K1), the
# steered encounter counts as __GFP_NOFAIL (K4), naming by address only (K5).
ALLOC_CONTROL_FLAGS = {"record_ok": 2, "nofail": 4, "addr_naming": 8}
ALLOC_RANGES_MAX = 64


def alloc_line(alloc):
    """The `M` line: the allocation set the kernel arms for each trace
    (KCOV_LEANUX_ALLOC_LOAD): `M flags n` and n hex `lo hi` pairs, sorted and
    disjoint. None or {"flags": 0, "ranges": []} is `M 0 0`: disarmed, no
    kind-305 records (the default until the phased flip, section 6.6)."""
    alloc = alloc or {"flags": 0, "ranges": []}
    if type(alloc) is not dict or set(alloc) != {"flags", "ranges"} or type(alloc["flags"]) is not int \
            or alloc["flags"] & ~(ALLOC_INVENTORY | sum(ALLOC_CONTROL_FLAGS.values())):
        raise InvalidTrace("allocation set")
    ranges = [tuple(r) for r in alloc["ranges"]]
    if len(ranges) > ALLOC_RANGES_MAX or any(
            len(r) != 2 or not all(type(x) is int for x in r) or not 0 < r[0] < r[1] < 2**64 for r in ranges) \
            or any(a[1] > b[0] for a, b in zip(ranges, ranges[1:])):
        raise InvalidTrace("allocation ranges")
    return " ".join(["M", str(alloc["flags"]), str(len(ranges))] + [f"{lo:x} {hi:x}" for lo, hi in ranges])


def serialize_wire(traces, steer_wire=None, dispatch=(), arm_records=False, alloc=None, arm_masks=None):
    """`steer_wire`: each steered trace's resolved schedule
    (harness/steer.py), [(kind, length, draw, [return addresses], hex[, flags])].
    `dispatch`: the dispatch set's function addresses (harness/linux.py),
    which a batch with network traces needs. `arm_records`: whether the
    kernel writes the kind-303 arm records for the dispatch set's timers
    (the `A` line; D3). `alloc`: the allocation set (the `M` line; A).
    `arm_masks` (W8, per-trace arming): trace id -> the subset of `dispatch`
    the trace arms, a bit per entry (harness/linux.py `arm_masks`); absent,
    a network trace arms the whole set."""
    traces = [validate_trace(trace) for trace in traces]
    steer_wire = steer_wire or {}
    if any("steer" in t and t["id"] not in steer_wire for t in traces):
        raise InvalidTrace("a steered trace has no resolved schedule")
    if not 1 <= len(traces) <= 4096:
        raise InvalidTrace("guest batch requires 1–4096 traces")
    if len({trace['id'] for trace in traces}) != len(traces):
        raise InvalidTrace("guest batch trace identifiers must be unique")
    if any(uses_wireguard(t) for t in traces) and not dispatch:
        raise InvalidTrace("network traces need the dispatch set")
    if len(dispatch) > 32 or any(type(a) is not int or a <= 0 for a in dispatch):
        raise InvalidTrace("dispatch set")
    if type(arm_records) is not bool:
        raise InvalidTrace("arm_records")
    lines = ["LEANUX_WIRE_V2", str(len(traces)), " ".join(["D", str(len(dispatch))] + [f"{a:x}" for a in dispatch]),
             f"A {int(arm_records)}", alloc_line(alloc)]
    arm_masks = arm_masks or {}
    for trace in traces:
        schedule = steer_wire.get(trace["id"], []) if "steer" in trace else []
        mask = arm_masks.get(trace["id"], (1 << len(dispatch)) - 1 if uses_wireguard(trace) else 0)
        if type(mask) is not int or mask < 0 or mask >> len(dispatch):
            raise InvalidTrace("arm mask outside the dispatch set")
        routes = fixture_routes(trace)
        # seccomp W: the eighth field declares the child fixture (descriptor 8)
        lines.append(f"T {trace['id']} {len(trace['ops'])} {trace.get('rlimit_nofile', 32)} {net_mode(trace)} {len(schedule)} {mask:x} {len(routes)} {int(bool(trace.get('seccomp_child')))} {trace.get('seccomp_prefill', 0)}")
        # W4: the fixture's routes into wg0 (family, destination, MTU), one line each
        for route in routes:
            lines.append(f"R {route['family']} {route['dst']} {route['mtu']}")
        for op in trace["ops"]:
            def fd(field):
                value = op.get(field, {"literal": -1})
                if "pipe" in value:
                    return (FD_KIND_PIPE_READ + value["end"], value["pipe"])
                return (FD_KIND_REF, value["ref"]) if "ref" in value else (FD_KIND_LITERAL, value["literal"])
            kind, value = fd("fd")
            newkind, newvalue = fd("newfd")
            a = op.get("init", op.get("count", FCNTL.get(op.get("cmd"), 0)))
            b = op.get("flags", op.get("arg", 0))
            op_value = op.get("value", "0")
            if op["op"] == "wg_xmit":
                # W4: b = gso_size (0: none), the value field 1 for IP_PMTUDISC_PROBE (0: DO)
                a, packet = encode_packet(op["packet"])
                # W4: b = gso_size (0: none); the value field: bit 0 = IP_PMTUDISC_PROBE
                # (0: DO), bits 8-15 = the sender's TOS (W5)
                b = op["packet"].get("gso_size", 0)
                op_value = (1 if op["packet"].get("pmtudisc") == "probe" else 0) | (op.get("tos", 0) << 8)
            if op["op"] == "wg_set_mtu":
                a = op["mtu"]
            if op["op"] == "wg_inject":
                a, b = op["family"], op["port"]
                # the sender's TOS (bits 0-7) and the link-local source (bit 8)
                # W5: tos | ll << 8; W9: the destination code << 9
                op_value = str(op.get("tos", 0) | (256 if op.get("from") == "ll" else 0)
                               | (INJECT_DESTINATIONS[op.get("to", "loopback")] << 9))
            if op["op"] == "wg_advance":
                a = op["ticks"]
            if op["op"] == "wg_flood":
                a, b = op["count"], op["port"]
                op_value = str(op.get("family", 4))   # the value field carries the family
            if op["op"] == "wg_batch":
                # W7: a = the item count, b = the guest's wait after the submission (ms)
                a, b = len(op["items"]), op.get("wait_ms", 100)
            if op["op"] in ("wg_deladdr", "wg_delroute"):   # W9
                a = op["family"]
                if op["op"] == "wg_delroute" and "dst" in op:   # lane C: a named route; b's top bit marks it
                    b = (1 << 31) | op["plen"] | (ROUTE_OIFS.get(op.get("oif"), 0) << 8) | (ROUTE_TYPES.get(op.get("type"), 0) << 16)
                    op_value = str(int(op["dst"], 16) | (op.get("metric", 0) << 32))
            if op["op"] == "wg_addroute":   # lane C: a = plen | type << 8 | oif code << 16 | flags << 24, b = metric, value = dst | mtu << 32
                a = op["plen"] | (ROUTE_TYPES[op["type"]] << 8) | (ROUTE_OIFS.get(op.get("oif"), 0) << 16) \
                    | (sum(ROUTE_FLAGS[f] for f in op.get("nlflags", [])) << 24)
                b = op.get("metric", 0)
                op_value = str(int(op["dst"], 16) | (op.get("mtu", 0) << 32))
            if op["op"] == "wg_addaddr":   # lane C: a = plen, value = the address
                a = op["plen"]
                op_value = str(int(op["addr"], 16))
            if op["op"] in ("epoll_ctl", "epoll_wait"):
                # epoll R (design 6): fd = the set; epoll_ctl's newfd = the target,
                # a = cmd, b = events, value = data; epoll_wait's a = maxevents, b = timeout
                kind, value = fd("epfd")
                if op["op"] == "epoll_ctl":
                    newkind, newvalue = fd("fd")
                    a, b, op_value = op["cmd"], op["events"], op["data"]
                else:
                    a, b = op["maxevents"], op["timeout"]
            payload = None   # seccomp W: the hex payload of install, probe and prctl
            if op["op"] == "seccomp_install":
                # a = via | mode << 8, b = flags | bad << 16, value = 1 << 32 | len (an override), payload = the program
                a = SECCOMP_VIA[op["via"]] | (op.get("mode", 2) << 8)
                flags = 0
                for flag in op["flags"]:
                    flags |= SECCOMP_FLAGS.get(flag, flag if type(flag) is int else 0)
                bad = 3 if op["filter"] is None else SECCOMP_BAD.get(op.get("bad"), 0)
                b = flags | (bad << 16)
                op_value = str((1 << 32) | op["len"]) if "len" in op else "0"
                payload = b"".join(struct.pack("<HBBI", *insn) for insn in (op["filter"] or ()))
            if op["op"] == "seccomp_probe":
                # a = nr, b = where | strict << 8, payload = the six arguments
                a, b = op["nr"], SECCOMP_WHERE[op["where"]] | (SECCOMP_STRICT.get(op.get("strict"), 0) << 8)
                payload = struct.pack("<6Q", *op.get("args", [0] * 6))
            if op["op"] == "seccomp_prctl":
                a = SECCOMP_PRCTL[op["cmd"]]
                payload = struct.pack("<4Q", *(op.get(f, 0) for f in ("arg2", "arg3", "arg4", "arg5")))
            if op["op"] == "seccomp_query":
                a, b, op_value = SECCOMP_QUERY[op["cmd"]], op.get("action", 0), str(op.get("flags", 0))
            line = f"{OPCODES[op['op']]} {kind} {value} {newkind} {newvalue} {a} {b} {op_value}"
            if GUEST_PIPES:
                line += f" {op.get('pause_ms', 0)}"   # the ninth field (P1)
            if op["op"] == "wg_set":
                line += " " + encode_set(op["config"], op.get("device")).hex()
            elif op["op"] in ("wg_get", "wg_get_start"):
                line += " " + encode_get(op.get("device")).hex()
            elif op["op"] == "wg_xmit":
                line += " " + packet.hex()
            elif op["op"] == "wg_inject":
                line += " " + op["message"]
            elif op["op"] == "wg_flood":
                # payload = n_leading(1) ‖ control_flag(1) ‖ the leading valids
                # then the control (each 148 bytes); the invalid template is
                # built in the guest
                leading = op.get("messages", [])
                control = op.get("control")
                header = bytes([len(leading), 1 if control else 0]).hex()
                line += " " + header + "".join(leading) + (control or "")
            elif op["op"] == "wg_batch":
                line += " " + encode_batch(op).hex()
            elif payload is not None:
                line += " " + payload.hex()
            lines.append(line)
        for entry in schedule:
            # (kind, length, draw, ips, hex[, flags]); flags: 1 = match the
            # unwound chain too (allocation entries, kind 305)
            kind, length, draw, ips, value = entry[:5]
            flags = entry[5] if len(entry) > 5 else 0
            if len(entry) not in (5, 6) or flags not in (0, 1) or (flags and kind != 305):
                raise InvalidTrace("steering entry")
            ips = (list(ips) + [0, 0, 0, 0])[:4]
            lines.append(f"S {kind} {length} {int(draw)} {flags} " + " ".join(f"{ip:x}" for ip in ips)
                         + f" {'' if draw else value}")
    return "\n".join(lines) + "\n"
