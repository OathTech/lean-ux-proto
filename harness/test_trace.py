"""Contract-boundary checks; no host experiment syscalls."""
from copy import deepcopy
import hashlib
from pathlib import Path
import json
import os
import random
import re
import shutil
import subprocess
import unittest

from .trace import (FIELDS, KCOV_CAPACITY, OPCODES, RESERVED_OPCODES, InvalidTrace, UnsupportedTrace, filter_may_kill, loads_trace,
                    serialize_wire, validate_trace)

ROOT = Path(__file__).resolve().parents[1]


class TraceContractTests(unittest.TestCase):
    def setUp(self):
        self.trace = {"version": 1, "id": "case", "ops": [
            {"op": "eventfd2", "init": 0, "flags": 2048},
            {"op": "write", "fd": {"ref": 0}, "count": 8, "value": "18446744073709551615"},
        ]}

    def test_corpus_is_valid_and_ids_unique(self):
        paths = sorted((Path(__file__).resolve().parents[1] / "corpus/handwritten").glob("*.json"))
        traces = [loads_trace(path.read_text()) for path in paths]
        self.assertGreaterEqual(len(traces), 20)
        self.assertEqual(len({t['id'] for t in traces}), len(traces))
        self.assertTrue(serialize_wire(traces).startswith(f"LEANUX_WIRE_V2\n{len(traces)}\nD 0\nA 0\nM 0 0\n"))

    def test_accepts_phase4_domain(self):
        # Amended 2026-09-29: blocking creation and getter arguments are valid.
        trace = deepcopy(self.trace)
        trace['ops'][0].update(flags=0)
        trace['ops'].append({"op": "fcntl", "fd": {"ref": 0}, "cmd": "F_GETFD", "arg": 1})
        trace['ops'].append({"op": "fcntl", "fd": {"ref": 0}, "cmd": "F_GETFL", "arg": 4294967295})
        self.assertEqual(validate_trace(trace), trace)

    def test_rejects_normative_boundary_violations(self):
        mutations = [
            lambda t: t.update(version=True),
            lambda t: t.update(extra=1),
            lambda t: t.update(id="non ASCII é"),
            lambda t: t['ops'][0].update(init=2**32),
            lambda t: t['ops'][1].update(count=True),
            lambda t: t['ops'][1].update(count=69633),
            lambda t: t['ops'][1].update(value="18446744073709551616"),
            lambda t: t['ops'][1].update(value="00"),
            lambda t: t['ops'][1].update(value=0),
            lambda t: t['ops'][1].update(fd={"literal": 7}),
            lambda t: t['ops'][1].update(fd={"literal": -(2**31)-1}),
            lambda t: t['ops'][1].update(fd={"ref": 1}),
            lambda t: t['ops'][1].update(fd={"ref": 0, "literal": 8}),
            lambda t: t['ops'].append({"op": "close", "fd": {"ref": 1}}),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                trace = deepcopy(self.trace)
                mutation(trace)
                with self.assertRaises(InvalidTrace):
                    validate_trace(trace)

    def test_json_duplicates_and_constants_rejected(self):
        for text in ['{"version":1,"version":1}', 'NaN', 'Infinity', '{']:
            with self.assertRaises(InvalidTrace):
                loads_trace(text)

    def test_unsupported_is_explicit(self):
        self.trace['ops'].append({'op': 'socket'})
        with self.assertRaises(UnsupportedTrace):
            validate_trace(self.trace)

    def test_d3_advance_and_fired_expectations(self):
        # D3 interface: wg_advance {ticks} is wire opcode 19 with `a` = ticks;
        # `fired:wg_expired_*` is an expectation form; the `A` line carries
        # the arm-record switch.
        trace = {"version": 1, "id": "d3", "ops": [{"op": "wg_advance", "ticks": 2**31}],
                 "steer": [["tai64n_now", "draw"]],
                 "expect": ["fired:wg_expired_new_handshake", "wg_timers_data_sent.not_pending=1"]}
        self.assertEqual(validate_trace(trace), trace)
        plain = {k: v for k, v in trace.items() if k not in ("steer", "expect")}
        wire = serialize_wire([plain], dispatch=(1,), arm_records=True)
        self.assertEqual(wire.splitlines()[3:7], ["A 1", "M 0 0", "T d3 1 32 1 0 1 0 0", f"19 0 -1 0 -1 {2**31} 0 0 0"])
        for bad in ([{"op": "wg_advance", "ticks": 0}], [{"op": "wg_advance", "ticks": 2**31 + 1}],
                    [{"op": "wg_advance", "ticks": 1, "extra": 0}]):
            with self.assertRaises(InvalidTrace):
                validate_trace(dict(trace, ops=bad))
        for label in ("fired:", "fired:net_rx_action", "fired:wg_expired_X", "fired:wg_expired_a=1"):
            with self.assertRaises(InvalidTrace):
                validate_trace(dict(trace, expect=[label]))

    def test_wire_preserves_widths_and_reference_modes(self):
        self.trace['ops'].append({'op': 'dup3', 'fd': {'literal': -2147483648}, 'newfd': {'ref': 0}, 'flags': 4294967295})
        self.assertEqual(serialize_wire([self.trace]),
                         'LEANUX_WIRE_V2\n1\nD 0\nA 0\nM 0 0\nT case 3 32 0 0 0 0 0\n1 0 -1 0 -1 0 2048 0 0\n6 1 0 0 -1 8 0 18446744073709551615 0\n3 0 -2147483648 1 0 0 4294967295 0 0\n')

    def test_sender_tos_and_link_local_source(self):
        # W5 (docs/2026-10-06-w5-w6-receive.md, section 6): `tos` on wg_inject
        # and wg_xmit, `from: "ll"` on an IPv6 wg_inject; the wire carries
        # tos | ll << 8 in wg_inject's value field and, for wg_xmit, the TOS in
        # bits 8-15 of the value field (bit 0 is W4's IP_PMTUDISC_PROBE, b its gso_size)
        base = {"version": 1, "id": "t", "ops": [
            {"op": "wg_inject", "family": 6, "port": 51820, "message": "00", "tos": 0xb9, "from": "ll"},
            {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a000001"}, "tos": 3}]}
        wire = serialize_wire([validate_trace(base)], dispatch=[1]).splitlines()
        self.assertEqual(wire[6].split()[:8], ["13", "0", "-1", "0", "-1", "6", "51820", str(0xb9 | 256)])
        self.assertEqual(wire[7].split()[:8], ["11", "0", "-1", "0", "-1", "4", "0", str(3 << 8)])
        for bad in ({"op": "wg_inject", "family": 4, "port": 1, "message": "00", "from": "ll"},
                    {"op": "wg_inject", "family": 6, "port": 1, "message": "00", "from": "lo"},
                    {"op": "wg_inject", "family": 6, "port": 1, "message": "00", "tos": 256},
                    {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a000001"}, "tos": -1},
                    {"op": "wg_observe", "tos": 0}, {"op": "wg_up", "from": "ll"}):
            with self.assertRaises(InvalidTrace):
                validate_trace({"version": 1, "id": "t", "ops": [bad]})

    def test_failslab_extension(self):
        """A2: the (b-task) class is enabled only under the declared
        extension, and the marker only with such a failure."""
        from harness.steer import ALLOC_FAIL, SteeringError, alloc_refusal, resolve
        trace = deepcopy(self.trace)
        trace['steer'] = [['kmallocEventfdCtx', ALLOC_FAIL]]
        validate_trace(trace)
        self.assertIn('not enabled', alloc_refusal(trace, 'kmallocEventfdCtx', ALLOC_FAIL))
        self.assertIsNone(alloc_refusal(trace, 'kmallocEventfdCtx', 'draw'))
        trace['domain_extension'] = 'failslab'
        validate_trace(trace)
        self.assertIsNone(alloc_refusal(trace, 'kmallocEventfdCtx', ALLOC_FAIL))
        self.assertIsNone(alloc_refusal(trace, 'sendBufSkb', ALLOC_FAIL))
        # b-kworker stays record-only; the 8 KiB kvmalloc stays refused
        self.assertIn('not enabled', alloc_refusal(trace, 'kzallocKeypair', ALLOC_FAIL))
        self.assertIn('vmalloc', alloc_refusal(dict(trace, rlimit_nofile=1024), 'kvmallocFdArray', ALLOC_FAIL))
        self.assertIsNone(alloc_refusal(dict(trace, rlimit_nofile=128), 'kvmallocFdArray', ALLOC_FAIL))
        # the marker without a forced task-context failure is refused
        for steer in ([['kmallocEventfdCtx', 'draw']], [['sendBufSkb', ALLOC_FAIL]]):
            with self.assertRaises(SteeringError):
                resolve(dict(trace, steer=steer), {}, {})
        for bad in (dict(trace, domain_extension='other'), {k: v for k, v in trace.items() if k != 'steer'}):
            with self.assertRaises(InvalidTrace):
                validate_trace(bad)

    PIPES = {"version": 1, "id": "pipes", "ops": [
        {"op": "pipe2", "flags": 2048},
        {"op": "write", "fd": {"pipe": 0, "end": 1}, "count": 69632, "value": "7", "pause_ms": 5},
        {"op": "read", "fd": {"pipe": 0, "end": 0}, "count": 69632},
        {"op": "fcntl", "fd": {"pipe": 0, "end": 1}, "cmd": "F_SETPIPE_SZ", "arg": 4096},
        {"op": "dup3", "fd": {"pipe": 0, "end": 0}, "newfd": {"literal": 20}, "flags": 0},
        {"op": "fcntl", "fd": {"ref": 4}, "cmd": "F_GETPIPE_SZ", "arg": 0},
    ]}

    def test_pipes_contract(self):
        trace = validate_trace(self.PIPES)
        self.assertEqual(serialize_wire([trace]).splitlines()[5:], [
            'T pipes 6 32 0 0 0 0 0', '14 0 -1 0 -1 0 2048 0 0', '6 3 0 0 -1 69632 0 7 5', '5 2 0 0 -1 69632 0 0 0',
            '7 3 0 0 -1 1031 4096 0 0', '3 2 0 0 20 0 0 0 0', '7 1 4 0 -1 1032 0 0 0'])
        mutations = [
            lambda t: t['ops'][1].update(fd={"ref": 0}),                 # a ref may not name a pipe2
            lambda t: t['ops'][5].update(fd={"pipe": 4, "end": 0}),      # a pipe end must name a pipe2
            lambda t: t['ops'][1].update(fd={"pipe": 0, "end": 2}),
            lambda t: t['ops'][1].update(fd={"pipe": 1, "end": 0}),      # not earlier
            lambda t: t['ops'][1].update(fd={"pipe": 0}),
            lambda t: t['ops'][1].update(pause_ms=0),
            lambda t: t['ops'][1].update(pause_ms=21),
            lambda t: t['ops'][2].update(count=69633),
            lambda t: t['ops'][0].update(flags=-1),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                altered = deepcopy(self.PIPES)
                mutation(altered)
                with self.assertRaises(InvalidTrace):
                    validate_trace(altered)


class EpollContractTests(unittest.TestCase):
    """epoll stream R (docs/2026-10-12-epoll-design.md section 6;
    contracts/trace-v1.md, Epoll): the three operations, their wire fields and
    the tier-1 domain."""

    EPOLL = {"version": 1, "id": "epoll", "ops": [
        {"op": "epoll_create1", "flags": 524288},                                            # 0: a set
        {"op": "eventfd2", "init": 0, "flags": 2048},                                        # 1
        {"op": "pipe2", "flags": 2048},                                                      # 2
        {"op": "epoll_ctl", "epfd": {"ref": 0}, "cmd": 1, "fd": {"ref": 1}, "events": 1, "data": "18446744073709551615"},
        {"op": "epoll_ctl", "epfd": {"ref": 0}, "cmd": 1, "fd": {"pipe": 2, "end": 1}, "events": 4, "data": "7"},
        {"op": "epoll_wait", "epfd": {"ref": 0}, "maxevents": 16, "timeout": 0},
        {"op": "epoll_ctl", "epfd": {"literal": 20}, "cmd": 2, "fd": {"ref": 1}, "events": 0, "data": "0"},
        {"op": "dup", "fd": {"ref": 0}},                                                     # 7: a set may be dup'd
        {"op": "epoll_wait", "epfd": {"ref": 7}, "maxevents": 1, "timeout": 0},
    ]}

    def test_wire(self):
        trace = validate_trace(self.EPOLL)
        self.assertEqual(serialize_wire([trace]).splitlines()[5:], [
            'T epoll 9 32 0 0 0 0 0',
            '27 0 -1 0 -1 0 524288 0 0',            # b = flags
            '1 0 -1 0 -1 0 2048 0 0',
            '14 0 -1 0 -1 0 2048 0 0',
            '28 1 0 1 1 1 1 18446744073709551615 0',   # fd = the set, newfd = the target, a = cmd, b = events, value = data
            '28 1 0 3 2 1 4 7 0',                   # the target as a pipe end
            '29 1 0 0 -1 16 0 0 0',                 # a = maxevents, b = timeout
            '28 0 20 1 1 2 0 0 0',
            '2 1 0 0 -1 0 0 0 0',
            '29 1 7 0 -1 1 0 0 0',
        ])

    def test_domain(self):
        invalid = [
            lambda t: t['ops'][3].update(epfd={"ref": 1}),            # a ref to a non-producer? eventfd2 is one: fine; a read is not
            lambda t: t['ops'][3].update(fd={"literal": 3}),           # a reserved fixture descriptor
            lambda t: t['ops'][3].update(cmd=-1),
            lambda t: t['ops'][3].update(cmd=2**32),
            lambda t: t['ops'][3].update(events=-1),
            lambda t: t['ops'][3].update(data=5),                      # data is a decimal string
            lambda t: t['ops'][3].update(data="18446744073709551616"),
            lambda t: t['ops'][3].update(data="01"),
            lambda t: t['ops'][3].pop("data"),
            lambda t: t['ops'][5].update(maxevents="16"),
            lambda t: t['ops'][5].update(timeout="0"),
            lambda t: t['ops'][5].update(epfd={"ref": 5}),             # not earlier
            lambda t: t['ops'][0].update(flags=-1),
            lambda t: t['ops'][0].update(init=0),                      # not a field of epoll_create1
        ]
        invalid[0] = lambda t: t['ops'][3].update(epfd={"ref": 5})    # a forward reference
        for mutation in invalid:
            with self.subTest(mutation=mutation):
                altered = deepcopy(self.EPOLL)
                mutation(altered)
                with self.assertRaises(InvalidTrace):
                    validate_trace(altered)
        # tier 1's bounds are explicit unsupported inputs, not invalid ones
        for mutation in (lambda t: t['ops'][5].update(maxevents=0), lambda t: t['ops'][5].update(maxevents=17),
                         lambda t: t['ops'][5].update(timeout=1), lambda t: t['ops'][5].update(timeout=-1)):
            with self.subTest(mutation=mutation):
                altered = deepcopy(self.EPOLL)
                mutation(altered)
                with self.assertRaises(UnsupportedTrace):
                    validate_trace(altered)


class SeccompContractTests(unittest.TestCase):
    """seccomp stream W (docs/2026-10-12-seccomp-design.md section 6;
    contracts/trace-v1.md, Seccomp): the five operations, their wire fields,
    the child fixture and the validator's rules (the kill scan, strict
    child-only, the probe set, the fixture exclusions)."""

    ALLOW = [[0x06, 0, 0, 0x7fff0000]]                          # RET ALLOW
    KILL = [[0x06, 0, 0, 0]]                                     # RET KILL_THREAD
    TRAP = [[0x20, 0, 0, 0], [0x15, 0, 1, 102], [0x06, 0, 0, 0x00030000 | 7], [0x06, 0, 0, 0x7fff0000]]
    SECCOMP = {"version": 1, "id": "seccomp", "seccomp_child": True, "rlimit_nofile": 16, "ops": [
        {"op": "seccomp_prctl", "cmd": "get_seccomp"},                                   # 0
        {"op": "seccomp_query", "cmd": "get_action_avail", "action": 0x7fff0000},        # 1
        {"op": "seccomp_query", "cmd": "get_notif_sizes", "flags": 1},                   # 2
        {"op": "seccomp_install", "via": "seccomp", "flags": ["log"], "filter": TRAP},   # 3
        {"op": "seccomp_probe", "nr": 102, "where": "self", "args": [1, 2, 3, 4, 5, 2**64 - 1]},   # 4
        {"op": "seccomp_install", "via": "prctl", "flags": [], "filter": KILL, "mode": 3},   # 5
        {"op": "seccomp_probe", "nr": 102, "where": "child"},                            # 6
        {"op": "seccomp_probe", "nr": 60, "where": "child", "strict": "prctl"},           # 7
        {"op": "seccomp_capdrop"},                                                       # 8
        {"op": "seccomp_prctl", "cmd": "set_no_new_privs", "arg2": 1, "arg5": 2**64 - 1},   # 9
        {"op": "seccomp_install", "via": "seccomp", "flags": [64], "filter": None},     # 10: the flag-mask arm, a NULL program
        {"op": "seccomp_install", "via": "seccomp", "flags": [], "filter": ALLOW, "len": 4097, "bad": "insns"},   # 11
    ]}

    def test_wire(self):
        trace = validate_trace(self.SECCOMP)
        lines = serialize_wire([trace]).splitlines()[5:]
        self.assertEqual(lines[0], 'T seccomp 12 16 0 0 0 0 1')                 # the eighth field: seccomp_child
        self.assertEqual(lines[1], '32 0 -1 0 -1 2 0 0 0 ' + '00' * 32)         # a = cmd, four zero arguments
        self.assertEqual(lines[2], '34 0 -1 0 -1 0 2147418112 0 0')             # a = cmd, b = action, value = flags
        self.assertEqual(lines[3], '34 0 -1 0 -1 1 0 1 0')
        self.assertEqual(lines[4], f'30 0 -1 0 -1 {2 << 8} 2 0 0 ' + '2000000000000000' + '1500000166000000' + '0600000007000300' + '060000000000ff7f')
        self.assertEqual(lines[5], '31 0 -1 0 -1 102 0 0 0 ' + ''.join(x.to_bytes(8, 'little').hex() for x in (1, 2, 3, 4, 5, 2**64 - 1)))
        self.assertEqual(lines[6], f'30 0 -1 0 -1 {1 | 3 << 8} 0 0 0 0600000000000000')   # prctl, mode 3, no flags
        self.assertEqual(lines[7], '31 0 -1 0 -1 102 1 0 0 ' + '00' * 48)                   # where = child
        self.assertEqual(lines[8], f'31 0 -1 0 -1 60 {1 | 2 << 8} 0 0 ' + '00' * 48)        # strict = prctl
        self.assertEqual(lines[9], '33 0 -1 0 -1 0 0 0 0')
        self.assertEqual(lines[10], '32 0 -1 0 -1 0 0 0 0 ' + (1).to_bytes(8, 'little').hex() + '00' * 16 + 'ff' * 8)
        self.assertEqual(lines[11], f'30 0 -1 0 -1 {2 << 8} {64 | 3 << 16} 0 0 ')          # bad 3: a NULL program
        self.assertEqual(lines[12], f'30 0 -1 0 -1 {2 << 8} {2 << 16} {(1 << 32) | 4097} 0 ' + '060000000000ff7f')   # len override, bad insns

    def test_kill_scan(self):
        self.assertFalse(filter_may_kill(self.ALLOW))
        self.assertFalse(filter_may_kill(self.TRAP))
        self.assertFalse(filter_may_kill([[0x06, 0, 0, 0x7ffc0000], [0x06, 0, 0, 0x7ff00000], [0x06, 0, 0, 0x00050001]]))
        self.assertTrue(filter_may_kill(self.KILL))
        self.assertTrue(filter_may_kill([[0x06, 0, 0, 0x80000000]]))      # KILL_PROCESS
        self.assertTrue(filter_may_kill([[0x06, 0, 0, 0x7fc00000]]))      # USER_NOTIF
        self.assertTrue(filter_may_kill([[0x06, 0, 0, 0x00010000]]))      # non-canonical
        self.assertTrue(filter_may_kill([[0x16, 0, 0, 0]]))               # RET|A
        self.assertTrue(filter_may_kill([[0x3c, 0, 0, 0], [0x06, 0, 0, 0x7fff0000]]))   # DIV|X
        self.assertFalse(filter_may_kill([[0x9c, 0, 0, 0], [0x06, 0, 0, 0x7fff0000]]))  # MOD|X: rejected at the install, never runs
        self.assertFalse(filter_may_kill(None))

    def test_domain(self):
        invalid = [
            lambda t: t['ops'][6].update(where="self"),                   # a self probe after a filter that may kill (op 5)
            lambda t: t['ops'][4].update(strict="seccomp"),              # strict is child-only
            lambda t: t['ops'][4].update(nr=1),                           # outside the probe set
            lambda t: t['ops'][7].update(nr=1),                           # a strict child: 60 joins the set, 1 does not
            lambda t: t['ops'][4].update(args=[0] * 5),
            lambda t: t['ops'][4].update(where="elsewhere"),
            lambda t: t['ops'][3].update(via="ioctl"),
            lambda t: t['ops'][3].update(flags=["log", "nope"]),
            lambda t: t['ops'][3].update(flags=[65536]),
            lambda t: t['ops'][5].update(flags=["log"]),                  # prctl passes no flags
            lambda t: t['ops'][3].update(mode=2),                         # mode is prctl's
            lambda t: t['ops'][3].update(filter=[]),
            lambda t: t['ops'][3].update(filter=[[0x06, 0, 0, 0x7fff0000]] * 4097),
            lambda t: t['ops'][3].update(filter=[[0x06, 256, 0, 0]]),
            lambda t: t['ops'][3].update(len=65536),
            lambda t: t['ops'][3].update(bad="pointer"),
            lambda t: t['ops'][10].update(bad="insns"),                   # a null filter is the NULL arm already
            lambda t: t['ops'][0].update(cmd="get_thp"),
            lambda t: t['ops'][9].update(arg2=-1),
            lambda t: t['ops'][1].update(cmd="get_notif_sizes"),          # action only with get_action_avail
            lambda t: t['ops'][2].update(action=0),
            lambda t: t['ops'][1].update(flags=2**32),
            lambda t: t.update(seccomp_child=1),
            lambda t: t.update(rlimit_nofile=8),                          # descriptor 8 needs room
            lambda t: t.pop("seccomp_child"),                             # a child probe needs the declaration
            lambda t: t['ops'].append({"op": "dup", "fd": {"literal": 8}}),   # 8 is the child fixture's
            lambda t: t.update(steer=[["x", "draw"]]),                    # a steered trace has no child probe
        ]
        for mutation in invalid:
            with self.subTest(mutation=mutation):
                altered = deepcopy(self.SECCOMP)
                mutation(altered)
                with self.assertRaises(InvalidTrace):
                    validate_trace(altered)
        # a trace without a child probe must not declare the fixture; a
        # network trace never has it
        no_child = deepcopy(self.SECCOMP)
        no_child['ops'] = [op for op in no_child['ops'] if op.get("where") != "child"]
        with self.assertRaises(InvalidTrace):
            validate_trace(no_child)
        del no_child['seccomp_child']
        validate_trace(no_child)
        net = deepcopy(self.SECCOMP)
        net['ops'].append({"op": "wg_get"})
        with self.assertRaises(InvalidTrace):
            validate_trace(net)
        # the control-suite inputs are valid: the mirror stops on them
        for flags in (["tsync"], ["new_listener"], ["tsync", "new_listener", "tsync_esrch"], ["wait_killable_recv", "new_listener"]):
            altered = deepcopy(self.SECCOMP)
            altered['ops'][3].update(flags=flags)
            validate_trace(altered)


class OpcodeTableTests(unittest.TestCase):
    """The wire opcode table (harness/trace.py OPCODES, explicit since the D3
    merge: a positional derivation gave pipe2 and wg_advance the same code)
    and its mirror in harness/guest.c (OP_* #defines). Fail closed: every
    operation has a code, codes are distinct and disjoint from the reserved
    ones, the guest defines exactly the same names and codes, and the guest
    compares opcodes only through those names."""

    GUEST = (ROOT / "harness" / "guest.c").read_text()

    def test_codes_distinct_and_complete(self):
        self.assertEqual(set(OPCODES), set(FIELDS))
        codes = list(OPCODES.values()) + list(RESERVED_OPCODES)
        self.assertEqual(len(codes), len(set(codes)))
        self.assertTrue(all(isinstance(c, int) and c >= 1 for c in codes))
        self.assertEqual((OPCODES["pipe2"], OPCODES["wg_advance"]), (14, 19))
        self.assertEqual((OPCODES["wg_create"], OPCODES["wg_down"], OPCODES["wg_delete"]), (15, 16, 17))
        # E-B took its reserved code 18 at the int-e merge; the interface commit
        # reserves 20-24 for the W streams (docs/2026-10-11-interface.md)
        self.assertEqual(OPCODES["wg_flood"], 18)
        # W9 took 23 and 24 (wg_deladdr, wg_delroute), W8 took 22 (wg_netns_close)
        self.assertEqual(sorted(RESERVED_OPCODES), [20, 21])
        self.assertEqual((OPCODES["wg_deladdr"], OPCODES["wg_delroute"], OPCODES["wg_netns_close"]), (23, 24, 22))
        self.assertTrue(all(isinstance(v, str) and v for v in RESERVED_OPCODES.values()))
        self.assertFalse(set(OPCODES.values()) & set(RESERVED_OPCODES))
        self.assertEqual(sorted(c for n, c in OPCODES.items()
                                if n not in ("pipe2", "wg_advance", "wg_create", "wg_down", "wg_delete", "wg_flood",
                                             "wg_set_mtu", "wg_batch", "wg_deladdr", "wg_delroute", "wg_netns_close",
                                             "epoll_create1", "epoll_ctl", "epoll_wait",
                                             "seccomp_install", "seccomp_probe", "seccomp_prctl", "seccomp_capdrop",
                                             "seccomp_query")),
                         list(range(1, 14)))
        # W4+W7's codes, allocated by the coordinator (docs/2026-10-11-interface.md)
        self.assertEqual((OPCODES["wg_set_mtu"], OPCODES["wg_batch"]), (25, 26))
        # epoll R's codes (docs/2026-10-11-interface.md, next targets)
        self.assertEqual((OPCODES["epoll_create1"], OPCODES["epoll_ctl"], OPCODES["epoll_wait"]), (27, 28, 29))
        # seccomp W's codes (docs/2026-10-11-interface.md, next targets)
        self.assertEqual(tuple(OPCODES[n] for n in ("seccomp_install", "seccomp_probe", "seccomp_prctl",
                                                    "seccomp_capdrop", "seccomp_query")), (30, 31, 32, 33, 34))

    def test_guest_defines_match(self):
        defines = {name.lower(): int(code) for name, code in re.findall(r"^#define OP_(\w+) (\d+)$", self.GUEST, re.M)}
        self.assertEqual(defines, OPCODES)

    def test_reserved_opcodes_are_rejected_everywhere(self):
        # no name maps to a reserved code (a trace cannot ask for one), the
        # guest defines none of them, and its switch fails any other code
        self.assertFalse(set(RESERVED_OPCODES) & set(OPCODES.values()))
        defines = {int(code) for code in re.findall(r"^#define OP_\w+ (\d+)$", self.GUEST, re.M)}
        self.assertFalse(defines & set(RESERVED_OPCODES))
        self.assertRegex(self.GUEST, r'default: fail\(t->id, i, "invalid_input", "wire_opcode"\);')
        for code in RESERVED_OPCODES:
            with self.assertRaises(InvalidTrace):
                validate_trace({"version": 1, "id": "r", "ops": [{"op": f"reserved_{code}"}]})

    def test_guest_has_no_numeric_opcodes(self):
        numeric = re.findall(r"(?:code\s*[!=<>]=?\s*\d+|\bcase\s+\d+\s*:)", self.GUEST)
        self.assertEqual(numeric, [])


@unittest.skipUnless(shutil.which("gcc"), "needs gcc")
class GuestHashTests(unittest.TestCase):
    """harness/guest.c's BLAKE2s-256 and write pattern, compiled on the host
    into a driver that includes the guest source with its main renamed; no
    trace operation runs (only the guest's pure helpers)."""

    DRIVER = r"""
#define main guest_main
#include "guest.c"
#undef main
int main(void)
{
    blake2s_self_test();
    static char text[2 * MAX_IO + 16];
    static unsigned char data[MAX_IO];
    while (fgets(text, sizeof(text), stdin)) {
        unsigned i, count;
        unsigned long long value;
        if (sscanf(text, "W %u %llu %u", &i, &value, &count) == 3) {
            fill_write_buffer(i, value, count);
            print_hex_bytes(write_buffer, count < 8 ? 8 : count);
            printf("\n");
            continue;
        }
        size_t n = strcspn(text, "\n") / 2;
        for (size_t k = 0; k < n; ++k) { unsigned b; sscanf(text + 2 * k, "%2x", &b); data[k] = (unsigned char)b; }
        unsigned char digest[32];
        blake2s256(data, n, digest);
        print_hex_bytes(digest, 32);
        printf("\n");
    }
    return 0;
}
"""

    @classmethod
    def setUpClass(cls):
        cls.dir = ROOT / ".cache" / "tmp" / f"guest-hash-{os.getpid()}"
        cls.dir.mkdir(parents=True, exist_ok=True)
        (cls.dir / "driver.c").write_text(cls.DRIVER)
        subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-std=c11", "-I", str(ROOT / "harness"),
                        str(cls.dir / "driver.c"), "-o", str(cls.dir / "driver")], check=True)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def run_driver(self, lines):
        out = subprocess.run([str(self.dir / "driver")], input="".join(l + "\n" for l in lines),
                             capture_output=True, text=True, check=True)
        return out.stdout.splitlines()

    def test_blake2s_matches_hashlib(self):
        rng = random.Random(3)
        sizes = [0, 1, 7, 8, 63, 64, 65, 127, 128, 129, 4095, 4096, 4097, 65536, 69632] + [rng.randrange(1, 69633) for _ in range(8)]
        inputs = [bytes(rng.randrange(256) for _ in range(n)) for n in sizes]
        self.assertEqual(self.run_driver([d.hex() for d in inputs]), [hashlib.blake2s(d).hexdigest() for d in inputs])

    def test_write_pattern(self):
        def pattern(i, value, count):
            return bytes(value >> (8 * k) & 0xff if k < 8 else (7 * i + 13 * k + 17 * (k >> 8)) % 256
                         for k in range(max(count, 8)))
        cases = [(0, 1, 8), (3, 2**64 - 1, 0), (63, 12345678901234567, 69632), (17, 5, 4097), (1, 0, 300)]
        self.assertEqual(self.run_driver([f"W {i} {v} {c}" for i, v, c in cases]),
                         [pattern(i, v, c).hex() for i, v, c in cases])


class LifecycleWireTests(unittest.TestCase):
    """L's operations and fixture on the wire, and the guest's KCOV area
    against the host's bounds (moved out of GuestHashTests at the int-dl
    merge: no compiler needed)."""

    def test_lifecycle_operations_and_bare_fixture(self):
        # L (docs/2026-10-05-l-lifecycle.md section 6): opcodes 15-17, the
        # bare fixture as the wire's net 2, only on network traces; P's ninth
        # wire field (pause_ms) is 0.
        self.assertEqual([OPCODES[n] for n in ("wg_create", "wg_down", "wg_delete")], [15, 16, 17])
        self.assertEqual(len(set(OPCODES.values())), len(OPCODES))
        trace = {"version": 1, "id": "life", "net_fixture": "bare",
                 "ops": [{"op": "wg_create"}, {"op": "wg_down"}, {"op": "wg_delete"}]}
        self.assertEqual(validate_trace(trace), trace)
        wire = serialize_wire([trace], dispatch=[1])
        self.assertIn("\nT life 3 32 2 0 1 0 0\n15 0 -1 0 -1 0 0 0 0\n16 0 -1 0 -1 0 0 0 0\n17 0 -1 0 -1 0 0 0 0\n", wire)
        del trace["net_fixture"]
        self.assertIn("\nT life 3 32 1 0 1 0 0\n", serialize_wire([trace], dispatch=[1]))
        for bad in ({"net_fixture": "wg0"}, {"net_fixture": True}, {"net_fixture": "bare", "ops": [{"op": "dup", "fd": {"literal": 8}}]}):
            with self.subTest(bad=bad):
                with self.assertRaises(InvalidTrace):
                    validate_trace(dict(trace, **bad))
        with self.assertRaises(InvalidTrace):
            validate_trace(dict(trace, ops=[{"op": "wg_create", "extra": 1}]))

    def test_guest_capacity_matches_host_bounds(self):
        guest = (Path(__file__).resolve().parent / "guest.c").read_text()
        match = re.search(r"#define CAPACITY \((\d+)UL \* 1024\)", guest)
        self.assertIsNotNone(match)
        self.assertEqual(int(match.group(1)) * 1024, KCOV_CAPACITY)


if __name__ == '__main__':
    unittest.main()
