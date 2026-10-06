"""Strict, dependency-free validation and guest serialization of trace v1."""
from copy import deepcopy
import json
import re

from .wg import InvalidConfig, encode_get, encode_packet, encode_set, validate_config, validate_packet


class InvalidTrace(ValueError):
    kind = "invalid_input"


class UnsupportedTrace(InvalidTrace):
    kind = "unsupported_input"


PRODUCERS = {"eventfd2", "dup", "dup3"}
FIELDS = {
    "eventfd2": {"op", "init", "flags"}, "dup": {"op", "fd"},
    "dup3": {"op", "fd", "newfd", "flags"}, "close": {"op", "fd"},
    "read": {"op", "fd", "count"}, "write": {"op", "fd", "count", "value"},
    "fcntl": {"op", "fd", "cmd", "arg"},
    # WireGuard configuration of the fixture's `wg0` (harness/wg.py)
    "wg_set": {"op", "config"}, "wg_get": {"op"},
    # Stage B1: bring wg0 up, send a packet into it, observe what it emitted
    "wg_up": {"op"}, "wg_xmit": {"op", "packet"}, "wg_observe": {"op"},
    # Stage B2: a raw WireGuard message sent to wg0's listen port
    "wg_inject": {"op", "family", "port", "message"},
    # D3: the virtual time advance by `ticks` jiffies (docs/2026-10-05-d3-timers.md, 4.3)
    "wg_advance": {"op", "ticks"},
}
WG_OPS = {"wg_set", "wg_get", "wg_up", "wg_xmit", "wg_observe", "wg_inject", "wg_advance"}
OPCODES = {name: i + 1 for i, name in enumerate(FIELDS)}
FCNTL = {"F_GETFD": 1, "F_SETFD": 2, "F_GETFL": 3, "F_SETFL": 4}


def _integer(value, low, high, where):
    if type(value) is not int or not low <= value <= high:
        raise InvalidTrace(f"{where}: expected integer in [{low}, {high}]")


def _fields(value, keys, where):
    if type(value) is not dict or set(value) != keys:
        raise InvalidTrace(f"{where}: expected exactly {sorted(keys)}")


def validate_trace(trace):
    """Return a detached valid trace; reject all inputs outside trace v1."""
    if type(trace) is not dict or not {"version", "id", "ops"} <= set(trace) <= {"version", "id", "ops", "rlimit_nofile", "steer", "expect"}:
        raise InvalidTrace("trace: expected exactly ['id', 'ops', 'version'] and optionally 'rlimit_nofile', 'steer', 'expect'")
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
        if "steer" not in trace:
            raise InvalidTrace("expect: only a steered trace states expected outcomes")
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
        _fields(op, FIELDS[name], f"ops[{i}]")
        for field in ("init", "flags", "arg"):
            if field in op:
                _integer(op[field], 0, 2**32 - 1, f"ops[{i}].{field}")
        for field in ("fd", "newfd"):
            if field not in op:
                continue
            fd = op[field]
            if type(fd) is not dict or set(fd) not in ({"literal"}, {"ref"}):
                raise InvalidTrace(f"ops[{i}].{field}: expected literal or ref")
            if "literal" in fd:
                _integer(fd["literal"], -(2**31), 2**31 - 1, f"ops[{i}].{field}.literal")
                if 0 <= fd["literal"] < 8:
                    raise InvalidTrace(f"ops[{i}].{field}: reserved fixture descriptor")
            else:
                _integer(fd["ref"], 0, i - 1, f"ops[{i}].{field}.ref")
                if ops[fd["ref"]]["op"] not in PRODUCERS:
                    raise InvalidTrace(f"ops[{i}].{field}: reference must name FD producer")
        if "count" in op:
            _integer(op["count"], 0, 16, f"ops[{i}].count")
        if name == "write":
            value = op["value"]
            if type(value) is not str or not re.fullmatch(r"0|[1-9][0-9]{0,19}", value, re.ASCII) or int(value) >= 2**64:
                raise InvalidTrace(f"ops[{i}].value: expected canonical uint64 decimal string")
        if name == "fcntl":
            if type(op["cmd"]) is not str or op["cmd"] not in FCNTL:
                raise UnsupportedTrace(f"ops[{i}].cmd: unsupported fcntl command")
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
        if name == "wg_advance":
            _integer(op["ticks"], 1, 2**31, f"ops[{i}].ticks")
        if name == "wg_xmit":
            try:
                validate_packet(op["packet"], f"ops[{i}].packet")
            except InvalidConfig as exc:
                raise InvalidTrace(str(exc)) from exc
    return deepcopy(trace)


def uses_wireguard(trace):
    """Traces with WireGuard operations get the network fixture: a fresh
    network namespace with `lo` up and a down `wg0`; UDP listeners on
    127.0.0.1 and ::1 at descriptors 4 and 5, a dual-stack UDP sender at 6,
    and the generic-netlink socket at 7, in place of the /dev/null fillers.
    `wg_up` also adds an address and a default route on `wg0` per family."""
    return any(op["op"] in WG_OPS for op in trace["ops"])


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


def serialize_wire(traces, steer_wire=None, dispatch=(), arm_records=False):
    """`steer_wire`: each steered trace's resolved schedule
    (harness/steer.py), [(kind, length, draw, [return addresses], hex)].
    `dispatch`: the dispatch set's function addresses (harness/linux.py),
    which a batch with network traces needs. `arm_records`: whether the
    kernel writes the kind-303 arm records for the dispatch set's timers
    (the `A` line; D3)."""
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
    if len(dispatch) > 16 or any(type(a) is not int or a <= 0 for a in dispatch):
        raise InvalidTrace("dispatch set")
    if type(arm_records) is not bool:
        raise InvalidTrace("arm_records")
    lines = ["LEANUX_WIRE_V2", str(len(traces)), " ".join(["D", str(len(dispatch))] + [f"{a:x}" for a in dispatch]),
             f"A {int(arm_records)}"]
    for trace in traces:
        schedule = steer_wire.get(trace["id"], []) if "steer" in trace else []
        lines.append(f"T {trace['id']} {len(trace['ops'])} {trace.get('rlimit_nofile', 32)} {int(uses_wireguard(trace))} {len(schedule)}")
        for op in trace["ops"]:
            def fd(field):
                value = op.get(field, {"literal": -1})
                return (1, value["ref"]) if "ref" in value else (0, value["literal"])
            kind, value = fd("fd")
            newkind, newvalue = fd("newfd")
            a = op.get("init", op.get("count", FCNTL.get(op.get("cmd"), 0)))
            b = op.get("flags", op.get("arg", 0))
            if op["op"] == "wg_xmit":
                a, packet = encode_packet(op["packet"])
            if op["op"] == "wg_inject":
                a, b = op["family"], op["port"]
            if op["op"] == "wg_advance":
                a = op["ticks"]
            line = f"{OPCODES[op['op']]} {kind} {value} {newkind} {newvalue} {a} {b} {op.get('value', '0')}"
            if op["op"] == "wg_set":
                line += " " + encode_set(op["config"]).hex()
            elif op["op"] == "wg_get":
                line += " " + encode_get().hex()
            elif op["op"] == "wg_xmit":
                line += " " + packet.hex()
            elif op["op"] == "wg_inject":
                line += " " + op["message"]
            lines.append(line)
        for kind, length, draw, ips, value in schedule:
            ips = (list(ips) + [0, 0, 0, 0])[:4]
            lines.append(f"S {kind} {length} {int(draw)} " + " ".join(f"{ip:x}" for ip in ips) + f" {'' if draw else value}")
    return "\n".join(lines) + "\n"
