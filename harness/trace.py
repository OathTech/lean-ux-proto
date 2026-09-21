"""Strict, dependency-free validation and guest serialization of trace v1."""
from copy import deepcopy
import json
import re


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
}
OPCODES = {name: i + 1 for i, name in enumerate(FIELDS)}
FCNTL = {"F_GETFD": 1, "F_SETFD": 2, "F_GETFL": 3}


def _integer(value, low, high, where):
    if type(value) is not int or not low <= value <= high:
        raise InvalidTrace(f"{where}: expected integer in [{low}, {high}]")


def _fields(value, keys, where):
    if type(value) is not dict or set(value) != keys:
        raise InvalidTrace(f"{where}: expected exactly {sorted(keys)}")


def validate_trace(trace):
    """Return a detached valid trace; reject all inputs outside trace v1."""
    _fields(trace, {"version", "id", "ops"}, "trace")
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
            if op["cmd"] != "F_SETFD" and op["arg"] != 0:
                raise InvalidTrace(f"ops[{i}].arg: getter argument must be zero")
        if name == "eventfd2" and not op["flags"] & 2048:
            raise InvalidTrace(f"ops[{i}].flags: EFD_NONBLOCK is required")
    return deepcopy(trace)


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


def serialize_wire(traces):
    traces = [validate_trace(trace) for trace in traces]
    if not 1 <= len(traces) <= 4096:
        raise InvalidTrace("guest batch requires 1–4096 traces")
    if len({trace['id'] for trace in traces}) != len(traces):
        raise InvalidTrace("guest batch trace identifiers must be unique")
    lines = ["LEANUX_WIRE_V1", str(len(traces))]
    for trace in traces:
        lines.append(f"T {trace['id']} {len(trace['ops'])}")
        for op in trace["ops"]:
            def fd(field):
                value = op.get(field, {"literal": -1})
                return (1, value["ref"]) if "ref" in value else (0, value["literal"])
            kind, value = fd("fd")
            newkind, newvalue = fd("newfd")
            a = op.get("init", op.get("count", FCNTL.get(op.get("cmd"), 0)))
            b = op.get("flags", op.get("arg", 0))
            lines.append(f"{OPCODES[op['op']]} {kind} {value} {newkind} {newvalue} {a} {b} {op.get('value', '0')}")
    return "\n".join(lines) + "\n"
