"""Import an explicit, sequential subset of saved Linux/amd64 syzkaller text.

This parses data only. It never executes a program or starts an executor.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

from .trace import InvalidTrace, validate_trace

ADAPTER_VERSION = 1
ENCODING_BASE = 0x7F0000000000
MAPPED_BYTES = 16 << 20
MAX_INPUT_BYTES = 64 << 10
NUMBER = r"(?:0x[0-9a-fA-F]+|0|[1-9][0-9]*)"
CALL = re.compile(r"(?:(r[0-9]+)\s*=\s*)?([A-Za-z0-9_]+(?:\$[A-Za-z0-9_]+)?)\s*\((.*)\)", re.ASCII)
POINTER = re.compile(r"&\(\s*(" + NUMBER + r")\s*\)(?:\s*=\s*(.*))?", re.ASCII)
SUPPORTED = {"eventfd2", "dup", "dup3", "close", "read$eventfd", "write$eventfd", "read", "write", "fcntl$getflags", "fcntl$setflags"}


class SyzkallerImportError(ValueError):
    kind = "unsupported_input"

    def __init__(self, code, detail, line=None):
        super().__init__(f"line {line}: {detail}" if line else detail)
        self.code, self.detail, self.line = code, detail, line


def _reject(code, detail):
    raise SyzkallerImportError(code, detail)


def _number(text, bits=64):
    if not re.fullmatch(NUMBER, text):
        _reject("integer_expression", "Expected an explicit unsigned decimal or hexadecimal integer")
    value = int(text, 16 if text.startswith("0x") else 10)
    if value >= 1 << bits:
        _reject("integer_width", f"Integer exceeds the supported unsigned {bits}-bit width")
    return value


def _arguments(text):
    """Split only outer commas; compound forms are rejected by each argument parser."""
    parts, start, depth, quote = [], 0, 0, None
    for index, char in enumerate(text):
        if quote:
            if char == "\\":
                _reject("escaped_string", "Escaped or compressed buffers are outside this subset")
            if char == quote:
                quote = None
        elif char in ('"', "'"):
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                _reject("call_properties", "Trailing call properties or malformed parentheses are unsupported")
        elif char == "," and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
    if quote or depth:
        _reject("argument_syntax", "Unclosed argument syntax")
    parts.append(text[start:].strip())
    if any(not part for part in parts):
        _reject("argument_syntax", "Missing argument")
    return parts


def _fd(text, references):
    if re.fullmatch(r"r[0-9]+", text):
        if text not in references:
            _reject("unknown_reference", "Descriptor reference has no earlier producer")
        return {"ref": references[text]}
    if text.startswith("r"):
        _reject("resource_arithmetic", "Result arithmetic and indirect resources are unsupported")
    value = _number(text)
    # Linux takes an int even when a syzkaller resource literal uses 64 bits.
    low = value & 0xFFFFFFFF
    return {"literal": low - (1 << 32) if low & (1 << 31) else low}


def _buffer(text, name, count):
    pointer = POINTER.fullmatch(text)
    if not pointer:
        _reject("pointer_form", "Require an explicit mapped &(address) buffer; special/automatic pointers are unsupported")
    address = _number(pointer[1])
    if not ENCODING_BASE <= address <= ENCODING_BASE + MAPPED_BYTES - 16:
        _reject("pointer_range", "A complete 16-byte footprint must lie in the serialized 16 MiB data region")
    initializer = pointer[2]
    if name == "read$eventfd":
        if initializer is not None and _number(initializer) != 0:
            _reject("output_initializer", "Typed output buffers permit only an omitted or zero initializer")
        return None
    if name == "write$eventfd":
        if initializer is None:
            _reject("implicit_write_data", "Typed writes require an explicit uint64 initializer")
        return _number(initializer)
    if initializer is None:
        _reject("implicit_buffer", "Generic buffers require explicit content or output size")
    if name == "read":
        output = re.fullmatch(r'""\s*/\s*(' + NUMBER + ')', initializer)
        if not output:
            _reject("output_buffer", 'Generic reads require =""/SIZE')
        size = _number(output[1])
        if not count <= size <= 16:
            _reject("buffer_size", "Output buffer must contain count bytes and be at most 16 bytes")
        return None
    data = re.fullmatch(r'"([0-9a-fA-F]*)"', initializer)
    if not data or len(data[1]) % 2:
        _reject("input_buffer", "Generic writes require an explicit even-length hexadecimal byte string")
    payload = bytes.fromhex(data[1])
    if not count <= len(payload) <= 16:
        _reject("buffer_size", "Input buffer must contain count bytes and be at most 16 bytes")
    if any(payload[8:]):
        _reject("write_padding", "Bytes after the first uint64 must be zero in trace v1")
    return int.from_bytes(payload[:8].ljust(8, b"\0"), "little")


def parse_program(text, trace_id, *, target="linux/amd64"):
    """Return a trace-v1 object, or reject the entire program with a precise reason."""
    if target != "linux/amd64":
        _reject("target", "Only the staged Linux/amd64 ABI is supported")
    if type(text) is not str or not text.isascii() or len(text.encode("utf-8")) > MAX_INPUT_BYTES:
        _reject("input_size_or_encoding", "Input must be ASCII and at most 64 KiB")
    references, operations = {}, []
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        try:
            match = CALL.fullmatch(line)
            if not match:
                _reject("call_syntax", "Expected one complete supported call per line")
            assignment, name, arguments = match.groups()
            if name not in SUPPORTED:
                _reject("syscall", f"Unsupported syscall description: {name}")
            args = _arguments(arguments)
            expected = {"eventfd2": 2, "dup": 1, "dup3": 3, "close": 1, "fcntl$getflags": 2}.get(name, 3)
            if len(args) != expected:
                _reject("argument_count", f"{name} requires exactly {expected} arguments")
            if assignment is not None:
                if name not in {"eventfd2", "dup", "dup3"}:
                    _reject("assignment", "Only descriptor-producing calls may bind result names")
                if assignment in references:
                    _reject("reference_redefinition", "Result names may not be rebound")
            if name == "eventfd2":
                op = {"op": name, "init": _number(args[0], 32), "flags": _number(args[1], 32)}
            elif name in {"dup", "close"}:
                op = {"op": name, "fd": _fd(args[0], references)}
            elif name == "dup3":
                op = {"op": name, "fd": _fd(args[0], references), "newfd": _fd(args[1], references), "flags": _number(args[2], 32)}
            elif name.startswith("fcntl$"):
                command = _number(args[1], 32)
                admitted = {1: "F_GETFD", 3: "F_GETFL"} if name == "fcntl$getflags" else {2: "F_SETFD"}
                if command not in admitted:
                    _reject("fcntl_command", "Only GETFD, GETFL, and SETFD are supported")
                op = {"op": "fcntl", "fd": _fd(args[0], references), "cmd": admitted[command], "arg": _number(args[2], 32) if len(args) == 3 else 0}
            else:
                count = _number(args[2])
                if count > 16:
                    _reject("io_length", "Only allocated-buffer I/O lengths 0–16 are supported")
                value = _buffer(args[1], name, count)
                op = {"op": name.split("$")[0], "fd": _fd(args[0], references), "count": count}
                if value is not None:
                    op["value"] = str(value)
            operations.append(op)
            # This catches domain failures at their source line, including NONBLOCK.
            validate_trace({"version": 1, "id": trace_id, "ops": operations})
            if assignment is not None:
                references[assignment] = len(operations) - 1
        except InvalidTrace as exc:
            raise SyzkallerImportError("trace_domain", str(exc), lineno) from exc
        except SyzkallerImportError as exc:
            raise SyzkallerImportError(exc.code, exc.detail, lineno) from exc
    try:
        return validate_trace({"version": 1, "id": trace_id, "ops": operations})
    except InvalidTrace as exc:
        raise SyzkallerImportError("trace_domain", str(exc)) from exc


def import_program(text, trace_id, *, target="linux/amd64"):
    """Return an auditable accepted/rejected record; never silently drop a call."""
    record = {"adapter_version": ADAPTER_VERSION, "format": "syzkaller-text-subset", "target": target,
              "source_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
              "fixture": "trace-v1: reserved descriptors 0–7, limit32, sequential, nonblocking"}
    try:
        record.update(status="accepted", trace=parse_program(text, trace_id, target=target))
    except SyzkallerImportError as exc:
        record.update(status="rejected", kind=exc.kind, reason={"code": exc.code, "detail": exc.detail, "line": exc.line})
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--id", required=True)
    args = parser.parse_args()
    record = import_program(args.source.read_text(), args.id)
    print(json.dumps(record, sort_keys=True))
    return 0 if record["status"] == "accepted" else 2


if __name__ == "__main__":
    raise SystemExit(main())
