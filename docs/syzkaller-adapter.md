# Restricted import of saved syzkaller programs

`harness/syzkaller_adapter.py` converts a small sequential subset of the staged
Linux/amd64 program format to the frozen trace-v1 format. This lets the prototype
reuse suitable saved or mutated operation sequences. It parses data only; it
does not run an executor, start a guest, or change the tested kernel scope.

```
scripts/in-bundle python3 -m harness.syzkaller_adapter example.syz --id imported-example
scripts/in-bundle python3 -m unittest harness.test_syzkaller_adapter
```

The CLI emits one import record. Accepted records contain the complete trace;
rejected records contain a reason code, explanation, and source line where
available. Exit codes are 0 for acceptance and 2 for rejection. Both record
forms include the input-text SHA-256, adapter version, target, and fixture name.
Callers should retain the original text alongside the record. The Python API is
`parse_program(text, trace_id, target="linux/amd64") -> trace`, raising
`SyzkallerImportError`, or `import_program(...) -> record` to retain rejection
as data. No call is silently omitted or replaced after a parse failure.

## Supported forms

There is one call per line, with optional comments and `rN =` bindings for
descriptor producers. Bindings must be unique and refer only to earlier calls.
Integers are explicit unsigned decimal or hexadecimal values. Programs are
ASCII, at most 64 KiB, and contain 1–64 operations.

| Saved-program call | Imported operation |
| --- | --- |
| `eventfd2(init, flags)` | eventfd2, with uint32 arguments (blocking mode allowed since the Phase 4 amendment) |
| `dup(fd)` | dup |
| `dup3(fd, newfd, flags)` | dup3, with uint32 flags |
| `close(fd)` | close |
| `read$eventfd(fd, &(address)[=0x0], count)` | read with an explicit valid buffer |
| `write$eventfd(fd, &(address)=uint64, count)` | write of the explicit little-endian value |
| `read(fd, &(address)=""/size, count)` | read where count ≤ size ≤ 16 |
| `write(fd, &(address)="hexbytes", count)` | write where count ≤ buffer size ≤ 16 and bytes after byte 8 are zero |
| `fcntl$getflags(fd, command)` | GETFD (1) or GETFL (3), with unused arg recorded as zero |
| `fcntl$setflags(fd, 0x2, flags)` | SETFD with uint32 flags |

All I/O counts are 0–16. Every explicit pointer must leave a complete 16-byte
footprint inside the serialized data region beginning at `0x7f0000000000`, of
size 16 MiB. Pointer addresses are projected to the trace runner's valid local
buffers. Typed writes require an explicit initializer; typed reads permit the
serializer's omitted default output initializer or an explicit zero. Generic
write bytes are decoded as little-endian, with zero padding through eight bytes.
Buffers containing structures, references, escapes, or compressed data are
outside this subset.

Descriptor literals use the low signed 32 bits, matching Linux's `int`
parameter conversion; for example `0xffffffffffffffff` becomes -1. Producer
references remain references, including stale references and failed producers.
The trace validator then applies reserved-slot, reference, length,
and all other frozen-domain rules. It rejects literals that target slots 0–7.

The adapter rejects result arithmetic, resource arrays, automatic/special
pointers, implicit write data, unsupported fcntl commands, other syscalls,
execution properties such as `async` or `fail_nth`, and any out-of-domain trace.
Rejections remain visible inputs with an explicit reason. The adapter does not
repair flags, insert calls, silently shorten programs, or infer missing values.

## Meaning and limits of an import

An import supplies an operation sequence for the existing trace fixture:
descriptors 0–7 reserved, descriptor limit 32, fresh sequential process, and
eventfds that never wait. Arbitrary syzkaller executor environments have different
inherited descriptors, resource limits, scheduling, and memory conventions.
Consequently this is a projection into the fixed experiment, not a claim that
the original executor run and the imported trace have identical observations.
Only Linux-versus-Lean evaluation of the imported trace determines agreement.
No results, expected return values, or acceptance classifications are imported
from syzkaller.

The syntax was checked against the staged revision
`853b104bb454141a5b0fc0e4218ec78e9f34ffb1`, particularly
[`prog/encoding.go`](../.deps/syzkaller/prog/encoding.go),
[`sys/linux/sys.txt`](../.deps/syzkaller/sys/linux/sys.txt), and
[`sys/targets/targets.go`](../.deps/syzkaller/sys/targets/targets.go).
The staged `syz-prog2c -strict` accepted both a typed-eventfd example and a
generic-buffer example. Their generated C files were retained as parser
evidence and were never compiled or executed. Three fixed-seed calls to staged
`syz-mutate` (seeds 2, 11, and 41) produced serialized programs accepted by this
adapter; two changed the input sequence and one retained it. This checks a
concrete integration path, not general compatibility with every program that
syzkaller can generate.

## Independent aliasing cases

`corpus/critic/` contains 32 deterministic traces with 480 operations, divided
among four families: closing the original descriptor, moving an alias to a
chosen number, replacing another live object, and probing state after errors.
Each family uses eight different counter/flag choices. The main object follows
1–4 unrelated allocations, placing its original descriptor at 9–12; moved
aliases use 18–25. Main initial counters include 2, 7, 257, 65539, 4294967295,
19, 1025, and 8193, and both ordinary and semaphore modes occur.

The traces retain unrelated objects and check their counters, use multiple
aliases, close and reuse numeric slots, replace descriptors while preserving
another alias, and follow failed operations with successful reads. These cases
are intended to distinguish a general alias-preservation repair from one
specialized to descriptor 8, counter 1, or one operation ordering. They are
independent of the initial handwritten examples. Their source was validated
locally; guest comparisons and repair acceptance belong to the coordinator's
independent evaluator.
