# Configured source and correspondence, version 1

These records describe the native x86-64 Linux 6.12.110 build at commit
`fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c` and the frozen FD/eventfd trace domain.
They support review and local proof construction. They do not establish a
simulation relation with a formal semantics of the kernel's C implementation.

`helpers-v1.json` inventories 19 helper groups and 82 selected source branches.
Each branch is represented, excluded by the domain, abstracted with a stated
contract, absent in this configuration, or unresolved. Exclusion is explicit;
an untested supported branch cannot be relabeled excluded to make a run pass.
`testability-v1.json` records all seven operation forms, actual syscall dispatch,
source-derived test obligations, external helper contracts, and future domain
extensions. `model-bindings-v1.json` maps every executable model definition and
reported branch label to these records or to experiment machinery.

The selected branch inventory is an audit of the retained helpers, not an
exhaustive CFG of all eight preprocessed translation units. For example,
`eventfd_poll`, `eventfd_signal_mask`, unrelated `fcntl` commands, other file
kinds, and VFS functions not reached by this fixture are outside the slice.

## Capture and validation

Run `scripts/in-bundle python3 scripts/capture-correspondence.py`. It reads the
accepted build's `.cmd` records and preprocesses eight units serially. The exact
GCC command and working directory are retained. Only object/dependency-output
options are removed; `-E` and a private output path are added. The trailing
objtool invocation is recorded but not executed. Source and accepted kernel
outputs remain inputs throughout. No kernel rebuild or download occurs.

Each capture includes preprocessed `.i` files, GCC line-directive maps, an active
include closure with hashes, original/adapted commands, config/generated-header
identities, compiler and compiler-wrapper identities, vmlinux/bzImage identities,
source revision from the dependency lock and an archive-member comparison for every captured source input. Copies of the capture script and
wrappers preserve the task's launch machinery after worktree cleanup. GCC's
working-directory marker is recorded separately from input files. The manifest
stores output paths relative to itself so the coordinator can promote the whole
directory into durable evidence without duplicating shared dependency stores.

`scripts/in-bundle python3 scripts/capture-correspondence.py --verify PATH`
checks a captured manifest's input and output identities. Every captured active
header contributes to the input identity; this covers the product configuration
actually used here. Other configurations need new captures and reviewed records.

`scripts/in-bundle python3 scripts/capture-correspondence.py --check-records`
checks source anchors, unique classifications, external contracts, complete
model-definition bindings, branch labels and operation coverage. During parallel
development, `--model-root PATH` reads the model worker's worktree. This check
does not infer semantic correctness from declaration names or label strings.

The final capture verifies the staged release archive and every selected source member, in addition to compiler, build and output identities. Its identity and location
are recorded in `capture-v1.json`; the coordinator must promote that directory
before cleaning the task scratch directory. A failed preliminary capture is not
acceptance evidence.

## Retained computational structure

Descriptor membership, allocation cursor, limit, per-descriptor close-on-exec,
shared file identity, file status, and counter/mode form the retained state.
Lookup, allocation, installation, replacement, removal and context update have
separate executable helpers. The source's temporary open-fd reservation bitmap
is folded into the allocation/installation composition: the model advances the
cursor then installs the entry, with no operation allowed between these stages.
This abstraction would need revision for concurrent or interrupted allocation.

The initial kernel FD table has capacity 64 (`NR_OPEN_DEFAULT=BITS_PER_LONG`),
while the fixture bounds all trace descriptors below 32. Table expansion and
its retry paths are therefore outside this fixture. A descriptor reference in
the trace retains its old number after close; later reuse changes the file it
names. File identity remains separate from descriptor number.

The file's status is `O_RDWR | O_NONBLOCK` (2050). `anon_inode_getfile` masks out
close-on-exec before creating the file; that bit is descriptor-local. Semaphore
mode belongs to the eventfd context. Temporary references and unreachable
object reclamation are abstracted explicitly, rather than equating a kernel
reference count with the number of open descriptors.

## Local proof contracts

`Leanux/Reference/EventfdRead.lean` independently encodes the selected C fragment
using a UInt32 flag word, UInt64 counter/output slot, and three control points.
The reference first assigns the selected output, then subtracts that stored
output from the counter. Its transition definitions never call mirror helpers.
`EventfdContract.lean` defines `StepSimulation readValue doRead`, requiring the
two steps, intermediate and final relations, both store effects, preserved
flags/mode, and terminal state. It quantifies every related UInt64 counter and
UInt32 flag word, including zero and both semaphore modes.

The source bridge requires a held context lock, readable/writable context,
writable disjoint output storage, and no external interference. The supported
`eventfd_read` caller holds the lock and passes its separate local `ucnt` after
checking a nonzero counter. The helper theorem intentionally also covers zero,
which other callers can supply. Context and branch examples are inhabited in
Lean. These witnesses document the omitted memory/concurrency context; they are
not evidence that arbitrary real C addresses satisfy it.

`AliasContract.lean` defines `CloseAliasPreservation` over the actual `Files`,
`WellFormed`, `fileCloseFd`, and lookup APIs. Closing one of two distinct live
descriptors for the same object must succeed, remove that descriptor, and
preserve the other descriptor and its entire accessible file value. The
coordinator freezes these propositions, reference transitions, relations,
interface/admission definitions and identities before accepting proof changes.

The planned evidence category is **encoded-fragment simulation**. The formal
C-source bridge, full API simulation, concurrency, and memory safety remain
open obligations. KCOV and branch labels are execution evidence with separate
limits; neither establishes those proofs.
