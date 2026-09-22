# Configured source and correspondence, version 1

These records describe the native x86-64 Linux 6.12.110 build at commit
`fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c` and the frozen FD/eventfd trace domain.
They support step-by-step source review and behavioral comparison of the
executable model. They do not establish complete computational correspondence
merely by recording source locations.

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

## Step correspondence and remaining gaps

The configured `eventfd_ctx_do_read` computation selects the output from the
semaphore flag and counter, assigns the output, then subtracts that stored value
from the counter. The executable mirror must retain the corresponding computation
and ordered updates, with intermediate states traceable to the source. Its
`eventfd_read` caller holds the context lock, passes a separate local output slot,
and checks a nonzero counter before calling the helper.

Descriptor removal must preserve other descriptors' access to a shared file.
Validate that behavior through the executable model and Linux comparisons. Record
source-side ownership and reclamation abstractions explicitly.

The handwritten Lean proof references, theorem statements, and proof checks have
been removed. Source manifests and implementation bindings remain. Their reviewed
identities are useful provenance, but matching names, branch labels, or final
outputs alone is insufficient to establish that every modeled step corresponds
to Linux. Unresolved source and intermediate-state correspondence remains work
for the executable mirror.
