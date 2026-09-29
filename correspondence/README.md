# Configured source and correspondence

These files relate the mirror to the native x86-64 Linux 6.12.110 build at commit
`fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c`. The governing principle is in
[AGENTS.md](../AGENTS.md): keep data and control-flow choice points aligned
with the C. The design rules are in section 3 of the
[way-forward plan](../docs/2026-09-29-way-forward.md).

## Control-flow anchors (`kcov-anchors-v1.json`)

Each mirror branch label names the witness lines of the C arm it claims:
- `covered` lines must be covered when the label is reported;
- `uncovered` lines must be absent when the label is reported.

`python3 -m evaluator.check` compares these, for every operation, with the lines
that Linux's KCOV PCs map to through DWARF, including inline frames. The lines
were chosen from the configured C as statements executed only on that arm.
They were then validated against the recorded corpora on 2026-09-29: on every
one of 35,412 operations, each witness line was covered when its label was
reported and absent when it was not.

Details:
- **Fail-closed.** Each of the following fails the check:
  - a label with no entry;
  - an operation with no label;
  - an operation whose coverage touches no anchored file;
  - an operation whose label set is not one of the op's `paths`. This stops a
    model from omitting an arm it took. Label sets are compared as sets; step
    order becomes checkable in Phase 2.
- **Validation.** The table itself is validated on load: every line is an
  anchored `file:line`, every entry has at least one witness or a stated
  reason, and every path is made of anchored labels. A unit test checks that
  the labels in the Lean sources and in the table match exactly.
- **Unobservable labels** state why KCOV cannot see them in this build, for
  example the semaphore/ordinary select at `fs/eventfd.c:180`.
- **`known_gaps`** lists C choice points that KCOV observes but the mirror does
  not yet model. Hits are counted in the report, not failed. They are Phase 2
  work:
  - `__put_unused_fd` lowering `next_fd` (`fs/file.c:566`);
  - the last-reference `eventfd_release` (`fs/eventfd.c:114`).

This table is interim. Phase 2 replaces the string labels with typed step
constructors that carry their own source anchors.

The mirror still collapses several C steps: open-fd bitmaps, refcounts, VFS
dispatch and user copy. The plan's section 2.2 lists them.

## Configured source capture

`scripts/in-bundle python3 scripts/capture-correspondence.py`:
- reads the accepted kernel build's `.cmd` records;
- preprocesses the eight modeled translation units serially with the exact GCC
  command;
- writes `.i` files, line maps, the include closure with hashes, and a
  comparison of every source input against the pinned archive.

`--verify PATH` rechecks a captured manifest. `capture-v1.json` records the
retained capture: 8 translation units and 801 archive members checked, with no
modifications. The capture is source provenance and a fixed C text for later
proof work. It is not evidence of agreement.

## Domain facts

The trace domain has these properties. `contracts/scope-v1.json` records the
same facts in machine-readable form.
- Fixture descriptors 0–7 are reserved.
- `RLIMIT_NOFILE` is 32, while the initial kernel table capacity is 64.
- Eventfds are nonblocking.
- The file status is `O_RDWR | O_NONBLOCK` (2050).
- Close-on-exec is descriptor-local.
- Descriptor references keep their number after close, so reuse changes the
  file they name.
