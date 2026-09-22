# Lean-ux objectives

Status: corrected at the user's direction on 2026-09-22. This document and the
[prototype execution plan](prototype-plan.md) supersede earlier proposals and
proof milestones. Current implementation status is in the [pause handoff](pause-handoff.md).
The campaign remains paused; removing proof work does not resume it.

## Purpose

Build a highly faithful executable Lean mirror of progressively larger parts of
Linux. Each modeled computational step must correspond to a step in the configured
Linux implementation. Test the executable model against actual kernel behavior.
The long-term ambition includes a large part, potentially all, of the kernel.
Each actual claim identifies the configuration, environment, and behaviors covered.

Do not construct proofs about the Lean model, proofs between handwritten Lean
encodings, or proof-audit infrastructure. An eventual simulation between actual
Linux code and the model motivates computational fidelity; building that proof
is outside this project phase. Existing model proof requirements are withdrawn.

The mirror has two inseparable responsibilities. Its observable behavior must
agree with the chosen Linux implementation. Its computations must also have an
explicit relationship to Linux's state changes and algorithmic flow. This
relationship must be visible in the executable helpers and intermediate states,
with source mappings and explicit gaps. Matching final outputs alone is insufficient.

The project also develops the means to construct this mirror with sustained agent
work: reproducible experiments, independent evaluation, targeted repairs, and
acceptance criteria that resist shortcuts. Human involvement should concentrate
on consequential changes of scope or assumptions and on assessing completed
results.

## The first objective

Produce a small but complete demonstration of this method using file descriptors
and eventfd objects. The result must combine an executable mirror, a Linux test
runner, a step-by-step record of computational correspondence, and an automatic
workflow for finding and repairing behavior discrepancies.

The prototype succeeds when the following capabilities work together:

1. A fixed experiment can run against the pinned Linux guest and Lean, with
   reproducible observations and an explicit supported input domain.
2. Every modeled helper has a source-grounded account of retained state,
   decisions, updates, calls, correspondence points, and abstractions.
3. Generated experiments expose an injected semantic fault, reduce it to a
   useful counterexample, and drive a principled repair without human semantic
   patching. Naturally discovered disagreements are retained separately.
4. Independent challenges reject an over-specialized repair and attempts to
   weaken the evaluator, supported domain, or source-correspondence requirement.
5. Every modeled step identifies the corresponding Linux computation, including
   intermediate state, branch predicates, update order, and relevant effects.
   Unmatched steps or unjustified abstractions remain explicit implementation gaps.
6. The evaluator independently reproduces acceptance from recorded inputs, and
   an interrupted run resumes from durable work records without losing failures
   or silently accepting incomplete work.

This establishes a prototype of a scalable model-construction method. Remaining
source-correspondence gaps, configuration limits, and omitted kernel behavior
must remain visible in its result.

## Initial scope

The baseline is Linux v6.12.110, commit
`fa5b06866b643cce7072a4e7c6be7ee3f0f1b95c`, with the repository's resolved x86-64
configuration and Lean 4.33.1. Source and tool identities come from the
[dependency locks](../dependencies/sources.lock.json); the tested development
environment is described in [offline usage](offline-usage.md).

| Dimension | Initial choice |
| --- | --- |
| Operations | `eventfd2`, `dup`, `dup3`, `close`, `read`, `write`, and `fcntl` with `F_GETFD`, `F_SETFD`, `F_GETFL` |
| Objects | Ordinary and semaphore eventfds; descriptor tables and shared file objects |
| Execution | One test thread, nonblocking eventfds, no injected signals or external producers |
| Inputs | Explicit x86-64 argument widths, little-endian I/O, valid allocated buffers, bounded traces and fixed descriptor limits |
| Kernel execution | QEMU TCG guest; one CPU, 256 MiB, no guest NIC, KVM, host disk, or shared host filesystem |
| Deferred behavior | Blocking calls, changing nonblocking mode, faulting user pointers, concurrent calls, modeled fork/exec, epoll, mmap, device/KVM internals |

The harness may use processes and other infrastructure outside the modeled trace;
those mechanisms belong to the experiment fixture and must be documented. The
initial fixture distinguishes its own descriptors from descriptors the trace may
operate on. Memory allocation pressure and unexpected external interference are
classified outcomes outside the initial deterministic comparison domain.

Descriptor numbers remain observable, including allocation and reuse. A reference
to a previous result retains its numeric value after close; reuse can therefore
change the object it names. Shared object identity must preserve aliasing. Logical
ownership may abstract raw kernel reference counts only with explicit treatment
of temporary and kernel-held references.

This scope is a methodology experiment. Firecracker confinement remains a later
application requiring its own complete authority and environment inventory.
Generalizing to other architectures or configurations is separate work.

## Computational correspondence

Future simulation work motivates the following relationship between a source
region from correspondence point A to B and the executable model. This is a design
requirement, not a request to construct a theorem in this prototype:

```text
For every admitted kernel state c and mirror state m:
  related_A(c, m) and KernelRegion_A_B(c, effects, c')
  imply that some corresponding mirror execution reaches m',
  produces matching relevant effects, and establishes related_B(c', m').
```

Control locations are part of this account. Each modeled computational step
needs a corresponding Linux step; merely matching syscall entry and return is
insufficient. Regions may contain multiple steps, which must remain accounted
for individually. Record any collapsed or omitted work as an abstraction requiring
review, rather than silently treating it as faithful correspondence.

Each modeled helper must identify the following information:

- State fields and relationships retained by the mirror, including ownership.
- Branch predicates, validation order, arithmetic widths and conversions.
- Updates and relevant effects, including effects preceding an error.
- Calls and loop boundaries, with helper contracts or invariants.
- Entry, exit, and necessary intermediate correspondence points.
- Omitted mechanisms and the assumptions or future obligations permitting them.

Every call leaving the modeled region has a recorded contract or an unresolved
obligation. Matching names and source locations is useful bookkeeping; evidence
about the corresponding computation is required as well.

For example, `eventfd_ctx_do_read` selects a value from the semaphore mode and
counter, assigns that output, then subtracts it from the counter. The executable
mirror must expose the corresponding computation and order of updates. Preserve
the configured source and record caller conditions, including the held lock,
distinct writable output slot, and absence of concurrent interference in this
slice. A separately handwritten Lean reference is not the Linux implementation
and is not a substitute for this source correspondence or kernel comparisons.

## The configured program

A source commit denotes many possible kernel builds. The correspondence target
must include the resolved configuration, architecture, compiler and flags,
generated headers, relevant source and patch hashes, and actual preprocessing
inputs. Preserve configured, preprocessed translation units alongside mappings
to the original source and macro definitions.

The build's own preprocessing commands provide the initial configured view.
Preprocessing, compilation, GNU C extensions, assembly, and their relationship
to executable behavior remain explicit trust or formalization obligations.
Compile-time selection does not eliminate runtime dispatch or environmental
variation.

The correspondence inventory distinguishes code absent from this build, code
excluded by a stated domain restriction, executed code abstracted by a contract,
and code whose behavior remains unknown. Unobserved behavior is never silently
classified as irrelevant. Future configurations acquire separate identities and
invalidate affected evidence until it has been re-established.

## Testability and evidence

Each operation has a testability record: how to reach it; required objects and
permissions; controlled environment; reset procedure; observations and later
state probes; comparison rules; expected failures; coverage limitations; and
unsupported cases. These records accumulate into an interface and dependency
inventory as the project grows.

Syzkaller supplies useful descriptions, generation, mutation, and minimization
machinery. The prototype begins with a small typed trace contract, then adds a
restricted adapter where it preserves that contract. Syzkaller support for an
input does not establish that our evaluator can judge all its effects.

Results retain distinct evidence categories:

| Category | Meaning |
| --- | --- |
| Behavioral evidence | Identified experiments agree under recorded conditions |
| Structural accounting | Identified source decisions, state changes, and dependencies have dispositions |

Behavioral agreement and structural accounting are separate requirements. Tests,
coverage, and source labels do not by themselves establish complete step fidelity.
Unknown behavior, infrastructure failures, and timeouts never count as agreement.
Freeze the trace domain, observation rules, source identities, and allowed model
changes. A repair cannot change those requirements to obtain a passing result.
Proofs about the Lean model are not an accepted evidence category.

## Automation and its trust boundary

Contributors propose artifacts. A separately controlled evaluator rebuilds and
checks them against fixed contracts and produces authoritative evidence. Its
own fault-injection tests must show that incorrect semantics, overfitting,
tampered comparisons, and stale source identities are rejected for the intended
reason.

The current collaboration agents share project access. Roles and local hashes
provide engineering discipline, not security against an agent using all that
access maliciously. The prototype must enforce a narrower OS boundary for
candidate builds and executables, and demonstrate that they cannot
modify accepted inputs or results. Strong isolation of an agent's entire tool
host is a separate capability, to be implemented and tested before claiming
resistance to fully hostile contributor agents.

Automatic checks and durable recovery records should be frequent; requests for
human attention should be rare. Routine implementation, testing, repair,
integration, and scheduling proceed within the fixed scope. A change that weakens
the claim, changes trusted assumptions, requires new external access, or exceeds
the agreed scope is surfaced explicitly. No fixed number of attempts guarantees
success: unresolved obligations remain unresolved when the evidence is absent.
