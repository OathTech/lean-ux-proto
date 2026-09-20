# Lean-ux objectives

Status: current project direction, consolidated on 2026-09-20. This document and
the [prototype execution plan](prototype-plan.md) supersede the implementation
sequence in the earlier [proposal](2026-09-20-prototype-proposal.md). The earlier
documents remain useful design history. Only environment preparation has been
completed; the mirror and its acceptance infrastructure are planned work.

## Purpose

Build an executable Lean mirror of progressively larger parts of Linux, arranged
so that its correspondence to the kernel can eventually be proved. The long-term
ambition includes a large part, potentially all, of the kernel. Each actual claim
will identify the kernel configuration, environment, and behaviors it covers.

The mirror has two inseparable responsibilities. Its observable behavior must
agree with the chosen Linux implementation. Its computations must also have an
explicit relationship to Linux's state changes and algorithmic flow. This
relationship should decompose into local simulation proofs and support reasoning
about their composition.

The project also develops the means to construct this mirror with sustained agent
work: reproducible experiments, independent evaluation, targeted repairs, and
acceptance criteria that resist shortcuts. Human involvement should concentrate
on consequential changes of scope or assumptions and on assessing completed
results.

## The first objective

Produce a small but complete demonstration of this method using file descriptors
and eventfd objects. The result must combine an executable mirror, a Linux test
runner, a record of computational correspondence, an automatic repair workflow,
and a meaningful local stepping theorem.

The prototype succeeds when the following capabilities work together:

1. A fixed experiment can run against the pinned Linux guest and Lean, with
   reproducible observations and an explicit supported input domain.
2. Every modeled helper has a source-grounded account of retained state,
   decisions, updates, calls, correspondence points, and abstractions.
3. Generated experiments expose an injected semantic fault, reduce it to a
   useful counterexample, and drive a principled repair without human semantic
   patching. Naturally discovered disagreements are retained separately.
4. Independent challenges reject an over-specialized repair and attempts to
   weaken the evaluator, supported domain, or proof obligation.
5. Lean checks a local simulation theorem between two explicitly distinct
   representations, over arbitrary related states, with matching effects and a
   relation at the next correspondence point. A second theorem establishes a
   useful descriptor ownership invariant.
6. The evaluator independently reproduces acceptance from recorded inputs, and
   an interrupted run resumes from durable work records without losing failures
   or silently accepting incomplete work.

This establishes a prototype of a scalable construction method. The source-side
semantics, configuration generalization, and composition work still required for
an actual Linux simulation theorem must remain visible in its result.

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

For a source region from correspondence point A to B, the intended obligation is:

```text
For every admitted kernel state c and mirror state m:
  related_A(c, m) and KernelRegion_A_B(c, effects, c')
  imply that some corresponding mirror execution reaches m',
  produces matching relevant effects, and establishes related_B(c', m').
```

Control locations are part of this account. Regions may contain multiple steps,
and internal steps may leave the represented state unchanged. Collapsing steps
requires a justification; forward simulation alone does not establish reverse
inclusion of behaviors, termination, timing, or confidentiality properties.

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

The first stepping theorem will target the small computation in
[`eventfd_ctx_do_read`](../.deps/linux/fs/eventfd.c): select a value according to
semaphore mode and the counter, write that output, and subtract it from the
counter. A frozen, independently maintained Lean encoding of the source-shaped
steps will be related to the mirror implementation. The theorem covers the
symbolic zero/nonzero and semaphore/ordinary cases with fixed-width arithmetic,
explicit memory/ownership assumptions, and the lock-held obligation.

This theorem relates two Lean encodings. The source-to-reference encoding is
initially a reviewed, recorded assumption; it is not a formal semantics of the
actual kernel C. Defining the reference by invoking the candidate mirror would
not satisfy the objective. A descriptor alias-preservation theorem complements
the stepping theorem but does not replace it.

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
| Model theorem | A property follows for the Lean model under stated assumptions |
| Encoded-fragment simulation | A stepping theorem relates distinct Lean encodings; the source translation obligation remains |
| Kernel-source simulation | A theorem connects the mirror to an explicitly justified semantics of configured kernel source; deferred in this prototype |

Tests, coverage, and structural reports cannot be promoted automatically to proof.
Unknown behavior, infrastructure failures, and timeouts never count as agreement.
Accepted proof statements, assumptions, and their transitive dependencies are
audited; an empty domain or an added axiom cannot substitute for the obligation.
The frozen proof contract includes the definitions of the admitted domain, state
relations, effect comparison, reference transitions, and permitted abstractions.
Keeping a theorem's name and printed type while weakening those definitions is
a contract change, not a successful proof repair.

## Automation and its trust boundary

Contributors propose artifacts. A separately controlled evaluator rebuilds and
checks them against fixed contracts and produces authoritative evidence. Its
own fault-injection tests must show that incorrect semantics, overfitting,
tampered comparisons, stale source identities, and invalid proof assumptions are
rejected for the intended reason.

The current collaboration agents share project access. Roles and local hashes
provide engineering discipline, not security against an agent using all that
access maliciously. The prototype must enforce a narrower OS boundary for
candidate builds, tactics, and executables, and demonstrate that they cannot
modify accepted inputs or results. Strong isolation of an agent's entire tool
host is a separate capability, to be implemented and tested before claiming
resistance to fully hostile contributor agents.

Automatic checks and durable recovery records should be frequent; requests for
human attention should be rare. Routine implementation, testing, repair,
integration, and scheduling proceed within the fixed scope. A change that weakens
the claim, changes trusted assumptions, requires new external access, or exceeds
the agreed scope is surfaced explicitly. No fixed number of attempts guarantees
success: unresolved obligations remain unresolved when the evidence is absent.
