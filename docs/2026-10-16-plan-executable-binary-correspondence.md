# Plan: executable reconstruction and paired binary/mirror execution

Status: implementation started, 2026-10-16. Worktree
`.worktrees/binary-pair-runner`, branch `task/binary-pair-runner`, created from
planning commit `caa6668`. The earlier experiments remain on their original
branch; the implementation baseline is `cb845fe`.

[USER 2026-10-16] Develop binary/mirror correspondence through executable
reconstruction and assertions, exercising them on workloads before attempting
universal proof. The mirror fixes the target abstraction; loop invariants
belong in the executable paired program too. This note records the build sequence.

[USER 2026-10-16] Begin this experiment in a separate worktree, preserving the
existing M1/M2 and sequential sibling as comparison baselines.

[AGENT 2026-10-16] Establish the mechanism on index lookup, then test its value
on the unfinished allowed-IPs loop. Build small examples before generalizing
the runner or adding proof automation. The stages below are the proposed
implementation order, not completed work or new standing gates.

## Objective and hypothesis

Build a Lean program that executes the compiled kernel under Kraken beside
the existing executable mirror. At chosen correspondence points it
reconstructs the mirror's target state from the binary configuration and
checks equality, together with executable loop and memory assertions.

The intended workflow is:

1. Develop the operational mirror against kernel behavior using testing.
2. Develop reconstruction and invariants against paired executions using
   testing and concrete counterexamples.
3. Prove establishment and preservation of those same definitions by
   symbolic execution and composition.

This is counterexample-guided development, initially with a human or agent
revising candidates. Captured workloads and generated cases provide an
incomplete counterexample search; they are not universal verification. A
stuck proof is not itself a concrete counterexample.

The hypothesis to measure is that a tested reconstruction and annotated
paired program leave little further invariant invention for the proof.
Runtime throughput and proof-line counts alone do not answer that question.

## Starting point

The [previous experiment](2026-10-16-goal-binary-proof-refactoring.md#sibling-sequential-experiment-result)
produced `Binary.Sequential.lookup_simulation`: a complete sequential sibling
of M1, with endpoint correspondence and the original entry domain. Removing
selected-path decision/cut alignment simplified composition, but substantial
physical proof machinery remained. Its short adaptation time does not
measure new-function proof cost.

Useful existing components are:

| Component | Reuse and limit |
| --- | --- |
| `binary/Main.lean`, `binary/run.py` | Recorded workload-prefix replay, concrete Kraken execution, actual decoded service bodies in the appropriate mode, mapped-access checks, and endpoint comparisons. These are specialized probes, not a persistent paired runner. |
| `binary/Layouts.lean`, `binary/layouts.py` | DWARF-derived record offsets. Pointer graphs and allocation interpretation still need explicit definitions. |
| `binary/MirrorLoop.lean` | An executable index-loop presentation and equalities connecting it to the actual mirror, including `indexLookup_eq` and `loop_run`. |
| `binary/AllowedipsSource.lean`, `binary/AllowedipsLoopComposition.lean` | Source-loop presentation and a composition lemma. Audit their exact connection to the executable mirror before adapting them. |
| `binary/SequentialRelation.lean` | A useful endpoint specification example. Its `At` is a logical predicate, not yet an executable reconstruction function. |
| M1 witnesses and M2 components | Known inputs, physical lemmas and regression comparisons. M2 function composition remains unfinished at this baseline. |

Current probes construct Kraken entry memory from the mirror state after a
recorded workload prefix. They do **not** restore a captured kernel entry
snapshot. Preserve that distinction in every test result. Existing kernel
coverage comparisons are useful independent evidence, but do not validate
all initial bytes.

The first experiment remains deliberately sequential: no concurrent Linux
contextual-refinement claim. Keep M1, its trust surface, the sequential
sibling and incomplete M2 available unchanged for comparison. No mirror edit
to make correspondence pass, no automatic merge from main, and no change to
the oracle or Kraken as part of this planning task.

## What the paired program contains

The mutable execution state contains the Kraken machine, mirror World,
mirror local/control state, persistent pointer interpretation, environment
record cursors and current correspondence-point occurrence. A point
occurrence distinguishes repeated loop visits and nested calls; a PC alone
does not identify it.

The following is an interface sketch, not a proposed final Lean API:

```text
reconstruct : Point -> Interpretation -> BinaryConfiguration
              -> Except DecodeError TargetState

assertAt    : Point -> PairedState -> Except AssertionError Unit

advanceBinary : Segment -> BinaryConfiguration -> ExecutionOutcome
advanceMirror : Segment -> MirrorConfiguration -> ExecutionOutcome
```

`TargetState` is determined by the existing mirror, not chosen to discard a
disagreement. Reconstruction may vary by proof point because values move
between memory and registers. The interpreter and reconstruction never read
the expected mirror result to decide what the binary means.

Write `alpha` for reconstruction. At a correspondence point the logical
obligation is `alpha point interpretation binary = .ok (target mirror)`,
together with successful execution of the additional assertions. `target`
extracts the already specified mirror state and locals; it is not an
adjustable abstraction chosen by the candidate. There is no second,
independently written specification for the checker to approximate. The
eventual proof establishes these same definitions directly; this is not a
certificate-checker project or a soundness theorem about a certificate
checker. Component lemmas may make the executable definitions easier to
reason about.

The current World also contains supplied environment and diagnostic history.
Stage 0 must distinguish those from reconstructed physical state using the
mirror's existing structure/state split. Supplied records remain explicit
inputs with checked consumption; diagnostic decision traces remain a
separate validation channel. Do not invent byte representations for them or
silently default them. A decoder for one function's state is an incremental
component, not a claim that the whole target World has been reconstructed.
Unchanged components are carried through explicit frame arguments, not
extra clauses relating unrelated kernel subsystems.

Pointers require one coherent interpretation across segments and repeated
calls. Record the roots and object identities used to establish it. Embedded
owners and legitimate aliases must remain representable. Future allocation
and release need explicit interpretation-update rules; arbitrary remapping
at a checkpoint is forbidden. If reconstruction needs a retained binary
snapshot or ghost value, name it and prove/update its provenance from actual
execution rather than copying the expected mirror value.

Both programs choose their own branch and next point. A source branch may
not choose a Kraken successor or make the runner ignore an unexpected exit.
Point selection is a proof convenience; neither step counts nor every
instrumented decision need align. The programs may stutter relative to one
another. External values come from the declared environment and recorded
inputs, with separate record-consumption checks for each side.

## Build sequence

Each row ends with a runnable or reviewable deliverable. Use the completion
conditions to assess progress, without adding a new gate for each row.

| Stage | Build | Completion condition |
| --- | --- | --- |
| 0. Fix the pilot interface | Identify the M1 target state, binary roots, mirror locals, environment inputs and proposed points; choose a source-segmentation mechanism. Scope the actual kernel-entry capture separately. | A concrete entry/exit example and one collision iteration can be described without reading expected source values during reconstruction or modifying the mirror. |
| 1. One complete paired call | Factor the existing concrete executor for reuse; add executable reconstruction and structured comparisons for index lookup at entry/return. | Known miss, live, NULL and dead cases run; deliberate relevant state corruption produces an explicit mismatch. |
| 2. Persistent segments and loop | Add source/binary advance-to-point operations, loop assertions and write-footprint checks; preserve both resulting states between segments and calls. | A collision loop is checked at successive headers, and the dead-peer two-lookup regression checks the owner clear and its consequence on the second call. |
| 3. Workload-driven iteration | Feed existing recorded workloads and labeled synthetic variations through the same paired program; add focused failure/replay tools. | Failures identify the first broken clause and have small replay recipes; corpus progress is reported by paths/assertions exercised, not just pass counts. |
| 4. Actual entry-state capture | Implement the scoped capture/loader path with binary identity, registers, reachable memory and relevant environment state. | At least one invocation begins from actual captured kernel state, reconstructs the expected mirror entry and executes to the recorded return. Missing state fails explicitly. |
| 5. Unfinished M2 join | Apply the established machinery to allowed-IPs lookup and its trie loop, including `common_bits` in both address families. | The paired loop executes with runtime reconstruction, cursor/remaining-work assertions and persistent state; no function-level proof is claimed yet. |
| 6. Prove and measure | Prove the tested M2 loop join and compose it with appropriate existing physical regions, using the same reconstruction/assertions. | Report how many invariants changed after proof began, why they changed, and whether the previously open join closes. Distinguish a closed join from a complete function theorem. |

### Stage 0: resolve the open interfaces

Start at the existing compiled image and mirror pins. Decide which values
are needed at entry, bucket-loop header, helper return, owner-store exit and
function return. Avoid reproducing all M1 cuts.

The most important implementation choice is how to pause the mirror. Prefer
existing functions and the proved operational loop presentations. If those
do not expose a needed boundary, write an executable presentation in the
binary/proof package with a small equality theorem connecting it to the
original mirror, including failures and effects. This is a source adapter,
not a second handwritten mirror whose agreement is merely assumed. Do not
begin by building a general resumable Lean interpreter.

Scope capture here so that stage 4 has an implementable design: invocation
selection, a coherent stopped/serialized entry, ABI registers, memory roots,
reachable objects, per-CPU/service state and the recorded return. Determine
whether existing capture facilities suffice. Any needed instrumentation
must follow the project's oracle-change process and have a separate capture
identity where appropriate; do not silently alter the read-only oracle.
If the capture mechanism is blocked, stages 1–3 still test constructed
states, but the captured-entry part of the experiment remains incomplete.

### Stage 1: extraction first, small executor second

Implement pure, total Lean decoding functions with explicit errors for
missing bytes, unresolved pointers, malformed structures and traversal
exhaustion/cycles. Decode actual fields, not zero-filled placeholders. A
finite traversal budget is a runtime safeguard; exhausting it is a failure,
and its adequacy/termination must eventually be justified in the proof.

Use the existing construction of initial memory only as a labeled fixture.
Establish entry correspondence, run the actual mirror and Kraken function,
then decode and compare the successors. Keep actual decoded callbacks where
the current probe supports them. Report unsupported instructions, addresses
and calls explicitly; do not replace their effects with the expected mirror
effect.

Keep interpretation, traversal and equality separate enough for useful
diagnostics. Prefer named checks over one opaque boolean. A successful
reconstruction followed by a field mismatch should show the object identity,
binary address, decoded value and source value. A decode failure should show
the attempted read and the path used to reach it.

### Stage 2: make the paired program executable at intermediate points

Add only the combinators needed by the pilot: run a segment to a declared
exit, check a point, branch on actual exits, and repeat through a loop header.
A segment descriptor names the binary entry/exits, mirror action/continuation
and attached assertions. Record a call/return context and occurrence counter
so a loop-header check cannot pass by immediately stopping at its starting
PC. Preserve enough local trace for diagnosis, without retaining giant
histories as permanent artifacts.

The loop assertion includes reconstruction equality, the cursor's relation
to remaining entries, saved locals, required mapped storage and any
separation facts the next iteration needs. A termination measure can be
computed and its decrease checked on observed iterations. Runtime budgets
are not evidence of universal termination.

Maintain binary memory, mirror state and interpretation across the whole
sequence. Reinitializing the call ABI for a second invocation is an explicit
caller action; it must not reconstruct the data heap from the mirror again.
The dead-peer regression must observe the first call's cleared owner word
on the second call. No precondition may exclude the known dead-peer state
merely to avoid the finding.

Kraken's concrete effect handler already catches unmapped read/write ranges.
Add footprint/allocation checks where supplied metadata permits: an access
can be mapped yet cross an object boundary or touch a released object.
Mapping tests are not an execution-wide permissions or lifetime proof.
Both overly permissive and overly restrictive alias assertions are bugs in
the candidate specification and should be testable.

As an early feasibility check, prove one small segment implication using
the executable reconstruction and assertion. This checks that the chosen
API is suitable for symbolic reasoning before adding many decoders. It is
not a requirement to finish M1 again before exploring M2.

### Stages 3–4: distinguish workloads, mutations and captured states

Begin with the existing index cases
`d1_wrong_receiver_index_same_bucket` and `d1_second_response`. Keep the
current three-way kernel coverage/result/decision comparison as a test;
do not make its decision alignment the new relation's definition.

Vary collision length, early/wrong-kind matches, embedded owner choices,
NULL/dead/live counts and permitted aliases. First vary supported workload
inputs so the campaign can generate corresponding recordings. Constructed
state mutations are also useful, but label them as such and check the
declared domain independently. Use successful cases that exercise aliases
as well as corruptions intended to fail. Selected undefined-value seeds
remain testing of those choices, not universal quantification.

A replay recipe names the image/mirror/Kraken pins, workload and invocation,
input records, interpretation setup, explicit mutations and undefined-value
choices. A mismatch report includes the point occurrence, both independently
reached exits, first failed clause and relevant reads/writes. Reduce cases
manually first; automate reduction only if repeated failures justify it.

For actual captured entries, read kernel registers and memory without
repairing them using the mirror. Resolve real addresses through the explicit
interpretation. Any relocation must preserve pointer edges/aliasing and be
documented, not performed by filling in missing values from expectations.
Keep the snapshot coherent at the chosen sequential boundary, and identify
missing memory or later external input rather than silently supplying it.
Retain only regeneration commands and small regression inputs in Git;
snapshots and execution dumps are ephemeral.

### Stages 5–6: the experiment that measures usefulness

Use `b1_trie_routing` and its IPv4/IPv6 cases as the initial allowed-IPs
workloads, adding labeled structural variations for traversal depth,
prefix mismatch, absent children, remembered peer and dead-peer behavior.
Begin with the existing `common_bits` implementation/proofs; do not duplicate
the target to avoid its representation difficulties. Define executable trie
reconstruction and the invariant at a useful loop header, then debug the
paired iterations through their actual exits.

Freeze a tested candidate version before attempting the unfinished loop
proof. Establish the entry assertion, prove each segment preserves the next
assertion, discharge the loop/termination obligations and derive the exit
effect. Use Kraken's actual symbolic semantics with all permitted undefined
outcomes. Concrete execution does not replace a universal implication.
Retain named service assumptions until their image proofs are supplied.

Record any new condition discovered during proof. If it has a concrete
counterexample, add the reproducer and rerun the paired program. If it is a
logical or solver difficulty without a counterexample, record that separately.
Apply Rule Zero to discrepancies: investigate the mirror and reconstruction
before claiming a kernel defect; never weaken the target to suppress one.

## Tooling boundaries and measurements

Start in the standalone `binary/` package, keeping executable definitions
available to proof modules and IO/reporting at the outside. Suggested module
responsibilities are decoding, execution-to-point, paired control/assertions,
index pilot, allowed-IPs pilot and workload IO. Names and file boundaries are
implementation choices, not a requirement for a generic framework.

Factor a lemma when a recurring property needs proving; add a tactic when a
predictable search or normalization procedure earns its cost on examples.
Do not build an invariant synthesizer, SMT integration, global assertion
registry or certificate format before the paired examples demonstrate need.

Measure separately: reconstruction/assertion development time, time spent
debugging runtime counterexamples, proof time after the candidate is fixed,
build/run waiting, and new conditions invented during proof. Distinguish
reused physical/source proofs from new work. Report the cost of applying the
library to M2, not just the ease of replaying already-solved M1.

Reassess after stage 2 if pausing the real mirror requires a second large
semantics, reconstruction depends on expected values, or supporting the
runner costs more than the tested joins. After stage 6, stop and report one
completed proof/join or the concrete blocker. Do not expand to the rest of
WireGuard merely because the runner exists.

All heavy work uses `capped`; builds use normal parallelism and workload
runs use `LEANUX_QEMU_SLOTS=16`. KILLED banners and timeouts fail. Use scoped
tests during development, known-mismatch controls for the new checks, and
the existing binary trust gate at proof claim points. New theorem claims
need axiom reports and kernel replay; the external gate remains
`lake check --from-export` outside Nono as described in
[binary/README.md](../binary/README.md). This plan adds no new gate or
acceptance claim. No merge to main, push, shared-cache edit or other-worktree
mutation is authorized by it.

## First runnable slice

Implemented on `task/binary-pair-runner`, 2026-10-16. Stages 0–2 have an
index pilot, and stage 3 has the two specified recorded-prefix workloads
plus a focused mutation set. Stages 4–6 remain open; this is not a report
that the overall hypothesis has been established.

[AGENT 2026-10-16] Use the existing `LookupMirror.body`/`finish` presentation
and its `indexLookup_eq` theorem to pause the source. Stop the binary at the
bucket header, the helper-entry or miss-tail exit, and the original return.
This avoids a second source interpreter and preserves independent branch
selection. Source steps and binary instruction counts do not align.

The executable component is `PairMemory.reconstruct`. Its target is fixed
by `PairMemory.target`: all table membership and order within each of 8192
buckets, every interpreted embedded owner word, and every peer reference
count. Cross-bucket list order is not physically represented. The decoder
never receives the mirror state; identities and addresses are established
once before running. It checks backlinks, cycles, bucket hashes, owner kinds,
mapped reads, containing-object bounds and separation. Different entries
may legitimately point to the same peer. Unrelated World state, supplied
environment and diagnostic logs are outside this component. A complete
World reconstruction and its frame composition are not claimed.

`PairIndex.lookup` retains both heaps and the pointer interpretation across
iterations and calls. It resets call ABI registers as an explicit caller
action; it never materializes a successor heap from the source. Header
assertions check reconstructed data, remaining chain, cursor, query, kind
mask, output pointer, stack depth and BH-disabled count. Loop measure checks
observe a decreasing remaining list. Return assertions check result/output,
saved registers, stack, restored preempt count, pending-softirq word, KCOV
count/content and the binary's actual read/write requests against permitted
ranges. Permission requests are recorded by the factored `ProbeSupport`
executor; callbacks execute their decoded bodies. The access checks are
runtime assertions, not universal memory-safety or lifetime proofs.

The runner's declared fixture is sequential, starts with preempt count zero,
has no pending softirq and uses a bounded KCOV_TRACE_PC buffer. It does not
execute environment interference at BH-enable. World and records come from
the real prefix replayer; the additional states are explicitly synthetic.
The mirror itself, the oracle and Kraken semantics were not changed. All
existing M1/partial-M2 statements and `TrustBase.lean` remain unchanged.

The first suite covers an empty bucket, a nonempty miss, live/NULL/dead hits,
two successive live or dead lookups, collisions of lengths 1, 3 and 8 before
the sought entry, wrong-kind stops, and keypair-owner dead hits. Collision
entries deliberately share a peer. Each positive case runs two undefined
seeds. Fifteen controls reject changed counts/owner words, unresolved
pointers, cycles, bad backlinks/kinds, missing memory/interpretation,
overlapping allocations, a missing instruction label, mapped accesses
outside the footprint, and wrong loop cursor/query/remaining work. The
mapped cross-entry read control first confirms that its bytes are mapped.

The dead-peer two-call regression passes for both owner kinds. For the
handshake case, the first call executes 441 instructions and the second 271:
the second actually reads the retained NULL owner word. No dead-peer state
was excluded to obtain this result.

### Proof interface and limits

`PairNextProof.word_loadInt` connects the executable word reader to Kraken's
load. `PairNextProof.next_segment` composes M1's existing three-instruction
back-edge proof with reconstruction equality and the updated cursor/exit.
It uses the same `reconstruct` definition as the runner. Its premises are
explicit arguments, not added axioms or an oracle fact: the initial
`Corresponds` equality and the executable next-pointer read.

Both declarations use only `propext`, `Classical.choice` and `Quot.sound`.
Fresh local kernel replay of `PairNextProof` passes. The existing binary gate
passes with a clean private Kraken at
`7ebba06a30eaf08c10b26b28ca14bfee1c791576` and an unchanged trust-surface diff.
No new external-export acceptance is claimed. Baseline imports still emit
their existing module/deprecation/unused-simp warnings; the new modules emit
no warnings and add no suppression. Those inherited warnings are not fixed
by this experiment.

This proof uses `Effects.All`, which erases access requests. It does not
prove the runtime footprint checks, the full loop, the full call, callback
contracts, kernel-entry reachability or concurrent contextual refinement.
It reuses an already-proved physical region, so its brevity is not evidence
of reduced new-function proof cost. No invariant changed while proving this
small lemma; the word-reader implementation was rewritten using Kraken's
existing byte conversion to simplify the connection. The decisive test of
new invariant invention remains the unfinished M2 join.

### Measurements and next boundary

The worktree was created at 23:46 UTC. Authoring, local elaboration debugging,
builds and scoped validation overlapped; no reliable per-activity timing was
collected for this slice. Fresh workload generation took about two minutes
per workload, largely outside paired execution. Reused builds and M1 lemmas
make this unsuitable for a campaign throughput estimate.

At the measured runtime checkpoint, each workload supplied 15 cases, 48
completed calls over two seeds and 94 checked loop headers. The live-query
workload executed 22,404 instructions in its positive calls; the wrong-index
workload executed 21,774. Paired suite execution took about 4.3 seconds per
workload; capture/build/three-way checks are excluded. Failure controls are
reported separately, not counted as successful calls. Both fresh kernel
checks and both independent coverage/result/decision comparisons passed.

The next boundary is actual entry capture, then application to the allowed-IPs
loop. Current `harness/guest.c` and `harness/linux.py` provide filtered KCOV
PC/comparison streams, not register/heap snapshots. A capture must select one
invocation in the recorded operation, stop the single CPU coherently at
function entry, read all ABI state and the real stack/return, traverse table
roots into embedded owners and referenced peers, and include per-CPU/task
and coverage-buffer storage read by the service bodies. It must record the
same invocation's return and identify the image and source records. Actual
addresses must enter a persistent interpretation; missing bytes must fail.
A separate loader and generalized call/service addresses are needed before
the synthetic fixture can be replaced. No capture implementation or new
oracle instrumentation has been added at this checkpoint.
