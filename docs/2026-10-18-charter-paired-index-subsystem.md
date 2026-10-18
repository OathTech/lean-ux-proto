# Charter: a composable binary index-table subsystem

Status: charter recorded; implementation paused pending the user's instruction
to resume. Worktree `.worktrees/binary-pair-runner`, branch
`task/binary-pair-runner`, implementation baseline `b630836f`.

[USER 2026-10-18] Adopt a larger checkpoint that tests fresh-function proof
cost and composition: index lookup, removal and handshake-to-keypair
replacement over one retained heap and executable reconstruction. Record the
charter now and pause before beginning implementation.

This increment follows the
[complete-call and cost calibration](2026-10-18-plan-paired-call-increment.md)
and the [executable correspondence plan](2026-10-16-plan-executable-binary-correspondence.md).
It is a sequential sibling experiment. It preserves the original M1 result,
its dead-peer scope, and the wider binary adequacy campaign's obligations.

## 1. Question and starting evidence

The question is whether developing reconstruction and invariants by execution,
then proving those same definitions, makes new binary proofs affordable.
The checkpoint must exercise structural mutation, demonstrate reuse on a
second new function, and compose calls through their actual postconditions.

| Capability | Baseline and remaining uncertainty |
| --- | --- |
| Complete call from a tested entry assertion | `PairCallAdequacy.lookup_checked` establishes sequential allowed-IPs lookup for both families, reusing earlier physical regions and named callback contracts. This is not a fresh-function cost measurement. |
| Executable index reconstruction | `PairMemory` and `PairIndex` reconstruct bucket order, owner peer words and peer counts; the runner retains memory and identities across lookups. A complete bridge from this reconstruction to the existing lookup theorem remains open. |
| New mutation tested | `PairRemove` runs the complete removal body and actual services. The calibration passes 54 calls, including collision chains and repeated removal. The recorded-prefix comparison selects calls; it does not execute their intervening callers. |
| Missing invariant discovered by execution | An unhashed owner with stale non-NULL `pprev` passes lookup-only reconstruction but can unlink another entry. The added ownership decoder checks hashed flags against source membership and rejects this state. |
| Fresh mutation proved | Three instructions in two removal regions and the tested ownership-flag update are proved. Bucket reconstruction through unlink, the successor repair and full removal adequacy remain open. |
| Runtime cost | Unchanged IPv4 captured replay took 256.55 seconds. A generated smaller-KCOV variation took 0.35 seconds, with different comparison work. This diagnoses a major cost; unchanged-capture acceleration has not been delivered. |

The implementation baseline uses mirror `cb2348e`, lagging main `77c9b55`
at the previous checkpoint, and clean Kraken
`7ebba06a30eaf08c10b26b28ca14bfee1c791576` on Lean v4.35.0. The oracle is
the pinned, read-only `.artifacts/kernel-net-choice-s4/vmlinux`. Record pins
and lag again on resumption and at the result; do not silently update them.

The previous increment passed fresh local kernel replay. Its export at
`d2dac16b` contains `PairCallAdequacy`, `PairCallWitness` and
`PairRemoveOwnership`; external acceptance is pending. The earlier external
acceptance at `a33869e` covers its earlier boundary modules only.

## 2. Target theorem and observations

For any finite sequence of admissible index lookup, removal and
handshake-to-keypair replacement calls, establish the following:

Starting from one checked initial paired state and one allocation
interpretation, accepted execution of the actual mirror sequence has a
corresponding sequence of terminating binary calls under Kraken. Each call
returns the matching interface result and reestablishes the same executable
reconstruction. The proof carries the physical frame and callback readiness
through the sequence, deriving the next call's memory obligations from the
previous postcondition and explicit caller setup.

The three anchors and source functions are:

| Binary anchor | Actual mirror |
| --- | --- |
| `wg_index_hashtable_lookup` | `WG.indexLookup` |
| `wg_index_hashtable_remove` | `WG.indexRemove` |
| `wg_index_hashtable_replace` | `WG.indexReplaceHandshake` |

The observation is the interface result and the index-table projection
needed by these calls: membership and order within buckets, embedded owners
and their peer words, peer counts, and owner linkage validity. Reconstruct
from machine memory without consulting the expected source result. The
source projection is computed independently from the actual mirror state.
The logical relation is equality with the successful executable
reconstruction, using the same definitions exercised by the runner.

Every relation clause must be justified by an anchored read/write or the
observations of this increment. Unrelated World fields are outside the
relation and handled by frame theorems. Supplied environment and diagnostic
histories are not reconstructed physical state. Coverage, preempt state,
pending-softirq state and ABI storage are carried as explicit physical
readiness/frame conditions, not hidden in source observations.

Correspondence points are proof choices. In particular, a pointer splice may
temporarily violate the endpoint relation. Prove the segment's combined
effect and reestablish reconstruction at its endpoint; do not force a full
relation after every internal store. Decision alignment remains an
independent differential-test channel, not a simulation observation.

Admissibility must state actual caller obligations, source acceptance and
required memory conditions. For example, any requirement on the replacement
entry's prior linkage must be justified from the C's calling convention and
call sites, with its conditional scope made explicit. It must not be a
placeholder for the desired conclusion. Never assume that every future
binary entry already satisfies its precondition, or that a successful future
run exists. Source-only obligations and initial resource bounds may be
explicit; their consequences for later binary states must be proved.

The sequence uses an explicit caller transition to install the next ABI
arguments and return slot while preserving the shared data heap. Prove its
frame obligations. Do not rematerialize memory from the mirror or select a
fresh unrelated address interpretation between calls.

## 3. Scope and limits

Execution is sequential. The environment does not interleave interrupts,
workers or other mutators during a call. Captures must identify this execution
mode. The result does not claim concurrent contextual refinement, ordinary
kernel scheduling, or execution of compiled caller instructions between the
selected calls.

Use a fixed universe of allocated peers and embedded entries for each
sequence. Replacement transfers table membership between existing entries;
removal changes membership without proving allocation retirement. Allocation,
freeing, RCU lifetime transitions and reinsertion by the random-index allocator
are later work. This boundary must not remove the index lookup's NULL or
dead-peer paths, or suppress the original two-lookup defect witness.

Retain named decoder, service and environment hypotheses. Existing callback
contracts may be reused and must remain visible; execution of their bodies
in tests is not a proof of those contracts. This increment does not discharge
the wider campaign's callback-image proofs or transport landed whole-operation
properties. A new ordinary helper cannot be assumed correct under the name
of a service contract.

Keep the existing mirror operational code unchanged. A discrepancy is a
finding to investigate under Rule Zero, not permission to edit the mirror
to make a theorem close. No merge, push, oracle modification, global change,
or work in another worktree is authorized by this charter. Any necessary
change to the pinned semantics must be surfaced with its scope and tests;
it is not part of the baseline estimate.

## 4. Completion criteria

### A. Complete removal adequacy

Prove execution of the entire anchored function, including the entry and
return envelope, under the executable entry assertion. Cover unhashed
entries, sole entries, and head, middle and tail deletion in collision
chains. Prove the predecessor update, optional successor backlink repair,
owner unhashing and preservation of all remaining decoded data.

The result must export matching source reconstruction, restored ABI and
callback state, and a physical write frame. Its entry assertion must have
concrete checked witnesses executed to return. The existing ownership
update and fragment-fetch theorems are starting components, not this result.

### B. Complete replacement adequacy and measure reuse

Prove unsuccessful replacement and successful replacement at every list
position, including both successor cases. Prove index copying, neighbour
rewiring, the old owner's final unlinked state, and preservation of each
owner's own peer word. The current image has 41 replacement instructions
and 25 removal instructions, excluding service bodies.

Use the structural-update mechanisms developed for removal where they fit.
Record which lemmas are reused, which need generalization, and which parts
remain bespoke. Completing a second handwritten proof without useful reuse
is a meaningful cost result and must be reported as such.

### C. Lookup through the same executable relation

Connect the existing lookup proof to the common reconstruction and executable
entry checks. Prove preservation of the ownership linkage component added
for mutation. Cover live and dead peers, NULL owner words, wrong-kind and
index misses, and arbitrary represented collision chains. Preserve the
dead-then-NULL repeated-lookup behavior of the fixed mirror.

Derive the old physical premises from checked data and named hypotheses;
do not accept the old physical relation as a second independent assumption.
The postcondition must supply the common relation needed by the next call.

### D. Compose calls over one heap

Prove finite-sequence composition for the three operations under the stated
admissibility conditions. The result includes ordered interface results,
endpoint reconstruction and the reusable physical frame/readiness state.

Execute a nontrivial witness such as lookup, successful replacement, lookup
under the old and new kinds, removal, and subsequent lookup. Also test
unsuccessful replacement and repeated removal, with surviving colliding
entries. Retain one heap and identity interpretation throughout. The
general theorem must not be specialized to that example or a fixed call
count. If execution budgets are used in the runner, distinguish them from
the proof's termination argument.

### E. Capture, validate and report cost

Capture and replay actual kernel entry/return states for both new mutators.
Use the established three-way comparison before paired function tests, and
exercise the branch cases with labelled generated states where the capture
corpus does not supply them. Include focused negative controls for newly
discovered assertion classes.

Keep three evidence categories distinct: actual captured calls, states
materialized from recorded mirror prefixes, and synthetic sequences. A
sequence assembled from selected calls is not a captured uninterrupted
kernel execution. Source-derived arguments are not captured arguments.

Provide witnesses, complete theorem statements and named premises, proof
and execution validation, and the cost assessment described below. An open
bucket proof or unfinished sequence theorem means this goal is incomplete,
even if many physical regions and tests pass.

## 5. Work order and runtime experiment

On resumption, inspect the clean baseline and pins, then inventory the common
entry/exit interface. Begin with the removal bucket-splice reconstruction
lemma and complete removal. Develop replacement by execution and prove it
using those mechanisms. Connect lookup to the common relation and finish
the sequence theorem. Capture work and independent checks may overlap
proof work when they do not depend on unfinished changes.

Prefer lemmas for recurring mathematical properties and endpoint effects.
Use tactics for predictable search or iteration only when concrete repeated
obligations warrant them. Do not start a general framework as a separate
deliverable. Retain useful internal physical lemmas without importing
unnecessary decision-history alignment into the new headlines.

Runtime optimization is a supporting experiment. The leading candidate is
a bounded KCOV mapped-region/headroom contract that preserves the actual
capacity metadata, accounts for callback writes and saturation, and retains
the independent captured comparisons. A proved memory-representation change
is an alternative if it is smaller. Reducing captured capacity is only a
diagnostic and cannot count as unchanged-capture acceleration.

[AGENT 2026-10-18] Initially timebox this supporting investigation to two
hours of focused work. If it has not produced a proved, measurable improvement,
record the result and return to subsystem adequacy. Broaden it only for a
demonstrated blocker to that goal. Measure unchanged captures with matching
work before and after; report optimization success separately from theorem
completion.

## 6. Cost accounting and checkpoint policy

The planning estimate is one to two days of sustained work after resumption,
not a measured forecast or a guarantee. The main uncertainties are the
bucket-splice proof and the executable-reconstruction bridge to lookup.

Record UTC stage boundaries and elapsed time for assertion development,
counterexample diagnosis, fresh instruction proofs, reconstruction updates,
composition, capture/runtime work and validation. Distinguish overlapping
jobs from additive time; do not call elapsed agent time person-hours.
Track proof sizes and fresh versus reused instructions as supporting data,
not as substitutes for completed theorems.

The report must answer:

1. Which invariants were found by execution, and which were still invented
   during proof? Did proof work force changes to tested definitions?
2. What did complete removal cost beyond its three existing instructions?
3. How much of replacement reused the removal machinery, and what was its
   marginal cost?
4. Did function postconditions suffice for composition, or what missing
   state/readiness obligations did composition expose?
5. What remains bespoke, and which further mechanism has a demonstrated
   repeated use rather than speculative value?
6. Is workload iteration fast enough in practice, and what remains unknown
   about fresh-function and campaign-wide cost?

Use internal commits and progress reports throughout the run. Do not stop
work merely because one component lemma or function finishes. The substantive
checkpoint is completion of the subsystem goal, or a concrete blocker or
budget overrun requiring reassessment. Report an incomplete target honestly;
do not relabel a smaller result as completion. Preserve counterexamples and
their reproducible definitions rather than narrowing valid entry states.

## 7. Trust, validation and deliverables

All heavy work stays inside `capped`, with normal build parallelism and
`LEANUX_QEMU_SLOTS=16` for applicable runs. KILLED banners and timeouts are
failures. Keep outputs private to this worktree and the approved oracle
read-only. Existing inherited warnings remain visible; introduce no warning
suppression or new warning and report any unresolved inherited findings.

The theorem statements, executable entry domain and explicit trust premises
must be reviewable. Keep every unproved semantic or environment assumption
named in `binary/TrustBase.lean` and expose relevant assumptions as headline
hypotheses. Reconstruction and its preservation are proved definitions, not
axioms. No `sorry`, native-evaluation axiom, unsafe proof path, or bypass of
kernel checking is permitted. Report `implemented_by`, `extern` or other
trust-sensitive mechanisms encountered on the proof path.

Print axioms for every headline and witness; only `propext`,
`Classical.choice` and `Quot.sound` are standard. Run fresh `leanchecker`
replay of each headline closure. At the claim point prepare a leanexport
of the complete headline and witness modules and record their exact commit.
The external gate is `lake check --from-export` run by the user outside
nono, following `binary/README.md`. Local replay is not external acceptance.

Deliver one commit series on this branch, one register row for this increment,
and one report covering the full goal, findings, measured cost and limitations.
Update reproduction commands and identify the exact trust surface. Generated
captures, logs, measurements and exports remain ephemeral; commit their
conclusions and commands, not evidence bundles. Do not claim new function
coverage for a function whose full theorem remains open.

## 8. Pause and resumption

This charter is the current stopping point. No implementation of this
increment begins during the charter-writing turn. Resume only on the user's
instruction, using the baseline and work order above; the supporting runtime
budget starts with resumed work, not while paused. No background build,
capture or proof job is needed to preserve this checkpoint.
