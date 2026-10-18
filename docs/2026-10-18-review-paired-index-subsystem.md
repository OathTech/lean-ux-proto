# Independent review: paired index subsystem

Reviewed baseline: `41675f863a944db2853701674b398a57a6853c0a`, branch
`task/binary-pair-runner`, 2026-10-18. This review covers the stated sequential,
fixed-allocation result; it does not independently establish its ELF decoding,
callback-image hypotheses, hardware interpretation, or kernel entry reachability.

Verdict: **proceed with insertion on this foundation**, retaining the explicit
conditional scope. I found no circular future-execution/precondition premise,
replacement of the actual mirror by a specification, or defect in the finite
composition argument. Two permission-surface issues below should be addressed
when extending that surface. Neither invalidates the present conditional
theorem: both make a hypothesis stronger than necessary. External export
acceptance is still pending and must remain reported separately.

## Findings

### R1 — Medium: permission domain includes arbitrary unverified heaps

`binary/PairSequenceExecution.lean:32` defines `EntryDomain` as any successful
`prepare` applied to any `current : MachineState`. `prepare` installs ABI
registers and a return slot; it does not check the heap, callback readiness,
source admissibility, or reachability from the checked initial state
(`binary/PairSequenceCheck.lean:61`). Consequently,
`ReturningDomainPermissions ... (EntryDomain ...)` in the headline is access
safety for many more states than any sequence covered by the initial check
can reach. It is not merely permission safety along the proved execution.

This is not circular and does not make the conclusion unsound. The concern is
future applicability: a real permissions map can admit every intended execution
without satisfying a universal claim over malformed, unrelated prepared heaps.
Testing the accepted cases cannot establish this stronger domain premise.

Recommended disposition: make the permission family range over entries whose
readiness has been established, or otherwise give an explicit, sufficient
physical access-domain predicate that the composition proves at each call.
This weakens the permission hypothesis; it should not narrow R, narrow the
accepted source domain, or assume that a future execution exists. Until then,
state this quantifier breadth explicitly among the limitations.

### R2 — Medium: returning-history permission premise has no first-return boundary

`binary/TrustBase.lean:130` quantifies over every `ActualHistory` whose last
state satisfies `Returned`. `Returned` checks only the endpoint PC, stack and
callee-save registers (`binary/TrustBase.lean:116`). It does not say that this
is the first return. A history can reach the return state, execute a caller
continuation, and later reach another state satisfying the same endpoint
predicate. Such a history also falls under `ReturningCallPermissions`.

This matters for the abstract ambient `fetch` used by the theorem: it can
contain caller instructions outside the anchored ranges. For example, an
extension at the return destination can execute an otherwise unrelated access
and jump back while preserving the tested registers. The permission hypothesis
then demands permission for that caller access too. The paired runner, in
contrast, stops immediately at its return destination
(`binary/ProbeSupport.lean:268`).

Again this is an unnecessarily strong premise, not a proof of an unsafe run.
Recommended disposition: define the permission audit on a history stopped at
its first call boundary, in a way that also handles removal's tail call. A
first-boundary predicate should not rely solely on a particular syntactic RET
instruction. Prove that the histories used by the execution theorem satisfy
that boundary, or document the broader premise until this is done. Avoid
describing the existing quantified premise as excluding all executed caller
continuations.

## Checks on the argument

- `Corresponds` is equality with the same executable reconstruction used by
  the runner (`binary/PairMemory.lean:147`). The decoder does not inspect the
  expected source state. Its target includes every source peer and keypair,
  so removing an object from the supplied Names cannot silently omit it from
  the comparison. Bucket order, owner peer words and peer counts are related;
  unrelated World fields and diagnostic histories are not.
- Linkage validity is checked separately and carried together with
  reconstruction in `Ready` (`binary/PairSequenceFacts.lean:69`). Mapping,
  immutable kinds, coverage phases, preempt state and pending-softirq state
  are explicit physical resources. They are not claims of source-observable
  history alignment.
- `AdmissibleSequence` depends only on accepted source prefixes. It contains
  neither a machine state nor a successful binary run. The actual mirror
  functions are used by `source`; accepted execution remains a visible
  condition, including the mirror's explicit refusals.
- `call_checked` derives each function's executable Pre from retained
  resources. `install_ready` proves the caller transition's heap/service
  frame. `sequence_from_ready` invokes the call theorem, obtains the actual
  returned state's `Ready`, and uses that state for the induction hypothesis.
  There is no rematerialization or new Names interpretation between calls.
- The execution is universal over Kraken's undefined effects through
  `Effects.All`, rather than merely one favorable concrete seed. The two
  runtime seeds are supplementary tests. Fault/unimplemented branches do not
  become silent successful steps.
- The public sequence postcondition exports the final `Ready` and ordered
  per-call interfaces/histories. Intermediate `Ready` facts are proved and
  consumed inside the induction, not retained in `Observed`. This suffices
  for the stated final composition. A later consumer that needs reconstruction
  at every recorded boundary should export those facts explicitly rather than
  treating `Observed` as already containing them.
- The five callback contracts guarantee actual Kraken execution with stated
  effects, but remain hypotheses. Runtime execution of their instruction
  bodies is not a discharge of those universal hypotheses. The report
  distinguishes this correctly.

## Capture and test interpretation

The mutator capture tests reconstruct the mirror's input projection from the
captured entry (`binary/PairMutatorCapture.lean:44`), execute the actual mirror
function, and compare the resulting projection against both Kraken's return
and independently captured kernel return bytes (`binary/PairMutatorCapture.lean:121`).
They do not reconstruct the expected source post-state from the return.
This is a useful transition test, not an independent test that a workload's
mirror prefix reaches the captured entry. That distinction is explicit in
the report and runtime output. The endpoint comparator checks every supplied
capture byte and the represented registers/flags; the complete PC sequence
is checked too. These are finite sampled executions, not substitutes for the
theorem or for the missing callback-image proofs.

## Consequence for the next random-input boundary

Keep supplied random inputs outside physical reconstruction. A new contract
must not fix one deterministic machine state and then promise that actual
Kraken execution returns every arbitrary caller-supplied draw. State a concrete
machine/stream compatibility condition, or expose the draw produced by an
actual execution and establish its coupling to the supplied stream. State
stream consumption and frame effects separately. Compatibility must not be
defined as the desired insertion simulation, its future R, or its successful
completion. Actual captures can test this boundary, but do not prove its
universal contract. An unmodeled ordinary helper must not become trusted merely
because it is placed behind this boundary.

## Independent validation

Read the charter, report, complete headline and printed surface, named trust
declarations, reconstruction, caller setup, readiness derivation, finite
execution semantics, and captured replay/comparison path. No implementation
file was edited.

- `capped /usr/bin/python3 -B -m unittest binary.test_trust_gate`: exit zero.
- `capped lake env leanchecker --fresh PairSubsystemSurface`: exit zero,
  independently replaying the headline and witness closure.
- External `lake check --from-export` acceptance remains the user's pending
  gate. Local replay must not be reported as that acceptance.

This was a bounded surface review, not an independent rerun of all QEMU
captures or a proof of the universal service hypotheses.
