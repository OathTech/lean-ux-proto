# Independent review of the window-proof port

## Status — 2026-10-13

No unresolved proof, source-coverage or documentation finding remains in the
completed port. The final full build succeeded, and the source declarations,
axiom-print list and printed results agree. All six findings below are resolved;
the final effort-unit correction was independently rechecked after the writer
slot returned to the coordinator.

Reviewed by the independent `statement_review` subagent. The complete charter
and predecessor review at `3e1b256` were read; neither the predecessor verdict
nor the implementers' interpretation was treated as settled. Review covered
statement fidelity, source observation, lifecycle framing, actual failure
handling, the W2 dump changes, validation and the requested documentation.
The reviewer ran no builds, differential checks or guests, and changed only
this review file after an explicit single-writer handoff.

## Exact reviewed state

The base is `ef7c5356b9ce02fa13c19a08ae6adc71f3c4644e`, branch
`spike/window-r`, in `.worktrees/spike-window-r`. The reviewed port was still
uncommitted: 46 new `Leanux/Spikes/*.lean` files, the spike-library/default-target
addition to `lakefile.toml`, the updated spike report and conventions document,
and this review. The mirror diff outside `Spikes` was empty.

After the final whitespace cleanup, the aggregate SHA-256 of the 46 Lean files
was `65d1a9154284b4b006ce79531d25d2c92ab70559282470234fb1142b27e46e66`.
This hashes each lexically sorted relative path, NUL, its bytes, and NUL.
It identifies the source reviewed and built before the coordinator's checkpoint;
it is not a claim that the branch already had a final commit.
A final staged-diff follow-up verified removal of exactly one blank EOF line
from each of seven files; no other source bytes changed.

## Findings and dispositions

**R1 — Mechanical renaming changed executable error text and a constructor.
Resolved.** The initial port of `GhostOperations.lean` contained strings such
as `a floodLogged to ...` and `the batchLogged queued`, and matched
`.injectLogged` where the real constructor is `.inject`. The strings are part
of exact `Stop` results, so this was a semantic erasure defect as well as an
elaboration defect. The coordinator restored the original literals and
constructor. The corrected source was rechecked, and its erasure proofs and
the complete project now compile.

**R2 — Counterexample and new exports must be in the required build/audit.
Resolved.** The checked arbitrary-World witness is imported by `Axioms.lean`,
so the required default build checks its guards. The new whole-syscall exports
and supporting theorems have explicit axiom prints. Independent source-name
and final-output comparisons found 1,240 distinct declarations, prints and
reports, with no missing or extra names and no axiom outside the permitted
three. The final build returned exit 0 with 94 jobs; the reviewer read its
completed output, and the build owner supplied the process exit status.

**R3 — Erasure plus endpoint evolution does not prove event completeness.
Resolved in the current argument.** The predecessor review's claim that any
unlogged acceptance would make `syscallLogged_evolves` unprovable is too strong:
validation followed by deletion of that lifetime can leave an ordinary final
snapshot and an unchanged history. This is a counterexample to that generic
reasoning, not a discovered omitted call in either concrete observer. The
current report explicitly corrects it. Completeness rests on the concrete
source substitution reviewed below, together with the local exact append
theorem; erasure and evolution establish their separate formal obligations.

**R4 — The old nonreceive classification and observation wording do not port
unchanged. Resolved by explicit refinement and a checked witness.** General
scheduling in send/timer waits, and NET_RX at an encrypt poll, invalidate the
old arbitrary-World classification. `NoReceiveCall` now also excludes
`wgSet`, `wgUp`, `wgXmit`, `wgAdvance` and `wgObserve`; dispatch bodies are
classified separately. `PortCounterexample.result` checks original
`.wgAdvance 0` retaining lifetime 1 while changing its counter from 0 to 1
and its first bitmap word to 2. The report correctly identifies this as an
arbitrary-World witness, without claiming an accepted-trace counterexample or
a repeated acceptance. It adds no quiescence premise to conceal the change.

The new `Activation.consistent` evaluates a copied World and discards it.
Its validator evaluations therefore belong to a discarded trial, while actual
activation runs commit their events. The observer and report distinguish these
cases. The probe preserves the original failure handling: a hidden-record
mismatch returns false; every other `Stop` propagates. No generic error
swallowing was added.

**R5 — Ranked recommendations lacked charter-required references and altitude
judgments. Resolved.** The conventions document now ranks its recommendations,
gives references at `ef7c535`, and labels their altitude implications. In
particular, the observation recommendation is conditional: proof-side history
or an instrumentation cut may preserve the operational boundary, whereas
history fields or proof-specific production branches would not. The main
report supplies effort and named refinement links for each intermediate model.

**R6 — The predecessor estimate's unit was shortened. Resolved.** The
predecessor review estimates four to eight **agent-hours**, not four to eight
elapsed hours. The coordinator restored that unit. The reviewer independently
rechecked the corrected wording and the explicit distinction from the current
port's 29-minute elapsed implementation/validation figure and approximately
36 minutes through final review. This did not affect a theorem or validation
result.

## Statement and coverage assessment

`S1` quantifies over the original `Runner.executeTrace` success without an
extra reachability, callback or trace restriction. Its history uses global
allocation lifetimes (`internalId`) and wire nonces. `counterLogged_run` records
one event exactly when the actual validator returns true, including packets
discarded later in committed execution. Deletion does not clear the history;
fresh lifetime allocation preserves separation from old events.

The following source paths were checked separately from erasure:

| Original path at `ef7c535` | Observer treatment |
| --- | --- |
| Sole validator call, `WG/RxData.lean:362` | `RxPoll.lean:35` substitutes `counterLogged`. |
| Poll caller, `Env/Batch.lean:113` | `napiSoftirqLogged` uses `rxPollLogged`. |
| Poll caller, `Env.lean:760` | `pollScheduledInlineLogged` uses `rxPollLogged`. |
| Encrypt callback, `Env/Batch.lean:158`; worker hook, `WG/Data.lean:108` | `encryptStepLogged`/`encryptIterLogged` receive the logged NET_RX callback. |
| Decrypt callbacks, `Env/Batch.lean:162` | Both softirq and IRQ-exit callbacks are observed. |
| Committed activation runs, `Env/Batch.lean:224` and `:275` | Dispatch and resumption use `activationRunLogged`. |
| Discarded trial, `Env/Batch.lean:197` | Original `Activation.consistent` is lifted; real World and history are retained. |
| Send/timer waits, observation, injection, flood and batch | `GhostOperations`, `GhostSyscalls` and `GhostRunner` follow all reachable committed scheduler calls and syscall tails. |

`S2` retains its exact mirror execution, acceptance and update results. The
128-word shape premise is explicit. Direct inspection against the locked
`receive.c:295–331` confirms the one-based increment, inclusive lower boundary,
circular word clears before the bit test, and test-and-set update. The theorem
allows arbitrary `Nat` words; correspondence to representable C states also
uses 64-bit words. This is the charter's mirror-to-property result, not a C
semantics simulation.

The original S3 exports state the lifecycle-aware nonreceive frame, surviving
counter equality and the other-slot frame for both validator outcomes.
`S3_syscall` additionally connects every successful original whole syscall to
its exact observed run and an `Evolution` witness, from the named lifetime
invariant. `S3_syscall_ambient` includes the runner's following ambient step.
Their callback obligations are discharged concretely. Neither export relies
on assuming the old nonreceive classification. Endpoint `Evolution` remains
a relation over projected states and histories; it does not independently
replace the source-coverage argument above.

The W2 stepped dump helpers have snapshot contracts for chunk, completion,
start, receive and socket updates. Both new syscall constructors are covered
by the original-action dispatch/frame composition. Their errors retain the
original paths rather than being converted into successful results.

## Declaration accounting, validation and process

Independent comparison with the predecessor axiom list confirms:
1,180 old declarations, 1,141 retained names, 39 removed names and 99 new
names, yielding 1,240. The removed groups are the 12 obsolete worker/scheduler
contracts, 25 environment contracts that are obsolete or no longer true, and
two `dumpSize` contracts. The report accounts for their replacements; false
ordinary contracts were not retained by adding hidden assumptions. All eight
terminal names and both new whole-syscall names are present.

The reviewer checked the final 94-job build output and all 1,240 axiom reports,
the source admission/axiom/unsafe/native-shortcut scan, the empty mirror diff,
and the unit output. The unit owner reported exit 0: 86 tests ran, with one
optional kernel-build test skipped. Its trailing negative-test JSON saying
`fail` is not the suite verdict; the suite reports `OK (skipped=1)`.
Reproduction commands are in the main spike report. No evidence logs or build
outputs are part of this review artifact.

The coordinator reported allowing disjoint simultaneous writes earlier in the
port. That violated charter §6's single-writer condition; separate files did
not make it compliant. The main report records the deviation and restoration
of serial writer handoffs. This reviewer remained read-only until the explicit
handoff for this file. The final source review and complete validation do not
erase that process deviation.
