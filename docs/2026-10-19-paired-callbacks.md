# Shared callback image proofs: increment report

Status: in progress on `task/binary-pair-runner`. Start 2026-10-19 17:24:01 UTC,
baseline `d61a8027`. The [charter](2026-10-19-charter-paired-callbacks.md) governs
the scope and budget. All five image contracts and remove/replace first-return headlines are locally proved; lookup first-return and closing validation remain in progress. External acceptance of this increment is pending.

## Review and dependency

The independent [charter review](2026-10-19-review-paired-callback-charter.md)
found R1: insertion's first-return claim requires an additional random-service
interior safety proof. Its endpoint frame and input coupling do not imply this.
The finding is accepted; the user chose the bounded revision recorded in the charter.
Five-callback implementation proceeds independently after review, starting
2026-10-19 17:30 UTC. First-return is now scoped to lookup/remove/replace;
insertion and mixed insertion retain the documented broader permission premise.

Baseline assumptions are the five behavioral callback contracts, decoding,
serialized environment and access permissions; insertion additionally uses
RandomReturnContract and RandomInputCoupling. The preceding insertion export
from `5433d7781d9d809b82ea4c19faa13d40af9a4957` remains externally pending.

## Measurements and failures

Preparation and charter review occupied roughly six elapsed minutes. This is
wall time with the independent reviewer running concurrently, not aggregate
person-hours. A read-only Lean API probe exited with errors for three guessed
identifiers; it established the actual load/store definitions, not a passing
build or theorem. Implementation, tests and proof measurements follow below.

### First callback calibration, 17:49 UTC

`CallbackBh.bh_image_contract` proves the existing `BhEnableContract` from
`ServiceImage.fetch`, including modular count subtraction, conditional pending
word reads, its exact memory frame and preserved ABI. The execution retains a
fixed-stack interior guard, useful for the subsequent first-return proof.
`#print axioms` lists only propext, Classical.choice and Quot.sound. This is a
local build result, not yet the external export gate.

Implementation from 17:30 to 17:49 took about 19 elapsed minutes: roughly the
first eight built executable cases, diagnosed runtime parser reduction, and
prepared shared machinery; the remainder developed and debugged the BH proof.
These categories overlap and are approximate, not instrumented task timings.
The proof is 189 lines; the reusable execution module is 78 lines. Remaining
callbacks and first-return integration are still open. This calibration leaves
room in the eight-hour budget, so the increment continues.

The generated suite executes 3,032 coverage cases and 50 BH cases, totaling
51,636 instructions. It tests early returns, modulo wrap, aliased destinations,
argument widths, nested counts and a rejected return-word overlap. These are
generated machine states, not captures. The executable readiness assertions
have ordinary Lean implication proofs to the unchanged named readiness
predicates. Reproduction: `capped lake build binary-callbacks CallbackBh`, then
`capped .lake/build/bin/binary-callbacks`, from `binary/`.

[AGENT 2026-10-19] Service decoding now produces literal instruction terms at
elaboration, as the anchored images already do. The old runtime parser is
retained for a per-listed-instruction executable comparison. Both reject the
unreachable UD2 at the hardirq failure site; rejection remains a failing fetch.
This avoids kernel reduction through a text parser and does not add an ISA
assumption. The external ELF/decoder interpretation remains explicit.

Development failures: the bundle Python lacked elftools (the system Python
regenerated successfully); runtime parser reduction hit recursion/heartbeat
limits; a compile-time parse experiment correctly rejected UD2; intermediate
Lean proofs failed elaboration, arithmetic normalization or framing until
repaired. One edit command used a wrong relative path and made no edit. No
KILLED banner, timeout or sandbox denial occurred. Inherited dependency lint
warnings remain visible; the new modules emit no warnings. The first
successful callback build checked the current complete proof and reported no
sorry axiom; failed intermediate elaborations are not counted as proofs.

### PC callback calibration, 18:00 UTC

The full `pc_image_contract` and ambient-decoder `pc_contract` now build with
only standard axioms, over unchanged `KcovReady .pc`. This includes every
preemption/mode early return, conditional metadata reads, capacity boundary,
64-bit increment wrap and potentially aliased stores. `bh_contract` likewise
transports the first image proof. `ServiceDecoderAgreement` is the explicit
literal-decoder premise; it does not assert callback behavior.

This callback took approximately eleven additional elapsed minutes and 329
function-specific lines, with 70 lines of new reusable memory/arithmetic facts
and 47 lines of decoder transport. The comparison store tail is already proved
using the same framing mechanism. All wrappers and consumers remain open.
`capped lake build CallbackContracts CallbackCmp binary-callbacks` passed; the
same generated suite passed again. New modules have no lint warnings. The
ordinary intermediate elaboration failures primarily concerned numeric
normalization, instruction-state unification and conditional-branch arithmetic;
no counterexample or new readiness restriction was introduced.

### Five callbacks and consumer integration

All five image contracts were complete by 18:06 UTC. The shared comparison
body takes 380 lines; its three wrappers share `wrapper_plan` and
`wrapper_body`, with roughly 24 execution-proof lines per wrapper and a short
contract corollary. This added about six minutes after the PC checkpoint.
The comparison body covers capacity arithmetic and shifts modulo 64 bits,
including wrap and aliased store destinations. No readiness predicate changed.

`CallbackContracts` supplies each contract under only
`ServiceDecoderAgreement`. Fresh replay with
`capped lake env leanchecker --fresh CallbackContracts` exited zero.
`capped lake build PairCallbackAdequacy` passed, printing only standard axioms
for the four single-call and two finite-sequence corollaries. All six reuse
the existing accepted mirror run, reconstruction and physical postconditions;
the five behavioral callback hypotheses have been removed. Insertion and
mixed insertion still explicitly require their random-service and input
coupling contracts. The sequence corollaries retain their broader permission
premises at this intermediate checkpoint. First-return work remains open.

Consumer integration required 151 lines of explicit theorem statements and
applications, with no new physical invariant. The dependency rebuild checked
477 jobs. The generated service suite passed again with unchanged counts.
A temporary simplifier loop in shift normalization failed at the recursion
limit and was replaced by a specific shift-by-three equality; this was an
ordinary proof-development failure, not a changed ISA or hidden assumption.
New-module lints were repaired, including a deprecated theorem alias. External
export acceptance is still pending and no campaign coverage percentage changes
as a result of these shared-service proofs.

### First-return mechanism and mutators, 18:32 UTC

Removal and replacement now export their unchanged physical/reconstruction
postcondition, the actual instruction history, `BeforeOuterReturn`, and
`RunEnvironment` for that same history. The named hypothesis is
`FirstReturnCallPermissions`: access safety on actual prefixes before the
first state with both the supplied return PC and the consumed outer stack
word. The proof establishes the stronger interior stack exclusion, even if
the supplied return PC aliases an image address. Removal's tail-call to
BH-enable is included. No entry predicate, reconstruction or physical
separation premise changed.

`StackCps`, `StackPath` and `region_guarded` retain instruction stack effects
while reusing the physical region calculations. The five callback proofs
supply the same guard through their interiors. There is no executable
certificate classifier or classifier soundness assumption: the small tactic
selects a candidate stack delta, then proves its instruction-semantic lemma.
The first-return compositions currently duplicate the original composition
scripts, sharing their state, frame, arithmetic and source lemmas. This is a
real maintenance cost, not counted as new physical proof discovery.

The local build of `PairRemoveFirstEnvironment` and
`PairReplaceFirstEnvironment` passed (254 jobs), and both headlines print
only the three standard axioms. Approximate elapsed development since the
18:09 integration checkpoint is 23 minutes; a material portion diagnosed
stack automation. Nested machine subtraction expanded into expensive modular
integer cases under `omega`. Direct bit-vector cancellation replaced it and
checks wraparound without an extra range hypothesis. The region tactic also
now chooses stack deltas deterministically before proving them. These fixes
made each new mutator composition module build in approximately 0.7–2.2 s.

Failures in this stage include ordinary elaboration/name-resolution errors,
deterministic heartbeat/recursion failures, and manually terminated diagnostic
Lean runs after their owned PIDs were checked. The `capped` direct-Lean runs
printed KILLED with exit 143 on termination; these are failures, not passes,
and no OOM is inferred from that banner. A wrong-directory edit/build command
also failed without changing the intended file. The final checked mutator
proofs contain no admitted theorem. Lookup first-return, sequence integration,
closing review and external export acceptance remain outstanding.

### Conditional-memory review repairs, 18:45 UTC

The independent review identified two test defects: the fixtures left
conditionally unused metadata mapped, and an initial negative-control helper
accepted any failure. Both are repaired. Seventeen positive cases remove bytes
that the selected path must not read. Thirty-nine negative cases require the
specific expected error and address, so a step-budget failure or unrelated
fetch failure does not pass. Four missing-return-word cases are runner entry
rejections during its initial metadata read, not ISA memory faults.

The reviewer independently reran the executable: 3,032 KCOV cases, 50 BH cases,
17 conditional positives, 39 negatives, and 51,935 instructions in successful
cases. All passed. The review's lookup/sequence boundary finding remains open.

The new `history_guard` lemma recovers an interior guard from a universally
proved complete region history. Its witness selection establishes only the
current guard; the execution proof still retains every undefined branch.
Lookup's ten-instruction prologue, its first callback, and reusable guarded
coverage calls now check using this mechanism and the original memory proofs.
This is intermediate progress, not a lookup first-return theorem. The sibling
composition scripts still duplicate existing bookkeeping; that cost remains
visible in this increment's assessment.
