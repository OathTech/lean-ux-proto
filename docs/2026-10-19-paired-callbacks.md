# Shared callback image proofs: increment report

Status: in progress on `task/binary-pair-runner`. Start 2026-10-19 17:24:01 UTC,
baseline `d61a8027`. The [charter](2026-10-19-charter-paired-callbacks.md) governs
the scope and budget. The BH-enable image contract is locally proved; external acceptance of this increment is pending.

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
