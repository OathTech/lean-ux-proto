# Shared callback proofs and first-return permissions

Status: proposed for independent review. Worktree `binary-pair-runner`, branch
`task/binary-pair-runner`; starting checkpoint `d61a8027`.

[USER 2026-10-19] Develop the agreed shared-callback increment: write and
independently review its charter, resolve findings, then execute the ready plan
to its closing checkpoint. Keep the existing sequential scope and measure
whether testing candidate contracts followed by reusable proofs reduces cost.

## Objective and claim

Prove the five service contracts used by the index-family binary refinements
from the pinned decoded image, and instantiate them in lookup, remove, replace,
insert and retained-heap finite-sequence headlines. The five are KCOV PC,
variable/variable 32-bit comparison, constant/variable 32-bit comparison,
constant/variable 8-bit comparison, and BH-enable on the physically ready
no-pending-work path. The shared comparison body should be proved once.

The result remains refinement between compiled instructions under Kraken and
the actual executable Lean mirror, under explicit sequential environment,
permissions, decoding and remaining random-service/input assumptions. Tests
discover candidate domain and effect defects; only kernel-checked proofs
discharge universal contracts. Keep the existing general conditional lemmas
and add corollaries without these five behavioral hypotheses. Do not replace
them with a bundled or renamed assumption, or a premise asserting execution.

Repair the permission boundary to cover exactly actual prefixes through the
first outer ABI return, including removal's tail-call return. Avoid relying
solely on a syntactic RET instruction or on a final PC that could have been
crossed earlier. The theorem must export permission safety for the same
execution that establishes its postcondition.

## Fixed scope and baseline

Mirror `cb2348e`; Lean v4.35.0; clean private Kraken
`cd2ae360bfcf8e1fc719793405811ff49c3e75ce`; approved read-only s4 oracle,
ELF SHA-256 `16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774`.
Read and compare the current pins before claims. No merge, push, main, mirror,
oracle, global-state or other-worktree edits. All heavy work uses `capped`;
applicable guests use `LEANUX_QEMU_SLOTS=16`. A killed job or timeout is failure.

R remains the tested minimal reconstruction over WireGuard observations.
Callback readiness and frames are physical resources, distinct from R and the
supplied input tape. Do not narrow valid WireGuard states, dead-peer behavior,
or observations to accommodate a contract defect. A necessary physical-domain
repair must be justified by the image, exposed, propagated to consumers, and
accompanied by positive entry evidence and the failing counterexample.

RandomReturnContract and RandomInputCoupling remain explicit outstanding
hypotheses. This increment does not add allocation/free/RCU, compiled callers,
concurrency or allowed-IPs' additional comparison contracts. The earlier
insertion export from `5433d7781d9d809b82ea4c19faa13d40af9a4957` remains pending
external acceptance; independent work can proceed without claiming acceptance.

## Execution sequence

1. Fresh-eyes review of this charter and its supporting implementation. Record
   findings individually and fix or answer each with checkable reasoning. The
   review may inspect any relevant code or claim; it is not limited to this list.
2. Exercise the actual fetched service bodies against the same executable plans
   and readiness definitions the proofs will use. Cover early returns, mode and
   preemption branches, full buffers, machine-width wraparound, argument widths,
   pending-word read conditions, and alias/resource cases. Distinguish generated
   states from captured states; reuse recorded entries for positive applicability.
   Retain a small reproducible regression for each discovered defect.
3. Prove the first callback as a calibration point. Record discovery, diagnosis,
   proof and integration costs separately. Then prove the comparison body and
   wrappers, and the remaining callback. Follow actual instruction effects,
   including unspecified flags; no native axiom, sorry, unsafe or kernel bypass.
4. Supply proved contracts to the existing index-family clients and add revised
   headlines. Tighten first-return permissions and prove the execution boundary
   needed by those headlines. Preserve source/reconstruction results and derive
   later entry readiness through the existing retained-heap composition.
5. Run scoped paired workloads, positive witnesses, builds, headline axiom
   reports, fresh kernel replay and existing trust-surface checks. Obtain an
   independent closing review and disposition its findings. Prepare an
   exact-commit leanexport for the external gate; record acceptance only when
   the user supplies its result. Update one report, one register row and README.

## Success, measurements and stop conditions

Success requires all five image proofs, their use in the revised single-call
and mixed-sequence headlines, and a first-return permission statement tied to
the successful execution. Concrete positive entries still run to return.
The report lists hypotheses before and after, exact checked modules/pins,
counterexamples and fixes, and all failures. It reproduces TrustBase.lean and
names the remaining interpretation/environment obligations. Test count or
anchored instruction coverage is not a substitute for this deliverable.

Measure fresh proof lines and time, reused machinery, cost per subsequent
wrapper and consumer, and review/repair cost. Distinguish elapsed wall time,
focused development time and aggregate compute. The scientific question is
whether one shared binary service proof removes repeated assumptions and
meaningfully lowers subsequent integration cost; do not extrapolate a campaign
rate from this increment.

[AGENT 2026-10-19] Start time is 2026-10-19 17:24:01 UTC. Budget one working
day, interpreted as eight focused development hours and a hard reassessment
at 2026-10-20 17:24:01 UTC. Review and validation costs are included and reported.
After the first callback, assess whether the remaining deliverables fit. If a
false contract, missing semantic mechanism or composition obstruction requires
substantial new scope, preserve a concrete reproducer, report the blocker and
stop at an honest partial checkpoint instead of silently enlarging the charter.
At budget exhaustion do likewise. A ready plan authorizes execution, not changes
to the mirror or a widening of the trust assumptions to make the proof pass.

The closing report distinguishes local completion from external acceptance.
The external command is `capped lake check --from-export <prepared-export>`
from `binary/`, outside nono; export the revised headline closure and name its
source commit. Ephemeral logs, exports and captures stay in `.tmp` and are not
committed. The report and reproduction commands are committed on this branch.
