# Prototype pause handoff — 2026-09-21

Paused at the user's explicit request. Do not resume implementation until asked.
The governing plan remains [prototype-plan.md](prototype-plan.md); current machine
state is recorded in `.artifacts/runs/campaign.json`.

## Completed and preserved

- Worktree bootstrap and offline tooling are implemented and checked.
- The executable Lean model covers the frozen sequential FD/eventfd contract.
- The Linux runner uses the pinned kernel in QEMU, a fresh process per trace,
  and per-operation KCOV records.
- All 35 handwritten traces, comprising 245 operations, agreed in three fresh
  independent runs. The ledger records G1 as passed.
- All 1,000 distinct generated traces agreed, comprising 34,932 operations.
  Another 32 independently authored traces, comprising 480 operations, agreed.
- Configured-source capture includes eight translation units and 876 checked
  identities. Comparison against the pinned archive checked 801 source members.
- The two local Lean proofs compile and pass the current independent audit at
  trust level zero. The eventfd stepping theorem uses `propext` and `Quot.sound`;
  the alias-preservation theorem uses `propext`. These relate Lean encodings;
  the configured-C-to-reference bridge remains formally unproved.
- The restricted syzkaller adapter and its documented limits are implemented.
  Nineteen ordinary implementation/unit checks passed at the latest checkpoint.

The campaign is **not complete**. G2 still needs the model-error repair exercise;
G3 and G4 remain pending. Passing the generated corpus or current proofs does not
replace those obligations.

## Resume work, in order

1. Read the master plan, ledger, and this handoff; obtain explicit resumption.
   The user directed that remaining work stay on modeling and formal verification,
   with no further cybersecurity-related tasks. Retain completed environment
   evidence without restarting those investigations or tests.
2. Refine `evaluator/ProofAudit.lean` to compare each declaration's actual closed
   type directly with the fixed proposition (or audit named evaluator witnesses).
   Its current examples establish expected-type elaboration. Also make
   `evaluator/proofs.py` check that the frozen statement strings match the
   checker's statements; it currently uses their names and matching hardcoded
   examples. Review found no defect in the present proof arguments.
3. Finish structural acceptance integration. Complete implementation-module
   discovery is implemented in `capture-correspondence.py`; reviewed file
   identities are recorded in `correspondence/implementation-v1.json`. Make
   acceptance enforce that identity check and require renewed correspondence
   review when implementations change. Label presence alone is not structural
   proof. Host validation followed by canonical serialization defines raw input
   validation; the standalone Lean JSON parser is not the syntax validator.
4. Demonstrate finding, reducing, and agent-repairing a deliberately introduced
   aliasing model error, then replay the accumulated corpus. No such model error
   or repair candidate has been created yet. The generator and reducer are ready.
5. Complete ordinary evaluator correctness controls, the final reproducible
   acceptance command, one-case replay command, job-resume command, interruption
   exercise, and final acceptance report. These command interfaces are not yet
   implemented; do not mistake the existing Python APIs for the final deliverable.

## Evidence locations

| Evidence | Repository-relative path |
| --- | --- |
| Handwritten comparisons | `.artifacts/runs/evidence/G1-independent/repeat-{0,1,2}/` |
| Generated inputs and ten completed batches | `.artifacts/runs/evidence/G2-generated/` |
| Additional comparisons | `.artifacts/runs/evidence/G2-generated/critic/` |
| Configured source and mappings | `.artifacts/runs/evidence/configured-source-v1/` |
| Current proof audit | `.artifacts/runs/evidence/proofs-path-corrected/` |
| Promoted worker evidence and source snapshots | `.artifacts/runs/evidence/pause-2026-09-21/` |
| Cleanup receipts | `.artifacts/runs/evidence/pause-2026-09-21/receipts/` |

Earlier failed build/proof attempts are retained as historical records. The proof
attempt named `proofs-initial` failed because its profile path was relative to the
wrong working directory; the corrected attempt passed. Lean/Lake required an
8 GiB per-process virtual address-space allowance and one Lean thread for the
fresh native build. Physical memory measurement is recorded separately in the
existing calibration evidence; this is not a group physical-memory allowance.

## Parked workspace

All worker agents finished and no project build or guest process remained when
parking began. All four task worktrees and their disposable scratch directories
were removed through the registered manager after evidence promotion. Only the
main checkout remains. Small Git refs `task/linux-runner` and
`task/source-correspondence` retain original task commit identities; their changes
are integrated into main. They do not retain build directories.

Exact evaluator source snapshots, input manifests, and build logs were retained;
disposable compiled outputs were removed. Resumption should create a new uniquely
named evaluation worktree and fresh build. Do not reuse removed worktree IDs.
Shared tools, dependencies, kernel outputs, and global configuration were not
changed during parking. The final checkpoint commit is recorded in the ledger.
