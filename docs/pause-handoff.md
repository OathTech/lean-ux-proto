# Prototype pause handoff — 2026-09-21, corrected 2026-09-22

Paused at the user's explicit request. Do not resume implementation until asked.
The governing plan remains [prototype-plan.md](prototype-plan.md); current machine
state is recorded in `.artifacts/runs/campaign.json`.

The user has withdrawn all model-proof work. Proof files, handwritten Lean proof
references, contracts, and audit code were removed on the dedicated removal
branch. Older proof tasks and proof evidence in the ledger are historical and
must not be resumed. Follow [AGENTS.md](../AGENTS.md): executable Linux behavior
and step-by-step computational fidelity are the deliverables. This cleanup does
not resume the campaign or solve the reported classifier interruptions.

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
- The restricted syzkaller adapter and its documented limits are implemented.
  Nineteen ordinary implementation/unit checks passed at the latest checkpoint.

The campaign is **not complete**. G2 still needs the model-error repair exercise;
G3 and G4 remain pending. Passing the generated corpus does not establish
step-by-step correspondence or replace the remaining obligations.

## Resume work, in order

1. Read the master plan, ledger, and this handoff; obtain explicit resumption.
   Keep work on the executable model and its Linux comparisons, with no model
   proof tasks and no further cybersecurity-related tasks. Retain completed
   environment evidence without restarting those investigations or tests.
2. Finish structural acceptance integration. Complete implementation-module
   discovery is implemented in `capture-correspondence.py`; reviewed file
   identities are recorded in `correspondence/implementation-v1.json`. Make
   acceptance enforce that identity check and require renewed correspondence
   review when implementations change. Review every modeled step against Linux;
   label presence alone does not establish computational fidelity. Host validation
   followed by canonical serialization defines raw input validation; the
   standalone Lean JSON parser is not the syntax validator.
3. Demonstrate finding, reducing, and agent-repairing a deliberately introduced
   aliasing model error, then replay the accumulated corpus. No such model error
   or repair candidate has been created yet. The generator and reducer are ready.
4. Complete ordinary evaluator correctness controls, the final reproducible
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
| Promoted worker evidence and source snapshots | `.artifacts/runs/evidence/pause-2026-09-21/` |
| Cleanup receipts | `.artifacts/runs/evidence/pause-2026-09-21/receipts/` |

Earlier build attempts and removed-proof reports remain historical records,
not active acceptance inputs. Lean/Lake required an 8 GiB per-process virtual
address-space allowance and one Lean thread for the fresh native build. Physical
memory measurement is recorded separately in the existing calibration evidence;
this is not a group physical-memory allowance.

## Parked workspace

All worker agents finished and no project build or guest process remained when
parking began. All four task worktrees and their disposable scratch directories
were removed through the registered manager after evidence promotion. At that pause checkpoint, only the
main checkout remained; subsequent maintenance worktrees are recorded in the ledger. Small Git refs `task/linux-runner` and
`task/source-correspondence` retain original task commit identities; their changes
are integrated into main. They do not retain build directories.

Exact evaluator source snapshots, input manifests, and build logs were retained;
disposable compiled outputs were removed. Resumption should create a new uniquely
named evaluation worktree and fresh build. Do not reuse removed worktree IDs.
Shared tools, dependencies, kernel outputs, and global configuration were not
changed during parking. The final checkpoint commit is recorded in the ledger.
