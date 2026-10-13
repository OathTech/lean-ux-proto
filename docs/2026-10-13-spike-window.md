# Receive counter window proof spike

> Restructured 2026-10-13: the proof tree moved from `Leanux/Spikes/` to `Leanux/Proofs/`, laid out by layer and result; the map and the results register are [docs/proofs.md](proofs.md). The names below are the historical ones.

## Progress — 2026-10-13

All eight terminal statements and both added whole-syscall statements compile
on `spike/window-r`, based at `ef7c5356b9ce02fa13c19a08ae6adc71f3c4644e`.
The full build passed (94 jobs); all 1,240 declaration axiom prints use only the
three permitted axioms. Units passed: 85 passed and one optional kernel-build
test skipped. The mirror diff is empty. Independent review found no unresolved
proof or source-coverage defect; its findings and dispositions are recorded in
the [port review](2026-10-13-spike-window-self-review.md). There is no remaining
proof blocker. The port is complete and remains on its unmerged task branch.

The eight terminal statement names are retained. The added `S3_syscall` and
`S3_syscall_ambient` export the whole original action's evolution relation.
The scheduler changes require a documented refinement of `NoReceiveCall` and
an explicit distinction between committed execution and discarded probes.
The original classification has a checked executable counterexample in
`PortCounterexample.lean`; the required target imports its `#guard`.

## Pin, scope and provenance

- Current mirror: `ef7c5356b9ce02fa13c19a08ae6adc71f3c4644e`.
- Worktree: `.worktrees/spike-window-r`; branch: `spike/window-r`.
- Predecessor: `spike/window` at `ed069baaac310b018851b4454e61aac91233a10a`,
  based on `fb2c29ce1f16b1aa551540acee587dd380a81f0f`.
- Binding charter: [window-proof charter](2026-10-12-charter-window-proof.md).
- Independent predecessor review: `task/spike-review` at `3e1b256`,
  `docs/2026-10-12-spike-window-review.md`.

[USER 2026-10-13] Port the complete spike and axiom prints, repair proofs,
export whole-syscall S3, and give short recommendations for cheaper future ports.
Keep the mirror unchanged, use capped builds, commit only on this branch, and
leave main unchanged. No push, differential checks or QEMU guests.

[USER 2026-10-12] Carry out the charter as an isolated proof spike, use subagents,
checkpoint with agent attribution, and leave the branch unmerged. This explicit
task authorization is the exception to the repository's general prohibition on
theorem work; the standing rule is unchanged.

Process deviation, 2026-10-13: I mistakenly allowed simultaneous writes in
separate files while keeping a single build owner. Charter §6 requires one
writer at a time in the same worktree; disjoint files did not satisfy that rule.
The implementing subagents have returned ownership, and work is again serial.
The mirror and shared inputs remained unchanged. This deviation is recorded,
not presented as an authorized change of the charter.

[AGENT 2026-10-13] Restore a single writer for the remaining proof, documentation
and review handoffs, as the charter requires.

## Statements and wording deltas

| Statement | Original binding wording | Proved wording and reason |
| --- | --- | --- |
| S1 | For every trace and every record stream that the runner accepts (`Leanux.Runner.executeTrace`), in the execution's sequence of accepted data packets no two packets share (keypair, counter). | `Leanux.Spikes.S1`: every successful original runner execution has its exact observer history, with no repeated lifetime/nonce event. Events record every committed true original validator return, including packets later discarded. Keypair identity is the allocation lifetime (`internalId`), because device-local slots can be reused. |
| S2 | `counterValidate kp theirs` returns true in a state exactly when `counter_validate` would: `theirs < REJECT_AFTER_MESSAGES`, the keypair's counter `< REJECT_AFTER_MESSAGES + 1`, `theirs` within `COUNTER_WINDOW_SIZE` of the highest seen, and the bit for `theirs` not yet set; and when it returns true the resulting `ReplayCounter` is the C's update (the backtrack bitmap shifted and the bit set). | `Window.S2`, `S2_acceptance`, `S2_update`: exact execution, acceptance iff and update for an existing keypair with a 128-word bitmap. The high-water mark is one-based (`nonce + 1`), the lower edge is inclusive, and the bit is tested after advancing word clears. The C uses circular word clearing, not a physical bitmap shift. |
| S3 | Every operation the runner executes other than the data-receive path leaves every keypair's `receivingCounter` unchanged; and on the data-receive path only the keypair the packet names changes. | `Leanux.Spikes.S3`: every original nonreceive syscall, including post-dispatch work, has an ordinary lifetime frame; each validator preserves its frontier and every other projected cell. `S3_surviving` states unchanged counters for surviving lifetimes. Allocation and deletion are legitimate lifecycle effects. Batches may contain several receives, so the named-keypair clause applies per validator event. |

The eight terminal names are `S1`, `S3`, `S3_nonreceive`, `S3_validator`,
`S3_surviving`, `Window.S2`, `Window.S2_acceptance`, and `Window.S2_update`,
all under `Leanux.Spikes`. S1 has only the original runner's successful-execution
premise. S2 exposes an existing keypair and a 128-word bitmap; arbitrary `Nat`
word values are allowed. C representability additionally restricts words to
64 bits, while the admitted nonce bound prevents increment/window-addition wrap.
The validator frame covers both true and false results.

`S3_syscall` now directly quantifies over successful executions of
`Leanux.syscall call` from the lifetime invariant. It supplies the exact history
of that syscall observer and an `Evolution` witness relating the initial and
final snapshots. `S3_syscall_ambient` includes the subsequent `skipAmbient` used
by the runner. Neither theorem has an assumed callback-framing premise.

### Scheduler-dependent classification refinement

Predecessor definition, recorded exactly:

```lean
def NoReceiveCall : Syscall → Prop
  | .wgInject .. | .wgFlood .. | .wgBatch .. => False
  | _ => True
```

The old theorem asserted `OrdinaryAction (Leanux.syscall call)` for every call
satisfying that definition, from every starting World. At the new pin,
`runSendWorkers` and timer waits can run the general scheduler; encrypt worker
polls can run NET_RX. The old classification therefore cannot be carried over.
The conservative replacement also excludes `wgSet`, `wgUp`, `wgXmit`,
`wgAdvance`, and `wgObserve`. Both new stepped-dump calls remain ordinary.
`NoReceiveDispatch` separately classifies dispatch bodies, because a body's
ordinary behavior does not establish that its return-to-user work is ordinary.

`PortCounterexample.lean` supplies a checked concrete arbitrary-World witness:
a ready keepalive with nonce 0, followed by an uncrypted packet that makes the
placeholder scheduler dispatch a decrypt activation. The retained keypair has
lifetime 1 and an initially zero replay counter. Original `.wgAdvance 0`
returns 0 and retains that lifetime with counter 1 and first bitmap word 2. This
is a counterexample to the previous unconditional classification, not a repeated
acceptance or a counterexample starting from an accepted runner trace. The
second packet rejects before the cryptographic primitive because its receiving
key is invalid. The mirror is unchanged.

[AGENT 2026-10-13] Replace the old arbitrary-World nonreceive classification
with the conservative committed-receive classification above. Keep the original
beside its counterexample and observe receive-capable waits explicitly; do not
assume quiescence to recover the old theorem.

### Committed events and discarded probes

The predecessor prose said “every true original validator return.” The new
`Env.Activation.consistent` runs an activation on a copied World to test whether
it matches the records, then discards that World. Such trials can evaluate the
validator. The history must describe committed execution: events from the trial
are discarded with its effects. The original probe is therefore lifted unchanged;
its snapshot-preservation theorem does not assume anything about the trial body.
Actual `Activation.run` calls are observed.

[AGENT 2026-10-13] Acceptance events record committed true validator returns,
including packets discarded later in the committed execution. Consistency probes
retain the real World and history. This makes the new transactional boundary
explicit rather than treating trial evaluation as packet acceptance.

Erasure alone does not establish observation completeness. Nor does an ordinary
final snapshot or `Evolution`: an unlogged validation followed by lifetime
deletion can leave an ordinary final state. The predecessor review's stronger
completeness argument is not relied on. Completeness is tied to the concrete
source substitution: `counterLogged_run` proves the exact append at the validator;
`rxPollLogged` substitutes that call; both poll callers and every committed
scheduler/wait caller use their observers. Independent source review checks this
interpretation separately from the kernel-checked erasure and evolution results.

## Proof architecture

The stable semantic boundary is `Snapshot`, containing the allocation frontier
and each slot's lifetime/counter cell. `Ordinary` permits unchanged cells,
deletion, device clearing and atomic fresh allocation. Its surviving-lifetime
frame is independent of packet, queue, scheduler or JSON representation.
`Evolution` adds exact validator transitions. Its invariant combines bitmap
shape, unique bounded live identities, historical identity bounds, no duplicate
events, and `Remembers` for previously accepted nonces whose lifetimes survive.

- `Window`, `Refinement`, `MirrorCalls`: circular-word arithmetic, exact original
  validator execution, acceptance/update, and intermediate repeated-call result.
- `Ghost`, `RxPoll`, `GhostWorkers`, `GhostScheduler`: exact result/World/error
  erasure; packet-ID reads and frees; callback-parametric worker Step/Iter/Loop
  composition; bounded activation execution and scheduling. No fuel induction,
  ring occupancy invariant or extra trace premise is needed for the new scheduler.
- `GhostOperations`, `GhostSyscalls`, `GhostRunner`: committed receive work in
  injection, flood, batch, send/timer waits and observation; all syscall tails;
  the original runner including stepped initialization and suspended-activation
  rejection. Original leaf actions remain original calls.
- `FrameWGBase`, `FrameWGTransitions`, `FrameWGMore`: packet-store snapshots and
  lifecycle frames; dump chunk/start/receive contracts independent of cursor
  shape. Packet stores and netlink sockets lie outside the snapshot.
- `FrameWGConfig`, `FrameWGDevice`, `FrameEnv*`: configuration/lifecycle contracts,
  generic worker callbacks, ordinary environment leaves and discarded probes.
  Receive-capable waits use evolution rather than the now-false ordinary frames.
- `FrameKernel`, `FrameFS*`, `FramePipe*`: original unrelated-call framing. The
  three pipe loops retain the predecessor's checked progress proofs and exact
  proof-side factoring; their executable mirror definitions are unchanged.
- `Evolution*`, `Statements`: compose all concrete callers, preserve the runner
  invariant and export all terminal theorems plus whole-syscall S3.

The new scheduler's `workerIter` and finite activation loops fit existing generic
composition rules. Packet-store helpers need no representation invariant for
snapshot framing. The substantial semantic repair is following the scheduler
through the expanded set of waits; changing old theorem arities alone would be
incorrect. The new W2 helpers frame each chunk and the socket wrapper separately.

The intermediate models and their checked links are:

| Model | Abstraction and checked link |
| --- | --- |
| `Window.step` and `Remembers` | Pure circular bitmap update and remembered nonces. `counterValidate_execution` identifies the actual monadic execution; `cExecution_refines_step` and `S2` connect it to the pure update. `mirrorCalls_refines` connects repeated original calls. |
| `Snapshot`, `Ordinary` | Only lifetime frontier and lifetime/counter cells are retained. `snapshot_lookup`, `snapshot_store`, `cExecution_snapshot`, allocation contracts and concrete `OrdinaryAction` lemmas connect World updates to this projection. `Ordinary.preserves` and `Ordinary.old_slot` give its invariant and frame. |
| `GhostM`, `History` | Extend the original action with committed acceptance events. `counterLogged_run` identifies each emitted event; `counterLogged_erases`, `rxPollLogged_erases`, the caller erasures and `executeTraceLogged_erases` preserve exact original results, Worlds and errors. |
| `Evolution`, `Inv` | Combine ordinary lifecycle transitions with exact named validator steps. `counterLogged_evolves`, concrete caller evolution contracts and `Evolution.preserves` establish the history invariant. `executeTrace_accepted_nodup` connects this to original runner success; `S3_syscall` exports the original whole-action relation. |

Decisions carried from the predecessor, retained with their original provenance:

- [AGENT 2026-10-12] Use `Keypair.internalId` for lifetime identity, since the
  device-local `KeypairId` can be reused after device recreation.
- [AGENT 2026-10-12] Pair fresh frontier increment and default-window insertion
  atomically in the projection; refine the whole actual `keypairCreate` call.
- [AGENT 2026-10-12] Combine operational Hoare contracts with fixed-predicate
  `Std.Do` specifications; preserve shared continuation contracts in tactics.
- [AGENT 2026-10-12] Keep any necessary loop/helper factoring under `Spikes` and
  prove equality to the original action; use actual private constants where possible.
- [AGENT 2026-10-12, superseded above] Only inject/flood/batch were classified
  receive-capable at the predecessor pin. The new scheduler invalidates that list.

## Effort

The predecessor took about four hours on 2026-10-12. This port began at
00:33 UTC on 2026-10-13. The first complete build, axiom audit and unit suite
had passed by 01:02 UTC: about 29 minutes elapsed, with three subagents.
This is elapsed time, not summed agent effort; final documentation and review
followed, bringing the work through final review to about 36 minutes elapsed.
The predecessor review estimated four to eight agent-hours for the port.
Three subagents supplied scheduler implementation, dump/framing repair and
independent review. Packet-store and scheduler erasure repairs were direct.
Large dump helpers exceeded the first 800,000-heartbeat WP attempt; strict
composition with shared continuations proved them without a new premise.
The semantic work was expanding the observed wait paths and distinguishing
committed activations from discarded consistency probes. Initializer, syscall
and whole-S3 composition then reused the existing invariant architecture.

## Validation

The full build returned exit 0 with 94 jobs. It includes the executable
counterexample guards and the axiom-print target. All 1,240 unique source
theorem/spec declarations have exactly one matching axiom print and report;
none uses an axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
The eight terminals and both whole-syscall additions are included. Independent
review repeated the source-name and output comparisons. No admission, added
axiom, unsafe declaration or native proof shortcut occurs in the spike.
The mirror diff against `ef7c535` is empty.

The predecessor's 1,180 declarations became 1,240: 1,141 names remain,
39 obsolete or false intermediate contracts were removed, and 99 replacement
or additional contracts were added. The removed names are accounted for as follows:

- Twelve worker/scheduler erasure and evolution contracts: the old
  `encryptWorkerLogged`, `txWorkerLogged`, `decryptWorkerLogged`,
  `condReschedLogged`, `runDecryptAtLogged` and `runDecryptWorkerLogged`
  pairs. Their replacements use worker Step/Iter/Loop, activation iteration/run,
  activation dispatch, scheduling and nested rescheduling.
- Twenty-five environment contracts: the ordinary/spec pairs for
  `afterAdvance`, `afterXmit`, `encryptWorker`, `idleTimers`, `observe`,
  `runCryptWorkers_default`, `runCryptWorkers`, `runTimersPlaceholder`,
  `runTimers` and `txWorker`; the sameSnapshot/spec pairs for `queuedWork`
  and `runSendWorkers`; and `condResched_ordinary`. Receive-capable waits
  now use logged evolution contracts; false ordinary contracts are not retained.
- Two `dumpSize` snapshot/spec contracts, replaced by the actual stepped-dump
  chunk, start, receive and socket-helper contracts.

The unit command returned exit 0: 86 tests ran in 21.188 seconds, 85 passed
and one optional kernel-build test was skipped because `KERNEL/vmlinux` was
absent. The empty-report negative test deliberately prints JSON with status
`fail`; the suite itself reports `OK (skipped=1)`. No differential check or
guest was run. Earlier failed port builds were failures; their remaining goals
were repaired before the successful complete build.

Reproduce from this worktree:

```sh
capped -- scripts/in-bundle lake build
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation harness.test_trace harness.test_wg harness.test_linux
git diff ef7c535 -- Leanux ':!Leanux/Spikes'
```

Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There must be
no source admissions, new axioms, unsafe declarations or native proof shortcuts.
The mirror diff must be empty. No differential check or guest is part of this spike.
Reconstructible outputs are temporary; the source branch and conclusions remain.

## Conventions for cheaper future ports

The short second deliverable is [proof-friendly mirror conventions](2026-10-13-window-proof-conventions.md).
No recommended mirror change is implemented by this spike. The predecessor's
report and detailed effort history remain available at `ed069ba`.
