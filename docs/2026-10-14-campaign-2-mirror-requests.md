# Proof campaign 2 — requests to the mirror team

## 1. Reject a batch that leaves handshake receive work pending

Status: **addressed on main** by `9db558b`, included in representation batch
`cb2348e`. The corrected-refusal carry is now kernel-checked over the split
mirror `b700659`: the actual runner and its observation both reject the trace
at operation index 1 with the original named outside-domain reason.
The accepted-backlog evidence below is historical, pinned to `ca6b22e` and
the later `de62c9d` campaign baseline. It is not a current acceptance claim.
This was a mirror acceptance/progress finding, not a captured Linux run or
kernel bug. No mirror change is made here.

On the affected revision, H5's completion requirement exposed an omitted
handshake receive-queue check in Env.afterBatch. Other queues were checked,
and the ordinary single-packet injection path already included handshake
receive work. The runner's trailing-record, suspended-activation and NET_RX
checks did not detect that old queued receive worker. The guard correction
now rejects the concrete trace.

The historical two-operation trace from the initialized fixture was:

1. `wg_up`, with an all-zero UDP-port draw selecting 32768 and jiffies-end 100.
2. `wg_batch` containing one IPv4 injection to port 32768, wait 100 ms. Its
   bytes were `[3,0,0,0]` followed by 60 zero bytes: a correctly sized cookie
   message, queued before authentication. Supplied records were NET_RX start,
   receive-worker queued, NET_RX stop and jiffies-end 101, with no dispatch.

The current typed trace is in
[BatchBacklogModel.lean](../Leanux/Proofs/WG/Progress/BatchBacklogModel.lean).
[BatchBacklogAcceptance.lean](../Leanux/Proofs/WG/Progress/BatchBacklogAcceptance.lean)
checks false acceptance and the exact rejection details using kernel reduction,
then derives the full runner equation. RunnerBoundaryClaims carries that refusal
to the actual audit. Reproduce the current refusal with
`capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.Statements`.
The old direct syscall fixture also has no current backlog result; it omits
the split runner's actual FIB initialization.

The historical accepted replay on the affected revisions left:

| Observation | Value |
| --- | --- |
| Handshake receive queue length | 1 |
| Its stored length counter | 1 |
| Pending workers | `[1]` (receive worker) |
| Remaining hidden records | `some []` |
| Suspended activations | 0 |
| NET_RX raised | false |

Resolved request: account for handshake receive work at batch completion and
retain the ordinary successful dispatch path. The proof tree now retains the
trace as a checked regression for the corrected refusal. The original change
is altitude-preserving: it belongs in the environment's completion rule.
The optional pending-worker identity review was not a second established
defect and is not reported as a new request.

[AGENT 2026-10-14] Request the environment guard correction rather than weaken
H5's completion claim. The source review identified the omitted queue, and
execution of the concrete runner trace reproduced acceptance and the backlog.
No guest run or differential validation was performed by this campaign; the
records here are constructed to test the mirror's accepted domain.

A separate critical read-only review found no material defect in the witness
or this request. It verified the replay/runner correspondence, parser bounds,
and that the handshake queue is runnable according to `Activation.hasWork`.
The optional pending-identity review above is not a second established defect.

## 2. Account for nested queue refill in activation budgets

Current disposition (2026-10-20): fixed on main `3f3879e0`, with the shared
proof carry at `3308c49a`; both are incorporated in this branch. The evidence
below describes the earlier mirror. Current regression checks retain the
corrected budget, completion and cancellation outcomes.

Status: reproduced by executable model evaluation on `ca6b22e`, independently
reviewed against the mirror and pristine C. This is an environment-bound
finding. It is **not** an accepted-run nontermination counterexample, a captured
Linux schedule, or a kernel finding. The mirror is unchanged.

`Activation.run` (`Leanux/Env/Batch.lean:234`) takes initial queue occupancy plus
one as its iteration budget. Its stated premise is that a worker's queue cannot
refill during that activation. The encrypt path violates that premise:

1. Initial encrypt occupancy is one.
2. `encryptStep` runs `napiSoftirq` before its queue consume
   (`Leanux/WG/Data.lean:108`).
3. NAPI delivers the ordinary authenticated SYN from `w6_rst_syn`.
   `Stack.receive4` calls `reply4`, which calls `wgXmit`
   (`Leanux/Env/Stack.lean:91–98,142`), appending the reply's encrypt item.
4. Two productive iterations process the original item and the reply. The
   required third, empty poll is forbidden by the budget of two.

The original runner reports at operation 4:

```
wg_packet_encrypt_worker consumed more items than its queue held (1) in one run
```

[`Progress/QueueRefill.lean`](../Leanux/Proofs/WG/Progress/QueueRefill.lean)
contains the typed trace and every record. Reproduce with:

```
capped -- scripts/in-bundle lake env lean Leanux/Proofs/WG/Progress/QueueRefill.lean
```

Its executable check reports reproduction or throws an explicit error. The
trace starts from the ordinary fixture, configures the existing corpus peer,
completes the handshake, then batches that corpus SYN with one transmit. The
first four operations succeed. The last record row reaches the encrypt-budget
invariant and ends at encrypt stop; it omits the later operation-completion
suffix. Thus this is evidence about an initialized execution prefix and an
incorrect budget premise, not proof of a complete capturable schedule being
rejected. Legacy arm records and zero dispatch identities are supported model
paths. No arbitrary preloaded World is used.

The initialized-prefix equation has not been proved by kernel reduction.
Historically JSON parsing obstructed reduction; the typed trace removed that
obstruction, leaving the arithmetic's private repeatM implementation.
Progress.PowEvaluationSource and CurveEvaluationSource now provide exact
finite-evaluation bridges around that arithmetic obstruction. They have not
been composed into this initialized prefix, and further reduction or source
composition can still be necessary. The executable reproduction remains
separate from H5's kernel-checked boundary witnesses and local scheduler
contracts.

Statement-artifact check: the concern is the mirror's own “nothing refills”
premise, not an extra protocol assumption. The nested callback is already in
its modeled execution. Pristine `send.c:293–308` drains until empty;
`include/linux/ptr_ring.h:365–369` permits bottom-half work at consume's unlock.
An independent read-only review confirmed that path and found no relevant
model-domain exclusion. Differential validation remains the mirror team's task.

Request: derive an activation bound that accounts for items queued by callbacks
during the activation, while preserving dispatch, resumption and record checks.
A larger arbitrary constant would not establish the bound. This is an
altitude-preserving environment correction. Review the other worker budgets for
the same premise; they are not additional established findings here.

[AGENT 2026-10-14] Report the erroneous occupancy premise with its evaluated
initialized prefix, keeping the full-run acceptance and kernel-proof boundaries
explicit rather than counting it as a proved termination counterexample.

## 3. Restore pre-nest tailroom when cancelling the device peers nest

Current disposition (2026-10-20): fixed on main `3f3879e0`, with the shared
proof carry at `3308c49a`; both are incorporated in this branch. The evidence
below describes the earlier mirror. Current regression checks retain the
corrected budget, completion and cancellation outcomes.

Status: source correspondence error over `ca6b22e`, with a kernel-checked
reachable model witness and two independent read-only source reviews. No
externally compared output difference is established, and this is not a kernel
finding. The mirror is unchanged.

`Leanux/WG/NetlinkDump.lean:220–232` reserves the four-byte peers-nest header,
then saves `nestStart`. The empty-peer-list or dead-cursor arm restores that
post-reservation snapshot, retaining a four-byte debit even though its output
omits the nest. In pristine C, `drivers/net/wireguard/netlink.c:254,264–268`
starts and cancels the nest. `include/net/netlink.h:1925–1934` saves the tail
pointer **before** `nla_put`; `nla_nest_cancel` at lines 1975–1978 calls
`nlmsg_trim` with that pointer, removing the header too. The design's section
4.3 in `docs/2026-10-06-w1-w2-netlink.md` also says cancellation restores saved
pre-nest room. The correspondence audit's cancellation row missed the timing
of the saved snapshot.

[`Config/DumpCancellation.lean`](../Leanux/Proofs/WG/Config/DumpCancellation.lean)
contains the typed one-operation trace, ordinary initialized fixture and
callback witness. Reproduce its kernel-checked equations with:

```
capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Config.DumpCancellation
```

The trace is one `wg_get` on the fixture's empty `wg0`, with an empty hidden
record list. `executeTrace` accepts it. The callback returns zero, one data
message and a cleared cursor, with `skb.room = 3720`. The retained message
occupies 52 bytes: 20 for the generic-netlink header, three eight-byte scalar
attributes and eight bytes for the `"wg0"` name. C cancellation therefore leaves
`3776 - 52 = 3724`. The Lean arithmetic witness verifies the four-byte gap;
the C correspondence argument is the source inspection above, not a formal C
simulation theorem.

Scope: callback byte accounting is internal state. Observations omit message
lengths, and the supported empty/dead-cursor exits complete with ample room for
DONE in a fresh chunk. Thus the accepted trace is a reachable accounting
witness, **not** an accepted trace whose compared JSON or branch observations
diverge from Linux. No guest or differential check was run here. The concrete
checked case is the empty-list arm; the shared cancellation line also identifies
the dead-cursor arm by inspection.

Request: preserve the skb snapshot before the peers-nest reservation and restore
that snapshot on cancellation. This is altitude-preserving: it corrects the
existing tailroom abstraction and follows the C's allocation/cancellation order.
Check the other nest snapshots while making this repair; no additional mismatch
is asserted here. Mirror-team validation remains separate from the proof tree.

[AGENT 2026-10-15] Report the four-byte correspondence error with its accepted
fixture and exact callback equation, retaining the internal-only observability
limit instead of claiming an output or kernel defect.

## 4. Reconcile supplied-record pending identities after nested requeue

Current disposition (2026-10-20): fixed on main `3f3879e0`, with the shared
proof carry at `3308c49a`; both are incorporated in this branch. The evidence
below describes the earlier mirror. Current regression checks retain the
corrected budget, completion and cancellation outcomes.

Status: new accepted initialized runtime counterexample over main 783510e8;
[full report and reproducer](2026-10-19-proof-campaign-2-supplied-pending.md).
The fifth operation accepts with the encrypt pending identity still present,
although the enumerated worker queues, RX/TX lists, NAPI scheduling, suspended
activations and supplied records are empty. A nested native NAPI callback
requeues encrypt work; resuming the original activation drains the new item
without a new section start. An added empty encrypt dispatch is refused by
the empty-ring guard. This is a distinct supplied-record execution, beyond
the older placeholder-only witness and the rejected occupancy-bound prefix.

Request: reconcile device pending-work identities, resumed activations and
empty-ring dispatch, then determine the correct complete-stream acceptance
rule. Preserve the distinction between an existing activation's resumption
and a newly queued work unit. This evidence does not justify simply clearing
a bit, does not prove unfinished packet work or nontermination, and does not
claim correspondence with an actual Linux capture. It uses supported legacy
arm-record mode with supplied records and placeholders disabled. No mirror
change is made by the proof campaign; differential validation belongs to the
mirror follow-up. The counterexample is executable evidence, not a new
kernel-reduction theorem. H5's literal pending-identity emptiness remains
refuted pending disposition; the global termination obligation stays open.


## 5. Account for retained namespace-pin aliases at cleanup

Status: new accepted initialized placeholder counterexample, independently
reviewed for fixture-domain validity. The foreign fixture permits `dup(9)`,
then its single `wg_netns_close`, then `close(ref 0)`. The original runner and
exact boundary observer accept with pending worker 12 (`netnsCleanup`) after
the final close. The default descriptor limit is 32.

[Finding and executable recipe](2026-10-20-proof-campaign-2-namespace-pin.md).
The fixed-holder cleanup assumes the pin's last reference is gone; a retained
alias violates that assumption without violating either parser's stated domain.
The operation-end pending guard is restricted to supplied-record mode.

Request: determine and enforce the actual fixture domain or account for cleanup
at the last pin release, preserving the real scheduling behavior. This is an
altitude-preserving environment request, not a kernel claim. The proof campaign
makes no mirror change and continues the independent termination and service
claims. The unrestricted placeholder pending-emptiness statement remains refuted.
