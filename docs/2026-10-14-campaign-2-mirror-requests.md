# Proof campaign 2 — requests to the mirror team

## 1. Reject a batch that leaves handshake receive work pending

Status: reproduced by model execution and proved by kernel reduction on main
`ca6b22e`. This is a mirror acceptance/progress finding, not a claim
about a captured Linux run or a kernel bug. No mirror change is made here.

H5 asks that an accepted operation leave no undispatched runnable unit.
`Env.afterBatch` checks the decrypt, encrypt, transmit and handshake-send queues
at `Leanux/Env.lean:883`, but omits the handshake receive queue. The ordinary
single-packet injection path includes that queue in its drain check at line 773.
The runner's end checks cover leftover records, suspended activations and a
raised NET_RX softirq; they do not reject this queued receive worker.

A two-operation trace from the ordinary initialized fixture reproduces it:

1. `wg_up`, with an all-zero UDP-port draw selecting 32768 and jiffies-end 100.
2. `wg_batch` containing one IPv4 injection to port 32768, wait 100 ms. Its
   bytes are `[3,0,0,0]` followed by 60 zero bytes: a correctly sized cookie
   message, queued before authentication. Supply NET_RX start, receive-worker
   queued, NET_RX stop and jiffies-end 101 records, with no receive dispatch.

The exact typed trace, records, runner call and original syscall-world replay
are in [`BatchBacklog.lean`](../Leanux/Proofs/WG/Progress/BatchBacklog.lean).
The two terminal declarations are in
[`Progress/Statements.lean`](../Leanux/Proofs/WG/Progress/Statements.lean).
Reproduce with `capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.Statements`;
both equations use `decide +kernel`, not compiled evaluation as a proof oracle.
The model evaluation reports `executeTrace accepted`; replaying the same two
syscalls from the same initial fixture leaves:

| Observation | Value |
| --- | --- |
| Handshake receive queue length | 1 |
| Its stored length counter | 1 |
| Pending workers | `[1]` (receive worker) |
| Remaining hidden records | `some []` |
| Suspended activations | 0 |
| NET_RX raised | false |

Request: make the batch completion guard account for the handshake receive
queue (and review whether its pending-worker identity should also be checked).
An incomplete recorded schedule should fail noisily, as the existing drain
checks intend. Please retain the ordinary successful dispatch path. The proof
campaign will carry the change and keep this trace as a regression witness for
the corrected refusal. The change is altitude-preserving: it belongs in the
environment's completion rule, not the WireGuard mirror.

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

The initialized-prefix equation has not been proved by kernel reduction:
JSON parsing first obstructed reduction; a typed trace removes that obstruction,
but the cryptographic arithmetic's `repeatM.impl` remains non-reducing. The
executable reproduction is explicitly separate from H5's kernel-checked batch
backlog witness and local scheduler contracts.

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
