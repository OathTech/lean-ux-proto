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
