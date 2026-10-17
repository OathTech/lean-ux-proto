# Campaign 2: the queued-handshake prediction is stale

The legacy `queuedDevice` prediction in
`Leanux/Proofs/WG/Config/QueuedHandshake.lean` is false over the current
mirror for an input within its resident-peer domain. This is a statement
artefact following the queue-record change in `1f0fbeb`; it predates the
state split. The mirror remains unchanged at `b700659`.

The checked witness is
`Config.QueuedFindings.pending_requeue_counterexample` in
`Leanux/Proofs/WG/Config/QueuedHandshakeFindings.lean`. It executes the
actual `sendQueuedHandshakeInitiation 0 false`, with:

- peer 0 resident, alive, already pending, reference count 2;
- `sendWorkQueue = [0]` and an expired last-send timestamp;
- record mode enabled, a supplied zero clock read and a following send-worker
  queue record for address 1;
- the corresponding send-worker unit/address mapping.

Every other Ambient field is arbitrary. The call returns normally, consumes
the supplied records, leaves reference count 3, and produces queue
`[0, 0]`. For every possible clock value, the old prediction leaves queue
`[0]`. Equality with the old predicted final Device is therefore impossible.

The original source cut tests only `handshakePending`. The landed source
tests that flag together with the result of `peekQueuedUnit`: a matching
queue record identifies a further queueing after the worker was taken.
Commit `1f0fbeb` also removed the old `queuedThisCall` write.
Both differences are visible directly in `Leanux/WG/Send.lean`; the
counterexample needs no hypothesis about how the state split was implemented.

The finding isolates the small original pure `queuedDevice` expression
because the old aggregate is not carried yet. Its body was checked against
the original modulo declaration name and whitespace. The operational
computation is the actual imported mirror, not a replacement. No
reachability from the runner fixture, captured-kernel execution, or kernel
bug is claimed.

The current correction carries all five original queued-send source contracts.
It retains the resident-peer domain and observes the actual peek result.
queuedDeviceAfterInspection includes that bit; the decorated suffix and full
call have exact erasure equalities to the actual source, including failures.
The clock contract witnesses the actual prefix, clock and suffix runs.
The old pure queuedDevice remains labelled historical for pending callers;
downstream staged-send/installation and terminal wrappers remain open.
The independent retained-reference contract peerGet_exact stays in
QueuedReferenceSource. The existing counterexample continues to refute the
old prediction.

Reproduce the checked witness with:

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle lake build Leanux.Proofs.WG.Config.QueuedHandshakeFindings
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Config.QueuedHandshakeFindings
~~~

The scoped trust checks and cumulative H1–H6 status are recorded in
[the retrofit report](2026-10-16-proof-campaign-2-state-split.md). Development
took two changed probes: record-update syntax and result normalization failed
first, then the kernel-checked witness passed without warnings. No cap or
proof limit was increased; no infrastructure retry or guest run occurred.


The timer retry carry checks a second witness on the original empty-queue
domain. TimerDiscipline.RetryQueueFindings.pending_empty_queue_counterexample
keeps a resident already-pending peer with reference count two, starts with
sendWorkQueue empty, and supplies the matching queue record/unit association.
Actual queuedAfterClock returns normally with queue [0]. The old
queuedAfterClock_empty conclusion is false: its nonempty arm requires the
entry peer's handshakePending to be false. The empty queue does not supply
that fact. This refutes the automatic retry eligibility inference, including
its downstream use to derive FreshRetryPeer, without changing the valid
conditional completion theorem that assumes FreshRetryPeer explicitly.

The witness leaves unrelated Ambient inputs arbitrary and asserts neither
reachability nor a kernel discrepancy. Reproduce with scripts/in-bundle lake
build Leanux.Proofs.WG.TimerDiscipline.RetryQueueFindings and fresh leanchecker
replay on that module under the capped settings above. The retrofit report
records its checked counts and the outstanding corrected retry composition.
