# Campaign 2: accepted supplied records retain an encrypt pending identity

Status: a new H5 runtime counterexample over main 783510e8. The actual
initialized runner accepts the constructed supplied-record execution, but
its last operation retains the encrypt-worker pending identity. The enumerated
worker queues drain. This refutes pending-identity emptiness;
it does not establish divergence, unfinished packet processing, a Linux capture
or a kernel defect. No mirror file is changed.

## Statement and classification

H5 asks for operation completion without pending units, unless a named stop
explains the remainder. Reading this as an empty pendingWork list is false
even with supplied records. Statement artefact is the first distinction:
a pending identity and useful unfinished packet work are different claims.
The witness settles the former only. It does not justify weakening the
charter silently to the latter.

This differs from the older placeholder result: supplied section starts do
clear the bit here. It also differs from the earlier queue-refill witness,
which stopped at an occupancy budget and omitted the completion suffix.
The new execution yields, resumes with a newly sampled bound, and succeeds.

## Exact execution and cause

The fixture reuses QueueRefill.concreteTrace: configure the existing corpus
peer, bring the device up, observe, receive its handshake response, then
batch an authenticated SYN with one transmit. The fifth operation's record
row keeps its first eleven records, then supplies the encrypt reschedule,
encrypt/decrypt stops and the remaining transmit/NET_RX/timer reads through
jiffiesEnd. The mode supplies records with placeholders disabled and uses
the existing legacy arm-record and destination-cache modes. No arbitrary
preloaded world or assumed invariant is supplied.

The committed activation journal contains eight receipts overall. During
the fifth operation:

1. Decrypt dispatch yields after one attempted iteration.
2. Encrypt dispatch starts with occupancy one, clearing its pending bit.
   Its actual NAPI callback requeues encrypt work and sets the bit again;
   the activation yields with one item still queued.
3. Encrypt resumption consumes that item and then empty-polls, completing
   in two attempts from occupancy one. Resumption has no new section start,
   so the pending identity remains.
4. Decrypt resumption empty-polls and completes.
5. Transmit dispatch drains both packets and completes.

The final operation returns 2. pendingWork is [2], the encrypt identity;
its supplied records and suspended activations are empty, NET_RX is clear,
all three ring counts and the handshake length are zero, transmit/send/clear
queues are empty, and no peer is NAPI-scheduled. Every peer's RX/TX lists are
also empty. These are the exact checked witness fields, not a general ring-coherence theorem or a claim that every
packet store, staged list or delivery obligation is empty.

A control adds a second encrypt section after its ring drains. The runner rejects
it at operation 4: the record at section-start site 44 remains where it
expects jiffiesEnd site 128. The empty-ring guard prevents dispatch from
consuming the pending unit's section.

Relevant current sources are AmbientM.hidden in Kernel/Defs.lean:2102
(section-start clearing), queueDeviceWork at :2219 (requeue bookkeeping),
Env/Batch.lean:264 (empty-ring dispatch rejection), :329 (resumption),
Env.lean:988 (batch queue checks), and Runner.lean:1185 (final record,
suspension and NET_RX guards). Data.encryptRingPoll runs its native NAPI
callback after consuming the first ring item. These locations explain the
model execution; no correspondence conclusion about the C is claimed here.

## Reproduction and request

The fail-noisy executable reproducer is
[Progress/RecordedPending.lean](../Leanux/Proofs/WG/Progress/RecordedPending.lean).
It checks the actual runner, its exact existing boundary inspection,
committed receipts and the rejected empty-dispatch control. The initialized
counterexample is runtime evidence, not a kernel-reduction theorem. Existing
observer-erasure/source-provenance theorems remain separate from evaluating
this concrete trace.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean Leanux/Proofs/WG/Progress/RecordedPending.lean
```

The reproducer reports success only if its boundary, eight committed receipts
and exact rejected control all match; otherwise it throws an error. Construction
used twelve capped stock-limit probes: four rejected candidate record suffixes,
three elaboration failures and five successful diagnostics, including the final
complete source. No unchanged retry, limit increase or KILLED outcome occurred.
Independent review checked supplied-mode initialization, observer erasure,
committed-versus-trial separation and the dispatch guard. It corrected an
initial overstatement about all packet work to the exact enumerated queue tests;
the primary pending-identity counterexample is unchanged. Final integrated
build/gate/replay results are in the campaign report.

Mirror-team request: reconcile the pending-work identity lifecycle with
nested requeue, activation resumption and empty-ring dispatch. Determine
which complete supplied streams the environment should accept and how an
empty but queued unit is represented. Preserve the source distinction between
resuming an activation and starting a new work unit. Differential validation
belongs to that follow-up; clearing a bit solely to make this claim close is
not justified by this proof campaign.

[AGENT 2026-10-19] Record the accepted supplied-record pending identity as a
new H5 finding, retain the narrower useful-work boundary explicitly, and
stop the campaign after committing already closed proofs and this record.
