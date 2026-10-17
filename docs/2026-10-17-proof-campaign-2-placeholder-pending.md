# Campaign 2: accepted placeholder pending identity

At mirror b700659, the actual initialized runner accepts the two-operation
placeholderBoundaryTrace with placeholders=true and no supplied records.
Its final actual audit cut has pendingWork equal to the receive-worker
identity, while its handshake empty test/count/length are true/zero/zero,
decrypt/encrypt empty tests are true, tx/send/clear lists are empty,
and no peer is NAPI-scheduled. Suspended work is empty and NET_RX is not raised.

The theorem checks those exact tests. It does not infer general physical-ring
coherence, an unexecuted callback or a supplied-record progress failure.
The runtime branch trace includes a completed receive item, its cookie lookup
miss and the following empty poll. This is stale placeholder-mode bookkeeping.

The source distinction explains it: queueDeviceWork appends a worker identity
in either mode, but AmbientM.hidden clears that identity on section start only
in the supplied-record branch. The placeholder branch returns bytes first.
Consequently, the pending-identity/nonempty-queue comment in afterBatch must
be qualified by record mode when cited. The mirror is unchanged.

The trace retains the old two-operation backlog fixture, removes supplied
records, and steers the UDP port with four zero bytes. Its source lives in
Progress/PlaceholderBoundaryModel. The companion recordedBoundaryControl adds
the receive-worker section to the constructed records and runtime-accepts with
an empty pending list. It is not a Linux capture or a kernel-proved control.

PlaceholderBoundarySource uses kernel computation to check the actual
executeTraceWithBoundaries result. PlaceholderBoundaryClaims extracts the same
audit, final cut and Device and uses exact observer erasure to establish actual
executeTrace acceptance. The literal headline is
Progress.original_placeholder_pending_identity. Three theorems use only the
standard axioms; scoped build and fresh replay pass. The failed/warned drafts
and counts are recorded in the [campaign report](2026-10-14-proof-campaign-2.md).

Reproduce with capped/scripts/in-bundle lake build on
Leanux.Proofs.WG.Progress.Statements, print axioms for that headline, and run
lake env leanchecker --fresh on that module, using LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16 on the shared host. To reproduce the runtime control,
import PlaceholderBoundaryModel and evaluate executeTrace and
executeTraceWithBoundaries on CurrentBoundaryWitness.recordedBoundaryControl
with placeholders=false. The Boolean kernel check concerns only the placeholder
trace. No mirror change or upstream finding is requested.
