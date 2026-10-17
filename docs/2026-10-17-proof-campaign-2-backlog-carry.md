# Campaign 2: historical backlog fixture now rejects

The constructed trace from the historical H5 finding is rejected by the actual
runner at mirror b700659. Progress.BatchBacklogAcceptance.pendingTrace_rejected
proves executeTrace returns operation index 1 with Stop.outsideDomain at
drivers/net/wireguard/queueing.h:128: work remains pending beyond the batch's
guest wait. The completion guard landed after the historical de62c9d result.
This is a corrected statement following a mirror fix, not a new discrepancy.

The trace itself is unchanged: wgUp followed by a batch containing the original
cookie-shaped input and its supplied receive-worker records. BatchBacklogModel
holds that fixture. The proof executes the imported runner with its actual
initialization, FIB boot and operation boundaries. A kernel-checked projection
identifies the precise failure; ordinary case analysis recovers equality of the
complete Except result. No compiled evaluation is used as proof.

The legacy runTwo/backlog construction is separately carried: it omits the
current runner's FIB boot and rejects at the route/source invariant, returning
no backlog. That direct fixture result is distinct from the actual runner
rejection above. General runner-boundary acceptance and historical backlog
wrappers remain lagging; the old accepted finding remains historical.
No captured Linux run or general progress property is claimed.

Reproduce with:

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle lake build Leanux.Proofs.WG.Progress.BatchBacklogAcceptance
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Progress.BatchBacklogAcceptance
~~~

The scoped axiom audit, replay and cumulative H1–H6 counts are recorded in
[the retrofit report](2026-10-16-proof-campaign-2-state-split.md).
