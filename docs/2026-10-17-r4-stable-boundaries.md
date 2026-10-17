# R4: stable receive boundaries and source-owned reservations

This checkpoint follows ec1fe31e over b3f56807, whose executable mirror is
identical to state-split landing b700659. The mirror is unchanged. R3 remains
complete. R4's chronological GRO-order counterexample remains valid; whole
initialized receive-pipeline conservation remains open.

The actual fixture establishes empty receive carriers, stable queue heads and
the initialized physical decrypt ring. The actual idle/completion guards imply
empty receive inventory when supplied the stable boundary and physical ring
refinement. The completion guard additionally requires its caller's actual
decrypt-ring flag. No device-deletion endpoint substitutes for that drain fact.

Native decrypt preparation selects the packet from the actual physical ring
history. Its carrier stays funded while temporarily outside the ring; dead or
crypted publication restores the full stable boundary. Publication retains
its actual acquired peer reservation for the later IRQ and payment. This
checkpoint does not compose that callback or the full decrypt iteration.

An explicit source-owned reservation discharges one actual peer release,
including final deletion. The clear timer either repays its coalesced get or
appends the matching work item and retains that exact epoch/slot/stamp loan.
The queued clear worker consumes the supplied reservation after its original
handshake/key clearing. Existing queued work is not funded merely by membership.
These contracts retain native WG and Ambient endpoints and the original Stops.

Poll readiness supplies the actual packet-state fact needed to remove a carrier
from the uncrypted-ring ledger. Completion requires the actual stopped-head
fact. Separate surviving-peer NAPI-bit contracts compose with the existing
queue, packet and ring frames through consumeDataDone and the concrete product
Stack callback, including reply traffic and peer deletion. Full poll-loop stable
preservation and its initialized callers remain subsequent obligations.

[AGENT 2026-10-17] Carry bounded nullable references for all three peer key slots,
separately from RX funding and configured identity. Current-slot compatibility
alone is not preserved by fresh allocation: a checked local state names the
next unallocated slot, and allocating it for another owner breaks compatibility.
That counterexample refutes an insufficient local invariant, not initialized
mirror behavior. Actual session and responder rotation preserve the smaller
three-slot invariant; session obtains its compatible handshake word from the
existing configured-identity invariant. No full affiliation, non-NULL key,
resident-owner or successful-session premise is introduced.

The remaining initialized conservation proof must connect admission/disposition
receipts, full poll/IRQ transitions, lifecycle drains and all source-owned
base/work/TX/dump/transient reservations through the original runner. Initial
facts and local contracts here do not assert that closure. R1, R2, R3, R5, R6
and the replay-window result retain their existing statuses.

Twelve new modules add 160 support theorems and twelve terminal exports:
662 → 674 proof files and 9,159 → 9,331 named theorems. All 131 preceding R4
terminal bodies and every other existing theorem are unchanged. R4 now has
143 terminal theorems; the full terminal surface has 677 declarations,
including two definitions. This extension retypes or deletes no existing
theorem. The split census remains 3,197 retyped/generalized, 1,709 deleted,
2,809 retained and 558 added.

Independent reviews cover every new module and its terminal contracts. One
duplicate permutation lemma was removed in favor of the existing checked
lemma. Seventy-eight module checks comprise 51 ordinary failures, 24 clean
passes and three rejected warning-bearing exit-zero runs. Three export checks
comprise one namespace-resolution failure and two clean passes. A malformed
checker-path invocation failed before starting Lean. Development failures were
syntax, proof composition and normalization at unchanged limits; recovery
terms were rejected. Scoped builds pass. The aggregate gate passes 732 build
jobs and all 677 terminal declarations in 4.483 seconds. Fresh root kernel
replay passes in 104.224 seconds with no warnings. The only build warning is the unchanged mirror-side
String.mk deprecation. There is no infrastructure retry, cap or heartbeat
increase, guest run, mirror edit, main update or push.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
