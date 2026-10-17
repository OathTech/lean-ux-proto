# Campaign 2: count does not bound arbitrary receive-ring metadata

At mirror b700659, the former count-based cookie activation prediction is
false over arbitrary PtrRing metadata. This is a statement-domain finding,
not evidence that a malformed ring is reachable.

Progress.CookieActivationBoundFindings gives a size-one ring containing a
cookie packet with consumerTail equal to two. Its count is one; after one
consume the packet is still polled, and the second consume clears the ring.
The old pure resolver predicts one processed packet and successful completion
on a finite, correctly sized section-stop record. Actual Activation.run has
two turns, makes two productive iterations and returns the exact invariant
that the receive worker consumed more items than its queue held (1).

The proof composes the actual occupancy read and two actual cookie iterations,
with an empty index table and the original cookie classification. Other
Product fields and activation inputs remain arbitrary. It uses no compiled
evaluation or added axiom. The old whole-loop adequacy is still pending;
a coherent-ring theorem would require an explicit domain and separate proof.

Progress.CookieItemsFindings gives a separate size-two witness: producer one
and head zero expose one logical cookie item, but slot one also contains a
non-cookie packet. The actual first receive step consumes the cookie and
exposes that other packet. Thus initial classification over logical items
is not an invariant of physical consumption without further assumptions.
This also makes no reachability claim.

Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.Progress.CookieActivationBoundFindings and
Leanux.Proofs.WG.Progress.CookieItemsFindings, then
scripts/in-bundle lake env leanchecker --fresh
Leanux.Proofs.WG.Progress.CookieActivationBoundFindings.
Use capped on this host, 32 Lean threads and LEANUX_QEMU_SLOTS=16.
The scoped axiom audit and counts are in the
[retrofit report](2026-10-16-proof-campaign-2-state-split.md).
