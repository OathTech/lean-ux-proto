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
evaluation or added axiom. The corrected CookieBoundedSource factors the exact bounded Product execution,
using the checked cookie leaf when applicable and actual receiveStep otherwise.
It retains zero-fuel, yield, rescheduling and exhaustion errors. This replaces
the two false count-only operational predictions; drain adequacy remains open.
A coherent-ring theorem would require an explicit domain and separate proof.

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

The later full-schedule witness in Progress.CookieScheduleFindings establishes
the actual scheduler failure on the same malformed size-one ring. It supplies
a singleton suspended receive activation and a correctly sized section-stop
record, with no yield records. Initial logical CookieOnly classification,
empty index table and the original yield-count bound all hold. Actual schedule
none propagates the receive occupancy-exhaustion invariant while probing the
candidate. Unrelated Product fields remain arbitrary. Thus the former
unconditional full-schedule completion claim is false on its stated domain,
not merely unsupported by the earlier activation theorem.

The corrected CookieScheduleOutcomeSource and CookieScheduleClaims retain that
domain and describe the actual bounded first turn, unchanged remaining scheduler
turns and original budget guard, including errors. They do not assert drain
adequacy, tail cookie classification, reachability or a kernel defect. Reproduce
the witness with scripts/in-bundle lake build
Leanux.Proofs.WG.Progress.CookieScheduleFindings and scripts/in-bundle lake env
leanchecker --fresh on that module; scoped validation is in the retrofit report.


CookieScheduleSupportFindings checks two additional consequences of the same
unrestricted domain. On the bad-tail ring, consuming once and then consuming
the successor's recomputed count differs from consuming the initial count.
Thus the former final-composition helper is false on physical ring state.
A separate size-three ring has a hole at its physical head but one logical
cookie item. With a valid yield/stop record stream, scheduleTurn probes a
receive activation that encounters the wrong hidden site and declines to
resume. It returns turnReturn, contradicting the old yield prediction
turnContinue. The exported finding negates the original projected total-return
contract; its concrete Product witness is local to the proof. No reachability
or coherence premise is inferred.

Reproduce both with scripts/in-bundle lake build
Leanux.Proofs.WG.Progress.CookieScheduleSupportFindings and fresh leanchecker
replay on that module, under the same capped settings above.
