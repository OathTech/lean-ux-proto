# R4: device boundaries and dynamic ingress

This checkpoint follows 7365f387 over main b3f56807, whose executable mirror
is identical to state-split landing b700659. The proof target and gate remain
on the branch and the mirror is unchanged. R1, R2, R3, R5, R6 and ReplayWindow
remain current. R4 chronology is refuted; initialized conservation remains open.

The complete native device command now retains its supplied funded account,
base/table coherence, configured identity and all three nullable key slots.
The actual environment deletion derives an empty carrier ledger and inactive
dump cursors from its guards before destroying the device. External loans are
zero at that boundary; the normal absent-device errno case is included. These
contracts preserve actual deletion and refusal paths rather than assuming
reference positivity or a successful tail.

The original receive observer now selects a unique next ledger from the actual
native front/admission receipt. Its transition contains executions and the
source outcome, not a funded endpoint premise. The same run establishes funding,
physical ring refinement, owner checks and slots at a rebased journal cut. The
real NET_RX entry/body/exit carries that receipt through its original section
markers, including safe stopped journals. Crypt waits, send draining and the
post-transmit wrapper retain the combined invariant with concrete receive and
scheduler proofs. The normal completion guard derives an empty current ledger
and RX store from its actual decrypt-ring flag. Timer callbacks and dispatch
retain three-slot compatibility through their original recorded guards.

The complete inject/flood/batch callers, global lifecycle composition and
initialized conservation remain open. Configuration's physical-ring frame and
stronger timer-loop composition continue separately. No Stop is assigned a
final World, and local funding assumptions are not initialized reachability.

Twelve modules add 154 support theorems and eleven terminal exports:
783 → 795 proof files; 10,702 → 10,867 named theorems. All previous theorem
bodies remain unchanged. R4 grows from 236 to 247 terminal theorems; the full
surface has 781 declarations, including two definitions. No existing theorem
was retyped or deleted. The split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

Independent review covers all twelve modules and eleven exports. One export
comment incorrectly described prior removals as a new payment; it was corrected
to say that the section uses the already remaining ledger. Forty-four source
checks comprise 30 ordinary failures and 14 clean passes; the separate eleven-
export check passes. Failures were local elaboration/source factoring, namespace
and bounded proof-search errors, including rejected recovery axioms. No limit
was raised. All scoped builds pass. The first aggregate gate passes 853 jobs/all 781 declarations in 5.992 seconds; fresh root replay passes in 114.813 seconds. After the review comment correction, the final gate passes in 6.072 seconds. Final fresh replay passes in 112.728 seconds without warnings; the intervening edit changed only that comment.
The sole aggregate warning is the immutable mirror's String.mk deprecation.
All heavy jobs were capped. No infrastructure rerun, cap increase, guest run,
main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
