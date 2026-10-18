# R4: complete traffic calls and lifecycle entries

This checkpoint follows 4e71927e over main b3f56807, whose executable mirror
is identical to state-split landing b700659. The proof tree, nondefault target
and gate remain on the branch. The mirror is unchanged. R1, R2, R3, R5, R6 and
ReplayWindow remain current. R4 chronology is refuted; initialized conservation
remains open.

Whole inject now selects its admission ledger from the original receive
execution, then derives an empty RX account and store from the actual completion
guard after the crypt wait. Whole flood follows each occurrence in its finite
message list through the real route, fixture send, receive and inline poll. Its
source-only transition path and final removal suffix select a unique remaining
ledger, whose funding is proved separately. Equal messages remain distinct
occurrences. The native caller and unchanged observer have the same execution.
Original stopped journals remain owner-safe; no stopped World is invented.

The complete deferred family, including both timer modes and the saved peer
getter, retains the stronger account, physical ring, owner journal and nullable
key slots. Actual afterBatch and inline poll use concrete callbacks. Recorded
completion derives an empty ledger/store from its real final flags. Placeholder
completion is not asserted: the conservation contract permits a residual ledger.
Actual transmit absorbs its source-created TX/send holders into the same account.

Native configuration retains physical ring refinement. Create, stop/down and
open/up retain all local entry components, including structural/configured
identity and slots. Fresh creation establishes these from its guarded endpoint;
shutdown and socket errors retain their actual paths. Narrow base-list/table
frames now cover ingress, decryption, receive completion, session construction,
handshake receiving and all five timer callbacks. These supplied-entry contracts
are not initialized runner closure. Full batch, global lifecycle composition and
initialized conservation remain open.

Fifteen modules add 195 support theorems and twelve terminal exports:
795 → 810 proof files; 10,867 → 11,074 named theorems. All 247 previous R4
terminal bodies and every earlier support body remain unchanged. R4 now has
259 terminal theorems; the complete surface has 793 declarations, including two
definitions. No existing theorem was retyped or deleted. The split census remains
3,197 retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review covers all fifteen modules and twelve exports. One export
comment overstated state retention on Stop; it now distinguishes normal state
invariants from stopped-journal safety. Forty-seven
source checks comprise 30 ordinary failures and 17 clean passes; the two export
checks both pass. Failures were elaboration, source factoring and bounded proof
search errors, including rejected recovery axioms and warnings. One flood check
returned zero with unused-simp warnings and is counted as a failure. The repaired
sources have standard axioms only and no warnings. No limit was raised. All
scoped builds pass. The aggregate gate passes 868 build jobs and all 793 declarations in
6.066 seconds. Fresh root kernel replay passes in 115.435 seconds without warnings.
The sole aggregate warning is the immutable mirror's String.mk deprecation.
All heavy jobs were capped. No infrastructure rerun, cap increase, guest run,
main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
