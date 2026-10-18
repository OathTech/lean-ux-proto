# R4: auxiliary state and peer configuration

This checkpoint follows 0db1407b over main b3f56807, whose executable mirror
is identical to the state-split landing b700659. The nondefault proof target
and gate remain on the branch. The mirror is unchanged. R3 is complete;
chronological GRO order is refuted and initialized R4 conservation remains open.

The existing owner journal supplies configured identity, receiving-owner
bounds and packet freshness. A conjunction adds the complete funded account,
physical ring and three-slot compatibility on the same actual observation.
Session setup now preserves that conjunction. Both handshake consumers carry
their optional acquired loan and auxiliary entry facts to the same native
endpoint. Slot compatibility also follows the concrete Stack callback,
poll/NAPI and decrypt/encrypt observers. These proofs permit peer/key deletion;
they do not assert that every slot survives.

Actual single/bulk removal preserves structural base-list/public-key-table
coherence, including saved-list drains and deleting puts. The whole acquired
peer configuration tail pays its caller loan on early malformed/negative
allowed-IP returns and on exhaustion after real keepalive/staged work. The
full update and its connected lookup preserve funding through both ordinary
updates and removal; lookup supplies the selected base occurrence. Structural
coherence independently follows all update paths, without funding assumptions.

Full receive-worker composition, stronger scheduler composition, complete
public configuration/device lifecycle and dynamic ingress/runner accounting
remain open. The older scheduler's weak-domain receive premise is not discharged
by a theorem requiring stronger entry facts. Stops retain their real observed
histories and have no invented final World. Other result statuses are unchanged.

Eleven modules add 137 support theorems and nine terminal exports:
747 → 758 proof files and 10,290 → 10,436 named theorems. All previous theorem
bodies remain unchanged, including 206 R4 exports; R4 now has 215 terminals.
The full terminal surface has 749 declarations, including two definitions.
No existing theorem is retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review covers all eleven modules and nine exports. Two documentation
findings about slot survival were corrected to state compatibility preservation;
the reviewer verified the corrections. No review finding remains open.
Thirty-two source checks comprise 19 ordinary failures and 13 clean passes;
one standalone nine-export check passes. Failed elaborations, recovery axioms
and warnings were rejected. Large proofs were split at actual source cuts
without increasing limits. All scoped builds pass. The first aggregate gate
passes 816 jobs and all 749 terminal declarations in 5.421 seconds.
Fresh root kernel replay passes in 107.381 seconds with no warnings.
The sole aggregate warning remains the mirror-side String.mk deprecation.
All heavy work used the outer capped wrapper. No infrastructure rerun, cap
increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
