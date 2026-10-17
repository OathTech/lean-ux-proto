# R4: lifecycle and worker holder accounts

This checkpoint follows a77d9ba8 over main b3f56807, whose executable mirror
is identical to the state-split landing b700659. The branch retains the
nondefault LeanuxProofs target and its gate. No mirror change is made.
R3 is complete; chronological GRO order is refuted, and initialized receive
conservation remains open.

The complete account now follows actual peer creation and bulk retirement,
including the saved ordered base occurrences through the two removal passes.
Single-peer removal states its required base-list uniqueness and membership;
these have not yet been derived from initialization. Full TX-step selection
finds the funded logical head in the supplied account, pays that occurrence
on DEAD/CRYPTED paths and retains actual freshness work. Empty and uncrypted
heads keep their source behavior. Native publication funds its own temporary
reference and repays it without changing the complete account.

Encryption retains the actual NAPI removal suffix and physical ring witness.
The TX activation iteration includes crypt-ahead, which may run encryption
and NAPI. Whole bounded dump calls and their three dispatcher arms retain
cursor funding through the original socket wrappers. Session setup derives
endpoint key facts from explicit entry configuration, ownership and slot
bounds. The zero-key timer charges only its actual newly queued clear work;
the new-handshake timer retains its real endpoint-reset cut and queue delta.

These are local contracts over a supplied complete account. Handshake
consumers, remaining timers, lifecycle coherence, outer scheduling/environment
and initialized runner composition remain open. Stops retain observed history;
no post-failure World or cleanup totality is asserted. R1, R2, R3, R5, R6
and replay-window status are unchanged.

Fifteen modules add 146 support theorems and twelve terminal exports:
720 → 735 proof files and 9,911 → 10,069 named theorems. All previous theorem
bodies remain unchanged, including 182 R4 exports; R4 now has 194 terminals.
The total terminal surface has 728 declarations, including two definitions.
No existing theorem is retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review passes all fifteen support modules and twelve terminal
wrappers without findings. Sixty-four source checks comprise 37 ordinary
failures and 27 clean passes; two standalone export checks pass. Failed
elaborations, recovery axioms and warnings were rejected. Finite explicit
composition repaired timeout-prone proofs without raising their limits.
All scoped builds pass. The aggregate proof gate passes 793 build jobs and
all 728 terminal declarations in 5.190 seconds.
Fresh root kernel replay passes in 110.672 seconds without warnings.
The sole aggregate build warning remains the mirror-side String.mk deprecation.
All heavy jobs ran under the outer capped wrapper; no infrastructure rerun,
cap increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
