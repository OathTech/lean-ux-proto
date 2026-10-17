# R4: observed receive and scheduler closure

This checkpoint follows 6e1304e9 over main b3f56807, whose executable mirror
is identical to state-split landing b700659. The nondefault proof target and
gate remain on the branch; the mirror is unchanged. Other result statuses
remain current. R4 chronology is refuted and initialized conservation is open.

The actual observed receive worker now joins native funding with owner checks,
physical ring preservation and three-slot compatibility on the same execution.
Its original incoming journal and safe stopped histories remain intact. This
discharges the stronger auxiliary scheduler's receive premise through activation,
dispatch, full schedule and nested rescheduling. The supplied combined entry
invariant remains explicit; this is not initialized runner closure.

Standalone configured identity survives actual releases, staged traffic and
every peer-command result, supplying the next command's entry fact. The device
peer loop now preserves the complete account and structural coherence, including
malformed/negative exits. Separate source cuts cover bulk removal and private-key
conflict payment before base retirement. Native shutdown preserves the account
and actual physical ring through timer/work drains, key clearing and sockets;
it does not claim crypt queues were drained.

Both fixture flags establish all local account/owner/slot/coherence facts, with
absent devices carrying no fabricated ring. A present initial fixture can run
one complete schedule without an input funding premise. Rebasing an account
uses precisely its actual removal suffix and retains the whole journal.
Whole device configuration/deletion, dynamic ingress and initialized conservation
remain open. No stopped execution is assigned a final World.

Ten modules add 112 support theorems and eight terminal exports:
773 → 783 proof files; 10,582 → 10,702 named theorems. All previous theorem
bodies remain unchanged; R4 grows from 228 to 236 terminals. The full surface
has 770 declarations, including two definitions. No theorem was retyped or
deleted. The split census remains 3,197 retyped/generalized, 1,709 deleted,
2,809 retained and 558 added.

Independent review covers all ten modules and eight exports with no findings.
Twenty-seven source checks comprise 15 ordinary failures and 12 clean passes;
the standalone eight-export check passes. The failures were local elaboration,
source factoring and namespace errors, including rejected recovery axioms;
no limit was raised. All scoped builds pass. The first aggregate gate passes
841 jobs and all 770 terminal declarations in 5.755 seconds. Fresh root replay
passes in 112.958 seconds without warnings. The sole aggregate warning is the immutable mirror's String.mk
deprecation. All heavy jobs were capped. No infrastructure rerun, cap increase,
guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
