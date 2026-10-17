# R4: scheduler and lifecycle accounts

This checkpoint follows aebd0f0a over main b3f56807, whose executable mirror
is identical to the state-split landing b700659. The branch retains the
nondefault LeanuxProofs target and gate. No mirror change is made.
R3 is complete; chronological GRO order is refuted, and initialized receive
conservation remains open.

Actual initiation and response consumers now return a separately charged
optional reference. Their failure paths pay the acquired reference. The
response session/keepalive continuation and shared final payment retain the
complete account, with configured identity, owner bounds and three-slot
compatibility explicit at session entry. This does not yet close the whole
handshake receive worker.

All five timer callbacks, actual timer dispatch and both timer modes retain
the account and physical receive ring. Nonreceive activations and dispatch
are concrete. Whole scheduling and all fourteen deferred constructors use
actual crypt/send/timer operations and their same committed removal suffix;
only the receive-worker preservation contract remains explicit. Stops retain
the actual observed journal; no post-failure World is asserted.

Structural base-list coherence holds initially and through actual creation.
Actual lookup derives the selected base occurrence and a distinct acquired
loan. Connected removal pays both through their respective source calls.
Allowed-IP insertion, replacement and refusal retain the complete account.
These are local contracts over supplied funding and entry invariants;
full lifecycle coherence, ingress propagation and initialized runner
composition remain open. R1, R2, R3, R5, R6 and replay-window status is unchanged.

Twelve modules add 209 support theorems and twelve terminal exports:
735 → 747 proof files and 10,069 → 10,290 named theorems. All previous theorem
bodies remain unchanged, including 194 R4 exports; R4 now has 206 terminals.
The total terminal surface has 740 declarations, including two definitions.
No existing theorem is retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.
The README and current declaration table now match the register.

Independent review passes all twelve support modules and twelve terminal
wrappers without findings. Sixty-five source checks comprise 40 ordinary
failures and 25 clean passes; two standalone export checks pass. Failed
elaborations, recovery axioms and warnings were rejected. Finite explicit
composition repaired timeout-prone proofs without raising limits. One
metadata-script NameError was corrected before that script launched a check.
All scoped builds pass. The first aggregate gate failed on missing namespace
qualifications in the appended exports; the corrected gate passes 805 build
jobs and all 740 terminal declarations in 5.309 seconds.
Fresh root kernel replay passes in 108.189 seconds without warnings.
The sole aggregate build warning remains the mirror-side String.mk deprecation.
All heavy jobs ran under the outer capped wrapper; no infrastructure rerun,
cap increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
