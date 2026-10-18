# R4: native receivers and source composition

This checkpoint follows f7153a13 over main b3f56807, whose executable mirror
is identical to the state-split landing b700659. The nondefault proof target
and gate remain on the branch. The mirror is unchanged. R1, R2, R3, R5, R6
and ReplayWindow retain their current statuses; R4 chronology is refuted and
initialized receive-pipeline conservation remains open.

The complete native handshake receiver now preserves the supplied funded
account. The proof follows actual MAC decisions, both Noise branches, cookie
replies, missing-peer returns, session setup, timers and final reference
payments. The whole peer command connects lookup or creation to the actual
update, early error and removal paths, paying separate base and caller
occurrences. Device creation preserves existing accounts on refusal and
establishes the empty account and physical ring on successful fresh creation.

Independent admission outcomes select a unique next carrier ledger for the
actual source execution. The original observer retains its incoming journal
and records the actual fresh receipt occurrence. Finite paths compose actual
admission and poll runs with a shared World and history, deriving funding from
supplied entry accounts. This does not connect the global ingress caller or
initialize its ledger. Transmit slot compatibility and the auxiliary scheduler
also compose; the latter still exposes its stronger receive-worker premise.

Observed receive-worker composition, whole device configuration/lifecycle and
dynamic ingress/initialized conservation remain open. Native handshake funding
alone does not establish all auxiliary endpoint facts. Stops retain their
actual histories; these normal-return accounts do not invent a final World or
assert totality.

Fifteen modules add 133 support theorems and thirteen terminal exports:
758 → 773 proof files and 10,436 → 10,582 named theorems. All previous theorem
bodies remain unchanged, including 215 R4 exports; R4 now has 228 terminals.
The full terminal surface has 762 declarations, including two definitions.
No existing theorem is retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review covers all fifteen modules and thirteen exports. Two
adjacent module comments were corrected from slot survival to compatibility.
A handshake comment now distinguishes an early missing-peer return from an
actual Stop. The complete arm theorem follows the real conditional payment;
no review finding remains open.

Fifty-six source checks comprise 33 ordinary failures and 23 clean passes;
five standalone export checks pass. The failures include two exit-zero checks
rejected for warnings, failed elaborations and recovery axioms. No rejected
candidate was published. Finite source factors resolved the proof failures
without raising limits. All scoped builds pass. The first aggregate gate
passes 831 jobs and all 762 terminal declarations in 21.831 seconds.
Fresh root kernel replay passes in 113.136 seconds without warnings. The sole aggregate warning remains the
mirror-side String.mk deprecation. All heavy work used the outer capped wrapper.
No infrastructure rerun, cap increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
