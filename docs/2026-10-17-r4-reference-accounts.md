# R4: source-owned reference accounts

This checkpoint follows d2973f9b over main b3f56807, whose executable mirror
is identical to state-split landing b700659. The branch retains LeanuxProofs
and the proof gate. No mirror change is made. R3 is complete; chronological
GRO order is refuted, and initialized receive conservation remains open.

[AGENT 2026-10-17] Keep one proof-level durable-holder account aligned with
actual base-list entries, ordered send/clear work occurrences, logical TX
batches including cached heads, and the two active dump cursors. Charge all
of these and transient source loans together with RX carriers. This preserves
newly acquired references at callback boundaries without adding journal events
or inferring funding from queue membership or spare reference count.

Creation now adds its actual initial reference before list publication.
Make-dead retains every detached base occurrence, and bulk removal preserves
the saved ordered list after clearing the trie. The DEAD transmit step drops
one logical batch and pays one supplied owner, preserving other queues and
permitting final peer deletion. TX freshness keeps its actual queued-work
delta. Dump completion pays its supplied optional cursor; the literal
replacement acquires the new cursor before paying the old, including aliases.

Complete holder alignment and funding now survive actual receive completion
and Stack replies. Exact passive-field frames discharge the base-list,
clear-work and active-cursor obligations. The original poll's consume/GRO
cuts retain newly acquired holders alongside the selected carrier and unchanged
removal history. No phase is inferred from a stored packet alone; no post-Stop
World is assigned.

The full initialized result still needs this account through the whole poll,
NAPI/decrypt callbacks, admission, other workers, lifecycle drains and runner.
CRYPTED TX completion, whole dump serialization and outer socket accounting
remain separate work. The dump tail helper explicitly requires its post-walk
cursor alignment until serialization proves it. Local funded contracts are
not a claim that every arbitrary state is funded or that reference counts
have no surplus. R1, R2, R3, R5, R6 and replay-window status remain unchanged.

Thirteen modules add 143 support theorems and thirteen terminal exports:
690 → 703 proof files and 9,539 → 9,695 named theorems. All preceding theorem
bodies remain unchanged, including 156 R4 exports; R4 now has 169 terminals.
The total terminal surface is 703 declarations, including two definitions.
No existing theorem is retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review passes all thirteen terminal wrappers and the holder
funding/frame/callback modules. One comment overstated the consume helper’s
phase premise; it was corrected without changing the theorem.
Fifty-five source checks comprise 30 ordinary failures, three warning-bearing
intermediate results and 22 clean passes. The two export checks comprise one
parser failure and one clean pass. Failed elaborations, recovery axioms and
warnings were rejected; limits were unchanged. All scoped builds pass.
The complete proof gate passes 761 build jobs and all 703 terminal
declarations in 5.238 seconds.
Fresh root kernel replay passes in 109.546 seconds without warnings.
The sole aggregate build warning remains the mirror-side String.mk deprecation.
All heavy jobs ran under the outer capped wrapper; no infrastructure rerun,
cap increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
