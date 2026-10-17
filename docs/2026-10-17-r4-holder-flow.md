# R4: complete holder accounts through receive and work flow

This checkpoint follows 95abd7cb over main b3f56807, whose executable mirror
is identical to state-split landing b700659. The branch retains LeanuxProofs
and its gate. No mirror change is made. R3 is complete; chronological GRO
order is refuted, and initialized receive conservation remains open.

The complete account now survives actual admission, whole poll, NAPI and
decrypt iteration. It charges base-list, ordered send/clear work, logical TX
batches and active dump cursors together with receive carriers and transient
source loans. Poll and decrypt retain their exact observed removal suffixes;
admission supplies the actual enqueue/finish receipt. The decrypt publication
loan is an additional charged occurrence and may name an owner held elsewhere.

Actual send/clear dispatch selects and pays its ordered holder occurrence.
Bounded work drains retain the unconsumed ordered work sublists; timer stopping
retains base, TX, cursor and caller loans through its real conditional drain.
The contracts preserve recorded selection, early return and failure arms;
they do not claim that every bounded drain empties its queues.

Dump serialization now proves its own cursor alignment. The actual socket
start/receive paths exchange old and new cursor charges, including aliases,
with callback-running state selecting the active holder. The encrypted TX
completion retains its actual freshness work delta, drops one selected logical
batch and pays its supplied batch owner, allowing final peer deletion.

Whole initialized conservation still needs complete lifecycle retirement,
durable TX holder selection and replacement, remaining dump and environment
callers, and runner integration. Local supplied funding, physical-ring and
freshness premises are explicit; none establishes initialized reachability.
No post-failure World is assigned. R1, R2, R3, R5, R6 and replay-window status
remain unchanged.

Seventeen modules add 203 support theorems and thirteen terminal exports:
703 → 720 proof files and 9,695 → 9,911 named theorems. All preceding theorem
bodies remain unchanged, including 169 R4 exports; R4 now has 182 terminals.
The total terminal surface has 716 declarations, including two definitions.
No existing theorem is retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review passes all new support modules and thirteen terminal
wrappers. A decrypt comment incorrectly suggested distinct owner identities;
it now distinguishes charged occurrences without changing the theorem.
A stale temporary TX handoff/manifest was also corrected before publication.
Eighty source checks comprise 52 ordinary failures, one warning-bearing
intermediate result and 27 clean passes. The standalone export check passes.
Failed elaborations, recovery axioms and warnings were rejected; limits were
unchanged. All scoped builds pass. The first aggregate gate fails in 3.407
seconds on export-context name ambiguity. Fully qualifying the decrypt
Physical and Journal names repairs the integration without changing contracts.
The repaired proof gate passes 778 build jobs and all 716 terminal
declarations in 4.955 seconds.
Fresh root kernel replay passes in 106.857 seconds without warnings.
The sole aggregate build warning remains the mirror-side String.mk deprecation.
All heavy jobs ran under the outer capped wrapper; no infrastructure rerun,
cap increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
