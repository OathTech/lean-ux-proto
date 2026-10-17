# R4: outer entries and complete batch accounts

This checkpoint follows d66cc2b8 over main b3f56807, whose executable mirror
is identical to state-split landing b700659. The proof tree, nondefault target
and gate remain on proofs/campaign. The mirror is unchanged. R1, R2, R3, R5,
R6 and ReplayWindow remain current. R4 chronology is refuted; initialized
pipeline conservation remains open.

Full batch now follows every actual receive/transmit item, including error
CQEs and the completion tail. Its source-only path selects one remaining ledger;
funding is derived separately. Structural base-list/table frames cover actual
Stack replies, crypt/TX workers, scheduler, deferred work and whole traffic calls.
They preserve the real source guards and copied-trial behavior.

The outer entry joins the funded account, optional physical ring, structural
and configured identity, nullable key slots and original owner journal. Fixture,
creation, configuration, guarded deletion, lifecycle and quiet controls supply
this entry. Inject returns its guard-derived empty entry; flood and batch retain
their actual residual ledgers. Full and stepped dump dispatches exchange their
funded cursor, including release. Original transmit dispatch retains acquired
TX/send holders through its socket, route, packetization and errno paths.
Namespace cleanup retains the device while clearing its carrier/socket/endpoint
state. Send, idle-timer, post-transmit and post-advance waits now return the exact
remaining ledger even from an absent device. Their outer record checks remain.
Normal state conclusions and owner-safe stopped journals stay distinct.

A concrete local witness shows that funded, stable RX storage and the physical
ring shape do not imply arbitrary-entry placeholder afterBatch emptiness. Its
worker queues are empty but NAPI is pending with a queued crypted packet; the
actual call returns with that packet still stored. This witness makes no
initialized-reachability or kernel claim. It justifies carrying residual ledgers
instead of assuming completion. No accepted loss/duplication counterexample is
claimed. The remaining proof connects actual syscall/runner occurrences and
each admitted packet to pending storage or its recorded disposition; stopped
transient carriers need their own phase account.

Fifteen modules add 218 support theorems and sixteen terminal exports:
810 → 825 proof files; 11,074 → 11,308 named theorems. All 259 earlier R4 terminal
bodies and every earlier support body remain unchanged. R4 has 275 terminal
theorems; the full surface has 809 declarations, including two definitions.
No existing theorem was retyped or deleted. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review covers all fifteen modules and sixteen exports. Forty-five
source checks comprise 26 ordinary failures and 19 clean passes; all three
isolated export checks pass. The first aggregate gate failed because two implicit
batch binders collided with an earlier opened function. Both now explicitly
bind List Env.BatchItem, and the repaired aggregate gate passes 883 build jobs
and all 809 declarations in 6.089 seconds. Failed development checks, recovery
terms and warnings were rejected. No proof warning remains; the sole aggregate
warning is the immutable mirror's String.mk deprecation. Fresh root replay passes in 112.708 seconds without warnings.
All heavy jobs were capped. No infrastructure rerun, cap increase, guest run,
main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
