# R3: checked scheduling and publication anchors

This checkpoint follows afb787ab over b3f56807, whose executable mirror is
identical to b700659. The mirror remains unchanged. Initialized R3 packet
authorization and R4 receive-pipeline conservation remain open.

The actual handshake worker, scheduler, crypt-ahead step, nested rescheduling
and all fourteen deferred cases now preserve the joint current-identity,
receiving-owner and allocation-journal checks. Timer dispatch and both wait
modes retain their original guards and stopped prefixes. Saved-peer scans
obtain their conditional allocation facts from the actual preceding getter.

[AGENT 2026-10-17] Audit-only subcalls carry owner bounds and existing captured
checks separately from allocation. This permits arbitrary saved scans without
inventing allocation validity; the full contracts join the conditional boundary
and current-identity proofs on the identical execution. The generic focused
invariant composes existing observers and keeps actual appended Stop prefixes.

A live crypted packet can now be anchored to one specified earlier decrypt
occurrence, its real successful publication and retained packet/peer identity.
The exact fixture establishes an empty anchor invariant. Actual prepare
preserves older anchors and installs the selected one; failed decryption
publishes DEAD. Actual normal consume, including nondelivery, freezes the
matching receipt, WG/Ambient endpoints and optional buffered origin.

That consume theorem still takes the enclosing caller's packet invariant.
Its separate incoming outer and nested journals are not silently identified.
Whole-call preservation, packet peer bounds across disappearance and fresh
creation, and the positional join to initialized routing history remain open.
This is a proof-closure gap, not an initialized counterexample.

Ten new modules add 131 support theorems and seven terminal exports add seven:
543 → 553 proof files and 7,704 → 7,842 theorems. All 204 earlier R3 terminal
bodies remain unchanged. R3 has 211 terminal theorems; the full terminal surface
has 587 declarations, including two definitions. No existing theorem is retyped
or deleted. The completed split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

Independent source reviews cover every new module and all seven exports.
The deferred store helper was replaced by the existing scheduler lemma after
review identified the duplicate proof. No contract changed.

Validation comprises 31 module checks: 18 ordinary failures, one warning-bearing
run rejected before its corrected clean run, and 12 clean passes. One additional
export check passes all seven named roots. Failures involved elaboration,
namespace/type inference and the unchanged heartbeat bound; the scheduler
repair selects the actual queue transformations before elaboration. No recovery
declaration or warning-bearing run supports a claim. Final named axiom checks
use only the standard three axioms. No infrastructure retry, memory-cap increase
or heartbeat increase occurs.

The complete proof gate passes 611 build jobs and 587 terminal declarations in
6.631 seconds. Fresh kernel replay passes in 107.325 seconds without warnings.
The sole build warning is the
unchanged mirror's String.mk deprecation. No guest run, mirror edit, main update
or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
