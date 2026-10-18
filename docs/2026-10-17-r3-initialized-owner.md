# R3: initialized owner checks and retained packet publication

This checkpoint follows 5c5bfebc over b3f56807, whose executable mirror is
identical to b700659. The mirror remains unchanged. Initialized R3 packet
authorization and R4 receive-pipeline conservation remain open.

Every concrete traffic/control, dump and syscall arm now preserves the joint
current-identity, receiving-owner and allocation-journal checks. The original
return-to-user suffix runs after normal errno returns; Stops preserve the
reached journal. A generic invariant theorem composes the existing initialized
runner, with arbitrary product syscall observers, the original WG store
projection and actual fixture establishment. Its concrete owner instance has
no trace-shape, successful-run, allocation or callback premise. Each reached
decrypt and copied-trial probe inherits its exact captured facts and strict
earlier history. Copied trials remain separate from committed callbacks.

[AGENT 2026-10-17] Carry a bound on the peer ID of every resident crypted RX
packet beside its publication anchor. Publication derives the bound from the
actual checked receiving owner. It remains meaningful after key invalidation
or peer disappearance; fresh peer creation uses the old frontier bound instead
of assuming every new resident existed before creation.

Actual prepare preserves this combined invariant, including DEAD rejection.
Creation, setup reset and packet free retain their real normal/errno/Stop
behavior. Receive completion, poll and the concrete Stack callback preserve
older publication anchors using exact surviving packet cells and both peer
identity fields, independently of later key validity. Poll retains its original
arbitrary product callback contract; a separate theorem supplies the actual
Stack callback. These normal-endpoint results do not certify every consumed
event by themselves. Whole-call packet-history propagation and the positional
join to contemporaneous initialized routing remain open. No initialized
counterexample is asserted.

Thirteen new modules add 161 support theorems; ten terminal exports add ten:
553 → 566 proof files and 7,842 → 8,013 theorems. All 211 previous R3 terminal
bodies remain unchanged. R3 has 221 terminal theorems; the full terminal
surface has 597 declarations, including two definitions. No existing theorem
is retyped or deleted. The completed split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent source reviews cover every new module and terminal export.
Two new completion helpers became public, with unchanged statements and
proofs, for reuse by the poll and ingress work. Typed foreign-subsystem
adapters replace per-operation foreign frames. The generic runner reuses
existing composition laws and has no new operational observer.

Validation comprises 52 module checks: 34 ordinary failures and 18 clean
passes. One additional export check passes all ten named roots. Failures
concerned namespace/type inference, tactic selection and the unchanged
heartbeat bound. Selecting actual action heads removed speculative elaboration;
no recovery declaration or warning-bearing run supports a claim. Final named
axiom checks use only the standard three axioms. No infrastructure retry,
memory-cap increase or heartbeat increase occurs.

The complete proof gate passes 624 build jobs and 597 terminal declarations
in 6.651 seconds. Fresh kernel replay passes in 103.207 seconds without warnings. The sole build warning is
the unchanged mirror's String.mk deprecation. No guest run, mirror edit, main
update or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
