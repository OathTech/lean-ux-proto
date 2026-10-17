# R3: concrete workers, owner bounds and configuration cuts

This extension follows c4fd1a37 over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized R3 packet
authorization and R4 pipeline conservation remain open.

## Established contracts

The actual fixture stack, including replies transmitted through WireGuard,
preserves supplied configured/current identity. This discharges the concrete
poll callback. Existing prepare, NAPI, decrypt and encrypt observers preserve
positional current checks on the same journal, including emitted Stop prefixes.
The encryption helper retains arbitrary product callbacks under their explicit
preservation contract.

The receiving-owner carrier combines bounded valid-key owner words, nullable
RX/key compatibility and RX key-slot bounds. The real fixture establishes it;
actual peer allocation, key allocation, session construction and index
acquisition preserve it at normal endpoints. Session and peer-allocation
observers carry it beside their existing current/history or R2 allocation
guarantees on the identical execution. A checked malformed supplied-state
allocation witness shows why RX slot bounds are needed; it is neither an
initialized execution nor an R3 counterexample.

[AGENT 2026-10-17] Published-packet transport permits peer absence between
calls and retains both identity fields for surviving peers. A normal consume
establishes entry residency through its first actual getter, recovering the
unchanged full consume certificate. This avoids requiring continuous residency;
it does not establish transport across all initialized interleavings or depend
on later receiving-key validity.

The complete configuration tail, peer removal and update project exactly to
both original routing-completion and product RX lifetime streams. Concrete
removal closes the former callback/append obligations through timer stop,
both flushed workers and the original bounded drain. Shared polymorphic source
factors retain their original output universe, null/refusal arms, arbitrary
incoming histories, WG/Ambient endpoints and every failed prefix. Literal
specialization equations preserve the existing raw and observed bodies.

## Counts and review

Twelve modules add 169 theorems and twelve terminal exports add twelve more:
486 → 498 proof files and 6,941 → 7,122 theorems. All 166 earlier R3 terminal
bodies are unchanged. R3 has 178 terminal theorems; the full terminal surface
has 554 declarations, including two definitions. No existing theorem is retyped
or deleted. The completed split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

Independent source reviews cover every new module and all twelve exports.
The resulting claims remain local propagation/projection contracts; none
asserts initialized authorization from supplied invariants.

## Validation

Fifty module-check attempts comprise 27 ordinary failures, one warning-bearing
exit-zero result rejected and repaired, one infrastructure preflight failure,
and 21 clean passes. Two of these are isolated removal-tactic diagnostics.
Five terminal-draft checks comprise two ordinary failures and three clean
passes. Recovery dependencies from failed elaboration are rejected; final
named axioms are standard-only and accepted proof sources have no warnings.
Existing heartbeat failures are repaired structurally without increasing limits.

The one infrastructure failure occurs before Lean starts: an imported
RetainingConfiguration object is temporarily absent during the preceding
checkpoint's rebuild. One unchanged retry after the root's stable-artifact
notice passes. There is no second retry.

Scoped builds and the complete gate pass: 556 build jobs and 554 terminal
declarations, with only the permitted axioms. Fresh kernel replay passes in 100.86 seconds without warnings.
Proof sources remain byte-identical through replay and this checkpoint.
The sole build warning is the unchanged mirror's String.mk deprecation.
No cap/heartbeat increase, crash, cancellation, guest run, mirror edit,
main update or push occurs.

## Remaining work and reproduction

Initialized closure still needs propagation of owner/allocation bounds through
ingress and all callers, published-packet transport across interleavings, and
the positional join with initialized configuration history. The scheduler,
full configuration and runner compositions follow. R4 remains next.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
