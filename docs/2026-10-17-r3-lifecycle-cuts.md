# R3: joint runner and receiving-owner callers

This checkpoint follows c83b4064 over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized R3 packet
authorization and R4 receive-pipeline conservation remain open.

Every syscall constructor now projects to both original routing-completion
and RX observers. One initialized typed runner supplies both histories and
the exact public JSON/error result, including indexed Stops and retained
failed prefixes. The routing projection keeps the final World; the RX
projection retains its original JSON result. These equalities hold for
arbitrary traces, placeholder settings and incoming histories.

[AGENT 2026-10-17] The joint runner uses a shared proof-side source factor
parameterized by the syscall observer and successful result projection.
Four definitional equalities establish the unchanged old specializations;
the executable runner is not edited.

Receiving-owner bounds now survive concrete consume completion, stack/poll,
NAPI, prepare and both crypt workers, transmit completion, peer removal and
device lifecycle. Peer and device configuration carry current identity and
owner bounds jointly, including allocation refusals, partial normal errors
and final reference payments. Arbitrary product poll callbacks and native
deletion notifiers retain explicit preservation contracts. All fifteen
remaining environment cases also retain positional current checks.

Thirty-two new modules add 317 theorems and fourteen terminal exports add
fourteen: 511 → 543 proof files and 7,373 → 7,704 theorems. All 190 earlier
R3 terminal bodies remain unchanged. R3 has 204 terminal theorems; the full
terminal surface has 580 declarations, including two definitions. No existing
theorem is retyped or deleted. The completed split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent source reviews cover every new module and all fourteen exports.
Review removed repeated poll/store and NAPI current-state proofs in favor of
existing contracts and narrowed a lifecycle module's description to its actual
scope. A device-key projection now reuses the existing checked factor; a direct
private alias resolves macro hygiene without duplicating its proof.

Validation includes 81 module checks: 41 ordinary failures and 40 clean passes.
Four export checks comprise two ordinary failures and two passes. Failures
include source normalization, identifier/macro resolution and the unchanged
200,000-heartbeat bound; each was repaired in source. An auxiliary axiom-output
parser failed to accept declarations with no axioms; its corrected parse of
the same successful Lean output passes without rerunning Lean. Recovery
dependencies and warning-bearing failed checks are not accepted. Final named
axioms are standard-only and final proof sources have no warnings. No
infrastructure retry, memory-cap increase or heartbeat increase occurs.

The complete proof gate passes 601 build jobs and 580 terminal declarations
in 6.981 seconds. Fresh kernel replay passes in 106.362 seconds without warnings.
The sole build warning is the unchanged mirror's String.mk deprecation.
No guest run, mirror edit, main update or push occurs.

Remaining work is owner propagation through handshake, scheduler, deferred
and outer syscall callers; concrete packet identity transport from publication
to consumption; and positional routing agreement with earlier initialized
configuration history. R4 follows that initialized R3 work.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
