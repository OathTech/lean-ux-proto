# R3: initialized incoming authorization

This checkpoint follows 014bfd15 over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized incoming
cryptokey-routing authorization is proved; initialized transmit handoff and
R4 receive-pipeline conservation remain open. Full R3 is not claimed.

Every selected actual Stack entry now has its earlier buffer, consume and
decrypt/publication positions in the same initialized joint journal. Its
source address selects the consuming peer in the flat longest-prefix table
at that consume's strict earlier prefix. The publication certificate retains
one configured session/material/current-peer witness. A later stopped outcome
does not remove these occurrences. The typed theorem retains address shape;
successful public parsing supplies it without an authorization premise.

The runner uses the original syscall observer and fixture. A membership-aware
array rule requires the routing contract only for actual trace operations,
with arbitrary earlier results and endpoint values. Actual syscall closure
and seven-field WG store transport establish the invariant; the final World
is not substituted for a captured earlier state. JSON projection and indexed
Stops retain the existing source correspondence.

The transmit source now has a factor ending immediately after the staged
splice. Local routing authorizes that completed front even if the original
send/payment tail later stops. All early errno arms, both splice getters and
WG/Ambient cuts remain. The older normal-return handoff theorem is unchanged.
This is a local theorem: connecting every initialized direct, batch and Stack
reply handoff to its reached routing state remains work. No counterexample or
wire-send claim is inferred from this coverage gap.

Five new modules add 30 support theorems and eight terminal exports:
612 → 617 proof files and 8,597 → 8,635 theorems. All 255 preceding R3 terminal
bodies remain unchanged. R3 has 263 terminal theorems; the full surface has
639 declarations, including two definitions. No existing theorem is retyped
or deleted. The split census remains 3,197 retyped/generalized, 1,709 deleted,
2,809 retained and 558 added.

Independent reviews cover every new module and all eight exports without findings.
Seventeen module checks comprise ten ordinary failures, five clean passes and
two rejected warning-bearing exit-zero runs. The eight-export check passes
cleanly. Failures concern proof/type composition and private-name delaboration;
only warning-free completed proofs support the claims. Five scoped module
builds pass. The proof gate passes 675 build jobs and 639 terminal declarations in 7.319 seconds. Fresh kernel replay passes in 102.759 seconds without warnings.
There is no infrastructure retry, cap increase or heartbeat increase. The sole
build warning is the unchanged mirror's String.mk deprecation. No guest run,
mirror edit, main update or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
