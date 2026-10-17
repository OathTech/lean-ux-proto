# R4: initialized live encryption-ring bounds

This extension follows 13a209ca over main b3f56807, executable-identical to
the state split at b700659. The mirror remains unchanged; the branch retains
the nondefault LeanuxProofs target and its gate.

The live encryption-ring predicate combines two properties: every packet ID
in a logical live ring item is below the device's next allocation ID, and
the physical ring refines an actual sequence of original ring operations
from an initialized ring. Consumed but uncleared physical slots remain
permitted. This predicate does not assert packet residency or separation
from a selected refused packet.

Concrete preservation covers handshake receipt, RX ingress, complete encrypt,
decrypt and transmit iterations, recorded scheduling including cryptAhead,
deferred work, traffic, configuration, dumps and lifecycle cleanup. Product
monad frames handle unrelated subsystems. The original syscall's dispatch
and return-to-user suffix retain their existing source choices and guards.
Normal errno returns are included; a Stop supplies no endpoint World.

The initialized bridge retains the existing owner journal and uses the exact
prefill, boot and ordered operation prefix. Each bounded operation position
has its actual prepared World and converted syscall certificate. A supplied
endpoint invariant or future-call preservation assumption is unnecessary in
the concrete specialization. Both placeholder modes and arbitrary typed
accepted traces remain in scope.

Independent review distinguishes this completed invariant transport from the
remaining W7 disposition problem. The earlier adjacent create/encrypt theorem
does not transport a refused item through arbitrary later scheduling. Actual
disposal requires the same item to reach the logical peer-queue head. An
earlier uncrypted head can stop a TX activation while later work remains,
so an empty work queue alone is insufficient. The full two-refusal source
episode and its later disposal remain open. Chronological GRO ordering is
still refuted, and the initialized normal ingress results remain unchanged.

Two separate reviews of the generic initialized bridge and its concrete
specialization found no outstanding issue. Their checks cover actual original
initialization, source-relative operation positions, exact erasure and the
absence of a supplied endpoint invariant. The W7 architecture review's gaps
remain explicit above; no disposal claim was inferred from these reviews.

Seventeen new modules and three exports add 217 named theorems: 893 → 910
proof files; 12,032 → 12,249 theorems. R4 has 315 terminals and the complete
surface has 849 declarations, including two definitions. All 312 earlier R4
terminal bodies and every earlier support theorem remain unchanged. No theorem
is retyped or deleted. The split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

The aggregate gate passes 968 jobs and all 849 declarations in 7.832 seconds.
Fresh root kernel replay passes in 114.850 seconds with no warnings.
The sole aggregate build warning is
the immutable mirror's String.mk deprecation; the new proofs are warning-free.
The outer capped wrapper contains the gate and its bundled subprocesses.
The published source cohort has 31 development checks: eleven ordinary
failures and twenty clean passes; a separate initialized-specialization check
also passes all three axiom queries without warnings. Failed elaborations,
including their recovery axioms, were rejected. Later unpublished geometry
and producer-cut work is outside these counts. No infrastructure rerun, cap
increase, guest run, main update or push occurred.

Separate follow-on geometry development had two ordinary failed checks and
two deliberately terminated checks (exit 143). They are failures, not evidence
for this checkpoint. Dirty worktrees were preserved to recovery refs after
each interruption before work resumed; branches and real indices were unchanged.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
