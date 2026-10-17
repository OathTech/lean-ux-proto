# R3: transmit handoffs and actual caller source

This checkpoint follows 313e87cb over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized incoming routing
authorization remains proved. Initialized transmit authorization and R4
receive-pipeline conservation remain open; full R3 is not claimed.

The native transmit observer executes the actual lifetime front once and
records a successful handoff immediately after the staging splice. It then
runs the original send/payment tail. Removing only these new receipts gives
the exact previous joint journal and native result for arbitrary incoming
histories, including Stops. Every new receipt has the captured WG/Ambient
entry and exit of that completed front. A later stopped tail retains it.

Positional checks attach the routing-completion prefix to that same entry.
They derive the selected longest-prefix peer and the destination of every
supplied packet, without a final World or a later send-success premise.
Normal-state routing uses the source's deletion-permitting retention relation;
review caught and corrected an overly strong exact-view premise. No peer
liveness, later encryption or wire-delivery claim is inferred.

The direct syscall, batch item, IPv4 Stack reply, GRO and poll now expose
shared source bodies with arbitrary product callbacks. Exact specializations
recover the existing observers, preserving FD payment, route errors, multicast,
NET_RX sections, batch results and stopped prefixes. The concrete transmit
callback preserves the routing invariant through Stack. The observed-poll
boundary retains its fresh local lifetime seed and promotes only its new
suffix. Joining the outer routing prefix to each local poll handoff, then
closing scheduler/outer callers and initialization, remains work.

[AGENT 2026-10-17] Parameterize the existing observed source bodies at their
actual callback boundaries, retaining their original specializations and
journals. This keeps copied trials and scheduler probes in their existing
scope while adding committed transmit receipts; no alternate interpreter or
history-independence assumption is introduced.

Fourteen new modules add 101 support theorems and fourteen terminal exports:
617 → 631 proof files and 8,635 → 8,750 theorems. All 263 preceding R3 terminal
bodies remain unchanged. R3 has 277 terminal theorems; the full surface has
653 declarations, including two definitions. No existing theorem is retyped
or deleted. The completed split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

Independent reviews cover the modules and exports; the routing-premise
finding is corrected. Fifty-five module checks comprise 29 ordinary failures,
25 clean passes and one rejected warning-bearing exit-zero run. Two export
checks pass cleanly. Failures concern local proof composition, names and
unproductive tactic matching at unchanged limits. Final proofs use only the
three standard axioms. Scoped builds pass. The proof gate passes 689 build
jobs and 653 declarations in 7.342 seconds. Fresh kernel replay passes in 105.441 seconds without warnings.
There is no infrastructure retry, cap increase or heartbeat increase. The
sole build warning is the unchanged mirror's String.mk deprecation. No guest
run, mirror edit, main update or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
