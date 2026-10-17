# R3: packet certificates and routing at consume entries

This checkpoint follows 00461124 over b3f56807, whose executable mirror is
identical to b700659. Initialized R3 packet authorization and R4 receive-pipeline
conservation remain open. The mirror is unchanged.

The original initialized joint runner now has one theorem combining its owner
checks, packet/receipt linkage and routing-completion safety. The routing
conjunct retains the existing address-shape premise. Separate local routing
checks record the table at each actual consume entry, including normal None
results and receipts preceding a Stop. The original poll and its concrete
Stack callback preserve these checks. A successful Some receipt then derives
source authorization against that occurrence's strict earlier routing prefix.
This local positional premise is not yet established for the initialized runner.

[AGENT 2026-10-17] Certify each consumed event at its actual captured native
entry and strict earlier journal. Compose its state transport and positional
certificate over the existing observer; a final endpoint alone does not
establish facts about an earlier captured state.

Packet publication now survives actual admission, non-CRYPTED replacement,
handshake sending/reception, allocating session fronts, completion, poll/Stack,
queued work and full peer removal. Transport preserves both peer identity
fields of surviving peers and permits disappearance. The allocating session
front retains RX contents without assuming that the key frontier is unchanged.
Both saved-peer passes, nullable payments and the original drain limits remain.

The poll derives a certificate for each newly consumed receipt from an actual
earlier decrypt/publication occurrence. Its generic product callback contract
is retained; a separate theorem discharges the concrete Stack callback. The
combined owner/publication invariant is established by the actual fixture and
carried through prepare, NAPI, decrypt/encrypt and handshake receive iterations,
including the reached journal on failure. Enclosing scheduler, configuration,
syscall and runner packet transport, and their positional routing join, remain
open. No initialized counterexample is asserted.

Twenty-one new modules add 231 support theorems; fourteen terminal exports add
fourteen: 566 → 587 proof files and 8,013 → 8,258 theorems. All 221 previous R3
terminal bodies remain unchanged. R3 has 235 terminal theorems; the full
terminal surface has 611 declarations, including two definitions. No existing
theorem is retyped or deleted. The completed split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent reviews cover every new module and all fourteen exports. One
comment was corrected to describe all three NAPI entry points. Validation
includes 53 module checks: 27 rejected failures and 26 clean passes. Two export
checks comprise one namespace failure and one clean pass. One development
term was rejected by the kernel for an invalid existential projection; explicit
existential elimination fixes it, and the final named axiom checks are standard
only. Other failures concern type inference, source-head selection and proof
normalization. No recovery declaration, failed check or warning-bearing check
supports a claim. There is no infrastructure retry, cap increase or heartbeat
increase.

The complete proof gate passes 645 build jobs and 611 terminal declarations in
7.102 seconds.
The gate also passed before the review's comment correction; the final run
rebuilds that correction. Fresh kernel replay passes in 105.212 seconds with
no warnings.
The sole build warning is the unchanged mirror's String.mk deprecation. No
guest run, mirror edit, main update or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
