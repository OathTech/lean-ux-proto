# R4: initialized ingress coverage and saved TX work

This extension follows f4f05042 over main b3f56807, executable-identical to
the split at b700659. The mirror is unchanged. The branch retains its
nondefault LeanuxProofs target and proof gate. ReplayWindow and R1, R2, R3,
R5 and R6 remain current; the chronological GRO-order claim remains refuted.

Every accepted original runner now supplies complete normal ingress coverage.
The proof exposes its actual seccomp prefill, optional boot, indexed operation
prefix, converted syscall and syscall-entry prefix. Flood covers every expanded
input position, batch covers every executed receive cursor, and inject retains
its descriptor, front and section-entry cuts. These paths are exposed before
quantifying over carriers. Each accepted admission has a pending or actual
completed-poll disposition, including admissions removed before their operation
returns. No selected-query, source-certificate, final-funding or poll-validity
premise is supplied to the initialized theorem. Both placeholder settings and
arbitrary typed traces remain in scope.

The derived final account separates exactly one pending identity from an actual
completed poll disposition and release with no residual copy. Its removal
certificate identifies the same poll invocation and allocation-valid input.
Existing initialized completion-identity uniqueness remains unchanged. Successful
finite execution does not imply an empty residual ledger. Stopped admissions
have no new disposition account, and no World is invented after a Stop.

Proof-only factors preserve the original runner by definitional equality.
Named certificates expose the operation loop and initialization continuations;
the existing certificate rules and callback domains remain unchanged. An early
selection-record design incurred dependent-cast and heartbeat failures. The
replacement uses proposition-valued queries at the precise actual prefill/boot
success World, retaining exact normal source certificates. Equal WG-store
contents alone do not authorize a different initialization World.

On TX, full staged sends preserve an older packet state through fresh allocation
and actual submission. Concrete Stack callbacks, RX completion, grouped poll and
NAPI retain that state using the existing R2 allocation contracts. A fresh
full-ring refusal followed by the entire original encrypt iteration therefore
retains its DEAD head: selected-item exclusion follows from the actual allocation
and live logical ring, and validity is supplied before allocation/create rather
than at a later convenient cut. The no-item worker arm is included.

A separate numeric bound and physical ring-refinement predicate covers live
logical encryption items, allowing stale consumed physical slots. It survives
actual TX/RX allocation, enqueue/refusal, consume, staging, Stack, NAPI, timers,
key/session maintenance, native socket sends and retirement after a dead mark.
Initialized transport of this predicate and the complete W7 caller chain remain
open. The existing pure two-slot refusal characterization is unchanged; the new
worker theorem concerns adjacent actual cuts and does not assert that a full W7
run has already been connected to them.

Root review strengthened inject coverage to retain its actual front and section
prefix before publication. Independent reviews cover the source-position cuts,
initialized bridge and saved-worker claim; all three reviews report no remaining
findings within their stated normal-execution scope. No mirror or kernel change was made to close a proof.

Thirty-three new modules and twelve exports add 305 named theorems: 860 → 893
proof files; 11,727 → 12,032 theorems. R4 has 312 terminals, and the whole
surface has 846 declarations, including two definitions. All 300 earlier R4
terminal bodies and every earlier support theorem remain unchanged. No theorem
was retyped or deleted in this extension. The split census remains 3,197
retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

The aggregate gate passes 951 jobs and all 846 declarations in 6.952 seconds.
Fresh root kernel replay passes in 113.512 seconds with no warnings. The aggregate build’s sole warning is
the immutable mirror’s String.mk deprecation; all new proofs are warning-free.
The outer capped wrapper contains the gate and every bundled subprocess.
The published source cohort has 146 development checks: 89 failures (including
four warning-only outcomes) and 57 clean passes, plus one separate source-shape
probe. Three isolated export checks comprise one ordinary qualifier failure and
two clean passes. The first aggregate gate failed on an implicit binder resolving
to an existing name in the full Statements namespace; an explicit typed binder
repairs it. Recovery axioms after elaboration errors were rejected as failures.
Later unpublished lifecycle work is outside these counts. No infrastructure
rerun, cap increase, guest run, main update or push occurred.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
