# R3: joint syscall, scheduler and receiving-owner cuts

This extension follows c69b05ad over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized R3 authorization
and R4 receive-pipeline conservation remain open.

The existing scheduler and all fourteen deferred-call cases now preserve
positional current checks, including crypt-ahead, saved filter trials, both
timer modes and their exact end guards. Whole peer/device configuration and
the complete wgSet syscall project to both original routing and RX observers.
Descriptor handling, task work, send/timer waits, arbitrary incoming histories,
ordinary errors and every stopped prefix remain in that single execution.
Unconditional append proofs justify focus distribution without an allocation
or initialization assumption.

The receiving-owner carrier now survives actual admission, enqueue, refusal
repayment, ENOSPC disposal, decrypt, packet replacement and publication.
The joint owner contract combines current checks, the existing R2 boundary
invariant and owner bounds on the same journal. The actual fixture establishes
it; concrete receive and decrypt observers preserve it. At a specified decrypt
occurrence, successful publication retains the strict earlier session prefix.

[AGENT 2026-10-17] Native receive uses a private existential allocation witness
only for normal-state transport, derived from the actual existing observer.
The outer checked contract still uses its own exact prior journal. No saved
earlier World is assigned allocation evidence from a later prefix.
The product decrypt worker retains arbitrary IRQ/softirq callbacks under
explicit carrier contracts; concrete poll/Stack owner propagation is still open.

Thirteen modules add 239 theorems and twelve terminal exports add twelve:
498 → 511 proof files and 7,122 → 7,373 theorems. All 178 earlier R3 terminal
bodies are unchanged. R3 has 190 terminal theorems; the full terminal surface
has 566 declarations, including two definitions. No existing theorem is
retyped or deleted. The completed split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

Independent reviews cover every new module and all twelve exports.
One duplicate private timer-view proof was replaced by reuse of the existing
proof. Direct use inside its tactic macro failed; a direct checked alias
resolves that reference without repeating the proof. The revised source passes.

Validation includes 54 module checks: 24 ordinary failures, one warning-bearing
exit-zero result rejected and repaired, and 29 clean passes. A separate reuse
diagnostic passes. Four export-draft checks comprise two ordinary failures and
two passes. One scoped build failed during the alias cleanup; the changed
source builds successfully. Failed elaboration recovery dependencies are
rejected, and final named axioms are standard-only with no proof warnings.
There is no infrastructure retry or increase of an existing limit.

The complete gate passes 569 build jobs and 566 terminal declarations in
6.416 seconds. Fresh kernel replay passes in 108.149 seconds without warnings. The sole build warning is the
unchanged mirror's String.mk deprecation. No guest run, mirror edit, main update
or push occurs.

Remaining initialized work includes owner propagation through all callers,
publication transport across interleavings, the other configuration/lifecycle
syscalls and the positional join to initialized configuration history. R4 follows.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
