# R4: concrete poll/decrypt boundaries and queued-work conservation

This checkpoint follows 0268b1fc over main b3f56807, whose executable mirror is
identical to the state-split landing b700659. The proof target and gate remain
on proofs/campaign. The mirror is unchanged. R3 remains complete; chronological
GRO order remains refuted. Initialized receive-pipeline conservation remains open.

The unchanged receive poll restores CarrierState and StableRx at every normal
endpoint, subtracting precisely its seeded removal journal. Its early-exit
head fact justifies NAPI completion; a whole-budget unsupported outcome is not
a completed poll. The actual softirq, inline and IRQ callers compose those
facts, retaining the original record guards and Stack callback.

[AGENT 2026-10-17] Compose callback accounting relative to a fixed incoming
history, using only its actual appended removal suffix. Each poll still receives
the current prior history; no history-independence premise or replacement
observer is needed.

The concrete decrypt iteration now discharges its NAPI and rescheduling
contracts. Publication's actual acquired reservation survives IRQ and is paid
at the source put. Normal completion restores stable funded receive carriers
and a physical ring witness. The exact receive-journal path is retained; the
physical ring journal is a separate observer of the same raw execution. The
headline terminal exposes that witness existentially.

Send and clear workers consume explicitly supplied stamped reservations.
Their native flushes and actual environment dispatch prove membership from the
recorded unit or default head, remove the first matching occurrence, and retain
every later duplicate. Pending guards and section records stay in source order.
The clear timer appends only its actual acquired owner, or repays it on queue
coalescing. Final peer deletion is allowed; queue membership or spare reference
count never supplies funding. All three nullable key slots retain their bounds
and ownership compatibility through admission, staged traffic and completion.

These remain local contracts. Whole-run conservation still needs complete
source-owned base/list, work, TX-batch, dump-cursor and transient funding,
including newly generated handoffs, lifecycle draining, and composition through
the initialized runner. No normal endpoint is invented for a Stop. R1, R2, R3,
R5, R6 and the replay-window result retain their existing status.

Sixteen new modules add 195 support theorems and thirteen terminal exports:
674 → 690 proof files and 9,331 → 9,539 named theorems. All 143 preceding R4
terminal bodies and every other existing theorem remain unchanged. R4 now has
156 terminal theorems; the full surface has 690 declarations, including two
definitions. No existing theorem is retyped or deleted. The split census remains
3,197 retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent review covers every module and all thirteen exports. One review
finding corrected the terminal comment's overly strong description of the
physical-history witness; no theorem statement changed. Seventy-one module
checks comprise 42 ordinary failures and 29 clean passes; all three export
checks pass. Failures were elaboration, source decomposition and normalization
at unchanged limits; recovery axioms were rejected. Scoped builds pass. The
aggregate gate passes 748 jobs and all 690 terminal declarations in 4.736 seconds.
Fresh root kernel replay passes in 105.281 seconds with no warnings.
The sole build warning is the unchanged mirror-side String.mk deprecation;
proof sources and fresh replay have no warnings. Every heavy job ran under the
outer capped wrapper; there was no infrastructure retry, cap increase, guest
run, mirror edit, main update or push.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
