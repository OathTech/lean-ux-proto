# R3: initialized publication transport

This checkpoint follows 245f3d30 over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized positional routing
and transmit handoff authorization remain open; full R3 and R4 receive-pipeline
conservation are not claimed.

The original initialized runner now derives the joint owner/publication
invariant for every typed trace and both placeholder settings, including
stopped prefixes. Native transmit, timers, peer/device configuration, device
lifecycle and dumps preserve packet anchors and peer frontiers. The actual
scheduler, deferred work, traffic, all remaining calls and every syscall carry
them through the existing observers. Arbitrary product callbacks retain their
explicit contracts, and the concrete callers discharge them. Saved-state trial
contracts retain their original conditional owner premises.

Each consumed occurrence receives a certificate from its strict earlier
publication. Exact journal projections preserve specified positions: a selected
Stack entry links to its earlier buffer, consume and decrypt occurrences,
retaining one configured session/material/current-peer witness. The source
winner is at the consume position; that routing premise remains supplied in
this join. The positional routing invariant now crosses worker, scheduler,
deferred, configuration and traffic callers; its initialized closure remains
separate. No initialized counterexample or cryptographic authenticity claim is
made.

Twenty-five new modules add 319 support theorems and twenty terminal exports:
587 → 612 proof files and 8,258 → 8,597 theorems. All 235 previous R3 terminal
bodies remain unchanged. R3 has 255 terminal theorems; the full terminal surface
has 631 declarations, including two definitions. No existing theorem is retyped
or deleted. The completed split census remains 3,197 retyped/generalized, 1,709
deleted, 2,809 retained and 558 added.

Independent reviews cover the new modules and all twenty exports. The 64 module
checks comprise 31 ordinary failures, 32 clean passes and one rejected exit-zero
run with a warning. Five export checks comprise three failures and two clean
passes. Failures concern source/type composition, namespace and scope syntax;
no failed, warning-bearing or recovery declaration supports a claim. The first
complete gate failed on section scope syntax; the corrected final gate passes
670 build jobs and 631 terminal declarations in 7.012 seconds. Fresh kernel replay passes in 104.127 seconds without warnings.
There is no infrastructure retry, cap increase or heartbeat increase. The sole
build warning is the unchanged mirror's String.mk deprecation. No guest run,
mirror edit, main update or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
