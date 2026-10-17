# R3: initialized outgoing authorization

This result follows 005c26cd over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Together with the existing
trie/configuration refinement and initialized incoming authorization, it
completes the charter's R3 property. R4 receive-pipeline conservation remains
open; its chronological GRO-order counterexample is retained.

`parsed_initialized_transmit_authorization` selects any completed handoff in
the actual initialized observer and derives its longest-prefix peer from the
routing history strictly before that occurrence. It retains the actual native
WG/Ambient front entry and exit and proves destination agreement for every
supplied packet. Public parsing discharges configuration address shape. Both
placeholder settings and prefixes preceding an indexed Stop are included.
There is no supplied final invariant, authorized-packet premise, successful
trace outcome or unresolved callback contract.

The observer executes each native front once, records the completed staging
splice, then executes the original send/payment tail. A stopped tail retains
the receipt. Direct socket transmission, batch transmission and Stack replies
are all wired through that observer. Polls keep the original fresh local seed
and promote only their new suffix; the caller's routing prefix remains attached
to each handoff. Encryption's softirq, decryption's IRQ/softirq placements,
committed scheduler resumes, deferred sends, timers and return-to-user waits
all use the checked callbacks. Configuration retains its original routing
completion events. Copied scheduler consistency trials retain their original
probe scope and cannot add committed transmit receipts.

The complete observer projects exactly to the original RX journal for
arbitrary incoming histories and has the executable runner's exact JSON or
indexed Stop. The poll additionally projects to the original joint routing/RX
journal. The theorem proves authorization of each selected occurrence; complete
handoff coverage follows the checked source specializations, native emission
law and independently reviewed wiring of all three executable wgXmit call
sites. No separate converse reachability theorem, Noise authenticity, later
wire-send guarantee or simulation against C is claimed.

Thirty-one new modules add 397 support theorems and twelve terminal exports:
631 → 662 proof files and 8,750 → 9,159 theorems. All 277 preceding R3 terminal
bodies are unchanged. R3 has 289 terminal theorems; the full surface has 665
declarations, including two definitions. This extension retypes or deletes no
existing theorem. The split census remains 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added.

Independent reviews cover every new module, the initialized contracts and the
twelve exports. A separate source-coverage review checked all committed
transmit and nested polling placements, copied trials, receipt emission and
position preservation; it found no substantive defect. Eighty-seven module
checks comprise 39 ordinary failures, 47 clean passes and one rejected
warning-bearing exit-zero run. Two export checks pass cleanly. The failures
were proof composition, syntax/imports and tactic selection at unchanged
limits; recovery terms from failed checks were rejected. The first gate run
rejected a nested terminal namespace before building; replacing it with a
section fixed the form without changing a theorem. The subsequent gate
passes 720 build jobs and all 665 declarations in 7.759 seconds.
Fresh kernel replay passes in 105.8 seconds with no warnings. Scoped builds pass; final proof sources have no
warnings or nonstandard axioms. The sole build warning is the unchanged
mirror's String.mk deprecation. No infrastructure retry, cap increase,
heartbeat increase, guest run, mirror edit, main update or push occurs.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
