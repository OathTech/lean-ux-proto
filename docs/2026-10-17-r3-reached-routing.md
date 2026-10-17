# R3: native identity transport and reached packet routing

This extension follows 4b792069. The executable mirror remains unchanged over
b3f56807 (identical executable sources to b700659). R3 remains in progress.

## Established contracts

CurrentIndex carries exact allocation stamp/static identity through the actual
read, borrow and fresh nullable owner-word store, then through the complete
index scan. Receiving material and current identity are retained without
affiliation, residency or credit premises, including normal None. Configured
table coherence is separately preserved by that scan.

CurrentPeerCreation retains every surviving peer identity below the entry
frontier through allocation, all initializers and row publication. Its current
support contract needs bounds only on named owners of valid receiving keys;
nullable affiliation supplies those bounds. Allocation refusal is included,
and an arbitrary old resident at the fresh frontier is permitted.

ConfiguredHandshake preserves the configured peer view through construction,
MAC processing, cache work, actual IPv4/IPv6 transmission and handshake sending.
The worker's final peer payment instead uses invariant/identity retention,
allowing deletion. Its existing generic conjunction bridge is public for later
native composition; its statement and proof are unchanged by that visibility
choice.

PollRouting certifies each consumed receipt against its actual native before
state and records actual execution validity. It carries the supplied flat table
through the concrete poll, GRO and Stack calls, including the emitted prefix of
a failed poll. Arbitrary incoming global histories are unrestricted; only the
new suffix is certified.

PollAuthorization joins routing and the existing consumed/buffered/entered
linkage on exactly that same promoted suffix, using the checked inverse
projection. Every actual entered packet has a strictly earlier successful
consume receipt and a longest-prefix source winner for its delivered bytes.
Native WG and Ambient endpoints, packet stamp and source linkage remain exact.
This is authorization of a raw peer slot under supplied routing, not initialized
historical key identity. The later global join must identify occurrences by
position; poll-local counters and equal event values need not be unique.

## Counts and validation

Five modules add 69 theorems and six definitions. Four terminal exports preserve
all 148 previous R3 terminal bodies and bring R3 to 152. The tree moves from
464 files/6,641 theorems to 469 files/6,714 theorems. The terminal surface is
528 declarations: 526 theorems and two definitions.

Full-source reviews pass: separately authored modules received independent
review, and CurrentIndex received mutual source review during completion.
Independent review of the four terminal exports also passes. All 75 module roots
have only the three standard axioms; accepted source has zero warnings.
The 22 output-free candidate checks comprise fourteen ordinary failures and
eight passes: handshake 3/3, creation 2/1, index 4/1, poll 3/2, entered-routing
2/1 (FAIL/PASS). Failures concerned source composition, binder/projection
normalization and syntax; a monolithic IPv4 proof reached its existing heartbeat
limit and was replaced with composition over the already checked source factors.
Recovery sorryAx dependencies in failed elaborations were rejected. No limit
increase, cancellation, infrastructure retry, mirror or guest change occurred.

Central scoped builds and the combined 487-job build pass. Full gate passes 527 jobs and 528 terminal
declarations in 2.50 seconds. Fresh root replay passes in 99.55 seconds without
warnings. The sole build warning remains the
unchanged mirror's String.mk deprecation.

## Remaining work

Whole-run configured/current/nullable support, publication-to-consume identity
transport and the positional join to initialized configuration history remain
open. The new local routing result makes no cryptographic authenticity or Linux
simulation claim. R4's initialized pipeline conservation follows R3 in the
campaign order.

## Reproduction

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
