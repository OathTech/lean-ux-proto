# R3: current identity through native lifecycle and observation journals

This extension follows d7669cde. The executable mirror remains unchanged over
b3f56807 (identical executable sources to b700659). Initialized R3 packet
authorization remains open.

## Established contracts

ConfiguredReceive covers actual response construction and Noise initiation/
response consumption. Authentication refusal may release and delete a peer;
normal returns preserve configured/current identity without positivity,
affiliation or successful-authentication premises. ConfiguredReceiveLeaves
carries the exact configured cells through receive-side timers, endpoint/cache
updates and cookie replies, including allocation refusal and both IP families.

CurrentLifecycle covers flushed send/clear work, the original bounded drain,
timer stopping and both peer-removal phases. CurrentDevice extends that
conjunction through remove-all, stopping, destruction, deletion and creation.
The deletion callbacks remain arbitrary native actions with explicit
preservation contracts. A new empty device needs no historical receipt.
Original guards, record failures and deletion behavior remain unchanged;
no final state is asserted after a Stop.

CurrentSessionPrefix carries configured/current identity through the existing
once-only session observer, both actual journal focuses and the native/product
adapter. Its combined contract joins the existing material/history safety on
the identical run and history. CurrentHistory supplies normal transport through
the unchanged lifetime-only observer. Those normal contracts accept arbitrary
incoming receipts; their trivial history-safety component does not certify
unrelated old events.

JointPrimitives executes each existing native lifetime observer once and adds
one routing completion on normal return, including negative errno results.
Its two exact projections recover the existing RX and routing observations,
with arbitrary incoming probes and receipts. A Stop preserves the actual
access prefix and emits no new routing completion. Configuration callers and
positional joins still require composition over these primitives.

## Counts, review and validation

Seven modules add 69 theorems; five terminal exports bring the increment to 74.
The tree moves from 469 files/6,714 theorems to 476 files/6,788 theorems.
All 152 previous R3 terminal bodies remain byte-identical. R3 now has 157
terminal theorems; the whole surface has 533 declarations, including two
definitions. No existing theorem is deleted or retyped in this extension.
The completed retrofit census remains unchanged.

Independent source reviews cover all seven modules and five exports.
Two reuse findings removed unpublished duplicates of cache reset and endpoint
extraction frames; their consumers now use the existing checked lemmas.

The 29 output-free module checks comprise 17 ordinary failures, eleven clean
passes and one exit-zero check with an unused-simp warning, repaired before
acceptance. FAIL/PASS counts are lifecycle 3/1, receive 5/2, device 1/1,
session journal 3/2, generic history 1/1, joint primitives 3/2 and receive
leaves 1/2, plus that warning-bearing leaf check. One additional complete
Statements check passes. Accepted source and all 83 named module roots have
zero warnings and only the three standard axioms. Failed elaboration recovery
dependencies are rejected. No infrastructure retry, limit increase, crash,
cancellation or guest run occurred.

Central scoped builds pass. The complete gate passes 534 jobs and all 533
terminal declarations in 7.43 seconds. Fresh root replay passes in 102.68
seconds without warnings. A final EOF-only normalization is followed by a
passing 3.43-second gate; the rebuilt module and both downstream root objects
are byte-identical to those freshly replayed.
The sole build warning remains the unchanged mirror's String.mk deprecation.

## Remaining work

Whole-run configured/current support, the anchored publication-to-consume
packet certificate and the positional join to initialized configuration history
remain open. A queued crypted packet can survive invalidation of its receiving
key, so current valid-key support alone does not establish packet identity at
consumption. R4's initialized pipeline conservation follows R3.

## Reproduction

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
