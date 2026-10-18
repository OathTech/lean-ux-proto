# R3: current identity at receive and consume cuts

This extension follows b413709f over b3f56807, whose executable mirror is
identical to b700659. The mirror is unchanged. Initialized R3 packet
authorization and R4 pipeline conservation remain open.

## Established contracts

Native traffic, counter validation, decryption, data completion and ingress
preserve supplied configured/current identity on normal returns. The actual
index owner lookup, invalidation, negative errno cleanup and failed-record
Stops remain in source order. No affiliation, positive reference count,
successful authentication or totality premise is added.

The existing receive response, after-MAC, reception and worker observers
preserve that identity at each actual session cut. CurrentChecks adds
positional checks at decrypt and saved-probe entries while retaining the older
material/history safety. Equal receipt values at different journal positions
remain separate occurrences. Session, decrypt, probe and receive-worker
composition retains the actual reached checks on Stop, without asserting a
final state. Incoming support remains an explicit invariant, not an
initialization claim.

PublicationConsume transports one anchored publication certificate through
the actual capture, queue removal, counter validation and endpoint cuts. Its
Live premise retains the selected packet allocation and peer identity through
earlier interleavings; later receiving-key validity is unnecessary. The actual
consume receipt identifies its native WG/Ambient entry and exit and its exact
journal position. Cleanup may remove residents after that entry. Whole-run
establishment of Live remains open.

The joint allowed-IP loop projects exactly to the existing routing completion
and RX lifetime observers. A shared monadic source factor retains the original
raw loop's arbitrary output universe. Literal specialization checks and an
exact old-tail factor equation preserve the existing source definitions and
callback domains. Concrete leaves prove their own append behavior; the new
RX projection requires append behavior from its supplied lower continuation.

CurrentPoll carries normal identity through the real poll and GRO operations
with arbitrary product-world callbacks under their explicit preservation
contract. It reuses the existing GRO observer erasure and preservation proofs.
The actual stack callback still needs its concrete transport proof: it can
send a reply through WireGuard.

## Counts and review

Ten modules add 143 theorems; one existing-tail factor theorem and nine
terminal exports bring the increment to 153. The tree moves from 476 files
and 6,788 theorems to 486 files and 6,941 theorems. All 157 earlier R3
terminal bodies remain unchanged. R3 has 166 terminal theorems; the whole
terminal surface has 542 declarations, including two definitions. No existing
theorem is retyped or deleted. The completed split-retrofit census is unchanged:
3,197 retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.

Independent source reviews cover all ten modules and nine terminal exports.
Three duplicate material helper proofs were removed from the unpublished
receive candidate; existing SupportCallers lemmas are exposed unchanged and
reused. A comment incorrectly suggesting reachable peer erasure after a
particular successful get/pure-IRQ payment was corrected. Terminal wording
now explicitly limits native invariant preservation to normal returns.

## Validation

The 49 output-free module checks comprise 28 ordinary failures and 21 clean
passes. Counts by module group (FAIL/PASS) are publication consume 2/1,
traffic 5/4, focus 0/2, joint configuration 6/2, positional checks 1/1,
sensitive cuts 0/2, native RX 8/2, receive history 3/3, poll 2/2 and
receive checks 1/2. Failed elaboration recovery dependencies and development
warnings were rejected; accepted sources and named axiom checks have no
warnings and only the three standard axioms. Heartbeat failures were repaired
by decomposing source continuations, without increasing limits.

One complete assembled Statements check passes without warnings. The first
full gate fails after 110.23 seconds because an existing material-retention
proof does not unfold the newly shared allowed-IP factor. Adding that unfold
changes no theorem statement. The changed gate passes all 544 build jobs and
542 terminal axiom checks in 41.80 seconds.
Fresh replay of Leanux.Proofs passes in 104.09 seconds without warnings.
The proof sources remain byte-identical through replay and this checkpoint.

Central scoped builds pass. The sole build warning remains the unchanged
mirror's String.mk deprecation. No infrastructure retry, cap/heartbeat
increase, crash, cancellation, guest run, mirror edit, main update or push
occurred.

## Remaining work

Initialized closure needs the actual peer/key allocation frontiers, nullable
owner compatibility and transport of published packet identity across
interleavings. Routing completion history must join each actual source
authorization at its specified earlier prefix. The complete configuration,
scheduler and runner compositions remain to be closed. R4 follows R3.

## Reproduction

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
