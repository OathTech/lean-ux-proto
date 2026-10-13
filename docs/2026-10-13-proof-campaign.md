# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`. The
[charter](2026-10-13-charter-proof-campaign.md) defines the campaign. Both named
prerequisites were carried over `2c7a076`; the audit wave at `f45bde8` is now
carried, with the mirror exactly matching the landed source. All existing
result rows are current over `f45bde8`; component rows retain their explicit
open obligations. R5 is resolved through checked Rule Zero counterexamples.
No integration into main, push, differential check or guest run.

| Result | Progress |
| --- | --- |
| R1 anti-replay | Complete with the intentional inclusive-floor correction; recorded replay and independent review checked. Seccomp frame carry checked. |
| R2 lifetime safety | Store identities, failure-retaining allocation/release and caller composition cover session/rotation, peer creation, receive entry/maintenance/completion, receive polling with the actual stack callback, transmit entry, TX staging, decrypt iteration and ten socket/cache/loopback calls; stale-cursor finding checked. Remaining callers, lifecycle and whole-run internal-access coverage remain in progress. |
| R3 cryptokey routing | Original prefix arithmetic and total longest-prefix lookup over represented trees, pure insertion, original empty-root, arbitrary-depth empty-child and exact-prefix insertion with sequence wrappers, and total original placement proved. Selected-root graft normal endpoints and rollback effects checked; successful graft representation, general mutation/history and path refinements remain open. Path proofs follow R2. |
| R4 delivery | Accepted original replay over f45bde8 refutes chronological post-GRO stack order: a held ACK followed by a distinct-flow SYN produces the SYN's RST first under the same key lifetime. Exact current poll erasure and removal-prefix order with an explicit callback queue contract pass the gate, as does the original-helper reorder equation. The former chronological callback theorem is retired, with its predicate unchanged. Selected-order/source-tag closure and pipeline conservation remain open. |
| R5 key lifetime | Resolved through Rule Zero counterexamples, with 13 positive local contracts. Original/observed replays show nonce R+1 authenticating before rejection, queued transport keepalive encryption after recorded expiry, and packet-held material used after zero/clear before a new handshake. The new time inputs have coherent coarse/jiffies/arm arithmetic; Linux schedule reachability is not claimed. Validated over f45bde8. |
| R6 flood resistance | Not started. |

**Last validated mirror: `f45bde8`.** The full proof gate passed 249 build jobs
and 206 terminal statements (ReplayWindow 15, R1 9, R2 116, R3 27, R4 26,
R5 13), with only permitted axioms. Stock
`leanchecker --fresh Leanux.Proofs` passes. The default model build passes
60 jobs; the unit tier passes 94 tests in 21.624 seconds with one skip.
Nine sequential original/observed replay checks pass: R1's inclusive floor,
both R2 stale-cursor variants, R4's GRO reordering, R5's boundary and strict
counter, delayed encryption, coherent post-clear and legacy post-clear cases.
Each asserts its witness and exact original/observed JSON equality. The new
R4 and R5 streams are generated mirror inputs, not Linux captures; their
scope and provenance are recorded below.
Independent reviews cover peer creation, the seccomp carry, mixed enqueue,
decrypt execution, keypair/packet releases, ambient caller composition,
allocation and release-bound composition, session creation and rotation,
the mixed peer-creation bridge, receive entry, maintenance, completion and polling,
TX staging, pure trie
insertion, original empty-root and arbitrary-depth empty-child insertion with
its wrapper, exact-prefix replacement, list deletion, placement and selected-root
graft endpoints/rollback, saved-peer scans, the ten-call socket family,
transmit entry, actual stack/poll composition, the prerequisite carry, and the
full-ring, receive-queue, complete receive-completion and outer-poll components, R5 receive/key-time, RX attempt and TX admission components, and the
R5 replays with the timer-pass observer.
The final source and contract reviews have no unresolved correctness findings;
their frozen file hashes matched before the checkpoints.

**Shared carry.** Signal/task and pipe helper frames, seccomp entry/tail frames
and arbitrary prefill preservation keep the seven-field WG projection intact.
The runner observers include the child fixture and prefill success/error paths;
no seccomp-free trace premise was added. The BPF converter proof shares compiler
continuations and proves progress of its integer pass counter before framing
the repeat loop. This carry took 17 compile passes over 36m34s; an independent
reviewer checked source correspondence and final deltas in two passes, and
another worker checked the loop architecture. That checkpoint also passed
`capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs`.

**Prerequisite carry.** Comparison records retain their exact operands;
`CounterWindow.counterValidate_execution` still identifies the full original
World. Clock consumers use the landed `Int64`/`UInt64` operations, timer arms
retain both signed-gap failures, and logged scheduling retains occupancy and
record-derived bounds plus kind-310 peek/read validation. No arbitrary-record
or malformed-World case was excluded. The carry took about forty minutes and
twelve local build invocations before the final gate; one worker interruption
was recovered after preserving all dirty worktrees to snapshot refs. The
interrupted build's completion handle was unavailable; its log reported a
normal proof failure, and subsequent collected builds and the gate passed.
The earlier transmit/stack implementation used five local attempts before this
carry. No cap was hit. R4/R5 property proofs are separate from these frames.

**Audit carry.** The index-unhash equations retain both the recorded decision
and missing-device failure; cookie frames retain rotation's extra clock and
randomness. Signed MTU and initiation-consumption inputs use the landed types.
Receive refusal now accounts for the C-shaped puts and packet free. Logged
polls retain the actual GRO batches, held packets and callback timing.
Independent source reviews covered the shared frames, R2 caller repairs and
R4 erasure/order work; all findings were corrected and frozen source hashes
reconciled. The R4 chronology claim failed and is reported below rather than
carried as a theorem. This checkpoint used fourteen root carry builds, six R2
builds and sixteen R4 builds/probes before the final passing gates and nine
witness reruns; intermediate failures were ordinary proof or assertion failures,
with no cap or interruption. Temporary logs and generated axiom files were
removed after checking their collected exit statuses.

## R1 — anti-replay uniqueness and the inclusive floor

[AGENT 2026-10-13] Reuse the existing pure counter-window model, exact S2
refinement, finite mirror-call refinement and committed runner observer for
R1. Add arithmetic bounds in the reusable `WG/CounterWindow` layer and export
the result from `WG/AntiReplay/Statements.lean`. This keeps the new proof
obligation at the small replay-state projection.

The original wording excludes counters **at or below** highest seen minus
8128. The proved wording excludes counters **strictly below** that boundary;
an unseen counter at equality may be accepted. Both the mirror's strict
`ctrTooOld` comparison and Linux `receive.c:counter_validate` implement this
inclusive edge, and Linux's `selftest/counter.c` explicitly tests acceptance
of zero after counters 1 through `COUNTER_WINDOW_SIZE`. This is an intentional
design nuance, not a mirror/kernel disagreement. The arithmetic statement
uses the one-based stored high-water mark to avoid natural-number subtraction
at an empty window.

**Architecture and refinement.** `CounterWindow/Bounds` proves the arithmetic
guard and preserves the 128-word bitmap through finite calls. The existing
`mirrorCalls_refines` identifies those calls with `accepted` and `finish`,
including the exact projected final state. `Keypairs/Evolution/Bounds` adds
`FloorHistory`: every earlier accepted nonce is at most 8128 above every later
one in the same allocation lifetime. `Inv.remembers` supplies the old
high-water bound; the validator's acceptance guard supplies the new bound.
`Evolution.floor` composes this through lifecycle and validator transitions;
the outer runner proof carries the invariant through the already checked
observer. `runner_floor` discharges all syscall contracts. Together with
`runner_uniqueness`, it quantifies over every successful original execution,
including arbitrary accepted record schedules and slot reuse. No new observer
copies or history fields were added. Committed-call coverage and discarded
scheduler probes retain the independently reviewed ReplayWindow interpretation.

**Rule Zero boundary witness.** A six-operation trace configures and brings up
wg0, observes its initiation, injects the recorded response, then injects valid
keepalives with wire counters 8200 and 72. Both return true in allocation
lifetime 1. The second is exactly at `8200 − 8128`. The record stream is a
reconstruction from the tracked `CONTENDED_ROAM_CMP` capture, with the two
authenticated datagrams from `rx_window.json`, widened legacy section identities,
monotonically adjusted clocks for the second data operation, and synthetic
site-128 end-of-wait bounds added for the current timer interface. This is an
accepted **non-placeholder mirror replay**, not a new Linux capture. The
original and logged runners produce identical JSON. The terminal theorem
`inclusive_boundary_witness` separately proves, by kernel reduction, that the
pure empty-window run `[8129, 1, 0, 1]` accepts exactly `[8129, 1]`.

Reproduce the recorded replay without QEMU or retained dumps:

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r1-inclusive-floor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/Logged/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

**Validation and effort.** Current validation is recorded above. The initial
build failed because its dependency scan preceded the newly added root import;
a fresh build resolved that dependency. Five local compile passes
resolved proof syntax and elaboration issues. R1 took roughly fifteen elapsed
minutes with bounded worker investigation and proof implementation; replay itself
took under one second. No differential check or guest was run.

**Independent review.** A worker uninvolved in the R1 implementation reviewed
the proof/source correspondence and observer coverage in two read-only passes.
No correctness defect was found. Its two reporting requests are addressed
above: distinguish the pure and runner witness counters, and identify the
record stream as reconstructed rather than a fresh Linux capture. It did not
run the build or gate; those results are the coordinator's checks.

**Ranked mirror-shape recommendations.** None: the existing named validator,
replay-state projection and proof-side lifetime evolution already make R1
routine. An observer/history field or a changed comparison in the mirror
would not preserve altitude and is not proposed.

## R2 — lifetime identity and retained references (in progress)

**Architecture decisions [AGENT 2026-10-13].** Separate resolved allocation
identity from ownership of saved numeric references. Share frontier algebra
between stores, and frame unrelated operations once over the seven-field WG
kernel projection. Keep observation history outside the exception layer so
failed prefixes survive. Strengthen access safety separately with release
uniqueness and then allocation/epoch bounds; share caller proofs through
explicit ambient contracts instead of duplicating each invariant's proof.
Observe saved peer-map entries at the demanded predicate evaluation, retaining
the saved stamp and proving it remains resident; do not insert a new getter.

**Checked model and refinement.** `Lifetimes/Store` and `Actions` describe
slot/stamp transitions over original executions. `Keypairs/Identity` uses the
existing whole-syscall evolution to exclude reintroduction of absent old keypair
identities at operation endpoints. Peer and packet primitive contracts extend
that algebra; the packet primitive result is within one device epoch. These
endpoint results alone do not establish internal-access coverage.

`Logged/Prefix` preserves the exact original result, successful World or Stop
while retaining prior events on failure. `Focus` injects local suffixes into one
mixed peer/keypair/packet stream. Packet stamps include `(ifindex, id + 1)`.
`LifetimeEvent.Safe` excludes reads and writes after release of the same stamp.
Failed getters resolve no object and emit no access. `ReleaseInv` adds resident
uniqueness across each family, including both packet stores. `AllocationInv`
adds separate slot and lifetime frontiers, current packet-frontier bounds and
past-epoch bounds. Those premises supply allocator vacancy; all-input erasure
still reproduces malformed occupied-slot overwrites without calling them safe.
Every runner fixture initializes the invariant, and seccomp prefill preserves it.

The source-observed complete calls currently cover `peerCreate`, `peerGet`, `peerPut`, dump completion,
keypair creation/acquisition/release/clearing/rotation/session creation, TX/RX
allocation and free, optional-peer/index/public-key lookup, complete receive
enqueue and `consumeData`, packet decryption and one decrypt-worker
iteration. Twelve endpoint/cache, timer, queued-handshake and receive-key-refresh
calls also preserve safe prefixes; Boolean guard/modifier results are retained.
Seven complete TX staging calls cover CPU selection, peer/device enqueue,
`createData`, staged-packet purge/send and keepalive. Their `TxContracts`
companion retains cached identity predicates through scalar device updates,
with a concrete allocation-invariant instance; CPU and enqueue results remain
`Nat` and `Int`. `PrefixLoops` shares finite range and map composition.
`CounterAccess` observes the complete validator on all inputs, with no bitmap-size
premise. `AllowedLookupAccess` observes peer acquisition after the original node
search. `ReceiveCompletion` composes rotation, staging, maintenance, source lookup,
reference release and statistics; `ReceivePoll` adds the original queue traversal
and cleanup with an explicit observed callback. Its ambient and allocation
contracts require callback preservation. `DeviceXmit` now observes the complete
original transmit entry, including its trimming/splice loops, lookup, packet
staging and reference cleanup. `StackAccess` supplies the actual IPv4/IPv6
callback and composes it with the original receive poll; TCP replies use the
observed transmit entry. `PrefixControl` preserves exact state-dependent
Stops and the prior history, and `PrefixLoops` shares list-iteration laws.
These concrete callbacks discharge the allocation-invariant contracts without
adding a field to the earlier TX contract.
`SavedPeers` gives exact short-circuit scan events under an explicit saved-stamp
residency premise. `LoopbackAccess`, `SocketCache`, `SocketSend` and `SocketCalls`
cover ten complete cache/endpoint/loopback/tunnel/IPv6 calls. Their all-input
erasure retains results and Stops; generic safety has an explicit device-statistics
contract, instantiated for allocation bounds. A cache-miss clock failure retains
exactly its preceding peer read. Generic record-consumer frames live once in
`Framing/KernelEffects`, with older interfaces derived by projection.
Shared bind and finite-loop laws compose these per-call contracts. Generic enqueue/decrypt
contracts admit explicit observed softirq, IRQ-exit and rescheduling callbacks;
they are instantiated at the allocation invariant. Peer creation reuses its
existing observer unchanged, with original slot/metadata geometry transporting
the stronger invariant. `AllocationRetention` uses surviving entry residents
and explicit release origins to retain bounds through releases.

Exact event equations cover pending-worker and refcount failures, including
writes before zero-refcount rejection and releases only after successful final
puts. Conditional whole-call equations retain six events before session birthdate
clock failure, and allocation/write before peer initialization's first cache
clock failure. Receive queue-record failure retains exactly five accesses,
including the packet setter's nested read. These equations are not accepted-run
witnesses. Lookup preserves the first matching index's exit even if its kind is
wrong; receive entry preserves ENOSPC's keypair put, peer put and packet free,
and EPIPE's pure callback.
Handshake-completion clock failure retains four accesses before the Stop.
The timer guard's nested peer getter is evaluated unconditionally before
`andM`; its observer preserves that elaborated order. Coverage is
checked against actual source calls; erasure or an unchanged-Kernel theorem
cannot certify that a lifted helper contains no reads. TX observations retain
the setter's read/write pair, both restoration getters and the nonce write
before rejection. Duplicate cleanup IDs remain admitted, including a later
Stop after an earlier free. The keepalive allocation-record failure equation
retains its initial peer read. Plain staged packet values have no resident
TX/RX store identity until `newTxSkb` runs. Shared filesystem frames
also end at return, leaving queued task work for its later caller proof.
The poll retains both `dropPeeked` getters and releases keypair then peer then RX
packet. GRO invokes batch callbacks before the current packet's cleanup and
flushes the remaining GRO state after the final peer update. Its budget
and malformed-queue Stops remain in domain. An exact empty-bitmap failure equation
retains the validator's initial keypair read and no write; this is an original
getter-conditioned failure, not an accepted-trace finding. Safe access prefixes
do not establish delivery, order or reference ownership.

**Remaining claim.** Full caller, device-lifecycle and scheduler closure remain
unproved. Encrypt/TX workers, IPv4 socket send/setup, handshake
execution and timer callbacks, peer removal, netlink and direct resident scans
need coverage. Saved scalar-reference
ownership is a separate obligation: aliased or dangling IDs may legitimately
stop after earlier safe accesses. No distinct-keypair-slot premise is hidden in
rotation or clearing. The stale cursor below does not resurrect the old stamp,
so it does not refute the endpoint identity theorem or settle charter R2.

**Concrete reference finding.** An eight-operation accepted mirror run creates
28 peers, starts a stepped dump, deletes wg0, creates a new wg0 and 27 replacement
peers, then receives a chunk. The dump retained slot 26, old identity 27, with
two references. Its continuation cleanup releases replacement identity 55,
which has one reference, removing it while the peer list and public-key table
still name slot 26. The received message is the already queued first chunk;
continuation generation performs the destructive release. Old identity 27 does
not return: this is reference retargeting and table incoherence.

The guest rejects deletion with a pending dump (`wg_delete_with_dump_pending`),
and the W1/W2 design requires that restriction. `Env.wgDelete` checks worker
idleness but omits the dump guard. C retains `ctx->wg`; the mirror resumes a
Boolean-held cursor against the current device. This is an accepted-mirror
domain bug, not evidence of a Linux lifetime bug. The explicit non-placeholder
records are synthetic, not a fresh capture. Five runner checkpoints, their count
and original JSON equality are checked. The kernel-reduced
`stale_cursor_retargets_replacement` separately exercises `wgGetDeviceDone`;
the full replay reaches the same bad put through dump-resume cleanup.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

A second accepted eight-operation variant gives replacement peer 26 an IPv4
`10.0.0.0/8` binding before the stale continuation releases it. The final
checkpoint follows the actual device root: that prefix still names slot 26,
while resident identity 55 is absent. It checks eight checkpoint emissions,
five specified projections and original-runner JSON equality. The records are
again synthetic and explicit. This rules out unconditional owner-residency
invariants; it neither resurrects identity 27 nor by itself demonstrates
packet misrouting or disagreement with insert/remove history. The original
witness is unchanged.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor-orphan |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/ReplayOrphan.lean
```

**Effort and review.** Each reproduction takes under one second. The main caller
checkpoints took roughly 6–25 minutes each, with 4–19 compile passes; TX
staging took fourteen passes over 24m44s: two passed and twelve failed before
correction. Receive completion/poll took fourteen passes over 23m50s: three
passed and eleven failed before correction, ending with the full 206-job build.
Saved scans and the ten-call socket checkpoint took twenty invocations over
about 43 minutes: three passed and seventeen failed before the final 214-job
build. IPv4 send erasure/safety attempts failed at proof-search heartbeat
limits; its unused observer was removed. It remains an open caller obligation,
with a second architecture prepared using explicit tail-call stages to retain
shared continuations. This is a proof failure, not a mirror finding.
Counts and failed
passes are retained in the checkpoint history; current validation is above.
Failures were proof elaboration/simplification failures, not passes or mirror
findings. One earlier tactic loop was stopped by its verified PID and repaired.
Independent source reviews cover every listed checkpoint and its final deltas.
They corrected scope wording and identified an unused impossible KDF-failure
premise; that vacuous lemma was deleted. The maintenance review also corrected
the draft no-device frame argument to `modifyDev`'s actual no-op behavior.
The TX review checked the seven callers against the mirror and C, and clarified
that the per-call contracts compose through existing laws without exporting a
new sequence runner. No remaining correctness finding is reported for the
checked components. The completion/poll review checked all-input source order
and callback scope; it moved a generic conditional law into `Logged/Prefix`
and narrowed a docstring to the safety theorem's actual conclusion.
The socket review corrected saved-stamp and cache-flag scope wording, checked
all ten calls and their six exports, and reconciled the shared frame and
conditional-law moves. Its frozen source hashes match the validated tree.
C initializes cache/handshake before its
peer-counter increment, whereas the mirror increments/inserts first: the proof
follows the mirror, without claiming a C simulation or a lifetime counterexample.

**Ranked mirror-shape recommendations.** (1) Restore the documented pending-dump
deletion rejection: altitude-preserving fixture-domain enforcement. (2) If that
domain is expanded, retain the actual device lifetime in the cursor as C does:
altitude-preserving, requiring separate validation. (3) Keep named allocation,
deletion and same-object update boundaries: altitude-preserving operational
structure. No production history field is proposed; mirror edits remain outside
this campaign.

## R3 — cryptokey routing (in progress)

**Architecture decisions [AGENT 2026-10-13].** Use width-parametric prefix
arithmetic, one inductive Patricia tree and one pure insertion algorithm.
Contexts describe structural paths without adding another executable algorithm.
Keep raw addresses and original allocation order. At original mutation boundaries,
require freshness throughout the node store, including unrelated entries and
the opposite address family.

**Checked model and refinement.** `Prefix` defines leading bits and branch
selection arithmetically. `ArithmeticMirror` refines original `commonBits`,
`prefixMatches` and `choose`, retaining their branch effects and entire Worlds.
`Tree.Valid` requires bounded addresses/CIDRs and local edge constraints. The
independent flat-list `Winner` specification selects a longest matching owned
prefix. Pure lookup satisfies it without compression or node-ID uniqueness.
Strict CIDR growth bounds height by width plus one.

`Store.RepAt` gives exact node values, children and backlinks, allowing unrelated
store entries. `LookupMirror` proves that original `findNode` terminates normally,
returns the pure answer and preserves the Kernel; the actual 130-iteration bound
is discharged rather than assumed. Original `nodePlacement` likewise terminates
and yields an exact or stopped context, preserving the source's ordered exits
and allowing exact matches on ownerless nodes. External root linkage remains an
explicit caller obligation, not part of `RepAt`.

`Insertion` preserves validity/compression, replaces exactly the requested
canonical-prefix owner and accounts for all old/new node IDs by permutation.
The first fresh ID names the requested node; a needed ownerless intermediate
gets the second. Exact overwrite retains the old ID and raw address. Lookup
agrees with the independently updated flat binding list.

`MutationMirror` refines original empty-root insertion. `ChildMutation` and
`ChildStore` handle the root's immediate empty child; `DeepChild` and
`DeepChildStore` extend that case to arbitrary represented depth. Context
replacement requires the local root ID to remain fixed. Initial whole-tree
`Nodup` separates the changed parent from retained ancestors/siblings, while
`NodesBelow` protects them from fresh allocation. Exact source-stage contracts
compose allocation, peer-list append and connection; original traversal derives
the placement premise. The resulting state represents the existing pure
insertion, retains validity/unique IDs and links to the actual device root.
Original lookup from that root satisfies the updated flat-list `Winner`.

These mutation contracts distinguish normal allocation refusal from success;
arbitrary bad records may still Stop. `add` refusal preserves the Kernel.
The original `insert` wrapper advances the sequence once before either normal
outcome, including refusal. Exact equations preserve opposite root values and
any supplied opposite-family representation; existing opposite-root linkage
is preserved, not inferred. The statements describe exact endpoint states,
not mutation-event order. Peer-list append is exact without yet proving list
coherence or ownership.

`ListsMirror` gives the total original `listDel` endpoint as the source's
saved-peer fold, with pointwise filtered lists and unchanged identities and
allocation metadata. `ExactMutation` and `ExactStore` handle exact-prefix
replacement at arbitrary represented depth. They preserve the old node ID,
unmasked address and structure, allocate nothing, and append once to the
post-filter target list. They require representation and unique node IDs, but
no old-owner liveness or coherent peer-list premise. Total original `add`,
actual-root lookup and `insert` sequence advancement refine the same pure
insertion. This remains an endpoint refinement, not a resident-access observer.

`GraftMirror` stages the original selected-root nonempty graft; `GraftStore`
derives placement from the represented input and classifies every normal return.
It distinguishes first allocation refusal, second refusal with exact source
rollback, and the one-node/two-node success endpoints. The `insert` wrapper
retains its sequence increment in each case. Rollback advances the node frontier
once, restores node lookups under whole-store freshness, and filters that ID
from every resident peer list. It preserves any supplied tree representation;
whole-device equality and peer-list freshness are not assumed. Bad records may
Stop: these are normal-return endpoint contracts, not failed-prefix observers
or reachability claims for all alternatives.

**Remaining claim.** Successful nonempty-graft representation, post-success
freshness and lookup, deeper grafts, removal and general configuration histories
remain open. Parsed-input
bounds and history invariants still need propagation through all mutations.
Both packet paths follow R2. Owners are raw peer slots, not allocation or
cryptographic identities; no liveness/ownership claim follows from tree lookup.
The R2 orphan-owner replay above is a constraint on any proposed ownership
invariant, not yet an R3 counterexample. No R3 statement has been reshaped
and no Rule Zero finding is claimed.

**Effort and review.** Arithmetic, pure-tree and original traversal work took
5, 6 and 20 compile passes; pure insertion took 13. Empty-root insertion took
12 passes over 11m44s. Placement took 21 over about thirty minutes, including a
failed monolithic child-insertion attempt. Its staged replacement closed in
19 passes over eighteen minutes; that proof failure was not a mirror finding.
Arbitrary-depth insertion plus its wrapper took eight capped builds over 11m49s:
five passed, three failed during ordinary proof development, with no cap hits.
Exact-prefix replacement and list deletion took 21 capped builds over about
eighteen minutes: seven passed and fourteen proof iterations failed before
correction; the final full build passed 195 jobs. Selected-root graft endpoints
and rollback took 40 capped invocations over 35m28s: six passed and 34 failed
during proof compilation, with no cap hits; the final full build passed 208
jobs. Independent review corrected a draft `freeNode` contract that omitted
node residency, and wording that confused normal-return classification with
reachability. Successful graft refinement remains a follow-on, with no semantic
obstruction identified. Independent reviews checked each layer
and final terminal scopes; no correctness finding remains. Reporting corrections
separated root values from linkage, endpoint equations from event order, and
successful Worlds from failing Stops. Current validation is above; reproduce
with `capped -- scripts/in-bundle scripts/proof-gate`.

**Ranked mirror-shape recommendations.** None from these components. The named
arithmetic helpers and integer address encoding admit refinement without
production changes; correspondence to C byte layout remains informal.


## R4 — full-ring drop component (in progress)

**Checked component.** `Queues/PtrRing` applies the original `full` guard and
`produce` operation to each attempted item. A full ring rejects every attempt
and remains exactly unchanged. `Queues/Fill` proves symbolic filling and
consumption below the batch-retirement threshold. `Queues/FullRing` starts
from the original size-1024 ring and performs two literal produce/consume
pairs. Its logical count is zero, while slots 0 and 1 remain occupied. The
next 1024 guarded production attempts accept exactly 1022 items and reject
the final two. The final producer is 0, consumer head 2, consumer tail 0 and
logical count 1022; its logical FIFO contains exactly the accepted new items
in order, excluding the old consumed items and both rejected items.

`Queues/Enqueue` classifies normal returns of the complete original
`enqueuePerDeviceAndPeer`: success produces the item, `-ENOSPC` leaves the
ring unchanged, and `-EPIPE` means the entry ring was physically full and
remains unchanged. The earlier peer-queue capacity test retains priority;
peer-queue and packet-state updates may precede `-EPIPE`. Missing objects and
queue-work failures remain Stops. These contracts impose no ownership or
queue-validity premise and do not assert unchanged peer state.

**Receive-queue extension.** `Queues/PrevQueue` proves the
original dequeue, peek, peek-then-drop and enqueue laws. Logical contents are
`peeked.toList ++ items`; the cached item is not counted by the original
`count`. Normal peeks retain those contents, and dropping a present peek removes
exactly their head. The normal-return laws impose no validity premise. A
nonstub empty queue without a cached peek produces the original invariant Stop;
structurally coherent queues have ordinary dequeue and peek results.

`RxQueueView` records each resident peer's device epoch, allocation identity and
complete receive queue. `RxHelperFrames` proves successful-endpoint equality for
original `peerGet`, `peerGetMaybeZero`, `keypairGet`, `keypairPut`, `freeRxSkb`,
`counterValidate` and `receivedWithKeypair`; `peerPut` may delete a peer, while
each surviving entry retains its exact old view. The counter frame admits
malformed bitmaps and their Stops, without a 128-word premise. Fresh getter/update
and map-retention lemmas support later caller composition. These frames do not
establish internal access coverage, error-state equality or full `rxPoll` order.

[AGENT 2026-10-13] Track the complete receive queue together with epoch and peer
identity, and permit deletion in the release relation. This avoids treating
lifetime-safety contracts as queue-preservation contracts or silently assuming
reference ownership. Full poll observation is the next separate obligation.

**Complete receive-completion frames.** `RxQueuePrimitives` gives exact
consecutive-read equality and fresh getter/setter contracts over the full queue
view. `RxMaintenanceFrames` preserves queues through original endpoint/cache
and receive-timer operations, including their hidden-input checks and eager
peer reads. `RxTxFrames` composes the original staged-transmit, enqueue,
allocation and cleanup actions. `RxCompletionFrame` covers original source
lookup, statistics and the complete `consumeDataDone` body. Each post-state
resident retains its entry queue, epoch and peer identity; deletion is allowed.
The contracts make no assertion about a World after a Stop, internal accesses,
packet stores or delivery. The outer-poll observations below compose these queue frames.
No mirror code or clock/ownership premise was changed.

**Completion-frame effort.** Thirteen sequential capped local builds comprised
two passes and eleven ordinary compilation failures, all collected. The worker
had two provider interruptions during implementation and one during read-only
reporting; after each interruption, all dirty worktrees including nonignored
untracked files were preserved to snapshot refs before edits or rebuilds, with
branches and real indexes unchanged. The coordinator finished the component.
No cap was hit. The proof gate passes 239 build jobs and all 199 terminal
statements, including three new R4 exports. Stock fresh kernel replay, the
60-job model build and the 93-test unit tier pass. Independent review of the
four frozen modules, exports and report/register found no unresolved issue;
reviewed source hashes matched. Named temporary logs and axiom outputs were
removed after collection. Reproduce with the proof gate command above.

**Outer poll and stack callback components over 2c7a076.** The following describes
the earlier checked component; the f45bde8 carry and invalidated chronological
claim are recorded immediately below. `RxPollPrimitives` names exactly
original peek/cache and two-getter drop sequences. `RxPollPrefix` observes the
outer poll body's explicit drop site, emitting only after the update succeeds.
Its exact local run law appends one ID on success and none on failure. Its
complete erasure preserves every result, full success World and original Stop.
`RxPollOrder` proves that the retained removal log is an initial segment of the
current resident's entry queue, even if a subsequent helper or callback stops.
No queue-coherence, reference-ownership or normal-return premise is imposed.
The invariant is `entry = removed ++ remaining`, with each resident's current
queue equal to `remaining`; exact queue retention permits deletion and the next
successful getter restores residency. Repeated entry IDs remain admitted, so
this is not a no-duplication theorem. This log does not observe operations
inside its opaque arbitrary callback.

`Logged/Projected` permits proof-side local accumulators to carry extra data
while erasing to the original loop. `RxPollGro` uses it to carry GRO entries
with the local `workDone` ordinal, skb value and exact bytes returned by the
original `consumeDataDone`. A successful `some bytes` return emits that buffer
entry; a `none` return, including keepalives, emits none. In particular,
`rxPollFree = false` is not treated as delivery. The complete tagged observer
erases to original `rxPoll` with the actual `forM deliverInner` callback.
`GroCallback` emits immediately before each original `deliverInner` call;
failure retains that call's entry but never fabricates visits to the remaining
suffix. `RxPollGroOrder` proves for every input World and outcome that callback
entries are a prefix of the exact tagged completion buffers. The accumulator
invariant equates the logged buffers with the local GRO list; before flushing,
no callback entries exist. Full-budget Stop therefore keeps buffered obligations,
and a callback failure keeps the unvisited suffix. Entry to the stack is the
observed boundary, not a claim that the stack accepts the packet.

[AGENT 2026-10-13] Keep original queue removal and GRO/stack callback observations
separate at their actual source boundaries, with failure-retaining histories.
Use explicit ordinal/skb/payload records for buffered entries, rather than
identifying occurrences by nonce or payload equality. All additions are proof-side.

**GRO audit carry and Rule Zero finding (f45bde8).** The original wording was
"callback entries form a prefix of tagged successful completion buffers",
exported as `original_poll_callback_prefix` over `2c7a076`. Real GRO invalidates
that chronological statement. `GroSafe` retains its original definition; the
false whole-poll theorem is retired, not silently assigned a different meaning.

`docs/proof-campaign-replay.py r4-gro-reorder` constructs six operations with
explicit records. The batch receives nonce 0 carrying a one-byte ACK-only TCP
segment (source port 40001, destination 80), then nonce 1 carrying a SYN on a
different flow (source port 40002, destination 443). Both share one peer and key
allocation lifetime. `DeliveryOrder/ReplayGro.lean` checks original
`executeTrace trace false` acceptance, identical checkpoint/acceptance-observer
JSON, exact validator history `(lifetime, 0), (lifetime, 1)`, and the input
ciphertexts against that lifetime's receiving key. The actual output appends
the SYN's RST encrypted with outgoing nonce 1, then the ACK's RST with nonce 2;
both byte-exact ciphertexts also occur in the original runner's final observable
rows. Peer/key lifetime preservation, counters and receive-store cleanup are
checked. These are generated accepted mirror inputs, not a Linux capture or
proof of kernel schedule reachability.

The source mechanism is GRO selection: the first segment remains held while
the SYN enters the normal list; completion appends the held segment behind it.
The original-helper theorem `original_gro_held_then_normal` proves precisely
`napiGroReceive H; napiGroReceive N; napiGroFlushAll = callback [N,H]`, assuming
the original byte classifier holds H and takes N normally. This is a design
nuance at the post-GRO stack boundary, not evidence that WireGuard's receive
queue or decrypt FIFO reversed. C source agrees on the different-flow inputs,
with a nonempty held ACK payload and a header-only SYN
(tcp_offload.c:261,318,379-381; gro.h:528;
dev.c:6385,6388). Two other source-reading concerns remain separate and
unconfirmed: the classifier ignores the zero-payload `len < mss` flush, and it
does not inspect an existing same-flow held segment on the normal arm. Neither
is reported as a differential finding.

`Queues/GroState` carries tagged `rxList`, `rxCount` and `held` through all four
original helpers. Their erasure and the complete tagged poll's erasure preserve
every result, successful World and Stop, without a validity premise. Callbacks
now run at batch flushes inside the loop and at completion. The removal-prefix
theorem therefore explicitly requires every successful callback to `RetainsRx`;
the old arbitrary-callback premise is no longer valid. The concrete stack's
queue-frame discharge remains open. The completion event still means a
successful `consumeDataDone` output, before GRO admission; a second held offer
can be observed before GRO refuses it. It is not silently classified as a drop
or as a resident queued item.

The distinct replacement predicate `SelectedGroSafe` specifies a visited prefix
of normal completion offers followed by held offers, each class in its source
order. Its universal whole-poll theorem is still open. The original per-list
actual-callback visited-prefix theorem remains checked, including a failed
call's entry and the unvisited suffix. Reproduce the accepted witness with:

```sh
capped -- scripts/in-bundle sh -c 'python3 -B docs/proof-campaign-replay.py r4-gro-reorder | lake env lean --run Leanux/Proofs/WG/DeliveryOrder/ReplayGro.lean'
```

[AGENT 2026-10-13] Preserve the failed chronological predicate and finding,
carry observers to actual GRO state, and give any selected-order theorem a
distinct name. Input/output occurrence provenance and pipeline conservation
remain obligations rather than consequences of erasure.

**Audit-carry local validation.** The current R4 target passes 156 jobs and
contains 26 terminal theorems: the former chronological poll export is retired
and the original-helper reorder equation has a distinct name. Sixteen capped
build/probe invocations comprise five passes and eleven ordinary compilation
or assertion failures, all corrected and collected. The replay's final run
passes every exact assertion above. Independent read-only review of its frozen
generator and checker found no correctness defect and confirmed the scope is
post-GRO stack order on generated accepted mirror inputs. No interruption or
cap failure occurred. The subsequent whole-tree gate and fresh kernel replay pass, as recorded
in the progress section.

**Remaining local bridge.** The complete observers still have separate
contracts: callback-framed entry-queue removal-prefix order and exact tagged
GRO erasure. Besides the selected-order invariant, two links remain open:
buffered tags must form
a subsequence of `rxPollGro`'s own removed tags, with distinct ordinals, and
those removed tags must agree with the `rxPollRemovals` log. Event counts and
composition with receive enqueue and recorded scheduler activations also remain
open. The actual
stack callback may perform other work internally; its entry observer claims
only this supplied `forM`'s entry sites. No packet-store emptiness, no-loss,
whole-schedule ordering or speculation/rollback claim follows from these local
components. The scheduler's discarded activation trials must eventually discard
history together with their trial Worlds.

**Earlier outer-poll effort and validation (2c7a076).** Thirty sequential capped local
build/elaboration invocations over about twenty-three minutes comprised eleven
passes and nineteen ordinary compilation failures, all collected. The failures
were proof elaboration, tuple/continuation matching and simplifier issues; none
was a cap failure or a mirror finding. No process was interrupted. The final
`capped -- scripts/in-bundle lake build Leanux.Proofs.WG.DeliveryOrder.Statements`
passes 153 jobs and includes all 26 R4 terminal declarations. The complete proof
gate passes 246 jobs and 206 terminal statements with only permitted axioms;
stock fresh kernel replay passes. The model build passes 60 jobs and the unit
tier passes 93 tests in 21.539 seconds with one skip. Independent source and
contract review found no unresolved defect; the frozen file hashes matched.
The review confirmed that the two remaining correspondence links are explicit
limitations, not consequences of erasure alone. Temporary compiler and check
logs were removed after collection. No QEMU, differential check, mirror edit,
integration into main or push was performed.

**Measurement and formal scope.** The landed
[W7 full-ring tier](2026-10-13-w7-full-ring-tier.md) records the Linux/mirror
measurement provenance: two prior consumed slots remain occupied, and all
1024 producers run before worker consumption. The new kernel theorem is a
closed ring-operation witness, not a replay or refinement of that whole
recorded execution. Its separate original-enqueue theorem does not yet
compose the ring witness with a real peer queue or an accepted runner trace.
No mirror change was needed. Whole recorded-schedule delivery,
worker-local ownership and pipeline conservation remain open, following R2's
remaining caller/lifecycle closure. This component establishes no packet
arrival, cryptographic, scheduler-fairness or delivery-order claim.

[AGENT 2026-10-13] Use symbolic filling and pointwise slot algebra rather than
reducing 1024 concrete array updates in the kernel. The proof still uses the
original ring operations; this makes the witness cheap to recheck without
changing the mirror or adding trusted computation.

**Receive-queue validation and effort.** The full `LeanuxProofs` build passes
234 jobs, including all sixteen R4 terminal theorems (nine new). The proof gate
passes all 192 statements with only permitted axioms. Independent review of the
frozen source, original queue semantics and report found no unresolved issue.
Ten sequential capped build invocations over about twelve minutes comprised
four passes and six ordinary proof-compilation failures, all collected; no cap
was hit and no process was interrupted. The failures concerned tactic branch
scope, projection unfolding and generated helper matching, not mirror changes.
No QEMU, differential check or recorded replay was run for this local component.
The named temporary compile log was deleted after collection. Reproduce with
`capped -- scripts/in-bundle scripts/proof-gate`.

**Full-ring validation and effort.** The complete `LeanuxProofs` build passed 224 jobs;
seven R4 terminal theorems are imported by the root. The proof gate passes all
174 terminal statements with only permitted axioms; stock kernel replay, the
60-job default build and 93-test unit tier pass. Independent review checked
the code, source correspondence, report and register; its table-format finding
was corrected, and no correctness finding remains. Reproduce with
`capped -- scripts/in-bundle scripts/proof-gate`. Twelve capped build
invocations over about twenty minutes comprised two passes, nine ordinary
proof-compilation failures and one deliberately terminated large-reduction
attempt; no cap was hit. The writer initially resumed after that deliberate
interruption without the required preservation step. Work then stopped, the
coordinator snapshotted all six dirty worktrees including untracked files with
branches and real indexes unchanged, and implementation resumed only after
preservation. The symbolic replacement compiled without large reduction.
No QEMU, differential check or new recorded replay was run in this slice.

**Ranked mirror-shape recommendations.** None from these components. Original
physical-slot fullness and batched retirement explain the ring witness, and
proof-side named boundaries plus projected accumulator erasure handle the poll
without a mirror change.


## R5 — key lifetime enforcement: Rule Zero findings

**Disposition.** The original unconditional encryption-age and post-zero-use
claims are false in the mirror's accepted-record domain. Authenticated reception
also precedes the packet's wire-counter limit check. These findings resolve R5
under Rule Zero; the original statement remains unproved. The thirteen positive
local contracts below describe the boundaries the code actually enforces.
They do not assert universal transport of TX admission certificates through
all subsequent operations, or whole-run AEAD observation coverage.

| Original wording | Checked result and reason |
| --- | --- |
| No data encryption or decryption under a key older than `REJECT_AFTER_TIME` | RX attempts require an actual unexpired recorded comparison. TX checks age at staging; an already admitted transport keepalive can encrypt after a later recorded expiry. |
| No use past `REJECT_AFTER_MESSAGES` on its counter | RX checks the stored receiving counter before AEAD, then checks the packet's wire nonce during replay validation. Nonces R and R+1 authenticate before rejection. This refutes the wire-nonce reading, not the stored-counter guard. TX staging certificates bound assigned nonces strictly below R. |
| No peer key-material use after its zero timer until a new handshake | The timer queues clear work. Even after that work removes the published slots and index, a queued packet's reference retains the same material until encryption/transmission releases it. |

The time witnesses use **type-4 transport keepalives with empty plaintext**,
not nonempty inner IP payloads. All are generated/reconstructed accepted mirror
inputs, not new Linux captures or evidence that Linux can realize their schedules.
The mechanisms match Linux `receive.c:242–331`, `send.c:162–219,342–414`,
`noise.c:112–177` and `timers.c:105–133`: authentication before replay validation,
admission-time TX checks, and reference-counted clearance. We judge these
boundaries to be design nuances, not demonstrated Linux security defects.

**Architecture and refinement.** `KeyTimes/Clock` proves exact original
`birthdateTest`/`branchExpired` executions, including wrapped signed64 deadlines,
actual clock-consumption Worlds and comparison operands. Equality is expired.
`Receive` factors original decryption by equality and recovers the successful
entry key lookup, validity, stored counter and unexpired clock. The later original
validator's true return implies a wire nonce below R, without bitmap-shape premises.

`ReceiveAttempts` emits immediately before actual AEAD, after the original getter,
guard, allocation and fragment checks. All-input erasure preserves the complete
World or exact Stop. Every event satisfies admission, including failed tags;
exact singleton coverage and the failed-authentication endpoint prevent a
vacuous empty-log result. `Staging` similarly emits after the original allocation
map, immediately before `createData` receives its IDs. Certificates retain actual
key/clock/allocation executions and bounded assigned arguments on a later Stop.
They do not prove the later store contents or immutable material transport.
`ZeroTimer` frames the entire transport-keypair store through the original callback.

The shared `Logged/TimerPass` observer records completed original timer, clear,
send-worker and crypt-scheduler units, with exact result/World/Stop erasure.
The runtime witnesses reconstruct the literal next-operation reset from an
accepted runner checkpoint, execute the original advance where present, and
compare the observed timer endpoint with the accepted runner's final Kernel.
Crypt observations are scheduler calls, not per-packet AEAD events. Each time
witness checks the retained packet/material and a newly appearing exact ciphertext.

**Counter witness.** `r5-rx-wire-limit` reconstructs the tracked five-operation
session and an existing authenticated nonce-R packet. `r5-rx-wire-past-limit`
derives that same session with the harness's Noise helper, checks its response
against the tracked response, and generates authenticated nonce R+1. Here
`R = 18446744073709543486`. Both original and validator-observed runners accept
with equal JSON. Their final stored-counter operands are `[0,R]`; AEAD succeeds;
the subsequent validator rejects `[R,R]` or `[R+1,R]`; the acceptance history
is empty. This is decryption followed by an explicit drop, not delivery.

**Time witness.** `r5-delayed-encryption` establishes a session born at 132 seconds
and uses two nonempty receives to set the keepalive timer's second-fire flag.
The first callback admits nonce 1 at 311 seconds, with age operands
`[312000000000,311000000000]`, and rearms the timer. The next callback records
`[312000000000,322000000000]`, invalidates sending, stages another keepalive and
queues a handshake. Before that handshake runs, the crypt worker encrypts and
transmits the earlier packet using unchanged key material. Exact unit order,
packet identity, complete key value, reference counts and ciphertext arrival
are asserted against original executions.

**Post-clear witness.** `r5-coherent-post-clear` follows the same seven-operation
construction, with the second expiry comparison at 673 seconds. The zero timer
(expiry 132+540=672 seconds) and actual clear worker then run before crypt.
After clear, all three peer keypair slots are empty, the key index is absent,
and handshake state is zero. The same allocated packet retains exactly one
reference to the same key material. Its new ciphertext appears before the
queued handshake worker; transmission removes the packet and final key reference.
No new handshake intervenes. The older `r5-post-clear-transport` remains a separate
five-operation legacy-mode witness with deliberately incoherent coarse/jiffies
clocks and disabled arm records; its provenance is not upgraded by the new case.

The two new time variants enable arm records and check monotonically ordered
coarse-nanosecond and UInt64-jiffies words, exact timer delays and the relation
`J(t) = 2^32 - 75000 + 250*t`. Their windows end at 323 and 674 seconds via
site 128 (kind 310). Queue-work and timer identities are explicit and stable.
The later TAI read also advances by the elapsed coarse seconds. This arithmetic
coherence does **not** establish kernel scheduling reachability; the original
runner's accepted domain is the claim being tested. Cache-clock records remain
disabled. The second callback may run long after its expiry, as accepted by the
mirror's recorded timer-window rule.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-rx-wire-past-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
python3 -B docs/proof-campaign-replay.py r5-delayed-encryption |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-coherent-post-clear |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
```

For the earlier cases, use `r5-rx-wire-limit` with `Replay.lean`, or
`r5-post-clear-transport` with `ReplayPostClear.lean`.

**Effort and validation.** Earlier local proof checkpoints used 17 receive/time
builds (10 ordinary failures), 10 staging builds (6 failures), 4 RX-attempt builds
(1 failure), and 4 timer-observer builds (2 failures); their gates, stock kernel
replay, model build, units and independent reviews passed. This extension used
13 replay executions: eight passed, two failed on Lean syntax, and three rejected
incorrect generated record placement/jitter. All five final reproductions pass:
0.838s, 0.862s, 8.566s, 8.437s and 2.018s respectively for boundary, strict counter,
delayed, post-clear with arm records, and legacy post-clear. Original/observed
JSON equality and all assertions pass in each. One provider interruption left
no running job; every dirty worktree was preserved to snapshot refs before
further edits. No cap was hit. The first checkpoint gate failed because its forbidden-token
scan found the word `admit` in a replay diagnostic string; that wording was
corrected. The proof gate now passes 246 build jobs and all 206 terminal
statements with permitted axioms only. The unit tier passes 93 tests in 22.231s
with one skip. Stock fresh kernel replay and the 60-job model build pass.
Independent source, assertion and report review found no unresolved defect;
its wording findings were corrected and frozen hashes matched before commit.
The mirror remains byte-identical to main `2c7a076`. No QEMU, differential
check, integration into main or push was performed.

[AGENT 2026-10-13] Resolve R5's false original statement through the accepted
counterexamples permitted by Rule Zero. Keep the positive local contracts at
their proved boundaries; stronger replacement transport theorems are follow-on
work, not claims of this result. Distinguish generated clock arithmetic from
measured kernel execution.

**Ranked mirror-shape recommendations.** None is required for these findings.
The landed signed clock helpers and operand-bearing branches expose the relevant
semantics. Adding a proof-motivated age guard to the later encrypt worker would
change the C's control flow and is not altitude-preserving.
