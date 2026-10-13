# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`. The
[charter](2026-10-13-charter-proof-campaign.md) defines the campaign. Main
`2c7a076` includes both named prerequisites and has been merged into this
worktree on the user's landing instruction. The proof gate passes over that
commit, including the R4 full-ring and receive-queue components, R5 staging
admission, RX-attempt coverage and both R5 replay witnesses. All registered
components are current.
The mirror and kernel match it exactly; R4 and R5's dependent work is now unblocked. No integration into main, push, differential check or guest run.

| Result | Progress |
| --- | --- |
| R1 anti-replay | Complete with the intentional inclusive-floor correction; recorded replay and independent review checked. Seccomp frame carry checked. |
| R2 lifetime safety | Store identities, failure-retaining allocation/release and caller composition cover session/rotation, peer creation, receive entry/maintenance/completion, receive polling with the actual stack callback, transmit entry, TX staging, decrypt iteration and ten socket/cache/loopback calls; stale-cursor finding checked. Remaining callers, lifecycle and whole-run internal-access coverage remain in progress. |
| R3 cryptokey routing | Original prefix arithmetic and total longest-prefix lookup over represented trees, pure insertion, original empty-root, arbitrary-depth empty-child and exact-prefix insertion with sequence wrappers, and total original placement proved. Selected-root graft normal endpoints and rollback effects checked; successful graft representation, general mutation/history and path refinements remain open. Path proofs follow R2. |
| R4 delivery | The full-ring witness, original enqueue refusal projection, original PrevQueue FIFO/peek/drop laws and retained receive-queue helper frames pass the gate and independent review. Complete receive-completion retention passes the gate and independent review. Whole-poll and recorded-schedule delivery/conservation remain open. |
| R5 key lifetime | Original clock/operand equations, successful RX decryption admission, validator wire limit and zero-timer transport-store frame pass the gate and independent review. TX submission certificates and exact timer-pass observation pass the gate and independent review. Accepted replays show nonce R decrypting before rejection and a packet-held key used after clear in synthetic, incoherent-clock legacy mode. RX-attempt admission, exact coverage and failed-tag endpoints pass the gate and independent review. Admission-to-encryption transport, whole-run attempt composition and coherent-clock post-clearance exclusion remain open. |
| R6 flood resistance | Not started. |

**Current validation.** The full proof gate passes 239 build jobs and 199
terminal statements (ReplayWindow 15, R1 9, R2 116, R3 27, R4 19, R5 13), with only permitted
axioms. Stock `leanchecker --fresh Leanux.Proofs` passes. The default model
build passes 60 jobs; the unit tier passes 93 tests in 22.711 seconds with one
skip. The R1 explicit-record witness and both R2 checkpoint variants pass on
`2c7a076`, with original/observed JSON equality; the R1 history remains
`[(1, 8200), (1, 72)]`. The reconstructed/synthetic streams now supply the
required site-128 end-of-wait records, without adding timer sections. The new
five-operation R5 wire-limit replay also passes with original/observed JSON
equality and no validator acceptance. The new synthetic post-clear replay passes
its original/checkpoint equality, timer-unit and retained-key assertions, as
detailed below.
Independent reviews cover peer creation, the seccomp carry, mixed enqueue,
decrypt execution, keypair/packet releases, ambient caller composition,
allocation and release-bound composition, session creation and rotation,
the mixed peer-creation bridge, receive entry, maintenance, completion and polling,
TX staging, pure trie
insertion, original empty-root and arbitrary-depth empty-child insertion with
its wrapper, exact-prefix replacement, list deletion, placement and selected-root
graft endpoints/rollback, saved-peer scans, the ten-call socket family,
transmit entry, actual stack/poll composition, the prerequisite carry, and the
full-ring, receive-queue and complete receive-completion components, R5 receive/key-time, RX attempt and TX admission components, and both
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
wrong; receive entry preserves the ENOSPC Stop and EPIPE's pure callback.
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
The poll retains both `dropPeeked` getters, releases keypair then peer then RX
packet, and invokes its callback only after the final peer update. Its budget
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
packet stores or delivery. Whole-poll observation remains a separate obligation.
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

**Measurement and formal scope.** The landed
[W7 full-ring tier](2026-10-13-w7-full-ring-tier.md) records the Linux/mirror
measurement provenance: two prior consumed slots remain occupied, and all
1024 producers run before worker consumption. The new kernel theorem is a
closed ring-operation witness, not a replay or refinement of that whole
recorded execution. Its separate original-enqueue theorem does not yet
compose the ring witness with a real peer queue or an accepted runner trace.
No mirror change was needed. Whole-poll and recorded-schedule delivery,
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

**Ranked mirror-shape recommendations.** None from this component. Original
physical-slot fullness and batched retirement already explain the witness.


## R5 — receive admission and key-time boundaries (in progress)

**Checked component.** `KeyTimes/Clock` gives exact run equivalences for
`birthdateTest` and `branchExpired`: the original clock consumer's result,
the wrapped `Int64` deadline, the signed comparison, both integer operands
and the complete comparison-record World. Equality is expired. No range or
no-wrap premise replaces the original operation. The contracts also hold in
placeholder mode with that consumer's value; an explicit-record execution
uses its consumed clock word.

`KeyTimes/Receive` factors the original `decryptPacket` definition by a
checked equality, keeping the rejection expression and remaining body intact.
Every successful authenticated decryption recovers its original entry keypair
lookup, receiving validity, stored receiving counter strictly below
`REJECT_AFTER_MESSAGES`, and the exact original clock-read execution after
the two preceding branch records. The clock's comparison must be unexpired.
The guard contract separately holds without assuming successful authentication.
Those two contracts alone do not observe all AEAD attempts; the new observer
below covers that local boundary. The later
original `counterValidate` can return true only for a wire nonce strictly
below the limit, without a bitmap-shape or entry-residency premise.

**RX attempt extension.** `KeyTimes/ReceiveAttempts` captures
the original key lookup and rejection-guard executions and emits immediately
before the original AEAD suffix, after allocation and fragment checks. The
observed packet and captured key determine the exact wire nonce, ciphertext
and key bytes passed to AEAD. All-input erasure retains the complete original
return World or exact Stop. Every event carries a valid receiving key, stored
counter below R and an actual unexpired recorded-clock execution, with no
residency invariant or authentication-success premise.

Coverage is an exact equation, not only a conditional property of emitted
events: successful original getter, false guard and `skbCowDataRx = true`
produce exactly one event. A separate failed-tag equation returns `none`,
keeps that same event, and identifies the exact four preparation/authentication
branch records after allocation. Guard rejection and allocation failure still
follow the source before the event. The shared failure-retaining observation
semantics preserve it when a later enclosing continuation stops. This is one
original `decryptPacket` call; composing attempt histories through workers,
scheduling and the whole runner remains open. It neither bounds the packet's
wire nonce nor proves acceptance or delivery.

`KeyTimes/ZeroTimer` projects the entire transport-keypair store, including
key bytes: the original zero-key timer callback preserves it on every normal
return. Its live, unqueued arm queues separate clear work; this frame proves
neither that the worker ran nor that later key use is excluded.

**Checked TX admission component.** `KeyTimes/Staging` follows the
original `sendStagedPackets` and emits one batch after its original
`packetsCb.mapM newTxSkb` succeeds, immediately before `createData` receives
the returned IDs. All-input erasure preserves the entire normal-return World
and exact Stop. Every emitted certificate contains successful executions of
the actual original key getter, clock consumer and allocation map, the
initial key's sending validity and unexpired signed deadline, and the
peer/keypair fields and strict nonce bound of every allocated argument.
The observation survives a failure in subsequent submission. Empty staging,
key/age rejection, nonce rejection and allocation failure follow the original
paths; no certificate is emitted before allocation completes. Thus an empty
observation does not rule out partial allocation effects before a Stop.

These certificates are attached to source arguments and the completed map,
not to hypothetical comparison values. They do not establish final packet-store
contents or immutable key material through later work. The source increments
`sendingCounter` before checking the assigned nonce: admitting nonce `R - 1`
may therefore leave the mutable counter at `R`. A strict bound on that later
counter is not the admission contract. Shared `Logged/Capture` supplies exact
run witnesses and erasure/contracts; `Logged/PrefixLoops` supplies the list
accumulator invariant. Neither adds history to mirror state.

**Original wording and precise boundary.** The charter says no encrypt or
decrypt under a keypair older than `REJECT_AFTER_TIME` or “past
`REJECT_AFTER_MESSAGES` on its counter.” The proved receive wording is:
*every AEAD attempt passes the key's stored-counter and recorded-age gates;
subsequent validator acceptance passes the packet's wire-counter gate*.
The interpretation “wire nonce strictly below R before decryption” is false.
The witness below uses equality at R, so it does not refute a strict
“wire nonce greater than R” reading or the stored-counter reading. This is
an intentional separation visible in Linux `receive.c:242–331`, not a mirror
mismatch. TX checks age and assigned nonce while staging; carrying that
admission to the later encryption call remains open. The unconditional
post-zero-timer prohibition is false for accepted legacy-mode mirror inputs,
as the separate post-clear replay below shows. Exclusion for physically
coherent clocks remains unproved.

**Concrete boundary replay.** `r5-rx-wire-limit` reconstructs a five-operation
explicit-record input from `CONTENDED_ROAM_CMP`, the existing
`d2_rx_reject_after_messages` ciphertext, and synthetic monotone end-of-wait
bounds. It is not a new Linux capture. The original runner and the proved
validator observer both accept it and produce equal JSON. At the final
operation, the stored-counter check has operands `[0, R]` and passes; the
age comparison has operands `[312288452009, 132804484259]` and is unexpired.
AEAD succeeds and the decrypt worker marks the packet decrypted. The later
validator sees operands `[R, R]`, rejects the wire nonce, and RX polling
records the counter-invalid drop. The acceptance history is empty, so this
is successful decryption followed by rejection, not delivery or an accepted
counter at the limit. Here `R = 18446744073709543486`.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-rx-wire-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
```

**Validated receive/key-time checkpoint.** The reproduction passed with exit 0 in 0.837 seconds.
Six terminal theorems compile and the complete `LeanuxProofs` target passes
228 jobs. Seventeen capped build invocations comprised ten ordinary proof
failures and seven passes; no cap was hit and no process was interrupted.
The proof gate passes 180 terminal statements with only permitted axioms;
stock kernel replay, the 60-job model build and 93-test unit tier pass.
Independent review checked the exact source contracts, statement scope and
replay provenance with no correctness finding. Its stale validation-label
finding was corrected by this completed-check update. Frozen code hashes
match the review. No mirror, kernel or harness change was made.

[AGENT 2026-10-13] Keep this first R5 layer at original operation boundaries:
exact clock executions, receive admission and the callback's immediate store
frame. Defer TX admission transport and post-clearance schedule exclusion
instead of inferring them from the identity frames.

[AGENT 2026-10-13] Certify TX staging at its actual completed allocation /
submission boundary using exact captured original runs. Keep later store,
identity, key-material and scheduled-encryption transport as explicit follow-on
obligations; preserve source early-return and failure behavior.

**TX extension validation.** Eight R5 terminal theorems compile, and the full
`LeanuxProofs` target passes 230 jobs. Ten capped build invocations over about
16 minutes comprised six ordinary proof failures and four passes; all exits
were collected, no cap was hit and no process was interrupted. The extension's
combined checkpoint passes the proof gate (183 statements, 231 build jobs),
stock kernel replay, the 60-job model build and 93-test unit tier.
Independent review found no mathematical or source-refinement defect. Its
duplicated report-paragraph finding was corrected before handoff.

[AGENT 2026-10-13] Observe original receive attempts immediately before AEAD,
using exact getter/guard execution witnesses and singleton coverage independent
of authentication success. Keep whole-run composition separate from this local
source contract; do not infer a wire-nonce bound from the stored-counter gate.

**RX attempt validation.** Thirteen R5 terminal theorems compile, and the full
`LeanuxProofs` target passes 235 jobs. Four capped builds comprised one ordinary
proof failure and three passes over 4m57s; every exit was collected, with no
cap hit or interruption. The proof gate passes all 196 terminal statements
with only permitted axioms; stock kernel replay, the 60-job model build and
93-test unit tier pass. Independent review of the frozen source and report
found no unresolved issue. The named build log was removed after collection.

**Rule Zero: post-clear use in the accepted-input domain.** The charter's
wording forbids peer key-material use after its zero timer fires until a new
handshake. `r5-post-clear-transport` is an accepted five-operation input:
the first four operations establish the captured session, and `wg_observe`
replays persistent keepalive admission, the zero timer, the actual clear
worker, then encryption and transmission. The admitted nonce is 1. Immediately
after clear, the current/next/previous peer slots are empty, its handshake
state is zero and the keypair index is gone. The packet still holds lifetime
1 with reference count 1 and exactly the original key material. The later
crypt scheduler produces the expected ciphertext under that retained key,
then releases both packet and keypair; no new handshake intervenes.

This is a **synthetic runner-domain finding, not a Linux execution**. It
deliberately copies an unexpired coarse-clock read while the end-of-wait
jiffies word makes both timers due, and sets `arm_records=false` and
`dst_cache_records=false` for legacy replay mode. The admission comparison
is `[312288452009, 132288452009]`; the end bound is 135005. Those clocks are
not asserted physically coherent. The mechanism of retaining material while
an in-flight packet owns a reference matches `keypair_put`/`keypairs_clear`
in Linux `noise.c:112–177`; it is reference-counted lifetime behavior. This
witness establishes neither a Linux security bug nor reachability with
coherent recorded clocks. A clock/schedule premise is needed for that stronger
interpretation; the callback's name alone cannot establish revocation.

The replay asserts full original/checkpoint JSON equality. `Logged/TimerPass`
additionally observes completed original timer/worker/scheduler calls, with
all-input result/World/Stop erasure and an exact unit-emission equation.
From the original session checkpoint, the replay reconstructs the literal
next-operation reset and runs that observer at the original timer-pass entry.
It checks the after-clear store, packet and key bytes, scheduler entry,
derived ciphertext and final releases. Its final Kernel equals the accepted
runner checkpoint, and only the caller's end-of-wait word remains. Original
branch order independently shows clear's retained reference, encryption,
transmission and final keypair release. Crypt observations include the final
empty scheduler call; they are not per-packet AEAD events.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-post-clear-transport |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayPostClear.lean
```

The original-run probe and the completed assertion replay passed. The timer
observer took four capped module builds: two ordinary proof failures and two
passes; the standalone assertion replay had one syntax failure before its
passing run. No cap hit, interruption or mirror change occurred. The combined
gate, stock kernel replay, model build and unit tier pass. Independent review
checked source correspondence, exact entry reconstruction, assertions and
provenance; no finding remains.

[AGENT 2026-10-13] Keep the post-clear finding scoped to the accepted legacy
record domain and expose its incoherent-clock trigger. Use exact timer-unit
observations to inspect the retained reference; do not infer Linux reachability
or a general AEAD event history from it.

**Ranked mirror-shape recommendations.** None from this component. The
landed signed clock helper and operand-bearing branch expose the required
semantics directly. A proof-specific age guard in the later encryption
worker would alter the C's control flow and is not altitude-preserving.
