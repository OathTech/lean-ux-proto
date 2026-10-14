# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`; governed by
[the charter](2026-10-13-charter-proof-campaign.md). Both prerequisites were
carried from `2c7a076`, then the audit at `f45bde8` and documentation-only
`a39aded`. The mirror is byte-identical to main. Checked components are current
over `a39aded`, including the six-call R2 handshake-send extension. Open
obligations below remain explicit. No integration into main,
push, differential check or guest run has been performed by this campaign.

| Result | Disposition |
| --- | --- |
| R1 anti-replay | Complete: uniqueness and the intentional inclusive-floor correction, with pure and accepted-run witnesses. |
| R2 lifetimes | Endpoint identity and failure-retaining access contracts cover the listed call families. Whole-run caller/lifecycle/scheduler closure and saved-reference ownership remain open. The stale-cursor finding is checked. |
| R3 routing | Prefix arithmetic, represented-tree lookup and the listed insertion cases are checked. Removal, general mutation/history and packet-path refinements remain open. |
| R4 delivery | W7's two full-ring drops are explained. An accepted replay refutes chronological post-GRO stack order. Current per-poll selected order, removal/provenance and concrete callback frames are checked; pipeline conservation remains open. |
| R5 key lifetime | Resolved under Rule Zero by counter-limit, delayed-encryption and post-clear-use witnesses, with 13 local positive contracts. |
| R6 flood resistance | Cookie exclusion proved at the original call boundary; accepted 19-retry/20-initiation episode resolves the literal limit through Rule Zero. Six terminal contracts. |

**Current validation.** `a39aded` has mirror source unchanged from `f45bde8`.
The proof gate passes 274 jobs and 252 terminal statements
(ReplayWindow 15; R1 9; R2 140; R3 34; R4 35; R5 13; R6 6), using only `propext`, `Classical.choice` and `Quot.sound`.
Fresh stock kernel replay passes, as do the 60-job default model build and
94-test unit tier (21.921 seconds; one skip). Independent frozen-source
and scope reviews have no unresolved correctness findings in these components.

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle lake build
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation harness.test_trace harness.test_wg harness.test_linux
```

Unchanged runtime witnesses were not rerun for later proof-only extensions.
All nine cases passed the audit carry; the retry and two current time witnesses
also passed the stronger complete-advance check. Generated R4–R6 streams prove
accepted mirror behavior, not Linux capture or schedule reachability. Distinct
reproduction commands and provenance are retained in each result below.

**Carries and review history.**

| Carry | Preserved correspondence and effort |
| --- | --- |
| Seccomp/shared frames | Seven-field WG projection, child fixture and prefill success/error paths; no seccomp-free premise. BPF continuation sharing and loop-counter progress. 17 compile passes over 36m34s, with independent source and architecture review. |
| Prerequisites (`2c7a076`) | Exact comparison operands and validator World, signed/unsigned clock operations, both timer-arm signed-gap failures, occupancy/record bounds and kind-310 peek/read validation. About 40 minutes and 12 local builds; earlier transmit/stack work used five attempts. |
| Audit (`f45bde8`) | Index decisions and missing-device failure; cookie rotation clock/randomness; signed MTU/initiation fields; receive-refusal cleanup; actual GRO state and callback timing. Fourteen root, six R2 and sixteen R4 build/probe calls preceded passing gates and nine replay checks. The failed chronology theorem was retired explicitly. |

A prerequisite-carry worker interruption required preserving all dirty worktrees
before resumption. Its build handle was unavailable; its log reported a normal
proof failure, and later collected builds and gate passed. No arbitrary-record
or malformed-World case was excluded. Audit failures were ordinary compilation
or assertion failures, with no cap or interruption. Substantive review findings
were corrected; source hashes were reconciled at checkpoints. These carry
contracts are distinct from the R4/R5 property proofs.

## R1 — anti-replay uniqueness and the inclusive floor

**Decision [AGENT 2026-10-13].** Reuse the pure counter window, exact S2
refinement, finite mirror-call refinement and committed runner observer. Put
new arithmetic in `WG/CounterWindow`, with terminals in `WG/AntiReplay`.

**Original and proved wording.** The charter excludes counters at or below
highest seen minus 8128. The proof excludes counters strictly below it;
unseen equality may be accepted. The mirror's strict `ctrTooOld` comparison,
Linux `receive.c:counter_validate` and `selftest/counter.c` agree. This is an
intentional inclusive edge, not a mirror/kernel disagreement. The arithmetic
uses the one-based stored high-water mark, avoiding subtraction at an empty window.

**Architecture/refinement.** `CounterWindow/Bounds` proves the guard and bitmap
bounds; `mirrorCalls_refines` identifies finite original calls with pure
acceptance and final state. `Keypairs/Evolution/Bounds` adds `FloorHistory`:
an earlier accepted nonce is at most 8128 above a later one in the same
allocation lifetime. `Evolution.floor` transports it through lifecycle and
validator transitions. `runner_floor` and `runner_uniqueness` discharge the
original syscall contracts for every successful execution, including accepted
record schedules and slot reuse. No new observer or production history was
added; committed calls and discarded probes retain ReplayWindow's reviewed scope.

**Rule Zero witness.** The pure run `[8129, 1, 0, 1]` accepts `[8129, 1]`,
proved by kernel reduction. Separately, a six-operation accepted runner trace
establishes a session and accepts authenticated keepalive counters 8200 and 72
in lifetime 1: `72 = 8200 - 8128`. Original and logged JSON agree. Its explicit
records are reconstructed from tracked `CONTENDED_ROAM_CMP`, with datagrams
from `rx_window.json`, widened legacy section identities, adjusted second-data
clocks and synthetic site-128 end-of-wait bounds for the current timer interface.
This is an accepted non-placeholder mirror replay, not a fresh Linux capture.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r1-inclusive-floor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/Logged/Replay.lean
```

**Effort/review.** About fifteen minutes and five local compile passes; replay
under one second. An initial dependency scan preceded the new root import and
failed; a fresh build resolved it. Two independent read-only review passes
found no correctness defect. Their reporting corrections distinguish the pure
and runner counters and reconstructed records from a new capture. Current
validation is above; no remaining R1 obligation is recorded.

**Ranked recommendations.** None: the existing validator, replay projection
and proof-side lifetime evolution suffice. A proof-driven comparison change
or production history field would not preserve altitude and is not proposed.

## R2 — lifetime identity and retained references (in progress)

The charter asks for safety of every internal access after release, across every run, with a reused slot denoting a new identity.
The checked components establish endpoint identity evolution and failure-retaining local access safety. Whole-run closure remains open.
The accepted stale-cursor findings below expose reference retargeting; they do not resurrect an old identity or settle the full charter claim.

**Send-family extension.** Six complete send calls and three terminal exports pass the local R2 target (205 jobs; 140 terminals),
the coordinated proof gate and fresh stock kernel replay. Current campaign validation is recorded above.

**Architecture decisions [AGENT 2026-10-13].** Separate resolved allocation identity from ownership of saved numeric references.
Share frontier algebra and the seven-field WG kernel projection; retain observation history outside the exception layer.
Strengthen access safety with resident uniqueness and allocation/epoch bounds, sharing caller proofs through explicit ambient contracts.
Observe saved peer entries when their predicates are demanded, carrying saved stamps without inserting source getters.
Factor IPv4 send into source tail stages that retain the entry route. Keep TX socket and rescheduling contracts explicit.
Keep the five handshake calls at exact local boundaries. Share canonical record, jitter, checksum, crypto and index frames,
preserving legacy signatures by projection instead of duplicating generated source matchers.
Factor buffer allocation from its exact original socket-send suffix, reusing the existing send observer and keeping ordinary returns distinct from Stops.

**Models and refinement.** `Lifetimes/Store` and `Actions` describe slot/stamp transitions over original executions.
`Keypairs/Identity` uses whole-syscall evolution to exclude reintroduction of absent old keypair identities at operation endpoints.
Peer and packet primitive contracts extend that algebra; the packet primitive result is within one device epoch.
These endpoint results do not establish internal-access coverage.

`Logged/Prefix` preserves the original result, World on success and Stop, retaining preceding events on failure.
`Focus` embeds local histories into the mixed peer/keypair/packet stream. Packet stamps are `(ifindex, id + 1)`.
`LifetimeEvent.Safe` excludes reads and writes after release of that stamp; failed getters resolve no object and emit no access.
`ReleaseInv` adds resident uniqueness, including across both packet stores. `AllocationInv` adds slot/lifetime frontiers,
current packet bounds and past-epoch bounds. These premises establish allocator vacancy; unconditional erasure still reproduces
malformed occupied-slot overwrites without declaring them safe. Every runner fixture initializes the invariant; seccomp prefill preserves it.
Peer creation reuses its observer through slot/metadata geometry. `AllocationRetention` transports bounds using surviving residents
and explicit release origins. Shared filesystem frames end at return, leaving queued task work to its later caller.

**Completed original call families.** Each listed observer has exact source erasure; safety states its invariant and callback premises.

- **Allocation, references and lookup:** `peerCreate`, `peerGet`, `peerPut`, dump completion, keypair creation/acquisition/release,
  clearing/rotation/session creation, TX/RX allocation/free, and optional-peer/index/public-key lookup.
  Index lookup preserves the first matching entry's exit even when its kind is wrong. Rotation/clearing needs no distinct-slot premise.
- **Receive entry and maintenance:** complete enqueue, `consumeData`, packet decryption and one decrypt-worker iteration;
  twelve endpoint/cache, timer, queued-handshake and receive-key-refresh calls retain Boolean guard/modifier results.
  `CounterAccess` covers the whole validator without a bitmap-size premise. ENOSPC retains keypair put, peer put and packet free;
  EPIPE retains its pure callback. `AllowedLookupAccess` observes acquisition after the original node search.
- **Receive completion, polling and stack:** `ReceiveCompletion` composes rotation, staging, maintenance, lookup, release and statistics.
  `ReceivePoll` retains traversal, both `dropPeeked` getters and keypair/peer/RX-packet cleanup, with explicit callback preservation.
  `StackAccess` supplies the actual IPv4/IPv6 callback; TCP replies use the complete `DeviceXmit` observer, including trimming/splice loops.
  GRO callbacks precede the current packet's cleanup; final GRO flushing follows the final peer update.
  Budget and malformed-queue Stops remain covered. Concrete callbacks discharge allocation contracts without extending `TxContracts`.
- **TX staging:** seven complete calls cover CPU selection, peer/device enqueue, `createData`, staged purge/send and keepalive.
  CPU/enqueue retain their `Nat`/`Int` results. `TxContracts` transports cached identity predicates through scalar device updates.
  Observations retain the setter's read/write pair, both restoration getters and the nonce write before rejection.
  Plain staged values acquire resident packet identity only at `newTxSkb`.
- **Socket/cache/loopback:** `SavedPeers`, `LoopbackAccess`, `SocketCache`, `SocketSend`, `SocketSend4` and `SocketCalls` cover eleven calls.
  Saved scans observe demanded predicates with an explicit saved-stamp residency premise; statistics preservation is explicit and concretely discharged.
  IPv4 source stages retain both reset paths: nonlocal-source clearing resets the local interface before the mismatch test;
  the second route lookup retains its full World effect, and route-error false fallthrough retains the entry route.
  Erasure has no endpoint-family-validity premise. It includes socket-port Stops after earlier cache/stat effects; those are not accepted-domain runs.
- **Encryption:** `EncryptWorker` covers original packet encryption, step and iteration, preserving softirq-first execution,
  padding before checksum, the later keypair lookup, the packet setter's reread and dead-break enqueue of the entire item.
  Empty items fail after ring replacement; empty rings perform no replacement. Consumed-ring replacement has its own allocation contract.
  Checksum, softirq and rescheduling callbacks have explicit erasure/preservation contracts; the concrete checksum has a full-Kernel frame.
  The stronger packet contract transports identity predicates preserved by checksum. Callback contracts may permit identity changes:
  the result concerns resolved current-store accesses, not saved head/keypair association, batch homogeneity or reference ownership.
- **TX completion and workers:** `TxCompletion` covers `sendSkbToPeer`, `timersDataSent`, `timersAnyAuthenticatedPacketSent`,
  `keepKeyFresh` and `createDataDone`; `TxWorker` adds `txStep` and `txIter`. Both socket families include loopback's saved-peer scan.
  Negative socket returns are ordinary Boolean failures; Stops retain earlier accesses and skip later cleanup.
  The pending-timer read precedes jitter, then the unconditional timer-guard read. Key freshness retains its short-circuit tests.
  Polling retains the peeked-queue write on empty/uncrypted exits, both head reads, both drop-site peer reads, dead-head cleanup,
  every packet free and keypair/peer puts. Rescheduling occurs only after a true completed step and remains an explicit caller contract.
- **Handshake construction, consumption and MAC:** `HandshakeConstruct`, `HandshakeConsume` and `HandshakeCalls` cover
  `createInitiation`, `createResponse`, `consumeInitiation`, `consumeResponse` and `addMacToPacket`, preserving their distinct result types.
  Constructors retain private `setChain`'s fresh getter/setter and later rereads. Initiation consumption reads the flood clock before
  replay/flood rejection, retains signed operands, and reads the consumption clock after preceding writes.
  Response consumption retains the state-check getter and the setter's separate fresh getter. Ordinary rejection performs its puts;
  a Stop does not execute later cleanup. MAC addition retains the immediate saved-peer write before its short-circuited age test.
  The ambient index-insertion contract is concretely discharged for `AllocationInv`, as are reference-taking lookups and failure puts.
- **Handshake send:** `HandshakeSend` covers `sendBufferToPeer`, `timersSessionDerived`, `timersHandshakeInitiated`,
  `sendHandshakeInitiation`, `sendHandshakeResponse` and `handshakeSendWorker`. Buffer allocation refusal precedes peer access
  and creates no modeled packet identity. Its unconditional source factor reuses original `sendSkbToPeer`, discarding only the Boolean result.
  A normal allocation/socket refusal still lets initiation reach its retransmit jitter/timer; a Stop skips subsequent work.
  Response reads its first clock before its first peer getter; construction/session refusal, later clocks and fresh setters keep their original order.
  Initiation's jitter precedes the eager timer-guard getter. The worker performs `peerPut` after every normal initiation return, never after a Stop.
  Ambient socket, index-insertion and session create/put/replacement contracts are explicit and concretely discharged for `AllocationInv`.
  These are complete local calls; outer dispatch and historical reference ownership remain open.

`PrefixControl` and `PrefixLoops` share exact conditional, bind, range, map, list and accumulating-fold laws.
Generic enqueue/decrypt contracts retain explicit softirq, IRQ-exit and rescheduling observers.
`Framing/KernelEffects`, `WGTime`, `WGData`, `WGHandshake` and `WGIndex` provide canonical frames with legacy projections.
The index frame preserves the full kernel except the scalar index table, including device presence, resident values and frontiers;
the original device check and collision/draw records remain. Access-free helper coverage follows source inspection separately:
neither erasure nor an unchanged-Kernel theorem alone proves that an internally lifted helper contains no reads.

**Failure-prefix coverage.** Exact conditional equations retain pending-worker/refcount accesses, including writes before zero-refcount rejection;
release events occur only after successful final puts. Session birthdate-clock failure retains six events, peer initialization's first
cache-clock failure retains allocation/write, receive queue-record failure retains five accesses including the setter's nested read,
and handshake-completion clock failure retains four accesses. Cache-miss and keepalive allocation-record failures retain one peer read.
An empty-bitmap validator failure retains the initial keypair read and no write. TX jitter failure retains the pending-timer read;
MAC age-test failure retains its peer read/write pair. The IPv4 clear/reset equation retains read/write before a reset-clock Stop,
but covers a source segment. These are original-run-conditioned equations, not accepted-run witnesses.
The timer guard's peer getter executes unconditionally before `andM`. Duplicate cleanup IDs and malformed queues remain admitted,
including a later Stop after an earlier free. Safe access prefixes establish neither delivery/order nor reference ownership.

**Remaining closure.** Full caller, device-lifecycle and scheduler coverage remains unproved: concrete encrypt/TX scheduler callbacks,
socket setup/reinitialization, receive-handshake processing and outer send dispatch, timer callbacks, peer removal, netlink and remaining resident scans.
Saved scalar-reference ownership is separate: an aliased or dangling ID may stop after earlier safe accesses.
No C simulation is claimed. C initializes cache/handshake before incrementing the peer counter; the mirror increments/inserts first.
The proofs follow the mirror's order; that difference alone is not a lifetime counterexample.

**Accepted reference findings.** An eight-operation mirror run creates 28 peers, starts a stepped dump, deletes wg0,
creates a new wg0 with 27 replacement peers, then receives a chunk. The cursor retained raw slot 26, old identity 27,
with two references. Continuation cleanup instead releases replacement identity 55, with one reference, removing it while
the peer list and public-key table still name slot 26. The received message is the already queued first chunk;
continuation generation performs the destructive put. This is reference retargeting and table incoherence, not resurrection of identity 27.

The guest rejects deletion with a pending dump (`wg_delete_with_dump_pending`), as the W1/W2 design requires.
`Env.wgDelete` checks worker idleness but omits that guard. C retains `ctx->wg`; the mirror resumes a Boolean-held cursor against the current device.
This is an accepted-mirror domain bug, not evidence of a Linux lifetime bug. Its explicit non-placeholder records are synthetic, not a fresh capture.
The replay checks five runner checkpoints, their count and original JSON equality. The kernel-reduced
`stale_cursor_retargets_replacement` separately exercises `wgGetDeviceDone`; the full replay reaches the bad put through dump-resume cleanup.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

A second accepted eight-operation variant gives replacement peer 26 an IPv4 `10.0.0.0/8` binding before the stale continuation releases it.
The final checkpoint follows the actual device root: the prefix still names slot 26 while resident identity 55 is absent.
It checks eight checkpoint emissions, five specified projections and original-runner JSON equality, again using explicit synthetic records.
This rules out unconditional owner-residency invariants; it neither resurrects identity 27 nor alone proves packet misrouting
or disagreement with insert/remove history. The original witness is unchanged.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor-orphan |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/ReplayOrphan.lean
```

**Review dispositions.** Independent source reviews cover every listed checkpoint and its final deltas; frozen hashes were reconciled.
An unused lemma with an impossible KDF-failure premise was deleted. The no-device frame argument was corrected to `modifyDev`'s actual no-op.
Reviews corrected saved-stamp/cache-flag scope, arbitrary-input erasure versus accepted-domain behavior, and conditional failure-equation wording.
A reusable conditional law moved into `Logged/Prefix`; an overbroad docstring was narrowed to its theorem's conclusion.
TX review checked source/C ordering and confirmed composition through existing laws without requiring a new sequence runner.
Legacy frame signatures were preserved through canonical projections, resolving duplicate generated matcher declarations.
Documentation status/count discrepancies were corrected. No unresolved correctness finding remains for the checked components;
this does not close their stated caller, scheduler or ownership obligations.
Send-family review qualified the no-prior-access statement to buffer allocation refusal; response/session allocation has preceding peer accesses.

**Effort.** The ledger records invocations, not an invented campaign total. Each accepted cursor reproduction takes under one second.

| Checkpoint | Capped invocations: passed / failed | Elapsed |
| --- | --- | --- |
| TX staging | 14: 2 / 12 | 24m44s |
| Receive completion/poll | 14: 3 / 11 | 23m50s |
| Saved scans and initial ten-call socket family | 20: 3 / 17 | About 43m |
| Staged IPv4 send | 8: 5 / 3 | About 8m |
| Encryption worker | 4: 2 / 2 | About 6m |
| TX completion/worker | 6: 1 / 5 | 21m03s |
| Five-call handshake family | 7: 1 / 6 | About 15m |
| Six-call handshake send family | 6: 2 / 4 | 7m39s |

Earlier caller checkpoints took roughly 6–25 minutes each with 4–19 compilation invocations.
The first IPv4 architecture failed at proof-search heartbeat limits; its unused observer was removed.
The second uses explicit source tail stages and compiled source-equivalence, erasure and safety contracts.
Other failures were proof elaboration, simplification or integration failures, including broad-reduction heartbeat exhaustion,
bind/fold alignment, private-name normalization, metadata inference and duplicate matchers. They remain failures, not mirror findings.
One earlier tactic loop was deliberately stopped by its verified PID and repaired. The later IPv4, encryption, TX and handshake
checkpoints reported no interruptions or cap failures; their process exits were collected.
The send extension corrected four ordinary proof failures (explicit Session import, option-case alignment and discard/branch normalization).
Its final rerun incorporates the reviewed buffer-allocation qualifier; all exits were collected, with no interruption or cap failure.
The three send-family exports pass coordinated validation and final frozen-source review; R2 now has 140 terminals.

Validation details are retained in checkpoints `859d56a` (IPv4), `e6905f2` (encryption), `52a4602` (TX) and `d75f994` (handshake).
At `d75f994`, R2 has 137 terminal statements; the complete target, coordinated proof gate, fresh stock Lean kernel replay,
model build and unit tier pass. Current campaign counts are recorded above. Unchanged cursor witnesses were not rerun for these extensions.
No differential check or guest was run for this proof work.

**Ranked mirror-shape recommendations.** (1) Restore pending-dump deletion rejection: altitude-preserving fixture-domain enforcement.
(2) If that domain expands, retain the actual device lifetime in the cursor as C does: altitude-preserving, with separate validation.
(3) Retain named allocation, deletion and same-object update boundaries: altitude-preserving operational structure.
No production history field is proposed, and no mirror change was made for these proofs.

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
arbitrary bad records may still Stop. In these empty-root/empty-child branches,
`add` refusal preserves the Kernel.
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

`GraftSuccess` now refines both successful selected-root endpoints to the
existing pure insertion: the requested node becomes a parent, or a second fresh
ownerless node splits the old subtree and requested leaf. Whole-store freshness
and duplicate-free represented IDs justify the exact reparenting and descendant
frames. Split-bit separation is derived from the prefix geometry. Successful
original `add` and `insert` retain the actual root link, validity, unique IDs,
conditional compression, exact allocation count, and the opposite root value
and any supplied opposite-family representation. `insert` advances the sequence
once. Original lookup at the resulting device root terminates and satisfies
`Winner` over the independently updated flat bindings. Only the target peer is
required resident; no old-owner liveness or list coherence is assumed. The
success premise is an actual original return of zero, not a post-state
representation assumption. Normal refusal/rollback contracts remain unchanged;
record Stops remain outside these normal-return claims.

`GraftLink` and `DeepGraft` extend nonempty grafts below an arbitrary represented
path. The immediate parent's root stays fixed, so existing context replacement
frames all outer ancestors and siblings. Whole-tree unique IDs and whole-store
freshness separate the parent, old focus and fresh nodes. The source-shaped
`graftTail` retains the final original `chooseAndConnectNode`; its factorization
back to original `add` is an all-input equality. Original placement, including
its stopping condition, is derived from the represented path.

Four new terminals classify normal `add` endpoints and prove successful `add`,
actual-root lookup and `insert` refinement. They preserve both roots, supplied
opposite-family representation, validity, unique IDs, conditional compression
and exact frontier/sequence effects. Second-allocation refusal still consumes
one ID and filters every peer list; it does not imply whole-state rollback.
Only the requested peer must be resident; old owner labels may be orphaned.
These normal-return contracts do not classify record Stops. Independent source
review, the coordinated gate and fresh kernel replay pass.

**Remaining claim.** Unified insertion dispatch, removal and general configuration
histories remain open. Parsed-input bounds and history invariants still need propagation through all mutations.
Both packet paths follow R2. Owners are raw peer slots, not allocation or
cryptographic identities; no liveness/ownership claim follows from tree lookup.
The R2 orphan-owner replay above is a constraint on any proposed ownership
invariant, not yet an R3 counterexample. No R3 statement has been reshaped
and no Rule Zero finding is claimed.

**Effort and review.** Arithmetic, pure-tree, original traversal and pure
insertion work used 5, 6, 20 and 13 compile invocations respectively. The
following tranche counts are separate, not an inferred campaign total.

| Tranche | Capped invocations: passed / failed | Elapsed |
| --- | --- | --- |
| Empty-root insertion | 12; outcomes not separately tallied | 11m44s |
| Placement | 21, including a failed monolithic child architecture | About 30m |
| Staged child replacement | 19; outcomes not separately tallied | About 18m |
| Arbitrary-depth empty child | 8: 5 / 3 | 11m49s |
| Exact-prefix replacement and list deletion | 21: 7 / 14 | About 18m |
| Selected-root graft endpoints/rollback | 40: 6 / 34 | 35m28s |
| Selected-root successful refinement | 7: 4 / 3 | About 8m |
| Arbitrary-depth nonempty graft | 30: 4 / 26 | 36m47s |

The staged child architecture replaced a failed monolithic proof; this was not
a mirror finding. Three deep-graft source-factor attempts hit Lean heartbeat
limits. Including the original final return in the proof-side cut point made
the all-input equality close by `rfl`. The final targeted/full builds passed
106/273 jobs; all exits were collected, with no cap or interruption.
Earlier checkpoint validation is retained in the corresponding commits;
current combined validation is above.

Independent reviews corrected a `freeNode` contract missing node residency,
and distinguished normal-return classification from reachability, root values
from linkage, endpoints from event order, and successful Worlds from Stops.
The deep-graft docstring now states target-peer residency explicitly while
allowing old owner labels to be orphaned. Frozen source and scope reviews have
no unresolved correctness finding. A duplicated effort paragraph was removed;
an earlier reviewer observation about the source-factor proof was withdrawn
after rereading its final `rfl` body.

**Ranked mirror-shape recommendations.** None from these components. The named
arithmetic helpers and integer address encoding admit refinement without
production changes; correspondence to C byte layout remains informal.


## R4 — queue, poll and delivery-order components (in progress)

**Architecture decisions [AGENT 2026-10-13].** Use symbolic filling and pointwise slot algebra over
original ring operations. Track complete receive queues with epoch and peer identity, permitting
deletion. Observe removal, completion offers and callback entry at their actual boundaries, retaining
failed prefixes. Tag occurrences by local ordinal, skb and bytes; relate observers directly through
event/result projection. Derive concrete stack frames through existing source factors. Preserve
`GroSafe` and the failed chronological claim, with selected-order results under distinct names.

**Ring geometry and W7.** `Queues/PtrRing` applies original `full` and `produce` to every attempt: a
full ring rejects each attempt and remains unchanged. `Fill` proves symbolic filling and consumption
below the retirement threshold. `FullRing` starts with the original size-1024 ring and performs two
produce/consume pairs. Logical count is zero, but slots 0 and 1 remain occupied. The next 1024 guarded
attempts accept exactly 1022 items and reject the last two. Producer, consumer head and tail finish at
0, 2 and 0; logical count is 1022, and the FIFO contains exactly the accepted new items. The [landed W7
tier](2026-10-13-w7-full-ring-tier.md) corrected the earlier one-drop prediction: it omitted the
keepalive’s uncleared slot. Linux and the mirror agree on both `-EPIPE` drops without a mirror change;
all producers precede worker consumption. The theorem is a closed ring witness, not refinement of that
complete recorded run.

**Original enqueue and queues.** `Queues/Enqueue` classifies complete `enqueuePerDeviceAndPeer` normal
returns: success produces the item; `-ENOSPC` leaves the ring unchanged; `-EPIPE` means physical
fullness and an unchanged ring. The earlier peer-capacity test retains priority, and
peer-queue/packet-state updates may precede `-EPIPE`. Missing objects and queue-work failures remain
Stops. No ownership or queue-validity premise, or unchanged-peer-state conclusion, is imposed.

`PrevQueue` proves original dequeue, peek, peek/drop and enqueue laws. Contents are `peeked.toList ++
items`; original `count` excludes the cache. Normal peeks preserve contents, and dropping a present peek
removes their head, without a validity premise. A nonstub empty queue without a cached peek retains its
invariant Stop; coherent queues have ordinary dequeue/peek results. `RxQueueView` records resident
epoch, peer allocation identity and complete queue. `RxHelperFrames` covers `peerGet`,
`peerGetMaybeZero`, `keypairGet`, `keypairPut`, `freeRxSkb`, `counterValidate` and
`receivedWithKeypair`; `peerPut` may delete entries. The counter frame admits malformed bitmaps and
Stops without a 128-word premise.

`RxQueuePrimitives`, `RxMaintenanceFrames`, `RxTxFrames` and `RxCompletionFrame` compose fresh
getter/setter laws through endpoint/cache maintenance, receive timers, staged transmission, allocation,
cleanup, source lookup, statistics and complete `consumeDataDone`. Every surviving receive cell retains
its exact entry view. These normal-endpoint frames permit deletion; they establish neither error-state
equality nor internal-access, packet-store or delivery properties. No clock or ownership premise was
added.

**Outer-poll observation.** `RxPollPrimitives` names original peek/cache and two-getter drop sequences.
`RxPollPrefix` emits after the outer drop update succeeds: its local law appends one ID on success and
none on failure. Erasure preserves every result, full successful World and Stop. `RxPollOrder` maintains
`entry = removed ++ remaining`, with each resident’s queue equal to `remaining`; a later successful
getter restores residency after deletion was permitted. Current callbacks explicitly require
normal-return `RetainsRx`, discharged below. The log covers this outer drop site, not opaque
callback-internal operations. Repeated entry IDs remain admitted, so this prefix result alone is not
no-duplication.

**Retired chronological claim.** Over `2c7a076`, `original_poll_callback_prefix` stated that callback
entries form a prefix of tagged successful completion buffers. Real GRO at `f45bde8` invalidates it. The
theorem is retired; `GroSafe` retains its original definition. The accepted chronological counterexample
remains valid.

**Accepted GRO counterexample.** `proof-campaign-replay.py r4-gro-reorder` constructs six operations
with explicit records. One batch receives nonce 0 carrying a one-byte ACK-only TCP segment (ports
40001→80), then nonce 1 carrying a SYN on a different flow (40002→443), under one peer/key allocation
lifetime. `DeliveryOrder/ReplayGro.lean` checks original `executeTrace trace false` acceptance,
identical checkpoint/acceptance-observer JSON, exact validator history `(lifetime, 0), (lifetime, 1)`,
and input ciphertexts against that lifetime’s receiving key. Output appends the SYN’s RST at outgoing
nonce 1, then the ACK’s RST at nonce 2; both byte-exact ciphertexts also occur in the original runner’s
final observable rows. Lifetime preservation, counters and receive-store cleanup are checked. This is
generated accepted mirror input, not a Linux capture or proof of kernel schedule reachability. The
audit-carry checkpoint is `3d50a4a`. Reproduce with:

```sh
capped -- scripts/in-bundle sh -c 'python3 -B docs/proof-campaign-replay.py r4-gro-reorder | lake env lean --run Leanux/Proofs/WG/DeliveryOrder/ReplayGro.lean'
```

The ACK remains GRO-held while the SYN enters the normal list; completion appends the held segment
behind it. `original_gro_held_then_normal` proves the original helper equation `napiGroReceive H;
napiGroReceive N; napiGroFlushAll = callback [N,H]` under the original classifier’s hold/normal
hypotheses. This is a design nuance at the post-GRO stack boundary; it does not show reversal of
WireGuard’s receive queue or decrypt FIFO. C supports these different-flow inputs (`tcp_offload.c:261,318,379–381`, `gro.h:528`,
`dev.c:6385,6388`). Two separate source concerns remain unconfirmed: zero-payload `len < mss` flushing,
and inspecting an existing same-flow held segment on the normal arm. Neither is a reported differential
finding.

**Current GRO refinement.** `Logged/Projected` supports enriched local accumulators. `Queues/GroState`
carries tagged `rxList`, `rxCount` and `held` through all four original helpers. Their erasures and
complete `RxPollGro` erasure preserve every result, successful World and Stop on all inputs. Successful
`consumeDataDone` emits its exact bytes, skb and local `workDone` ordinal before GRO admission. `none`,
including keepalives, emits nothing; `rxPollFree = false` does not imply delivery. A second held offer
can thus be observed immediately before GRO refuses it. That pending offer is neither silently
classified as a drop nor counted as admitted.

`GroCallback` emits immediately before each original `deliverInner` call; failure retains that entry
without fabricating visits to the remaining suffix. Callbacks now occur at batch flushes and completion.
Distinct `SelectedGroSafe` specifies a visited prefix of normal offers followed by held offers,
preserving each class’s source order. `SelectedGro` proves it for every outcome of one poll starting
with empty history. An actual successful original poll with `bytes.forM Env.deliverInner` yields exact
selected-offer/callback-entry equality, including multiplicity. No initial history property or queue
frame is assumed. The invariant derives `rxCount = rxList.length` and at most one held entry, tracks
pending offers and full-budget Stops, and proves terminal flushing by the actual nil/singleton cases.
`PrefixEnsures.rangeInvariant` supplies loop composition. This is callback entry, not completed delivery
or normal-before-held order across polls; the checked selected-order checkpoint is `67f880f`.

**Tags and observer correspondence.** `RxPollTags` proves on every normal or stopped poll that buffered
`(ordinal, skb)` tags form a subsequence of outer removal tags. Removal ordinals enumerate from zero,
and buffered ordinals are distinct. A pending removal can emit one completion offer or return `none`; a
Stop before `workDone` increments retains the removal. Repeated skb IDs remain possible: these ordinals
identify local occurrences, not allocation identities. `Logged/ProjectsPrefix` and `RxPollProjection`
directly prove agreement of the two observers’ results, successful Worlds, Stops and projected outer
removal logs, including callback failure. Separate erasures alone would not prove log equality. Neither
bridge assumes queue retention, unique skb IDs, successful execution or an initial history property.
This correspondence checkpoint is `40addf7`.

**Concrete stack and callback provenance.** `RxStackFrames` proves normal-return `RetainsRx` for actual
`bytes.forM Env.deliverInner`. IPv4 TCP resets re-enter original `wgXmit`, including protocol/allocation
errors, trimming/splice, staging and cleanup. UDP/IPv6 changes the sender inbox; loopback handling
changes flags/records without another queue poll. Surviving cells retain their complete view, deletion
is permitted, and no valid-packet, live-owner or scheduler premise is introduced. `RxPollProvenance`
composes that frame with the projection: on every outcome, outer removals prefix the initial resident’s
queue, and buffered skb occurrences form its subsequence. The only queue premise names that initial
cell. Separately, selected entries permute buffered entries; entered callback ordinals are therefore
distinct, and every entered entry—including exact bytes—was buffered and has its tag in the removal log.
Failing callback entry counts. These results establish neither allocation identity nor uniqueness
between polls. The checkpoint is `c0713d8`; observer definitions and the original chronological
predicate remain unchanged.

**Remaining scope.** Receive enqueue, general ring interleavings, worker-local ownership, pipeline
conservation and recorded scheduler composition remain open, alongside R2’s caller/lifecycle closure.
Discarded speculative activations must discard history with their trial Worlds. Local observations imply
neither packet-store emptiness nor whole-schedule no-loss/no-duplication. Finite-prefix conservation
must account for pending obligations rather than infer eventual delivery from a finite run. The ring
witness is not yet composed with original enqueue and a real peer queue; it alone makes no
packet-arrival, cryptographic, fairness or delivery-order claim.

**Validation and effort.** R4 has 35 terminal theorems. Checkpoints above passed coordinated proof
gates, fresh stock kernel replay, model builds, unit tiers and independent frozen-source review; current
whole-tree validation is recorded above. Across the R4 slices, **105 capped local invocations comprise
36 passes, 68 ordinary failures and one deliberate termination**. All outcomes were collected; no memory
cap was hit. Corrected failures concerned elaboration, matching, simplification or replay assertions.
Owned temporary outputs were removed. These proof slices made no mirror edits, main integration, push or
new QEMU/differential run.

The completion-frame worker had two provider interruptions during implementation and one during
read-only reporting; all dirty worktrees, including nonignored untracked files, were preserved before
subsequent edits or rebuilds. Separately, after deliberate termination of a large-reduction attempt, the
initial ring writer resumed without the required preservation. Work stopped; the coordinator snapshotted
all six dirty worktrees, leaving branches and real indexes unchanged, before implementation resumed.
Symbolic slot algebra replaced the large reduction. This missed-preservation incident is retained
separately from ordinary compilation failures and provider interruptions.

**Review dispositions.** Independent source, premise and scope reviews found no unresolved correctness
defect; final hashes matched. A table-format finding was fixed. Reviews required explicit callback-log
scope and independent correspondence/provenance proofs rather than conclusions inferred from erasure;
the checked components now supply those bridges. Reviews also preserved the
generated-witness/kernel-capture distinction, the retired chronological theorem and unchanged predicate,
and remaining pipeline limits.

**Ranked mirror-shape recommendations.** None from these components. Physical occupancy and batched
retirement explain W7; proof-side boundaries, queue frames and projected accumulators handle the local
poll without changing the mirror. Recheck with `capped -- scripts/in-bundle scripts/proof-gate`.

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
admission-time TX checks, and reference-counted clearance. These are statement
artefacts relative to the charter's unconditional wording, explained by the
implementation's admission and reference-release boundaries, not demonstrated
Linux security defects.

**Independent R5 review disposition.** The [review of 7fc444d](2026-10-13-review-r5-counterexamples.md)
agrees with those classifications and the thirteen local theorem statements.
Its requested clock-domain qualification is recorded in the
[timer-model note](2026-10-13-review-items-7-8.md#proof-domain-qualification):
the environment imposes no elapsed-virtual-time bound between staging and a
recorded crypt-worker activation. The three witnesses uncommitted at that
review's snapshot were committed in `3d50a4a`, and all five R5 reproductions
passed the audit-carry checkpoint. The current two time replays strengthen
their observer connection to the complete original advance syscall.
No upstream-tray entry is justified by this evidence.

Two supporting assertions in the review are not adopted: authenticate-then-check
is the actual receive order, not the only logically possible order (a numeric
limit could reject an untrusted nonce without updating replay state); and no
measured or universal Linux worker-latency bound follows from these witnesses.
Kernel reachability is unestablished, rather than proved impossible. Likewise,
the rejected nonce does not advance the receiving counter or reach the stack;
its queue, packet, reference and record effects are not an unchanged-World claim.
Nor does the review's proposed 128-packet bound hold per staging call: C
`device.c:207–217` trims the old queue before splicing the new batch, deliberately
retaining excess GSO segments; the mirror follows that order. The 1024 crypt-ring
slots count batch entries, not a global bound on retained packets. Finally,
three of the thirteen R5 terminals are erasure results (staging, timer pass and
receive attempt), correcting the review's count of two. These corrections do
not change the proved statements or the no-tray disposition.

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
`Logged/Advance` factors the complete original advance syscall, retaining its
descriptor, seccomp and task-work effects. The two current time witnesses
start at an accepted runner checkpoint, load the next operation's records,
execute that observer and compare its final Kernel, decisions, receiving
endpoint, jiffies and exhausted records with the accepted runner's checkpoint.
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

**Effort/review.** Local tranches used 17 receive/time builds (10 ordinary
failures), 10 staging builds (6 failures), four RX-attempt builds (one failure),
and four timer-observer builds (two failures). Thirteen replay executions had
eight passes, two Lean-syntax failures and three generated-record/jitter
failures. All five final reproductions passed in under nine seconds each,
including exact original/observed JSON and assertions. The first checkpoint
gate failed on the forbidden word `admit` in a diagnostic string; it was corrected.
One provider interruption left no running job; all dirty worktrees were preserved
before edits resumed. No cap was hit. Independent source, assertion and scope
reviews found no unresolved defect after wording corrections; frozen hashes
matched. Current combined validation is above; earlier details are in the
checkpoint history. No new Linux guest execution is claimed.

[AGENT 2026-10-13] Resolve R5's false original statement through the accepted
counterexamples permitted by Rule Zero. Keep the positive local contracts at
their proved boundaries; stronger replacement transport theorems are follow-on
work, not claims of this result. Distinguish generated clock arithmetic from
measured kernel execution.

**Ranked mirror-shape recommendations.** None is required for these findings.
The landed signed clock helpers and operand-bearing branches expose the relevant
semantics. Adding a proof-motivated age guard to the later encrypt worker would
change the C's control flow and is not altitude-preserving.


## R6 — cookie exclusion and retry-limit finding

**Original claims and disposition.** The charter requires that an initiation
without valid MAC2 under load never reaches Noise, and that retransmission
stops after `MAX_TIMER_HANDSHAKES` attempts. The first has an original-source
cookie-only path theorem and complete Noise-state preservation on ordinary
completion. The second is false literally: the accepted episode below sends
19 retries, 20 initiations including the first, with `MAX_TIMER_HANDSHAKES=18`.
This is the C's strict `attempts > MAX_TIMER_HANDSHAKES` design;
`timers.c:49` itself reports `MAX_TIMER_HANDSHAKES + 2`. It is a wording/design
nuance resolved by Rule Zero, not evidence of a mirror/C disagreement.

**Cookie proof.** `Cookies/Gate` factors the original
`receiveHandshakePacket` without changing its control flow. `FailedMac2`
contains actual load and `makeCookie` execution witnesses, MAC1 equality, and
an explicit MAC2 inequality against the cookie that invocation returned.
The derived original validator result is `noCookie`; seven subsequent original
branch records lead exactly to `sendHandshakeCookie`. The selected source
suffix contains no Noise consume/create call. Its complete result equation
retains reply failures as the original Stop. Invalid MAC1 instead takes the
original five-record drop suffix before cookie creation or Noise.
`Cookies/Load` constructs the active-load result from either queue depth at
least 512 or the actual unexpired recorded decay clock, retaining signed wrap.

`Cookies/Frames` preserves the complete device after removing exactly cookie
secret/birthdate and TX packet/byte statistics from its view, together with
both global peer/keypair allocation counters. Full peer and keypair records,
static identity, indices, device peer/keypair/packet/node frontiers and all
other device fields remain visible. Both `makeCookie` calls may independently
rotate. IPv4/IPv6, reply allocation refusal and ordinary socket errors are
covered. Missing records before a witness completes can Stop; these theorems
do not assert that every input completes. The frame is per original
`receiveHandshakePacket` call, not the enclosing queue worker or arbitrary
later scheduler activity. Valid-MAC2 rate limiting is a different path.

**Accepted retry episode.** `r6-retransmit-limit` derives a 23-operation input
from tracked `d3_retransmit_gives_up` and initiation draws. It uses explicit
records, coherent coarse/jiffies/timer-arm arithmetic and advancing TAI values,
with cache-clock records disabled. `FloodResistance/Replay.lean` checks original
runner acceptance, exact checkpoint JSON agreement, stable peer identity,
empty keypair store, timer/counter/queue boundaries and actual new initiation
bytes. The first 19 timer callbacks increment and queue the original send worker;
each worker transmits one new initiation and rearms. The twentieth callback
compares `[19,18]`, gives up without transmitting, purges the staged packet and
arms deferred zeroing. The preceding callback compares `[18,18]` and rearms.
These are generated accepted mirror inputs, not a Linux capture or proof of
kernel schedule reachability. Counts describe this episode only: resets,
rate/dead/allocation/socket branches can change other episodes.

`Logged/Advance` connects observations to the complete original advance syscall,
including its seccomp/dispatch/task-work prefix, result, successful World and
Stop. Recorded timer units are observed; the placeholder path is deliberately
lifted without a unit-coverage claim. Its erasure is the sixth R6 terminal and
is also used by both current R5 time replays.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r6-retransmit-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/FloodResistance/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

[AGENT 2026-10-13] State the cookie result over actual original rejection runs
and retain the literal retry-limit counterexample. Do not replace the false
limit with an unproved universal episode bound or promote generated records
to measured kernel schedules.

**Effort/review.** Cookie proofs used thirteen capped builds: three passes
and ten ordinary failures in elaboration, factorization and normalization.
The abstract load-continuation factor avoided broad expansion without weakening
the state view. Retry/Advance used nine invocations: five passes and four
compilation/assertion failures, including a corrected reply-endpoint assertion.
The final retry and both strengthened R5 time replays pass. All exits were
collected, with no interruption or cap hit. Independent source/contract review
found no unresolved correctness defect; its two reporting corrections were
incorporated. Current gate, fresh stock kernel replay, model and unit results
are above; `66df779` records the documentation-only review/tray carry.

**Ranked mirror-shape recommendations.** None. The existing load, validator,
cookie-reply and retry-callback boundaries suffice: proof-side source factors
and the full device projection establish cookie exclusion. Changing the retry
comparison to make the charter's literal limit true would alter the C's
behavior and is not altitude-preserving; it is not proposed.
