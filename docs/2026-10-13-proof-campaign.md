# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`; governed by
[the charter](2026-10-13-charter-proof-campaign.md). Both prerequisites were
carried from `2c7a076`, then the audit at `f45bde8` and documentation-only
`a39aded`, then the scheduler robustness change at `7a92672`.
The registered components pass coordinated validation over the authorized `c047e64` carry,
including R2 concrete Batch scheduling and allowed-IP access, R3 insertion and complete
represented peer removal from explicit list coherence, and R4 finite and RX/TX source
journals plus the concrete RX scheduler. The mirror remains byte-identical to that main
revision, and all seven register rows are current at their stated scope.
Open obligations below remain explicit. No integration into main,
push, differential check or guest run has been performed by this campaign.

| Result | Disposition |
| --- | --- |
| R1 anti-replay | Complete: uniqueness and the intentional inclusive-floor correction, with pure and accepted-run witnesses. |
| R2 lifetimes | Endpoint identity and failure-retaining access contracts cover the listed call families, now including the concrete Batch scheduler, separate copied trials and six allowed-IP list/removal calls. Whole-run environment/lifecycle closure and saved-reference ownership remain open. The historical stale-cursor recipes now have checked pending-dump rejection at `c047e64`. |
| R3 routing | Prefix arithmetic, represented-tree lookup, bounded-input normal insertion dispatch, pure removal/locality and all local source removal arms are checked. Unified represented-forest target removal and complete original removeByPeer from explicit resident-list coherence pass scoped and coordinated validation. Initialized insertion/list coherence, configuration-history and packet-path refinements remain open. |
| R4 delivery | W7's two full-ring drops are explained. An accepted replay refutes chronological post-GRO stack order. Per-poll selected order, removal/provenance, concrete stack frames and RX/TX source ring journals are checked; pipeline conservation remains open. |
| R5 key lifetime | Resolved under Rule Zero by counter-limit, delayed-encryption and post-clear-use witnesses, with 13 local positive contracts. |
| R6 flood resistance | Cookie exclusion proved at the original call boundary; accepted 19-retry/20-initiation episode resolves the literal limit through Rule Zero. Six terminal contracts. |

**Last coordinated validation.** The mirror is byte-identical to `c047e64`.
The proof gate passes 332 jobs and 335 terminal declarations: 333 theorems and two helper definitions
(ReplayWindow 15; R1 9; R2 160; R3 68; R4 64; R5 13; R6 6), using only `propext`, `Classical.choice` and `Quot.sound`.
Fresh stock kernel replay, the 60-job default model build and the 114-test unit tier
(23.573 seconds; one skip) pass. The unchanged runtime retains the preceding carry's
118-job executable build and eleven passing reproduction checks; neither was rerun for
this proof-only extension. Independent frozen-source and scope review has no unresolved finding.

**Represented-removal extension.** Over the same `c047e64` mirror, the new
R3 source passes its 125-job Statements target and the 332-job full proof build.
The coordinated checks above include all six new exports: three single-step forest
contracts and three complete coherent peer-removal contracts. No runtime reproduction changed.

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle lake build
capped -- scripts/in-bundle lake build leanux-model
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

All eleven current reproduction checks pass, as detailed below. Generated streams establish
mirror behavior, not Linux capture or schedule reachability. Reproduction commands and provenance
are retained with each result.

**Preceding `c047e64` carry checkpoint.** The full local proof target passed 325 jobs
and counted 329 terminal declarations. Exact observers retain kind-311 caller-jiffies reads before timer guards
and before jitter, including arbitrary arm-record mode and its Stops. The typed timer family exposes
the actual caller value/site. `requireNotPending` is now the original no-op; peer get/put histories
therefore remove its retired read rather than invent a replacement access. Cookie framing permits both
ratelimiter tables while retaining every resident object and allocation frontier. The carry also retains
recorded under-load comparison operands, cookie-reply checks, per-packet destination validation,
the new seccomp record/calls and stable per-session observation ordering. Runner erasure and anti-replay
contracts quantify the new `floodExact` mode; committed scheduler observations keep both crypt-ahead sites.

All eleven current reproduction commands pass: nine accepted runs with exact original/observer output
agreement, and two R2 rejection checks. Each R2 check separately accepts the first three operations,
verifies the old cursor's identity and reference count, then requires both complete runners to reject
operation 3 with the exact pending-dump reason. The raw stale-cursor theorem remains a local counterexample;
its former full-run reachability is historical, not an ownership proof for the current runner.
The migrated retry episode still has 19 retries/20 initiations; both coherent time witnesses still
check original complete-advance equality and new transmitted ciphertext. GRO still reverses the
selected packets' chronological stack order under one peer/key lifetime. No new Linux capture is claimed.

**Decision [AGENT 2026-10-14].** Keep both historical R2 recipes and check their current rejection,
while preserving their accepted pre-delete boundary and labeling all later old values historical.
For the coherent R5/R6 recipes, generate timer caller records from the recipe's chosen clock,
in source order, with independent arm-expiry checks. The separate historical W7 fixture uses
main's `with_timer_caller_jiffies` migration, which reconstructs caller values from the captured
arm expiry and matching delay; it is not an independently captured caller-clock observation.
These are input-reproduction migrations, not a mirror rule or new kernel evidence.

Local validation used 23 sequential capped invocations: 14 passed and nine failed ordinarily
(seven proof elaboration/normalization failures and two Lean parser failures in the rewritten R2 replayers).
Invocation 4 was launched before the final timer diagnostic from invocation 3 was noticed; it retained
that known failing goal. Subsequent targeted corrections closed it without changing the source boundary.
The full target passed in invocation 10; all eleven final replayers passed in invocations 11 and 14–23.
All exits were collected by 05:58:22 UTC, 29m33s after the 05:28:49 token grant; no cap or interruption occurred.
Review finding CARRY-R4-1 removed obsolete pending-worker/getter descriptions. CARRY-R4-2 corrected the
jitter-failure theorem and terminal to require the original caller-read success before the failed jitter;
this is an explicit changed source prelude, not an `armRecords = false` restriction. The reply invariant
copy and an accidentally lifted `idleTimers` call were also corrected; the observer again records that
call's validator events. Final frozen-hash review reconciled all forty files with no unresolved finding;
the five coordinated trust/build/unit invocations above all passed. Only documentation reconciliation
followed those source checks. The campaign diff passes the whitespace speedbump; the broader staged
merge reports carried whitespace in three upstream text files and two kernel patch files, all unchanged
from `c047e64`. These are outside the campaign repair diff.

**Carries and review history.**

| Carry | Preserved correspondence and effort |
| --- | --- |
| Seccomp/shared frames | Seven-field WG projection, child fixture and prefill success/error paths; no seccomp-free premise. BPF continuation sharing and loop-counter progress. 17 compile passes over 36m34s, with independent source and architecture review. |
| Prerequisites (`2c7a076`) | Exact comparison operands and validator World, signed/unsigned clock operations, both timer-arm signed-gap failures, occupancy/record bounds and kind-310 peek/read validation. About 40 minutes and 12 local builds; earlier transmit/stack work used five attempts. |
| Audit (`f45bde8`) | Index decisions and missing-device failure; cookie rotation clock/randomness; signed MTU/initiation fields; receive-refusal cleanup; actual GRO state and callback timing. Fourteen root, six R2 and sixteen R4 build/probe calls preceded passing gates and nine replay checks. The failed chronology theorem was retired explicitly. |
| Scheduler (`7a92672`) | The committed `cryptAhead` observer includes the original encrypt iteration and logged NAPI callback, exact temporary TX queue changes and Stops. Copied-World consistency trials still execute the original action and discard its returned World; no trial acceptance history is appended. Existing acceptance evolution composes through the new TX prefix; this adds no whole-scheduler R2 access or ownership claim. Local validation is recorded below; coordinated trust and fast-tier checks pass. |

**Decision [AGENT 2026-10-14].** Reconstruct the campaign's common seed from
tracked `rx_roam_v6` operations and the 40 historical hidden records formerly
in `CONTENDED_ROAM_CMP`, rather than depend on the removed evaluator fixture.
The generator documents that capture's provenance and retains each recipe's
explicit transformations. Seed migration is a reproduction repair, not new
kernel evidence. The seed and all ten generated JSON values equal their
pre-carry versions. Independent review corrected an overbroad history-retention
docstring: successful committed execution retains acceptance events; exact
Stop erasure does not imply a retained failed history.

The scheduler carry's targeted build passes 101 jobs and full `LeanuxProofs`
passes 284 jobs. All ten campaign replayers and the existing `W7_CRYPT_AHEAD`
case pass, including original/observed output agreement; no existing witness
event or endpoint assertion changed. The W7 input rearranges captured records
and adds synthetic end-of-wait bounds; it is not a fresh kernel capture.
Fifteen sequential capped invocations used 16m20s through the final check:
fourteen passed and the first compile failed on two explicit Stop proof goals,
then closed using the existing `evolves_throw` lemma. All exits were collected;
there was no cap or interruption. Total writer-token ownership was 17m22s.
The four coordinated trust/fast checks above also pass.
The W7 observer check is reproduced by:

```sh
capped -- scripts/in-bundle bash -o pipefail -c 'python3 -B -c "import json; from evaluator.test_model_replay import W7_CRYPT_AHEAD, with_jiffies_end, with_timer_caller_jiffies; print(json.dumps(with_timer_caller_jiffies(with_jiffies_end(W7_CRYPT_AHEAD))))" | lake env lean --run Leanux/Proofs/Logged/Replay.lean'
```

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
records use `historical_session_seed`: tracked `rx_roam_v6` operations and the
40 historical record words documented in the generator, with datagrams from
`rx_window.json`, widened legacy section identities, adjusted second-data
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
The historically accepted stale-cursor findings below expose reference retargeting; they do not resurrect an old identity or settle the full charter claim.

**Allowed-IP access extension.** Three grouped exports cover `listAddTail`, `listDel`,
`removeByPeer`, `rootRemovePeerLists`, `free` and `peerMakeDead` (160 R2 terminals).
The six-call component passes its local 134-job target; the scoped Statements target passes 224 jobs. Frozen-source review has no correctness or premise findings.
Coordinated validation passes with the counts above; this extension does not close whole-run R2.

**Previous scheduler checkpoint.** The concrete Batch scheduler added five grouped exports (157 R2 terminals).
The complete ten-call family and whole trial filter pass their 173-job local target;
the scoped Statements target passes 221 jobs and the full proof tree passes 305 jobs. Coordinated
proof-gate, fresh kernel replay and fast-tier checks pass, with current counts above.
The prior receive-family checkpoint at `6c4d08f` had 152 terminals.

**Architecture decisions [AGENT 2026-10-13].** Separate resolved allocation identity from ownership of saved numeric references.
Share frontier algebra and the seven-field WG kernel projection; retain observation history outside the exception layer.
Strengthen access safety with resident uniqueness and allocation/epoch bounds, sharing caller proofs through explicit ambient contracts.
Observe saved peer entries when their predicates are demanded, carrying saved stamps without inserting source getters.
Factor IPv4 send into source tail stages that retain the entry route. Keep TX socket and rescheduling contracts explicit.
Keep the five handshake calls at exact local boundaries. Share canonical record, jitter, checksum, crypto and index frames,
preserving legacy signatures by projection instead of duplicating generated source matchers.
Factor buffer allocation from its exact original socket-send suffix, reusing the existing send observer and keeping ordinary returns distinct from Stops.

**Cookie frame decision [AGENT 2026-10-14].** Mask only the device's cookie secret/birthdate and both ratelimiter tables
in a full-Kernel projection; derive legacy frames by projection. This permits actual rotation/rate accounting while retaining
device presence, complete resident objects, allocator frontiers and `netIfindexNext` for concrete allocation safety.

**Receive composition decision [AGENT 2026-10-14].** Reuse the original load/source factor and existing lower-call observers;
share a failure-retaining bounded worker loop. Keep rescheduling explicit and separate handshake byte queues from resident skb stores.

**Scheduler trial decision [AGENT 2026-10-14].** Keep original copied-World consistency trials outside the committed access history;
prove their complete filter order/results and isolated safe prefixes separately. This avoids committing and then rolling back speculative releases.

**Allowed-IP access decision [AGENT 2026-10-14].** Share a full-Kernel mask of only nodes and trie roots/sequence,
including the existing exact `RemovalSource` parent tail, and project legacy frames from it.
Observe every demanded saved peer-map entry, including misses, interleaved with each hit's original saved-value write;
carry saved stamps across the fold without inserting getters. The mask retains `nextNode`, every resident object and every allocation frontier.

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
  Initiation's caller-jiffies read precedes jitter, which precedes the eager timer-guard getter. The worker performs `peerPut` after every normal initiation return, never after a Stop.
  Ambient socket, index-insertion and session create/put/replacement contracts are explicit and concretely discharged for `AllocationInv`.
  These are complete local calls; outer dispatch and historical reference ownership remain open.
- **Cookies:** `CookieAccess` covers `makeCookie`, `cookieMessageCreate`, `cookieValidatePacket` and `cookieMessageConsume`
  with their distinct byte-list, MAC-state and Unit results. The first three are resident-access-free by source inspection;
  unchanged endpoints alone would not establish that coverage. Rotation retains the age test, new-birthdate clock, random secret and fresh device read;
  creation draws its nonce first. Validation retains invalid MAC1, disabled/invalid MAC2, rate-limit, allocation and clock outcomes.
  Consumption observes the reference-taking index lookup, peer read, authenticated clock, fresh setter getter/write and final put.
  Missing MAC1 and failed authentication keep their ordinary puts; Stops skip later cleanup.
  `CookieStable` explicitly frames cookie/ratelimiter changes for an arbitrary ambient invariant; `AllocationInv` discharges it concretely.
  No authentication-success, packet-shape or index-owner-coherence premise is added.
- **Handshake receive and ingress:** `HandshakeReceive` observes endpoint extraction/update, cookie replies and the complete
  `receiveHandshakePacket`, including recorded load/decay, nested ordinary returns and Stops. False response-session creation still
  reaches common completion; peer RX stats precede device stats, then received/traversal timers and the final peer put.
  `ReceiveWorker` pops before handling, decrements only after normal completion, and composes the original iteration and whole
  4096-step loop with explicit rescheduling observations. Exhaustion remains the original Stop; no drain premise is added.
  `ReceiveIngress` covers CPU selection, `packetReceive` and `wgReceive`, including header rejection, busy/full queue paths and
  the existing complete `consumeData` observer. Header/DS-field leaves are resident-access-free by source inspection.
  Named cookie/socket/session/staging/statistics/queue contracts discharge concretely for `AllocationInv`; callbacks remain explicit.

- **Concrete Batch scheduling:** `BatchNapi`, `BatchActivation`, `BatchScheduler`, `BatchTrials` and `BatchCalls` cover
  both NAPI placements, activation work/occupancy tests, `cryptAhead`, iteration/run, dispatch, schedule and nested rescheduling.
  Eager saved-peer filtering records every tested entry, including misses, before callbacks; short-circuit `any` records only demanded entries.
  The schedule guard retains its eager device getter even when the next site is not NET_RX. Dispatch retains queue erasure before section start.
  `cryptAhead` retains append/encrypt/erase and error ordering. The original occupancy and record-budget loops retain every exhaustion Stop.
  Actual checksum, stack/NAPI, encrypt, decrypt, TX and receive callbacks discharge concretely for `AllocationInv`.
  The original consistency filter still discards each trial World/history. Its exact equation uses the separately observed trials in source order,
  including the first non-hidden Stop; every candidate has a safe isolated prefix from the same entry invariant, without claiming unevaluated candidates ran.

`PrefixControl` and `PrefixLoops` share exact conditional, bind, range, map, list and accumulating-fold laws.
`PrefixWorkers` shares original iteration and bounded whole-loop erasure and prefix safety, including callback/exhaustion Stops.
`PrefixBatch` shares exact section wrappers and pure-observation composition; `Framing/Batch` provides canonical scheduler frames with legacy projections.
Generic enqueue/decrypt contracts retain explicit softirq, IRQ-exit and rescheduling observers.
`Framing/KernelEffects`, `WGTime`, `WGData`, `WGHandshake`, `WGIndex`, `WGCookie` and `WGReceiveHeaders` provide canonical frames with legacy projections.
The index frame preserves the full kernel except the scalar index table, including device presence, resident values and frontiers;
the original device check and collision/draw records remain. Access-free helper coverage follows source inspection separately:
neither erasure nor an unchanged-Kernel theorem alone proves that an internally lifted helper contains no reads.

`AllowedIpsAccess` now covers the six local list/removal calls with complete result/World/Stop erasure and concrete `AllocationInv`.
`listDel` reads every tested captured map entry and writes only hits. `removeByPeer` reuses the exact shared node suffix;
`rootRemovePeerLists` preserves child pushes before the owner lookup/list check. `free` clears both roots and updates sequence before either walk;
`peerMakeDead` retains peer-list removal before trie removal, then hash removal before its final fresh peer read/write.
All source outcomes for missing nodes/owners, malformed arrays, duplicate IDs or cycles are retained, including original bound-exhaustion Stops and their access prefixes.
The node-only mask permits no peer/keypair/packet change; arbitrary ambient invariants explicitly supply node stability and scalar peer-list/hash contracts.
Concrete allocation discharges all of them, without shape, list-coherence or saved-owner premises. Insertion/allocation callers, complete peer removal,
netlink, timers and device lifecycle remain separate closure obligations. Node helper access-freedom is checked against source, not inferred from endpoint framing.

**Failure-prefix coverage.** Exact conditional equations retain the current refcount accesses, including writes before zero-refcount rejection;
release events occur only after successful final puts. Session birthdate-clock failure retains six events, peer initialization's first
cache-clock failure retains allocation/write, receive queue-record failure retains five accesses including the setter's nested read,
and handshake-completion clock failure retains four accesses. Cache-miss and keepalive allocation-record failures retain one peer read.
An empty-bitmap validator failure retains the initial keypair read and no write. TX jitter failure, after a successful original caller-jiffies read, retains the pending-timer peer read;
MAC age-test failure retains its peer read/write pair. The IPv4 clear/reset equation retains read/write before a reset-clock Stop,
but covers a source segment. These are original-run-conditioned equations, not accepted-run witnesses.
The timer guard's peer getter executes unconditionally before `andM`. Duplicate cleanup IDs and malformed queues remain admitted,
including a later Stop after an earlier free. Safe access prefixes establish neither delivery/order nor reference ownership.

**Remaining closure.** Whole-run environment and device-lifecycle coverage remains unproved: outer runners and deferred-unit callers,
socket setup/reinitialization, timer callbacks, peer removal, netlink and remaining resident scans. The Batch scheduler now discharges
its concrete worker callbacks; this does not discharge the separate R4 mutation-journal callback contracts or conservation obligations.
Saved scalar-reference ownership is separate: an aliased or dangling ID may stop after earlier safe accesses.
No C simulation is claimed. C initializes cache/handshake before incrementing the peer counter; the mirror increments/inserts first.
The proofs follow the mirror's order; that difference alone is not a lifetime counterexample.

**Historical accepted reference findings (through `7a92672`).** An eight-operation mirror run created 28 peers, started a stepped dump, deleted wg0,
created a new wg0 with 27 replacement peers, then received a chunk. The cursor retained raw slot 26, old identity 27,
with two references. Continuation cleanup instead released replacement identity 55, with one reference, removing it while
the peer list and public-key table still name slot 26. The received message is the already queued first chunk;
continuation generation performs the destructive put. This is reference retargeting and table incoherence, not resurrection of identity 27.

The guest rejects deletion with a pending dump (`wg_delete_with_dump_pending`), as the W1/W2 design requires.
`Env.wgDelete` then checked worker idleness but omitted that guard; `c047e64` restores it, including queued DONE chunks. C retains `ctx->wg`; the mirror resumes a Boolean-held cursor against the current device.
This was an accepted-mirror domain bug, not evidence of a Linux lifetime bug. Its explicit non-placeholder records are synthetic, not a fresh capture.
The historical replay checked five runner checkpoints, their count and original JSON equality.
The current replay instead checks the accepted pre-delete boundary and exact original/observer rejection at operation 3. The kernel-reduced
`stale_cursor_retargets_replacement` separately exercises `wgGetDeviceDone`; the historical full replay reached the bad put through dump-resume cleanup.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

A second historically accepted eight-operation variant gave replacement peer 26 an IPv4 `10.0.0.0/8` binding before the stale continuation released it.
The final checkpoint follows the actual device root: the prefix still names slot 26 while resident identity 55 is absent.
It previously checked eight checkpoint emissions, five specified projections and original-runner JSON equality, using explicit synthetic records.
The current check likewise rejects operation 3 before replacement allocation. The old accepted run ruled out unconditional owner-residency invariants on that mirror; it neither resurrects identity 27 nor alone proves packet misrouting
or disagreement with insert/remove history. The historical input recipe is unchanged; its current accepted domain has changed.

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
this does not close their stated enclosing-environment, lifecycle or ownership obligations.
Send-family review qualified the no-prior-access statement to buffer allocation refusal; response/session allocation has preceding peer accesses.
Receive review qualified common completion to a false `beginSession` return, excluding Stops,
and corrected the stale cookie-map sentence that left the now-covered local receive composition open.
Scheduler review checked source order, failed prefixes and whole-filter trial correspondence; all 13 frozen Lean hashes were reconciled without findings.
The stale map/report claims that scheduler callbacks remained open were corrected to the enclosing environment and lifecycle limits.
Allowed-IP frozen-source review found no correctness or premise issue. Its current-versus-pending opening was qualified to the preceding coordinated checkpoint;
source-outcome wording was corrected to avoid claiming all duplicate-ID lists fail.

**Effort.** The ledger records invocations, not an invented campaign total. Each historical cursor reproduction took under one second; both current rejection checks also passed in under one second.

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
| Four-call cookie family | 5: 2 / 3 | 11m41s |
| Handshake receive/worker and thin ingress | 7: 2 / 5 | 20m06s through full-build collection |
| Concrete Batch scheduler and separate trials | 18: 5 / 13 | 29m41s through full-build collection |
| Allowed-IP list/removal access | 6: 3 / 3 | 17m17s through scoped-target collection |

Earlier caller checkpoints took roughly 6–25 minutes each with 4–19 compilation invocations.
The first IPv4 architecture failed at proof-search heartbeat limits; its unused observer was removed.
The second uses explicit source tail stages and compiled source-equivalence, erasure and safety contracts.
Other failures were proof elaboration, simplification or integration failures, including broad-reduction heartbeat exhaustion,
bind/fold alignment, private-name normalization, metadata inference and duplicate matchers. They remain failures, not mirror findings.
One earlier tactic loop was deliberately stopped by its verified PID and repaired. The later IPv4, encryption, TX and handshake
checkpoints reported no interruptions or cap failures; their process exits were collected.
The send extension corrected four ordinary proof failures (explicit Session import, option-case alignment and discard/branch normalization).
Its final rerun incorporates the reviewed buffer-allocation qualifier; all exits were collected, with no interruption or cap failure.
The three send-family exports pass coordinated validation and final frozen-source review at `83d0df9` (140 R2 terminals).
The cookie extension corrected three ordinary build failures: a missing framing import and structure syntax,
identity-predicate transport, and legacy projection normalization. Its final 208-job target passes with 143 R2 terminals;
all five invocations' exits were collected, with no interruption or cap failure. Frozen-source review reports no findings.
The coordinated 280-job gate checks 266 terminal statements; fresh stock-kernel replay, the 60-job model build
and 94-test unit tier (22.079 seconds; one skip) pass. Earlier results above are historical checkpoints. The receive extension's five ordinary failures were an implicit event binder,
a missing postcondition-to-preservation projection, normalization of the device-stat update, and two Lean layout errors.
The corrected scoped target and full proof-tree build pass; all seven exits are collected, with no interruption or cap failure.
The frozen review's two wording findings are fixed as described above. Coordinated gate/kernel/fast-tier validation passes.

Validation details are retained in checkpoints `859d56a` (IPv4), `e6905f2` (encryption), `52a4602` (TX) and `d75f994` (handshake).
At `d75f994`, R2 has 137 terminal statements; the complete target, coordinated proof gate, fresh stock Lean kernel replay,
model build and unit tier pass. Current campaign counts are recorded above. Unchanged cursor witnesses were not rerun for these extensions.
No differential check or guest was run for this proof work.

The allowed-IP extension's three ordinary failures were loop/matcher elaboration, recursive source-loop/continuation alignment,
and explicit projection arguments. All six capped builds were collected (exit codes `1,0,1,1,0,0`); no interruption or cap failure occurred.
The final 134-job component and 224-job Statements targets pass with 160 R2 terminals. The first coordinated gate failed
on an ambiguous legacy/canonical `getNode_sameKernel` reference in `RxCompletionFrame`; explicitly selecting the canonical theorem
repaired it without changing a statement or premise. Independent review checked the repair and frozen sources. The repeated gate,
fresh stock kernel replay and fast tier all pass. Writer handoff and cleanup took 17m56s; coordinated checks followed.

**Ranked mirror-shape recommendations.** Pending-dump deletion rejection is resolved by `c047e64`, with both current rejection checks passing.
(1) If that domain expands, retain the actual device lifetime in the cursor as C does: altitude-preserving, with separate validation.
(2) Retain named allocation, deletion and same-object update boundaries: altitude-preserving operational structure.
No production history field is proposed, and no mirror change was made for these proofs.

The scheduler extension's second build failed because a generic wrapper was moved to a new module while that invocation's dependency graph was already running.
That was a build-input timing error, not a cap or interruption. Subsequent invocations kept input sources fixed until their exits were collected.
The remaining failures were ordinary source-factor/type elaboration: pure scan insertion, discard normalization, paired match cases,
explicit queue-update inference, source bind normalization and `Except.map` reduction. No mirror semantics or theorem premises changed.
All 18 exits were collected: five passes, the timing failure and twelve ordinary elaboration failures, with no cap or interruption.
The final 221-job Statements and 305-job full-tree builds pass with 157 R2 terminals; frozen-source review found no unresolved issue.
Validation was collected at 03:35:55 UTC, 29m41s after the token grant; token handoff and cleanup took 30m55s in all.
Coordinated proof-gate, fresh kernel replay and fast-tier checks pass. Independent review reconciled all 13 Lean files
and the final report/register with no unresolved findings. The unchanged cursor witnesses were not rerun.

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

The four deep-graft terminals classify normal `add` endpoints and prove successful `add`,
actual-root lookup and `insert` refinement. They preserve both roots, supplied
opposite-family representation, validity, unique IDs, conditional compression
and exact frontier/sequence effects. Second-allocation refusal still consumes
one ID and filters every peer list; it does not imply whole-state rollback.
Only the requested peer must be resident; old owner labels may be orphaned.
These normal-return contracts do not classify record Stops. Independent source
review, the coordinated gate and fresh kernel replay pass.

`InsertionCases` factors seven established case proofs into reusable contracts;
public signatures and the stronger branch-specific exact endpoints are retained.
`InsertionDispatch` derives all five cases from the original total placement
witness and the final context edge [AGENT 2026-10-14]. No path/exactness/stopping
predicate is assumed by its callers. Five new terminals classify normal `add`
and `insert` returns, establish refusal effects, and connect successful insertion
to actual-root longest-prefix lookup over independently updated flat bindings.
The common success contract gives representation, root/frontier/sequence,
validity, unique IDs and conditional compression; it does not unify every Device
field or peer-list effect. Both refusal endpoints remain exact, including the
second refusal's consumed ID and pointwise all-peer filtering. The opposite root
value and any supplied opposite-family representation are preserved; linkage of
that supplied tree is not inferred. Input address/CIDR bounds, valid representation,
unique node IDs, whole-store freshness and resident target peer remain explicit.
Old owner labels may be orphaned. Invalid-input returns and record Stops are
outside the bounded-input normal-return classification. Independent frozen-source
review found no correctness issue; the coordinated gate and fresh stock kernel replay pass.

**Pure removal.** `Removal` adds one recursive `Tree.eraseId` and a local
`compact` helper [AGENT 2026-10-14]. Exact ordered entry filtering and node-ID
subsequence hold on arbitrary trees. Validity and enclosing child geometry are
preserved, output is compressed, and independent longest-prefix lookup agrees
with the filtered entries. Node-ID uniqueness and frontier bounds are inherited.
Absent-ID identity requires input compression: malformed ownerless unary nodes
would otherwise be normalized. With compression and distinct IDs, at most two
IDs disappear and only a targeted leaf can make a nonempty subtree empty.
A binary target retains its node ID after owner clearing.

`ContextRemoval` derives the precise locality equations: a binary/unary target
changes only its focus; a leaf either retains its owned parent or promotes its
nonempty sibling through an ownerless parent. Outer ancestors and siblings keep
their exact pure data, with ID separation derived from whole-tree uniqueness.
These equations explain the source's target-plus-immediate-parent shape; they
are not original `removeByPeer` execution or deallocation-event theorems.
Six new terminal exports pass the local 110-job target and full 286-job proof
build. Independent frozen-source and documentation review found no issue; the
coordinated proof gate, fresh stock kernel replay and fast tier above pass.

**Local original removal.** `RemovalSource` imports only the original
`WG.AllowedIps` and factors the exact node-only suffix after `listDel`; this
keeps later R2 access/frame proofs independent of the higher list-mutation
proof imports [AGENT 2026-10-14]. Its unconditional `rfl` equation reproduces
original `removeByPeer`, including the saved peer list, empty test, pre-loop
sequence increment, both continues and final iteration record. It covers all
inputs and Stops as an equation; it does not expose a failed-prefix World.
The pristine C removal at `allowedips.c:303–341` was inspected read-only. No
simulation against the C or mirror change is claimed.

`RemovalMirror` proves total exact endpoints for a binary target and a leaf or
unary target whose saved parent tag selects a device root. Binary removal needs
only a resident target with two populated child slots; those children are not
read. Unary removal additionally needs a distinct resident child. Each step
retains source list deletion before target lookup and the exact branch order.
The full resulting kernel is specified, with every peer list filtered at the
removed ID and other raw owner labels preserved. The binary target remains resident
with no owner; leaf and unary targets are erased. The sole child's complete
record changes only at its backlink. Root-tagged contracts do
not require or infer that the input root points to the target.

`RemovalStore` gives pointwise whole-node-map equations, selected/opposite root,
frontier and sequence effects, and local representation transport. Binary owner
clearing represents pure erasure under compression and uniqueness. Unary
promotion derives parent/descendant separation from tree uniqueness and represents
the surviving subtree. These are separate local execution and structural facts;
the selected-root/whole-forest bridge and complete saved-list loop are established
by the later layers below, with explicit input coherence for the whole loop.
The raw nonroot source arms are covered by the extension below. No arbitrary-world saved-list coherence, owner
residency, history invariant or packet authorization is inferred. One step keeps
the sequence unchanged; the source equation retains the original loop's increment.

Eight new terminals pass the 113-job scoped target. Independent frozen source
and documentation review has no unresolved findings; its owner-label wording
correction is fixed. The coordinated proof gate, fresh stock kernel replay and
fast tier above pass and include these eight terminals.

**Nonroot original removal extension.** `RemovalSource.removeParentTail` factors
only the final collapse suffix, starting with the fresh parent getter after
freeing the target [AGENT 2026-10-14]. This small boundary keeps each source
reduction local and avoids reducing the entire source body at once;
the original loop equation still closes by `rfl` with only the original import.

`RemovalChildMirror`, `RemovalCollapse` and `RemovalSteps` prove total original
iterations for nonroot unary detachment, leaf removal with an owned parent,
and leaf removal that collapses an ownerless parent through a root or child
slot. Input premises name resident target/parent records, readable target and
opposite child slots, valid slot indices, and distinct identities; sibling and
grandparent residency is required only when that path dereferences them.
Optional absent siblings are included. No owner-residency, saved-list coherence,
input-root linkage or desired output is an execution premise. Original `set!`
behavior is retained without a parent-array-length condition in arms that do
not read its child array. List deletion still precedes the target getter.

The exact collapse-prefix equation derives the owner/sibling reads from the
updated parent after detachment, then frees the target and enters the continuation
with its fresh parent read. It requires
no sibling/grandparent residency and leaves their later Stops in the actual
continuation. It equates results, complete successful Worlds and exact Stops;
it supplies no event journal or returned World on failure. The total endpoint
theorems separately discharge the later reads from input snapshots and ID
separation. No C simulation or mirror modification is claimed.

`RemovalChildStore` gives pointwise whole-node-map equations in source write
priority, even for aliased arguments to the pure endpoint expressions. The
execution premises supply the separation under which target and collapsed
parent are retired. Promoted siblings retain every field except their backlink;
other raw owner labels remain intact. Retained-parent/child-collapse arms keep
both roots; root collapse updates its selected family root and frames the other.
Every arm preserves `nextNode` and the per-step sequence and filters all peer
lists exactly. These raw local contracts supply the represented refinement below;
they do not themselves assume or establish saved-list coherence.

Nine grouped exports pass the 117-job Statements target, bringing R3 to 62
terminals. Independent frozen source, premise, store, export and documentation
review found no correctness defect; its two documentation precision findings
are fixed. Coordinated proof-gate, fresh stock kernel replay and fast-tier checks pass,
with current counts above.

**Represented target removal.** [AGENT 2026-10-14] Use the existing exact
source endpoints behind structural focus and retained-parent/grandparent
transport, rather than reduce the full source again. This keeps source order
and late Stops in the checked raw layer while the new layer derives linkage
and alias separation from the input representation. Carry resident-only list
coherence through the saved-list fold as an explicit input invariant; its
initialized preservation belongs to the subsequent history layer.

`RemovalContext` obtains a real focus from explicit node-ID membership,
decomposes the last context edge and separates the two families through their
encoded widths. `RemovalTransport` proves the local represented store updates;
`RemovalCases` connects all seven structural cases to their original total
source WPs. `RemovalDispatch.remove_forest_total` derives those cases from
`ForestRep`, per-tree compression and distinct node IDs. Target membership is
an explicit input, not a consequence of forest representation. Compression
supplies the nonempty sibling at ownerless-parent collapse. No owner residency,
saved-list coherence, desired endpoint or successful-return premise is used
to obtain total execution.

The returned full Kernel endpoint represents `eraseId` in both families,
preserves every node outside the original forest and erases every represented
ID absent from the resulting forest. Other device/Kernel fields are framed;
all resident peer lists are filtered exactly, while node allocation frontier
and the per-step allowed-IP sequence are unchanged. `NodesBelow` is preserved
when supplied. Valid prefixes additionally yield valid, compressed,
duplicate-free results, ordered entry filtering and ID sublists. Original
`findNode` at either actual resulting root selects the longest-prefix winner
among those filtered entries and preserves the resulting Kernel.

The earlier raw all-input source equations continue to cover malformed/missing
targets and late Stops. The represented step theorem proves normal completion
under its structural inputs; it does not reinterpret an absent original target
as a no-op and supplies no World on a failed computation.

**Complete coherent peer removal.** `RemovalLists.ResidentLists` states, for
resident peers only, that the saved list is duplicate-free and contains exactly
the IDs of entries carrying that peer label. Raw orphan owner labels remain
permitted. `OwnedIds` demands owned entries for saved IDs, rather than membership
in the structural tree alone. Exact entry filtering proves every later saved ID
survives prior removals, including ownerless-parent collapse.

`RemovalLoop.remove_saved_total` runs the original fixed `forIn` list and
composes both-family representation, all-peer list filtering, frontier/sequence
preservation, complete device/Kernel framing, outside-node preservation and
retirement of every disappeared represented ID. It does not reread a changing
peer list. `RemovalPeer.removeByPeer_total` then includes the original initial
peer getter, empty-list branch, one sequence increment for a nonempty list,
saved loop and final false iteration record. Empty lists return at their original
branch without the final record. Residency and list coherence are explicit
input premises, not consequences of arbitrary forest representation.

The complete operation preserves resident-only coherence and filters each
family's entries by the target peer label. Owner functionality is derived from
the represented node store, so this filter is proved from saved-list membership.
The target remains resident with its list empty; all other peer fields retain
their input values. All peer-list effects are specified by ordered filtering at
the saved IDs. Validity, compression, distinct IDs, ID sublists and supplied
node-frontier bounds survive. Original `findNode` at the actual resulting family
root selects the longest-prefix winner among exactly the entries of other peers.
This is an operation theorem conditional on input coherence, not initialized
insertion or configuration-history closure, and raw labels do not establish
cryptographic identity or packet admission.

Six grouped exports (three single-step and three whole-peer) pass the final
Statements target: 125 jobs and 68 R3 terminals. The full proof build passes
332 jobs. Independent source, premises, retirement, loop and final export review
has no unresolved correctness finding. Frozen documentation reconciliation corrected
two stale validation-status labels. The coordinated 332-job gate checks all 335 declarations;
fresh stock kernel replay, the 60-job model build and 114 unit tests (23.573 seconds,
one skip) pass. These checks include the six new exports and leave the remaining
history and packet-path obligations explicit.

**Remaining claim.** Establishing insertion/list coherence and owner-frontier
bounds from initialization, and propagating them through configuration histories,
remain open.
Parsed-input bounds and history invariants still need propagation through all mutations.
Both packet paths follow R2. Owners are raw peer slots, not allocation or
cryptographic identities; no liveness/ownership claim follows from tree lookup.
The historical R2 orphan-owner replay above constrained ownership invariants over its former accepted domain;
`c047e64` now rejects that recipe before deletion. It is not an R3 counterexample for the current runner. No R3 statement has been reshaped
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
| Unified insertion dispatch | 11: 8 / 3 | 12m08s |
| Pure removal and context locality | 9: 6 / 3 | 9m05s validation; 10m16s writer-token ownership |
| Local removal source and endpoints | 7: 2 / 5 | 14m17s through source freeze; 14m49s through handoff receipt |
| Nonroot removal and parent collapse | 9: 3 / 6 | 16m06s through frozen handoff preparation; 12m48s through scoped-target collection |
| Represented forest and coherent peer removal | 29: 14 / 15 | 43m01s through final full-target collection; 47m57s writer-token ownership |

The represented-forest and coherent-loop tranche used 29 capped builds: 14
passes and 15 ordinary failures, including two elaboration heartbeat failures.
The first 17 calls closed the single-step forest bridge; the 12-call continuation
closed resident coherence and the complete saved-list loop. Failures concerned
implicit binder inference, context simplification, full-record definitional
reduction, list/Boolean lemmas and monadic bind elaboration. Explicit local
projections and a small `Except.bind` run equation resolved those issues without
changing the mirror or weakening input obligations. All exits were collected;
there was no cap hit, crash or interruption. One patch-context mismatch made no
change to its affected file. Final scoped/full builds passed 125/332 jobs. No
runtime reproduction changed or was rerun. The worker returned the token after final
review corrections and owned-log cleanup; all four coordinated trust/build/unit
invocations then passed. Campaign scope and whitespace checks pass.

The staged child architecture replaced a failed monolithic proof; this was not
a mirror finding. Three deep-graft source-factor attempts hit Lean heartbeat
limits. Including the original final return in the proof-side cut point made
the all-input equality close by `rfl`. The final targeted/full builds passed
106/273 jobs; all exits were collected, with no cap or interruption.
Unified dispatch's final targeted/full builds passed 108/278 jobs. One failed
pre-write relocation script changed no files; its following unchanged-target
build passed and is included in the ledger. Three Lean builds failed: one binder
error and two default-heartbeat failures in rollback metadata. Projection-only
simplification closed the latter without raising limits. All exits were collected;
no cap or interruption occurred. Earlier checkpoint validation is retained in the
corresponding commits; current combined validation is above.

Local removal used seven capped builds: two passes and five failures. The first
broad body proof hit simplifier/heartbeat limits; concrete execution equations
closed without changing the source. The remaining collected diagnostics were
residual definitional `Except.map` goals, missing peer-index binder types and
unfolded metadata projections. Invocation three returned failure but its `/tmp`
log was read-denied by nono; its diagnostics are unavailable and that owned file
was deleted. No sandbox/global setting changed. All process exits were collected;
no cap hit or interruption occurred. The final scoped target passed 113 jobs;
there was no separate full build in this worker slice.

Nonroot removal used nine capped builds: three passes and six ordinary failures.
Failures concerned declaration layout, an unreduced Option guard, a redundant
closing tactic, map-lookup simplification and metadata projection elaboration.
Increasing the metadata heartbeat limit did not resolve it; explicit projection
reduction then passed at the default limit. One failed patch application matched
no text and made no change; it was not a build invocation or interruption.
The final scoped target passed 117 jobs at 04:15:41 UTC after the 04:02:53 token
grant. Every process exit was collected; no cap, crash or interruption occurred.
No separate full proof build or coordinated gate was run in this worker slice.

Pure removal used nine capped builds, six passing and three ordinary failures.
The failures concerned namespace/implicit-ID elaboration, simplified conjunction
shapes and rewrite ordering in local compaction proofs. The final
targeted/full builds passed 110/286 jobs; every exit was collected, with no cap
or interruption. Owned build output was removed at handoff. Two subsequent
read-only planning turns disconnected after validation had completed. All four
dirty worktrees, including nonignored untracked files, were snapshotted after
each interruption before further edits; no build was interrupted.

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

`RingGeometry` now represents a positive-size ring by tail `t`, a physically occupied stale list,
and a live FIFO. Slots are `(stale ++ live)[offset n t j]?`; the bounds are
`t + stale.length < n` and `stale.length + live.length ≤ n`. Original initialization has both lists
empty. Physical fullness is exactly total occupancy `n`; original peek, count and items expose only
the live list, retaining multiplicity. Size zero has separate unconditional refusal/empty laws.
`RingSteps` proves exact original production and consumption: a physically free produce appends one
live occurrence; consume moves the live head into stale storage or clears exactly the stale prefix
plus that head. The original batch threshold and ring-end wrap determine retirement, for every batch,
including zero and values larger than the ring. Successor bounds are proved, not postulated.
No distinct-payload, endpoint-validity, or ownership premise is added. The six new terminal exports
pass the local target (176 jobs), coordinated proof gate, fresh stock kernel replay and frozen review.

[AGENT 2026-10-14] Use direct tail-relative slot offsets and exact `ringOf` equalities to separate
physical stale occupancy from logical live contents; the geometry checkpoint deferred finite journals to a separate slice.

**Finite ring journals.** `RingJournal` executes the existing `tryProduce` and original `consume`
for each command, recording every accepted/refused offer and successful/empty poll. Its invariant
retains the exact physical `ringOf` and proves `admitted = consumed ++ live` and
`consumed = retired ++ stale`. Retirement therefore clears already-consumed physical slots; it
is not a packet-loss disposition. `run_inv` supports any represented entry ring and every batch value.
Initialized conservation uses the actual original `PtrRing.init n` batch; for size zero, an exact
history equation records only refusals/empty polls and preserves the complete arbitrary entry ring.
Finite conservation permits a nonempty live suffix and implies no eventual consumption.

`RingMap` proves payload mapping commutes with original full/peek/produce/clear/discard/consume,
count/items, guarded production and initialization, on arbitrary rings without injectivity.
`RingOccurrences` increments an ordinal for every offer, including refusal, and proves exact erasure
of all journal outcomes and the final physical ring. From initialization, consumed and live
occurrences partition admissions, with distinct ordinals across their joint list. Duplicate payloads
are unrestricted. Arbitrary-ring erasure does not assert freshness relative to preexisting contents;
journal ordinals are neither packet allocation identities nor lifetime stamps.

[AGENT 2026-10-14] Keep finite occurrence journals separate from packet identity and scheduling;
derive source admission guards independently, retaining the existing `EnqueueResult` API.

**Original enqueue and queues.** `Queues/Enqueue` classifies complete `enqueuePerDeviceAndPeer` normal
returns: success produces the item; `-ENOSPC` leaves the ring unchanged; `-EPIPE` means physical
fullness and an unchanged ring. The earlier peer-capacity test retains priority, and
peer-queue/packet-state updates may precede `-EPIPE`. Missing objects and queue-work failures remain
Stops. No ownership or queue-validity premise, or unchanged-peer-state conclusion, is imposed.
`EnqueueAdmission` independently derives from each original TX/RX body that a zero return requires
an existing, non-full entry ring. The older success alternative alone does not establish that guard.
The guard theorems themselves are successful-return implications. The RX and TX source journals below
observe installed mutations; concrete RX scheduler composition is described below.
Passing the full test and then stopping in queue-work emits no admission.

**RX source ring journals.** `RxRingJournal` relates each reached history to a finite execution of the
original guarded ring operations. `Inv` links its endpoint to the complete device interface-index/ring
cell on normal return; `Safe` retains only an existential replay ring on Stop. `RxRingFrames` proves
this cell is preserved by the actual lookup, reference/release, packet and decrypt helpers.
`RxRingCuts` derives enqueue outcomes and the independent free guard from original source, without
endpoint assumptions supplied by callers. `RxRingEntry` observes complete RX enqueue and `consumeData`.
Admission is emitted after installed production; its deferral across the final pure return crosses
no source effect. EPIPE emits a refused offer; ENOSPC and pre-install Stops emit no ring event.
Neither refusal is classified as packet disposal. A later consumeData Stop retains an emitted offer.

`RxRingWorker` factors the original decrypt step at branch-checked consumption and installed ring
replacement, before later packet getters, decryption and publication. Empty polls are recorded after
the original empty-branch check succeeds. Complete step/iteration erasure preserves result, successful
World and exact Stop on every input. Softirq still precedes the ring read. IRQ, softirq and rescheduling
observers have explicit erasure and journal-preservation contracts, allowing their own refined ring
operations; the concrete RX scheduler below now discharges these callbacks. No saved-head, packet-ID uniqueness,
valid-World, homogeneous-batch or ownership assumption is introduced.

From an initialized ring, all four observed calls retain admission/consumed/live conservation and
an ordinal refinement with exact event/ring erasure and joint consumed/live ordinal distinctness.
Positive size also retains the retired/stale physical witness; zero size remains covered.
Duplicate skb numbers are permitted. The interface index is not a fresh lifecycle identity, and the
ordinal witness is an existence result, not uniqueness of the refinement itself.

[AGENT 2026-10-14] Place RX journal observations at installed-ring cuts, using the complete enqueue
outcome wrapper only because its last mutation is followed by a pure return. Keep callback contracts
explicit and keep failed-prefix replay separate from any unavailable failed World.

**Shared source core and TX journals.** `RingSource` factors the finite replay relation, full-cell
invariant, failed-prefix safety, outcome observation and initialized conservation over an arbitrary
ring payload type. The existing RX API and terminal statements retain their meanings and signatures.
Generic endpoint contracts are explicit; both RX and TX cuts derive them from their original bodies.
A generic normal-endpoint contract alone does not establish source event completeness: that also
uses the concrete enqueue/poll boundaries, whose installation has no subsequent effect or failure
before return. This is refinement of the executable mirror, not a C simulation.

`TxRingFrames` retains the entire interface-index/encrypt-ring cell through actual packet, peer,
keypair, CPU and publication helpers. `TxRingCuts` derives the complete original enqueue endpoints,
independent non-full success guard and branch-before-install consume cut. `TxRingEntry` observes
complete enqueue and `createData`: ENOSPC emits no offer; EPIPE emits refusal and still reaches the
original DEAD publication; later publication or cleanup Stops retain reached events. Saved-device
reads are justified by concrete intervening frames, without a convenient World-validity premise.

`TxRingWorker` observes original `encryptPacket`, step and iteration. Softirq runs before the ring
getter and may itself perform observed ring operations. Installed consumption is recorded before
empty-list, head/member getter, checksum, encryption, setter-reread and publication failures.
Padding remains before checksum; a normal encryption failure marks DEAD, breaks the packet walk,
and publishes the original whole list. Checksum, softirq and rescheduling callbacks have explicit
erasure and journal-preservation contracts; the concrete checksum contract is discharged separately.
No ring frame is asserted for NAPI/stack callbacks, which can enqueue TX work.

Initialized conservation counts whole-list ring occurrences, retaining empty/duplicate payloads in
the underlying model and original empty-item Stops at source calls. It proves neither uniqueness of
constituent packet IDs nor ownership of saved heads, keypairs or peer-queue aliases. As for RX, only
normal return links the replay ring to the actual World; the interface index is no lifecycle stamp.

[AGENT 2026-10-14] Share the payload-parametric source-journal core between RX and TX, preserving the
RX API. Compose TX events at installed mutation cuts and expose callback contracts rather than
framing callbacks that may enqueue work.

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

**Concrete RX scheduler calls.** `RxRingCallbackFrames` and `RxRingNapi` prove the complete
interface-index/decrypt-ring cell frame through actual rxPoll/GRO, stack delivery and IRQ placement.
`RxRingEncrypt`, `RxRingSocket`, `RxRingTx` and `RxRingHandshake` cover the non-decrypt workers,
including both socket families, loopback, keypair/session changes, peer deletion, TX staging and
cryptAhead's actual encrypt iteration. No valid-World, resident-owner, packet-distinctness or
homogeneous-batch premise is added. These are normal-endpoint frames; failed executions have no
returned World. Source inspection separately establishes that the lifted callees contain no decrypt-ring
mutation cut, so their whole-call lifting does not hide an RX journal event on a later Stop.

`SourceScheduler` shares original run/dispatch/schedule control with activation and NAPI observers as
parameters. `RxRingScheduler` instantiates it concretely: decrypt activations use the checked worker
journal, while other activations preserve the cell. Eager pending-NAPI getDev, queue erase before
section start, fallback dispatch order, cryptAhead, suspension/resumption, ambiguity and every record
or occupancy budget failure retain their original position. Unconditional erasure covers the complete
result, successful World and exact Stop. Its six-call family includes consumeData and nestedResched.
The ring invariant has no remaining callback premise at these concrete call boundaries.

`RxRingTrials` relates separately observed activation trials to the original consistency decision and
ordered filter. Hidden mismatch means false; the first non-hidden Stop propagates. Each trial begins
at the caller's World/history; its returned World and events never enter committed history. Every
candidate has a separately safe reached prefix, without a claim that every candidate was evaluated.
Initialized conservation extends a prior refined history that may already describe a nonempty current
ring. Admission/consumed/live conservation and distinct offer ordinals also cover size zero and
duplicate skb values. The retired/stale structural representation requires positive size; a failed
prefix has only an existential replay ring.

[AGENT 2026-10-14] Share scheduler control through callback-parameterized proof-side bodies;
keep copied-trial histories separate from committed ring histories. Canonical read-only scheduler
frames replace duplicate legacy proof bodies by projections, preserving their theorem statements.

**Remaining scope.** TX-ring callback/scheduler composition, enclosing ingress/runner and lifecycle
operations, worker-local ownership and joint peer-queue/packet-store conservation remain open.
Concrete RX scheduler refinement alone implies neither packet-store emptiness nor whole-schedule
no-loss/no-duplication. Finite-prefix conservation must retain pending obligations and cannot infer
eventual delivery. The interface index does not distinguish fresh lifecycle resets. Initialized
index/keypair affiliation, lifecycle purges versus anomalies and operation-specific RX quiescence
still need source-derived invariants; none is assumed by these erasures or smuggled into the final
charter claim. There is no new accepted counterexample or Linux simulation claim in this slice.

**Validation and effort.** The RX scheduler extension adds six grouped exports (64 R4 terminals).
The concrete core passes 208 jobs and the complete Statements target passes 230 jobs. Coordinated
proof gate (325 jobs, 329 terminals), fresh stock kernel replay, 60-job model build and
110-test unit tier (23.853 seconds, one skip) all pass. Independent review has checked
source/control, callback discharge, separate trials, exports and all fourteen frozen hashes;
no unresolved correctness or scope finding remains. Fifteen sequential capped builds used 30m07s from the 04:49:27 UTC grant through final
collection at 05:19:34: four passed and eleven failed ordinarily. Failures concerned type inference,
normalization, WP leaf selection/depth and an integration-only duplicate generated matcher for
Activation.hasWork. Canonical hasWork/occupancy SameKernel proofs now live in Framing/Batch, with
legacy EnvLeaves statements unchanged as projections. All exits were collected; no cap or interruption
occurred. Review corrected copied queue-frame wording, a normal-endpoint versus Stop distinction,
the canonical frame header's read-only scope, and the positive-size condition on retired/stale
representation; these did not change theorem statements.
The prior TX source-journal extension added five grouped exports (58 R4 terminals).
The complete local target passes 193 jobs. Coordinated proof gate, fresh stock kernel replay and
fast-tier checks pass, with current counts above. Independent frozen source and scope review has
no unresolved correctness findings; its report-status finding is corrected by this refresh.
The preceding RX source-journal extension added five grouped exports (53 R4 terminals).
The 187-job scoped target passes. Independent frozen review has no unresolved findings;
the coordinated proof gate, fresh stock kernel replay and fast tier above also pass.
The preceding 48-terminal checkpoint has seven journal/map/admission exports that pass
the 181-job local target. Its independent frozen review had no findings; the combined
proof gate, fresh stock kernel replay and fast tier above include the preceding pure-journal extension and the `7a92672` carry.
The prior 41-terminal checkpoint is `15a56ad`. Before that geometry extension,
**105 capped local invocations comprise
36 passes, 68 ordinary failures and one deliberate termination**. All outcomes were collected; no memory
cap was hit. Corrected failures concerned elaboration, matching, simplification or replay assertions.
Owned temporary outputs were removed. These proof slices made no mirror edits, main integration, push or
new QEMU/differential run.

The general ring extension took 7m42s and used 13 capped invocations: four passed and nine failed ordinarily.
Failures concerned Boolean simplification, inferred type parameters, list/array lookup normalization,
and dependent-match export elaboration. All exits were collected; no cap or interruption occurred.
Review corrected the report’s “live ownership” wording to “live contents”; no unresolved finding remains.
Its exact one-step laws were the prerequisite for the new finite-journal component; pipeline conservation remains open.
The journal extension used 12 capped builds (four passes, eight ordinary failures) and one passing
scoped check, taking 11m11s through local validation and 12m02s of writer-token ownership. Failures concerned
Option/conditional normalization, inferred payload types and batch, induction unfolding, WP simplification,
and existential-witness elaboration/tactic syntax. All exits were collected, with no cap or interruption.
Independent review reconciled the source, seven exports and scoped documentation with no findings.
That pure journal slice did not yet claim source mutation-event placement or scheduler composition.
The RX source-journal extension took 19m07s from token grant through collected target validation,
using eight capped builds: two passed and six failed ordinarily. Failures concerned projection/type
inference, WP witnesses, bind/map and dependent-match normalization, and constructor namespace
resolution. All exits were collected; no cap or interruption occurred. No source or premise change
was made to suppress an original Stop. A separate scoped check failed on the English verb
“admit” in a new comment; the wording was replaced because the trust gate rejects that token
throughout the proof tree. The corrected scoped check passed; both check exits were collected.
Total writer-token ownership was 21m45s, including review corrections and cleanup.

The TX source-journal extension used eight capped builds: four passed and four failed ordinarily,
taking 11m58s from the 03:42:59 UTC grant through collected target validation at 03:54:57 UTC.
Failures concerned a missing projection import, frame normalization/name resolution, the local
history-event type, and EPIPE constant namespace normalization. All exits were collected; no cap or
interruption occurred. Total writer-token ownership was 13m44s. The source controls and theorem
premises were not weakened to resolve them.

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
and remaining pipeline limits. RX source-journal review corrected “unique ordinal refinement” to
existence with distinct ordinals, and “epoch” to interface index: the cell does not discriminate
lifecycle resets. Both corrections preserve the formal contracts.

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

**Lifecycle source discrepancy at `c047e64` (not yet a replay finding).**
`Receive.ratelimiterAllow` now creates and updates IPv6 entries in `table6`,
but `Device.ratelimiterInit` resets only `table`, and `gcEntries false` walks
and clears only that IPv4 table while reporting no IPv6 entries. The local
Linux `ratelimiter.c:55–83` walks both families and clears every entry on the
last uninit (`:205–221`); reinitialization allocates empty tables. Thus the
mirror source appears to retain IPv6 rate-limit state across the last uninit
and reinit. This was found while preparing R2 lifecycle composition and checked
against both sources. No accepted runner reproduction or differential result
has yet been established. It is not a Linux bug claim or a premise of the
cookie-exclusion theorem, and the campaign has not edited the mirror. A
follow-up should exercise IPv6 cookie admission, device deletion/recreation
and admission from the same source /64.


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
