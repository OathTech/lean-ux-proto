# Proofs about the mirrors

`Leanux/Proofs/` is the repository's proof tree: every theorem about the
executable mirrors lives there and nowhere else. Proofs are a validation
channel for the models beside the differential check, under Rule Zero: the
mirror is never edited to let a proof close; a proof that cannot close is a
report against the mirror, settled by the check. The standing rule and the
gate are in [AGENTS.md](../AGENTS.md); this file is the map of the tree and
the register of its results.

## Layers

The tree is laid out by layer and by result. Shared layers sit at the top,
subject-specific layers under the subject, and each result in its own
directory whose `Statements.lean` is the gated surface.

- `Leanux/Proofs.lean`: the root. It imports every result's `Statements`
  module and the checked counterexamples; `lake build LeanuxProofs` builds
  exactly this closure, outside the mirror's default build.
- `Leanux/Proofs/Framing/`: generic operational framing over the mirror's
  state and monad. `Basic` says which state an action leaves unchanged, with
  the lifetime distinction a reused keypair slot needs; `WP` is the
  weakest-precondition form; `Allocation` names the mirror's private
  allocation helpers for proofs. `Projection` composes and factors arbitrary
  equality views; `WGKernel` selects the seven dedicated WireGuard kernel
  fields, and `FSFileRefs` proves six original file-reference helpers once
  for the keypair, peer and packet projections. These are immediate-return
  frames, not preservation of queued work or later scheduler effects.
  `Index` exposes exact source equations for the recorded index-unhash helpers.
  `KernelEffects` shares record-consumer and refcount contracts; `WGTime`
  frames the original recorded age tests and jitter. `WGHandshake` frames
  seven original explicit-input crypto helpers over the full Kernel; `WGIndex`
  preserves every Kernel field except the device's scalar index table, including
  allocation geometry and device presence. Legacy signatures project these
  canonical contracts. `Batch` shares section-wrapper and record-only scheduler
  frames over the full Kernel, with legacy interfaces derived by projection. `Kernel`
  proves original kernel helpers over the full WG view, with the old keypair
  interfaces derived by projection. `Tools` shares loop/map contracts and proof
  setup without depending on the keypair frame hierarchy. `Signal`, `PipeAux`
  and the seccomp frames preserve that full view; `Control` shares compiler
  continuations and frames finite repeat loops using an explicit decreasing
  rank. `Prefill` preserves the view across arbitrary translated filters.
- `Leanux/Proofs/Logged/`: logged copies of mirror functions with erasure
  theorems (erasing the log gives back the original run, state, result and
  failure), from the validator (`Basic`, `RxPoll`) through the workers, the
  scheduler, the environment operations and the syscalls to the runner
  (`Runner`). The erasure core (`Outer`, `Tools`) is independent of what is
  logged. Validator observations carry acceptance events; `Checkpoints` observes
  arbitrary projections at committed operation boundaries, with exact erasure
  to the original runner and an exact singleton-append theorem. `Prefix`
  instead retains observations when execution fails, with exact original
  result/World or error erasure and compositional prefix-safety contracts.
  `Focus` injects a local observer's new suffix into a combined event stream
  without changing the previous interleaving. `Projected` erases extra local
  accumulator data while retaining the original result, complete World and Stop.
  `ProjectsPrefix` compares two failure-retaining observers by projecting both
  their results and event histories, including every stopped prefix.
  `PrefixGro` carries the original GRO state, batches and held packets with
  explicit callback erasure and preservation contracts. `PrefixLoops` gives finite range
  and map/fold composition plus accumulator-dependent list-loop contracts for
  failure-retaining observers. `Capture` retains exact original-action run
  witnesses with erasure and prefix contracts. `PrefixWorkers` composes one
  original worker iteration with explicit step and rescheduling contracts.
  `PrefixBatch` shares exact worker-section observations and callback preservation.
  `TimerPass` observes completed original timer, clear/send-worker and crypt
  scheduler calls, retaining exact before/after Worlds and failure erasure.
  `Advance` preserves the complete original advance syscall, including its
  seccomp/dispatch/task-work prefix and recorded timer-unit observations; its
  placeholder path is lifted without a unit-coverage claim.
- `Leanux/Proofs/WG/CounterWindow/`: the receive counter window as a pure
  model of `counter_validate` (`Model`), its refinement to the mirror's
  `counterValidate` (`Refinement`, the S2 theorems), and replay freedom for
  finite sequences of validator calls (`MirrorCalls`).
- `Leanux/Proofs/WG/Keypairs/`: the keypair store projected with allocation
  lifetimes (`Lifetimes`, `LifetimeMirror`), the ordinary steps that may
  allocate or delete a slot but never alter a surviving window (`Ordinary`,
  `OrdinaryHot`, `OrdinaryRules`, `SnapshotRules`); `Frames/` holds the
  per-function frame contracts over that projection for the kernel helpers,
  WireGuard, pipes, the filesystem syscalls and the environment; `Evolution/`
  carries the acceptance-history invariant through the observers, the
  scheduler, the operations, the runner and the syscalls.
- `Leanux/Proofs/WG/ReplayWindow/`: the first result (below).
- `Leanux/Proofs/WG/AntiReplay/`: campaign R1, uniqueness and the inclusive
  lower edge; reusable arithmetic is in `CounterWindow/Bounds`, and ordered
  acceptance-history bounds in `Keypairs/Evolution/Bounds`.
- `Leanux/Proofs/WG/Lifetimes/`: generic allocation frontiers, old-identity
  provenance and removal (`Store`), with projection contracts and composition
  over actual original helper executions (`Actions`). `WG/Packets/Primitives`
  covers the eight skb-store helpers within one device epoch;
  `WG/Peers/Primitives` covers getter/setter identity and reference helpers;
  `Peers/Frames` carries live identities through initialization, and
  `Peers/Allocation` gives exact original peer creation and finite-sequence
  allocation/reference contracts. `Lifetimes/Events` expresses
  release-before-access exclusion over allocation stamps. `Peers/Access`
  observes every peer-store access in the original `peerPut` and
  `wgGetDeviceDone`, including prefixes ending in errors; its finite caller
  family contains no allocation or device lifecycle. `Peers/CreationAccess`
  extends it with exact allocation/initialization observations and original
  `peerCreate`, retaining released-history bounds through failing prefixes.
  `Lifetimes/Tagged`, `MixedAccess`, `MixedFrames`, `Acquire` and `Enqueue`
  combine peer, keypair and epoch-tagged packet access histories through the
  original receive-enqueue helper, under an explicit callback contract.
  `KeypairAccess`, `Decrypt` and `DecryptWorker` extend this through packet
  decryption and one original decrypt-worker iteration, including failures.
  `ReleaseInvariant`, `KeypairRelease`, `PacketRelease` and `ReleaseCalls`
  add exact acquisition/release observations and finite compositions of the
  original keypair reference, packet-free and keypair-clear calls. `Ambient`
  separates caller preservation from the chosen history invariant;
  `ReleaseAmbient` instantiates enqueue/decrypt with release uniqueness.
  `AllocationInvariant`, `KeypairAllocation` and `PacketAllocation` establish
  complete original allocator observations and safety with slot, lifetime and
  epoch bounds. `AllocationFrames` transports identities, metadata and released
  sets separately; `AllocationInitial` covers runner fixtures and prefill.
  `AllocationRetention`, `AllocationReleaseFrames` and `AllocationReleases`
  retain allocation bounds across reference/free calls using entry-resident
  release origins. `AllocationAmbient` instantiates shared caller contracts
  for the release family, receive enqueue and decrypt iteration.
  `KeypairRotation` and `Session` cover original keypair rotation, confirmation
  and complete session creation; `SessionFailure` gives the exact retained
  prefix when the birthdate clock fails after allocation. `PeerAllocationFrames`
  and `PeerAllocation` reuse the existing complete peer observer at
  `AllocationInv`, with original creation geometry and slot bounds;
  `PeerAllocationFailure` retains the initial allocation/write at cache-clock
  failure. `LookupAccess` covers optional-peer, index and public-key lookup;
  `ReceiveEntry` covers complete device/peer enqueue and `consumeData`, with
  `ReceiveEntryFailure` retaining the exact queue-record failure prefix.
  `MaintenanceTimers`, `ReceiveMaintenance` and `MaintenanceCalls` cover
  endpoint/cache, receive-timer and queued-handshake calls, including safe
  failure prefixes and the original timer guard's unconditional peer read.
  `TxAccess`, `TxContracts`, `TxEnqueue`, `TxStaging` and `TxStagingCalls` cover
  TX setter events and the seven complete staging callers, with explicit
  scalar-update contracts and concrete allocation-invariant preservation.
  `EncryptWorker` adds complete packet encryption and worker step/iteration
  observers with explicit checksum, softirq and rescheduling contracts;
  `Framing/WGData` discharges the concrete checksum and padding frames. Consumed
  encrypt-ring replacement has its own allocation frame, separate from produce.
  Failed prefixes retain every resolved access; saved-head association and
  ownership are not asserted. Concrete Batch composition now discharges those
  worker callbacks; enclosing environment and lifecycle paths remain open.
  `TxCompletion` and `TxWorker` add the five TX completion helpers, worker step
  and iteration, with complete socket observers and explicit rescheduling.
  Exact failed prefixes include the peer read before a jitter Stop. The shared
  jitter frame is proved over the full Kernel and projected into the legacy
  snapshot interface. Coordinated validation, fresh kernel replay and independent
  frozen-source review pass.
  `HandshakeConstruct`, `HandshakeConsume` and `HandshakeCalls` observe the
  five original Noise constructors/consumers and MAC addition with their actual
  result types, fresh accesses, reference-taking lookups and failure puts. The
  index frame concretely preserves `AllocationInv`; a failed cookie-age test
  retains the earlier MAC1 read/write. Coordinated validation, fresh kernel replay
  and independent frozen-source review pass.
  `HandshakeSend` composes the original buffer send, two timer helpers, initiation,
  response and send worker, retaining ordinary refusals and failed access prefixes.
  Its explicit socket/index/session contracts have concrete allocation instances;
  outer dispatch and saved-reference ownership remain open.
  `CookieAccess` covers make/create/validate/consume with exact result and failed
  prefix preservation. `Framing/WGCookie` retains the full Kernel except cookie
  secret/birthdate and the ratelimiter table; legacy frames are projections.
  Ambient cookie stability is explicit and concretely discharged for allocation
  safety. `HandshakeReceive`, `ReceiveWorker` and `ReceiveIngress` compose full
  local receive processing, iteration/bounded workers and UDP/packet entry.
  `BatchNapi`, `BatchActivation`, `BatchScheduler`, `BatchTrials` and `BatchCalls`
  now compose the concrete Batch scheduler with exact erasure and allocation safety.
  Copied-World trial filters have separate execution and access-safety contracts;
  their histories are discarded. Outer environment/lifecycle and saved-reference
  ownership closure remain open.
  `CounterAccess`, `AllowedLookupAccess`, `ReceiveCompletion` and `ReceivePoll`
  cover the complete validator, routing lookup, receive completion and polling
  with an explicit callback contract; `ReceiveFailure` retains the exact
  malformed-bitmap failure prefix. `SavedPeers` records demanded saved-map
  reads with a residency premise; `SocketFrames`, `LoopbackAccess`, `SocketCache`,
  `SocketSend`, `SocketSend4` and `SocketCalls` cover eleven complete
  cache/endpoint/loopback/tunnel/IPv4/IPv6 callers and their failure prefixes.
  The IPv4 observer uses exact source tail stages and retains both endpoint
  accesses before a reset-clock failure. `DeviceXmit` and `StackAccess` observe the
  complete transmit entry, actual stack callback and receive poll using that
  callback. Socket setup and remaining outer environment/lifecycle coverage remain open.
- `Leanux/Proofs/WG/LifetimeSafety/`: campaign R2 in progress: keypair store
  absence/freshness at original operation endpoints (`Keypairs/Identity`),
  peer/packet helper-family contracts, and a checked stale dump-cursor finding.
  Complete local handshake receive/worker and UDP/packet ingress compose the
  existing observers with explicit rescheduling contracts; concrete Batch scheduling
  discharges its internal worker callbacks. Full caller/lifecycle
  and all-internal-access safety remain unproved.
- `Leanux/Proofs/WG/AllowedIps/`: width-parametric prefix arithmetic (`Prefix`)
  and exact original-helper execution equations (`ArithmeticMirror`); `Tree`
  proves longest-prefix lookup, canonical-prefix uniqueness and depth bounds
  from local structural validity. `Store` represents exact node values and
  backlinks; `LookupMirror` proves total correctness of the original traversal.
  `Insertion` preserves validity, compression and fresh identifiers while
  replacing exactly the requested canonical prefix in the pure tree.
  `StoreMutation` and `MutationMirror` connect original empty-root insertion
  to that tree, including normal allocation refusal and sequence increments.
  `Context` and `PlacementMirror` prove total original node placement and its
  exact-match, stopped-graft and known-empty-focus relationships to insertion.
  `ChildMutation` and `ChildStore` refine original insertion at a root's immediate
  empty child, preserving both family representations and composing with lookup.
  `DeepChild` and `DeepChildStore` extend the empty-child case to arbitrary
  represented depth using context replacement and ID separation; the original
  `insert` wrapper preserves its sequence update on success and refusal.
  `ListsMirror` gives total original list deletion and exact pointwise effects.
  `ExactMutation` and `ExactStore` refine original exact-prefix replacement at
  arbitrary depth, preserving old node fields and linking insertion to lookup.
  `GraftMirror` and `GraftStore` classify original selected-root graft returns
  and give exact rollback effects, including the consumed node identifier and
  all-peer list filtering. `GraftSuccess` connects both successful selected-root
  grafts to pure insertion, bounds the resulting store, preserves the opposite
  family and composes original actual-root lookup with the flat-list specification.
  `GraftLink` and `DeepGraft` extend nonempty child grafts to arbitrary depth,
  with exact source-tail factorization, normal allocation-refusal endpoints,
  successful representation and actual-root lookup.
  `InsertionCases` reuses the established branch contracts; `InsertionDispatch`
  derives every bounded-input normal-return case from total original placement,
  retaining exact refusal/rollback effects and common successful representation.
  Original insert then agrees with actual-root longest-prefix lookup. Supplied
  opposite-family representation is framed without inferring its root linkage.
  `Removal` implements pure ID erasure with exact entry filtering, node-ID
  subsequence, validity/compression and filtered longest-prefix lookup.
  Removal also bounds ID retirement by two under compression and uniqueness.
  `ContextRemoval` derives local compaction and unchanged outer contexts
  under those premises. No original removeByPeer execution is asserted by these pure laws.
  `WG/CryptokeyRouting/` exports these components of campaign R3.
  `RemovalSource` retains the original saved-list loop and both continues by an
  all-input equation while importing only the original AllowedIps module.
  `RemovalMirror` proves total exact binary and root-tagged leaf/unary iterations;
  `RemovalStore` gives pointwise map/backlink effects and local RepAt transport.
  Root-tagged endpoints do not infer actual input-root selection. General
  removal/history, saved-list coherence and packet-path refinements remain open.

- `Leanux/Proofs/WG/Queues/`: original guarded ring production, symbolic
  no-wrap filling and unretired consumption, the concrete two-carried-slot
  witness, and the complete original enqueue helper's normal-return ring
  projection. `RingGeometry` identifies original peek/count/items and physical
  fullness with a stale/live slot representation. `RingSteps` proves exact
  original guarded production and retained/retired consumption, including wrap,
  every batch value and repeated payloads, deriving successor bounds. Size zero
  is separate. `RingJournal` composes exact finite offer/poll histories with
  admitted/consumed/live and consumed/retired/stale conservation. `RingMap` and
  `RingOccurrences` erase fresh per-offer ordinals through original operations,
  including refusal, and prove joint consumed/live ordinal uniqueness from init.
  `EnqueueAdmission` independently derives successful TX/RX entry-ring freedom,
  retaining the existing result API. `RxRingJournal`, `RxRingFrames` and
  `RxRingCuts` derive a full device-index/ring refinement through original helpers
  and installed mutation cuts. `RxRingEntry` observes complete RX enqueue and
  consumeData; `RxRingWorker` covers decrypt step/iteration with explicit callback
  erasure and preservation contracts. Every reached prefix has a finite ring
  replay; only normal returns link its endpoint to the actual World. Initialized
  calls inherit physical conservation and distinct occurrence ordinals, including
  size zero. TX, lifecycle, peer-queue/packet-store and scheduler composition
  remain open. `PrevQueue`
  proves original logical FIFO, cached-peek and malformed Stop laws. `RxQueueView` and `RxHelperFrames` retain full receive queues tagged
  by device epoch and peer identity through original reference, release, replay
  validation and key-confirmation helpers. `RxQueuePrimitives`,
  `RxMaintenanceFrames`, `RxTxFrames` and `RxCompletionFrame` extend these
  concrete contracts through endpoint/timer maintenance, staged transmission
  and complete original receive completion, allowing peer deletion.
  `RxPollPrimitives`, `RxPollPrefix` and `RxPollOrder` prove that the outer
  poll body's observed removals form a prefix of its entry queue, including
  failed prefixes, with an explicit callback `RetainsRx` contract, exact
  source-site append and original erasure laws. `GroCallback`, `GroState` and
  `RxPollGro` carry local occurrence labels and exact completion bytes through
  original GRO normal/held lists, counts and actual callbacks. `RxPollGroOrder`
  preserves the old chronological predicate: its former universal poll theorem
  is false on real GRO, as the accepted `DeliveryOrder/ReplayGro` demonstrates.
  The original helper equation proves held-then-normal input selects
  normal-then-held output; the actual per-list callback retains its visited
  prefix on Stop. `SelectedGro` proves selected callback-prefix order for every
  input World and Stop of one poll, and exact selected-offer/callback-entry list
  equality on an actual original normal return. Its internal count/list and
  held-size invariants are derived from the empty local state; no caller queue
  premise is used. `RxPollTags` proves that buffered ordinal/skb tags form a
  subsequence of observed drops, whose ordinals are consecutive from zero;
  buffered ordinals are distinct. `RxPollProjection` proves exact result/World/Stop
  and removal-log agreement between the tagged and removal-only poll observers,
  including actual callbacks. `RxStackFrames` discharges receive-queue retention
  for the concrete stack callback, including IPv4 TCP replies through original
  transmit entry and loopback errors. `RxPollProvenance` composes the concrete
  entry-queue prefix and buffered skb subsequence, and proves distinct callback
  ordinals with exact buffered-entry/removal-tag origins on every Stop.
  `WG/DeliveryOrder/` exports these R4 components. Whole-schedule ownership and
  conservation remain open.

- `Leanux/Proofs/WG/KeyTimes/`: exact original signed clock-test and comparison
  records (`Clock`), receive admission guards and the later wire-counter
  acceptance bound (`Receive`). `ReceiveAttempts` observes the actual AEAD
  boundary, proves admission for every event, and gives exact singleton coverage
  and failed-authentication endpoints. The zero-timer callback's complete
  transport-keypair-store frame is in `ZeroTimer`. `Staging` certifies actual
  completed TX allocations and submitted arguments with original key/clock
  witnesses and assigned-nonce bounds, retaining events on subsequent failure.
  `WG/KeyLifetime/` exports R5's positive local contracts and accepted-run
  counterexamples: nonce R/R+1 authenticates before validation rejects it; queued
  transport keepalives encrypt after recorded expiry or after zero/clear, before
  a new handshake. The new time witnesses use coherent coarse/jiffies/arm
  arithmetic; an earlier legacy witness deliberately does not. All are generated
  mirror inputs, not Linux captures. R5 is resolved as a Rule Zero finding;
  universal TX admission transport and whole-run attempt coverage are not claimed.

- `Leanux/Proofs/WG/Cookies/`: exact original load and post-MAC source factors,
  explicit MAC2 failure against the cookie returned by original `makeCookie`,
  invalid-MAC1 drop, and cookie-only result equality. Reply frames retain all
  device fields except cookie secret/birthdate and TX statistics, plus global
  peer/keypair counters; both secret rotations and IPv4/IPv6 sends are covered.
  `WG/FloodResistance/` exports six R6 terminals and reconstructs one accepted
  retry episode disproving the literal `MAX_TIMER_HANDSHAKES` attempt limit.
  It makes no universal retry-episode or kernel-schedule claim.

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

## Results

| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | 7a92672 | current |
| R1: anti-replay uniqueness and inclusive floor | No wire counter is accepted twice in one allocation lifetime; every accepted counter is at or above the inclusive lower edge, for pure runs, original validator calls and accepted runner histories. Equality at the charter's floor is intentionally permitted, with a concrete recorded replay. | `Leanux/Proofs/WG/AntiReplay/` (`Statements.lean`, 9 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r1--anti-replay-uniqueness-and-the-inclusive-floor) | 7a92672 | current |
| R2 components: store identities; access prefixes; stale dump-cursor finding | Original endpoints preserve fresh lifetime identity, and failure-retaining observations cover the listed allocation, reference, receive, transmit, socket, polling, handshake, cookie, complete handshake receive/worker, thin UDP/packet ingress and concrete Batch scheduler calls under explicit ambient/callback contracts. Cookie-state framing retains all resident objects and allocator geometry. Accepted runner witnesses expose a stale dump cursor releasing a replacement peer, including an orphaned trie binding. Copied consistency trials have separate exact filter and safe-prefix contracts. Whole-run environment/lifecycle closure and saved-reference ownership remain open. | `Leanux/Proofs/WG/LifetimeSafety/` (`Statements.lean`, 157 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r2--lifetime-identity-and-retained-references-in-progress) | 7a92672 | current; remaining obligations explicit |
| R3 components: prefix arithmetic, pure mutations and represented-tree lookup | Original IPv4/IPv6 helpers and all bounded-input normal insertion cases refine pure insertion and represented-tree longest-prefix lookup. Dispatch derives placement cases internally; refusal/rollback endpoints remain exact, while common success gives structural representation, roots, allocation and sequence effects. A supplied opposite-family representation is framed without inferring linkage. List deletion has exact filtered endpoints. Pure removal filters entries and preserves structural/local compaction laws. The original removal loop has an all-input source equation; binary and root-tagged leaf/unary steps have total exact endpoints and local representation transport. General removal/history, saved-list coherence and packet paths remain open. | `Leanux/Proofs/WG/CryptokeyRouting/` (`Statements.lean`, 53 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r3--cryptokey-routing-in-progress) | 7a92672 | current; remaining obligations explicit |
| R4 components and GRO order finding | Exact physical-ring laws and finite journals conserve admitted occurrences across consumed/live and retired/stale contents; tag erasure permits duplicate payloads. RX enqueue/consumeData and decrypt step/iteration now refine those journals on reached prefixes under explicit worker callback contracts; initialized calls inherit conservation and ordinal distinctness. Original TX/RX success independently implies an entry ring that is not full. Queue/poll and concrete stack contracts establish per-poll removal prefixes, selected GRO callback order and occurrence provenance. An accepted generated replay refutes chronological post-GRO stack order. Pipeline/scheduler conservation remains open. | `Leanux/Proofs/WG/DeliveryOrder/` (`Statements.lean`, 53 terminal theorems; `ReplayGro.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r4--queue-poll-and-delivery-order-components-in-progress) | 7a92672 | current; remaining obligations explicit |
| R5: key lifetime enforcement; Rule Zero findings | Thirteen local theorems identify exact original clock tests, RX AEAD admission and failed-tag coverage, accepted-wire-nonce bounds, TX staging certificates, zero-timer store framing and timer-pass erasure. Accepted original/observed replays authenticate nonce R+1 before rejection and encrypt queued transport keepalives after recorded expiry or zero/clear before a new handshake, using the same packet-held material. New time inputs have coherent coarse/jiffies/arm arithmetic, without a Linux schedule claim. The original unconditional statement is false; universal replacement transport theorems are not claimed. | `Leanux/Proofs/WG/KeyLifetime/` (`Statements.lean`, 13 terminal theorems; `Replay.lean`, `ReplayDelayed.lean`, `ReplayPostClear.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r5--key-lifetime-enforcement-rule-zero-findings) | 7a92672 | current |
| R6: cookie exclusion and retry-limit finding | Original under-load calculation and rejected-initiation suffix are exact. Invalid MAC2 against the actual original cookie result executes only the cookie reply; invalid MAC1 drops earlier. Ordinary completion preserves full Noise stores, indices and peer/keypair allocation counters. An accepted generated episode has 19 retries and 20 total initiations with MAX=18, then gives up on callback 20; this refutes the literal limit without claiming a universal replacement bound. The whole advance observer has exact original erasure. | `Leanux/Proofs/WG/FloodResistance/` (`Statements.lean`, 6 terminal theorems; `Replay.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r6--cookie-exclusion-and-retry-limit-finding) | 7a92672 | current |

The gate for every row: `capped -- scripts/in-bundle scripts/proof-gate`
(the build, the axioms of every terminal statement, the forbidden tokens,
the imports and the default targets).

## Adding a result

1. Make a directory under the subject, `Leanux/Proofs/<Subject>/<Result>/`,
   with a `Statements.lean` that holds every terminal statement, each with a
   docstring saying in plain words what it claims. Material another result
   could use goes in a layer, not in the result.
2. Import the `Statements` module from `Leanux/Proofs.lean`; the gate fails
   until it does.
3. Run the gate. Add the row above with the charter, the review, the mirror
   commit the result holds over, and the status.
4. The mirror stays as it is. If the proof needs the mirror to be different,
   that is a finding, reported with the path and what the kernel does there.

## Lag and repair

A row names the mirror commit its result holds over. A mirror change may
land while the result lags: the integration record says so, the row's status
becomes "lagging since <commit>", and the repair is a follow-on task on the
proof tree, not a condition on the mirror change. Every claim point reports
the lag.

The tree was restructured from `Leanux/Spikes/` on 2026-10-13; the dated
documents above keep the historical names in their prose.
