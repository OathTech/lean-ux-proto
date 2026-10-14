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
  `PeerBorrow` derives positive-count acquisition and normal immediate repayment,
  retaining the full outside-peer Kernel and every complete peer record pointwise.
  It shares the existing WGBase proof environment without changing legacy signatures.
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
  `ProjectsUnder` adds exact invariant-conditional projection, unconditional
  appended-suffix/focus laws and untouched-history frames for joint observers.
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
  outer environment dispatch remains open; saved-reference affiliation is a
  separate stronger property.
  `CookieAccess` covers make/create/validate/consume with exact result and failed
  prefix preservation. `Framing/WGCookie` retains the full Kernel except cookie
  secret/birthdate and both ratelimiter tables; legacy frames are projections.
  Ambient cookie stability is explicit and concretely discharged for allocation
  safety. `HandshakeReceive`, `ReceiveWorker` and `ReceiveIngress` compose full
  local receive processing, iteration/bounded workers and UDP/packet entry.
  `BatchNapi`, `BatchActivation`, `BatchScheduler`, `BatchTrials` and `BatchCalls`
  now compose the concrete Batch scheduler with exact erasure and allocation safety.
  Copied-World trial filters have separate execution and access-safety contracts;
  their histories are discarded. Initialized whole-run environment/lifecycle
  access closure remains open; reference affiliation is a separate stronger property.
  `AllowedIpsAccess` observes six original list/removal calls, including every
  demanded saved-map entry interleaved with its hit write, original owner reads,
  and exact failed prefixes. `Framing/WGAllowedIps` masks only nodes/trie roots
  and sequence, retaining full resident stores and all allocation frontiers;
  legacy frames project the canonical contracts. Concrete `AllocationInv`
  discharges node stability and scalar peer-list/hash updates. Insertion and
  enclosing lifecycle composition remain open. This extension's
  coordinated gate, fresh kernel replay and fast-tier validation pass.
  `KeyMaintenance` covers reset, handshake clearing, current-key expiration and
  queued clearing; `TimerCallbacks` covers all five expired callbacks and their
  dispatcher. Exact erasure retains clock/getter order and all failed prefixes;
  explicit scalar-index, keypair-release, staging and work-queue contracts have
  concrete `AllocationInv` discharges. Own-timer detachment, reference
  ownership and outer lifecycle composition remain separate. Six new grouped
  exports pass the 226-job scoped Statements and 334-job full proof targets;
  coordinated gate, fresh kernel replay and fast-tier checks also pass.
  `PeerRemoval` composes both flushed workers, the exact 4096-step send-workqueue
  drain, timer stop and complete after-dead/optional/all-peer removal. Queue
  erasure/pending reset precede sections, and both passes retain the saved scalar
  IDs with current-store accesses. Scalar queue/count contracts have concrete
  `AllocationInv` instances; no drain-progress or ownership premise is added.
  Three grouped exports pass the 227-job scoped and 340-job full proof targets;
  independent source/documentation review and coordinated validation pass.
  `DeviceControls` composes socket free/reinit/init, device open/up/stop/down
  and namespace pre-exit, with exact result/World/Stop erasure and concrete
  allocation safety. Saved scalar peer-ID loops preserve each original fresh
  access, and ordinary negative returns differ from Stops. The canonical
  `Framing/WGSocketLifecycle` mask omits only socket labels and incoming port;
  unchanged legacy frames are projections. The socket lifts are separately
  source-inspected for access coverage. Three grouped exports pass the 229-job scoped and 349-job full targets;
  independent review and coordinated validation pass.
  `DeviceRetirement`, `DeviceCreation` and `DeviceLifecycle` cover complete
  guarded create/destruct/delete. Exact retirement events name the actual
  pre-drop peer/keypair/TX/RX stores at the final original `wg := none` cut.
  Successful creation establishes a fresh empty epoch without imposing the
  allocation invariant at provisional setup; existing-device/refusal returns
  and all Stops retain their original behavior. Canonical `WGDeviceLifecycle`
  initialization/ratelimiter frames supply unchanged legacy projections.
  Four grouped exports pass scoped/full targets of 233/362 jobs, independent
  frozen review and coordinated validation.
  Initialized enclosing environment/Runner coverage remains open.
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
  callback. Remaining outer environment/lifecycle coverage remains open.
- `Leanux/Proofs/WG/LifetimeSafety/`: campaign R2 in progress: keypair store
  absence/freshness at original operation endpoints (`Keypairs/Identity`),
  peer/packet helper-family contracts, and a checked local stale dump-cursor finding with historical runner reachability; its full recipe is now rejected.
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
  `InsertionMetadata` derives exact peer-map and Device-frame fields for that
  common outcome; `InsertionEntries` supplies binding-ID origin and entry
  correspondence. `InsertionCoherence` derives fresh-ID absence and resident list
  coherence from represented input. `RoutingInvariant` combines both family
  representations, validity/compression/Nodup, coherent lists and node/peer/owner
  frontier bounds; `InsertionRouting` preserves it through original bounded-input
  normal insertion, both normal refusals and complete peer removal. Owner bounds
  allow orphan raw labels; rollback preserves coherent stores pointwise while
  retaining its consumed ID and the wrapper sequence increment.
  `RoutingView` retains device/list absence and exact routing fields;
  `RoutingLifecycle` derives original creation/refusal and raw-release effects
  and invariant preservation. `RoutingInitial` establishes the invariant from
  the original configured fixture. `FlatHistory` uses canonical prefix bits and
  raw owners without node IDs; `RoutingHistory` chains actual normal calls and
  returns, deriving all intermediate coherence/agreement from the fixture.
  Reached-root original findNode returns a flat-history winner and its actual
  raw node owner. Input bounds/residency are explicit only for insertion;
  enclosing configuration/Netlink/Runner closure and packet paths remain open.
  `AddressBounds` proves the actual UInt8 fold bound and pins the original private
  parseAllowedIp; `ConfigurationInputs` derives selected-family insertion bounds
  from actual setAllowedip guards and composes normal returns with routing/flat
  preservation. `ClearWalk` factors the original root-list traversal, proves
  normal-return coverage/list clearing and preserves the full list-only frame.
  Complete WG.free, clear-history and enclosing parser/configuration closure
  remain open; traversal totality and failed Worlds are not asserted.
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
  `RemovalChildMirror`, `RemovalCollapse` and `RemovalSteps` add total nonroot
  unary, owned-parent leaf and ownerless-parent collapse steps, with both root
  and child final slots and optional absent siblings. The exact collapse-prefix
  equation retains later Stops at the original post-target-free parent reread.
  `RemovalChildStore` gives complete map effects and root/frontier/sequence/list
  metadata. Raw endpoints do not infer actual linkage or owner residency.
  `RemovalContext` derives a focus from explicit target membership and separates
  the two families by encoded width. `RemovalTransport` and `RemovalCases`
  transport all seven source cases through represented contexts, deriving
  residency and ID separation from the input forest. `RemovalDispatch` proves
  total original target-step execution, both-family pure erasure, exact retirement,
  peer-list filtering and complete outside-forest/device/Kernel frames. Original
  actual-root lookup afterward selects the winner among surviving entries.
  `RemovalLists` defines explicit resident-only list coherence and exact saved-ID
  filtering. `RemovalLoop` executes the original fixed saved list, deriving later
  owned membership after each removal. `RemovalPeer` proves complete original
  removeByPeer from that input coherence, preserving it and removing exactly the
  target peer's entries, with the conditional sequence increment and empty target
  list. Original actual-root lookup then selects the surviving peer-filtered winner.
  The separate finite-call history layer now derives initialization and peer
  lifecycle preservation; enclosing configuration/Runner closure and packet paths
  remain open. Its five exports pass scoped/full builds, independent frozen review and
  coordinated checks.

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
  retaining the existing result API. `RingSource` shares source-journal replay,
  prefix safety and initialized conservation across payload types; `RxRingJournal`
  retains the RX API. `RxRingFrames`/`RxRingCuts` and `TxRingFrames`/`TxRingCuts`
  derive full device-index/ring frames and installed-mutation source endpoints.
  `RxRingEntry` observes complete RX enqueue/consumeData; `TxRingEntry` observes
  TX enqueue/createData. `RxRingWorker` covers decrypt step/iteration, and
  `TxRingWorker` covers encryptPacket and encrypt step/iteration, with explicit
  callback erasure and preservation contracts. Every reached prefix has a finite
  ring replay; only normal returns link its endpoint to the actual World.
  Initialized calls inherit physical conservation and distinct occurrence
  ordinals, including size zero. TX ordinals name whole-list occurrences, not
  constituent packets. `RxRingCallbackFrames`, `RxRingNapi`, `RxRingEncrypt`,
  `RxRingSocket`, `RxRingTx` and `RxRingHandshake` discharge the complete RX-cell
  frames of actual callbacks and non-decrypt workers. `SourceScheduler` shares
  callback-parameterized original run/dispatch/schedule control; `RxRingScheduler`
  instantiates it with unconditional erasure and concrete RX-journal refinement.
  `RxRingTrials` retains exact copied-world decision/filter behavior and certifies
  speculative prefixes separately from committed history. Initialized prior
  journals may describe nonempty current rings. `RxBorrow` proves the adjacent
  original lookupSrc/peerPut cut, retaining the lookup result, exact access/Stop
  erasure and safe failed prefixes. Queue/NAPI/key-slot projections and conditional
  bounded slot-affiliation preservation follow; no initial liveness or trie-validity
  premise is required. Its destination lemma covers immediate repayment only.
  The four new exports pass scoped and coordinated validation.
  `TxDisposition`, `TxDispositionProjection`, `TxDispositionStep` observe actual
  TX admission/publication/drop/completion cuts, with all-input source erasure and
  direct createData access/ring projection. Full-step access projection uses entry
  AllocationInv and concrete helper contracts. `TxDispositionCuts` gives exact
  EPIPE/ENOSPC/DEAD continuations, reached free markers and normal disposal no-send.
  `TxDispositionBorrow` derives strict-acquisition positivity and immediate repayment.
  The six observer/cut exports pass coordinated validation. `TxPublication` now
  retains all full peer TX queues across the actual strict borrow, CPU update and
  work-record interval, deriving nonfinal repayment without peer affiliation.
  `TxDisposal` proves exact normal list erasure and original ENOSPC packet absence.
  `TxDispositionEndpoints` gives normal EPIPE queue retention, DEAD head and unchanged
  ring, plus actual DEAD-head txStep disposal with unchanged socket output. Five
  new exports pass scoped/full targets of 243/365 jobs, independent frozen review
  and coordinated validation.
  RX carrier preservation through transmit callbacks, initialized W7 transport
  between the local refusal/disposal endpoints, outer ingress/runner/lifecycle and joint receive-pipeline conservation
  remain open. The RX scheduler extension passes coordinated validation at the mirror pin in the register. `PrevQueue`
  proves original logical FIFO, cached-peek and malformed Stop laws. `RxQueueView` and `RxHelperFrames` retain full receive queues tagged
  by interface index and peer internal ID through original reference, release, replay
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
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | c047e64 | current |
| R1: anti-replay uniqueness and inclusive floor | No wire counter is accepted twice in one allocation lifetime; every accepted counter is at or above the inclusive lower edge, for pure runs, original validator calls and accepted runner histories. Equality at the charter's floor is intentionally permitted, with a concrete recorded replay. | `Leanux/Proofs/WG/AntiReplay/` (`Statements.lean`, 9 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r1--anti-replay-uniqueness-and-the-inclusive-floor) | c047e64 | current |
| R2 components: store identities; access prefixes; stale dump-cursor finding | Original endpoints preserve fresh lifetime identity, and failure-retaining observations cover the listed allocation, reference, receive, transmit, socket, polling, handshake, cookie, complete handshake receive/worker, thin UDP/packet ingress, concrete Batch scheduler, six allowed-IP list/removal calls, key maintenance, all expired timer callbacks, seven flush/peer-removal calls, eight socket/device controls and guarded create/destruct/delete under explicit ambient/callback contracts. Cookie-state framing retains all resident objects and allocator geometry. Historically accepted runner witnesses exposed a stale dump cursor releasing a replacement peer, including an orphaned trie binding; c047e64 now rejects both recipes before deletion, checked against the original and observer. Copied consistency trials have separate exact filter and safe-prefix contracts. Initialized whole-run allocation-identity access closure remains open, including remaining timer firing, Netlink and enclosing environment/Runner callers; actual final device-store retirement is now covered locally. Raw-reference affiliation/credit is a separate stronger property, needed where R3/R4 rely on it. | `Leanux/Proofs/WG/LifetimeSafety/` (`Statements.lean`, 176 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r2--lifetime-identity-and-retained-references-in-progress) | c047e64 | current components; remaining obligations explicit |
| R3 components: prefix arithmetic, pure mutations and represented forests | Original IPv4/IPv6 helpers and all bounded-input normal insertion cases refine pure insertion and represented-tree longest-prefix lookup, retaining exact refusal/rollback endpoints. Original removal has an all-input loop equation and exact raw endpoints, including late Stops. From ForestRep, Compressed, Nodup and explicit target membership, unified removal-step dispatch derives all seven cases and gives total source execution, both-family pure erasure, exact retired-node absence, all-peer list filtering and full outside-forest/device/Kernel frames. Validity and actual-root longest-prefix lookup follow. Explicit resident-only list coherence additionally yields total complete original removeByPeer, preserved coherence, exact peer-owner filtering and conditional sequence/list effects. The combined routing invariant now preserves resident-list coherence and raw owner/frontier bounds through original normal insertion, both refusals and complete removal. Original creation/refusal and raw release preserve the invariant; finite actual normal calls from the configured fixture refine canonical flat updates without node IDs and reached-root longest-prefix lookup. Actual local parsed attributes now justify setAllowedip bounds and normal insertion composition; original root-list clearing has normal coverage and full list-only framing. Complete WG.free/clear-history, enclosing configuration/Netlink/Runner closure and packet paths remain open. | `Leanux/Proofs/WG/CryptokeyRouting/` (`Statements.lean`, 80 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r3--cryptokey-routing-in-progress) | c047e64 | current components; free/configuration and packet-path closure open |
| R4 components and GRO order finding | Exact physical-ring laws and finite journals conserve admitted occurrences across consumed/live and retired/stale contents; tag erasure permits duplicate payloads. RX enqueue/consumeData/decrypt and TX enqueue/createData/encryption refine those journals on reached prefixes under explicit callback contracts; initialized calls inherit conservation and ordinal distinctness. TX occurrences are whole batches, not constituent packet identities. Original TX/RX success independently implies an entry ring that is not full. Queue/poll and concrete stack contracts establish per-poll removal prefixes, selected GRO callback order and occurrence provenance. An accepted generated replay refutes chronological post-GRO stack order. Concrete RX scheduler calls now discharge their callbacks; copied trials have separate exact decisions/filter and initialized prefix conservation. The adjacent source lookup/reference repayment restores the semantic Kernel on normal return, with exact access-prefix erasure and conditional slot-affiliation preservation. Joint TX disposition observations now project exactly to createData ring/access histories; full-step access projection uses entry AllocationInv. Source-derived normal endpoints now retain the EPIPE queue item and DEAD head with unchanged ring, erase ENOSPC packet slots, and dispose the actual DEAD txStep head without socket output. Publication retains every peer TX queue through its temporary reference interval without a peer-affiliation premise. Transport between these endpoints under arbitrary schedules remains open. RX carrier preservation, outer runner/lifecycle and joint receive-pipeline conservation remain open. | `Leanux/Proofs/WG/DeliveryOrder/` (`Statements.lean`, 79 terminal theorems; `ReplayGro.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r4--queue-poll-and-delivery-order-components-in-progress) | c047e64 | current components; pipeline closure open |
| R5: key lifetime enforcement; Rule Zero findings | Thirteen local theorems identify exact original clock tests, RX AEAD admission and failed-tag coverage, accepted-wire-nonce bounds, TX staging certificates, zero-timer store framing and timer-pass erasure. Accepted original/observed replays authenticate nonce R+1 before rejection and encrypt queued transport keepalives after recorded expiry or zero/clear before a new handshake, using the same packet-held material. New time inputs have coherent coarse/jiffies/arm arithmetic, without a Linux schedule claim. The original unconditional statement is false; universal replacement transport theorems are not claimed. | `Leanux/Proofs/WG/KeyLifetime/` (`Statements.lean`, 13 terminal theorems; `Replay.lean`, `ReplayDelayed.lean`, `ReplayPostClear.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r5--key-lifetime-enforcement-rule-zero-findings) | c047e64 | current |
| R6: cookie exclusion and retry-limit finding | Original under-load calculation and rejected-initiation suffix are exact. Invalid MAC2 against the actual original cookie result executes only the cookie reply; invalid MAC1 drops earlier. Ordinary completion preserves full Noise stores, indices and peer/keypair allocation counters. An accepted generated episode has 19 retries and 20 total initiations with MAX=18, then gives up on callback 20; this refutes the literal limit without claiming a universal replacement bound. The whole advance observer has exact original erasure. | `Leanux/Proofs/WG/FloodResistance/` (`Statements.lean`, 6 terminal theorems; `Replay.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r6--cookie-exclusion-and-retry-limit-finding) | c047e64 | current |

The gate for every row: `capped -- scripts/in-bundle scripts/proof-gate`
(the build, the axioms of every terminal statement, the forbidden tokens,
the imports and the default targets).

The current coordinated checkpoint over `c047e64` passes the 365-job proof gate
(378 declarations, permitted axioms only), fresh stock kernel replay, the 60-job
default build and 114 unit tests (21.897 seconds, one skip). The three-export R3
parser/guard/root-list-clear extension passes scoped/full targets of 154/358 jobs
and independent frozen review, with no unresolved finding. These checks cover
the earlier R2/R3/R4 components, including the W7 joint observer, too.
The preceding carry's 118-job executable build and eleven reproduction checks
remain current for the unchanged runtime: nine accepted runs and two expected
pending-dump rejections. They were not rerun for this proof-only extension.
The runner/anti-replay contracts include both floodExact modes, and timer source
contracts retain explicit caller-jiffies records and their failure order.
The four-export R2 device lifecycle extension passes scoped/full targets of
233/362 jobs, independent frozen review and coordinated validation.
The five-export W7 endpoint extension passes scoped/full targets of 243/365 jobs,
independent frozen review and coordinated validation.
Current components do not close the remaining R2/R3/R4 obligations.
The R6 report also records an IPv6 rate-table lifecycle
source discrepancy for follow-up, without claiming an accepted replay or differential finding.

## Result table: claim, theorem, boundary, premises, counterexample, pin

What each result's statements establish and what must not be inferred from
them, following the [pre-release review](2026-10-14-pre-release-review.md) §4.
These rows describe the current campaign source over mirror `c047e64`; validation
status is recorded above. The earlier review read proof snapshot `ffea367`,
which was a proof-branch commit, not its mirror revision. Names below are
representative exports; each result's `Statements.lean` gives the complete surface.

| Result | Original claim (charter) | Representative theorems | Event boundary | Substantive premises | Counterexample or remaining obligation |
| --- | --- | --- | --- | --- | --- |
| ReplayWindow S1 | Every accepted execution has its exact acceptance history and no two events share a lifetime and wire counter | `S1` | Committed validator acceptances in a successful `executeTrace`, including packets dropped later; copied scheduler trials are separate | A successful original runner execution, for every placeholder/floodExact setting. The exact logged execution is a conclusion, not an extra premise | No remaining S1 obligation; the theorem concerns the executable mirror, not all Linux executions |
| ReplayWindow S2 | `counterValidate` returns the receive.c rule's result and replay state | `S2`, `S2_acceptance`, `S2_update` | Original validator versus the Lean `CounterWindow.step` rule | A resident keypair with a 128-word bitmap, established by reachable allocation | No remaining S2 obligation. Identifying `step` with the C rule is a source correspondence claim; the refinement is within Lean |
| ReplayWindow S3 | Nonreceive calls and validator calls preserve the other keypairs' windows | `S3`, `S3_nonreceive`, `S3_validator`, `S3_surviving`, `S3_syscall`, `S3_syscall_ambient` | Surviving old cells; other cells at a validator; whole-syscall evolution including ambient work | The stated lifetime-aware invariant and successful original execution; the nonreceive specialization uses its explicit call classification | Allocation/deletion are permitted and reused slots denote new lifetimes; equality of every store cell was never claimed |
| R1 anti-replay | No repeated acceptance under one lifetime; nothing at or below the floor accepted | `pure_uniqueness`, `mirror_uniqueness`, `runner_uniqueness`, `pure_run_floor`, `mirror_floor`, `mirror_run_floor`, `runner_floor`, `pure_run_below_floor` | Pure window runs, original validator calls and accepted runner histories | The corresponding S1/S2 premises | `inclusive_boundary_witness` and an accepted replay show equality at highest minus 8128 may be accepted. The proved exclusion is strictly below the floor |
| R2 lifetime safety | No dead identity is resolved after release | `keypair_no_resurrection`, `peer_create_fresh_identity`, `packet_*_free_prevents_later_lookup`, access-safety families, `scheduler_family_allocation_access`, `allowedips_family_allocation_access_preserves`, `key_maintenance_family_allocation_access_preserves`, `timer_callback_family_allocation_access_preserves`, `peer_removal_family_allocation_access_preserves`, `device_control_family_allocation_access_preserves`, `device_lifecycle_family_allocation_access_preserves`, `device_retirement_actual_maps` | Operation endpoints and failure-retaining access prefixes of the covered original call families, including concrete Batch scheduling; isolated copied trials have separate contracts | Resident uniqueness/allocation bounds and each stated callback or ambient contract | Initialized whole-run allocation-identity access closure remains open, including remaining timer firing, Netlink and enclosing environment/Runner callers; actual final device-store retirement is now covered locally. Raw-reference affiliation/credit is a separate stronger property, needed where R3/R4 rely on it. `stale_cursor_retargets_replacement` is a raw local counterexample; its historically accepted runner recipes now reject at operation 3 under the pending-dump guard |
| R3 cryptokey routing | Lookup follows insertion/removal history; incoming and outgoing packets are bound to the owning peer | `pureTree_lookup_correct`, `original_findNode_lookup_correct`, `original_insert_longest_prefix`, `original_add_all_cases`, `original_insert_all_cases`, `pure_removal_entries_and_lookup`, `original_removal_*`, `original_removeStep_forest_*`, `original_removeStep_then_findNode`, `original_removeByPeer_forest_*`, `original_removeByPeer_then_findNode`, `original_insert_routing_preserved`, `original_insert_coherent_peer_maps`, `original_insert_refusal_coherent`, `original_removeByPeer_routing_preserved`, `original_peerCreate_routing_*`, `original_peerPut_routing_preserved`, `original_initialized_routing_history`, `original_initialized_history_findNode`, `parsed_setAllowedip_bounded_call`, `parsed_setAllowedip_routing_preserved`, `original_rootRemove_lists_normal` | Represented tries versus an independent flat-prefix winner; pure removal, every raw original removal arm, unified represented-forest target removal and complete coherent peer removal; initialized finite original-call histories and reached-root lookup; local actual-parser/guard insertion cuts and normally completed root-list clearing | Insertion uses the stated address bounds, fresh IDs and resident target. Removal derives local linkage/separation from ForestRep, Compressed, Nodup and explicit target membership; validity additionally supports lookup. Complete peer removal also assumes a resident target and explicit resident-only list coherence, which it preserves. Original insertion covers bounded-input normal returns, including allocation refusals. Explicit RoutingInvariant additionally supplies resident list coherence and node/peer/owner frontier bounds, all preserved by these insertion/removal calls; owner bounds do not imply residency. Finite histories instead derive this invariant from the original configured fixture and actual normal create/insert/remove/release calls; only insertion carries reached-input bounds/residency, and query bounds are explicit. Local parser success derives address shape; setAllowedip guards derive family/CIDR/width bounds. Root-list clearing uses resident-list ownership and a represented subtree, with original normal return explicit; it preserves other Kernel/device/peer fields and assumes no owner residency | Complete WG.free/clear-history and enclosing parser/configuration/Netlink/Runner closure and both packet paths remain open. A raw peer-slot winner is not yet identity authorization; no accepted misrouting counterexample is claimed |
| R4 delivery | Per-peer/key delivery follows receive order for every recorded schedule; loss occurs only at explicit arms | `two_carried_slots_*`, `original_enqueue_epipe`, `original_poll_selected_callback_complete`, `original_poll_removal_ordinals`, RX/TX ring-journal families, `original_rx_scheduler_*`, `original_rx_consistency_*`, `original_lookup_*`, `original_tx_disposition_*`, `original_tx_strict_reference_cut`, `original_create_data_*_endpoint`, `original_dead_tx_step_disposal` | Physical ring mutations, reached prefixes, poll removals and selected GRO callback entries; concrete RX scheduler and separate trial filters | Explicit callbacks for the local worker families; concrete RX scheduling discharges its callbacks. Initialized conservation uses a prior refined ring history; retired/stale structural representation requires positive ring size. The W7 endpoint contracts assume normal return and their stated entry live-peer/capacity/full-ring or actual logical-DEAD-head conditions | Accepted `r4-gro-reorder` refutes chronological post-GRO order; selected normal-before-held order is proved. Local W7 source cuts and normal EPIPE/ENOSPC/DEAD-step endpoints are checked; initialized transport between those endpoints, RX carrier preservation, outer lifecycle/runner and joint receive-pipeline conservation remain open. Universal outgoing conservation is additional scope. Callback entry is not delivery, local ordinals are not global identities, and a stopped prefix has no retained World |
| R5 key lifetime | No encryption/decryption past the reject time or counter; no use after zeroing | `original_decryption_admission`, `original_accepted_wire_nonce`, `original_staging_admissions`, `original_zero_timer_preserves_transport_keys`, `receive_guard`, `original_age_*`, `original_receive_attempt_*` | Decryption/staging admission, exact recorded clocks, the zero timer's local effect and observed attempts | The stated original-call, recorded-clock and counter premises; the environment admits worker latency unbounded by virtual time | Accepted replays authenticate a past-limit nonce before rejection and encrypt queued material after expiry or clear. These follow the C's order and were [reviewed as statement artefacts](2026-10-13-review-r5-counterexamples.md). Rule Zero resolution does not assert universal enforcement or a universal replacement bound |
| R6 flood resistance | An initiation without valid MAC2 cannot pass the under-load cookie gate; retransmission stops at MAX | `original_invalid_mac2_cookie_only`, `original_invalid_mac2_noise_preserved`, `original_invalid_mac1_drop`, `original_under_load_queue`, `original_under_load_decay` | Actual load-phase execution and cookie suffix; Noise preservation on normal completion | `FailedMac2` with its prefix, clock and actual cookie-execution premises | Accepted 19-retry/20-initiation episode refutes literal MAX=18. No universal corrected retry bound, real-load reachability, CPU/memory bound or availability guarantee is claimed |

The counts below are declaration counts, not counts of completed charter
properties. Exports include semantic properties, refinements, erasure and frame
contracts, failed-prefix statements and concrete boundary witnesses. One theorem
can combine several of those roles, so they are described in the rows rather
than forced into disjoint numerical categories. Runtime replay programs are
checked separately and are not included in the terminal declaration count.

| Result | Current source declarations | Theorems | Helper definitions |
| --- | ---: | ---: | ---: |
| ReplayWindow | 15 | 13 | 2 |
| AntiReplay | 9 | 9 | 0 |
| LifetimeSafety | 176 | 176 | 0 |
| CryptokeyRouting | 80 | 80 | 0 |
| DeliveryOrder | 79 | 79 | 0 |
| KeyLifetime | 13 | 13 | 0 |
| FloodResistance | 6 | 6 | 0 |
| Total | 378 | 376 | 2 |

C memory safety, constant time, cryptographic security and the physical
erasure of secrets are separate claims that no row makes.

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
