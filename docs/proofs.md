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

Build counts and validation results in the module descriptions record their
original checkpoints. The current mirror/toolchain carry status is in
[Results](#results).

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
  and the seccomp frames preserve that full view. `Wait` shares the complete
  fuel-bounded wait walk, epoll callback and wake wrappers. `Pipe` and `PipeRead`
  share original source factors, release geometry, write-count and read-occupancy
  progress over the full WG view. Legacy Wait/Pipe/PipeRead interfaces project
  these contracts; source factors are aliases and weak wait-IH signatures are
  unchanged. These frames require neither valid filesystem inputs nor sufficient
  wake fuel and constrain normal endpoints only. `FSBase`, `Eventpoll`, `FS`
  and `EventpollCalls` extend the canonical full-WG proofs through descriptor,
  inode, eventfd, pipe and epoll callers, all eleven FS dispatch arms and actual
  taskWorkRun. Their 347 legacy theorem signatures remain unchanged projections;
  generic SameView list/search rules retain weak callback premises and fixed
  epoll fuel results discharge the legacy weak-IH wrappers. Private source aliases
  remain exact. These are normal-endpoint frames, not later namespace-cleanup
  execution. `Control` shares compiler
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
  `PrefixOuter` retains observer history outside indexed Runner exceptions,
  with exact run/bind/erasure rules and an explicit two-branch WP bridge.
  `Focus` injects a local observer's new suffix into a combined event stream
  without changing the previous interleaving. `Projected` erases extra local
  accumulator data while retaining the original result, complete World and Stop.
  `ProjectsPrefix` compares two failure-retaining observers by projecting both
  their results and event histories, including every stopped prefix.
  `ProjectsUnder` adds exact invariant-conditional projection, unconditional
  appended-suffix/focus laws and untouched-history frames for joint observers.
  `FocusComposition` distributes focus using actual append contracts, with an
  invariant-conditional interface for lower observers and exact failed-prefix
  composition. It never assumes incoming-history independence.
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
  `FilesystemLocal` gives six source-audited lifts for the actual wait walk,
  safewake, epoll callback and pipe read/write/release. Their full WG frames
  transport AllocationInv; exact lifts retain the entire incoming history and
  original result/World/Stop. Source access coverage is independent of framing.
  `FilesystemCalls` adds the eleven typed original FS dispatch arms and actual
  taskWorkRun with its pop-before-release order and exhaustion Stop. Source-audited
  exact lifts retain arbitrary incoming history; full-WG frames transport
  AllocationInv without valid-FS, fuel/drain or callback-ownership assumptions.
  fputFinal may queue netnsCleanup; the later Env, syscall and Runner layers
  supply its eventual execution and enclosing composition.
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
  worker callbacks; initialized Runner composition is supplied by RunnerSafety.
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
  initialized Runner composition is supplied by RunnerSafety; saved-reference affiliation is a
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
  their histories are discarded. `Audit` and `BatchAudit` add a failure-retaining
  sum stream of committed lifetime events and actual consistency-filter entries.
  Saved entries retain their own World/history allocation facts through later
  mutations. The literal filter emits one marker before executing the original
  filter, including empty lists and Stops. Concrete schedule, nested-reschedule
  and receive-worker observers erase unconditionally, project to the existing
  committed observers from an allocation-valid entry, and retain safe prefixes.
  From empty history and local AllocationInv, every recorded entry supplies the
  premise of the exact ordered trial-filter and isolated trial-safety contracts.
  Coverage comes from the source placement and exact filter-entry equation,
  separately from projection. Result-dependent focus and generic finite-loop
  projection support later callers. RunnerSafety supplies initialized whole-run
  access closure; reference affiliation is a separate stronger property.
  `SavedPeerLookup` observes captured-map lookups per scalar peer-list occurrence:
  Some emits one saved read, None emits none, and duplicates repeat. `EnvWorkersAudit`
  composes original queue guards and deferred send/clear/crypt workers through the
  audit scheduler; `EnvTimersAudit` covers full fire/recorded/placeholder dispatch,
  idle and advance with all source bounds and failures. `Environment/TimerSource`
  shares literal post-scan and placeholder cuts, including the original pure fold.
  `Framing/EnvLeaves` gives complete Kernel bookkeeping frames and legacy projections.
  `EnvDeferredCalls` groups fifteen typed originals with unconditional erasure,
  concrete AuditInv failed-prefix preservation and local reached-trial safety.
  `EnvControlsAudit` covers up/down/delete, MTU/address/routes, namespace cleanup
  and the exact observation tail after idle. `Framing/EnvOperations` retains full
  resident stores/frontiers, masking only MTU/inet-family scalars where needed;
  canonical `dropHiddenRecord` keeps the actual World ordinal effect. Legacy
  frames project these contracts. `EnvTrafficAudit` observes multicast loopback,
  the complete inline saved-peer scan, inject and both flood modes; flood queue
  replacement preserves identity/metadata, and its receive worker carries actual
  nested scheduling probes. `EnvBatchAudit` preserves captured device scalars,
  partial CQEs and deferred-worker order. Source-only `ObservationSource` and
  `BatchSource` retain exact original continuations/item loops. `EnvRemainingCalls`
  groups these fifteen originals with unconditional erasure, concrete AuditInv
  failed-prefix safety and local reached-trial facts.
  `SyscallWrappersAudit` composes literal callback-parametric socket/netlink/
  rtnetlink wrappers with original ordinary-negative cleanup and Stop cuts.
  `Framing/Syscalls` supplies the full WG frame for the original four-close
  netnsClose, projecting its legacy snapshot API; queued cleanup stays in Env.
  `SyscallDispatchAudit` covers all 34 typed constructors (35 dispatch arms),
  using concrete FS/seccomp frames, focused WG calls and actual Env observers;
  netlink autobind socket records use the dump mask. `SyscallsAudit` preserves
  the original reset, seccomp entry/tail calls, task work and postworkers.
  Three grouped contracts retain unconditional erasure, AuditInv failed-prefix
  safety and actual reached-trial facts. RunnerSafety supplies initialized composition without parser, ownership,
  valid-descriptor or drain premises.
  `AllowedIpsAccess` observes six original list/removal calls, including every
  demanded saved-map entry interleaved with its hit write, original owner reads,
  and exact failed prefixes. `Framing/WGAllowedIps` masks only nodes/trie roots
  and sequence, retaining full resident stores and all allocation frontiers;
  legacy frames project the canonical contracts. Concrete `AllocationInv`
  discharges node stability and scalar peer-list/hash updates. RunnerSafety supplies initialized composition. This extension's
  coordinated gate, fresh kernel replay and fast-tier validation pass.
  `AllowedIpsInsert` covers complete original add/insert, including exact-owner
  rewrites, demanded saved-map reads, allocation refusals and partial rollback.
  Canonical `Framing/WGAllowedIpsInsert` additionally masks the node frontier,
  retaining all tracked residents and allocation geometry; legacy frames project it.
  `ConfigurationLeaves` and `ConfigurationPeer` cover setPort, setAllowedip and
  complete setPeerCmd with exact ordinary-negative cleanup and failed prefixes.
  `WG/Configuration/PeerSource` shares the literal source stages without lifetime
  or routing imports. Six new grouped exports have concrete AllocationInv
  discharges and no routing/address/attribute-validity premises. Scoped/full
  targets pass 238/372 jobs; independent frozen source/documentation review is
  clear. Coordinated proof gate, fresh kernel replay and fast-tier validation pass.
  `ConfigurationDeviceFrames` and `ConfigurationDevice` extend those same three
  exports to complete original wgSetDevice. Canonical `Framing/WGConfiguration`
  masks only static identity, device cookie/MAC keys, update generation and fwmark;
  legacy frames project it. The existing peer precomputation observer is focused
  into mixed history with concrete metadata transport. Original-only
  `Configuration/DeviceSource` shares the exact preflight/update/private-key/peer
  continuations. Generation-before-error, old-peer put-before-remove, saved-ID
  loops and ordinary-return zero-key records retain their source order, without
  valid-attribute, routing, ownership or progress premises. Component/scoped/full
  targets pass 178/246/386 jobs. Independent frozen source/documentation review
  is clear; coordinated proof gate, fresh kernel replay and fast-tier validation pass.
  RunnerSafety supplies initialized composition.
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
  RunnerSafety supplies initialized caller coverage.
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
  callback. RunnerSafety supplies initialized caller coverage.
- `Leanux/Proofs/WG/NetlinkDump/{Source,DeviceSource}` retain literal original
  serialization/header/peer-walk cuts. `Framing/WGDump` proves complete read-only
  Kernel frames and masks only the two netlink socket records, with unchanged
  legacy projection APIs. `Lifetimes/DumpAccess` covers all seven original dump
  calls with typed exact erasure, demanded cursor/peer observations, ambient
  contracts and concrete allocation-safe failed prefixes. New-cursor acquisition,
  old-cursor put, queue-before-done and pop-before-next-dump retain source order;
  no cursor-affiliation or drain premise is introduced. Component/scoped/full
  builds pass 176/255/401 jobs and independent frozen source/export review is
  clear; coordinated gate, fresh kernel replay and fast-tier validation pass.
- `Leanux/Proofs/WG/LifetimeSafety/`: campaign R2 lifetime safety: keypair store
  absence/freshness at original operation endpoints (`Keypairs/Identity`),
  peer/packet helper-family contracts, and a checked local stale dump-cursor finding with historical runner reachability; its full recipe is now rejected.
  Complete local handshake receive/worker and UDP/packet ingress compose the
  existing observers with explicit rescheduling contracts; concrete Batch scheduling
  discharges its internal worker callbacks. The audit scheduler derives reached
  copied-trial entry invariants locally; the syscall layer carries these facts.
  `RunnerAudit` retains the literal initialized Runner, indexed errors and JSON;
  `RunnerSafety` discharges initialization/prefill and every concrete syscall,
  preserving AuditSafe on success and failure. Its three grouped exports cover
  every typed Trace and both booleans, with no parser, length, progress or success
  premise. Actual reached markers yield saved-entry validity, exact ordered
  filter correspondence and safe isolated trial histories. Source coverage
  remains distinct from erasure; scalar affiliation/credit is not asserted.
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
  whole device-command composition is supplied by the later completion layer.
  Later optional-state contracts cover guarded device lifecycle; enclosing syscall/Runner
  execution and packet paths remain open.
  `AddressBounds` proves the actual UInt8 fold bound and pins the original private
  parseAllowedIp; `ConfigurationInputs` derives selected-family insertion bounds
  from actual setAllowedip guards and composes normal returns with routing/flat
  preservation. `ClearWalk` factors the original root-list traversal, proves
  normal-return coverage/list clearing and preserves the full list-only frame.
  `ClearSnapshot` retains original node values, current-node submap and resident-list
  provenance/exclusions through both saved-root phases. `ClearEndpoint` derives
  complete normal WG.free: empty represented families and resident lists, seq+1,
  unchanged frontiers/full other fields, and node deletion only. `RoutingCall.clear`
  empties the independent flat tables in initialized finite histories. Enclosing
  configuration closure, traversal totality and failed Worlds are not asserted.
  `RoutingRetains` permits peer deletion while preserving nodes/table/frontiers
  and survivor lists; it derives invariant/flat transport. `RoutingCompletions`
  observes actual whole setAllowedip returns with exact signed results/views and
  semantically valid flat prefixes. `RoutingSendFrames` derives concrete original
  send/cleanup frames. Shared `Configuration/AllowedIpSource` factors the original
  tail; `PeerTailRouting` and `PeerTailCompletion` cover its allowed-IP loop, early
  cleanup and full keepalive/staged-send suffix. Erasure is unconditional; semantic
  prefix safety and normal reached-state agreement use explicit entry routing,
  resident target and local attribute shape. No failed World or enclosing closure
  is asserted.
  `RoutingSocketFrames`, `RoutingHandshakeFrames` and `RoutingFlushFrames` derive
  concrete normal routing frames through both socket families, handshake/key-clear
  work, the actual bounded drain and final peer cleanup. `RoutingAcquire` separately
  derives raw-slot residency from actual lookup/create outcomes. The completion
  sum includes nested removeByPeer; `Configuration/PeerRemovalCompletion` and
  `PeerUpdateCompletion` cover peer death/removal and the complete acquired-peer
  update stage. `PeerCommandCompletion` composes the literal public preflight
  through an internal acquisition suffix, deriving target residency from actual
  lookup/create outcomes. `ParserShape` propagates the actual private parsers and
  operations accumulator through public parseTrace; its literal suffix factor has
  an rfl source equation. Parsed peer commands therefore need no extra address-shape
  premise. `RoutingDeviceFrames` projects existing configuration/socket masks and
  proves endpoint-cache/key-expiry frames. `Configuration/DeviceCompletion` composes
  all four original DeviceSource cuts, including a completed free before both saved
  remove-all loops. Normal clear/remove-all also leaves the journal's flat tables
  empty. Public parsing discharges shape for complete device commands; routed
  present-device entry is retained by those local contracts. `RoutingGlobal` adds
  absence with empty folded tables, without changing completion validity.
  `RoutingDeviceLifecycleFrames` derives guarded creation and deletion-permitting
  down/stop frames from original calls. `Configuration/LifecycleCompletion` proves
  absent whole peer/device commands retain their entry journals, and composes actual
  destruction/deletion with clear before final device drop. Arbitrary fixture rows
  remain permitted; direct invalid allowed-IP completion is not generalized to absence.
  All initial fixture modes and successful seccomp prefill establish optional routing.
  `RoutingTxFrames` and `RoutingRxFrames` derive original TX completion/worker,
  transmit entry, concrete Stack, receive completion/poll and decrypt-worker
  routing retention. Surviving peer lists are preserved while peer deletion is
  permitted. Generic checksum/GRO/IRQ/softirq/rescheduling callbacks require their
  own frames; actual checksum and Stack callbacks are discharged. Whole-call lifts
  preserve optional completion state on normal return and leave the journal
  unchanged on every outcome, retaining only prior history safety on Stop. They
  do not assert a failed World, packet authorization or enclosing scheduler closure.
  `RoutingAdmissionFrames` covers actual index acquisition, receive enqueue,
  consumeData and complete wgReceive, including normal EPIPE/ENOSPC cleanup.
  `RoutingNapiFrames` closes both actual direct poll callers, IRQ-exit placement
  and crypt iterations with concrete checksum/Stack/rescheduling callbacks.
  `RoutingMaintenanceFrames` covers all five timer callbacks and device open/up/
  namespace exit. These original normal-endpoint frames require no residency,
  affiliation, credit, saved-list or drain premise. Their whole-call lifts preserve
  optional completion state on normal return and leave history unchanged on every
  outcome; Stop retains prior history safety without a returned World.
  `RoutingSessionFrames` proves routing equality for the eight original keypair,
  index, session, response and session-timer helpers. `RoutingNoiseReceiveFrames`
  factors the canonical cookie frame and permits peer retirement in incoming
  initiation/response/cookie cleanup. `RoutingHandshakeReceiveFrames` reuses the
  exact cookie/load factor and a local checked MAC/switch cut, deriving complete
  handshake receive, queue-step and actual receive-worker iteration frames.
  No residency, affiliation, credit, valid-packet or drain premise is added.
  Their silent lifts preserve optional state on normal return and retain unchanged
  prior safe journals on Stop, without a failed World or authorization claim.
  `RoutingSchedulerFrames` derives cryptAhead, all activation iterations, complete
  run/dispatch/schedule and nested-reschedule frames by instantiating the exact
  SourceScheduler contracts with a fixed input routing view and extracting through
  erasure. Copied consistency trials keep their original Stops; no successful-trial
  premise is needed. `RoutingEnvWorkersFrames` composes actual deferred workers,
  queue checks and afterXmit, using fresh getter facts at setters.
  `RoutingEnvTimersFrames` shares the exact timer scan/fold source factors and closes
  both timer modes, idleTimers and afterAdvance with concrete callbacks. These
  all-input normal frames add no residency, affiliation, credit or drain premise.
  Their whole-call lifts preserve optional state on normal return and leave the
  journal unchanged on every outcome; Stop retains only prior history safety.
  Remaining Env traffic/control, syscall/Runner execution and packet authorization
  remain open.
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
  lifecycle preservation; the later completion layer supplies whole device-command
  composition and guarded device lifecycle. Enclosing syscall/Runner execution and packet paths remain open.
  Its five exports pass scoped/full builds, independent frozen review and coordinated checks.

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
  between the local refusal/disposal endpoints, initialized syscall/Runner composition
  and joint receive-pipeline conservation
  remain open. The RX scheduler extension passed coordinated validation at its preceding checkpoint. `PrevQueue`
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
  `Logged/ProjectsUnderTo` supports exact projections with mapped results.
  `StampedGro`, `RxPollJoint` and `RxPollJointProjection` carry captured allocation
  stamps through the actual second getter, GRO buffers and focused callbacks,
  with unconditional source/GRO projection and allocation-conditional direct
  lifetime projection. `RxPollStampSafety` retains a fresh local occurrence
  journal beside arbitrary valid prior lifetime history. `RxPollStampPhase`
  proves full stamped callback/removal provenance, distinct removal and callback
  allocation stamps on every reached prefix, and their observed release on normal
  poll completion. Failed callbacks retain their entry and may leave a pending
  stamp. `RxPollCaptureSupport` connects each removal and entered key to the
  original capture read before its removal inside the appended suffix. Allocation
  safety excludes prior releases; normal-return releases belong to this suffix.
  `RxPollHistory` starts each poll with fresh local metadata and exactly the current
  lifetime history, preserving global audit/probe interleaving by appending only
  the new suffix. Its direct audit projection needs no history-neutrality premise.
  `RxPollComposition` retains distinct entry stamps across finite poll sequences
  and restores released-entry boundaries on normal return. Its generic focused
  audit frame preserves recorded metadata, without certifying nested poll coverage.
  `RxNapiCuts` factors the complete saved-map scan and short-circuit IRQ scan,
  retaining exact source equations for softirq, inline polling and IRQ exit.
  `RxNapiHistory` uses the stamped observer at both direct source poll sites;
  all three callers erase exactly, project directly to the existing R2 audit
  observer at the identical incoming history, and preserve the entry-stamp
  boundary on normal return and uniqueness on failed prefixes.
  `RxWorkerCuts` factors the nonpolling encryption tail and exact RX publication
  prefix, deriving the cached setter's identity from its original getter.
  `RxWorkerHistory` observes concrete encrypt/decrypt softirq and IRQ callbacks;
  `RxActivationHistory` covers transmit pre-encryption and one actual activation
  iteration, including temporary work queues, suspended bookkeeping and late Stops.
  All four contracts directly project to the existing focused R2 observers at the
  same incoming audit history and preserve normal boundaries/failed-prefix uniqueness.
  `RxActivationRunHistory` observes complete activation runs and dispatch, including
  original occupancy reads, queue selection, section records and failed prefixes.
  `RxScheduleHistory` carries stamped committed polls through actual scheduling and
  nested rescheduling, projecting directly to the existing full R2 audit, including
  exact consistency-filter probe payloads. Copied trial histories stay separate;
  each reached probe supplies allocation validity and exact ordered trial decisions.
  `RxEnvWorkersHistory` observes deferred crypt/send processing and afterXmit;
  `RxEnvTrafficHistory` covers injection and both flood receive-worker modes;
  `RxEnvBatchHistory` retains batch CQEs and the inline poll inside its original
  NET_RX receive section. Each projects directly to the corresponding full R2
  audit at the same incoming history and preserves normal release boundaries
  and failed-prefix uniqueness. Only inspected poll-free leaves are focused.
  `RxEnvTimersHistory` observes both timer passes and wait continuations, focusing
  only the literal poll-free placeholder timer block with its own saved-peer scan
  proof. Reset/absent-device return precede that block; crypt/send work follows it
  through concrete observers. `RxEnvControlsHistory` observes idle timers before
  the original observation tail and focuses inspected poll-free controls. Explicit
  mappings cover all fifteen deferred and fifteen remaining environment cases,
  with direct same-history full R2 projection and normal/failed boundary contracts.
  `WG/DeliveryOrder/` exports these R4 components. Initialized syscall/Runner
  composition, ownership and receive-pipeline conservation remain open.

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
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | ca6b22e | current |
| R1: anti-replay uniqueness and inclusive floor | No wire counter is accepted twice in one allocation lifetime; every accepted counter is at or above the inclusive lower edge, for pure runs, original validator calls and accepted runner histories. Equality at the charter's floor is intentionally permitted, with a concrete recorded replay. | `Leanux/Proofs/WG/AntiReplay/` (`Statements.lean`, 9 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r1--anti-replay-uniqueness-and-the-inclusive-floor) | ca6b22e | current |
| R2: initialized lifetime safety | For every typed Runner trace and both placeholder/flood modes, committed peer/keypair/packet access histories are safe from release-before-access, including failed prefixes. Every actual reached consistency-filter entry is allocation-valid and supplies exact ordered filter correspondence and safe isolated copied-trial histories. The observer preserves exact original JSON or indexed Stop without parser, array-length, progress or success premises. Original local contracts and endpoint identity refinements remain available. Historical stale-cursor inputs retargeted replacement identities; their current full recipes reject at operation 3 under the pending-dump guard. Raw-reference affiliation/credit is a separate stronger property. | `Leanux/Proofs/WG/LifetimeSafety/` (`Statements.lean`, 208 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r2--lifetime-identity-and-retained-references) | ca6b22e | current |
| R3 components: prefix arithmetic, pure mutations and represented forests | Original IPv4/IPv6 helpers and all bounded-input normal insertion cases refine pure insertion and represented-tree longest-prefix lookup, retaining exact refusal/rollback endpoints. Original removal has an all-input loop equation and exact raw endpoints, including late Stops. From ForestRep, Compressed, Nodup and explicit target membership, unified removal-step dispatch derives all seven cases and gives total source execution, both-family pure erasure, exact retired-node absence, all-peer list filtering and full outside-forest/device/Kernel frames. Validity and actual-root longest-prefix lookup follow. Explicit resident-only list coherence additionally yields total complete original removeByPeer, preserved coherence, exact peer-owner filtering and conditional sequence/list effects. The combined routing invariant now preserves resident-list coherence and raw owner/frontier bounds through original normal insertion, both refusals and complete removal. Original creation/refusal and raw release preserve the invariant; finite actual normal calls from the configured fixture refine canonical flat updates without node IDs and reached-root longest-prefix lookup. Actual local parsed attributes now justify setAllowedip bounds and normal insertion composition. Complete original normal WG.free empties both represented families and resident lists, preserves other fields/frontiers, increments sequence once and only deletes nodes; clear now participates in finite flat histories and actual-root lookup. Whole-setAllowedip/removal completions and the actual acquired-peer configuration stage now preserve semantically valid completed prefixes on later Stop and derive normal reached-state flat agreement, through concrete deletion-permitting send/flush/cleanup frames. Actual lookup/create outcomes now derive residency through the complete public setPeerCmd observer. Successful public parseTrace supplies address shape for every configured peer; malformed entries remain permitted alternatives. Entry routing stays explicit, while local stage contracts retain their stated residency/shape inputs. Complete original wgSetDevice now composes the clear/removal/peer-command journal through concrete configuration and socket frames; parsed device commands need no separate shape premise. Successful clear/remove-all leaves the folded flat tables empty. Optional routing now covers absent whole configuration, actual guarded create/down/destruct/delete and every fixture/prefill mode without altering event validity. Concrete silent TX/Stack/RX completion and poll frames now preserve routing and surviving lists; generic worker callbacks retain explicit frame contracts. Concrete receive admission, both direct NAPI poll callers, IRQ placement, crypt iterations, five timer callbacks and device open/up/namespace exit now close further original callers without callback/residency premises. Session creation, incoming Noise/cookie processing, complete handshake receive and the actual receive-worker iteration now also retain routing without residency/credit premises. Whole-call lifts preserve optional completion state on normal return and unchanged safe histories on every outcome. Complete scheduler, deferred workers and both environment timer modes now retain routing through original source contracts. Remaining Env traffic/control, syscall/Runner execution and packet paths remain open; clear totality and physical-node emptiness are not claimed. | `Leanux/Proofs/WG/CryptokeyRouting/` (`Statements.lean`, 111 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r3--cryptokey-routing-in-progress) | ca6b22e | current components; remaining Env/Runner and packet paths open |
| R4 components and GRO order finding | Exact physical-ring laws and finite journals conserve admitted occurrences across consumed/live and retired/stale contents; tag erasure permits duplicate payloads. RX enqueue/consumeData/decrypt and TX enqueue/createData/encryption refine those journals on reached prefixes under explicit callback contracts; initialized calls inherit conservation and ordinal distinctness. TX occurrences are whole batches, not constituent packet identities. Original TX/RX success independently implies an entry ring that is not full. Queue/poll and concrete stack contracts establish per-poll removal prefixes, selected GRO callback order and occurrence provenance. An accepted generated replay refutes chronological post-GRO stack order. Concrete RX scheduler calls now discharge their callbacks; copied trials have separate exact decisions/filter and initialized prefix conservation. The adjacent source lookup/reference repayment restores the semantic Kernel on normal return, with exact access-prefix erasure and conditional slot-affiliation preservation. Joint TX disposition observations now project exactly to createData ring/access histories; full-step access projection uses entry AllocationInv. Source-derived normal endpoints now retain the EPIPE queue item and DEAD head with unchanged ring, erase ENOSPC packet slots, and dispose the actual DEAD txStep head without socket output. Publication retains every peer TX queue through its temporary reference interval without a peer-affiliation premise. Transport between these endpoints under arbitrary schedules remains open. One joint stamped rxPoll now projects directly to the original poll, GRO occurrence journal and lifetime history. From arbitrary valid prior lifetime history, removal/callback stamps are distinct on every reached prefix and all have actual releases on normal poll completion; full stamped callback provenance is unconditional. Original capture reads now support each removal and entered key inside the new suffix, excluding incoming releases. A persistent journal projects directly to the existing audit observer at the same lifetime history; finite original-poll sequences retain distinct entry stamps, with actual releases restored on normal boundaries. The direct softirq and inline poll callers plus IRQ exit now retain exact erasure, direct audit projection and the same boundary/failed-prefix uniqueness; every reached direct poll uses the stamped observer. Concrete encrypt/decrypt iterations, transmit pre-encryption and one activation iteration now compose observed NAPI callbacks with direct R2 audit projection and the same normal/failed boundary contracts. Complete activation runs, dispatch, record-driven scheduling and nested rescheduling now preserve stamped committed entry uniqueness and directly project to the full R2 audit with exact reached-filter probes. Copied trial histories remain isolated. Deferred crypt/send continuations, injection, both flood receive-worker modes and batch item/full processing now retain actual scheduler calls and the batch inline poll inside its NET_RX wrapper, with direct same-history R2 audit projection. Both timer modes, wait continuations, observation and inspected poll-free lifecycle/control calls now complete the local deferred and remaining Env families, with explicit constructor coverage and direct full-audit projection. Initialized syscall/Runner composition, RX carrier preservation and joint receive-pipeline conservation remain open. | `Leanux/Proofs/WG/DeliveryOrder/` (`Statements.lean`, 107 terminal theorems; `ReplayGro.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r4--queue-poll-and-delivery-order-components-in-progress) | ca6b22e | current components; initialized Runner and pipeline closure open |
| R5: key lifetime enforcement; Rule Zero findings | Thirteen local theorems identify exact original clock tests, RX AEAD admission and failed-tag coverage, accepted-wire-nonce bounds, TX staging certificates, zero-timer store framing and timer-pass erasure. Accepted original/observed replays authenticate nonce R+1 before rejection and encrypt queued transport keepalives after recorded expiry or zero/clear before a new handshake, using the same packet-held material. New time inputs have coherent coarse/jiffies/arm arithmetic, without a Linux schedule claim. The original unconditional statement is false; universal replacement transport theorems are not claimed. | `Leanux/Proofs/WG/KeyLifetime/` (`Statements.lean`, 13 terminal theorems; `Replay.lean`, `ReplayDelayed.lean`, `ReplayPostClear.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r5--key-lifetime-enforcement-rule-zero-findings) | ca6b22e | current |
| R6: cookie exclusion and retry-limit finding | Original under-load calculation and rejected-initiation suffix are exact. Invalid MAC2 against the actual original cookie result executes only the cookie reply; invalid MAC1 drops earlier. Ordinary completion preserves full Noise stores, indices and peer/keypair allocation counters. An accepted generated episode has 19 retries and 20 total initiations with MAX=18, then gives up on callback 20; this refutes the literal limit without claiming a universal replacement bound. The whole advance observer has exact original erasure. | `Leanux/Proofs/WG/FloodResistance/` (`Statements.lean`, 6 terminal theorems; `Replay.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r6--cookie-exclusion-and-retry-limit-finding) | ca6b22e | current |

The gate for every row: `capped -- scripts/in-bundle scripts/proof-gate`
(the build, the axioms of every terminal statement, the forbidden tokens,
the imports and the default targets).

The R4 timer/control extension passes its 296-job scoped Statements and 463-job
full proof builds. The coordinated gate passes all 469 terminal declarations
(107 R4; 467 theorems and two definitions) with permitted axioms only. Fresh stock
kernel replay, the 60-job default build and 124 unit tests (23.711 seconds, one
skip) pass. Exact five-file scope/hashes, all 467 prior terminal statements/proof
bodies, census, tokens/imports, whitespace including new files and mirror equality
pass. Independent frozen review is clear after correcting one stale scope sentence.
The mirror remains `ca6b22e`; initialized syscall/Runner composition, successful stack
delivery and receive-pipeline conservation remain open.
Historical checkpoint counts and validation timings are recorded in their commit
messages. The [campaign report](2026-10-13-proof-campaign.md) retains effort,
failed attempts, counterexamples and reproduction commands. The supplementary
Lean 4.35 six-checker export passed on 417 declarations at the toolchain carry;
it does not cover subsequent declarations and was an export-only speedbump,
not a sandboxed project gate. Current validation is the named proof gate and
fresh stock kernel replay above.

Runner/anti-replay contracts include both floodExact modes; timer contracts
retain recorded caller-jiffies operands and failure order. The R6 report retains
the IPv6 rate-table lifecycle source discrepancy without claiming an accepted
replay or differential finding.

## Result table: claim, theorem, boundary, premises, counterexample, pin

What each result's statements establish and what must not be inferred from
them, following the [pre-release review](2026-10-14-pre-release-review.md) §4.
These rows describe the current campaign source over mirror `ca6b22e`; validation
status is recorded above. The earlier review read proof snapshot `ffea367`,
which was a proof-branch commit, not its mirror revision. Names below are
representative exports; each result's `Statements.lean` gives the complete surface.

| Result | Original claim (charter) | Representative theorems | Event boundary | Substantive premises | Counterexample or remaining obligation |
| --- | --- | --- | --- | --- | --- |
| ReplayWindow S1 | Every accepted execution has its exact acceptance history and no two events share a lifetime and wire counter | `S1` | Committed validator acceptances in a successful `executeTrace`, including packets dropped later; copied scheduler trials are separate | A successful original runner execution, for every placeholder/floodExact setting. The exact logged execution is a conclusion, not an extra premise | No remaining S1 obligation; the theorem concerns the executable mirror, not all Linux executions |
| ReplayWindow S2 | `counterValidate` returns the receive.c rule's result and replay state | `S2`, `S2_acceptance`, `S2_update` | Original validator versus the Lean `CounterWindow.step` rule | A resident keypair with a 128-word bitmap, established by reachable allocation | No remaining S2 obligation. Identifying `step` with the C rule is a source correspondence claim; the refinement is within Lean |
| ReplayWindow S3 | Nonreceive calls and validator calls preserve the other keypairs' windows | `S3`, `S3_nonreceive`, `S3_validator`, `S3_surviving`, `S3_syscall`, `S3_syscall_ambient` | Surviving old cells; other cells at a validator; whole-syscall evolution including ambient work | The stated lifetime-aware invariant and successful original execution; the nonreceive specialization uses its explicit call classification | Allocation/deletion are permitted and reused slots denote new lifetimes; equality of every store cell was never claimed |
| R1 anti-replay | No repeated acceptance under one lifetime; nothing at or below the floor accepted | `pure_uniqueness`, `mirror_uniqueness`, `runner_uniqueness`, `pure_run_floor`, `mirror_floor`, `mirror_run_floor`, `runner_floor`, `pure_run_below_floor` | Pure window runs, original validator calls and accepted runner histories | The corresponding S1/S2 premises | `inclusive_boundary_witness` and an accepted replay show equality at highest minus 8128 may be accepted. The proved exclusion is strictly below the floor |
| R2 lifetime safety | No dead identity is resolved after release | `runner_audit_erasure`, `runner_initialized_access_safety`, `runner_initialized_reached_trials`; prior store, access and caller-family contracts | Original initialized Runner, every typed Trace and both placeholder/flood modes; committed failed histories and separately certified copied trials at actual reached filter entries | No parser, hidden-array length, progress, success or initial allocation premise on the initialized exports. Local helper premises are discharged by original initialization, successful prefill and concrete caller contracts. Erasure holds for arbitrary incoming history; initialized safety starts from empty history | The stated allocation-identity access property is closed; coordinated validation passes. No failed World is asserted. Reference affiliation/credit, routing authorization, pipeline conservation, C memory safety and executable diagnostic output are separate. The raw stale-cursor witness retargets a replacement identity; its historical runner recipes now reject before deletion |
| R3 cryptokey routing | Lookup follows insertion/removal history; incoming and outgoing packets are bound to the owning peer | `pureTree_lookup_correct`, `original_findNode_lookup_correct`, `original_insert_longest_prefix`, `original_add_all_cases`, `original_insert_all_cases`, `pure_removal_entries_and_lookup`, `original_removal_*`, `original_removeStep_forest_*`, `original_removeStep_then_findNode`, `original_removeByPeer_forest_*`, `original_removeByPeer_then_findNode`, `original_insert_routing_preserved`, `original_insert_coherent_peer_maps`, `original_insert_refusal_coherent`, `original_removeByPeer_routing_preserved`, `original_peerCreate_routing_*`, `original_peerPut_routing_preserved`, `original_initialized_routing_history`, `original_initialized_history_findNode`, `parsed_setAllowedip_bounded_call`, `parsed_setAllowedip_routing_preserved`, `original_rootRemove_lists_normal`, `original_free_routing_endpoint`, `original_free_then_findNode`, `original_routing_silent_frames`, `routing_completion_source_erasure`, `setAllowedip_completion_routing`, `original_peerConfigTail_routing_prefix`, `original_peer_update_completion_erasure`, `original_peer_removal_routing_prefix`, `original_peer_update_routing_prefix`, `original_configuration_acquisition_routing`, `original_setPeerCmd_completion_erasure`, `original_setPeerCmd_routing_prefix`, `parsed_trace_peer_commands_routing`, `original_device_configuration_completion_erasure`, `original_device_configuration_routing_prefix`, `parsed_trace_device_configuration_routing`, `original_optional_lifecycle_erasure`, `original_optional_lifecycle_routing_prefix`, `original_optional_routing_initialization`, `original_tx_routing_frames`, `original_rx_routing_frames`, `original_traffic_routing_completion`, `original_receive_admission_routing`, `original_concrete_napi_routing`, `original_timer_device_routing`, `original_session_routing_frames`, `original_handshake_receive_routing_frames`, `original_handshake_routing_completion`, `original_scheduler_routing`, `original_environment_worker_routing`, `original_environment_timer_routing` | Represented tries versus an independent flat-prefix winner; pure removal, every raw original removal arm, unified represented-forest target removal and complete coherent peer removal; initialized finite original-call histories and reached-root lookup; local actual-parser/guard insertion cuts and complete normally returned WG.free; whole-setAllowedip/removal completion journal and actual original acquired-peer update, retaining safe earlier completions on Stop; complete public peer command with derived lookup/create residency; public parseTrace supplies every configured peer's address shape; complete original device configuration observes clear before remove-all cleanup, with empty folded tables after normal remove-all; optional-device state through guarded creation/down/destruction/deletion and absent configuration, initialized from every fixture/prefill mode; silent whole TX/Stack/RX calls, receive admission, concrete NAPI/crypt callbacks, timer callbacks, device controls, session helpers and the complete handshake receive/actual worker iteration, full scheduler, deferred workers and both environment timer modes retain routing on normal return | Insertion uses the stated address bounds, fresh IDs and resident target. Removal derives local linkage/separation from ForestRep, Compressed, Nodup and explicit target membership; validity additionally supports lookup. Complete peer removal also assumes a resident target and explicit resident-only list coherence, which it preserves. Original insertion covers bounded-input normal returns, including allocation refusals. Explicit RoutingInvariant additionally supplies resident list coherence and node/peer/owner frontier bounds, all preserved by these insertion/removal calls; owner bounds do not imply residency. Finite histories instead derive this invariant from the original configured fixture and actual normal create/insert/remove/release/clear calls; only insertion carries reached-input bounds/residency, and query bounds are explicit. Local parser success derives address shape; setAllowedip guards derive family/CIDR/width bounds. Root-list clearing uses resident-list ownership and a represented subtree. Full clear uses the explicit entry RoutingInvariant and original normal return; its source-derived endpoint empties represented roots/lists, preserves complete peers except lists and other Kernel/device fields except roots/sequence, and permits only node deletions. Neither requires owner residency. Completion-stage semantics use explicit entry RoutingInvariant/flat agreement, resident insertion target and local attribute shape; actual insertion outcomes preserve loop residency, while concrete send/flush/cleanup frames permit later deletion. The complete public setPeerCmd contract derives target residency through actual lookup/create outcomes, requiring only entry routing/flat agreement and local address shape. Successful public parseTrace discharges that shape for its configured peers, without excluding malformed entries. The present-only device contract retains routed entry. The optional lifecycle/configuration contracts use GlobalCompletionState: absence denotes empty flat tables, while presence retains routing/flat agreement. DeviceAddressShape is discharged by successful public parsing; no fixture-authenticity, saved-list, drain or credit premise is added. Actual fixture initialization handles all net/bare flags, and successful prefill preserves it. Silent traffic frames add no resident-owner, credit, affiliation, valid-packet or drain premise; generic callback arguments require RetainsRoutingCall, with actual checksum and Stack callbacks discharged. The concrete NAPI/crypt, admission, maintenance, handshake, scheduler, deferred-worker and environment-timer contracts require no callback, residency, affiliation, credit or successful-trial premise. Erasure has no such premises; failed outcomes carry safe completed history, not a returned World | Enclosing syscall/Runner execution and both packet paths remain open. Clear totality and physical-node emptiness are not asserted. A raw peer-slot winner is not yet identity authorization; no accepted misrouting counterexample is claimed |
| R4 delivery | Per-peer/key delivery follows receive order for every recorded schedule; loss occurs only at explicit arms | `two_carried_slots_*`, `original_enqueue_epipe`, `original_poll_selected_callback_complete`, `original_poll_removal_ordinals`, RX/TX ring-journal families, `original_rx_scheduler_*`, `original_rx_consistency_*`, `original_lookup_*`, `original_tx_disposition_*`, `original_tx_strict_reference_cut`, `original_create_data_*_endpoint`, `original_dead_tx_step_disposal`, `joint_poll_correspondence`, `joint_poll_fresh_history`, `joint_poll_removal_identity_safety`, `joint_poll_callback_identity_safety`, `joint_poll_callback_removal_provenance`, `joint_poll_callback_entry_prefix`, `joint_poll_capture_read_suffix`, `joint_poll_suffix_lifetime`, `joint_poll_persistent_correspondence`, `joint_poll_boundary_composition`, `joint_poll_finite_sequence`, `original_napi_softirq_joint`, `original_inline_poll_joint`, `original_napi_irq_exit_joint`, concrete crypt-worker/activation-iteration contracts, `original_activation_run_joint`, `original_dispatch_joint`, `original_recorded_schedule_joint`, `original_nested_reschedule_joint`, `original_deferred_workers_joint`, `original_inject_joint`, `original_flood_joint`, `original_batch_joint`, `original_environment_deferred_joint`, `original_environment_remaining_joint` | Physical ring mutations, reached prefixes, poll removals and selected GRO callback entries; concrete RX scheduler, direct NAPI and crypt-worker callers, complete activation/dispatch/scheduler calls, deferred crypt/send processing, injection, both flood modes, batch item/full processing, both timer/wait modes, observation, lifecycle/control families and exact saved trial probes | Explicit callbacks for the local worker families; concrete RX scheduling discharges its callbacks. Initialized conservation uses a prior refined ring history; retired/stale structural representation requires positive ring size. The W7 endpoint contracts assume normal return and their stated entry live-peer/capacity/full-ring or actual logical-DEAD-head conditions. The joint poll starts a fresh local metadata journal with arbitrary prior lifetime history satisfying AllocationInv; no per-iteration freshness, queue-uniqueness or release premise is added. Releases are asserted only on normal return. Finite poll composition starts from AllocationInv; its persistent boundary additionally retains audit/probe validity, previous entry distinctness and their observed releases. These boundary properties are derived by initialization and composition, not assumed per poll iteration. The direct NAPI, crypt-worker, complete scheduling and complete local environment-family contracts retain this same entry invariant; their empty-history corollaries require only local AllocationInv. Actual saved probes derive allocation validity and ordered copied-trial safety; they are not committed callback entries | Accepted `r4-gro-reorder` refutes chronological post-GRO order; selected normal-before-held order is proved. Local W7 source cuts and normal EPIPE/ENOSPC/DEAD-step endpoints are checked; initialized transport between those endpoints, RX carrier preservation, initialized syscall/Runner composition and joint receive-pipeline conservation remain open. Both direct poll sites, their crypt-worker callers, complete local scheduling and all deferred/remaining Env constructors are observed exactly, including full audit probe correspondence. Capture/read support, exclusion of prior releases, exact audit projection and cross-poll entry uniqueness for finite original-poll sequences are proved; a generic focused audit frame does not observe any polls hidden in its callee. Universal outgoing conservation is additional scope. Callback entry is not delivery, local ordinals are not global identities, and a stopped prefix has no retained World |
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
| LifetimeSafety | 208 | 208 | 0 |
| CryptokeyRouting | 111 | 111 | 0 |
| DeliveryOrder | 107 | 107 | 0 |
| KeyLifetime | 13 | 13 | 0 |
| FloodResistance | 6 | 6 | 0 |
| Total | 469 | 467 | 2 |

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
