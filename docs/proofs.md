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
  `KernelEffects` shares record-consumer and refcount contracts; `WGTime`
  frames the original recorded age tests; `Kernel`
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
  without changing the previous interleaving. `PrefixLoops` gives finite range
  and map composition plus accumulator-dependent list-loop contracts for
  failure-retaining observers. `Capture` retains exact original-action run
  witnesses with erasure and prefix contracts. `PrefixWorkers` composes one
  original worker iteration with explicit step and rescheduling contracts.
  `TimerPass` observes completed original timer, clear/send-worker and crypt
  scheduler calls, retaining exact before/after Worlds and failure erasure.
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
  `CounterAccess`, `AllowedLookupAccess`, `ReceiveCompletion` and `ReceivePoll`
  cover the complete validator, routing lookup, receive completion and polling
  with an explicit callback contract; `ReceiveFailure` retains the exact
  malformed-bitmap failure prefix. `SavedPeers` records demanded saved-map
  reads with a residency premise; `SocketFrames`, `LoopbackAccess`, `SocketCache`,
  `SocketSend` and `SocketCalls` cover ten complete cache/endpoint/loopback/tunnel/IPv6
  callers and their failure prefixes. `DeviceXmit` and `StackAccess` observe the
  complete transmit entry, actual stack callback and receive poll using that
  callback. IPv4 socket send and outer scheduler/lifecycle coverage remain open.
- `Leanux/Proofs/WG/LifetimeSafety/`: campaign R2 in progress: keypair store
  absence/freshness at original operation endpoints (`Keypairs/Identity`),
  peer/packet helper-family contracts, and a checked stale dump-cursor finding.
  Full caller/lifecycle and all-internal-access safety remain unproved.
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
  all-peer list filtering; successful graft representation remains open.
  `WG/CryptokeyRouting/` exports these checked components of campaign R3;
  general mutation/history and packet-path refinements remain open.

- `Leanux/Proofs/WG/Queues/`: original guarded ring production, symbolic
  no-wrap filling and unretired consumption, the concrete two-carried-slot
  witness, and the complete original enqueue helper's normal-return ring
  projection. `PrevQueue` proves original logical FIFO, cached-peek and malformed
  Stop laws. `RxQueueView` and `RxHelperFrames` retain full receive queues tagged
  by device epoch and peer identity through original reference, release, replay
  validation and key-confirmation helpers. `RxQueuePrimitives`,
  `RxMaintenanceFrames`, `RxTxFrames` and `RxCompletionFrame` extend these
  concrete contracts through endpoint/timer maintenance, staged transmission
  and complete original receive completion, allowing peer deletion.
  `WG/DeliveryOrder/` exports these R4
  components; whole-poll and whole-schedule order, ownership and conservation remain open.

- `Leanux/Proofs/WG/KeyTimes/`: exact original signed clock-test and comparison
  records (`Clock`), receive admission guards and the later wire-counter
  acceptance bound (`Receive`). `ReceiveAttempts` observes the actual AEAD
  boundary, proves admission for every event, and gives exact singleton coverage
  and failed-authentication endpoints. The zero-timer callback's complete
  transport-keypair-store frame is in `ZeroTimer`. `Staging` certifies actual
  completed TX allocations and submitted arguments with original key/clock
  witnesses and assigned-nonce bounds, retaining events on subsequent failure.
  `WG/KeyLifetime/` exports R5's local components and a reconstructed accepted-run
  wire-limit witness. A separate accepted legacy-mode replay uses packet-held
  key material after clear, with deliberately incoherent coarse/jiffies clocks.
  Admission-to-encryption transport, whole-run attempt composition and
  coherent-clock post-clearance schedule exclusion remain open.

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

## Results

| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | 2c7a076 | current |
| R1: anti-replay uniqueness and inclusive floor | No wire counter is accepted twice in one allocation lifetime; every accepted counter is at or above the inclusive lower edge, for pure runs, original validator calls and accepted runner histories. Equality at the charter's floor is intentionally permitted, with a concrete recorded replay. | `Leanux/Proofs/WG/AntiReplay/` (`Statements.lean`, 9 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r1--anti-replay-uniqueness-and-the-inclusive-floor) | 2c7a076 | current |
| R2 components: store identities; access prefixes; stale dump-cursor finding | Original operation endpoints preserve identity provenance and fresh slot reuse. Failure-retaining observations cover complete peer creation/reference calls, keypair allocation/acquisition/release/rotation/session creation, packet allocation/free, receive entry/maintenance/completion, receive polling with the actual stack callback, transmit entry, TX staging, decrypt iteration and ten cache/endpoint/loopback/tunnel/IPv6 calls. Saved-peer scans retain the demanded prefix with explicit residency. Explicit ambient callback contracts compose access safety, resident uniqueness and allocation bounds initialized by runner fixtures. Exact runner checkpoints reproduce a retained dump cursor releasing a replacement peer, including a variant that leaves its trie binding orphaned. Remaining callers, lifecycle and whole-run internal-access safety remain unproved. | `Leanux/Proofs/WG/LifetimeSafety/` (`Statements.lean`, 116 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r2--lifetime-identity-and-retained-references-in-progress) | 2c7a076 | current components; R2 in progress |
| R3 components: prefix arithmetic, insertion and represented-tree lookup | Original IPv4/IPv6 prefix helpers refine leading-bit arithmetic. Valid pure trees have bounded depth and longest-prefix lookup; pure insertion preserves structure and replaces exactly the canonical-prefix binding. Original placement terminates with the corresponding context. Original empty-root, arbitrary-depth empty-child and exact-prefix insertion refine that tree and lookup from the actual device root, with exact allocation/refusal and sequence effects and preservation of any supplied opposite-family representation. Original list deletion terminates with pointwise filtered peer lists and unchanged identities. Selected-root graft normal returns have exact source endpoints and rollback effects; successful graft representation, general mutation/history and packet-path refinements remain unproved. | `Leanux/Proofs/WG/CryptokeyRouting/` (`Statements.lean`, 27 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r3--cryptokey-routing-in-progress) | 2c7a076 | current components; R3 in progress |
| R4 components: physical full-ring refusal and receive-queue laws | Two original produce/consume pairs leave slots 0 and 1 occupied but logically consumed. The next 1024 guarded producer attempts accept 1022 and reject two, with exact FIFO contents and cursor/count geometry. Every normal original enqueue return has its source ring effect; -EPIPE implies an entry-full, unchanged encrypt ring. Original PrevQueue peek/drop removes exactly the logical head, with structural totality and an explicit malformed Stop. Original helper frames preserve receive queues; peer release, staged TX, key refresh and complete receive completion retain each surviving entry. Whole-poll and recorded-schedule delivery/conservation remain unproved. | `Leanux/Proofs/WG/DeliveryOrder/` (`Statements.lean`, 19 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r4--full-ring-drop-component-in-progress) | 2c7a076 | current components; R4 in progress |
| R5 component: receive admission and key-time boundaries | Original age tests retain the exact consumed clock, signed64 comparison and operands. Every observed original AEAD attempt requires receiving validity, an unexpired recorded predicate and stored counter below R, with exact singleton coverage including failed authentication; later validator acceptance requires wire nonce below R. The zero-key timer callback preserves the whole transport-keypair store. Original staging submission carries actual key/clock executions, assigned nonce bounds and completed allocation witnesses, even on a later Stop. A reconstructed accepted run decrypts nonce R and then rejects it. Exact timer-unit observations support a second accepted replay using packet-held material after clear in synthetic, incoherent-clock legacy mode. Admission-to-encryption transport, whole-run attempt composition and coherent-clock post-clearance exclusion remain unproved. | `Leanux/Proofs/WG/KeyLifetime/` (`Statements.lean`, 13 terminal theorems; `Replay.lean`, `ReplayPostClear.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r5--receive-admission-and-key-time-boundaries-in-progress) | 2c7a076 | current components; R5 in progress |

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
