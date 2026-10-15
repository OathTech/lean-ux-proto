# WireGuard proof campaign 2

## Current checkpoint

Work is on `proofs/campaign-2` in `.worktrees/proofs-campaign-2`, over mirror
`de62c9d`, Lean v4.35.0. It is **lagging main's representation batch
`cb2348e`**; no merge or push has occurred during this resumption.
**None of H1–H6 is complete.** Scoped validation passes; the full proof gate
remains failed in inherited campaign-1 files.

| Result | Headlines | Established checkpoint | Still open |
| --- | ---: | --- | --- |
| H1 Noise | 20 | State/slot contracts, ordered clearing and rotation, static release budgets, full normal session effects and consecutive first-match confirmation | Whole-call edge coverage, session totality, exposed derivation-clock provenance, allocation-lifetime confirmation |
| H2 Index | 51 | Exact index operations and successful-lookup provenance, original caller table safety, successful session publication coherence, session store bound and distinct allocation IDs across actual consecutive calls | Reachable hashed uniqueness and owner/peer-word residency through driver entries; outer-removal frames await decision |
| H3 Roaming | 12 | Data publication/first-poll join, both authenticated handshake cuts and inspection retaining them through continuation failure | General queue/caller coverage, final endpoint preservation |
| H4 Configuration | 73 | Configuration leaves/flags, bounded public readback, port/fwmark/key effects, normal live-key removal and private-key collision composition, full REMOVE_ME and witness-free normal REPLACE_ALLOWEDIPS effects, empty-root insertion, exact root transfer and actual peer-dump readback | Collision completion, queued-work/remove-all ordering, mixed attributes, global ownership and general multipart readback |
| H5 Progress | 33 | Historical backlog counterexample, source-connected scheduling inspections, cut/pow/drain/poll bounds | Whole-worker record decrease, full operation-end coverage and global termination/progress |
| H6 Timers | 39 | Local arm/delete rules, recorded delays, actual retry/send pairs, consecutive same-peer count bound and both response session hooks, data-completion sends and receive-data timer-hook composition | Complete caller/site coverage, scheduler episodes and session-relative arm counting |

Total: **228 headlines**. The factoring checkpoint `69f988a` preserved all 153
then-existing headlines. Recent mathematical checkpoints include `a2923a1`
(H1 consecutive confirmation) and `7b34fa4` (H6 response-session timer hook).

[USER 2026-10-15] Resume before the split lands; factor claims over a
WireGuard-only view and separate frames, then continue the charter. On the
eventual split, delete frames made trivial or unstatable and retype substantive
claims. No shared-layer edits, merge or push. This supersedes the earlier pause
at `aeece72` and earlier authority to merge the index fix, which already landed
on this branch at `de62c9d`.

[USER 2026-10-15] Shared layers remain campaign 1's. Necessary local variants
must be named for the shared lemma and live in result directories. Report an
overlap larger than “a few” before copying it. The
[six-family outer-removal request](2026-10-15-campaign-2-shared-frame-request.md)
is **pending**; those variants have not been implemented.

[USER 2026-10-14] Write mirror-team requests in this tree and notify the user.
The [three existing requests](2026-10-14-campaign-2-mirror-requests.md) have been
reported; no new request arises from the latest increments.

[AGENT 2026-10-15] Use a genuine WG data projection and a separately named
ambient context, with universal execution contracts over concrete realizations.
Keep normal return, total return and exact outcomes distinct. Observations start
at the actual same entry and compose through actual successors; independent
existential runs are never spliced. Inspection totality is not original-operation
success. Public statements name neither `World` nor `Kernel`.

### Claims, frames and the split boundary

Paths below are under `Leanux/Proofs/WG/`; `.lean` is implicit. Public claims
remain the six result `Statements` modules. Their concrete source proofs are
connections to the current executable mirror, not replacement interpreters.

| Area | Data / claims / source connections | Separate frame support |
| --- | --- | --- |
| Common C2 | `Campaign2/View` is data-only; `Campaign2/Bridge` defines projection and universal execution contracts. | No shared campaign-1 layer is changed. |
| H1 | `Noise/Model`, `Statements`, `Slots`, `StateEdges`, `ConsumeEdges`, `ClearModel`, `ClearEffects`, `ClearSource`, `RotationModel`, `RotationEffects`, `RotationSource`, `SessionModel`, `SessionSource`, `ConfirmationSequenceModel`, `ConfirmationSequenceEffects`, `ConfirmationSequenceSource`; `Execution` holds the concrete monad connection; `AccessSource` holds accessor read/write contracts, reexported by `Basic`. | `KernelFrames`, `PeerFrames`, `SlotFrames`, `ClearFrames`, `RotationFrames`, `SessionFrames`. |
| H2 | `Index/View`, `LookupProvenanceSource`, `TableModel`, `OwnerWordModel`, `AllocationModel`, `ReleaseModel`, `LifecycleModel` and pure release effects/bounds; `Statements`, `HandshakeClaims`, `OwnerUpdateClaims`, `LifecycleSource`, `LinkSource`, `SendSource`, `DispatchSource`, `ResponseSource`, `ConsumeSource`, `StagedSource`, `ReceiveOperations`, `ReceiveSource`, `ClearSource`, `TimerSource`, `FlushSource`, `SessionCoherenceModel`, `SessionCoherenceEffects`, `SessionCoherenceSource`, `SessionAllocationEffects`, `SessionAllocationSource`, `SessionSequenceModel`, `SessionSequenceEffects`, `SessionSequenceSource` and the other operation/source modules. | `IndexFieldFrames`, `OwnerFieldFrames`, `StoreFieldFrames`, `LifecycleFrames`, `NewlinkFrames`, `SendFrames`, `DispatchFrames`, `ResponseFrames`, `ConsumeFrames`, `StagedFrames`, `ReceiveFrames`, `ClearFrames`, `TimerFrames`, `FlushFrames`, `SessionCoherenceFrames`, `SessionAllocationFrames`; the old `HandshakeFrames` and `OwnerFrames` paths are import-only reexports, not duplicated lemmas. |
| H3 | `Roaming/Model`, `View`, `Statements`, `EndpointClaims`, `EndpointSource`, `Authentication`, `PublicationModel`, `PublicationSource`, `PublicationClaims`, `PollEndpointModel`, `PollEndpointSource`, `PollEndpointClaims`, `ResponseModel`, `ResponseCryptoSource`, `ResponseConsumeSource`, `ResponseLookupSource`, `ResponseCallSource`, `ResponseCallClaims`, `InitiationModel`, `InitiationCryptoSource`, `InitiationLookupSource`, `InitiationConsumeSource`, `InitiationCallSource`, `InitiationCallClaims`, `HandshakeAuditModel`, `HandshakeAuditSource`, `HandshakeAuditClaims`. | `Roaming/Frames`, `PublicationFrames`, `PollEndpointFrames`; `Basic` reexports the endpoint source connection. The response and initiation increments reuse existing accessor/read/clock support without new frames. |
| H4 | `Config/Model`, `AllowedRemovalModel`, `AllowedPairsModel`, `AllowedPairsEffects`, `AllowedRemovalConverseSource`, `AllowedRemovalConverseClaims`, `QuietModel`, `LiveRemovalModel`, `LiveRemovalSource`, `CollisionModel`, `CollisionRemovalSource`, `CollisionRequestSource`, `AllowedInsertModel`, `AllowedInsertSource`, `AllowedReadbackSource`, `AllowedRoundTripSource`, `AllowedTransferModel`, `AllowedPlacementSource`, `AllowedTransferOperations`, `AllowedTransferSource`, `AllowedTransferRequestSource`, `AllowedTransferReadbackSource`, `RemoveFlagModel`, `RemoveFlagEffects`, `RemoveFlagSource`, `RemoveFlagRequestSource`, `ReplacementConverseSource`, `ReplacementConverseRequestSource`, `ClaimView`, `Statements`, `SourceClaims`, `ObservationBridge`, and existing substantive effect/source modules. | `ConcreteFrames` isolates six whole-kernel endpoint contracts; `OperationFrames` isolates seven generic helpers; `ReadbackFrames` retains socket/fixture preservation; `AllowedListFrames`, `AllowedRootFrames`, `AllowedRemovalFrames`, `AllowedPairsFrames`, `QuietFrames`, `LiveRemovalFrames`, `KeyFieldFrames`, `CollisionFrames`, `AllowedInsertFrames` isolate within-WG preservation. |
| H5 | `Progress/Model`, `View`, `Statements`, `SourceClaims`, `ObservationBridge`; `ControlLaws` is generic state/error control and `ControlSource` connects it exactly to the original worker; the scheduler/source modules retain actual execution factors. `CutModel`, `CutSource` and `CutClaims` establish original cut-loop progress; `FlushQueueModel`, `FlushQueueSource` and `FlushQueueClaims` establish original flush effects and count decrease; `PowModel` and `PowSource` connect a finite evaluator to the original arithmetic loop. `DrainModel`, `DrainOperations`, `DrainSelectionSource`, `DrainAuditSource`, `DrainEffects` and `DrainClaims` connect a phase audit and queue bound to the original workqueue drain. `PollBoundModel`, `PollBoundEffects`, `PollStepSource`, `PollLoopSource`, `PollBoundSource` and `PollBoundClaims` connect the actual receive poll to its budget audit; no new structural frames. | `StackFrames` isolates caller-guard preservation; `CutFrames` isolates record/error-location preservation; `FlushQueueFrames` isolates queue preservation through worker bodies and release. Probe/filter/no-work contracts also establish outputs and remain substantive source claims. |
| H6 | `TimerDiscipline/Model`, `View`, `SendView`, `Statements`, `ObservationBridge`, `ObservationClaims`, `SourceClaims`, `SendDispatchModel`, `SendDispatchClaims`, `RetryDispatchModel`, `RetryDispatchClaims`, `RetryRearmModel`, `RetryRearmClaims`, `RetrySequenceModel`, `RetrySequenceClaims`, `ResponseSessionModel`, `ResponseSessionEffects`, `ResponseSessionClaims`, `OutgoingResponseSessionModel`, `OutgoingResponseSessionClaims`, `DataDoneModel`, `DataDoneClaims`, `RxDataTimersModel`, `RxDataTimersClaims`, and `*Source` operational proofs. | `SourceFrames`, `RecordedFrames`, `RecordedJitterFrames`, `SectionFrames`, `SelectionFrames`, `RetryFrames`, `JitterFrames`, `InitiationFrames`, `InitiationPreservationFrames`, `SendCutFrames`, `SendPeerFrames`, `SendSocketFrames`, `SendBufferFrame`, `SendWorkerFrame`, `SendDispatchFrames`, `RetryDispatchFrames`, `RetryRearmFrames`, `WorkStateFrames`, `ResponseSessionFrames`. |

A compound exact effect is not a disposable frame merely because its name
contains “frame”: mark/generation updates, cleared-peer accumulation, reference
decrements and dump/UDP payload results remain substantive claims. The seven
H4 dump/UDP helpers with arbitrary kernel predicates are concrete source
contracts that also establish outputs. After the mirror split, delete only
structural preservation made trivial or unstatable; retain and retype those
outputs and meaningful within-WG preservation. H6's reference-decrement proof
is therefore in `SendWorkerSource`, separate from send preservation.

## H1 — Noise session state machine

The original state-edge, slot, clearing, rotation, confirmation and session
contracts are checked. Create/consume initiation can restart from any prior
state; the claim is the code's edges, not a single linear handshake. An
initiator with an existing next key demotes that next key to previous and puts
old current; without next it demotes current. Responder installation goes to
next. Slots are optional values, not a bound of three on the entire key store:
outstanding packet references can retain keys.

`ClearRun`, `RotationRun` and `ConfirmationEffect` preserve exact ordered
writes, puts, unhashing, reference changes and possible erasure. Normal effects
derive their execution evidence from the original call. Separate total-return
contracts use static `ClearReady`, counting every repeated release. Aliases are
allowed; no owner/peer equality, global reference ownership or fresh allocation
is silently assumed.

`SessionEffect` covers the complete original `beginSession`. False returns
preserve Device and allocation counter even if records were consumed. True
returns derive the accepted tag, live peer, non-NULL handshake peer word,
counter increment, allocation overwrite, role/remote-index and KDF fields,
handshake zeroing, ordered rotation and actual hashed-handshake replacement.
Birthdate remains existential; exposed derivation-clock provenance is open.
H4's expiry contracts supply slot validity, zero/unhash and actual reset-clock
observations without duplicate H1 proofs.

This does not establish retained-slot residency. For example, old next=current
may name a key with one reference and a non-NULL peer word, with previous empty.
Initiator rotation demotes next and releases current, leaving previous naming
the erased key. Confirmation can similarly release an old previous alias of
the received key. These are local invariant boundaries, **not accepted-run
findings**. Live-slot coherence belongs at completed rotation cuts, not every
primitive assignment.

The actual finite `ids.mapM (receivedWithKeypair pid)` sequence now has normal
and total contracts. On normal return, the first input matching the initial next
slot is the sole true result and supplies the exact single `ConfirmationEffect`;
all other calls return false. If nothing matches, the device is unchanged.
Result length is preserved. Normal effects need only the initial resident peer;
total completion adds `ClearReady d [p.keypairPrevious]` only when some input
matches the initial next slot. Later duplicate IDs remain allowed, and a match
leaves next empty. These are consecutive calls without another installation,
not confirmation once per allocation lifetime.

Whole-run edge ownership, session totality, reachable allocation/slot coherence
and confirmation once per allocation lifetime remain open. Exact source-call
observers with event completeness and structural execution derivations were
both considered; equal endpoints cannot justify an empty event history.
Campaign 1's existing snapshot omits the required tags/slots.

[AGENT 2026-10-15] Do not add a mixed begin/confirm-only sequence as a new
lifetime result: after a successful session zeroes the handshake tag, that
sequence cannot install another session for the same peer. Genuine repeated
installation needs the actual consume/create operations. Cursor, store-bound
and surviving-next preservation through their rejected paths and failed-reference
release remains the concrete missing support; slot confirmation alone does not
establish key residency when aliases can erase the key.

## H2 — Session index uniqueness

[AGENT 2026-10-15] Interpret “no two live sessions share an index” as no two
**simultaneously hashed receiving-index owners within a device** sharing it.
Unhashed objects retained by references do not reserve their former number.
The C unhashes before release and does not clear the stale numeric field
(`noise.c:131–139`, `peerlookup.c:192–197`); insertion tests currently hashed
entries (`peerlookup.c:119–163`). In the mirror, local ownership is in
`Device.indexTable`; `remoteIndex` is the separate peer-supplied namespace.
This is a source-grounded statement clarification, not a mirror counterexample.

Numeric-index uniqueness and embedded-owner uniqueness are separate invariants.
Owner identity and its optional peer word are also distinct. Lookup stops at
the first equal index, including a disallowed kind. Returned ownership comes
from that original row; matched-entry contracts cover NULL, zero-reference
store-back of NULL, and bounded positive-reference acquisition. They require
the relevant owner/peer residency; absent/disallowed rows have separate total
contracts. No owner=referenced-peer equality is assumed.

A normally returning successful original lookup now derives the first equal-index
permitted row, the initial owner word and resident peer, positive reference count
and non-overflowing acquisition. Its exact final device retains acquisition and
owner-word store in order, including aliases. Only the entry device is assumed;
table uniqueness, owner/peer coherence, an `isDead` condition and completion are
not asserted. The exact effect is reused on the same concrete run by determinism,
not by joining independent executions. No new frame module is needed.

Removal, specialized keypair removal, replacement, allocation and release have
exact contracts. The landed keypair removal operation is
`indexRemove (.keypair id)`, not a separate declaration. Replacement preserves
numeric indices; owner uniqueness additionally needs a fresh destination owner.
Insertion first removes the old owner row and then installs a fresh index.
Recorded-collision results retain their contiguous draw/layout hypotheses,
arbitrary suffixes, retries and exact exhausted-stream error. The corpus-draw
two-call instance does not constitute general runner coverage. Errors expose
no final state.

`TablesSafe` combines both uniqueness properties with the hashed-key-owner
allocation bound. It is preserved on normal return through original lifecycle,
creation/deletion, initiation/response sending and consumption, staged/keepalive
sending, handshake reception, receive iteration, clear workers, timer dispatch,
workqueue draining, timer stop and post-death removal. These contracts do not
promise readiness or completion.

The session-coherence headline combines the exact H1 effect and table invariant
from the same original run. With an initially resident caller, a self handshake
peer word and exclusion of the allocation ID from its actual rotation releases,
a true return leaves the key resident with one reference, places it in the
role-selected slot and uniquely publishes it at the former handshake index.
Other aliases and overwriting an unhashed object remain allowed.
`TablesSafe` bounds hashed owners, not every stored key or live slot; these
static premises are not yet reachable invariants.

The complete original `beginSession` now preserves `KeypairStoreBounded` on
normal return from a resident caller and a bounded entry store. Its allocation
cursor increases by exactly one on true and stays unchanged on false; the
candidate allocation ID was absent from the entry store. This follows through
the actual allocation, derivation writes, ordered rotation/releases and index
replacement. It needs no slot-freshness, self peer-word, table-safety or readiness
premise. The new key can still be erased by a rotation alias; final residency,
completion and reachable boundedness are not claimed.

The actual finite `pids.mapM beginSession` sequence now has unconditional
observation erasure, including errors. On normal return from an initial device
and bounded store, actual entry snapshots supply every successful allocation ID;
those IDs are exactly the consecutive range starting at the entry cursor and
are pairwise distinct. Each call entry retains store boundedness and candidate
freshness; the final cursor advances by the number of true results. Input peer
order and result length are preserved. Caller residency is derived from each
normal original run's first peer read, so no all-callers-resident premise or
preservation frame is needed. Calls are consecutive, with no interleaved
handshake installation; stopped runs retain their original error, not a partial
observation list. This is not retained-key lifetime or final residency.

The remaining charter core is reachable hashed-table uniqueness and owner-object/
peer-word residency at actual lookup cuts through driver entry points. Outer
`peerRemove`/`peerRemoveAll` table closure awaits the documented six-family
decision; no workaround copies that layer. Data ingress/workers also have
uncovered paths whose shared-frame overlap needs its own inventory before work.
[AGENT 2026-10-15] Treat full reference/slot lifetimes, broader record layouts
and a complete corpus-runner witness as supporting extensions, not separate H2
deliverables; prioritize the actual driver invariant and lookup identity clauses.

## H3 — Endpoint roaming

[AGENT 2026-10-14] “Endpoint changes only” means remote roaming:
family, address, port and IPv6 scope. Local source caches legitimately change
during routing/clearing, and `endpoint_eq` ignores flowinfo. Full-record
get-after-set is not claimed; `n1_flowinfo_only.json` exercises the distinction.

Source conversion and original endpoint setters are checked. Authentication
requires actual consume/AEAD evidence, not tag endpoints or MAC admission alone.
The outer source address is not an AEAD input. Data roaming occurs before later
inner-packet checks; these contracts do not assert delivery.

For a CRYPTED publication, the decrypt publication cut retains actual AEAD
plaintext and historical key provenance before the original callback; dead
publications do not assert plaintext provenance. The first-poll endpoint cut
includes the original budget and an actual true counter-check result, not a
proved counter-window invariant. Their join is from the same execution
and conditional on matching the actual packet identity. It neither supplies a
general queue invariant nor assumes packet-peer/key-owner equality. Softirq and
stack callbacks remain arbitrary; there is no final endpoint or scheduler claim.

For response-kind packets, exact source and decorated-observation equations
connect the full original caller to the actual pre-setter cut. A missing cut selects a
pure suffix; a present cut invokes the setter immediately and retains session,
timer, keepalive, statistics and release continuations. For a present cut on
normal full return, the contract derives actual under-load/MAC admission,
separately recorded owner/reference,
same-entry lookup, both DH checks, exact derived AEAD key/AAD, empty plaintext,
and consumer state recheck/commit. Cutting before the setter matters because
its later cache-reset read can fail after the endpoint write.

For initiation-kind packets, the corresponding exact caller factor and same-entry
decorated transcript reach the actual pre-setter cut. A present cut on normal
full return derives MAC/under-load admission, both actual AEAD results with
their exact derived keys and associated data, first-match public-key lookup
and bounded reference acquisition, the supplying precomputed-DH peer read,
the timestamp's `memcmp` ordering, the wrapped signed flood comparison, and
the committed initiation fields and consumption-clock update. It assumes
neither fixed plaintext lengths nor coherence between the table key and the
resident peer's stored remote static key. Original failed-reference puts,
rejection/error paths, response send, timers, statistics and final release
remain in the exact source equation.

A separate inspection now retains both handshake certificates through failed
continuations. It runs the actual prefix once, then the suffix from that exact
concrete successor, returning both projected outcomes at its unchanged entry.
First-component equality with the original prefix excludes a vacuous certificate;
second-component equality with inspection of the full original caller retains
its exact success or error. A prefix error is the full-call error; a no-cut
prefix completes through its pure suffix; a present cut retains authentication
facts even if the setter or later continuation fails. Error outcomes have no
final state. This is total inspection and erasure of inspection data, not
operational receiver execution or a guarantee that the endpoint write completes.

General queue provenance, netlink/whole-run caller exclusion and final endpoint
preservation remain open. Forged crypted packets in arbitrary states are not
accepted-run findings. Exact consume transcripts were chosen over a larger
crypto-dataflow frame layer; neither handshake caller needed new shared variants.

## H4 — Configuration semantics

[AGENT 2026-10-15] Clarify the charter's “allowed-IP removal flag” for the
pinned Linux 6.12.110. There is no per-entry allowed-IP flag: its UAPI
(`include/uapi/linux/wireguard.h:188–194`) lists family, address and CIDR,
and `netlink.c:329–355` only validates and inserts. The earlier
[W1/W2 design note, section 2.1](2026-10-06-w1-w2-netlink.md) already records
that `WGALLOWEDIP_A_FLAGS` does not exist in this version. Supported removal
semantics use peer `REMOVE_ME`/`REPLACE_ALLOWEDIPS` and device `REPLACE_PEERS`.
Those obligations, insertion/ownership transfer and effective readback remain
in scope; no per-prefix removal behavior is invented. Independent source
review confirmed this statement/version correction, not a mirror omission
or an accepted-run finding.

[AGENT 2026-10-14] Get-after-set means the effective configuration: private-key
clamping, allowed-IP masking, an allocated zero port and ignored flowinfo follow
the C's operations. Set is not transactional: earlier updates survive a later
parse error. The claims retain those outcomes rather than asserting raw-input
identity or rollback.

Checked leaves include validation/flag errors, absent remove/update-only and
self-key no-ops, removal precedence, identity and cookie precomputation, peer
scalars and expiry. The bounded public readback composes scalar set with the
original getter, including a later malformed entry: one resident peer on a
stopped device, a positive reference count with its temporary increment below
2^31, matching public-key and interface selection, no allowed IPs, sufficient
chunk room, and idle socket 7 with an empty queue. A fixed peer dump needs at
least 168 bytes; the complete getter additionally budgets device and nest
overhead. General multipart dump composition is open.

Port effects distinguish stopped devices, existing creating namespaces,
unchanged ports, nonzero replacement and zero-port allocation. Supplied-record
zero-port return/collision contracts retain their explicit draw assumptions.
An occupied first recorded candidate is an outside-domain stop, not ordinary
bind failure or proved retry. Bind failure retains preceding source/cache
clears; equal outer-port requests still increment generation. Fwmark effects
preserve remote destinations while clearing source/cache fields; reset
timestamps remain existential, including duplicate-list effects.
Private-key installation composes identity/cookie keys with ordered per-peer
precomputation, expiry and optional staged sending; full outer effects cover
the noncolliding request. Normal-return effects are not completion guarantees.
Existential expiry timestamps and actual reset-clock observations remain
separate contracts. The unchanged-key arm compares raw requested bytes with
stored clamped bytes.

[AGENT 2026-10-15] Compose private-key updates from a baseline after optional
self-peer removal: removal may flush other peers’ work under the old identity,
so an unrestricted surviving-peer frame against request-entry state would be
false. Prove the key-only block before composing later peer attributes.

Allowed-IP removal has total contracts under supplied `RemovalEffect` witnesses
and normal converses deriving those witnesses from an initially resident named
peer under `NodePairs` (every resident node has two child slots). This is a static representation condition, not proved
reachable trie validity, ownership or acyclicity. Peer death removes list/public
identity membership and sets deadness. Live-key removal admits aliases under
multiplicity-aware release budgets, positive peer references/count and empty
send/clear work queues. The outer total removal still takes a supplied
`RemovalEffect`; the after-death contract additionally requires initial deadness.
The final release may retain a dead peer when references remain. The normal
converse does not import these totality premises.

The empty-list REPLACE_ALLOWEDIPS device request now also derives its removal
witness from the actual normal execution, under initial `NodePairs` and a stopped
device. Lookup matching/residency, positive reference and its increment bound
remain explicit. The exact final effect retains generation, lookup acquisition,
ordered removal, balanced release and sequence change; the peer remains with an
empty allowed-IP list and its original reference count/identity, and processed
nodes are absent or unowned. No supplied removal run, root-only restriction or
global trie invariant is assumed. This extends the earlier witness-based total
claim with a normal-return converse; arbitrary structures are not asserted to
complete. The two new source-composition files add no frames or variants.

The normal full single-peer removal contract now derives both the structural
removal and ordered clear effects from the same actual run. Its premises are
initial residency, `NodePairs`, positive peer reference/device counts and empty
send/clear queues. It takes neither a supplied `RemovalEffect` nor `ClearReady`;
these normal effects do not promise completion.

A changed private-key-only request also has an exact normal collision effect.
The generated public key must select the named resident peer; its reference
count is positive and its temporary increment below 2^31. The request retains
the same node-shape, positive device-count and empty-queue conditions, with
matching device selection. Lookup acquisition and the immediate caller put
remain two ordered store writes, restoring the original reference count before
removal without assuming structural map equality. The resulting removal witness
and live-key cleanup are followed by identity/cookie/per-peer installation over
the actual post-removal baseline, including that baseline's staged-send test
and peer list. Normal outer return is zero. Final removal may erase the peer
or retain it dead when references remain; no aggregate clock provenance is
inferred from existential timestamps.

The actual `setPeerCmd` REMOVE_ME path now derives lookup acquisition, full
removal and the caller’s final release in their original order. Initial public
key, valid flags containing REMOVE_ME, supported protocol, first lookup match,
resident positive reference below the increment bound, `NodePairs`, positive
device count and empty send/clear queues are explicit. Later PSK, endpoint,
allowed-IP and keepalive attributes are unrestricted because their installation
is bypassed. Invalid flags/protocol are still rejected before removal. The
intermediate reference count is the original count; final erasure occurs exactly
when it was one, otherwise the surviving count is one less. The exact acquired
map insertion is retained, with no structural map-equality shortcut. A singleton
original `wgSetDevice` request carries this effect after interface selection and
the generation increment. Neither theorem assumes a supplied removal/clear run
or promises completion with queued work. No new frames or shared variants were
needed. The four new files separate the effect model and its consequences from
peer-command and device-request source composition.

Valid IPv4/IPv6 insertion into the selected empty root now has exact normal
allocation-failure and success effects. Both increment the sequence; success
retains allocation, peer-list append, parent and root writes in order. The cursor
may overwrite an existing node: no freshness or global topology is assumed.
Composing the actual setter with the actual peer dump reads back one masked,
fixed-width serialized prefix on success and fixed attributes without an
`allowed_ips` attribute after `-ENOMEM`. The named peer’s allowed-IP list is
initially empty; cursor freshness, zero-or-incremented matching sequence and
sufficient room are explicit. Source exceptions remain exceptions. This is
peer-dump scope, not outer socket/multipart or ownership coverage.

`AllowedInsertFrames.hiddenAlloc_sameKernel_node_spec_variant` is one local,
cited variant of campaign 1’s `Keypairs/OrdinaryHot.hiddenAlloc_sameKernel`;
importing that shared module exposed the inherited counter-refinement failure.
It preserves the original allocation loop and reuses C2 hidden-read support.
No existing shared lemma was changed or deferred six-family variant copied.

Exact transfer of an existing root leaf now returns zero totally under its
resident-node/destination and matching raw address/CIDR premises. The original
sequence increment, node-owner write, global list filtering and destination
append remain ordered. Stored address, prefix fields, parent/children, roots and
allocation cursor are retained. Arbitrary prior owners, duplicate list entries
and same-peer reassignment are allowed; no allocation or live-reference premise
is needed. The source factor preserves the untouched fallback branches.

A total paired readback composes the actual setter, donor dump and destination
dump, threading the real buffer/context. Here the node’s old owner is the
distinct resident donor, its list filters to empty (it may already be empty),
and the destination list starts empty. The donor emits fixed attributes; the
destination emits the stored masked prefix. The donor dump resets the allowed-IP
cursor and sequence, preserving other context fields, so no initial sequence
premise is needed. Initial cursor freshness and sufficient room are explicit,
and room consumption is exact. This remains root-leaf and peer-serialization
scope; all six new modules are substantive effects/source connections, without
new structural frames.

The cancelled-nest finding below is internal accounting, not a demonstrated
output mismatch. Total collision completion, queued-work removal, remove-all's
two-pass ordering, mixed attributes, global ownership and general getter round
trips remain open. No deferred shared-frame family was copied for these effects.

## H5 — Termination and progress

The literal no-pending-at-completion claim is historically refuted on this
branch by the accepted constructed batch-backlog witness below. The remaining
proofs distinguish original executions, generic worker laws and total
inspections. Probing an activation does not establish successful execution after
detachment; scheduler claims retain actual dispatch/resumption, NAPI and
caller-stack busy/idle/error branches. Nested callback refill remains an
obstacle to the old queue-occupancy bound.

The recorded cut proof derives its budget before ambient stripping and includes
the final empty/non-cut observation. Prefix-only allocation acceptance gives
total return; allocation rejection keeps its exact original stop. Original
send/clear flush effects erase one matching queue occurrence, allow duplicates
and retain final reference release, including peer deletion.

The whole-drain audit has unconditional exact correspondence with the original
4096-turn drain, preserving selection priority, hidden/placeholder behavior,
all errors and successful final state. It is an inspection at unchanged entry,
with the original outcome inside its datum. Below 4096 initial queued items,
actual selector membership and original flush effects bound loop turns begun
by count+one and exclude only the drain's own exhaustion. Selector/worker errors
are tagged by their actual call, not their text, and have no final-state field.
Normal completion with `upTo = none`, under the stated resident-device and
queue-count entry premises, leaves both queues empty; requested-clear completion
may leave other work. Exactly 4096 removals leave no extra turn to
observe empty queues: this is a source boundary, not an accepted witness.

The original modular-exponentiation loop has a finite evaluator with sufficient
fuel `e + 1`, proved by its checked fixed-point equation and induction. Zero
exponent and zero modulus preserve the original behavior: it returns 1 at
exponent zero even modulo 1, so unrestricted equality with stock `Nat.powMod`
would be a statement artefact. This is local operational adequacy, not an
algebraic, compiler or whole-run theorem.

Whole-worker record decrease, full operation-end coverage, detached-activation
progress and global termination remain open. No successful drain/dispatch or
complete scheduler run is inferred from total inspection.

The original receive poll now has an exact phase audit, including all prefix
and completion errors. With requested budget at most `MAX_QUEUED_PACKETS + 1`,
a normally returned loop prefix reaches its queue-test stop or its budget, so
the original finish-time exhaustion guard is false. Each continued iteration
increments the local count; arbitrary callback effects need no queue-preservation
premise. The queue-test stop includes an uncrypted head, not just an empty queue.
Zero budget takes the original early return; normal positive-budget completion
returns less than budget. The original unsupported repoll remains. Counts cover
cleanup-completed iterations, not callback/internal work; inspection retains a
historical finish cut and does not promise successful poll or callback completion.

## H6 — Timer discipline

Local contracts cover the original arm/delete guards and all seven concrete
arming sites, exact wrapped caller-read-plus-delay equations, traversal/session/
data/handshake hooks, and jitter below 83. Recorded arming uses the actual caller
read and arm record; arm-record mode may still permit placeholders. The separate
finite supplied-record jitter success/exhaustion claims require contiguous
rejected/accepted records and exclude ambient interleavings/placeholders. No
distribution claim is made.

Persistent keepalive remains conditional on its interval and running/live
guards. A final timer value alone does not prove an arm event occurred.
`createDataDone` invokes traversal once per encrypted item/list before its
per-packet send loop (`Data.lean:181–194`, C `send.c:242–260`), not once per
individual packet or necessarily a successful transmission. Zero-key firing
queues asynchronous clearing; it does not immediately prove key erasure.

The exact original timer/send pair starts with a resident device and empty
send queue. Successful selection derives the same peer, retry eligibility,
entry attempts at most 18, fresh enqueue/reference acquisition and timer detach.
The callback increments attempts; the worker preserves that count, releases the
acquired reference and leaves an empty queue and false pending flag. This is
not a proof of global reference ownership or network transmission.

Conditional rearming uses the actual before-arm state, its running/live and
arm-record conditions, actual caller read and bounded jitter. Exact expiry
survives retained release and section stop; the clock-gap conclusion stays at
its established pre-release cut. Consecutive successful pairs use adjacent
actual states. When all select the same initially resident peer, attempts grow
by their length and a nonempty sequence is bounded by 19 from zero. This
excludes 20 such successful pairs, not a twentieth timer callback. An empty
sequence preserves the whole snapshot.

The incoming response caller now has exact source and decorated-observation
correspondence, retaining errors and the unchanged continuation. On normal full
return, a present response cut records the actual session entry, returned Bool
and H1 `SessionEffect`. The session-derived hook is invoked exactly when that
Bool is true; that case derives the allocation-counter increment and a resident
live peer without an initial readiness or liveness premise. Running-device and
arm-record conditions at the actual hook entry give the wrapped zero-key expiry
from its caller read and `clockGap` immediately after the hook. Hook invocation
is distinct from a guarded arm. Rejected normal callers may have no cut; later
caller failure does not retain prefix evidence in this returned observer, and
no final caller expiry preservation is claimed.

The outgoing `sendHandshakeResponse` now has the matching exact source and
transcript contract. Its cut retains the actual MAC-added message and session
result, using the outgoing `respSessionBegun` decision. Response-creation
rejection yields no cut; a present cut records true or false session completion,
with the hook reached exactly on true. The same conditional recorded-arm facts
hold at that hook. The later traversal/authenticated-send hooks, second clock
and last-sent write, and socket send remain in the original continuation.
No transmission, final expiry or retained failed-call cut is claimed.

The original `createDataDone` now has an exact decorated execution, including
errors. On normal full return its packet IDs retain input order and duplicates;
actual successful non-keepalive sends determine whether the data-sent hook is
invoked. Traversal precedes the entire list, including an empty list. Each hook
carries its actual before/after snapshots and recorded clock path. Running/live,
recorded-mode and interval/pending conditions at that hook give exact wrapped
expiry; data-sent also gives bounded jitter. Hook invocation is distinct from
arming. Authenticated-sent deletion, loop markers and `keepKeyFresh` execute
unchanged. No transmission, final-expiry preservation or failed-call certificate
retention is claimed. All three new modules contain data, effects and source
connections; no structural frame was added.

The original `consumeDataDone` now has an exact decorated execution preserving
its optional packet result and all errors. On normal full return, traversal is
observed at its actual cut and the data-received hook is invoked exactly for a
nonzero packet length. The receipt effect distinguishes the pending timer,
running device and live peer branches, including the request for another
keepalive. Its recorded-arm conclusion gives the exact wrapped expiry at the
hook cut. Endpoint update, confirmation, staged sends and key refresh remain
the original prelude; the original packet validation and routing suffix remain
unchanged. This accepts a raw packet argument and establishes timer discipline,
not authentication or delivery. It does not retain cuts after a later failure
or preserve expiry through the remaining caller. The three new modules contain
observations, source correspondence and claims; no structural frames were added.

Complete traversal caller coverage, scheduler retry episodes and whole-run
arm-site/session counting remain open. The give-up path also arms
zero-key material; covering both session-derived hooks cannot prove once-per-session.
No H6 mirror mismatch has been established.

## Findings and mirror requests

All requests are in the [mirror-team document](2026-10-14-campaign-2-mirror-requests.md).
The mirror and kernel were not edited. No finding has been classified as a
kernel defect or sent upstream.

| Finding | Evidence and limit | Status / ranked change |
| --- | --- | --- |
| H5 batch backlog | Kernel-checked accepted constructed fixture trace, plus separate replay summary. Not a captured Linux run. | Historical over `de62c9d`; main `9db558b` adds the completion guard. Carry and corrected-refusal proof remain pending. H5 request 1, altitude-preserving. |
| H5 nested queue refill | Evaluated initialized prefix and source review; operation 4 reaches the worker occupancy-budget invariant, with later suffix incomplete. Not an accepted complete trace or kernel-proved prefix. | H5 request 2: callback-aware activation bound, altitude-preserving. |
| H4 dump cancellation | Accepted getter and kernel-checked internal room 3720 versus source-derived C room 3724. Concrete empty-list case; dead-cursor extension is inspection only. No demonstrated compared-output difference. | H4 request 1 (document request 3): restore pre-nest cancellation snapshot, altitude-preserving. |

Other local alias examples, the 4096-turn boundary and statement-domain
qualifications are not accepted-run findings. H1, H2, H3 and H6 have no ranked
mirror-change request at this checkpoint.

## Validation, effort and trust limitations

All headline declarations use only `propext`, `Classical.choice` and
`Quot.sound`; structural/token checks pass. Source factoring, ordered effects,
WP composition and finite induction were used without changing mirror
definitions. Ordinary elaboration/normalization failures were corrected;
their detailed iterations remain in commit history, not duplicated here.

Each checkpoint below passed its scoped build, standard-axiom checks, fresh
stock kernel replay (exit 0). Independent review has passed through the H6
receive-data increment; the new H4 REMOVE_ME and replacement-converse increments await independent review.
Counts record the check at
that increment, not the current number of declarations. Earlier H1 confirmation
had 140 build jobs/20 headlines; H3 response 59 jobs; H2 coherence 206 jobs;
H5 drain 196 jobs/32 headlines plus four source equations. Earlier H4/H6 checks
remain recorded in their commits, and affected shared C2 changes were rechecked.

| Increment | Build jobs | Headlines + support checked | Corrected Lean drafts |
| --- | ---: | ---: | ---: |
| H6 incoming response | 207 | 36 + 4 | 5 |
| H4 removal/collision | 185 | 66 + 5 | 5 |
| H3 initiation | 73 | 10 + 4 | 19 |
| H2 session allocation | 209 | 49 + 7 | 1 |
| H6 outgoing response | 210 | 37 + 4 | 3 |
| H3 failure-retaining inspection | 76 | 12 + 7 | 2 |
| H2 allocation sequence | 212 | 50 + 6 | 4 |
| H4 insertion/readback | 190 | 68 + 11 | 14 |
| H5 receive-poll bound | 210 | 33 + 15 | 10 |
| H6 data completion | 213 | 38 + 5 | 9 |
| H4 root transfer/readback | 196 | 70 + 8 | 5 |
| H2 successful lookup | 213 | 51 + 3 | 1 |
| H6 receive-data timers | 216 | 39 + 3 | 4 |
| H4 REMOVE_ME request | 200 | 72 + 6 | 9 |
| H4 replacement converse | 202 | 73 + 3 | 3 |

These were ordinary source/elaboration corrections, not infrastructure retries.
Failed recovery declarations containing `sorryAx` were never accepted. H3
initiation's count includes one diagnostic build; H4 insertion includes the
avoided inherited counter import and one deterministic elaboration-limit failure.
H3 inspection had two prototype failures and no implementation failures; H2
sequence had two of each; H5 poll had two prototype/eight implementation failures.
H6 data completion had seven prototype/two implementation failures plus one
JavaScript typo before Lean launched. H4 root transfer had one prototype/four
implementation failures, including two broad simplifier-limit failures resolved
by exact source factoring. H2 lookup had one prototype tactic-availability
failure and no implementation failures. H6 receive-data timers had two prototype
and two implementation normalization failures. H4 REMOVE_ME had one pure-effect,
four peer-source and four device-wrapper draft failures, including one diagnostic
build and three simplifier-limit failures. The wrapper initially retained the
DeviceRef default name alongside an index; using the existing index-only selector
corrected that statement-constructor mistake without changing limits or the mirror.
Its preceding bounded prototype passed on the first invocation. The replacement
converse had two constant-normalization draft failures and one explicit-sequence
projection mismatch; no limit failure or retry. Successful outputs were reused when only
wrapped/zero-axiom output parsing needed correction; no resource limit increased.

Review dispositions: H5 drain and H2 sequence made source correspondence
unconditional and kept bounds only on effects; H3 initiation distinguished
`memcmp` replay ordering from signed wrapping clocks; H4 readback clarified the
peer’s allowed-IP list; H4 transfer clarified that only the allowed-IP cursor
and sequence reset. All findings were fixed. H5 drain's staged EOF whitespace
was corrected in the next commit. Both pre-adjustment and changed-interface H2
sequence replays passed; this was source-driven revalidation, not a retry.
The six-target scoped build passes together (393 jobs), with existing unused-simp
and deprecated-tactic warnings. Combined inspection covers all 228 headlines. This does **not**
constitute a passing full gate.

The full gate was last actually run at `69f988a` and **failed** in inherited
`WG/CounterWindow/Refinement.lean` and `WG/ReplayWindow/Counterexamples.lean`
(counter operands and index-owner carries). Campaign 1 owns those repairs.
No existing shared lemma was edited.

**Exactly one infrastructure rerun**, at `84355d1`: a combined import overlapped
an active rebuild and found `ReceiveFrames.olean` absent. One retry after
confirmed build completion passed. Source corrections and parsing the same
wrapped axiom output are not infrastructure retries. There have been no memory
cap hits, cap increases, guest runs or guest timeouts.

A bounded read-only trial kernel-checked one original
`curve25519 (List.replicate 32 17) basePoint` equation through the finite
evaluator bridge (`decide +kernel`, about 0.334 s, standard axioms). Candidate
bytes from ordinary evaluation were not proof. The **single reduction trial of
`executeTrace QueueRefill.concreteTrace` failed**, exit 1, at stock simplifier
step exhaustion, using the checked original-pow rewrite. This was capped stdin
with 32 threads, unchanged limits and a 120-second trial budget. Its
failed recovery declaration printed `sorryAx`; no theorem or source file was
obtained or committed. There was no retry, timeout, limit increase or rebuild.
This does not show the target equation false or establish full-prefix throughput.

Stock trust-surface annotations are recorded explicitly: `repeatM` uses
`implemented_by repeatM.erased`, and stock `Nat.powMod` has an external
implementation annotation. The finite proof uses logical definitions, a checked
fixed-point equation and induction, not those executable overrides as oracles.
No project axiom or forbidden trusted-code declaration was added.

Reproduce scoped validation with the six targets (default memory cap unchanged):

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build \
  Leanux.Proofs.WG.Noise.Statements Leanux.Proofs.WG.Index.Statements \
  Leanux.Proofs.WG.Roaming.Statements Leanux.Proofs.WG.Config.Statements \
  Leanux.Proofs.WG.Progress.Statements Leanux.Proofs.WG.TimerDiscipline.Statements
# Print every headline's axioms; inspect that only the three standard axioms occur:
python3 - <<'PY' | LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake env lean --stdin
from pathlib import Path
import re
areas = ['Noise', 'Index', 'Roaming', 'Config', 'Progress', 'TimerDiscipline']
for area in areas:
    print(f'import Leanux.Proofs.WG.{area}.Statements')
for area in areas:
    source = (Path('Leanux/Proofs/WG') / area / 'Statements.lean').read_text()
    namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
    for name in re.findall(r'^theorem (\w+)', source, re.M):
        print(f'#print axioms {namespace}.{name}')
PY
# Replay each module separately; leanchecker --fresh accepts one module:
for area in Noise Index Roaming Config Progress TimerDiscipline; do
  LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake env leanchecker --fresh "Leanux.Proofs.WG.$area.Statements" || exit $?
done
# Full gate: expected inherited failure, not reported as a scoped pass:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The gate already supplies the headline discovery/axiom-check procedure; no
additional audit infrastructure was introduced. After the split lands by paste,
retype claims and delete structural frames that the new types make unnecessary.
