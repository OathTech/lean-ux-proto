# WireGuard proof campaign 2

## Progress

**Resumed for state-split preparation, 2026-10-15.** Work remains on
`proofs/campaign-2` over mirror `de62c9d`. Main has since advanced to the
representation batch at `cb2348e`; this checkpoint is **lagging main**. No merge
or push has been performed during this resumption. None of H1–H6 is complete.

[USER 2026-10-15] Resume before the split lands. Read the design on
`task/state-split`, factor claims over a WireGuard-only projection, separate
frames, then continue H2 and the remaining charter. Delete frames made trivial
or unstatable by the eventual new types; retype the substantive claims. No
shared-layer edits, merge or push. This supersedes the earlier pause pending
landing, whose closed checkpoint was `aeece72`.

[AGENT 2026-10-15] Use a real data projection (`Campaign2/View`) and an explicit
execution connection (`Campaign2/Bridge`). The view contains WireGuard state
and a separately named ambient context, with no task, file, pipe, epoll or
seccomp stores. Contracts quantify **every concrete realization**, keeping
partial correctness, total return and exact stops distinct. Clock/prefix
observations execute the original composites on a copy of the same entry;
checked erasure equations retain the original result, final state and errors.
No independent existential projected runs are spliced together.

| Result | Existing mathematical checkpoint | Factoring / remaining mathematics |
| --- | --- | --- |
| H1 Noise | 18 state/slot, ordered-clear, rotation/confirmation and full session-effect contracts | Public projection complete; exact normal session composition and static rotation/release totality are checked. Whole-call edge coverage, session totality, exposed derivation-clock provenance and lifetime confirmation remain open. |
| H2 Index | 48 contracts, including lifecycle boundaries, handshake reception/sending, staged/keepalive sending, queued clearing, worker/timer dispatch, original workqueue draining/post-death removal, and successful session publication coherence | Public projection complete: 14 total contracts, 32 normal-return contracts, 1 exact stop and 1 projected initializer theorem; reachable coherence, broader records and the corpus runner composition remain open. |
| H3 Roaming | 9 contracts, including decrypt publication, its same-execution first-poll endpoint connection, and exact response-caller authentication at the pre-setter cut | Public projection complete; first selected packet provenance is conditional on matching publication identity. Initiation, failed-call prefix retention, general queue provenance and complete caller coverage remain open. |
| H4 Configuration | 64 contracts, including normal removal/death converses under two-slot node shape, live-key removal with empty work queues, and the internal dump-accounting finding | Public projection and frame separation complete. Queued-work removal, private-key collision, mixed attributes, global ownership and general dump composition remain open. |
| H5 Progress | 30 contracts, including original exponentiation-loop finite evaluation, flush queue effects/count decrease, cut-loop budget adequacy, and the accepted batch-backlog counterexample | Public projection and frame separation complete; the recorded cut cannot exhaust its budget and normal selected flushes decrease queue count. Whole-worker record decrease, full loop coverage and probe/detach composition remain open. The backlog witness is historical over `de62c9d`: main's batch guard now addresses request 1. |
| H6 Timers | 35 timer/worker contracts, including consecutive original retry pairs, conditional recorded rearming and same-peer attempt counting | Public projection and frame separation complete; a successful pair from an empty send queue derives the retry bound, reference acquisition/release, final empty queue and cleared pending flag. Conditional rearming preserves the exact expiry through release and section stop; consecutive successful pairs selecting the same initial peer increase attempts by their length and are bounded by 19 from zero. Scheduler retry episodes and whole-run arming/session counts remain open. |

Projection/frame factoring completed at `69f988a` for all six results, preserving
all 153 existing headline names before new mathematics. The following H2 lifecycle/sender
and H6 dispatch/rearm increments, H3 publication/poll and response provenance, H5 cut-loop progress, H1 ordered clearing/rotation and H4 live-key removal bring the total to 204. No public statement directly names `World` or
`Kernel`.
The full proof gate remains failed in inherited campaign-1 counter-window and
index carries; those files have not been edited. Scoped validation does not
constitute a passing full gate. The report's earlier results concern their
recorded mirror commits, not the newer representation batch.

### Claims, frames and the split boundary

Paths below are under `Leanux/Proofs/WG/`; `.lean` is implicit. Public claims
remain the six result `Statements` modules. Their concrete source proofs are
connections to the current executable mirror, not replacement interpreters.

| Area | Data / claims / source connections | Separate frame support |
| --- | --- | --- |
| Common C2 | `Campaign2/View` is data-only; `Campaign2/Bridge` defines projection and universal execution contracts. | No shared campaign-1 layer is changed. |
| H1 | `Noise/Model`, `Statements`, `Slots`, `StateEdges`, `ConsumeEdges`, `ClearModel`, `ClearEffects`, `ClearSource`, `RotationModel`, `RotationEffects`, `RotationSource`, `SessionModel`, `SessionSource`; `Execution` holds the concrete monad connection; `AccessSource` holds accessor read/write contracts, reexported by `Basic`. | `KernelFrames`, `PeerFrames`, `SlotFrames`, `ClearFrames`, `RotationFrames`, `SessionFrames`. |
| H2 | `Index/View`, `TableModel`, `OwnerWordModel`, `AllocationModel`, `ReleaseModel`, `LifecycleModel` and pure release effects/bounds; `Statements`, `HandshakeClaims`, `OwnerUpdateClaims`, `LifecycleSource`, `LinkSource`, `SendSource`, `DispatchSource`, `ResponseSource`, `ConsumeSource`, `StagedSource`, `ReceiveOperations`, `ReceiveSource`, `ClearSource`, `TimerSource`, `FlushSource`, `SessionCoherenceModel`, `SessionCoherenceEffects`, `SessionCoherenceSource` and the other operation/source modules. | `IndexFieldFrames`, `OwnerFieldFrames`, `StoreFieldFrames`, `LifecycleFrames`, `NewlinkFrames`, `SendFrames`, `DispatchFrames`, `ResponseFrames`, `ConsumeFrames`, `StagedFrames`, `ReceiveFrames`, `ClearFrames`, `TimerFrames`, `FlushFrames`, `SessionCoherenceFrames`; the old `HandshakeFrames` and `OwnerFrames` paths are import-only reexports, not duplicated lemmas. |
| H3 | `Roaming/Model`, `View`, `Statements`, `EndpointClaims`, `EndpointSource`, `Authentication`, `PublicationModel`, `PublicationSource`, `PublicationClaims`, `PollEndpointModel`, `PollEndpointSource`, `PollEndpointClaims`, `ResponseModel`, `ResponseCryptoSource`, `ResponseConsumeSource`, `ResponseLookupSource`, `ResponseCallSource`, `ResponseCallClaims`. | `Roaming/Frames`, `PublicationFrames`, `PollEndpointFrames`; `Basic` reexports the endpoint source connection. The response increment needs no new frame support. |
| H4 | `Config/Model`, `AllowedRemovalModel`, `AllowedPairsModel`, `AllowedPairsEffects`, `AllowedRemovalConverseSource`, `AllowedRemovalConverseClaims`, `QuietModel`, `LiveRemovalModel`, `LiveRemovalSource`, `ClaimView`, `Statements`, `SourceClaims`, `ObservationBridge`, and existing substantive effect/source modules. | `ConcreteFrames` isolates six whole-kernel endpoint contracts; `OperationFrames` isolates seven generic helpers; `ReadbackFrames` retains socket/fixture preservation; `AllowedListFrames`, `AllowedRootFrames`, `AllowedRemovalFrames`, `AllowedPairsFrames`, `QuietFrames`, `LiveRemovalFrames`, `KeyFieldFrames` isolate within-WG preservation. |
| H5 | `Progress/Model`, `View`, `Statements`, `SourceClaims`, `ObservationBridge`; `ControlLaws` is generic state/error control and `ControlSource` connects it exactly to the original worker; the scheduler/source modules retain actual execution factors. `CutModel`, `CutSource` and `CutClaims` establish original cut-loop progress; `FlushQueueModel`, `FlushQueueSource` and `FlushQueueClaims` establish original flush effects and count decrease; `PowModel` and `PowSource` connect a finite evaluator to the original arithmetic loop. | `StackFrames` isolates caller-guard preservation; `CutFrames` isolates record/error-location preservation; `FlushQueueFrames` isolates queue preservation through worker bodies and release. Probe/filter/no-work contracts also establish outputs and remain substantive source claims. |
| H6 | `TimerDiscipline/Model`, `View`, `SendView`, `Statements`, `ObservationBridge`, `ObservationClaims`, `SourceClaims`, `SendDispatchModel`, `SendDispatchClaims`, `RetryDispatchModel`, `RetryDispatchClaims`, `RetryRearmModel`, `RetryRearmClaims`, `RetrySequenceModel`, `RetrySequenceClaims`, and `*Source` operational proofs. | `SourceFrames`, `RecordedFrames`, `RecordedJitterFrames`, `SectionFrames`, `SelectionFrames`, `RetryFrames`, `JitterFrames`, `InitiationFrames`, `InitiationPreservationFrames`, `SendCutFrames`, `SendPeerFrames`, `SendSocketFrames`, `SendBufferFrame`, `SendWorkerFrame`, `SendDispatchFrames`, `RetryDispatchFrames`, `RetryRearmFrames`, `WorkStateFrames`. |

A compound exact effect is not a disposable frame merely because its name
contains “frame”: mark/generation updates, cleared-peer accumulation, reference
decrements and dump/UDP payload results remain substantive claims. The seven
H4 dump/UDP helpers with arbitrary kernel predicates are concrete source
contracts that also establish outputs. After the mirror split, delete only
structural preservation made trivial or unstatable; retain and retype those
outputs and meaningful within-WG preservation. H6's reference-decrement proof
is therefore in `SendWorkerSource`, separate from send preservation.

H5 retains two runner findings, two generic worker laws, eighteen total
inspection contracts, two total original no-work contracts, one scheduler
agreement and two original recorded-cut progress contracts. Inspection totality is not underlying-operation success. The actual
dispatch and NAPI decorations erase to the original actions, with exact stops;
all branch observations retain their concrete intermediate executions. Generic
worker laws have an exact original-operation instance and make no claim that
arbitrary callbacks are WireGuard-local.

The final family pass moved 38 preservation helpers, 11 supporting definitions
and one exact model write/read equation without changing their text. Pure models
were separated only to avoid import cycles. Compound effects, index-changing
invariant proofs and release bounds remain claims. Independent read-only review
of the projected interfaces found no semantic defect. A new pure frame file's
namespace header initially failed compilation; correcting that header closed the
same declarations. This was a source correction, not an infrastructure retry.

Validation at the completed factoring checkpoint: all six public modules build
together (238 jobs). All 153 terminal declarations import together and their
printed axioms are a subset of `propext`, `Classical.choice`, `Quot.sound`.
Commands: `LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build` with all
six `Leanux.Proofs.WG.<Result>.Statements` targets; the same capped bundle runs
`lake env lean --stdin` for the complete headline axiom list and
`lake env leanchecker --fresh <module>` for replay. Fresh stock replay passed
for H2, H4 and H5 after the final family moves; H6 passed at `5085fd9` and is
unchanged since. The full
`LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate`
failed in inherited `ReplayWindow.Counterexamples` and `CounterWindow.Refinement`;
its forbidden-token and import/root/default-target checks passed. No cap hit,
guest run or infrastructure rerun. Mirror and shared proof files are unchanged.

[USER 2026-10-15] The index-lookup fix has landed at `de62c9d`; merge main
into the campaign branch, carry the index frames and permit H2 to start.
Guest slots default to 16; concurrent capped runs are allowed. No merge to
main or push.

[USER 2026-10-15] “Pay the frames” means campaign 2's own results. Existing
shared lemmas remain campaign 1's. Any necessary local replacements belong
inside the result directory, named as variants of the shared lemma; report
rather than copy a layer if more than a few would be needed. Scoped validation
continues with inherited breakage recorded. The existing standalone C2 contracts
suffice for this carry, so no shared-layer copy is needed.

[AGENT 2026-10-15] Carry the local Noise, expiry and staged-send contracts
through the embedded-owner representation. The internal expiry-prefix total
contract is now a normal-completion contract: a NULL handshake peer word
stops before clearing. The public successful-expiry statement is unchanged;
its assumed original run establishes prefix success. This is a statement-domain
correction for the landed mirror, not a new mirror finding. Index removal uses
owner identity even when the owner's peer word is NULL. No shared definition
or lemma has been edited. Independent read-only review found no correctness
issue in the six-file carry. The queue-refill reproduction still reports its
expected operation-4 invariant failure. No cap hit or infrastructure rerun.

[USER 2026-10-14] Work H1, H3 and H4 before H2; start H2 only after the
index-lookup fix lands and its landing is relayed. Merge other main landings
into the campaign branch and carry proofs; never integrate into main or push.

[USER 2026-10-14] Put any requests for the mirror team in a document in this
tree and notify the user. The first request is the
[batch-completion guard](2026-10-14-campaign-2-mirror-requests.md); the user has
been notified.

The initial full proof-target build failed in inherited
`WG/CounterWindow/Refinement.lean`: its execution equation still uses the
old counter-limit branch records. That shared repair belongs to campaign 1.
New result modules are checked independently until the shared carry lands;
this does not count as a passing full proof gate.

## H1 — Noise session state machine (in progress)

[AGENT 2026-10-14] Start with a small peer/slot projection and exact original
operation contracts, then compose caller coverage. Keep normal endpoints
separate from event coverage and successful initialized executions. No existing
shared lemma or definition is edited.

Source qualifications to retain in the statements: create/consume initiation
can restart from any prior state. Initiator rotation with an existing `next`
demotes that pending key to `previous` and puts the old current; without a
pending key it demotes current. These are the C's explicit arms, not findings
against the mirror. The original charter wording “as the code implements them”
requires all of them. Confirmation's once-per-lifetime property will require
allocation/slot provenance, beyond an immediate second-call result.

Architecture after factoring: `Model` defines the slot projection, `Execution`
the concrete normal-execution connection, and `AccessSource` the accessor
contracts reexported by `Basic`; public `Statements` use the common snapshot.
`Slots` proves all rotation arms, confirmation, clearing and exact handshake zeroing; `KernelFrames` and `PeerFrames` isolate hidden-input,
allocation and index-operation frames; `StateEdges` and `ConsumeEdges` prove
tag endpoints. The initial eleven terminal statements cover these local contracts.
The consume statements establish the returned peer's tag, not failed-prefix
framing or authentication provenance. `beginSession`'s tag contract is checked;
its complete normal allocation/rotation effect is now covered below.

General original keypair clearing now has two additional projected contracts.
For a resident entry peer, normal completion derives `ClearRun`: each next,
previous and current slot is read from the evolving state, cleared before its
put, and followed by the exact table-unhash, reference-decrement and possible
store-erasure writes. The final peer has all three slots empty and its other
fields unchanged. No operational readiness witness is assumed by this theorem;
actual successful puts establish their resident/non-NULL/positive-count needs.

A separate total-return theorem uses static `ClearReady`: each non-NULL key in
the three slots is resident, its peer word is non-NULL, and its reference count
covers its number of slot occurrences. Aliases are permitted, including a last
reference released at the last occurrence. No owner/peer equality, residency of
the peer named by that word, queue emptiness, upper reference bound or hidden
record premise is required. This is a local model contract, not a reachable
ownership theorem. `ClearModel` preserves the actual sequential maps;
`ClearSource` connects them to the unchanged original operation. `ClearEffects`
contains the substantive reference-budget argument and `ClearFrames` only
untouched-peer preservation. The same result is available for H4's live-key
removal dependency; workqueue flush and full collision removal remain open.

H1 now has 13 headlines and the campaign has 174. Capped full-parallel Noise
and Config builds passed (174 jobs), all 73 affected headline axiom checks use
only the three standard axioms, and separate fresh stock kernel replays passed
for both Statements modules. All 174 campaign headlines import and pass axiom
inspection together; gate token and import/root/default-target checks pass.
Independent review closed with no outstanding findings; the reference-budget
lemma was moved from Frames to Effects because it transforms a substantive
invariant. No cap failure, timeout, guest run or infrastructure rerun. The full
gate remains failed in unchanged inherited shared files. Reproduce with
`LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Noise.Statements Leanux.Proofs.WG.Config.Statements`
and separate capped `lake env leanchecker --fresh <module>` runs. No mirror
mismatch or additional mirror-team request arose from this increment.

Four further projected contracts derive exact rotation and confirmation effects
on normal return and prove total completion from static release budgets.
`RotationModel` records each original peer write and immediate put, preserving
paired writes and the source's order. Initiator rotation with next releases old
current then old previous; without next it releases old previous. Responder
rotation releases old next then old previous. Confirmation reads current from
the then-current peer, writes previous, releases old previous, then writes
current/next together. A mismatch returns false with the original Device.
`RotationSource` proves exact equality with the original operations, including
their branch records and errors, and derives the ordered relation from the
actual normal execution. `RotationEffects` constructs that relation from
`ClearReady` counts for precisely the released keys. `RotationFrames` contains
only key-store/readiness preservation through a peer-slot write.

These budgets allow aliases, including new/received identities. They do not
prove retained-slot residency. For example, let old next=current name one
resident key with one reference and a non-NULL peer word, old previous be empty,
and the new key be distinct, resident and an initiator. Rotation demotes next to
previous and then releases current, leaving previous naming the erased key.
Confirmation can similarly release old previous when it aliases the received
key. These are
local statement-boundary examples, not accepted-run mirror findings. The total
confirmation contract adds no received-key residency premise, because the
original operation does not dereference it.

H1 now has 17 headlines and the campaign 187. The capped full-parallel Noise
and Config build passed (181 jobs), all 17 Noise headline axiom checks use only
the three standard axioms, and fresh stock Noise kernel replay passed. Combined
import/axiom inspection of all 187 headlines and the gate's structural checks
passed. Independent review closed without findings. Ordinary source/elaboration
errors were corrected; no heartbeat exhaustion, cap failure, guest timeout or
infrastructure rerun in this increment. Reproduce with the preceding scoped
Noise/Config build command and capped fresh replay of `Noise.Statements`.
The full gate remains failed in the unchanged inherited files.

`SessionModel` and `SessionSource` now connect the full original `beginSession`
entry point to exact normal-return effects. A false return preserves the device
and allocation counter, including when allocation records were consumed. A true
return derives an accepted initial tag, live peer, non-NULL handshake peer word,
counter increment, allocation overwrite, role/remote-index assignment, both KDF
keys with validity and birthdate, handshake zeroing, ordered rotation/release and
replacement of the actually hashed handshake entry. The initial peer's residency
is the only peer premise; freshness, distinct slots and a successful-release
witness are not assumed. Aliasing may erase the allocated key before its identity
is installed in the final table, so store residency and lifetime coherence are
not concluded.

[AGENT 2026-10-15] Keep birthdate existential in this exact-effect milestone.
Its witness comes from the original derivation; no independently executed clock
probe is postulated. An exposed clock-read observation and total session success
remain separate obligations. `SessionFrames` holds counter and owner-word
preservation. Exact accessors and compound effects remain in Source: the review's
P3 placement question for `sessionPeer_read` was answered by its returned-peer
and residency equation, consistent with `Noise/AccessSource`, and a comment now
explains that distinction. Independent review closed with no outstanding findings.

H1 now has 18 headlines and the campaign 194. The capped full-parallel Noise and
Config build passed (220 jobs); all 18 Noise headlines and two exact suffix-source
equations use only standard axioms, and fresh Noise kernel replay passed. All
194 campaign headlines import and pass axiom inspection together; token and
import/root/default-target checks pass. Reproduce with
`LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Noise.Statements Leanux.Proofs.WG.Config.Statements`
and `capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Noise.Statements`.
Ordinary source/elaboration errors were corrected; no heartbeat timeout, cap
failure, guest timeout or infrastructure rerun. Full gate failure remains in
unchanged inherited files, last run at `69f988a`. No new mirror request or finding.

Expiry's remaining sending-key effect was already proved in H4's
`original_expiry_store_effects`, `original_expiry_keypair_fields` and
`original_expiry_clock_relation`: next/current sending validity, aliases,
handshake zero/unhash and the actual reset-clock provenance. H1 reuses those
checked normal-return contracts; no duplicate proof is needed.

Remaining H1 work: source-call coverage of owned edges through the runner;
session totality and an exposed derivation-clock observation; fresh-allocation
provenance for session installation and confirmation once per allocation lifetime.
The immediate second-call confirmation theorem is deliberately not presented
as the lifetime theorem. Slots are individually optional values, not a bound
of three on the entire store: outstanding packet references can retain keys.

The read-only source review found no new mirror/C discrepancy. It also
identified a necessary invariant boundary: an initiator rotation can free old
current before overwriting its slot, so live-slot coherence belongs at completed
rotation cuts, not every primitive assignment. No accepted-run counterexample
is claimed here.

Two whole-run architectures were reviewed: a source-call observer with exact
erasure and event-completeness equations, or direct structural execution
derivations with primitive silent rules. Neither may infer empty history merely
from equal endpoints. Campaign 1's existing replay-window projection omits
slots and handshake tags, so its whole-run theorem cannot discharge this work.
The local operational and WP composition variants are standalone because
importing the existing generic shared layer also imports the lagging refinement.

Effort: capped scoped elaboration iterations, an initial full-target build and
two full proof-gate runs. All full runs failed at inherited counter refinement;
the gate's token and import checks passed. The initial eight terminal statements
passed axiom inspection (only the three standard axioms) and stock kernel replay.
The expanded checkpoint's eleven H1 and five H3 statements pass scoped builds,
axiom inspection (only `propext`, `Classical.choice`, `Quot.sound`) and stock
kernel replay, run separately with `capped -- scripts/in-bundle lake env
leanchecker --fresh Leanux.Proofs.WG.Noise.Statements` and the corresponding
`Roaming.Statements` command. A combined `--fresh` invocation was rejected by
the checker because it accepts one module; the separate runs both exited zero.
The full proof gate remains failed as described above. No cap hit, mirror edit,
differential check or guest run.

Ranked mirror suggestions: none at this checkpoint.

## H2 — Session index uniqueness (in progress)

[AGENT 2026-10-15] Separate numeric-index uniqueness from embedded-owner
uniqueness, then prove exact contracts over the original operations before
composing reachable-state coherence. The landed representation keeps owner
identity in each table row and its optional peer word in the owner object.
The two are not interchangeable on arbitrary states.

[AGENT 2026-10-15] Clarify the charter's “no two live sessions, handshake or
keypair, share an index” as: within a device, no two simultaneously hashed
handshake/keypair entries own the same receiving index; lookup returns that
indexed owner and its acquired peer reference, or nothing. Unhashed objects
retained by references do not reserve their former index. This retains the
lookup-ownership meaning rather than asserting lifetime-wide numeric uniqueness.
In the C, `noise.c:131–139` unhashes before dropping the reference;
`peerlookup.c:192–197` unlinks without clearing the old numeric field, and
insertion at `peerlookup.c:119–163` tests currently hashed entries. Replacement
also unhashes the handshake while copying its index to the keypair. The mirror
has no local receiving-index field in `Keypair`: local ownership lives in
`Device.indexTable`; `remoteIndex` is the separate peer-supplied namespace.
This is a source-grounded statement clarification, not a mirror finding or an
accepted runner counterexample. Table uniqueness alone still does not establish
resident-owner, reference-lifetime or whole-driver reachable coherence.

The next lifetime boundary is stronger than `TablesSafe`: its allocation bound
covers hashed keypair owners, not every resident keypair or live slot.
`beginSession` allocates at `nextKeypairId` before rotation releases displaced
slots. Excluding a raw slot that aliases that fresh ID needs store/slot
coherence, alongside owner residency and reference obligations; table uniqueness
alone cannot establish it. This is an outstanding invariant dependency, not an
accepted-run counterexample or a mirror finding.

The first twenty terminal statements cover removal, the keypair-removal specialization,
handshake replacement, normally completed insertion, lookup owner/table
provenance, total matched-entry NULL/zero-reference/live lookup effects, and
recorded collision-prefix completion, a corpus-draw two-call instance and
bounded allocation freshness, three original handshake-operation numeric
uniqueness contracts, and total absent/disallowed lookup, plus exact keypair release and preservation
of allocation bounds, and three original handshake owner-uniqueness contracts. Removal and replacement return under device residency. Replacement
preserves numeric indices and every owner object's peer word; preserving owner
uniqueness additionally requires the destination keypair not already hashed.
Insertion first removes this owner's old row, then inserts a fresh numeric
index at the head, preserving both uniqueness properties. No unconditional
insertion-success claim is made for absent or exhausted draws. The landed
mirror has no `indexRemoveKeypair` declaration: its operation is now
`indexRemove (.keypair id)`, also used by `keypairPut` after a peer-word
dereference. The removal statement does not claim a NULL dereference succeeds.

`LookupSource` proves the original scan stops at the first equal numeric
index, including a disallowed kind; `Lookup` composes that scan with the
original reference-acquisition/store-back suffix. The general terminal lookup
postcondition says any returned owner comes from an initial row at the
requested index and allowed kind, and the table is unchanged. `PeerWords`
adds total contracts when the first matching row has a permitted kind and
a resident owner: a NULL word returns nothing; a resident zero-reference peer
returns nothing and stores NULL; a positive, bounded reference count returns
the owner and stored peer identity, increments the reference, then stores back
the word. The exact post-state retains the increment when handshake-owner and
referenced-peer identities alias. Missing objects and reference overflow are
excluded by explicit premises matching the original stops. These local effects
remain separate from reachable owner/peer coherence. `LookupMiss` also proves
that no first matching entry, or a disallowed kind on that first match, returns
nothing and leaves the entire device unchanged; lookup does not continue past
a disallowed equal-index entry.
`Collision` proves bucket walking tests exact numeric membership in the whole
table. `Insert` factors the original draw loop and proves freshness on normal
completion by induction over its budgeted iterations. `DrawRecords` proves
that any finite contiguous sequence of colliding four-byte draws followed by
a fresh draw completes the original insertion: the original record-derived
budget suffices, each collision yields to the next original iteration, and
the unused hidden-record suffix is preserved exactly. The collision premises
refer to the table after unhashing the inserting owner; repeated collisions
and arbitrary trailing records are allowed. Independent review found no
correctness issue and prompted the explicit “contiguous” qualification.
Interspersed ambient records, streams without a fresh draw, explicit branch-log
counting and the `s2_index_collision` runner instance remain open.

`CorpusDraws` instantiates two original insertions from an empty table with
`s2_index_collision`'s three steering values (0x0a0b0c0d twice, then
0x11223344), preserving an arbitrary unused suffix. This is local operation
composition: the actual runner has other operations between those insertions.
`Allocation` proves the original keypair allocator's exact normal effects,
copying its optional peer word and establishing freshness from explicit bounds
on resident and hashed keypair IDs. Both bounds are preserved. Their
initialization and preservation through all callers remain obligations.
Independent review found no correctness issue in these two increments.
The concrete composition initially failed kernel checking with deterministic
timeouts; factoring the generic two-call proof before applying concrete draws
resolved that elaboration problem. These were failed proof iterations, not
infrastructure outcomes or successful checks.

`HandshakeClaims` composes numeric uniqueness through original
`createInitiation`, `createResponse` and `beginSession`, including allocation,
slot rotation, displaced-key removals and owner replacement. These contracts
cover normal completion, including early returns; they do not characterize
stopped prefixes. Independent review found no correctness issue and confirmed
that numeric uniqueness needs no destination-owner freshness premise for
replacement: labels change while numbers remain fixed. These new result-local
index contracts do not edit or copy campaign 1's shared receive-state layer.

`Release` proves total original keypair release with a resident keypair,
positive reference count and non-NULL peer word. Its ordered state transformer
keeps both unhash operations on an immediate final release. `ReleaseEffects`
proves their net filtering effect, final-reference erasure, unchanged other
keypairs and preservation of both uniqueness predicates. `ReleaseBounds` keeps
the allocation cursor and both freshness bounds. These are two additional
terminal contracts. Non-NULL is sufficient for this mirror's dereference; no
peer-residency premise is silently inferred from it. Peer slots and packet
references are outside the contract. Independent read-only review found no
correctness defect in the exact operation, effects, bounds or terminal scope.
Proof elaboration initially failed on intermediate device equalities; explicit
substitution before the second dereference closed the same statement. These
were failed proof iterations, not infrastructure reruns.

`OwnerUpdateClaims`, `SessionOwners` and `OwnerCreation` establish embedded-owner
uniqueness through the three original handshake operations. The allocation
bound supplies the destination freshness needed by replacement; the designated
owner remains unhashed through key derivation, clearing and slot rotation.
The bound is retained after every normally completed call, including allocation
failure and early returns, so these three contracts compose across repeated
normal calls. Independent review first identified loss of the bound in the
weaker intermediate postcondition; the contract was strengthened before this
checkpoint. Review of the final composition found no correctness issue.
Unhashed does not imply resident or live: malformed slot aliases can release
the designated keypair while preserving these table predicates. Store/slot
safety, stopped prefixes and reachable owner-word coherence are explicitly
outside these contracts. The frames are new campaign-2 index predicates;
no campaign-1 lemma or shared layer was copied or edited.

`DrawExhaustion` proves exact original insertion rejection for a finite contiguous
stream consisting entirely of draws that collide after owner removal. The
record-derived budget includes the extra turn that reads the empty stream and
reports `no record left for index_draw`; `insertFinish` and budget exhaustion
are never reached. Empty input is covered. The hiddenPlaceholders flag is
unconstrained, but actual recordless placeholder execution is outside the
statement. This is expected rejection of incomplete input, not an accepted
runner trace or a nontermination finding. Since exceptions carry no World, the
terminal does not claim an observable post-error table or log. Independent
review found no correctness defect; its placeholder-mode wording correction
was applied. A failed axiom invocation named a nonexistent temporary file;
generating the inspection file from the terminal declarations corrected it.

`PeerRelease` adds exact original peer-put effects and allocation-bound
preservation. The last release filters all handshake-owner rows, charges the
staged packet count and erases the peer; other peers and the keypair store are
unchanged. No non-NULL handshake word premise is needed for removal by owner
identity. Both uniqueness predicates and both allocation bounds survive. The
original retirement of worker/timer identities executes, but the terminals
export device effects rather than a World frame. Independent read-only review
found no defect; dangling references from other objects remain outside scope.

`LifecycleModel` adds `View.TablesSafe`, which permits device absence and
requires numeric uniqueness, embedded-owner uniqueness and the hashed-keypair
allocation bound whenever a device exists. `LifecycleSource` projects the
original `Runner.initialKernel` core into an arbitrary observation: all fixture
flag combinations establish the invariant, without constructing a concrete run
or constraining unrelated observed context. Original `wgSetup` returns its
empty device and establishes the invariant without a precondition. Every normal
completion of original `wgDestruct` leaves no device, hence satisfies it. The
exact original destruction prefix is retained; its stopping behavior and
intermediate states are not proved safe by this endpoint result.
`LifecycleFrames` contains the one device-preservation lemma for dispatch-unit
retirement. No broad framing layer was copied.

The three lifecycle headlines bring H2 to 26. Independent read-only review
found no semantic issue; all prior 23 headlines are unchanged. The scoped Index
build passed (104 jobs), all 26 headline axiom checks passed, and fresh stock
kernel replay passed. A combined import/axiom inspection of all 156 campaign
headlines also passed with only the three standard axioms. Ordinary syntax and
monadic-association proof errors were corrected without weakening statements;
no infrastructure rerun or cap failure. The full gate's last run at `69f988a`
failed in the unchanged inherited modules, as recorded above.

`LinkSource` now composes the original `wgNewlink`, `wgCreate` and `wgDelete`.
Normal newlink and creation preserve the optional-device table invariant;
normal deletion leaves no device, including its already-absent return. Creation
uses original setup and newlink, and a normally returning negative newlink result
clears the device. Deletion retains its exact original prefix and uses the
original destruction endpoint. These contracts do not promise that missing
records or an early stop complete successfully, or preserve the invariant at
internal destruction cuts. `NewlinkFrames` holds three local initialization
frames and one fixed-count record-cut variant reusing campaign 2's existing
record-cut frame; no broad shared layer was copied.

These three headlines bring H2 to 29 and the campaign to 159. The scoped build
passed (152 jobs), all 29 H2 axiom checks and fresh stock kernel replay passed,
and the combined import/axiom inspection of all 159 headlines passed with only
the three standard axioms. The preceding 26 statements are unchanged; source
review found no semantic issue. No cap failure or infrastructure rerun. The
full gate remains the inherited failure recorded above, last run at `69f988a`.
Internal destruction preservation, all caller coverage, owner/peer-word coherence
and broader retry correspondence remain open.

[AGENT 2026-10-15] Strengthen the existing campaign-2 socket-send proof spine
once with an optional table/cursor observation paired with the optional initiation
peer observation. Handshake creation itself changes the table, so the broader
observation is restricted to the send spine; the existing `InitiationView` is
unchanged. `TimerDiscipline/SendView` is pure and imports no Index module. The
old send helpers follow by projection, preserving all nine old signatures and
the total getter's existing guarantee. This avoids copying a shared send layer.

`Index/SendSource` now proves original `sendHandshakeInitiation` and
`handshakeSendWorker` preserve `View.TablesSafe` on normal completion, including
early returns and a final peer release. Numeric and owner/bound creation facts
are combined on the same original execution. The worker needs no additional
resident-peer or retained-reference premise; final-reference removal filters
its handshake owner and preserves the invariant. `SendFrames` separately holds
socket, timer, peer-field and one small refcount kernel variant. Review moved
`indexRemove_tables` and `peerPut_tables` into `SendSource`: those operations
change the table, so their invariant claims are substantive, not structural
frames. The strengthened socket comment now names both observations.

H2 now has 31 headlines, with the earlier 29 unchanged; H6's 31 headlines are
also unchanged. The affected scoped build passed (175 jobs), all 62 affected
axiom checks and both fresh kernel replays passed, and combined import/axiom
inspection of all 163 campaign headlines passed with only the three standard
axioms. Independent read-only review found no outstanding mathematical or scope
defect. Ordinary elaboration failures were corrected; the direct expanded
release proof was replaced by exact removal plus a refcount frame. No cap
failure or infrastructure rerun. The full gate remains the inherited failure
recorded above. At that checkpoint, response sending, whole-caller coverage and
reachable owner/store coherence remained open for H2.

`DispatchSource` additionally composes original `Env.runOneSendWorker` through
its exact selection/dequeue factor and actual section reads around the proved
worker body. The two prefix table frames live in `DispatchFrames`; no new
shared variant or reference-count premise is needed. This closes one environment
send dispatch, including final peer release, not the entire scheduler or runner.
The new headline brings H2 to 32 and the campaign to 164. Its scoped build passed
(174 jobs), all 32 H2 axiom checks and fresh stock replay passed, and combined
import/axiom inspection of all 164 headlines passed with only standard axioms.
Independent read-only review found no issue; the previous 31 H2 statements are
unchanged. No failed build iteration, cap failure or infrastructure rerun in this
increment. The inherited full-gate failure is unchanged.

`ResponseSource` now composes original `sendHandshakeResponse`, including both
timestamp updates, response creation, session installation and the timer/send
suffix. Creation and installation combine their numeric and owner/bound
contracts over the same original runs. `ResponseFrames` adds only the
session-derived timer frame. The new normal-return headline needs no additional
residency or reference-count premise and covers normal early returns; it does
not guarantee transmission, completion or resident-store freshness. This brings
H2 to 33 and the campaign to 166. The scoped build passed (176 jobs), all 33 H2
axiom checks and fresh stock replay passed, and all 166 campaign headlines
import and pass axiom inspection together. Independent read-only review found
no defect. One ordinary map/discard proof mismatch was corrected; no cap failure
or infrastructure rerun. Previous headlines, mirror and shared layers are
unchanged. Whole-caller coverage and reachable owner/store coherence remain open.

`ConsumeSource` adds original `consumeInitiation`, `consumeResponse` and
`cookieMessageConsume` normal-return table-safety contracts. `ConsumeFrames`
preserves the existing optional table/cursor observation through reference
acquisition, lookup's actual suffix and public-key lookup. The index lookup
proof reuses its exact factor and existing scan theorem, retaining the actual
post-prefix state and both owner-word store-back cases, including NULL after
failed acquisition. The consumers compose the original failure-side releases;
those can remove rows, so unchanged-table equality is not claimed. No residency,
reference-count or owner-equals-peer premise is added.

These three headlines bring H2 to 36 and the campaign to 170. The scoped build
passed (178 jobs), all 36 H2 axiom checks and fresh stock replay passed, and all
170 campaign headlines import and pass axiom inspection together with standard
axioms only. Independent read-only review found no defect. Ordinary elaboration
fixes addressed a definitional equality, reused an existing module to avoid a
generated declaration clash, and explicitly simplified the initiation branch
conditions instead of letting eager automation recurse. No statement was
weakened; no cap failure or infrastructure rerun. Mirror and shared files remain
unchanged. Complete caller coverage and reachable coherence are still open.

The table invariant is about hashed entries; this checkpoint does not establish
all-driver reachable-session uniqueness or owner-store coherence through every
caller. Initialization of the table invariant now has its original-source anchor.

Independent read-only review found no semantic defect. Its wording finding was
fixed: the terminal lookup docstring now describes its exported provenance
postcondition, leaving stronger first-selection semantics to the internal
scan contract. The earlier twenty-three-statement checkpoint passed scoped build, standard-axiom inspection
and fresh stock kernel replay (`capped -- scripts/in-bundle lake env leanchecker
--fresh Leanux.Proofs.WG.Index.Statements`). The full proof gate still fails in
inherited `CounterWindow.Refinement` and `ReplayWindow.Counterexamples`;
token/import checks pass. The subsequent shared index frames remain campaign
1's carry. No mirror edit, cap hit, infrastructure rerun, guest or differential
run. Ranked mirror suggestions for H2: none at this checkpoint; no mirror
change has been requested to simplify the proofs. Independent review of the
three matched-entry contracts found no correctness issue; it checked owner
aliasing, missing-owner versus NULL distinctions, and the exact refcount bound.

`StagedSource` now closes original `sendStagedPackets` and `sendKeepalive`
table preservation. The proof retains the original nonce loop, skb allocation
map, fallback handshake queueing and actual enqueue continuations, including
EPIPE dead publication and other-failure keypair/peer releases. Caller peer and
key-owner identities remain independent. Direct normal-return `keypairPut`
preservation permits a NULL peer word when the reference is retained; it does
not import the stronger non-NULL premise of the total release contract.
`StagedFrames` isolates table/cursor-preserving packet, CPU and queue helpers,
including small local `peekQueuedUnit`, `queueDeviceWork`, and
`ipTunnelEcnEncap` kernel variants and a keepalive-site variant of the existing
C2 allocation lemma. Table-filtering releases remain substantive source claims.
No existing shared lemma or mirror definition is edited or layer copied.

The two new projected headlines need only initial `TablesSafe`. They cover
normal return, including allocation refusal, without extra residency, reference
count or owner-word identity premises. These callers enqueue crypt work; the
contracts do not establish worker execution, transmission, arbitrary-record
completion or resident-owner/store coherence. They provide the staged-send
boundary needed for the handshake receive caller.

H2 now has 38 headlines and the campaign 176. The scoped Index build passed
(182 jobs), all 38 H2 axiom checks and fresh stock replay passed, and all 176
campaign headlines import and pass axiom inspection together using only the
standard three axioms. Gate token and import/root/default-target checks pass;
the inherited full-gate failure remains. Independent review closed after moving
the purely structural enqueue helper into Frames. Ordinary elaboration fixes
only; no cap failure, timeout, guest run or infrastructure rerun. Reproduce with
`LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements`
and the same wrapper around `lake env leanchecker --fresh Leanux.Proofs.WG.Index.Statements`.
No new mirror finding or team request arose.

`ReceiveSource` extends that invariant through original `receiveHandshakePacket`
and one original `receiveStep`. Their only input is `View.TablesSafe`: no
readiness, residency, reference-count or owner-word identity premise is added.
Cookie replies, rejected messages, both Noise consumes, session installation,
staged/keepalive sending and final releases remain in the execution. The queue
iteration removes its head before the packet body and decrements the count only
after normal body completion. These are normal-return safety contracts, not
authentication, transmission, arbitrary-record completion or whole-worker
scheduling claims.

[AGENT 2026-10-15] Factor the original receiver into a continuation-form load
prefix and its packet body to keep proof elaboration bounded. `ReceiveOperations`
connects their composition to the original by definitional equality, including
all early returns and errors. The generic prefix's preservation premise is
discharged by the concrete packet-body theorem; it is not a public assumption.
`ReceiveFrames` isolates unchanged-table support. The existing H6 socket
observation supplies the cookie reply's no-cache transmission frame, without
copying a routing layer or assuming a resident observation peer.

H2 now has 40 headlines and the campaign 183. The capped full-parallel scoped
build passed (185 jobs), all 40 H2 headline axioms are standard, and fresh stock
kernel replay passed. All 183 campaign headlines import and pass standard-axiom
inspection together; gate token and import/root/default-target checks pass.
Independent review of the final continuation factor closed without findings.
Three deterministic 800k-heartbeat failures in the monolithic proof and ordinary
source-factor elaboration errors were resolved by factoring, without raising
limits or weakening statements. The first combined import check failed because
it overlapped the final rebuild and `ReceiveFrames.olean` was temporarily absent.
Exactly one infrastructure rerun, after confirmed build completion, passed.
No cap failure or guest run. The full gate remains failed in unchanged inherited
files, last run at `69f988a`. Reproduce with the preceding capped Index build and
fresh-replay commands. Whole-driver reachable coherence, broader records and the
corpus runner composition remain open; no new mirror finding or request arose.

`ClearSource` and `TimerSource` now extend the same normal-return invariant
through original queued key clearing, clear-worker dispatch, all five timer
callbacks and actual timer dispatch. Ordered keypair puts, handshake unhash,
final and compensating peer releases, queue selection/removal, due checks,
detachment and section reads remain in the original execution. The four public
claims add no residency, release-budget, slot-distinctness, readiness or abstract
callback premise. They do not assert completion on arbitrary inputs or
subsequent worker/scheduler coverage. `ClearFrames` and `TimerFrames` contain
only local unchanged-table/cursor support. Existing H6 generic selection and
section contracts are reused without a duplicate selection model or shared edit.

H2 now has 44 headlines and the campaign 193. The capped full-parallel scoped
build passed (189 jobs), all 44 H2 headlines use only standard axioms, and fresh
stock kernel replay passed. All 193 campaign headlines import and pass axiom
inspection together; token and import/root/default-target checks pass.
Independent read-only review closed without findings. Two ordinary elaboration
failures were corrected (queue-function specialization and discard-result/Ensures
conversion); no limit changes, infrastructure failures or reruns. No guest run.
Reproduce with the preceding capped Index build and replay commands. The full
gate remains the inherited failure last observed at `69f988a`. Whole-driver
closure, store/slot/lifetime coherence and runner composition remain open; no
new mirror finding or team request arose.

`FlushSource` extends table safety through original `drainHandshakeSendWq`,
`timersStop` and `peerRemoveAfterDead`. The two original bounded loops use an
explicit constant table-safety invariant; selection order, hidden-stream stops,
optional-target early return, the 4096 bound, pending/deadness/count guards,
ordered key clearing and final peer releases remain unchanged. These three
normal-return claims require only initial table safety, without readiness,
residency, empty-queue or release-budget premises. `FlushFrames` holds the local
queue and peer-count preservation support separately. Outer allowed-IP removal,
whole-driver closure and termination/progress remain open.

H2 now has 47 headlines and the campaign 199. The capped full-parallel scoped
Index build passed (191 jobs), all 47 headlines use only standard axioms, and
fresh stock kernel replay passed. All 199 campaign headlines import and pass
axiom inspection together; token and import/root/default-target checks pass.
Independent read-only review closed without findings. An initial elaboration
failure from omitted loop invariants was corrected; no infrastructure reruns,
cap changes or guests. Reproduce with the preceding capped Index build and
fresh-replay commands. The full gate remains the inherited failure last observed
at `69f988a`; no new mirror finding or team request arose.

[AGENT 2026-10-15] Outer `peerRemove`/`peerRemoveAll` table closure is deferred
for the user's shared-frame decision: six structural operation families need
local variants because campaign 1's snapshot omits the index table/cursor.
The [concrete overlap and alternatives](2026-10-15-campaign-2-shared-frame-request.md)
are recorded before implementation. No shared edit or variant copying has been
made for this increment. Independent H5/H3 work continues.

The next H2 increment avoids that deferred overlap. `SessionCoherenceModel`
states successful session publication over device data, `SessionCoherenceSource`
applies the exact H1 session effect and the existing H2 table invariant to the
same original execution, and `SessionCoherenceEffects` derives residency,
selected-slot placement and unique publication. `SessionCoherenceFrames` holds
only key-store preservation through excluded puts and unchanged handshake-row
membership through rotation. No shared variants are needed.

The new normal-return contract assumes an initially resident caller, table
safety, a self handshake peer word and exclusion of the allocation ID from the
actual role-dependent rotation releases. A true return then leaves that key
resident with one reference and the caller's peer word, places it in current or
next according to the original role, and publishes it at the former handshake
index. Both numeric-index and embedded-owner uniqueness identify that row.
Only actual releases are excluded; other aliases remain allowed. Allocation
may overwrite an existing unhashed object. These are static local premises,
not proved reachable invariants; allocation-store freshness, all-hashed-owner
residency, global lifetime safety and total completion remain open.

H2 now has 48 headlines and the campaign 204. The capped 32-thread Index build
passed (206 jobs), all 48 headline axiom checks are standard, and fresh stock
Index replay exited 0. Combined checks pass for all 204 headlines, including
projection and gate structural checks. Independent review closed without
findings. Reproduce with `LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build
Leanux.Proofs.WG.Index.Statements` and the same wrapper for `lake env leanchecker
--fresh Leanux.Proofs.WG.Index.Statements`. An initial Effects elaboration failure
was corrected. The first axiom-output parser rejected wrapped stock output;
the corrected parser checked the same successful Lean output without rerunning
Lean. No infrastructure rerun, cap hit, timeout or guest run. The full gate
remains the inherited failure; the shared-frame decision is still pending.

## H3 — Endpoint roaming (in progress)

[AGENT 2026-10-14] Observe the remote destination `(family, address, port,
IPv6 scope)`. The charter's “endpoint changes only” is read as remote roaming:
the full record also carries local-source caches, which routing and cache
clearing legitimately change, and flowinfo, which `endpoint_eq` ignores.
This preserves the intended remote-roaming claim; it does not claim full-record
get-after-set equality. `n1_flowinfo_only.json` already exercises that distinction.

Five terminal local contracts establish source conversion, setting a supported
remote destination, clearing source caches without roaming, and the composed
packet-source setter, plus exact successful data decryption under the resident receiving key. IPv6 link-local scope comes from the arrival interface.
The proof follows the original functions, including the endpoint-equality
early return and destination-cache reset; no mirror changes.

The read-only source review identifies the receive authorization cuts: Noise
consume success for initiation/response, and crypted publication followed by
replay acceptance for data. Data roaming precedes inner-IP/AllowedIPs checks;
authenticated malformed inner packets and keepalives may roam. Outer source
identity is not authenticated by the data AEAD. Cookie messages do not roam.
These source observations are not yet theorems about the whole receive path.

`PublicationSource` now factors the complete original `decryptStep` at the
publication point before `irqExit`, retaining arbitrary original callbacks and
their order. Its observer inspects the prefix from the same concrete entry and
then executes the original step; discarding the observation is exactly the
original operation, including every error. On normal completion, the consumed
flag agrees with whether the prefix produced a publication cut. For a consumed
packet, `PublicationClaims` derives the actual ring selection and input after
the first softirq, the resident key read by `decryptPacket`, and the packet
slot at publication. A CRYPTED slot contains the AEAD plaintext, preserves the
input source/peer/keypair fields and has the decoded input counter as its nonce.
No authentication premise is assumed. The callback may subsequently consume or
free that packet; final residency and equality of packet peer with key owner
are not claimed. `PublicationModel` holds the projected certificate and
`PublicationFrames` isolates the generic read and refcount-check frames.

This sixth terminal statement passes scoped build (48 jobs), inspection of all
six Roaming headline axioms (the standard three only), and fresh stock kernel
replay, through the capped bundle. All 165 campaign headlines also import and
pass axiom inspection together. Independent read-only review found no
mathematical or source-linkage defect; two minor findings were fixed: place the
generic read helper in the frame file, and make the CRYPTED condition explicit
in the nonce/field documentation. No cap hit or infrastructure rerun. The full
gate remains failed in the inherited shared carries noted above.

Two further projected headlines connect the original poll and decrypt publication.
`PollEndpointSource` factors the current poll's first iteration at the endpoint
setter, including the original zero-budget guard, then retains all remaining
iterations, GRO/stack callbacks, reference releases, skb freeing and repoll
stops. On normal full-poll return, `PollEndpointClaims` derives the actual
entry/before-read packet, its peer-field equality to the poll peer, CRYPTED
state, the actual counter-validation result `true`, supported source conversion
and immediate destination. It does not infer a counter-window invariant from
that Boolean result. The observation erases to the original poll on successes
and errors.

The second headline decorates original `decryptStep` with that poll as its
actual interrupt-exit callback. Publication and poll observations are sequential
cuts of the same execution. If the first packet reaching the setter has the
just-published identity, its bytes have the earlier AEAD provenance under the
key actually read at decryption. Initial/final softirq and stack callbacks stay
arbitrary. Earlier queued packets need their own provenance; no global
queue/store invariant, packet-peer/key-owner equality, current-key equality,
inner delivery, final endpoint preservation or `Env.napiIrqExit` scheduling
coverage is claimed. `PollEndpointModel` holds only projected data and
certificates. `PollEndpointFrames` isolates the queue-peek kernel variant of
shared `PrevQueue_peek_spec` and the snapshot-read equation; no shared layer is
copied or edited.

H3 now has 8 headlines and the campaign 178. The capped full-parallel scoped
build passed (52 jobs), all 8 H3 headline axiom checks and fresh stock replay
passed, and all 178 campaign headlines import and pass axiom inspection
together. Gate token/import/root/default-target checks pass. Independent review
closed with no outstanding findings; documentation now says literal packet-peer
equality, normal-return scope and conditional identity matching. Ordinary
elaboration corrections were made; no cap hit, timeout, guest run or
infrastructure rerun. The full gate remains the inherited failure recorded
above. Reproduce with `LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build
Leanux.Proofs.WG.Roaming.Statements`, capped `lake env lean --stdin` for the
headline axiom list, and capped `lake env leanchecker --fresh
Leanux.Proofs.WG.Roaming.Statements`.

Remaining work: general queue/poll provenance beyond this first-packet join,
cover the handshake and netlink callers,
and frame remote destinations across the remaining runner operations. Arbitrary
Worlds may contain forged crypted packets; they are not accepted-run findings.
Callbacks require their actual concrete framing contracts, not an assumed
authentication result. No Rule Zero finding or mirror-team request yet.

[AGENT 2026-10-15] For the remaining handshake caller proof, use exact consume
transcripts carrying actual AEAD arguments/results and the actual MAC admission
decision. Cut before the endpoint setter: its later cache-reset read can fail
after the endpoint write. Retain the original continuation and errors; immediate
destination equality requires successful setter completion. The response case
is now closed below; initiation remains open. Tag endpoints alone are insufficient
authentication evidence; semantic crypto-dataflow contracts were considered as
the alternative but would require more leaf contracts and preservation proofs.

The ninth H3 headline connects the complete original response-kind caller to
its actual pre-setter cut. Its only message premise is the response kind, not
authentication. A no-cut suffix is pure; a present cut immediately invokes the
original setter and retains session installation, timer hooks, keepalive,
statistics and final reference release. Both original-operation correspondence
and decorated-observation correspondence are exact, including errors. The latter
ties the returned certificate to that very prefix/suffix execution rather than
an independently supplied observation.

On normal full return, the cut derives the actual under-load/MAC admission,
lookup owner and referenced peer separately, the lookup's same-entry result and
post-lookup peer, both successful DH checks, exact KDF-derived AEAD key/AAD,
successful empty plaintext, and the consumer's state recheck and committed
fields. The outer source is not an AEAD input. This is response-only caller
coverage, not final endpoint preservation, initiation coverage, general queue
provenance or retained prefix evidence after a failing full call. `ResponseModel`
holds projected data and predicates; the five other new Response modules hold
substantive crypto/source/claim connections. No shared frame variants were added.

H3 now has 9 headlines and the campaign 203. The capped 32-thread scoped build
passed (59 jobs); all 9 headlines and 10 exact source equations have only the
three standard axioms, and fresh stock Roaming replay exited 0. Combined import
and axiom inspection of all 203 headlines, public projection checks and the
gate's token/import/root/default-target checks passed. Independent review closed
without findings. Reproduce with the preceding scoped Roaming build and fresh
replay commands. Deterministic parse/normalization errors and a simplifier step
limit were corrected; an existing generated sparse-case name collision was
resolved by importing the existing Noise frame module first. No existing shared
proposition changed, infrastructure retry, cap hit, heartbeat timeout or guest
run. The full gate retains the inherited failure last observed at `69f988a`.

Ranked mirror suggestions: none at this checkpoint. Effort: a read-only source
review and capped scoped proof builds; ordinary elaboration failures repaired.

## H4 — Configuration semantics (in progress)

Thirty-nine terminal declarations cover configuration leaves, peer flags, bounded
readback, normal-return guarantees, one sequential partial-error case, and
fwmark/cache frames. `Validation`, `Identity` and `Port` prove invalid allowed-IP
rejection, exact allowed-IP serialization, private-identity normalization,
static-static precomputation and stopped-device port setting. `Flags` proves
missing-peer remove/update-only and self-key no-ops, invalid flag/protocol
rejection, and acquired-peer removal precedence. The removal equation is a
stage result, not a complete lifecycle theorem.

`PeerScalars`, `PeerDump` and `RoundTrip` compose the original peer setter and
getter for an existing peer while down: the requested preshared key and
keepalive interval read back exactly. The dump has a fresh cursor, an empty
allowed-IP list and at least 168 bytes remaining (enough for the largest fixed
encoding, with IPv6). `Returns` and the local `*Returns` variants additionally
prove actual normal-return existence when the reference count is positive and
its increment is strictly below `2^31`. The broader `Ensures` statements remain
partial-correctness contracts without that count bound.

`DeviceScalars` reaches the original outer `wgSetDevice`: an index-selected
request updates one existing peer, then encounters a malformed peer entry.
It returns `-EINVAL` normally, retaining the scalar writes and device-generation
increment. A following peer dump returns and reads back the retained writes.
This is a proved partial-update case, not an atomic-update guarantee or an
accepted runner trace. `EndpointSources` proves exact local-source clearing,
cache-slot removal, and preservation of other peers and other device fields.
`Fwmark` proves a fwmark-only outer set writes the mark and increments the
generation, preserving every other device field outside the peer store.
`ClearedSources` joins the literal loop to the outer setter and proves every
listed peer ends with cleared source fields and no cache slot. `FwmarkEffects`
strengthens this to exact pointwise peer-store effects: unlisted peers are
unchanged, listed peers retain all other fields, and duplicate list entries
retain the last reset timestamp. Reset timestamps are existential; their record
provenance and consumption are not proved. These fwmark contracts concern normal
completion. `SocketPorts` proves actual normal return
and an exact device update for socket replacement and for initialization at a
nonzero port in an existing namespace: conflicts return `-EADDRINUSE` without
a device change, success replaces both sockets and the incoming port.
`RunningPort` and `DevicePorts` compose this with the original port setter and
outer configuration request: a different port clears listed peer sources/cache
before binding, so a bind error retains those effects. An equal-port inner
request leaves the device unchanged; an equal-port outer request still increments
the generation. The outer theorem assumes an existing namespace; the inner
contract also covers namespace failure. `RandomPort` proves port-zero success
selects within 32768..60999 and, for a supplied padded four-byte draw with a free
first candidate, proves an actual return installing exactly the computed port.
The generic zero-port theorem remains partial: missing records or a collision
can stop. `ZeroPort` composes normal port-zero behavior through the outer setter,
including stopped/running behavior and the equal-zero no-op. `RecordedPort`
strengthens the supplied-draw success theorem to exact final record-tail
preservation and proves an occupied first candidate raises the mirror's declared
outside-domain collision stop. This is a modeled-domain boundary, not a kernel
bind-error or collision-retry claim.

`PrivateKey` adds actual-return guarantees for identity installation, cookie-key
precomputation and an unchanged-key-only outer request. Unchanged means the raw
requested bytes equal the stored clamped bytes; repeating an unclamped request
can execute the update again. `Precomputation` preserves the complete surrounding
device and models the ordered peer-store writes, including DH output followed
by zeroing when necessary. `ExpiryEffects` gives the exact normal-completion
store transformation: handshake entries removed, handshake fields zeroed, slots
preserved, and next/current sending validity cleared without changing other
keypair fields. Its pointwise theorem handles aliased IDs. Missing targets stop
the original operation; the pure transformation's missing-target fallback is
not an executable-equivalence or return guarantee. The weak existential-time
contract leaves last-sent time unrestricted. `ExpiryClock` separately closes
that gap by exposing the actual prefix and reset-clock read from the original
run and using the returned clock in the final state, with wrapping arithmetic.
Independent review confirmed that relation. The read may use placeholders where
enabled; captured-record provenance is not established by this theorem.

The private-key installation block now composes identity installation,
cookie-key recomputation and the snapshotted peer-list loop for both staged-send
settings. Its ordered relation records resident peers and intermediate stores,
allowing repeated peers and aliased keypair slots. An unconditional source
equality connects the factor to the original configuration continuation.

Expiry invalidates current sending material before staging. The original
staging contract proves exact Device effects: an empty staged list is unchanged;
otherwise packets are restored, temporary key references preserve lookups, and
handshake queueing resets attempts and may retain a queued peer reference.
Already-pending work balances its temporary reference. The original handshake
queue function separately exposes the actual age-test clock read; the staging
and loop relations retain only existential clocks. Expiry alone does not imply
queue eligibility without a relationship between supplied clock values.
Dangling current slots cannot complete with nonempty staging. Records and
reference-count bounds may also stop execution. These are normal-completion
Device contracts, including the send-work queue, not descriptions of World
bookkeeping or record consumption. Independent reviews found no semantic defect
in the staging, per-peer, loop or installation increments and confirmed these
scope limits. The original outer private-key-only setter now composes that
relation when the raw key changes and no generated-public-key table entry
matches. It returns zero on normal completion and includes the generation
increment. The earlier unchanged-key total contract covers the no-op key arm;
collision removal and later peer attributes remain separate obligations.

[AGENT 2026-10-15] Compose private-key updates from a baseline after optional
self-peer removal: removal may flush other peers' work under the old identity,
so an unrestricted surviving-peer frame against the initial request state would
be false. Prove the key-only block before composing later peer attributes.

[AGENT 2026-10-14] Get-after-set means the effective configuration established
by the C: keys are clamped, prefixes masked, running port-zero may allocate a
port, and flowinfo-only endpoint changes are ignored. The configured flag is
`REPLACE_ALLOWEDIPS`, not a per-prefix removal flag. These qualifications keep
C semantics; they do not authorize narrowing accepted traces.

Local source factors are copied from campaign 1 at c4ef635 (`PeerSource`,
`DumpSource`) and ec95fa8 (`DeviceSource`), with definitional original-function
equations. The coordinator can unify them after landing; no existing shared
lemma is changed. Independent review found the first full-room dump premise
could not apply after the caller's headers; the sufficient-tailroom theorem
resolves that finding. Review of the normal-return and partial-error increment
found no defect. The fwmark/socket review found one wording error: a supplied
IPv4 socket assigns its port, which need not change the previous value. The
statement documentation now says assignment/preservation. No further defects
were found. Independent review of the port composition and recorded-draw
increment and subsequent outer-zero/record-tail/collision increment found no
defect. Review of the identity/precomputation/expiry leaves found no semantic
defect and identified the weak existential-time and missing-target scope limits
recorded above.

The outer getter is now composed for a single resident peer with no allowed
IPs and sufficient chunk room. Exact local source equations connect the
callback and receive-loop factors to the original definitions. The proof
carries the callback through dump start, data plus DONE queueing, receive and
coalescing; it proves total return of the exact canonical JSON, unchanged
device, and a drained, finished socket 7. The socket initially has an empty
queue and no running dump, and interface lookup selects this device. Its bound
flag is unrestricted. The loop proof exposes its first receive and proves the
finished tail immediately breaks, without expanding 4096 iterations. The
canonical peer includes `allowed_ips: []`. Independent architecture review
confirmed these premises and the distinction from multipart snapshots. A second
read-through of the completed increment found no semantic defect; its premature
validation sentence was corrected before the checks completed.

`ReadbackFrames` and `ScalarGetter` now carry socket 7 and fixture interface
selection through scalar configuration, then compose the original `wgSetDevice`
and `wgGetDevice`. For one resident, live peer on a stopped device, with a
bounded temporary reference count and no allowed IPs, the public getter returns
the new preshared key and keepalive interval in the exact canonical JSON. The
full Device includes the generation increment and balanced reference; the socket
is drained and finished. With a malformed second peer entry, the setter returns
`-EINVAL` and the same first update is read back. This is a total contract for
the composed original operations under the named premises, not an accepted
runner-trace witness or a general multipart theorem. Independent review found no
correctness defect and confirmed the retained partial-update semantics; public
key/table coherence is not assumed or claimed.

`AllowedLists` and `AllowedListView` prove the original list deletion and its
pointwise peer-list effect. `AllowedRemovalSource` factors the unchanged trie
removal loop; `AllowedRootRemoval` closes its singleton root-leaf path.
`AllowedReplacement` composes that path with lookup acquisition/release and the
original public device setter. The new terminal contract replaces a stopped
peer's owned singleton root leaf with an empty allowed-IP list: the node is
erased, its family root is cleared, all peer lists lose the node, the trie
sequence and device generation each advance once, and the lookup reference is
balanced. Ordered map writes remain explicit; no structural map equality is
inferred from pointwise lookup equality. This is a bounded successful-operation
contract, not general trie validity, ownership preservation through arbitrary
insertion, or multipart readback. Independent read-only review found no
correctness defect and confirmed that the extra root/owner premises specialize
the stronger operational helper to the advertised case.

`AllowedStructural`, `AllowedLeaf` and `AllowedCollapse` now cover branching
nodes, unary promotion, leaf deletion and parent collapse. Exact source equations
retain the original branch logs. `AllowedRemoval` composes those alternatives
through the original snapshot loop, reading each node from the evolving state.
Its pure `RemovalEffect` witness checks actual successive maps, including the
parent reread after leaf deletion; it assumes no distinctness that would hide
aliasing failures. `AllowedRemovalEffects` proves filtering of every peer list,
target-list emptiness and exactly one sequence increment for a nonempty snapshot.
`AllowedGeneralReplacement` carries this result through the original public
setter, including generation update and balanced lookup acquisition/release.
The two new terminal contracts accept arbitrary list lengths with a supplied
removal witness. They do not establish witness existence for every valid trie,
trie validity, lookup preservation, or ownership/list coherence. This extends
the earlier singleton-root result without treating operational readiness as a
global invariant. Independent review found no structural-case or read-order
defect in the removal relation, sequence frame, final public composition or
terminal scope.

`AllowedOwnerClear` strengthens both general removal terminals: every identity
in the original target list is absent or has a NULL owner after the operation.
Slot writes and reparenting preserve owners from the actual current map, and
later removals preserve already-cleared owners. This covers duplicates and
aliases whenever the existing readiness witness exists. It does not establish
that the list contains every node owned by the peer, physical deletion of
branching nodes, trie validity or lookup behavior. Independent read-only review
found no correctness or scope defect. The scoped build, all fifty-eight axiom
inspections and fresh replay were repeated for the strengthened statements;
the full gate still fails in the two inherited modules below.

`PeerDead` composes the witnessed removal with original `peerMakeDead`.
It removes every occurrence of the peer identity from the device list and
public-key table, clears the allowed-IP list/processed owners, and marks the
resident peer dead. Its reference count, the numeric index table and device
peer count remain unchanged at this stage, as the source requires. A small
metadata projection supplies the removal frame. This is not the subsequent
keypair/timer cleanup, workqueue drain or final release. Independent read-only
review found no correctness or source-order defect. Proof elaboration
needed the intermediate device equality simplified before substituting it;
no mirror or resource-limit change was made.

`EmptyKeypairs`, `QuietTimers` and `QuietRemoval` compose total contracts
through original `peerRemove (some pid)` for an empty-slot peer with empty
send/clear queues and a supplied allowed-IP removal witness. The exact Device
retains the three slot writes and five timer writes, the empty drain, count
decrement and final release in source order. The drain returns on its first
iteration without consuming a record. Positive references and device count
suffice; no reference-increment bound or stopped-device premise is needed.
Last-reference release unhashes and erases; otherwise a dead peer remains
resident. Timer deletion clears expiries, not counters or pending flags. Final
release changes World dispatch associations, so the terminal states a Device
contract. Independent read-only review found no correctness or scope defect.

[AGENT 2026-10-15] Share the existing Noise slots and state-edge dependencies
with Index lookup and handshake frames: combined imports exposed duplicate
Lean-generated `peerDeref` and `createInitiation` sparse-case declarations.
Sharing their prior declarations resolves the clashes; no theorem proposition
or mirror definition changes. All six campaign-2 Statements modules now import
together and all 150 terminal declarations pass standard-axiom inspection.
The new composition hit local heartbeat limits during nested record projection;
explicit frame projections and a generic count-decrement contract resolved them
without raising any limit.

`LiveRemovalModel` and `LiveRemovalSource` now remove the empty-key-slot
restriction for original `peerRemoveAfterDead` and `peerRemove`. Their two total
contracts use static `ClearReady`: resident, non-NULL-word keys with enough
references for their slot multiplicities, including aliases. The first theorem
derives the ordered `ClearRun`; it does not assume an operational clear witness.
The outer theorem retains the existing allowed-IP `RemovalEffect` witness.
Both require a resident peer, positive peer reference/device count and empty
send/clear queues; after-death removal additionally requires the dead flag.

The suffix starts from the actual cleared device, performs the five timer
writes, empty drain, count decrement and final release, and never repeats the
slot writes over the pre-clear device. Last-reference release erases/purges;
otherwise the dead peer remains. These are exact Device effects, not global
ownership or dispatch-association contracts. `LiveRemovalFrames` separately
proves the clear relation preserves queues/count and allowed-IP removal
preserves the keypair store, which transports the static readiness premise.
No new owner-equality, slot-distinctness or queue-coherence premise was added.

H4 now has 62 headlines and the campaign 180. The capped full-parallel Config
build passed (176 jobs), all 62 headline axiom checks and fresh stock replay
passed, and all 180 campaign headlines import and pass standard-axiom
inspection together. Structural gate checks pass; the full gate remains failed
in the unchanged inherited files. Independent review closed with no findings.
An initial 800k-heartbeat Lean elaboration timeout was corrected by projecting
peer/count facts before monadic composition, without raising a limit. No cap
hit, guest timeout or infrastructure rerun. Reproduce with `LEAN_NUM_THREADS=32
capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements`,
capped `lake env lean --stdin` for headline axioms, and capped `lake env
leanchecker --fresh Leanux.Proofs.WG.Config.Statements`.

Remaining: private-key collision removal and mixed-attribute outer composition; queued-work peer
removal/replacement and allowed-IP ownership, other partial-error combinations,
and general dump chunks/coalescing. Deferred removal work can change other
peers' dynamic state, so no unrestricted removal frame is claimed.

Rule Zero finding: the empty-device dump retains four bytes of a cancelled
peers-nest reservation. A one-operation getter trace is accepted from the
ordinary fixture; the original callback returns room 3720. C's pre-reservation
snapshot and cancellation give room 3724. Two independent source reviews agree.
This is a reachable internal accounting mismatch, not a demonstrated compared
output difference or kernel finding. The three `DumpCancellation` equations are
kernel checked; the C correspondence is source inspection. Statement-artefact
check: both the C and the mirror's own design require restoring pre-nest room.
[Request 3](2026-10-14-campaign-2-mirror-requests.md#3-restore-pre-nest-tailroom-when-cancelling-the-device-peers-nest)
gives the witness and reproduction command. Ranked mirror suggestion 1:
correct the saved cancellation snapshot (altitude-preserving).

Validation of the preceding sixty-statement checkpoint: scoped build,
standard-axiom inspection (only `propext`, `Classical.choice`, `Quot.sound`),
and fresh replay all passed. Replay command: `capped -- scripts/in-bundle lake
env leanchecker --fresh Leanux.Proofs.WG.Config.Statements`.
The full proof gate fails in inherited `CounterWindow.Refinement` and
`ReplayWindow.Counterexamples` after the index landing; token/import
checks pass. Effort includes repaired proof-elaboration failures, including two
local heartbeat limits resolved by simplifying put calculations before their
continuations. The suggested `vcgen` replacement failed with a missing toolchain
constant; the existing `mvcgen` proofs were retained and rechecked. A direct
scalar-frame proof hit its heartbeat limit; the staged lookup/update/release
contracts closed the same frame without raising the limit. No cap hit, infrastructure rerun, mirror edit, differential
check or guest run. Builds use full Lake module parallelism with
`LEAN_NUM_THREADS=32`; gate runs use `LEANUX_QEMU_SLOTS=16`, without a cap change.

[AGENT 2026-10-15] For the next general allowed-IP removal increment, derive
the existing `RemovalEffect` from normal execution under the static premise
that every resident node has exactly two child slots. This replaces a supplied
operational witness, not total-success readiness. The unrestricted converse is
too strong for the existing relation: source inspection shows a three-element
array with two non-NULL first children can take the original branching return,
whereas every `NodeRemoval` constructor requires a two-element array. These
examples have not been executed or kernel-proved and are not accepted-run
counterexamples. A generalized operational relation was considered; the chosen
two-slot invariant reuses the established relation and effects. Normal successful
reads supply the remaining successive-state premises without ownership,
acyclicity or distinct-node assumptions. This architecture is now checked below;
it is not a mirror-team request.

The two new normal-return headlines derive the existing `RemovalEffect` rather
than taking it as a premise. `NodePairs` requires exactly two child slots for
each resident node; the other premise identifies the initial resident peer and
its captured list. Branching, unary, leaf and collapsing cases use their actual
successive reads, including the parent read after leaf erasure. Aliases, cycles
and repeated list identities are not excluded. Normal completion derives exact
list filtering, processed-node owner clearing, the single sequence increment for
a nonempty list, and preserved node shape. `peerMakeDead` derives its removal
witness from the actual prefix, then obtains exact membership/death effects from
the existing execution theorem on the same concrete initial state. The peer
remains resident with its original reference count; index table and peer count
are unchanged at this stage. Later cleanup and release remain separate.

The shape premise matches pristine C `drivers/net/wireguard/allowedips.h:15–17`
(`bit[2]`) and the mirror's `newNode`, used at all three allocation sites with
`#[none, none]`. This is source provenance, not a proved reachable-state shape
invariant or total-success condition. Generic normal `add`/`insert` preservation,
full trie validity, queued-work removal and outer setter composition remain open.
The existing witness-based total-return claims are retained unchanged.

`AllowedPairsModel` defines shape. `AllowedPairsEffects` contains invariant
preservation through actual node/child/store mutation; those proofs must survive
the state split. `AllowedPairsFrames` contains untouched-node-store support.
`AllowedRemovalConverseSource` and `AllowedRemovalConverseClaims` connect the
original executions to projected claims. Independent review's P3 classification
finding was fixed by this Effects/Frames separation; final review closed with
no remaining findings.

H4 now has 64 headlines and the campaign 196. The capped full-parallel Config
build passed (181 jobs), all 64 Config headline axioms are standard, and fresh
stock kernel replay passed. All 196 campaign headlines import and pass axiom
inspection together; token and import/root/default-target checks pass. Reproduce
with `LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements`
and the same wrapper around `lake env leanchecker --fresh Leanux.Proofs.WG.Config.Statements`.
Ordinary proof elaboration errors were corrected. The first ephemeral axiom
driver failed on the unknown formatting option `pp.width`; removing that option
and rechecking the corrected driver passed. This was a driver correction, not
an infrastructure retry. No cap failure, guest run or infrastructure rerun.
Full gate failure remains inherited and unchanged, last run at `69f988a`.
No new mirror finding or request arose.

## H5 — Termination and progress (finding; remainder open)

The requested operation-end drain property is false on an accepted constructed
record stream. A two-operation trace starts from the runner's ordinary fixture,
brings wg0 up and batches one correctly sized cookie message. NET_RX queues the
receive worker, but its records contain no worker dispatch. `executeTrace`
accepts; the original syscall-world replay ends with one handshake receive
item, length counter 1 and pending receive-worker identity 1. No hidden record,
suspended activation or raised NET_RX remains.

`Progress/BatchBacklog` defines the exact trace and replay; the two terminal
statements prove runner acceptance and the state summary by `decide +kernel`.
The replay explicitly follows the runner's fixture initialization, syscall
calls and ambient skips; no arbitrary preloaded World is used. This is an
accepted mirror record stream, not a captured Linux execution. The
[mirror-team request](2026-10-14-campaign-2-mirror-requests.md) locates the omitted
handshake-queue drain check in `Env.afterBatch` and gives the reproduction.

Ranked mirror change: add the missing environment completion check
(altitude-preserving). The mirror is unchanged here. The progress claim is not
weakened to permit this backlog. Remaining H5 work includes committed scheduler
dispatch/resume coverage, record-budget productivity and the other operation
completion paths; the finding does not settle those obligations. Effort: one
read-only source review, model-only evaluation and kernel-reduction proofs.
A separate critical read-only review found no material defect. It checked the
runner/replay correspondence, ordinary parser bounds and that the remaining
queue satisfies the scheduler's runnable-work predicate. It also confirmed
the boundary: two checked equations, not a theorem exposing the runner's final
World, and no claim about capture feasibility. No findings required disposition.

Validation for the H4/H5 checkpoint: all seven new terminal statements build,
print only the three standard axioms, and pass separate stock kernel replays
with `leanchecker --fresh`. The full proof gate fails at the same inherited
counter-window refinement; token and import checks pass. No mirror changes,
guest runs or cap failures.

H5 continuation: `Progress/Scheduler` now proves the original resumption
probe's exact outcome and World preservation, its success/mismatch iff
contracts, and the empty/productive worker-iteration equations. Five additional
terminal statements make seven in H5. A successful probe runs an activation on
a copy; it does not itself resume it. In `schedule`, actual resumption first
removes that activation from `suspended`. Equating the probed and actual runs
needs a frame for that removal, because `cryptAhead` reads `suspended`.

A second investigation reproduced an invalid occupancy premise: a nested NAPI
callback inside the encrypt worker generates a reply and refills that worker's
queue. `QueueRefill` retains the initialized-prefix executable reproduction;
[request 2](2026-10-14-campaign-2-mirror-requests.md#2-account-for-nested-queue-refill-in-activation-budgets)
gives the exact evidence boundary, source locations and altitude-preserving
correction requested. The user was notified. This is an evaluated model-prefix
finding, not an accepted-run termination counterexample or a kernel-reduction
theorem. Both JSON-based reduction and a typed-trace reduction were attempted;
the latter exposes the remaining non-reducing arithmetic-loop implementation.
No proof oracle or added assumption substitutes for that missing proof.

Ranked mirror requests are now (1) the missing batch completion check and
(2) a callback-aware activation bound, both altitude-preserving. A read-only
independent review confirmed the second source path and required the explicit
prefix-only qualification above. That qualification is incorporated in the
request and witness documentation. The full scheduler has two candidate proof
architectures: an erased dispatch/resume event observer, or source-factorized
single-turn execution followed by a bounded iteration relation. Neither is
claimed complete. Kernel-checked local contracts do not establish termination
of every transitive arithmetic loop or full dispatch/resume completeness.

`Progress/Dispatch` factors the original dispatch selection/detachment from
its section-start read and activation execution, including transmit-unit
resolution. Three additional terminals establish the exact success and
false-result equivalences and the total no-work World frame. A successful
dispatch actually runs an iteration-zero activation; a selected activation
failure cannot be converted to a false no-work result. This is local dispatch
coverage, not a proof that all runnable work is dispatched by the scheduler.
Independent read-only review found no issue.

`Progress/ScheduleTurn` now connects the second architecture to the original
scheduler by exact source equality, preserving its record budget and exhaustion
continuation. Successful candidate filtering preserves the entire World and
selects exactly the successful probes, in order and with duplicates retained.
The zero/singleton/multiple-candidate resumption cases preserve original return,
committed execution after detachment, and ambiguity errors. These five terminals
made fifteen. `Progress/StackResume` adds three original caller-stack guard
contracts: a busy worker reports the original ambiguity stop, an idle worker
permits committed execution, and a failed work check propagates its exact stop.
The guard preserves the World. Its worker-only activation has no peer identifier,
as in the mirror; transmit checks therefore take the error case. Independent
read-only review found no defect. Productive-turn record decrease, iteration
coverage and the frame from probing to execution after detachment remain open.
No statement assumes that a successful probe guarantees successful detached
execution.

`RecordedTurn` adds four recorded dispatch/NAPI contracts. Scheduler
continuation at a worker start is equivalent to original dispatch selecting,
reading the start record and executing the activation. Normal no-work returns
and exact dispatch errors are distinguished. A normal NAPI turn executes the
original poll and its second peek; another NET_RX start returns to the caller,
otherwise the turn continues. Both peek Worlds are retained because ambient
records can be consumed. Independent read-only review found no defect. These
contracts do not assert poll-state framing, queue drainage, productive record
decrease or whole-loop completion.

`PlaceholderTurn` closes the recordless branch factor with its exact
receive/decrypt/encrypt/transmit priority. Three terminals establish unchanged
return when those four readiness checks are empty, actual dispatch execution
on normal continuation and exact dispatch-error propagation. The original
false-dispatch invariant remains in the factor. Recordless mode does not imply
enabled placeholders; the four empty checks do not cover suspended activations,
NAPI, timers or send work. Independent read-only review found no defect. These
results provide neither fairness nor the productive-turn measure.

The twenty-five H5 statements pass scoped build, standard-axiom inspection and
stock kernel replay (`leanchecker --fresh Leanux.Proofs.WG.Progress.Statements`,
through the capped bundle). The
full gate was rerun and fails at the same inherited counter refinement; token
and import checks pass. The separate executable refill reproduction succeeds.

The original `skipCutSites` now has a record-budget adequacy proof. `CutSource`
factors the unchanged range loop, including its original allocation check,
ambient stripping, head consumption and NET_RX ordinal update. An induction
on remaining turns proves that entry record count plus one suffices: every
continuing turn removes at least one record, and the extra turn finds an empty
or unselected head. The successful result leaves a genuine input suffix, every
reported site is selected, and reported-site count plus remaining-record count
is bounded by the initial count. No exact reported-site order is claimed.

The unconditional recorded outcome is successful return or the original
below-cut allocation error, with its actual location and message; budget
exhaustion is excluded. A separate total-return contract assumes `CutAccepted`
only over the consumed non-passive selected prefix. Failed allocation records
beyond the first unselected boundary need no premise. The acceptance test keeps
the original `headD 1` behavior, including successful empty payloads and no byte
length check. These claims concern the original operation on every concrete
realization of the projected entry, not an inspection adapter. The suffix/drop
operation is a substantive source effect; `CutFrames` contains only untouched
record/error-location preservation. No shared lemma was copied.

H5 now has 27 headlines, and the campaign has 172. The scoped Progress build
passed (84 jobs), all 27 headline axiom checks plus exact source equality use
only the three standard axioms, and fresh stock kernel replay passed. All 172
campaign headlines import and pass axiom inspection together; the gate's token
and import/root/default-target checks pass. Independent read-only review found
no correctness or scope defect. Ordinary elaboration corrections only; no cap
failure, timeout, guest run or infrastructure rerun. Reproduce with
`LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.Statements`
and the same wrapper around `lake env leanchecker --fresh Leanux.Proofs.WG.Progress.Statements`.
The full gate remains failed in inherited shared files. Worker-body record
monotonicity, scheduler-wide productive turns and operation-end closure remain
open; this result does not settle the callback-refill finding or prove whole
scheduler termination.

The original `runFlushedSendWork` and `runFlushedClearWork` now have exact
normal-return queue effects: erase the first matching occurrence, if present,
from the selected entry queue and preserve the other queue. Membership in the
selected entry queue implies that total queued-work count decreases by exactly
one; duplicates remain permitted. The only entry premise is the resident device.
Original pending checks, section reads, worker bodies and final peer releases
remain intact, including last-reference peer deletion. No readiness, live-peer,
reference-budget or input-execution-witness premise is added. These contracts do
not guarantee successful completion, selection membership, or whole-drain progress.

`FlushQueueModel`, `FlushQueueSource` and `FlushQueueClaims` hold the observation,
original-operation composition and projected claims; `FlushQueueFrames` holds
preservation. The existing C2 sending observation is strengthened once to retain
both queues, with old interfaces recovered by same-execution projections. The
resident-path sender helpers retain their existing Boolean pending premise;
the queue-only original flush proof derives residency from its actual normal
execution. Keypair cleanup projects existing exact `ClearRun` effects. Three
small named/cited local variants stand for shared `setChain_spec`, `peerPut_spec`
and `handshakeClear_spec`; no shared file or routing layer is copied or edited.

H5 now has 29 headlines and the campaign 201. The capped 32-thread affected
Progress/TimerDiscipline/Index build passed (255 jobs), all 111 affected headline
axioms are standard, and separate fresh stock kernel replays of all three modules
passed. All 201 campaign headlines import and pass axiom inspection together;
forbidden-token and import/root/default-target checks pass. Independent review
and a follow-up on the final `setChain` factoring closed without findings.
Reproduce with `LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.Statements Leanux.Proofs.WG.TimerDiscipline.Statements Leanux.Proofs.WG.Index.Statements`
and separate capped `lake env leanchecker --fresh` invocations for those modules.
Ordinary tuple/projection edits, initiation proof automation, optional tactic,
definitional throw reductions and membership-based arithmetic errors were
corrected. No cap failure, guest run or infrastructure retry. The full gate
remains the unchanged inherited failure last observed at `69f988a`.

[AGENT 2026-10-15] Address the original modular-exponentiation loop through
an exact finite accumulator evaluator before expanding the handshake caller
transcript. The original accumulator behavior is the contract: unrestricted
equality to stock `Nat.powMod` is a statement artefact, because the original
returns 1 at exponent zero even modulo 1.

`PowModel` now defines the exact accumulator/base/exponent step and an
Option-valued finite evaluator; exhausted fuel is explicit. `PowSource` connects
the original private `powMod` to its actual loop by definitional equality.
The stock `Lean.Loop.forIn_eq_of_monadTail`, with the standard `LawfulMonad Id`
and `MonadTail Id` instances, gives checked logical unfolding. Induction on fuel
proves successful finite evaluation and final exponent zero whenever the initial
exponent is smaller than the fuel. Thus `e + 1` suffices for every original input,
including zero exponent and zero modulus. The public theorem retains arbitrary
sufficient fuel. This is exact operational adequacy and local termination, not
an algebraic modular-power identity, optimized bound, compiler-correctness or
whole-run result. No new frame support is needed.

Trust-surface observations from the toolchain inspection are retained explicitly:
stock `Init/While.lean`'s `repeatM` has an `implemented_by repeatM.erased`
annotation, and stock `Nat.powMod` has an external implementation annotation.
The proof uses the original loop's logical definition and checked fixed-point
equation, followed by finite induction; it does not invoke either executable
override as an oracle. No new annotation or nonstandard axiom is introduced.

H5 now has 30 headlines and the campaign 202. The capped 32-thread Progress
build passed (190 jobs), all 30 headline axioms plus three source equations are
standard, and fresh stock Progress kernel replay passed. All 202 campaign
headlines import and pass axiom inspection together; token and
import/root/default-target checks pass. Independent review closed without
mathematical, source or scope findings. Reproduce with
`LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.Statements`
and the same wrapper around `lake env leanchecker --fresh Leanux.Proofs.WG.Progress.Statements`.
Three deterministic elaboration failures (Id inference, match/split normalization,
Boolean simplification) were corrected. No infrastructure rerun, cap failure,
heartbeat change or guest run. Full-gate failure remains inherited, last observed
at `69f988a`. Queue-refill reproduction was not changed or rechecked here; no
accepted witness or affordability of full kernel reduction is claimed. Whole-drain
selection, scheduler progress and operation-end coverage remain open. No new
mirror request arose.

Two bounded read-only reduction trials followed the finite-loop proof. One
concrete original `curve25519 (List.replicate 32 17) basePoint` equation checked
through a proof-required `Option.get` evaluator bridge and `decide +kernel`
(exit 0, about 0.334 seconds, standard three axioms). A separate ordinary
evaluation supplied candidate output bytes; that evaluation was not the proof.
This establishes one needed arithmetic call, not full-run reduction throughput.

The single whole-prefix trial for `executeTrace QueueRefill.concreteTrace`
**failed**, exit 1: stock `cbv`, using the checked original-pow equation as a
local evaluation rewrite, exceeded its simplifier step limit. The failed
elaboration's recovery declaration reported `sorryAx`; no theorem was obtained
or committed. This is not evidence that the target equation is false. The
queue-refill item remains executable-prefix evidence, not an accepted complete
execution or a kernel-checked prefix result. Both trials used capped stdin Lean
with the unchanged memory cap, 32 threads and a 120-second timeout. No timeout,
cap hit, retry, limit increase, rebuild or source-file write occurred. The failed
trial was stopped rather than repeated. Whole-prefix proof remains open.

## H6 — Timer discipline (in progress)

[USER 2026-10-14] Resume the interrupted H6 work, then H5, remaining H4 and
H2 when its prerequisite landing is relayed. The interrupted dirty worktrees
were preserved under snapshot refs without moving branches or working files.

`TimerDiscipline/ArmingSource` proves exact recorded arming, deletion, the
running/live guard, and peer effects of traversal, session derivation, data
receipt and handshake completion. `JitterFrames` proves that every successful
jitter draw is below `HZ / 3 = 83`, including the rejection loop, and frames
the entire kernel. Twenty-two terminal statements include the two authenticated
packet hooks that delete timers and the retransmit callback counter rule. The arm equation uses UInt64 addition and
the signed zero-or-one-tick admissibility gap; it is not a firing-time claim.
All contracts concern original functions on normal completion. They do not
assert that malformed record streams succeed.

`RetrySource` factors retry-mode queueing through the original common suffix and
proves the original retransmit callback's counter transition: counts through
18 increment, including 18 to 19; counts above 18 stay unchanged on give-up.
Normal completion preserves peer allocation identity and the retransmit-timer
field, including rate-limited/dead-peer returns and already-queued reference
balancing. The callback itself does not re-arm retransmission; the worker's
`timersHandshakeInitiated` hook does. Independent review found no issue.
This is not a completed 19-retry episode: actual worker rearming and reset
paths still need composition; dispatcher detachment is now covered below.

The charter's wording needs these source qualifications, with universal
caller coverage still open: “re-arms on every authenticated traversal” means
at the traversal hook with nonzero interval, running device and live peer.
“Once per session” is the session-derived hook's guarded arm attempt; the
retransmit give-up path separately arms absent zero-key timers. The zero-key
callback queues clear work, rather than clearing keys synchronously. None of
these local endpoints proves the absence of other arming sites in a whole
runner execution. The literal once-per-session count remains unproved, not
silently replaced by the local theorem.

Architecture: standalone weakest-precondition contracts, with a local map
composition rule and exact peer-update factorization for handshake completion.
These avoid the inherited shared import failure; existing shared lemmas remain
untouched. `RecordedSiteSource`, `RecordedJitterSource` and `ArmingPrefixesSource` connect the
original caller-read operations and exact wrapped expiry equations to session
derivation, handshake initiation, data sending and traversal. The jittered
sites retain the original read order and prove the jitter bound; traversal
permits an already pending timer. These contracts assume arm-record mode is
enabled, which also admits placeholder reads when that separate mode is enabled;
they do not assert consumption of supplied records. Independent review found no
mathematical defect; the stronger supplied-record wording was corrected.
`RemainingSitesSource` adds the other three concrete arming sites. Data receipt retains
both original decisions. Retransmit give-up includes the attempt-limit decision,
keepalive deletion and staged purge before the absent-zero-key test and arm.
Expired keepalive anchors its residency, running/live and need-another premises
to the actual state after the original `sendKeepalive`; deriving these premises
from callback entry remains open. Its theorem does not frame that send.
Independent read-only review found no issue in these three additions.
`FireSource` factors the complete original timer dispatcher into its actual selection
and detached section suffix, preserving all failure arms. `FireSelectionSource`
proves that every normally completed dispatch selected a resident peer's pending
timer of the worker's kind, due under the mirror's wrapped `timeBefore` test.
`FireRetrySource` carries the callback rule through detachment and actual section
reads: retransmission stays detached during this call. The selected-peer
premise is an actual original-prefix execution. Selection preserves kernel
state but can consume ambient records. One local kernel-state variant of
shared `Keypairs.Frames.peekUnit_spec` avoids editing the shared layer; no layer
is copied. Independent review found no defect in the source factor, frames,
provenance or two terminal scopes. These are individual-dispatch contracts,
not firing-order, whole-run coverage or universal retry-episode claims.
`InitiationArmSource` connects the retransmit arm hook to original
`sendHandshakeInitiation` by an exact source factor, retaining the rate-limit
and creation exits, every intervening operation and all branch logs. Two
terminals expose the reached/skipped continuation and compose the original
caller-read/jitter deadline at the actual post-prefix state. Socket-send
success is not inferred: the caller ignores that return. This does not yet
frame the entire send from entry or count a retry episode. Independent review
found no mathematical or source-linkage defect; its wording correction from
“recorded read” to “original caller-read result” was applied, since armRecords
alone does not exclude placeholder execution.

`JitterRecordsSource` and `JitterExhaustionSource` connect exact supplied one-byte draws
at both timer sites to the original sampler. A contiguous rejected prefix
followed by an accepted byte returns its original scaled value and changes only
the remaining record list; an arbitrary suffix survives. All-rejected finite
streams, including empty input, stop on the extra budget turn with the exact
missing-record error, before budget exhaustion. Ambient interleavings and
recordless placeholders are outside these two contracts; no distribution claim
is made. Independent read-only review found no arithmetic, linkage or World-frame
defect. This closes the restricted exhaustion clause previously removed from
the normal-completion bound's docstring.

`InitiationFrames`, `SendCutFrames`, `SendPeerFrames`, `SendSocketFrames`,
`SendBufferFrame`, `InitiationPreservationFrames` and `SendWorkerFrame` add three
normal-completion terminals. The original initiation-send prefix preserves
identity, attempt count, reference count and retransmit expiry. The final arm
hook may change the expiry but preserves the first three fields. The original
handshake-send worker then releases one reference, preserving residence under
`refs > 1`. Early returns and ignored socket results remain explicit; normal
return does not imply successful transmission. Independent read-only review
found no correctness or scope defect.

[AGENT 2026-10-15] Use result-local retry projections through cache/socket
operations. These fields are absent from campaign 1's keypair snapshot, so its
frame theorems cannot imply them. The two kernel/cut variants are named for the
shared contracts they specialize; the allocation variant names its Noise
counterpart. No existing shared declaration changes. Direct socket expansion
and an initial read/write-contract version hit local heartbeat limits; separate
cache/tunnel/send contracts and reduction of the known optional cache argument
closed the same proposition. One generated peekHiddenSite declaration clash
was resolved by importing the existing timer-selection module. No limit was raised.

The resumed increment connects the worker to original `Env.runOneSendWorker`.
`SendDispatchSource` factors the actual head-or-named selection, one-occurrence
queue erase, pending test/clear, section-start read, original worker body and
section-stop read. Its decorated execution erases exactly to the original,
including every error. `SendDispatchModel` records the pure selection and
before/after-section observations; `SendDispatchClaims` exports projected
contracts, and `SendDispatchFrames` separately proves that peeking preserves
the device and unit associations. Named selection uses the first matching
association; an absent peek is not asserted to mean a recordless stream.
Successful execution derives residency and `handshakePending = true` for the
selected queued peer, with the exact dequeued device before the section and
after its start read. Assuming every resident queued peer has reference count
greater than one, the worker and final state retain its allocation identity and
attempt count, with one reference released. A second headline states this
endpoint directly for original `runOneSendWorker`.

These are 31 H6 headlines and 161 across the campaign. The scoped H6 build
passed (130 jobs), all 31 axiom inspections and fresh stock kernel replay passed,
and combined import/axiom inspection of all 161 headlines passed with only the
three standard axioms. Independent read-only review found no correctness or
source-linkage defect. Wording corrections distinguish a count premise from
reference ownership, existential execution from a uniqueness claim, and normal
return from guaranteed completion. Routine source-factor/bind proof errors were
corrected without weakening statements; no cap failure or infrastructure rerun.
The full gate's inherited failure remains as recorded above, last run at `69f988a`.

`RetryDispatchSource` now connects actual `Env.fireTimer .timerRetransmit`
directly to actual `Env.runOneSendWorker`. The only entry premises are a named
resident device and its empty send queue. The observer runs each existing
inspection at that call's actual entry; the worker starts at the timer's actual
output state. Erasure gives precisely the two original calls, including errors.
`RetryDispatchClaims` exposes the actual selected due peer, timer-selection and
post-timer snapshots, and worker section observations in the pure
`RetryDispatchModel` certificate.

Successful worker selection rules out every empty-queue callback outcome. This
derives the selected peer's entry attempt bound (at most 18), alive/not-pending
flags and positive reference count, rather than assuming them. The callback
increments attempts once and freshly queues exactly that peer with one acquired
reference and a detached retransmit timer. The worker selects that peer and
releases the acquired reference, preserving identity and the incremented count;
the final reference count equals the entry count. `RetryDispatchFrames` isolates
the two queue-preservation lemmas that exclude the give-up branch. This is the
direct original-call pair, not an accepted `runTimers` trace or a scheduler
interleaving theorem. The following increment establishes final queue/pending
preservation; rearming is still needed before iteration into an episode proof.

H6 now has 32 headlines and the campaign 167. The scoped build passed (154 jobs),
all 32 H6 headline axiom checks plus exact erasure and fresh stock replay passed,
and all 167 campaign headlines import and pass axiom inspection together with
only the standard three axioms. Independent review found no mathematical or
source-linkage defect. Two wording findings were fixed: the callback increments
attempts while the worker preserves them, and the timer observation exposes
selection/result rather than separate timer-section start/stop snapshots.
Ordinary elaboration errors were corrected; no cap failure or infrastructure
rerun. The full gate remains the inherited failure described above.

The retry certificate now also concludes that the final send queue is empty and
the selected peer's pending flag is false, without a new entry premise.
`SendView` adds an internal queue/pending observation; socket sending proves
that richer preservation once and projects it to the existing H2/H6 interfaces.
`WorkStateFrames` carries those fields through creation, insertion, MACs, timer
hooks and retained peer release. `SendDispatchWorkSource` proves the substantive
net dequeue effect through the actual start/body/stop execution; it is not a
disposable frame. The same decorated retry execution supplies all certificate
conjuncts. No routing layer or shared campaign-1 lemma was copied.

Validation: affected H6 and H2 builds passed (206 jobs), all 68 affected
headlines plus observer erasure use only the three standard axioms, and fresh
stock kernel replay passed separately for both Statements modules. A combined
`leanchecker --fresh` command was rejected because it accepts one module; the
correct separate invocations passed. This was a command correction, not an
infrastructure rerun. All 170 campaign headlines import and pass axiom inspection
together; the gate's forbidden-token and import/root/default-target checks pass.
Independent review closed after moving the net dispatch-effect theorem from
Frames to Source and updating the headline's scope wording. Ordinary source
elaboration corrections did not weaken the contract. No cap failure or guest
run; the full gate remains failed in the unchanged inherited shared files.

`RetryRearmSource` now decorates that same original timer/send pair with the
actual initiation prefix and pre-release state. Its exact projection retains
the old retry certificate, including the empty queue, pending flag and acquired
reference's release. The new headline has the same entry premises: resident
device and empty send queue. If the observed prefix reaches the arm hook with
a running device, live selected peer and arm-record mode, the actual caller
read and bounded jitter determine the exact wrapped retransmit expiry. That
expiry survives peer release and section stop. The clock-gap claim remains at
the pre-release snapshot, where it was established. These conditions concern
the actual before-arm cut; neither reaching the hook nor successful network
transmission is promised.

`RetryRearmModel` and `RetryRearmClaims` hold the projected certificate and its
source connection. `RetryRearmFrames` isolates expiry preservation through
retained peer release. The retained-reference premise is derived from the
original retry execution, not added to the public statement. No shared layer
or routing proof was copied.

H6 now has 33 headlines and the campaign 181. The capped full-parallel scoped
build passed (162 jobs), all 33 H6 headlines use only the three standard axioms,
and fresh stock kernel replay passed. All 181 campaign headlines import and
pass standard-axiom inspection together; the gate token and import/root/default
checks pass. Independent review closed without findings. Reproduce with
`LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.TimerDiscipline.Statements`
and `capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.TimerDiscipline.Statements`.
No cap failure, guest run or infrastructure rerun. The full gate remains failed
in unchanged inherited shared files, last run at `69f988a`.

`RetrySequenceModel`, `RetrySequenceSource` and `RetrySequenceClaims` now
connect a list of consecutive original timer/send pairs to their actual adjacent
snapshots. Each step retains the existing conditional rearm certificate; exact
erasure preserves original errors, including the first failing pair. Starting
with an empty send queue, normal completion leaves it empty. If every actual
selection names the same initially resident peer, its identity and reference
count are preserved and attempts increase by the sequence length. For a nonempty
sequence, initial attempts plus length are at most 19 and pending is false.
The zero-start corollary excludes 20 successful pairs with that same peer; it
does not assert that a twentieth timer callback fails. The empty sequence
preserves the entire snapshot without an attempt or pending restriction.
There is no existence, scheduler coverage or transmission guarantee.

These files contain claims and exact source connections; no new frame file is
needed. The read-discard equality belongs to exact observer erasure, rather
than arbitrary-state preservation. Independent read-only review closed without
findings. The scoped H6 build passed (165 jobs); all 35 headlines and both
sequence erasures use only standard axioms, and fresh stock kernel replay passed.
All 189 campaign headlines import and pass standard-axiom inspection together;
the gate's token and import/root/default-target checks pass. Reproduce with the
same capped H6 build and replay commands above. A local parser initially rejected
wrapped axiom output; correcting the parser accepted the unchanged output,
without rerunning the checker. No cap failure, guest run or infrastructure rerun.
The full gate remains the inherited failure last observed at `69f988a`.

Scheduler retry-episode counting and source-complete caller coverage for
traversal/session derivation remain open. The dispatch claims do not establish
successful transmission, reference ownership, or that every timer callback is
followed by a rearming send. New claims stay
over the projection and new frames stay separate, pending deletion or retyping
when the split lands. No H6 mirror mismatch has been established; ranked mirror
suggestions: none.

Effort: capped elaboration, repaired syntax/composition errors and one local
heartbeat exhaustion; no memory-cap failure. The give-up proof was split into
exact deletion and purge contracts after combined automation failed. Its device
equation retains both actual tree-map inserts; no structural idempotence is
assumed. The dispatcher factor needed explicit failure-bind equations and a
shared case split on the due list after ordinary elaboration failures; an overly
broad simplification reached recursion depth and was replaced by bounded
rewrites. No resource limit was raised. Scoped build and axiom inspection
passed for the earlier twenty-nine statements using only the three standard axioms. Stock
kernel replay also passes: `capped -- scripts/in-bundle lake env leanchecker
--fresh Leanux.Proofs.WG.TimerDiscipline.Statements`. The full
proof gate remains failed at inherited `CounterWindow/Refinement.lean` and
`ReplayWindow/Counterexamples.lean`;
its token and import checks pass. No full-gate success or complete H6 result is
claimed. No mirror changes or guest runs.

Independent H6 review disposition: no mathematical defect found in the eleven
local contracts. Fixed the traversal docstring's “exactly when re-arms” wording:
the endpoint theorem does not observe arm-event occurrence when an old timer
was already present. Removed the jitter docstring's unproved exhaustion clause;
its proposition only covers normal completion. Added the source qualification
that `createDataDone` invokes traversal once per encrypted item/list, before
its per-packet send loop (`Data.lean:181–194`, C `send.c:242–260`), not once per
individual packet or necessarily a successful transmission. These corrections
change claims in prose, not theorem propositions. Whole-run event coverage and
failure characterization remain explicitly open.
