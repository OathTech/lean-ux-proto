# WireGuard proof campaign 2

## Current checkpoint

**State-split retrofit in progress:** the branch now incorporates main
`b700659`. The previous validation below is historical, over `de62c9d`;
all six results are lagging until carried. Counts, type-justified frame
deletions and scoped validation are tracked in the
[retrofit report](2026-10-16-proof-campaign-2-state-split.md).
The support tranches retype 195 original theorems, retain 114,
delete twenty-one type-given frames and add twenty-four support/finding declarations: 333
checked theorems, with 258 terminal names still awaiting whole-result validation.
Ten H2 table claims now have checked projected support and unchanged public
audit names; this is not a build of the full H2 Statements module.
The frame/claim file map and pending consumers are in the retrofit report.
The [timer carry finding](2026-10-17-proof-campaign-2-timer-carry.md) checks a
counterexample to a pre-wheel exact-peer statement; no mirror repair is requested.
The [peer-release carry finding](2026-10-17-proof-campaign-2-peer-release.md)
checks two counterexamples to a legacy totality domain; no reachable-state
or mirror-bug claim follows.

Historical checkpoint: branch `proofs/campaign-2`, worktree `.worktrees/proofs-campaign-2`,
Lean v4.35.0, mirror **`de62c9d`**. The proofs are **lagging main's
representation batch `cb2348e`**. No merge or push during this resumption.
**None of H1–H6 is complete.** The historical H5 backlog finding is complete;
the other H5 clauses and corrected-main carry remain open.

| Result | Headlines | Established scope | Remaining charter core |
| --- | ---: | --- | --- |
| H1 Noise | 22 | State/slot edges, clearing/rotation, session effects and recorded total success, total initiation creation, consecutive confirmation | Remaining whole-call edges/totality, clock provenance, allocation-lifetime confirmation |
| H2 Index | 52 | Exact index operations, all normal lookup outcomes, caller table safety, session coherence/allocation sequence | Reachable hashed uniqueness and owner/peer residency through all driver entries |
| H3 Roaming | 13 | Authenticated handshake cuts, decrypt/first-poll join, complete poll setter-attempt audit | Queue/callback authentication invariant, broader caller coverage, final endpoint |
| H4 Configuration | 79 | Leaves/flags, effective bounded readback, removal/replacement phase effects, root insertion/transfer, actual two-chunk getter and scalar set/get composition | Global ownership, queued cleanup/completion, mixed attributes, general getter pagination |
| H5 Progress | 42 | Accepted operation boundaries, actual final-boundary backlog, scheduling inspections, cut/pow/drain/poll bounds, arbitrary supplied-record index/jitter-loop adequacy, cookie activation, scheduled resumption and full bounded receive schedule | Whole-worker record decrease, global progress, corrected-main carry |
| H6 Timers | 50 | Seven local arm sites, recorded delays, caller hook compositions, retry bound, pending/absent-zero-key give-up, total recorded retransmit hook, initiation send, retry timer dispatch and named send worker | Complete caller coverage, scheduler episodes, session-relative counting |

**258 headlines**; latest increment: total original named send-worker dispatch
through initiation, rearm and retained reference release.
Scoped builds, axioms and fresh replay pass; independent review found no issue.
The full proof gate remains **failed in inherited campaign-1 files**.

[USER 2026-10-15] Resume before the split: factor claims over a WireGuard-only
view, separate frames, then continue. Delete frames made trivial or unstatable
by the future types; retype substantive claims. No shared-layer edits, merge or
push. This supersedes the pause at `aeece72`; the earlier index-fix merge
authority was already exercised at `de62c9d`.

[USER 2026-10-15] Shared layers remain campaign 1's. Only a few necessary named
local variants may be added; report larger overlaps before copying them.
The [six-family outer-removal request](2026-10-15-campaign-2-shared-frame-request.md)
and [follow-up inventory](2026-10-15-campaign-2-shared-frame-followup.md) remain
pending. The latter covers six H1 reinstallation families (three checked,
three unimplemented), nine additional H2 ingress families, and H4's dependence
on three already-pending removal families. These carries are deferred, not
split into batches to bypass the rule.

[USER 2026-10-14] Write mirror-team requests here and notify the user.
The [three requests](2026-10-14-campaign-2-mirror-requests.md) were notified;
the latest increments add none.

[AGENT 2026-10-15] Use a WG data projection plus separate ambient context,
with execution contracts universal over concrete realizations. Distinguish
normal-return effects, total original return and total inspection. Compose
observations through actual successors; never splice independent existential
runs. Errors have no final state. Public statements name neither `World`
nor `Kernel`.

## Claims, frames and the split boundary

Factoring checkpoint `69f988a` preserved all 153 then-existing headlines.
Paths below are relative to `Leanux/Proofs/WG/`; suffix `.lean` is implicit.
Each result's `Statements` contains public projected claims.
`Campaign2/View` is data-only; `Campaign2/Bridge` defines projection and
universal execution contracts.

| Result directory | Substantive files | Separate structural frame files |
| --- | --- | --- |
| `Noise` | `Model`, `Slots`, state/consume edges; clear, rotation, session and confirmation-sequence `Model/Effects/Source` families; `Execution`, `AccessSource`, `RestartModel`; `SessionReadyModel/Source/Claims`, `InitiationReadyModel/Source/Claims` | `KernelFrames`, `PeerFrames`, `SlotFrames`, `ClearFrames`, `RotationFrames`, `SessionFrames`, `SessionReadyFrames`, `InitiationReadyFrames`, standalone `RestartFrames` |
| `Index` | View/table/owner/allocation/release models; lookup provenance and empty-result source; lifecycle/caller operation sources; session coherence/allocation/sequence effects and sources | `IndexFieldFrames`, `OwnerFieldFrames`, `StoreFieldFrames`, `LifecycleFrames`, `NewlinkFrames`, `SendFrames`, `DispatchFrames`, `ResponseFrames`, `ConsumeFrames`, `StagedFrames`, `ReceiveFrames`, `ClearFrames`, `TimerFrames`, `FlushFrames`, `SessionCoherenceFrames`, `SessionAllocationFrames` |
| `Roaming` | Endpoint/authentication claims; publication, poll endpoint/attempt, response, initiation and handshake-audit model/source/claim families | `Frames`, `PublicationFrames`, `PollEndpointFrames` |
| `Config` | `ClaimView`, models/effects/source claims, observation bridge; allowed-IP removal/insertion/transfer, collision, removal flags, remove-all/replacement, multipart/suffix readback families; `SocketReadbackModel/Claims` and five substantive `SocketReadback*Source` files; `ScalarSocketReadbackClaims/Source` compose original set/get | `ConcreteFrames`, `OperationFrames`, `ReadbackFrames`, `AllowedListFrames`, `AllowedRootFrames`, `AllowedRemovalFrames`, `AllowedPairsFrames`, `QuietFrames`, `LiveRemovalFrames`, `KeyFieldFrames`, `CollisionFrames`, `AllowedInsertFrames`, `RemoveAllFrames` |
| `Progress` | Model/view/source/observation claims; control/scheduler sources; cut, flush-queue, pow, drain and poll-bound model/source/effect/claim families; `RunnerBoundaryModel/Claims`, `IndexProgressModel/Claims` and `JitterProgressModel/Claims` are projected; their `Source` files, `RunnerBoundaryAuditSource` and `BacklogSource` connect original operations; `CookieActivationModel/Source/Loop/Claims`, `CookieSchedulerSource` and `CookieScheduleModel/Source/Claims` | `StackFrames`, `CutFrames`, `FlushQueueFrames`, `CookieActivationFrames`, `CookieScheduleFrames` |
| `TimerDiscipline` | Model/view/send-view/observation claims; recorded, send/retry/rearm/sequence/boundary, pending-give-up, session, data and traversal model/source/effect/claim families; `AbsentGiveUpModel/Claims` and substantive `AbsentGiveUpSource`; `RetransmitReadyModel/Source/Claims`, `SendReadyModel/Source/Claims`, `RetryReadyModel/Source`, `FireReadyModel/Source/Claims`, `WorkerReadyModel/Source/Claims` | `SourceFrames`, `RecordedFrames`, `RecordedJitterFrames`, `SectionFrames`, `SelectionFrames`, `RetryFrames`, `JitterFrames`, `InitiationFrames`, `InitiationPreservationFrames`, `SendCutFrames`, `SendPeerFrames`, `SendSocketFrames`, `SendBufferFrame`, `SendWorkerFrame`, `SendDispatchFrames`, `RetryDispatchFrames`, `RetryRearmFrames`, `WorkStateFrames`, `ResponseSessionFrames`, `SendReadyFrames`, `FireReadyFrames` |

`Index/HandshakeFrames` and `OwnerFrames` are import-only reexports.
`Noise/Basic` reexports access contracts; `Roaming/Basic` reexports endpoint
source. Standalone `Noise/RestartFrames` is outside the headline import closure.
`Progress/ControlLaws` is generic control, not a structural frame layer.

Delete only preservation made trivial by the split. Compound effects that
also establish outputs—generation/deadness, ordered release, cleared-peer
accumulation, dump/UDP payloads—remain substantive. In particular, H4's
arbitrary-kernel-predicate dump/UDP helpers retain output obligations, and H6's
reference decrement belongs in `SendWorkerSource`, separate from preservation.
Source factors are proved equal to original operations; they are not substitutes
for the mirror.

## H1 — Noise session state machine

Checked state edges allow initiation creation/consumption to restart from any
prior state: the machine is not a single linear handshake. Optional next/current/
previous slots do not bound the entire retained key store to three. Initiator
rotation with an existing next key demotes next and puts old current; without
next it demotes current. Responder installation goes to next.

Exact clear/rotation/confirmation effects retain ordered writes, releases,
unhashing and erasure. Normal effects derive evidence from the actual call;
total contracts additionally use static `ClearReady`, counting repeated
releases. Aliases are allowed. An old next/current alias with one reference can
leave a slot naming an erased key; this is an arbitrary-state invariant boundary,
not an accepted-run finding.

Complete normal `beginSession` effects cover allocation, KDF fields,
role/remote index, handshake zeroing, rotation and hashed replacement.
False returns preserve device and allocation cursor, though records may be
consumed. Total success now follows from accepted/live handshake state,
non-null stored peer word, hashed handshake entry, static `SessionReady`, and
an armed successful 40-byte allocation record followed by an 8-byte birthdate
record. Readiness is calculated after the allocator's actual insertion, so it
accounts for overwriting an aliased key's reference count with one. The same
successful original run yields the existing ordered `SessionEffect`; no
execution witness is assumed. Allocation-ID aliases remain allowed, including
ones that erase the new key during rotation. Neither self-owner equality nor
referenced-peer residency is assumed: this mirror's dereference checks only
the non-null word. These facts do not establish final key coherence or
reachability. Birthdate remains existential; exact decoded-clock and final
record-suffix claims, other input outcomes and broader call totality remain open.

The full original `createInitiation` now succeeds under resident-peer/identity,
non-null stored-word and pure crypto guards, with a 32-byte ephemeral record,
16-byte timestamp and any finite collision prefix followed by a fresh index draw.
Collision tests apply after removing this handshake owner's old rows. The result
fixes the returned message, all ordered peer/index writes and exact unused record
suffix; a separate frame preserves the timer-record mode on that same run.
No prior handshake-state, liveness, reference-count, table-uniqueness, self-owner
or referenced-peer-residency premise is required. Crypto guards are named value
predicates; no successful execution is assumed. This does not assert a fixed
message length for arbitrary identity fields, send/rearm behavior or reachability.

For consecutive actual `receivedWithKeypair` calls, the first ID matching
initial next is the sole true result, with the exact confirmation effect;
no match leaves the device unchanged. Duplicates are allowed. Total completion
adds the previous-key release budget only if a match occurs. This is not
confirmation once per allocation lifetime.

[AGENT 2026-10-15] A begin/confirm-only sequence cannot model repeated
installation after successful begin zeroes the handshake tag. A genuine mixed
history needs actual consume/create operations. Three checked restart variants
preserve the relevant cursor/next predicate; release/consumer/creator transport
would complete six shared families and awaits the reported scope decision.
The proposed initial-next-below-cursor condition is design analysis, not a
proved mixed-history result. Whole-call coverage, reachable slot/key coherence
and lifetime confirmation remain open.

## H2 — Session index uniqueness

[AGENT 2026-10-15] “Live” means simultaneously hashed receiving-index owners
within one device. Unhashed retained objects do not reserve their stale number:
C unhashes before release (`noise.c:131–139`, `peerlookup.c:192–197`) and
insertion tests hashed entries (`peerlookup.c:119–163`). Remote indices occupy
a separate peer-supplied namespace. Numeric uniqueness, owner uniqueness and
owner/peer-word residency are distinct obligations.

Lookup stops at the first equal index even if its kind is disallowed.
Every normal successful lookup derives that permitted row, its resident owner
and referenced peer, positive bounded reference acquisition, and the exact
ordered acquisition/store effect. Every normal empty result has exactly one
cause: absent/disallowed first row; resident owner with NULL word; or resident
referenced peer with zero references. The first leaves the device unchanged;
the others retain the exact NULL store, including same-value insertion.
Missing owners, dangling peers and overflow are errors, not empty results.
No table uniqueness, owner=peer identity or deadness premise is smuggled in.

Removal, keypair-specialized removal (`indexRemove (.keypair id)`), replacement,
insertion and release have exact contracts. Replacement preserves numeric
uniqueness; owner uniqueness additionally needs a fresh destination owner.
Insertion removes the previous owner row before installing a fresh number.
Recorded collision/retry/exhaustion contracts retain their contiguous-record
premises; the two-call corpus-draw instance is not general runner coverage.
H5 now also proves exact insertion outcomes and budget adequacy for arbitrary
finite supplied records, including passive and malformed records.

`TablesSafe` combines numeric/owner uniqueness and the hashed-owner allocation
bound. Normal preservation covers lifecycle, send/consume/receive iterations,
clear/timer/drain and post-death removal paths. Session publication coherence
additionally requires a self handshake peer word and exclusion of the allocated
ID from actual rotation releases. True return then leaves a resident one-reference
key in the selected slot, uniquely published at the old handshake index.

Original consecutive `beginSession` calls preserve an initially bounded key
store and derive fresh consecutive allocation IDs for true returns. Cursor
advance equals their count; caller residency comes from actual normal reads.
Rotation aliases may still erase the new key. There is no retained-key lifetime
or completion claim.

Reachable invariants through every driver entry remain open. Outer removal
awaits six shared families; ingress needs nine more (160–230 preservation lines
plus 70–120 composition), with decrypt/NAPI estimated at another 250–400
preservation lines. Most shared contracts omit the observation rather than
being false. [AGENT 2026-10-15] Full reference lifetimes, broader record layouts
and whole-runner witnesses are supporting extensions, not separate H2 targets.

## H3 — Endpoint roaming

[AGENT 2026-10-14] Roaming concerns remote family/address/port/IPv6 scope.
Local source caches legitimately change; endpoint equality ignores flowinfo
(`n1_flowinfo_only.json`). Authentication needs actual consume/AEAD evidence,
not MAC admission or a CRYPTED label alone. The outer source is not an AEAD
input; roaming precedes later inner-packet checks and does not imply delivery.

Decrypt publication retains actual plaintext/key provenance before callbacks.
The first-poll join uses the same execution and matching packet identity,
plus the actual true counter-check result. It does not establish a general
queue invariant, replay-window correctness or packet-peer/key-owner equality.

Both original handshake callers have exact pre-setter cuts. Response facts
derive MAC admission, owner/reference lookup, DH checks, derived AEAD key/AAD,
empty plaintext and consumer commit. Initiation facts derive both AEAD results,
public-key lookup/acquisition, precomputed DH, timestamp `memcmp`, wrapped signed
flood comparison and commit. Separate inspections retain these certificates
through setter or later failure; their original outcome is exact. A cut records
an attempted setter, not completed mutation or an error's final state.

The whole original poll now audits every attempted iteration at its designated
`consumeDataDone` setter site. Records retain actual entry/prefix/continuation
outcomes, including failures; subsequent iterations use actual successors.
Each reached cut derives a resident packet with packet.peer equal to the selected peer ID, CRYPTED status, true counter
result and supported source endpoint. Source equality, audit head equations and
recursion establish retention beyond mere final-outcome equality.
Arbitrary callback writes are outside this site's classification. Persistent
AEAD provenance through queues/callbacks, other callers and final endpoint
preservation remain open.

## H4 — Configuration semantics

[AGENT 2026-10-15] Linux 6.12.110 has no per-allowed-IP removal flag:
UAPI `wireguard.h:188–194`, `netlink.c:329–355`, and
[W1/W2 §2.1](2026-10-06-w1-w2-netlink.md). The obligations use peer REMOVE_ME/
REPLACE_ALLOWEDIPS and device REPLACE_PEERS. This is a statement/version
correction, not a mirror omission.

[AGENT 2026-10-14] Readback means effective clamped/masked/allocated values,
not raw input. Set is nontransactional. Leaves cover validation, no-ops,
removal precedence, identity/cookie keys, peer scalars and expiry. Bounded public
scalar readback uses one resident stopped-device peer, bounded positive reference,
matching selector/key, no allowed IPs, sufficient room and idle socket 7.
168 bytes suffice for the peer fixed part; the outer getter also needs envelope room.

Port contracts distinguish unchanged/nonzero/zero allocation and failure.
Recorded draws remain premises; an occupied first candidate is an outside-domain
stop, not proved retry. Source/cache clearing can precede bind failure; equal
outer requests still increment generation. Fwmark preserves remote destinations.
Private-key effects retain clamping, precomputation, expiry and staged sending;
aggregate timestamps remain existential.
[AGENT 2026-10-15] Collision composition starts after optional self-peer removal:
its flush may change survivors under the old identity. Normal collision effects
use actual acquisition, caller put, removal and installation over that baseline.

Allowed-IP removal has witness-based total contracts and normal converses under
initial peer residency and `NodePairs` (two child slots per resident node).
This is representation shape, not topology, ownership or acyclicity.
Live-key removal retains aliases/multiplicity and reference-count effects.
Full REMOVE_ME derives acquisition, removal and caller release under positive
counts, shape and empty send/clear queues; final erasure occurs exactly when
the original peer reference count was one. Later peer attributes are bypassed,
while invalid flags/protocol are rejected first. The singleton device wrapper
retains selection and generation. Normal REPLACE_ALLOWEDIPS derives its witness,
empties the selected peer's allowed-IP list and balances the lookup reference;
these converses do not promise queued-work completion.

Original remove-all frees allowed IPs, captures the actual post-free peer list,
marks all selected peers dead, then cleans up that same list. Shape and listed
residency at the post-free cut yield first-pass residency/deadness even with
duplicates. Flag-only REPLACE_PEERS composes selection/generation and guarantees
a cut on normal selected-device return. Cleanup stays opaque. Initial-to-post-free
transport uses three already-pending shared families; no renamed copies were added.

Empty-root insertion preserves exact allocation failure/success and sequence
effects; paired actual dumps serialize the masked prefix or omit allowed IPs
after -ENOMEM. Exact root-leaf transfer permits duplicate lists/same-peer
reassignment, retains ordered owner/filter/append writes, and totally reads back
donor/destination with explicit room/cursor premises. These are peer-serialization
claims, not global ownership or full socket getters. One named
`hiddenAlloc_sameKernel_node_spec_variant` avoids importing the inherited
counter failure; the shared original is unchanged.

Two actual peer-getter calls now cover `a :: b :: tail` with only `a ≠ b`,
resident width-32 nodes and no endpoint. First room 168 emits a and splits at b.
The actual returned context feeds room at least `44 + 28 * (1 + tail.length)`,
emitting the whole suffix, clearing allowed-IP cursor/sequence and consuming exact
room. Later repeated IDs are allowed. Original coalescing uses actual fragments;
device remains unchanged. Header, flags, DONE and capacities are supplied.
The complete original socket getter additionally covers one resident peer with
no endpoint and a finite IPv4 list split into a nonempty fitting prefix and a
remaining suffix. Capacity inequalities force two actual chunks of capacity
3776 and leave room for DONE. The continuation ID is absent from the first
prefix; other duplicates remain allowed. Original start creates the first DATA;
the first receive invokes the resumed callback and queues DATA plus DONE; the
second receive and original drain/coalescer return the entire ordered list,
checking repeated device metadata. The device is unchanged, and the socket ends
idle/empty with cleared cursors, zero dump errno and current generation.
The original scalar setter now composes with that two-chunk getter on the same
actual successor. For a stopped device and a positive bounded lookup reference,
the result reads the new preshared key/keepalive interval and unchanged full
IPv4 list. A malformed second peer returns `EINVAL` without undoing the first
update, and the same readback succeeds. Device generation increases once;
the final socket is empty/idle at that generation. Existing selector/socket
frames suffice; no new structural frame was added. Multi-peer/general
pagination, concurrent updates, other setter compositions and reachability are
not established. Global ownership, mixed attributes, final queued cleanup and
total collision completion remain open.

## H5 — Termination and progress

The accepted constructed backlog witness below refutes historical
no-pending-at-completion. Original acceptance and backlog equations are
kernel-checked. A symbolic bridge now proves that this backlog occurs at the
original runner's actual final operation boundary, identifying both syscall and
ambient-strip successors without reevaluating the trace. Runnable backlog uses
the original activation predicate. This is a constructed fixture, not a parsed
or captured Linux run. Main's corrected refusal is not yet carried.

Every accepted original trace now supplies exactly one ordered projected boundary
per operation, with consecutive indices and identical output JSON. Each boundary
has absent/empty hidden records, no suspended activation and no pending NET_RX
signal, after original ambient stripping and guards. This covers file/network
operations and negative syscall returns. Exact source/audit erasure includes
prefill, descriptor/result bookkeeping, output formatting and final placement/
steering checks, including errors. Boundary lists are returned only on successful
whole-trace completion; later errors discard them. There is no pending-work,
worker-queue or scheduled-NAPI emptiness conclusion. Total inspection never
implies successful dispatch or drain.

Source-connected scheduler claims retain actual dispatch/resumption, caller
busy/idle/error and NAPI branches. Cut budgets are derived before ambient
stripping and include the final empty/non-cut observation; allocation rejection
keeps the original error. Send/clear flush removes one queue occurrence,
allows duplicates and retains final reference release/deletion.

The exact 4096-turn drain audit includes original outcomes. Below 4096 queued
items, actual selection/flush effects bound turns begun by count+one and exclude
only its own exhaustion. Worker/selector errors remain possible. Normal full
drain under resident-device/count premises empties both queues; requested-clear
may leave other work. Exactly 4096 removals leave no extra empty-observation
turn: a boundary, not an accepted finding.

Finite modular-power adequacy uses fuel `e + 1` and a checked fixed-point
equation. Original exponent zero returns 1 even modulo 1; unrestricted equality
with stock `Nat.powMod` would be a statement artefact. Poll audit under requested
budget at most MAX_QUEUED_PACKETS+1 excludes its finish-time exhaustion on normal
prefix return: each continued iteration increments count despite arbitrary
callbacks. Queue-test stop can mean an uncrypted head. Unsupported repoll remains.
Neither local result proves callback/internal work termination. General whole-worker
record decrease, detached-activation progress and global progress remain open.

For arbitrary finite supplied records and a resident device, original index
insertion now agrees with a terminating record resolver after unhashing this
owner's old rows. Each collision consumes a strictly shorter suffix, so the
original record-derived budget suffices. Outcomes are exactly an original
hidden-input error or the first fresh index with the exact inserted device
table and unused suffix. The second bucket walk cannot find a stolen index.
Passive records are skipped without payload validation, as in the original
read; wrong-site, malformed and missing input retain their original errors.
No table uniqueness or owner residency is assumed. Recordless placeholder/
domain-filter execution and global scheduler progress remain outside this claim.

Both original timer jitter sites now have the analogous total contract for any
finite supplied record list. Each successful draw consumes a strict suffix,
including skipped passive records; rejected draws recurse on that suffix.
The original length-plus-one budget therefore reaches either the first accepted
jitter below `HZ / 3` or the exact original missing/malformed/wrong-site error.
Success preserves the entire projected state except the unused record suffix.
No device-residency premise is needed. Recordless execution, distribution,
arming and scheduler progress are separate claims.


The complete original receive activation now has an exact outcome for arbitrary
finite supplied records when its queued messages classify as cookies and its
index table is empty. Every packet follows the actual lookup-miss path. The
original list-occupancy-plus-one budget suffices; outcomes are the exact hidden
error or exact queue/counter, five-per-packet decisions, final empty-poll decision
when applicable, suspension and unused suffix. Success consumes a strict record
suffix and either drains the list or yields after exactly one item. The independent
queue counter is subtracted without a consistency premise; an empty list alone
does not imply a zero counter. Cookie classification is an entry queue premise,
not a claim about ingress validation.

For one suspended receive activation and pure record-resolver success, a complete
source-connected original scheduler turn derives the candidate by running the
original probe, excludes dispatch/NAPI branches from the next record, removes the
old activation and commits a successful run on that detached state. It retains
the exact projected effect and strict suffix decrease; no execution-success
witness is assumed. This is one scheduler turn with no caller-held worker, not
whole-schedule termination or fairness. Only two projection equations are frames,
in `CookieActivationFrames`; the remaining files express operational claims.

The full original scheduler now succeeds from a singleton suspended receive
activation, an empty index and a cookie-only queue, with `n` arbitrary eight-byte
reschedule records followed by one arbitrary eight-byte stop record and no tail.
The premise `n ≤ initial queue length` gives exactly enough work for those yields.
The original record budget is `n + 2`: the yielding turns, the draining/stop turn,
and the final no-candidate return all fit. Equality and an initially empty queue
are covered. The exact final projection empties this receive queue, the records
and suspension list, subtracts the initial list length from the independent queue
counter and appends the exact packet/empty-poll decisions. Other work queues and
pending state are preserved, so this is neither global quiescence nor fairness.
No successful-run witness, counter consistency or ingress provenance is assumed.

## H6 — Timer discipline

Local contracts cover all seven concrete arm sites, actual clock-plus-delay
wrapping and jitter below 83. H6's finite draw certificates require contiguous
draws; H5 additionally proves arbitrary supplied-record jitter outcomes and
budget adequacy. General arm-record mode can permit placeholders.
There is no distribution claim. The applicable running/live/interval guards qualify each arm;
a final timer value alone does not prove an arm event.

The original retransmit arming hook is now total for a resident peer and valid
supplied caller/jitter/arm records. Any finite rejected-draw prefix followed by an
accepted draw is allowed. The running/live guard gives either the exact wrapped
expiry, last clock, registration replacement and two guard decisions, or a skipped
arm after consuming the caller and jitter reads. A skipped arm leaves its record,
all timers, last clock and registrations unchanged, with only the guards actually
evaluated logged. The explicit arm-validity premise also applies to that unused
record, so this is narrower than all skipped calls. No new frame variant is needed.
This hook contract does not supply the full send-worker or retry-history proof.

The full original `sendHandshakeInitiation` now succeeds from static guards and
supplied rate-test/last-sent, creation, tail-clock and retransmit records. Its
premises include pure cryptographic guards and tail readiness on the deterministic
creation result: resident live peer, running device, invalid cached cookie, zero
persistent-keepalive interval and no endpoint. Send-buffer allocation is unarmed
and therefore consumes no allocation record. The original no-endpoint send returns
an ignored address-family error; control still reaches retransmit rearming.
The headline establishes exact ordered Device updates, unused record suffix,
recorded mode and final arm clock. It does not claim complete log/registration/
sent-state framing or finish the enclosing worker's reference release. The three
new allocation-mode frames adapt campaign 2's own mode frames; no shared layer is
copied. No successful intermediate execution is assumed. Broader endpoint/cookie/
keepalive cases, dispatcher composition and the full retry history remain open.

The original retransmit `fireTimer` now completes from a recorded nonzero timer
identity whose first matching registration names a due peer, with attempts at
most 18. Static live/not-pending, signed age and bounded positive-reference guards,
recorded cache mode and a matching existing send-work identity establish callback
success. The five explicit records are section start, cache-reset clock, age-test
clock, queue record and section stop; the suffix is arbitrary. Selection may occur
among several due peers. The exact projected result includes timer detachment,
attempt increment, endpoint-source/cache clearing, acquired reference, queued send
work, eight callback decisions, fired symbol and the section-start pending-work
filter. Registrations and all other projected fields are preserved. Queue
consistency and timer-registration provenance are not inferred from the entry
guards. This ends at dispatch completion; the later worker's send/rearm and complete
retry history still require composition. Retaining the pending-work filter corrected
a draft statement assumption, not the mirror.

The original `runOneSendWorker` now also completes from a valid named section,
nonempty queue, selected membership and pending flag. The selected peer need not
be the head. Dequeue erases one occurrence and clears its flag before the actual
section start, initiation/send/rearm and worker `peerPut`; the final stop is then
consumed. Static creation/tail guards are stated on the deterministic post-dequeue
state, with reference count greater than one for retained release. The exact
Device includes that final decrement, and the headline also gives unused records,
recorded mode and final arm clock. It makes no queue uniqueness, full-snapshot,
packet-delivery or all-work-completion claim. The source proof retains the section
start's pending-work filter. No new structural frame layer was needed. A complete
retry pair and repeated scheduler history remain to be composed.

From a resident device and initially empty send queue, original timer/send pairs derive same-peer selection, entry attempts ≤18,
enqueue/reference acquisition, detach, increment and worker release. Consecutive
successful same-peer pairs from zero number at most 19. This excludes 20 such
pairs, not a twentieth callback. The immediate original callback after 19 has
exact all-outcome give-up behavior; normal return preserves identity/count and
empty queue. No intervening scheduler action or later invocation is inferred.

Above the limit with zero-key already pending, give-up is total: retain its
expiry, delete send-keepalive, purge staged packets, add their length to dropped,
and append exact true-give-up/false-zero-key-absent decisions. Hidden records,
clocks, attempts and device queues stay unchanged. No running/live/record-mode
premise is needed.

With zero-key absent, a running device/live peer and two valid contiguous
supplied caller/arm records give total original give-up behavior. It purges
staged packets, accounts drops, deletes send-keepalive and arms zero-key at the
wrapped caller-clock plus delay. The projected outcome fixes all four decisions,
the unused record suffix, last jiffies and registration: unit zero leaves the
registration list unchanged; a nonzero unit replaces all registrations at that
address. Other projected fields are unchanged. These static input premises do
not establish scheduler selection or a session history.

Both response callers observe actual session results; the session-derived hook
is reached exactly on true. Traversal compositions cover outgoing initiation,
outgoing response, common initiation/response receive tails, data completion and
data receipt in their stated contexts. Data completion traverses once per
encrypted item/list before its per-packet send loop (`Data.lean:181–194`,
C `send.c:242–260`), not per packet/transmission. Successful nonkeepalive sends
control data-sent; nonzero received length controls data-received. Guarded
recorded expiry is established at each actual hook cut. These normal caller
certificates do not retain later failures or promise final expiry/delivery.
Common response traversal does not require session success.

Zero-key firing queues clearing; it does not immediately erase keys.
Give-up can also arm zero-key for a partial exchange, so two session-hook proofs
cannot establish once-per-session. Complete caller coverage, scheduler episodes
and mixed-history/session-relative arm counts remain open. No H6 mismatch found.

## Findings and mirror requests

The [request document](2026-10-14-campaign-2-mirror-requests.md) ranks all three
changes as altitude-preserving. No mirror/kernel edit or upstream report occurred.

| Finding | Evidence and limit | Status |
| --- | --- | --- |
| H5 batch backlog | Kernel-checked accepted constructed fixture and backlog, with symbolic proof locating it at the actual final runner boundary; not parsed/captured Linux | Historical over de62c9d. Main `9db558b` adds completion guard; corrected refusal/carry open |
| H5 nested refill | Evaluated initialized prefix/source review; operation 4 reaches worker occupancy-budget invariant; later suffix incomplete | Neither accepted complete trace nor kernel-proved prefix; callback-aware bound requested |
| H4 dump cancellation | Accepted getter, kernel-checked internal room 3720 versus source-derived C 3724 | Restore pre-nest snapshot; no demonstrated compared-output mismatch. Dead-cursor extension only inspected |

Alias examples, statement qualifications and the 4096 boundary are not
accepted-run findings. H1/H2/H3/H6 have no ranked mirror-change request.

## Validation and trust limitations

Latest six-target build passed **482 jobs**. All **258 headlines** and eight new
worker-ready supports use only the three standard axioms; token/import/root/default/
projected-name checks pass. Independent read-only review found no issues. Fresh
TimerDiscipline replay passed. New tracked/untracked whitespace checks passed
before the final build. Author Source/Statements builds passed 170/264 jobs.

Retained-put/handshake-worker prototype: three capped stdin compilations, two
passes and one corrected Boolean-guard failure. Dispatcher prototype: seven
compilations, two passes and five corrected failures, including wrong draft
section constants corrected to the original named sites. One failed draft's
diagnostics and compressed copy were truncated by an insufficient tool-output
budget and lost. That unchanged source was not rerun for diagnostics; subsequent
outputs were fully captured. Both packaging builds passed, with stock limits,
unchanged memory cap and no infrastructure or unchanged-source diagnostic rerun.

The preceding timer-dispatch checkpoint `403fa0d` passed 479 build jobs, all
257 headlines and 12 supports on standard axioms, fresh TimerDiscipline replay
and independent review. Its callback/scaffold/specialization and corrected
packaging failures are counted in that commit.

The preceding initiation-send checkpoint `b90f9bb` passed 473 build jobs, all
256 headlines and 11 supports on standard axioms, fresh TimerDiscipline replay
and independent review. Its prototype and packaging counts are in that commit.

The preceding cookie-schedule checkpoint `8055612` passed 469 build jobs, all
255 headlines, 15 new and four existing supports on standard axioms, fresh
Progress replay and independent review. Its seven prototype calls had three
passes and four corrected failures; all three packaging builds passed.

The preceding initiation checkpoint `5ee787c` passed 465 build jobs, all 254
headlines and 29 new supports on standard axioms, fresh Noise replay and review.
Its source uses an 800000-heartbeat budget unchanged throughout the retained
continuation; earliest prototype budget provenance is unconfirmed, as recorded
in that commit. Memory cap was unchanged.

The preceding H5/H6 checkpoint `daa1b10` passed 461 build jobs, all 253 headlines
and 41 supports on standard axioms, both fresh replays and independent reviews.
Its compiler counts and corrected drafts are in that commit. The diagnostic
rerun violation below remains explicitly recorded; it was not infrastructure.
The earlier socket-getter review found a headline attribution error, corrected:
the callback returns DATA; the enclosing socket dump appends DONE and finalizes.
Earlier closed increments also passed
affected scoped builds, axiom checks and fresh replay; counts, corrected draft
failures and review dispositions are in their commits. Reviews did not rerun
reported validation. All review findings were fixed, including unconditional
source correspondence, explicit supplied dump envelopes and cursor-reset scope.
Standalone H1 restart support separately passed 116 jobs, seven declarations
and fresh replay; it adds no headline.

Full gate last actually ran at **`69f988a`: failed** in inherited
`WG/CounterWindow/Refinement.lean` and `WG/ReplayWindow/Counterexamples.lean`
(counter operands/index-owner carries). Campaign 1 owns repair. Scoped passes
are not a full-gate pass; existing shared lemmas were not edited.

**Two infrastructure failures, one rerun each:** `84355d1` import overlapped
rebuild and missed ReceiveFrames.olean; `9019ca8` repeated that orchestration
mistake while Config Statements rebuilt, missing its object. Each sole rerun
after confirmed build completion passed. Build and dependent import/axiom
checks are now sequential, including docstring changes.

The absent-zero-key increment also repeated a successful Lean axiom invocation
after its output parser failed. A second invocation failed on an unsupported
printing option; the third repeated the first input and passed. This was
redundant checking, not an infrastructure retry. [AGENT 2026-10-15] Root now
owns central axiom-output checks; parser repairs reuse captured output instead
of repeating successful Lean invocations.

**Separate cookie-loop diagnostic rerun violation:** after a failed scoped
`CookieActivationLoop` build, the author reran unchanged source through
`lake env lean -Dpp.structureInstances=false -Dpp.proofs=false` to read goals
truncated from the first output. Both exited 1; this was not infrastructure and
was not an allowed retry. Source corrections to monad/case reduction and loop
composition then passed. Diagnostic output must be retained and read from the
original invocation; changing printing options does not authorize a rerun.

**Separate process violation at `314d13e`:** an unconditional dependent build
repeated an unchanged failed REPLACE_PEERS source draft. This was not
infrastructure or a permitted retry. Launch control was corrected; neither
failure was accepted. There have been no cap hits/increases, guests or guest
timeouts. Ordinary corrected elaboration failures remain failures, documented
in commits. Earlier deterministic-limit accounting is in those commits; the
initiation investigation has the budget-history uncertainty stated above.

One bounded trial kernel-checked original curve25519 through the finite power
bridge (about 0.334 s). A separate single full QueueRefill reduction trial failed
at stock simplifier-step exhaustion with exit 1; its recovery printed sorryAx.
No theorem was obtained/committed, no retry or limit increase occurred.
The small bridge proves neither full-prefix throughput nor trace acceptance.

A separate sessionless H6 episode prototype evaluated the initial send and one
retry, but its full kernel-reduction proof failed with an application type
mismatch; recovery reported `sorryAx`. No theorem or mirror finding was accepted,
and the full attempt was not repeated or given larger limits. Seven stdin
trials comprised two successful stage evaluations, three elaboration failures,
one corrected missing-record failure and that failed full proof. This leaves
the twenty-initiation scheduler episode and mixed-history arm count open.

Stock `repeatM` has `implemented_by repeatM.erased`; stock `Nat.powMod`
has an external implementation annotation. Proofs use logical definitions,
checked equations and induction, not executable overrides as oracles.
No project axiom or forbidden trusted declaration was added.

The H5 runner increment used 16 implementation builds, with nine corrected
failed drafts (source/prefill normalization, case-rewritten equalities, range
normalization, explicit witnesses and initial-state reduction). A sub-agent
usage-limit interruption left the tree preserved at snapshot `ab0c13c`; root
completed the bridge and projected claims. No build was active at takeover; no
infrastructure retry, limit increase or new structural frame was needed.

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
# Standalone support, not imported by the headline modules:
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Noise.RestartFrames
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Noise.RestartFrames
# Full gate: expected inherited failure, not reported as a scoped pass:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The gate already supplies the headline discovery/axiom-check procedure; no
additional audit infrastructure was introduced. After the split lands by paste,
retype claims and delete structural frames that the new types make unnecessary.
