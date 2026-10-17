# WireGuard proof campaign 2

## Current checkpoint

**Campaign-owned state-split retrofit complete over b700659.** Main was incorporated on
the campaign branch; the mirror and existing shared layers remain unchanged.
The branch retains its proof target and gate. All six terminal closures now check; subsequent charter work uses the split projection.
Main's subsequent b3f56807 documentation-only review/proposal update is also
merged; the executable mirror remains byte-identical to b700659.

| Result | Headlines | Checked support | Split status |
| --- | ---: | ---: | --- |
| H1 Noise | 34 | 264 | Full terminal closure, all seven whole-call tag maps, their actual finite mixed histories and session derivation-clock receipt current; direct helper reinstallation refutes unrestricted repeat-confirmation uniqueness; successful confirmation IDs are distinct across actual finite histories of all four handshake create/consume calls, session installation/confirmation, clearing and expiry under an explicit initial next/cursor bound; broader driver/lifetime closure remains separate. |
| H2 Index | 91 | 491 | Full terminal closure and ingress/expiry/handshake/peer-creation owner coherence and whole-removal lifecycle finding/slot-covered arbitrary-AIP preservation and actual clear-work dispatch and both-mode handshake queueing and new-handshake/zero-key/retransmit callbacks and persistent-callback and successful-session slot-alias invariant counterexamples and positive publication-to-lookup handoff under explicit rotation freshness current; core named-operation H2 coverage checked; whole initialized driver/lifetime closure is a separate stronger scope; aggregate gate inherited-blocked. |
| H3 Roaming | 20 | 213 | Full terminal closure and invalid-MAC1/rate-limit/admitted-response/initiation rejection and cookie-message and whole data-admission endpoint preservation and actual first pre-put NAPI owner/packet authentication under the publication owner-head condition current; later polls, persistent queue provenance and broader caller coverage open. |
| H4 Configuration | 104 | 830 | Full terminal closure, actual mixed/key setter paginated readback with arbitrary endpoints, whole finite single-peer mixed-width getter and actual finite empty-IP peer getter and exact arbitrary-room empty-IP serializer/whole normal cursor callback and actual mixed/key setter composition with exact DATA/DONE count and arbitrary endpoints and arbitrary finite empty-IP multi-peer scalar and mixed fwmark/scalar set/get and actual endpoint set/weighted readback current; global ownership, queued cleanup, general mixed setters, mixed peer/allowed-IP pagination open. |
| H5 Progress | 53 | 349 | Full terminal closure, exact bounded outcomes and recorded batch, actual timer completion guards and recorded idle/post-advance wait completion and actual advance-syscall/runner linkage and send-worker completion guard and four final-idle syscall/runner receipts and exact all-mode finite allocation and successful modular-power evaluation bridges and actual activation-exit inspection current; global progress/coherent-ring adequacy open. |
| H6 Timers | 65 | 502 | Full terminal closure, actual retry blocks and allocation-labelled guarded session-arm events with outgoing call-entry origin and initialized give-up runtime witness with checked concrete curve outputs and all five syntactic traversal call sites covered by six observer branches with all-mode immediate effects; upstream data authentication, broader caller histories and session-relative counts remain open. |

The checked surface is 2,649 theorems in all 924 campaign-owned modules.
The completed retrofit accounts for 1,983: 1,321 retyped, 244 explicitly
corrected, 239 retained and 179 added support/finding declarations. One hundred fifty-eight
subsequent H2 declarations add table preservation and local owner coherence.
Seventy-nine H1 declarations add whole-operation and finite mixed-history tag ownership, actual derivation-clock provenance, direct-helper reinstallation and bounded fresh-installation confirmation history; two hundred forty-eight H4 declarations
add mixed fwmark/scalar, ordered peer-attribute, port-refusal/private-key readback and finite IPv4 getter/setter pagination and actual fitting multi-peer readback and complete finite single-peer mixed-width pagination plus actual finite empty-IP peer pagination with ordered cursor handoffs and complete receive/coalescer composition. Fifty-six H3 declarations
add invalid-MAC1, rate-limit and admitted-response/initiation rejection, cookie-message and whole data-admission endpoint preservation, plus actual first pre-put NAPI owner selection and conditional packet authentication. Sixty-one H5 declarations
establish recorded batch, actual timer completion guards and recorded idle/post-advance wait wheel completion and the actual send-worker completion guard and four final-idle syscall/runner links, exact finite evaluation and actual bounded activation exits. Sixty-four H6 declarations
connect actual timer-loop receipts, contiguous retry-block counts/bounds, local partial-exchange arming and allocation-labelled session-arm events, plus concrete original curve outputs. Of the 1,831 baseline theorems, 22 frames
were deleted because types supply their facts and five false cookie supports
were separately retired with checked counterexamples. No baseline declaration
remains awaiting retrofit; all 258 original terminal names/order survive,
with twelve new H1 headlines, thirty-nine new H2 headlines, seven new H3 headlines,
twenty-five new H4 headlines, eleven new H5 headlines and fifteen new H6 headlines (367 total).

The [retrofit report](2026-10-16-proof-campaign-2-state-split.md) records
claim/frame files, corrections, before/after counts and validation.
The retrofit's scoped builds and complete 2,980-root standard-axiom audit pass.
All seven final fresh replays pass. The full gate **fails** in inherited
CounterWindow.Refinement and ReplayWindow.Counterexamples; their old state
shapes and failed-elaboration diagnostics remain campaign 1's responsibility.
No shared lemma or mirror implementation was edited. The campaign-owned
retrofit is not a claim that the full gate or any entire charter result passes.

None of H1–H6 is a completed charter result. The timer retry-sequence contracts
concern supplied wheel units and their actual inspection. The first-turn and whole-episode
contracts now connect actual outer selection and every executed turn to their
unchanged continuation/finish. A contiguous qualifying same-peer block now has an
actual-history retry bound at its last send exit; arbitrary mixed histories and
session-relative counting remain open. No new
mirror-team request arises from these statement-domain findings.

## H2 continuation: confirmation preserves the index invariant

The original receivedWithKeypair now preserves numeric-index uniqueness,
embedded-owner uniqueness and the hashed-keypair allocation bound through
both false exits, ordered slot writes and immediate old-previous release.
The claim keeps an optional device and arbitrary Ambient inputs; it adds no
residency, distinct-slot, reference-budget or successful-confirmation premise.
Failures remain outside its normal-return conclusion. This is one missing
confirmation edge toward whole-driver propagation, not owner-word coherence,
reachability or complete H2 coverage.

Architecture: Index/ConfirmationClaims uses the campaign projection directly
and composes existing get/branch/peer-write/key-release contracts. Existing
frames stay in their separate files; no shared-layer variant is added.
Index/Statements appends one documented headline without changing the prior
52. H2 now has 53 headlines and 335 theorems; the campaign has 259 headlines
and 1,985 theorems. No existing statement is reshaped and no new finding occurs.

The first capped probe passes at the default limit. The scoped Index.Statements
build passes 257 jobs; its only warning is inherited Env:865 String.mk.
Axioms: 995 logical roots in 193 modules, including 644 public theorem roots,
standard only. Fresh kernel replay passes. Static checks and original-name
order pass; independent review finds no issue. No limit/cap increase, failed
probe or infrastructure rerun. The full-gate failure in inherited
CounterWindow/ReplayWindow remains as recorded; it is not rerun unchanged.
Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 threads and 16 QEMU slots.

No mirror change is requested for this step: existing narrowed operations and
proof contracts suffice. The next bounded obligations are lookup preservation
of an explicit hashed-owner coherence predicate and data-ingress table safety.

## H2 continuation: local hashed-owner coherence

A separate pure predicate now relates every hashed owner to a resident,
positively referenced peer. Handshake owners point to their containing peer;
keypair owners also name a resident, positively referenced keypair. It does
not require unique rows, a live isDead flag, an upper reference bound or
distinct IDs. It is a local entry invariant, not a reachable-state theorem.

Native lookup preserves that invariant on every normal return. Absent or
disallowed rows leave the device unchanged; NULL/zero-reference empty causes
contradict the supplied invariant. A successful lookup uses the actual
peer-reference increment followed by same-word owner storeback, handling aliases
through pointwise lookups without asserting TreeMap representation equality.

Allocation preserves the joint table-safety and coherence predicates. The
hashed-owner allocation bound prevents overwriting a hashed keypair; existing
unhashed objects may be overwritten and the new peer word may be arbitrary or
NULL. The new object is not yet published. Refusal and absent-device behavior
are retained under normal-return semantics, without completion or lifetime claims.

Removal and its actual keypair specialization preserve coherence and are total
for a present device. Insertion preserves it on normal completion when the
newly published owner is explicitly coherent. Handshake replacement is total
with an explicitly coherent destination keypair; its exact Boolean/table effect
allows existing destination rows, so this theorem does not assert owner
uniqueness. These publication premises are obligations for callers, not inferred
reachability facts. All claims use the native projection.

Architecture: OwnerCoherenceModel holds the three predicates; OwnerCoherenceFrames
and OwnerCoherenceAllocationFrames hold preservation facts; TableEffects holds
the three pure table transformations. Source/Claims files connect them to the
actual operations; six literal terminal wrappers are appended in Statements.
The existing own-result liftSkb_tables helper is made public without changing
its body for the forthcoming ingress proof; no theorem is added by that change.
Its eleven affected modules are all within Index and covered by the check.
No existing shared lemma or mirror function is edited.

This tranche adds 21 theorems: lookup seven, allocation three, table primitives
eleven. H2 has 59 headlines and 356 checked theorems; campaign totals are
265 headlines and 2,006 theorems. Existing claims are not reshaped. Global
reachability, complete driver-entry propagation and release ownership remain
open. No new mirror request is needed; the narrowed types and actual source
contracts suffice for these local obligations.

Development: lookup probe 1 fails three diagnostics with two unused-simp
warnings; changed probe 2 passes. Allocation probes 1 and 2 fail three and
five proof/import/projection diagnostics; changed probe 3 passes. Primitive
probes 1 and 2 each fail one proof-form diagnostic; probe 3 passes. The first
terminal packaging build fails four syntax errors because extraction stopped
at a record-field assignment; corrected extraction fixes them. All final
new proofs use the default limit, without warning suppression or cap changes.
Independent review of all three packages finds no correctness/domain issue
and identifies the need for literal terminal wrappers, which are supplied.

The promoted helper builds in 137 jobs; lookup integration passes 261 jobs.
The final combined Index.Statements build passes 265 jobs, with only inherited
Env:865 String.mk. Axiom inspection checks 1,020 logical roots in 201 modules,
including 666 public theorem roots, using only standard axioms. Fresh replay,
static checks, original 258-name order and mirror/shared boundaries pass.
No infrastructure rerun or unchanged failed-source rerun occurs. The inherited
full-gate failure remains recorded and is not rerun unchanged.

Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: data-ingress table preservation

The actual consumeData now preserves numeric-index uniqueness, embedded-owner
uniqueness and the hashed-keypair allocation bound on every normal return.
The only entry premise is TablesSafe; optional device, arbitrary Ambient inputs,
aliases, malformed objects and queue states retain their actual stopped outcomes.
Lookup, NULL/keypair acquisition, dead-peer cleanup, skb allocation, device/peer
enqueue, EPIPE publication and unsuccessful-enqueue cleanup all remain in the
source order. The short-circuit enqueue condition is the actual WG.orM.

Architecture: Index/RxQueueFrames contains two receive-queue preservation
contracts, named as local variants of WGMore.enqueuePerDeviceAndPeerRx_spec
and enqueuePerPeerRx_pure_spec. They reuse the guarded skb-store adapter and
existing reference/release contracts. Index/ReceiveDataClaims contains the projected source claim, composed
through proof-local factors whose equality to consumeData is reflexive.
Index/Statements appends one literal headline. The publication frame covers
the actual empty WG callback in consumeData, not arbitrary interrupt callbacks.
Full packetReceive/wgReceive, decrypt/poll workers and environment closure remain
open. This does not establish owner coherence or reachability.

The split removes the need for separate skb allocation/update/free frames:
their SkbM types and the existing guarded adapter supply table preservation.
This tranche uses two substantive queue families from the old ingress inventory,
not the broader worker layer. No shared lemma or mirror operation is edited.
No existing claim is reshaped; four new theorems bring H2 to 60 headlines and
360 theorems, and campaign totals to 266 headlines and 2,010 theorems in 598
owned modules. No mirror change is requested.

Development: probes 1–3 fail five, 101 and two diagnostics respectively
(composition, malformed pair-case tactic, then matcher branches). Probe 4
reaches the default heartbeat limit. Probe 5 has ambiguous orM/factor errors,
two default-limit failures and one warning; probe 6 has two default-limit
failures. Probe 7 has two unspecified-intermediate-predicate errors and two
unused-simp warnings. Changed probe 8 passes cleanly after explicit local source
factoring. An earlier package-generation search fails before Lean because the
reused skb helper had been promoted from private. No limit/cap increase, warning
suppression, infrastructure retry or unchanged failed-source rerun occurs.

Final scoped Index.Statements build passes 267 jobs; only inherited Env:865
String.mk warns. Axiom audit checks 1,024 logical roots in 203 modules, including
670 public theorem roots, standard only. Its first fresh replay passes; after
renaming the two frames as shared-lemma variants, the 267-job rebuild also
passes. Final combined replay is reported below. Static
checks, original 258-name order and mirror/shared boundaries pass. Independent
review finds no correctness/domain issue and confirms the callback restriction.
The inherited full-gate failure remains recorded, without an unchanged rerun.
Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under capped
with 32 Lean threads and 16 QEMU slots.

## H2 continuation: coherence needs release ownership

The proposed unrestricted preservation of OwnerCoherentSafe by peerPut is
false. A checked native witness starts with peer 0 and keypair 0 each at
reference count 1, keypair.peer = some 0, one hashed keypair row at index 7,
and empty queues/timers. Every actual WG/Ambient realization of that device
returns normally from peerPut (some 0): it removes the handshake owner if
present, erases peer 0 and retains the keypair row/object. The initial device
is coherent under the local predicate; the final device is not.

[AGENT 2026-10-17] Classify this as a statement-domain artefact: the predicate
omits reference ownership and release/unhash ordering. The witness does not
establish reachability, an accepted runner trace or a mirror/kernel defect.
No existing theorem is weakened or retired, and no mirror repair is requested.

A second checked theorem characterizes the missing obligation exactly for
the pure last-release device effect. Under initial hashed-owner coherence
and p.refcount = 1, final coherence holds iff every retained hashed owner
does not name the released peer. Other handshake owners already satisfy this
under coherence; retained keypair owners supply the substantive obligation.
This pure equivalence needs no resident-peer premise. Applying it to the
actual release still requires the resident peer and actual normal outcome;
the theorem supplies neither readiness nor reachability.

Architecture: Index/OwnerCoherenceReleaseFindings holds the native witness;
OwnerCoherenceReleaseFrames holds the pure preservation equivalence.
Statements appends two literal documented headlines. Four new theorems bring
H2 to 62 headlines/364 theorems and the campaign to 268 headlines/2,014 theorems
in 600 owned modules. The completed retrofit counts remain unchanged.

Finding probe 1 fails three record-layout syntax diagnostics; changed probe 2
passes. The equivalence's probe 3 fails four lookup/case goals and four
unused-simp warnings; changed probe 4 passes cleanly. No limit/cap increase,
warning suppression or infrastructure rerun occurs. Independent review finds
no correctness/domain issue and confirms the pure/operational distinction.

The final combined Index.Statements build passes 269 jobs; only inherited
Env:865 String.mk warns. Axiom audit checks 1,028 logical roots in 205 modules,
including 674 public theorem roots, standard only. Fresh kernel replay passes.
Static checks, original-name order and mirror/shared boundaries pass.
The inherited full-gate failure remains recorded and is not rerun unchanged.
Reproduce using the same scoped Index.Statements build and fresh replay
commands above, under capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: removal and conditional release coherence

Original removeByPeer and outer peerRemove now preserve table safety on
every normal return, with only TablesSafe at entry. The removal frame keeps
the exact optional (indexTable,nextKeypairId) pair. It uses the actual
allowedipsList snapshot, ordered listDel operations, every malformed-node
branch and the original pubkey-removal branch before marking the current
peer dead. Outer removal retains NULL handling, key clearing, actual worker
flushes, crypt-work refusals and final peer release through the existing
after-dead contract. No NodePairs, residency, readiness or owner-coherence
premise is added; no completion or owner-coherence conclusion is claimed.

The split supplies preservation for slotSet/subtree through their AipM types
and a guarded liftAip adapter. Only two mixed-WG removal families remain
necessary here. Index/AipRemovalFrames has three local variants of campaign
1's hoare_liftAip, removeByPeer_spec and peerMakeDead_spec, following its
native lift shape. Index/PeerRemovalClaims holds the two projected claims.
The broader rootRemovePeerLists/free and peerRemoveAll layer remains pending;
this package does not copy it or establish H4's general ownership transport.

The actual peerPut also has a normal-return owner-coherence contract using
the checked release obligation. It requires the actual resident positive
peer and explicitly requires every retained hashed owner to be detached on
last release. Nonfinal decrement preserves coherence without detachment:
the actual resident peer retains positive count and its embedded word.
Queue/timer refusals remain actual stopped outcomes; no readiness premise
is supplied. Index/OwnerCoherenceDecrementFrames holds the pure frame and
OwnerCoherenceReleaseClaims the projected source contract. This derives no
reachability or global reference-ownership invariant.

Three literal documented headlines are appended. Seven removal declarations
and three conditional-release declarations bring H2 to 65 headlines/374
theorems, and campaign totals to 271 headlines/2,024 theorems in 604 modules.
No existing claim is reshaped, shared lemma or mirror code edited, or mirror
change requested. Independent reviews of both packages find no issues.

Removal probe 1 fails record syntax, a projection mismatch and broad
automation at the default heartbeat limit. Probe 2 fails remaining record
syntax/liftM leaf mismatches and has one binder-name warning. Changed probe 3
passes the adapter/removal frame; probe 4 passes all five support/claim
declarations cleanly. Conditional-release probe 1 fails a nested-run rewrite
and reports one deprecation warning; probe 2 fails an Except.map reduction;
changed probe 3 passes cleanly. All final new proofs use default limits,
without cap/limit increases, suppression or infrastructure retries.

Final scoped Index.Statements build passes 287 jobs, with only inherited
Env:865 String.mk warning. Axioms: 1,156 logical roots in 223 modules, including
763 public theorem roots, standard only. Fresh kernel replay passes. Static
checks retain all 258 original names/order; mirror/shared boundaries pass. The inherited full-gate failure remains recorded and
is not rerun unchanged. Reproduce with the scoped Index.Statements build and
fresh replay above, under capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: keypair release preserves owner coherence

Original keypairPut preserves local hashed-owner coherence on every normal
return, with that invariant as its sole entry predicate. The key argument,
immediate-unhash flag, optional device and Ambient inputs are arbitrary.
Last release unhashes all rows for the key before erasing it; retained hashed
keys keep their peer word and positive count. Peers are unchanged, so no
peer-release detachment obligation is needed.

The source proof retains NULL input, absent device, missing key, zero count,
immediate-unhash dereference and deferred final-NULL refusal. A deferred
nonfinal key with a NULL word may return normally; the proof uses the existing
retained-key contract rather than imposing the non-NULL premise of the
stronger total exact-effect helper. No reference upper bound, readiness,
freshness or object-residency premise is added to the projected theorem.

Architecture: Index/OwnerCoherenceKeypairReleaseFrames holds pure preservation
of the actual resident/live key effect. OwnerCoherenceKeypairReleaseClaims
derives the actual normal-run cases and applies it; Statements appends one
literal documented headline. These three new theorems bring H2 to 66
headlines/377 theorems, and campaign totals to 272 headlines/2,027 theorems
in 606 modules. No existing claim is reshaped or shared/mirror code edited.
This does not establish global ownership or reachability. No mirror request
is needed.

Probe 1 elaborates with two unused-simp warnings; changed probe 2 fixes them
and passes cleanly at default limits. The warnings are fixed before
integration, without limit/cap increases, suppression or infrastructure retry.
Independent review finds no correctness/domain issue, including the retained
NULL-word case and the distinction from peer release.

The scoped Index.Statements build passes 289 jobs, with only inherited
Env:865 String.mk warning. Audit checks 1,159 logical roots in 225 modules,
including 766 public theorem roots, standard only. Fresh kernel replay passes.
Static checks retain all 258 original terminal names/order; mirror/shared
boundaries pass. The inherited full-gate failure remains recorded without an
unchanged rerun. Reproduce with the scoped Index.Statements build and fresh
replay commands above, under capped with 32 threads and 16 QEMU slots.

## H2 continuation: session-wide hashed-owner coherence

Every normal beginSession return now preserves coherence of all hashed
owners. Entry requires the actual resident caller, hashed-keypair owner IDs
below the allocation cursor, the existing SessionRotationFresh condition,
and local hashed-owner coherence. No table uniqueness, whole-store freshness,
self peer-word, positive-caller, reference budget, readiness or successful-result
premise is added.

The false return retains the device. On success, the actual SessionEffect
supplies a surviving handshake row. Rotation's exact handshake-membership
equivalence places that row in the entry table; coherence derives the caller's
self peer-word. Coherence of the surviving row after rotation supplies the
resident positive peer for the new key's publication. The allocation bound
prevents overwriting a hashed key; unhashed allocation-ID objects remain
allowed. Rotation freshness excludes only releases of the new key ID.
All other slot aliases and repeated releases retain their actual semantics.

Architecture: Index/OwnerCoherenceSessionFrames holds resident-peer write,
prepared-device and RotationRun preservation; OwnerCoherenceSessionEffects
composes the exact successful/false device effects; OwnerCoherenceSessionClaims
connects them to the native operation through the projection. Statements
appends one literal headline. Six new theorems bring H2 to 67 headlines/383
theorems and campaign totals to 273 headlines/2,033 theorems in 609 modules.
No existing claim is reshaped or mirror/shared layer edited. The static
freshness/bound obligations remain unproved reachability conditions, and
whole-driver H2 is still open. No mirror change is requested.

Probe 1 fails four case-rewrite goals without warnings. Changed probe 2
passes all five support/claim declarations cleanly at default limits.
Independent review finds no correctness/domain issue, including derivation
of the self-word and positive-peer facts from the actual publication row.
No limit/cap increase, warning suppression or infrastructure retry occurs.

Scoped Index.Statements build passes 292 jobs, with only inherited Env:865
String.mk warning. Audit checks 1,165 logical roots in 228 modules, including
772 public theorem roots, standard only. Its final replay is included in the
combined checkpoint below; original-name/order and boundary checks pass.
The inherited full-gate failure remains recorded, without an unchanged rerun.
Reproduce with the scoped Index.Statements build and fresh replay commands
above, under capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: confirmation and clearing preserve owner coherence

Original receivedWithKeypair and keypairsClear each preserve local coherence
for all hashed owners on every normal return. Coherence is the only entry
predicate; the optional device, caller IDs, slot aliases and Ambient inputs
remain arbitrary. The actual first peer read supplies the source effect's
residency, while each successful put supplies its resident/live/word facts.
Missing objects and refused releases remain Stops.

Confirmation's false branch retains the device; its true branch uses the
checked ordered rotation. Clearing follows each evolving resident peer and
its actual put, including repeated or aliased slot IDs. Neither claim promises
completion, positive references for every slot, or global reachability.

Architecture: Index/OwnerCoherenceClearFrames proves pure ClearRun
preservation using the peer-metadata write and key-release frames.
OwnerCoherenceKeypairCallerClaims applies actual source effects through the
projection. Two literal terminal headlines are appended. Five new theorems
bring H2 to 69 headlines/388 theorems. Existing claims remain unchanged.
No shared/mirror edit or mirror request is needed.

Probe 1 fails dependent ClearPut elimination; changed probe 2 fails an
incorrectly explicit start-device argument; probe 3 passes cleanly at default
limits. Independent review finds no issue, including the derivation of
residency from actual execution and both confirmation branches.
Final combined validation is recorded below.

## H4 continuation: mixed fwmark and peer-setting readback

The actual setter/getter sequence now has a mixed-attribute readback theorem:
set fwmark together with one peer's preshared key and keepalive interval,
then run wgGetDevice. The result contains the model's exact JSON and completed
socket state. A malformed second peer returns normal -EINVAL after retaining
the earlier fwmark, generation, endpoint-source/cache and scalar writes.
The proof records every non-peer Device field, the selected peer's actual
cleared/configured state and all other peer bindings.

The domain is explicit: creating namespace, singleton peerList, actual
hashtable hit and resident positive peer with room for its lookup reference,
and a stopped device. The getter additionally requires no Allowed IPs for
that peer, sufficient space, an idle empty socket and actual device selection.
The claim adds no reset-record readiness: a genuine reset Stop prevents the
getter, and the existential reset timestamp is obtained from the successful
source prefix. It asserts no post-error state. The mark is an arbitrary Nat
in the mirror; current dumping uses direct JSON conversion, so this is not
a theorem about netlink byte serialization or u32 input validation.

Architecture: Config/MixedAttributeModel defines the request, updated
device, cleared/scalar peer and exact effect predicate. MixedAttributeFrames
separates socket/selector preservation across the actual endpoint-source clear.
MixedAttributeSource proves the native setter effects; MixedAttributeClaims
composes the actual projected set/get. Statements appends one literal headline.
Four new theorems bring H4 to 80 headlines/586 theorems. Together with the H2
continuations, the campaign has 276 headlines and 2,042 theorems in 615 modules.
No existing claim is reshaped or shared/mirror code edited. General mixed
requests, ownership, queued-cleanup completion and pagination remain open.
No mirror change is requested.

Probes 1–2 fail source factoring/normalization, with five unused-simp warnings
in probe 2; changed probe 3 passes the frame and source. Probe 4 fails record
syntax and a reserved local name; probe 5 fails projection/congruence and
nested-precondition elaboration; probe 6 passes all three new proof declarations
cleanly. Every warning is fixed. Both H2 and H4 packages use default new-proof
limits; no cap/limit increase, suppression or infrastructure retry occurs.
Independent review finds no issue and confirms actual prefix failures,
partial-mutation ordering and the JSON-only observation domain.

Combined Index.Statements and Config.Statements build passes 414 jobs, with
only inherited Env:865 String.mk warning. Axiom inspection checks 1,731 logical
roots in 350 modules, including 1,192 public theorem roots, standard only.
Both fresh kernel replays pass. Static checks retain all 258 original
terminal names/order; mirror/shared boundaries pass. The full
gate still fails in inherited CounterWindow/ReplayWindow and is not rerun
unchanged. Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.Index.Statements Leanux.Proofs.WG.Config.Statements, followed
by scripts/in-bundle lake env leanchecker --fresh for each module, under capped
with 32 Lean threads and 16 QEMU slots.

## H6 continuation: first actual outer timer turn

The actual runTimers now has an exact first-turn connection to the checked
timerDispatchUnit_variant. Its projected entry predicate requires a present
device, an initial non-passive record naming a non-clear timer worker, and
the actual TimerWheel.nextDue selection. No callback-success, readiness,
record-sufficiency or logical-expiry premise is added. The original initial
queue reset and captured record budget are retained; the remaining original
turns, early breaks, step checks, delivery and final queue rejection follow
the unit unchanged. Worker/unit mismatches, callback failures and suffix
failures therefore remain exact outcomes from the same actual Product entry.

Architecture: TimerDiscipline/OuterFirstTurnSource contains the operational
factors and native equality proofs; OuterFirstTurnModel contains the projected
selection predicate; OuterFirstTurnClaims contains the projected agreement.
Statements appends its literal wrapper. No frame lemma, shared-layer copy,
state reconstruction or mirror edit is needed. Four theorems bring H6 to
51 headlines and 442 theorems, and the campaign to 277 headlines and 2,046
theorems in 618 modules. No existing statement is reshaped. This establishes
neither successful dispatch nor an entire retry episode, and does not move
the caller's requireNothingDue check into runTimers.

Development: seven changed probes fail with error/warning counts 1/2, 5/1,
7/6, 2/0, 5/0, 2/1 and 3/0 (source-factor congruence, monadic normalization,
branch rewrites and type/destructuring syntax). Probe 8 passes without
diagnostics. All proofs use default limits and the unchanged memory cap;
there is no unchanged retry or infrastructure failure. Independent review
finds no issue. No mirror change is requested.

The integrated scoped build passes 312 jobs with only the inherited Env:865
String.mk warning. Axiom inspection checks 1,375 logical roots in 270 modules,
including 780 public theorem roots, with standard axioms only. Fresh replay
passes. Static checks, original 258-name order and mirror/shared boundaries
pass. The inherited full-gate failure remains unchanged and is not rerun.
Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.TimerDiscipline.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 Lean threads and 16 QEMU slots.

## H6 continuation: first retransmission receipt

A normal actual runTimers return now supplies the first selected retransmission
unit's intermediate observations. The receipt records the original remaining
budget, the actual selected-prefix snapshot, the immediate post-unit snapshot,
and the exact outcome of the remaining original continuation. Its retry count
is nextAttempts of the entry count and its retransmit timer is detached at
that intermediate point. Later turns can change those fields again; no claim
is made about their values at the whole call's final state.

The entry premises are actual first record/wheel selection and the existing
retry observation. Prefix, callback and suffix success follow from the
normal whole-call return; no readiness, empty-queue, attempt-bound or successful
callback premise is inserted. The existing observed_erase theorem retains
every original error, independently of these entry premises. The receipt
inspects its suffix on the actual post-unit product, preserving all fixture
inputs rather than reconstructing a state from its projection.

OuterFirstReceiptSource contains the small receipt path and native decomposition;
OuterFirstReceiptClaims contains the projected effect; Statements adds the
literal wrapper. The three new theorems add no frame layer, changed statement
or mirror request. This supplies an intermediate transition for later induction,
but does not establish adjacency to a send worker or the inspection conditions
needed for a complete retry pair.

Development: probe 1 fails eight parser errors from a reserved local name;
changed probe 2 passes without diagnostics. The integrated build passes 314
jobs with only the inherited Env:865 warning. All 1,380 logical roots in 272
modules, including 783 public theorem roots, use standard axioms. Independent
review finds no issue. Fresh replay passes; no cap/limit increase or
infrastructure rerun occurred. Reproduction uses the same TimerDiscipline.Statements
build and fresh replay commands as the preceding first-turn increment.

## H2 continuation: data-ingress owner coherence

The actual consumeData now preserves hashed-owner coherence on every normal
return, with coherence alone at entry. Lookup supplies a newly held positive
peer reference and the selected hashed key's original positive reference;
keypairGet then supplies its extra reference. Dead-peer and failed-enqueue
cleanup release those acquired references, so the problematic final-peer
detachment case cannot occur. EPIPE publication temporarily acquires another
peer reference and restores it. Missing lookup, all aliases and arbitrary
Ambient inputs retain their original domains; missing objects, overflow,
queue membership and recorded-work refusals remain Stops. This establishes
local preservation, not completion or initialized whole-driver reachability.

OwnerReferenceModel retains the index table, keypair store and pointwise peer
presence/owner-word/reference count. OwnerReferenceFrames contains its pure
coherence transport and key-acquisition preservation. RxQueueOwnerFrames
contains the guarded Skb adapter and stronger variants of the same two queue
families already covered by RxQueueFrames. It asserts no arbitrary callback
preservation: publication uses the actual pure callback. The lookup-held
and final caller claims are projected in OwnerCoherenceLookupHeldClaims and
OwnerCoherenceReceiveClaims; Statements appends the literal headline. No
broader shared-layer inventory is copied, and no existing shared lemma or
mirror operation is edited. The ten new theorems bring H2 to 70 headlines
and 398 theorems; together with the H6 receipt, the campaign has 279 headlines
and 2,059 theorems in 625 modules. No statement is reshaped or new mirror
change requested.

Development: support/caller author probes 1–4 fail with 2, 1, 1 and 5 errors;
5 passes, 6 passes with one unused-simp warning, and corrected 7 passes clean.
Probe 8 fails three diagnostics from continuation indentation; its later caller
portion is not accepted. Root's changed caller probe 1 exposes one remaining
positive-count obligation, and changed probe 2 closes it without diagnostics.
The separate lookup-held helper has one failed probe (two normalization/kind
errors and three unused-simp warnings), followed by a clean changed probe.
All use default limits and the unchanged memory cap; there is no infrastructure
or unchanged-source rerun. Independent review of support and the final caller
finds no issue.

The support build passes 183 jobs without warnings; final Index.Statements
passes 299 jobs with only inherited Env:865 String.mk. Axioms: 1,181 logical
roots in 235 modules, including 786 public theorem roots, standard only.
Fresh Index replay passes. Static checks, original terminal-name order and
mirror/shared boundaries pass; the unchanged inherited full-gate failure is
not rerun. Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: handshake clearing and expiry preserve coherence

Both actual handshakeClear and expireCurrentPeerKeypairs now preserve local
hashed-owner coherence on every normal return. Coherence is the sole entry
premise: optional device, missing or NULL peer words, zero counts on unhashed
objects, arbitrary clocks and repeated next/current identities retain the
original partial domain. The exact native Config contracts carry ordered
handshake removal/zeroing, last-sent time reset and both validity writes.
The pure missing-key identity in invalidateDevice is not a claim that native
expiry succeeds when a selected key is absent.

Architecture: OwnerCoherenceExpiryFrames holds three pure preservation facts;
OwnerCoherenceExpiryClaims holds two projected claims; Statements appends two
literal headlines. No broader owner-reference projection is weakened to hide
validity writes, and no shared lemma or mirror operation is edited. Seven
theorems bring H2 to 72 headlines/405 theorems and the campaign to 281
headlines/2,066 theorems in 627 owned modules. Whole-driver reachability and
final queued-worker release ownership remain open. No new mirror request.

The sole capped source probe passes with no diagnostics at the default limits.
Independent review finds no issue. Index.Statements builds 301 jobs, with only
inherited Env:865 String.mk. Axioms: 1,188 logical roots in 237 modules,
including 793 public theorem roots, standard only. Fresh kernel replay passes.
Static checks, original terminal-name order and mirror/shared boundaries pass.
No limit/cap increase or infrastructure rerun occurs; the unchanged inherited
full-gate failure is not rerun. Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.Index.Statements and scripts/in-bundle lake env leanchecker
--fresh on that module, under capped with 32 Lean threads and 16 QEMU slots.

## H1 continuation: the response edge starts at whole-call entry

An actual consumeResponse returning a peer now derives that peer's entry
CREATED_INITIATION tag and final CONSUMED_RESPONSE tag. Previously the H3
observer established the former only after lookup. The new pure lookup-update
frame proves that acquisition and owner-word storeback preserve the referenced
peer's tag, including owner/peer aliases. Actual prefix execution and existing
observer erasure connect that fact to the whole call. No residency, coherence,
authentication or record-readiness premise is added.

ResponseEdgeFrames, ResponseEdgeSource and ResponseEdgeClaims separate the
pure frame, native bridge and projected claim; Statements adds a literal wrapper.
Four theorems bring H1 to 23 headlines/189 theorems. Failed-call rollback,
whole-driver edge ownership and allocation-lifetime confirmation remain open.

## H2 continuation: response and cookie consumers retain owner coherence

Actual consumeResponse and cookieMessageConsume now preserve local hashed-owner
coherence on every normal exit. A general indexLookup_peer_held contract derives
the retained peer reference from the actual returned lookup for any owner mask.
OwnerCoherenceHeldFrames contains the internal native held-reference predicate,
metadata-preserving peer writes and non-final cleanup; the two public caller
claims remain projected. Response composition reuses the existing exact H3
observer; cookie composition factors the actual original consumer.

Rejected paths, optional devices, arbitrary records and all aliases remain in
the original partial domain. Crypto/clock errors remain Stops. No entry reference
budget or cleanup readiness is assumed; successful lookup supplies count greater
than one, which discharges final-release detachment internally. Seven theorems
bring H2 to 74 headlines/412 theorems. Whole-driver reachable ownership remains
open; publication and genuinely final release retain their separate obligations.

## H4 continuation: ordered mixed peer attributes and their readback

One actual setPeerCmd now combines PSK, one valid Allowed-IP, an optional malformed
second entry and keepalive, followed by actual getPeerDump. Normal allocation
refusal retains the PSK and sequence increment; later malformed input retains
the PSK and inserted address; only complete success reaches keepalive. Cleanup
restores the original positive peer reference count. Exact readback includes
the result code, peer fields, JSON address masking, cursor reset and consumed room.

Premises are explicit: matching resident peer lookup, positive bounded reference
count, stopped device, empty selected root, legal prefix width, and, for readback,
empty target list and finite dump cursor/sequence/capacity conditions. There is
no allocation-record readiness, allocation-ID freshness or singleton-device
premise. Cursor aliases retain their actual overwrite effect, without asserting
global trie consistency. Stops are retained and no totality or wire-format claim
is made. MixedPeerModel/Frames/Source/Claims separate exact transforms, their
readback facts, native execution and projected composition. Four theorems bring
H4 to 81 headlines/590 theorems.

### Validation of the H1/H2/H4 continuation

All independent reviews find no correctness/domain issue. New proofs use stock
limits, with no suppressions or cap increase. H1 probes 1 and 2 fail three and
one proof-form errors (three unused-simp warnings in the first); probe 3 checks
with one unused-simp warning; probe 4 is clean. H2 held-support probes 1 and 2
fail three and two errors with twelve cascade warnings each; probe 3 is clean.
Response probes 4 and 5 fail three and four parser/cascade errors; probe 6 is
clean. Root's general lookup probe passes first time. Cookie probes 1 and 2 fail
three import/layout and two native-postcondition inference diagnostics; probe 3
is clean.

H4 probes 1–5 fail respectively: one source-reduction goal/one warning; two
diagnostic sites with nine bind-reduction goals/seventeen warnings; eight final
device goals/two warnings; record-layout parsing at two sites and a cascade;
missing Bridge import and its intro cascade. Probes 6 and 7 check the full
package and narrowed split imports cleanly. One early preview of probe 2 was
premature; its completed diagnostic output was subsequently read in full.

Integration first fails one unqualified Json.arr in the H4 terminal wrapper;
the corrected Index/Config build passes 429 jobs. Adding H1 first fails two
diagnostics from copying the scratch import/namespace shell into Statements;
extracting only its documented theorem fixes that packaging error. Final combined
Noise/Index/Config build passes 446 jobs, with only inherited Env:865 String.mk.
Support builds pass 114, 67 and 136 jobs. Axioms: 1,840 logical roots in 382
modules, including 1,286 public theorem roots, standard only. All three fresh
kernel replays pass. Static checks, original 258-name order and mirror/shared
boundaries pass. There is no infrastructure retry or unchanged failed-source
rerun. The inherited full-gate failure remains recorded and is not rerun.

Reproduce with scripts/in-bundle lake build on Leanux.Proofs.WG.{Noise,Index,Config}.Statements,
then scripts/in-bundle lake env leanchecker --fresh on each target, under capped
with 32 Lean threads and 16 QEMU slots. No mirror change is requested for this tranche.

## H2 continuation: initiation consumption and handshake publication

Actual consumeInitiation now preserves hashed-owner coherence on every normal
return from the sole projected coherence premise. The actual public-key lookup
derives its retained peer reference; misses and zero counts return normally,
while missing peers, overflow and hidden-input failures retain their Stops.
Post-lookup rejection releases only the acquired reference. Successful metadata
writes preserve owner words and counts. No public-key-table coherence, entry
reference budget or readiness premise is added.

OwnerCoherencePubkeyFrames holds the native acquisition fact;
OwnerCoherenceInitiationClaims composes the actual source through the existing
exact initiation observer and its erasure. Its literal Statements wrapper adds
the third theorem. The result remains local coherence, not reachability or
failed-call state preservation.

Actual createInitiation and createResponse also preserve coherence under an
explicit coherent-publisher premise: for a present Device, the caller's peer
is resident, positively referenced and has its own handshake owner word, even
when that owner is not yet hashed. Hashed-table coherence alone does not imply
this premise. OwnerCoherenceCreatorModel defines it, CreatorFrames proves
metadata/publication preservation, and CreatorClaims connects both actual
creators. Two literal wrappers bring this package to six theorems. No readiness,
success, cursor-bound, hash-membership or uniqueness premise is introduced.

Together these packages bring H2 to 77 headlines and 421 theorems. Global
driver propagation and caller discharge of publication/lifetime obligations
remain open. Neither package changes a shared layer or the mirror.

## H3 continuation: invalid MAC1 preserves the Device

The whole actual non-cookie receiveHandshakePacket call preserves the complete
optional Device, and thus every remote endpoint, on normal return when the
entry Device's actual MAC1 comparison fails. The predicate uses the source's
saturating message slices and has no packet-shape or type-1/type-2 premise.
Missing Device and earlier clock failures retain their stopped behavior;
Ambient and load-history changes are not claimed to roll back.

InvalidMac1Frames covers the actual load/decay prefix; InvalidMac1Source covers
both load outcomes of the actual receive body; InvalidMac1Claims is projected,
and Statements adds its literal wrapper. Four theorems bring H3 to 14 headlines
and 161 theorems. Later authentication failures, queued data callbacks and
whole-driver endpoint provenance remain open.

### Validation of the H2/H3 continuation

Independent reviews of all three packages find no correctness/domain issue.
The initiation package's probe 1 passes support only; probes 2–5 fail,
respectively, four parser/cascade diagnostics; five proof-construction errors
and two unused-simp warnings; one bind-normalization error and one warning;
two eliminated-successor-name errors. Changed probe 6 is clean. Creator probe
1 fails a projected/native Device rewrite; probe 2 is clean. Invalid-MAC1
probe 1 fails the final projected endpoint equation with one unused-simp warning;
probe 2 is clean. All final proofs use default limits without suppression.

The H3 support build passes 115 jobs; combined integration passes 348 jobs,
and the final Index/Roaming build passes 351 jobs. Only inherited Env:865
String.mk is reported. Axioms: 1,412 logical roots in 287 modules, including
918 public theorem roots, standard only and no missing roots. Both fresh kernel
replays pass. Static checks, original 258-name order and mirror/shared boundaries
pass. Current totals are 2,094 theorems, 646 owned modules and 289 headlines.
One static-check invocation mistakenly sent its Python body to the shell and
failed to parse; the corrected Python invocation passes all static checks.
No infrastructure retry, cap increase or unchanged failed-source rerun occurs.
The inherited full-gate failure remains recorded and is not rerun unchanged.

Reproduce with scripts/in-bundle lake build on
Leanux.Proofs.WG.{Index,Roaming}.Statements and scripts/in-bundle lake env
leanchecker --fresh on each target, under capped with 32 Lean threads and
16 QEMU slots. No new mirror request arises.

## H1 continuation: actual session derivation-clock provenance

The original beginSession now has a full Product observation connecting its
actual derivation clock read to the successful ordered preparation, rotation
and handshake-index publication. The entry projection is arbitrary; normal
return itself supplies the resident Device and peer. No successful allocation,
intermediate clock run, readiness or final-key-residency premise is added.

A successful receipt records the actual admission/allocation prefix, role and
chaining key, and the complete before/after clock projections. Its birthdate
is the same value used by SessionBirthEffect through RotationRun and final
index replacement. Aliased puts remain admitted and can erase the allocated
key. Normal false returns have no derivation receipt and preserve Device and
keypair counter, while retaining the prefix's actual record consumption.
The claim does not assert whole-snapshot rollback or receipts on stopped calls.
Existing observed_erase retains every original error without a new copy.

SessionClockModel holds the input, receipt and effect predicates;
SessionClockSource holds two exact source factors, prefix/derivation effects,
the native whole-run decomposition and actual Product observation path;
SessionClockClaims holds the projected claim. Statements adds a documented
literal wrapper. No standalone frame is added: the clock's Ambient type and
the existing native lift rule provide WG preservation locally. Seven theorems
bring H1 to 24 headlines and 196 theorems; campaign totals are 2,101 theorems,
649 modules and 290 headlines. Whole-driver edge ownership, wider totality and
allocation-lifetime confirmation remain open.

Independent review finds no correctness/domain issue. Development probes 1–5
fail, respectively: factor congruence and two record-layout sites with cascade;
match reduction and one unused-simp warning; bind normalization, derived-record
layout, rewritten-prefix equality and eliminated before-state names; Product/native
lift reassociation; missing receipt-constructor type annotation. Probe 6 passes
cleanly at default limits. Failed elaboration's generated recovery terms are
diagnostics, not accepted proof evidence.

The integrated Noise.Statements build passes 113 jobs without warnings.
Axioms: 477 logical roots in 89 modules, including 290 public theorem roots,
standard only with no missing roots. Fresh kernel replay passes; static checks,
original 258-name order and mirror/shared boundaries pass. No infrastructure
retry, dependency build during replay, cap increase or unchanged failed-source
rerun occurs. The inherited full-gate failure is unchanged.

Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Noise.Statements
and scripts/in-bundle lake env leanchecker --fresh on that target, under
capped with 32 Lean threads and 16 QEMU slots. No mirror change is requested.

## H2 continuation: actual peer initialization supplies publication coherence

Actual peerCreate preserves local hashed-owner coherence on every normal return
and every successful result names a resident peer with refcount one and its
own handshake owner word. A separate projected corollary establishes exactly
the handshake creators' publisher premise. Numeric allocation/limit errors
preserve the original Device; all stopped paths retain their actual behavior.

The proof admits nextPeer collisions. It tracks the unchanged index/keypair
stores and all other peer lookups through initialization, without asserting
coherence while the replacement's handshake word is temporarily NULL. The
actual handshakeInit self-word write restores coherence. This is positivity
and owner-word coherence, not accounting for reference ownership, public-key
table uniqueness or global reachability.

OwnerCoherencePeerCreateModel holds the pure footprint; Frames holds the
internal native initialization predicate and three supporting facts; Source
proves the actual creation effect; Claims contains the two projected contracts.
Statements adds one literal headline. Seven theorems bring H2 to 78 headlines
and 428 theorems. No new mirror change or shared-layer copy is needed.

An independent removal inventory confirms that dead-marking can preserve the
existing ownerReferences projection, but it cannot discharge final release's
detachment obligation from coherence alone. Coherence does not require every
hashed keypair naming a peer to occupy one of that peer's three slots. The
existing checked peerPut counterexample already exposes this invariant gap.
General removal needs slot coverage and retained-reference accounting, or an
explicit detachment premise at release. The later whole-removal finding
below turns this inventory into a checked actual-call counterexample.

## H2 continuation: whole quiet removal exposes the lifecycle obligation

The earlier last-peerPut witness now extends to the complete original peerRemove.
Its explicit Device contains one positively referenced peer, an empty three-slot
key set, empty work/trie/packet state and a positively referenced hashed keypair
whose peer word names that peer. The entry satisfies HashedOwnersCoherent.
The theorem derives an actual normal removal and its exact final Device for
every native state and Ambient realizing that Device. The keypair row remains
hashed after the peer disappears, so final owner coherence is false.

This is a checked statement-domain finding: local coherence does not connect
hashed keypairs to peer slots or establish retained-reference accounting.
The witness does not violate the separate numeric-index uniqueness predicate,
establish reachability from initialization, or demonstrate a mirror/kernel bug.
A keypair peer word alone must not be treated as a proved held-peer reference.
No mirror-team change is requested. The next positive architecture transports
an entry detachment condition through quiet removal; a second architecture
would allow live slots under explicit coverage and prove their actual unhashing.
Neither treats post-call coherence as an assumption.

OwnerCoherenceRemovalFindingModel holds seven pure witness definitions;
OwnerCoherenceRemovalFindings holds the projected whole-call claim.
Statements adds its literal documented wrapper. There are no new native frame
files or shared variants. Two theorems bring H2 to 430 theorems and 79 headlines.

Seven changed scratch probes were used. Probes 1–6 fail respectively on concrete
source recursion; source/cleanup recursion and membership decidability;
concrete specialization recursion; repeated singleton-map normalization;
ring/NAPI guard simplification; and the initialized empty-ring fact.
Probes 1 and 2 also emitted an unused-simp warning. Probe 7 accepts both
theorems with one unused-simp warning; removing that unused argument is checked
by the installed 331-job build. No limits were raised or unchanged job retried.
Independent review finds no semantic or domain issue.

## H2 continuation: quiet removal under entry detachment

The positive counterpart of the whole-removal finding is now checked.
A resident, positively referenced peer with three empty key slots, an empty
allowed-IP list and empty send/clear work queues can be removed while preserving
hashed-owner coherence on every normal return. The device peer count is positive.
At a last reference, the entry condition requires every retained owner other
than that peer's own handshake entry to stop naming the peer. A nonlast release
needs no additional detachment. This is an explicit local lifecycle obligation,
not a theorem that reachable driver states establish it.

The proof applies the actual whole-call quiet-removal contract. It transports
coherence and detachment through unlisting, dead-marking, ordered slot/timer
cleanup and the peer-count decrement, then applies the existing exact last-
or retained-reference release law. Crypt/NAPI/packet/timer refusals remain
possible; no hidden-record or completion readiness is introduced. The earlier
counterexample violates this entry condition and remains unchanged.

OwnerCoherenceQuietRemovalModel holds LastOwnerDetached;
OwnerCoherenceQuietRemovalFrames holds four small pure transports;
OwnerCoherenceQuietRemovalClaims contains the projected claim, and Statements
its documented wrapper. No shared variant or mirror change is needed.
Six new theorems bring H2 to 436 theorems and 80 headlines; campaign totals
are 2,137 theorems, 670 modules and 297 headlines. The later live-slot theorem separately discharges entry coverage through actual
ordered unhashing; this empty-slot theorem alone does not establish it.

Six changed scratch probes were used. Probe 1 fails with one record-normalization
goal and two default-heartbeat diagnostics in final composition. Splitting a
named pure release frame and abstracting cleanup output yields probe 2's clean
pass. Probe 3 fails at outcome let-bindings, and probe 4 at a redundant dsimp.
Probe 5 passes after that removal; probe 6 checks the split package with narrowed
imports without diagnostics. No limit increase, suppression or infrastructure
rerun occurred. Source review checks the entry/final distinction and retained
refusal cases without finding an issue.

The installed Index build passes 334 jobs, with only inherited Env:865 String.mk.
The axiom audit passes 1,285 logical roots in 270 modules, including 847 public
theorems, using only the three standard axioms. Fresh Index kernel replay passes without diagnostics after dependency
artifact writers stopped. Static checks, original headline order and the
source census pass. Existing C1 layers and the executable mirror are unchanged.
The inherited full gate remains failed and is not rerun. Reproduce with the
Index.Statements scoped build and fresh leanchecker command under capped,
scripts/in-bundle, 32 Lean threads and 16 QEMU slots.

## H4 continuation: mixed port refusal and actual readback

The actual mixed setter now has a contract for a changed nonzero listen port
that collides while the device is running in its creating namespace. Supported
flags include REPLACE_PEERS; private-key and peer-attribute suffixes remain
arbitrary. On a normal return the code is -EADDRINUSE. The earlier generation
increment, fwmark write and both endpoint-source/cache clearing passes persist.
All other device fields, including port, sockets, identity and index/keypair
stores, retain their original values. Listed peers have the actual final reset
value; unlisted bindings are unchanged. Replacement and later attributes do
not execute. Duplicate or missing listed peers are not excluded: missing-peer
or hidden-reset failures remain actual Stops, with no post-Stop claim.

A second claim composes the actual following wgGetDevice. Its bounded domain
adds a singleton resident peer, no allowed IPs, enough dump room and an idle,
empty socket 7. The device may remain running; there is no peer-reference bound
or reset readiness premise. The getter returns exact mirror JSON with the new
mark and original port, identity and serialized peer fields, empties its socket
at the incremented generation, and retains the setter's real source/cache
effects. This is not a byte-level netlink encoding theorem.

PortRefusalModel holds the request and committed-prefix Device.
PortRefusalFrames contains two substantive native frames for the clearing loops
and refused bind; PortRefusalSource connects the whole original setter;
PortRefusalClaims contains the two projected contracts. Statements adds two
documented wrappers. Seven theorems bring H4 to 597 theorems and 83 headlines.
The proofs use existing campaign-owned effects without changing shared lemmas.
No mirror change is requested.

Eight changed scratch probes were used. Probe 1 fails on projection elaboration,
Boolean equality, name shadowing and a missing frame import. Probe 2 fails on
two source-factor equalities. Probe 3 accepts the source with two unused-simp
warnings, removed in the next draft. Probes 4–6 fail on getter record layout,
projection congruence and dependent equality elaboration respectively.
Probe 7 checks both claims without diagnostics; probe 8 checks the exact split
bodies and both wrappers without warnings, with seven standard-axiom outputs.
Independent review finds no issue. No readiness premise, suppression, limit
increase or infrastructure rerun was introduced.

## Validation of the quiet-removal finding and mixed port refusal

The installed combined Index/Config build passes 449 jobs, with only the
unchanged Env:865 String.mk deprecation. The new proofs are warning-free.
The combined axiom audit covers 1,833 logical roots in 385 modules, including
1,252 public theorems: only propext, Classical.choice and Quot.sound.
Fresh kernel replays of both terminal modules pass without diagnostics,
after dependency artifact writers stopped.
Static token/import/root/default-target checks, all 258 original headline
names/order, source census and diff formatting pass. The executable mirror
and existing C1 shared layers remain unchanged. The owned tree now contains
2,131 theorems in 667 modules and 296 headlines. The inherited full-gate failure
is unchanged and is not rerun; no whole charter result is declared complete.

Reproduce the scoped build and each fresh replay using Index.Statements and
Config.Statements under scripts/in-bundle, capped, LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. Scratch diagnostics are reconstructible and not committed.
The separate H3 reply/socket overlap is inventoried in the shared-frame
follow-up; neither of its two architectures has been implemented.

## H2 continuation: actual slot clearing discharges coverage

Whole peerRemove now preserves owner coherence with live or aliased key slots.
At a last peer reference, every hashed owner naming that peer must be either
its own handshake entry or a keypair in one of its three original slots.
The public condition concerns the entry Device. The actual successful clearing
prefix supplies the ClearRun certificate; it is not a caller premise.
Each immediate key put unhashes its owner even when the key retains references,
and ordered clearing removes every covered owner. No slot distinctness, static
reference budget or ClearReady premise is imposed. Missing keys and insufficient
references on repeated aliases remain actual Stops.

The theorem keeps positive peer reference/count, a resident peer, an empty
allowed-IP list and empty send/clear work queues. It follows actual unlisting,
dead-marking, key clearing, timer cleanup, the crypt/NAPI guard, count decrement
and final release. Queue/timer refusals are eliminated only from the supplied
normal whole-call run. This establishes a local conditional preservation law,
not global reachable-state coherence or removal totality.

OwnerCoherenceSlotRemovalModel holds LastOwnerCovered; Frames contains six
pure transports; Source connects the actual post-dead removal; Claims lifts
the whole call through the campaign projection. Statements adds its documented
wrapper. Nine theorems bring H2 to 445 theorems and 81 headlines. No shared
variant or mirror edit is introduced.

Six changed probes were used. Probe 1 fails with two errors and three unused-simp
warnings; probe 2 checks the three initial pure transports without diagnostics.
Probe 3 fails with five diagnostics from parsing/cascades and an unreduced crypt
refusal; probe 4 fails on an unreduced observed Except-map contradiction.
Probes 5 and 6 check the complete and reordered split packages without
diagnostics. No limit increase or unchanged retry occurred. Independent review
finds no issue in the entry coverage, actual clearing certificate or refusals.

## H3 continuation: admitted response rejection preserves endpoints

The actual whole response-kind receiver now preserves every remote endpoint
when its same-entry receipts show MAC admission and no response-consumer cut.
The entry is otherwise arbitrary. Two read-only inspections observe the actual
MAC/load prefix and response prefix from the same complete Product state;
their erasure executes the original receiver once and retains every original
normal result and Stop. Normal whole-call execution supplies both successful
prefix receipts. MAC admission excludes the cookie-reply path, so a missing
response cut identifies actual consumer rejection and the remaining suffix
performs no endpoint write.

A stronger supporting frame preserves every optional full Endpoint observation
through consumeResponse, for every normal result. Actual index lookup derives
the extra reference needed by rejection cleanup. Arbitrary owner words, owner/
peer aliases, NULL clears and zero-reference misses retain their source behavior.
No coherence, residency, self-owner, reference-budget, source-family or hidden
input readiness premise is added. The peer map itself may change; an owner-word
clear is compatible with endpoint preservation. Broader caller and callback
authentication coverage remains open.

ResponseRejectionModel contains the admission and observation predicates;
Frames contains four native frames and two private pure map helpers, including
the native held-reference predicate. Source defines the two inspections and
their all-errors erasure; Claims contains the projected whole-call result.
Statements adds one documented wrapper. Nine theorems bring H3 to 179 theorems
and 16 headlines. Existing campaign-owned exact effects suffice; the pending
six-family cookie-reply/socket layer is not copied.

Seven changed probes were used. Probes 1–4 fail on projection normalization,
source bind reduction, eliminated-variable names or source/projection bookkeeping;
probes 2 and 3 also emit one warning each. Probe 5 fails on a nonexistent Option
lemma and emits two warnings. Its axiom output includes sorryAx from failed
elaboration recovery: that run is failed and supplies no accepted proof.
Probes 6 and 7 pass the complete and split-body checks without warnings,
printing only standard axioms for all seven public roots. Independent review
finds no issue. No suppression, limit increase or infrastructure retry occurred.

## H4 continuation: private-key update and actual getter

The actual private-key-only setter/getter composition now reads back its effective
identity and exact peer expiry effect. The source comparison distinguishes the
supplied key from the stored private key; clamping may affect the final value.
The initial identity is established, the generated public key has no peer-table
collision, and the getter domain is one resident peer without allowed IPs,
enough room for the effective installed identity, and an idle empty socket.
Running state, staged packets, keypair aliases and counts remain arbitrary.

An established old identity disables the staged-send branch even when the new
key removes the identity. Actual precomputation, handshake unhash/zero, expiry
clock and current/next invalidation produce the exact final Device. The expiry
time is derived from the actual ObservedKeyPeerRun, not a supplied historical
relation; the public conclusion exposes an existential effect, not a clock
receipt. Missing clocks, NULL handshake words and missing keypairs remain Stops.
On a normal set/get sequence the setter returns zero, JSON contains the effective
clamped identity and original serialized peer fields, and the getter empties
socket 7 at the incremented generation. A null key omits identity fields through
the actual JSON convention. No byte-level encoding claim is made.

KeyReadbackModel contains two pure effects; Frames has three substantive native
socket/selector frames and one pure Device-field frame. Source derives the exact
whole-setter effect; Claims composes the actual getter; Statements adds its
documented wrapper. Socket and fixture preservation are proved from execution,
not inferred from Device equality. Seven theorems bring H4 to 604 theorems and
84 headlines. No shared lemma or mirror code is changed.

Six changed probes were used. Probe 1 fails on bind grouping and action
metavariables. Probe 2 accepts the frames with one unused-simp warning, removed
in the next draft. Probe 3 fails on dependent inversion/projection and emits
three unused-simp warnings; probe 4 fails on projection elaboration and two
unnormalized pure-frame branches. The complete diagnostic output was inspected;
a truncated preview was not treated as complete evidence. Probes 5 and 6 pass
the whole and split-body checks without diagnostics and with seven standard-axiom
outputs. Independent review finds no issue. No limit increase, suppression or
infrastructure rerun occurred.

## Validation of slot removal, response rejection and key readback

The installed Config build passes 277 jobs. Its axiom audit covers 1,028 logical
roots in 213 modules, including 698 public theorems; fresh Config replay passes
without diagnostics. The installed Index/Roaming build passes 386 jobs and
their combined axiom audit covers 1,512 roots in 322 modules, including 983 public
theorems, all standard only. Both fresh terminal kernel replays pass without diagnostics, after
dependency artifact writers stopped.
Only the unchanged Env:865 String.mk warning remains in builds; all added proofs
are warning-free. Static token/import/root/default checks, all 258 original
headline names/order, source census and diff formatting pass. The mirror and
existing C1 shared layers remain unchanged.

The campaign now has 2,162 theorems in 682 owned modules and 300 headlines.
No whole H1–H6 charter result is declared complete; the inherited full-gate
failure remains failed and is not rerun unchanged. The preceding quiet-removal
package also received independent source review with no findings. Reproduce
the scoped builds and fresh replays on Config.Statements, Index.Statements and
Roaming.Statements under capped, scripts/in-bundle, LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. No new mirror-team request arises from these increments.

## H2 continuation: arbitrary allowed-IP removal and zero-key work

The whole peerRemove coherence contract now permits arbitrary allowed-IP lists
and trie representations. The entry resident/positive peer, positive numPeers,
empty send/clear work queues and LastOwnerCovered obligations remain. A pointwise
peer observation hides only allowedipsList; index/keypair stores, embedded owner
words, references, slots and cleanup queues remain visible. Actual listDel and
removeByPeer preserve this observation even when lists contain duplicates or
nodes have malformed shape. Missing nodes, invalid bit accesses and all later
cleanup refusals remain actual Stops; no NodePairs, readiness or reference
budget premise is introduced.

OwnerCoherenceAipRemovalModel holds the two observations. Frames contains two
pure transports and the named local listDel_spec/removeByPeer_spec variants;
Source contains the peerMakeDead_spec variant. These are three bounded variants
of C1 WGBase contracts, not a copied shared layer. Claims composes the actual
whole removal and Statements adds a wrapper. Seven theorems remove the prior
empty-allowed-IP restriction; broader root/free/remove-all overlap stays pending.

The actual queuedExpiredZeroKeyMaterial worker also preserves coherence under
resident/positive peer and LastOwnerCovered, with no numPeers, queue/list
emptiness or readiness premise. Handshake zeroing retains coverage, the actual
ClearRun derives detachment, and the final peerPut uses that derived fact.
OwnerCoherenceZeroWorkerFrames holds one pure coverage transport; Claims and
Statements contain the projected whole-worker claim and wrapper. These three
theorems do not establish scheduler selection or global reachability. Dropping
coverage still leaves the existing off-slot lifecycle obligation; no new
worker-specific counterexample is claimed.

AIP development probes 1–4 fail with 16, 7, 2 and 1 diagnostics respectively;
probe 3 also has one corrected unused-simp warning. Probes 5–6 check the complete
and narrowed packages without diagnostics. Both zero-worker probes pass without
diagnostics at default limits. Independent AIP review and root zero-worker
source review find no issue. No limit increase, suppression or infrastructure
rerun occurs. H2 now has 455 theorems and 83 headlines.

## H3 continuation: admitted initiation rejection preserves endpoints

The whole initiation-kind receiver now has the corresponding rejection contract:
same-entry Product receipts show actual MAC admission and no initiation-consumer
cut, and every remote endpoint is preserved on normal whole-call return. The
source observer executes the original receiver once after its two inspections;
erasure retains every original error and normal result. Normal execution derives
both successful prefix receipts. Admission excludes cookie-reply paths, and the
no-cut suffix is pure.

The supporting full optional Endpoint-map frame follows all of consumeInitiation,
including decrypt, timestamp/replay/flood rejection and successful handshake
writes. Public-key lookup supplies the retained reference used by rejection
cleanup. No owner coherence, self-word, residency, alias, reference-budget,
source-family or clock/decrypt readiness premise is added. Ambient logging and
handshake metadata may change; endpoint preservation does not assert a complete
peer-map frame.

InitiationRejectionModel holds admission and observation predicates; Frames holds
three native contracts and one private map helper. Source contains both inspection
definitions and all-errors erasure; Claims and Statements contain the projected
whole-call claim and wrapper. Existing owned response endpoint/cleanup support
is reused; no pending cookie-reply/socket layer is copied. Seven theorems bring
H3 to 186 theorems and 17 headlines.

Probe 1 checks the consumer frames. Probe 2 fails two linked rename/map diagnostics;
probes 3–4 check the whole claim, wrapper and six public axiom roots without
warnings. The first installed split build fails because the model header opens
an unavailable Noise namespace, causing three diagnostics; removing that
unneeded open resolves the package error. No proof body, limit or premise
changes. The corrected build passes. Independent review finds no correctness
or domain issue.

## H4 continuation: repeated callbacks and separate DONE transport

Five support contracts connect a resumed allowed-IP dump that splits again,
its actual fixed-size callback, final DATA without room for DONE, the subsequent
DONE-only dump, and the receive that triggers it. Resumed capacity is the actual
44-byte overhead plus 28 bytes per IPv4 item; DONE consumes its actual 20 bytes.
The failing next item must be readable because the source reads it before the
serialization refusal. The cursor is set to the next un-emitted node; repeated
IDs may revisit the same first occurrence, so no progress theorem is claimed.

Completion spill retains DATA and the callback-running flag. DONE-only retains
the actual nonpositive errno, accepts any optional Device with a NULL peer
cursor, and runs no WireGuard callback. The receive contract derives its actual
pop and queued DONE. PaginationCallbackSource and PaginationDoneSource contain
all five facts; there is no new model, frame file or headline. General bounded
pagination still requires a capacity partition, cursor freshness, callback/
receive induction and JSON coalescing. H4 now has 609 theorems and 84 headlines.

Probe 1 fails three parser/elaboration diagnostics. Probe 2 exits zero with one
unused-simp warning and is not accepted. Probe 3 fails one exposed Except.map
normalization goal. Probes 4–7 check the whole and split packages without
diagnostics and print standard axioms for all five facts. Independent review
finds no correctness issue and catches the overstrong cursor-progress docstring;
the installed text now describes the exact cursor assignment. No limit increase,
unchanged retry or infrastructure failure occurs.

## Validation of removal, initiation rejection and pagination support

The initial AIP/pagination build passes 369 jobs. After the corrected initiation
module header, the combined build passes 418 jobs; zero-worker installation
passes 347 jobs. The only build warning is inherited Env:865 String.mk.
The combined axiom audit covers 1,640 logical roots in 356 proof modules,
including 1,064 public theorems, with standard axioms only. All four fresh kernel
replays pass without diagnostics after dependency artifact writers stop.
Static checks and all 258 original terminal names/order pass. Mirror and
existing shared-layer boundaries are unchanged.

This checkpoint adds 22 theorems and 12 modules to 9dcb9646: 2,184 theorems,
694 owned modules and 303 headlines. No whole H1–H6 result is declared complete;
the inherited full-gate failure remains failed and is not rerun unchanged.
Reproduce builds and fresh replays on Index.Statements, Roaming.Statements,
Config.PaginationCallbackSource and Config.PaginationDoneSource under
Leanux.Proofs.WG, using capped, scripts/in-bundle, 32 threads and 16 QEMU slots.
No new mirror-team request arises.

## H6 continuation: every actual timer-loop turn

The observer now covers one complete original runTimers call from an arbitrary
Product entry and jPass. It resets queuedThisCall once, uses the actual record
budget, records every executed loop turn including a terminating turn, and
executes the original timerOuterFinish. Each turn retains its iteration,
incoming control, entry/exit Product snapshots, result and same-entry selected
unit inspection. The unit choice reads the actual next non-passive record and
rescans the current wheel on that turn. Successful execution derives worker/
timer agreement; it is not a callback-readiness premise.

Selected timer receipts connect the actual prefix snapshot and immediate
callback exit. Retransmit selection preserves identity and changes attempts to
nextAttempts with no remaining logical expiry at that immediate exit. Yield
receipts thread the exact observed snapshots and control through the finite
range; done receipts retain the terminating turn and exclude the unused tail.
Absent-device calls have their actual reset and false result. Errors from
selection, callback, loop or finish remain errors under whole-call erasure;
there is no partial receipt history on failure.

OuterEpisodeModel contains eleven data/model declarations; Source contains four
observer definitions, five public source theorems and one private selection
factor. Claims holds the projected episode theorem and Statements its literal
wrapper. Eight added theorems bring H6 to 453 theorems and 53 headlines. No frame
file, shared-layer copy or type-deletion is needed. The complete Product
observations retain the existing fixture projection; executable states are never
reconstructed from snapshots.

[AGENT 2026-10-17] Use a source-specific finite-loop observer over actual
timerOuterTurn rather than copying C1's absent Logged/TimerPass closure.
Its erasure keeps the real worker interleavings, reset and finish. The episode
certificate does not separately characterize finish's queue checks, prove fuel
adequacy, assert no remaining due timer, or establish a retry-19/session-once
bound. The supplied-unit sequence remains a separate theorem awaiting a
history invariant connecting its pairs to the actual episode.

Ten changed development probes were used. Probes 1–9 fail with errors/warnings
7/5, 3/0, 7/7, 11/1, 7/2, 1/0, 2/3, 1/0 and 1/0 respectively, on run/lift
normalization, annotations, eliminated locals, Boolean branches and bind form.
Probe 10 checks the complete package with zero diagnostics and only standard
axioms on all seven public roots. Default proof limits/caps are unchanged;
no suppression, unchanged retry or infrastructure failure occurs.

Installed split build passes 317 jobs, with only inherited Env:865 String.mk.
Axiom inspection checks 1,402 logical roots in 275 modules, including 790 public
theorems, standard only. Fresh terminal kernel replay passes
without diagnostics after all artifact writers stop.
Independent source review finds no correctness issue and confirms the limits
above. Static checks, original terminal names/order and mirror/shared boundaries
remain unchanged. The campaign now has 2,192 theorems in 697 owned modules and
304 headlines, versus 2,184/694/303 at ba6f537a. All H1–H6 remain in progress;
the inherited full-gate failure is not rerun or reclassified. Reproduce build
and fresh replay on Leanux.Proofs.WG.TimerDiscipline.Statements under capped,
scripts/in-bundle, 32 Lean threads and 16 QEMU slots. No new mirror request.

## H2 continuation: the actual clear-work dispatcher

The original Env.runOneClearWorker now preserves owner coherence with a lifecycle
obligation confined to the peer it actually selects. The pure entry selector
matches passive-record stripping, the optional recorded unit, its worker-specific
unitPeers lookup, queue membership and the head fallback. A successful source
selection proves agreement and actual queue membership. Missing devices,
empty queues, unknown or unqueued identities, malformed inputs, section failures
and worker-body Stops remain possible.

ClearWorkerOwnerEntry requires local coherence and, only for that selector's
result, a resident positively referenced peer with LastOwnerCovered. It requires
neither queue-wide coverage nor completion readiness. The actual dequeue
preserves those fields; the real section wrapper then composes the checked
zero-key worker. Duplicated queues and arbitrary records are retained.

OwnerCoherenceClearWorkerModel has three pure definitions; Frames has the
dequeue and section contracts; Source has the selector, exact source factor,
private peek equation and selected-peer theorem; Claims and Statements have the
projected whole-call claim and wrapper. Seven theorems bring H2 to 462 theorems
and 84 headlines. No shared variant or mirror change is added.

Probes 1–6 fail with 6, 7, 3, 3, 3 and 2 errors. The first also reports two
failed-elaboration sorry warnings; the sixth has two unused-simp warnings.
These are failed drafts, not accepted trust evidence. A bounded continuation
corrects two reduced equality witnesses and removes the unused arguments;
probes 7–8 check the complete and split packages without diagnostics. No limit,
cap, premise or source-semantics change occurs. Root source review finds no issue.

## H4 continuation: finite receive composition and complete page coalescing

PaginationPlanModel defines canonical first/resumed capacities and positive-sized
tail partitioning, with two flatten proofs. PaginationFinalSource connects the
actual final callback without a DONE-room premise and the fitting inline-DONE
transport. PaginationReceiveSource connects pop/refill, ordinary DATA drain
steps and a finite original receive-loop induction. Its bound counts each
ordinary DATA receive plus the finishing receive, including a separate DONE.
The one-step contracts are internal composition hypotheses: the eventual public
getter must discharge them from its canonical plan. The empty allowed-IP case
still needs its real single peer DATA envelope.

PaginationCoalesceModel defines recursive continuation DATA messages and DONE;
Claims proves the actual adjacent continuation merge and finite-page result.
The merge keeps the untouched later tail, including later Stops. Coalescing
preserves every IP occurrence in order, even for empty or repeated pages.
Only the first-page endpoint-none domain is imposed; no global ID uniqueness is
needed for this JSON theorem. Actual cursor progress still needs boundary
freshness, and production of those pages by the getter remains a separate task.

Nine added theorems and seven definitions bring H4 to 618 theorems, with
84 headlines unchanged. No arbitrary-pagination headline is claimed.
The source tranche uses seven changed probes: probes 1–5 fail on termination
reduction, parser/record syntax, nil witnesses, arithmetic or array normalization;
probes 2 and 4/5 additionally expose warnings or default simplifier recursion
limits. Probes 6–7 check the complete and narrowed packages without diagnostics.
No limit is raised; finite rewrites replace the recursive simplification.
Coalescing probe 1 checks adjacent merging; probe 2 exits zero with one unused
simp warning and is not accepted; probe 3 removes it and checks both standard
axiom roots. Independent reviews find no correctness issue and retain the
first-page capacity and cursor-freshness boundaries explicitly.

## H5 continuation: actual timer-completion guards

A true normal return of the original Env.runTimers establishes exactly its
final tests: Device present, empty send/clear work lists, encryptQueue.empty,
and empty txWorkQueue. The predicate uses the ring's own empty operation;
it says nothing about all physical slots, pendingWork, wheel exhaustion,
fairness or the adequacy of the loop budget. A false return carries no guard
conclusion. No callback or readiness premise is assumed.

TimerCompletionModel holds the projected predicate. Source proves the unchanged
finish guard, Claims connects the original complete call, and Statements adds
the wrapper. Three theorems bring H5 to 296 theorems and 44 headlines.
Probe 1 fails one source-bind factoring goal; probe 2 fails two optional-step/
Boolean normalization goals and emits two warnings. Probes 3–4 check the whole
and split package without diagnostics, standard axioms only. Root source review
and independent source reviews find no issue.

## Validation of clear dispatch, pagination support and timer completion

Builds pass 318 jobs for pagination/Progress, 91 for coalescing, and 489 for
Index/H6. The latter exposes the existing owned timerOuterTurn_selected_run
source theorem publicly, unchanged, so the next actual-history bridge can reuse
it without copying its proof. This changes visibility, not the theorem count.
The only warning remains inherited Env:865 String.mk.

The combined audit covers 2,567 logical roots in 532 proof modules, including
1,626 public theorem roots, with standard axioms only. All five fresh kernel replays
pass without diagnostics after dependency artifact writers stop.
Static checks, original terminal order and mirror/shared boundaries pass.
This adds 19 theorems and 12 modules to 7118b842: 2,211 theorems in 709 owned
modules, 306 headlines. All H1–H6 remain in progress; the inherited full gate
remains failed and is not rerun unchanged. Reproduce builds/fresh replays on
Index.Statements, Progress.Statements, TimerDiscipline.Statements,
Config.PaginationReceiveSource and Config.PaginationCoalesceClaims under
Leanux.Proofs.WG, through capped and scripts/in-bundle with 32 threads and
16 QEMU slots. No new mirror request or infrastructure retry.

## H4 continuation: actual finite IPv4 pagination

The original getter now returns every allowed-IP occurrence in order for a
singleton resident peer with an arbitrary finite readable IPv4 list, subject to
the actual 4096-envelope limit. Its entry domain includes no endpoint, an idle
empty socket, header room and cursor freshness at canonical chunk boundaries.
Freshness excludes a boundary ID from the entire emitted prefix; repeated IDs
away from those boundaries remain allowed. No callback-success, receive-success,
peer-reference or global ownership premise is assumed.

The source composition executes the actual first callback, repeated callbacks,
first-occurrence cursor search, DATA receives, final inline or separate DONE,
and coalescing. The exact envelope count includes the queued predecessor DATA
and any separate DONE, allowing completion on receive 4096. Empty lists emit
the real fixed peer DATA. The result preserves the whole Device and gives the
exact final socket; arbitrary Ambient inputs retain their original behavior.
This closes single-peer IPv4 pagination, not multi-peer/IPv6/endpoint pagination,
global ownership or general setter/getter composition.

Architecture: PaginationBoundaryModel and PaginationCountModel hold the pure
boundary/capacity/count/socket definitions. PaginationCanonicalSource,
CompletionSource, StartSource, FirstSource, ChainSource and SingleSource connect
the actual operations. PaginationManyClaims and PaginationClaims expose the
projected getter; Statements adds original_finite_ipv4_pagination. The public
getterDrain_range_source is an exact source factor, avoiding expansion of the
concrete 4096 range without raising proof limits. Twenty theorems in ten modules
bring H4 to 638 theorems and 85 headlines. No shared variant or mirror edit.

Development ledger: canonical/completion probes 1–6 fail on membership tactics,
record or constructor inference, recursive count context, errno/array
normalization, and default recursive simplification; probe 2 also warns.
Probes 7–8 check the complete and exact split packages. Start transport passes
its first probe. First-page probes 1–2 fail four and one diagnostics, then
probe 3 passes. Many-page probes 1–5 fail on count/branch arithmetic, concrete
range kernel recursion, rewrite orientation, and native/projected conversion;
probe 1 also warns. Probes 6–8 pass after an exact symbolic range factor.
Single-page probes 1–2 fail three syntax/cascade errors and one redundant
tactic; probe 3 passes. Final all-list composition and axiom probes both pass.
No limit/cap increase, warning suppression or infrastructure retry occurs.
Independent reviews of the support, first page and final whole composition
find no correctness or scope issue.

## H6 continuation: retry blocks from actual episode history

An adjacent-pair contract now connects two actual consecutive outer-loop runs:
an empty-send-queue retransmit selected by the current records and wheel,
followed by the actual nonempty send-worker turn. The intermediate concrete
state is shared by both runs; projected history is never used to reconstruct
an executable state. The successful actual dispatch and worker derive their
certificate without a supplied callback-success or entry-readiness premise.

For a nonempty contiguous same-peer block of those pairs, the normal original
episode now yields initial/final peer residency, preserved internalId/refcount,
exact attempt growth by the number of pairs, pending=false and an empty send
queue. Attempts are at most MAX_TIMER_HANDSHAKES + 1 (19) at the last send exit.
Later turns and final delivery are outside that bound. The theorem does not
assert that arbitrary episode histories are paired, exclude intervening resets
outside the block, prove fuel adequacy, or establish once-per-session arming.
All errors remain those of the exact observedRunTimersEpisode erasure.

OuterAdjacentModel holds the conditional certificate; Frames contains the
substantive requireStepComplete same-concrete-state contract; Source extracts
adjacent concrete runs; Claims connects the whole episode. ActualRetryBlockModel
holds receipt pairing and the final effect; Claims takes only snapshot continuity
from OuterTimerChain and execution certificates from the actual run. Statements
adds the two literal headlines. Thirteen theorems in six modules bring H6 to
466 theorems and 55 headlines. No shared layer is copied or edited.

Adjacent-pair probes 1–5 fail with 3, 2, 15, 3 and 3 diagnostics on lift/match,
reserved identifier, projection and layout issues; probes 6–7 pass the complete
and split packages, standard axioms only. Block-count probe 1 fails one reserved
name, probe 2 two membership/nil-length goals, and probes 3–4 pass the candidate
and exact split/terminal/axiom checks. No proof-limit/cap increase, warning
suppression or infrastructure retry. Independent reviews of both packages find
no correctness or scope issue.

## Validation of finite pagination and actual retry blocks

Scoped builds pass 102 jobs for canonical completion, 355 for first-page and
adjacent support, 107 for many-page composition, and 510 for both complete
terminal closures. The only warning is inherited Env:865 String.mk.
The combined axiom audit covers 2,185 logical roots in 446 proof modules,
including 1,353 public theorem roots, using only standard axioms.
Both final fresh kernel replays pass without diagnostics after dependency
artifact writers stop. Static checks, the original 258 terminal names/order,
and mirror/shared-layer boundaries pass.

Relative to c22ebdca this adds 33 theorems, 16 modules and three headlines:
2,244 theorems in 725 campaign-owned modules, 309 headlines. Every owned module
is in the scoped checked closure; all H1–H6 remain in progress. The full gate
still fails in inherited CounterWindow.Refinement and ReplayWindow.Counterexamples;
it is neither rerun unchanged nor reclassified. Reproduce builds and fresh
replays on Leanux.Proofs.WG.Config.Statements and
Leanux.Proofs.WG.TimerDiscipline.Statements through capped and scripts/in-bundle,
with 32 Lean threads and 16 QEMU slots. No new mirror-team request.

## H1 continuation: whole-response tag ownership

The actual consumeResponse now preserves every optional peer tag on every
normal refusal. Success changes only the returned peer and derives its entry
CREATED_INITIATION tag. The captured entry is arbitrary: no coherence,
residency, readiness, reference-budget or alias premise is added. Stops retain
their original domain. This is tag preservation, not Device rollback: lookup
may still clear an owner word on a normal miss.

ResponseTagModel holds the pure tag map. Frames contains two private map facts
and two local variants of WGBase.indexLookup_spec and peerPut_spec; actual
lookup supplies the retained reference for cleanup. Source composes the real
consumer, Claims conjoins the existing successful entry edge, and Statements
adds a literal headline. Seven theorems bring H1 to 203 and 25 headlines.
The successful-transcript alternative was rejected because a none receipt
does not retain rejection effects. No shared definition or lemma is edited.

Probe 1 fails one dependent-postcondition goal and warns on one unused simp
argument; probes 2–3 check the corrected and split packages without diagnostics.
Root source review finds no correctness/domain issue. No new premise or limit
increase is used.

## H4 continuation: paginated readback after actual setters

Mixed fwmark/peer-scalar and private-key-only set/get now compose with the
finite IPv4 getter. Each proof derives the actual post-set list, node map,
selector and socket inputs from the same normal setter run. The mixed request
retains mark/scalar writes on a later malformed-peer EINVAL and its actual
cache-reset timestamp. The private-key request retains effective/clamped or
null-key serialization, actual expiry time and ordered aliased key effects;
capacity, boundary freshness and receive count use the post-install identity.

Existing setter premises remain explicit. No callback-success, hidden-clock,
reset-readiness or reference premise is added. These are normal-return
compositions, not total setters. Singleton/no-endpoint/readable-IPv4/capacity/
boundary-freshness/socket/4096-envelope conditions remain. Global ownership,
free transport and unrestricted mixed/multi-peer/IPv6 behavior stay open.

PaginationCapacityFrames holds two substantive pure transport lemmas for
prefix-size equality, not facts supplied by narrowed types. MixedPaginationClaims
and KeyPaginationClaims contain the projected compositions; Statements adds
two literal wrappers. Six theorems are added. Mixed probe 1 fails three
proof-form goals; probes 2–4 pass the corrected/axiom/narrow-import checks.
Both private-key probes pass. Independent source review finds no issue.

MultiPeerCoalesceModel/Source/Claims add two further support theorems: the
actual coalescer preserves an arbitrary finite list within one DATA envelope,
adding an empty allowed_ips field only where absent. This is not a proof that
the getter produces that envelope. Its exact step retains the continuation
errors. Root probes 1–8 fail with 1, 1, 1, 1, 4, 1, 1 and 1 diagnostics
on type inference and higher-order source conversion; probe 1 also has seven
unused-simp warnings. Probe 9 exits zero with one warning and is not accepted;
probe 10 and the exact split-package check pass without warnings, standard
axioms only. No proof limit is raised. H4 now has 646 theorems and 87 headlines.

## H6 continuation: local partial-exchange arming

A checked local fixture runs the original give-up callback with a running/live
CREATED_INITIATION peer, attempts 19, empty key slots/store and allocation
counter zero. It returns normally, leaves those session observations intact,
arms zero-key at ZERO_KEY_MATERIAL_TICKS and performs one wheel enqueue.
The public total contract fixes the complete WG projection and only disables
recorded timer arming in Ambient; all other Ambient fields, including hidden
inputs, remain arbitrary. The source gives the exact four appended decisions.

This is a local arm-without-session-creation example, not a reachable runner
history or a counterexample to a precisely scoped reachable-session invariant.
[AGENT 2026-10-17] Keep session-hook calls, guarded logical arms and physical
enqueues distinct when stating the remaining count theorem. The smaller next
architecture labels existing actual response-caller receipts by their allocation
serial and derives the all-mode arm effect. A second architecture counts
derived versus give-up events across a named-caller history, but needs additional
counter frames and still does not supply whole-runner reachability.

PartialExchangeArmModel contains the pure fixture/view, Source the native
execution, Claims the projected contract, and Statements its wrapper. Three
theorems bring H6 to 469 and 56 headlines. Root source review finds no issue.
Probes 1–2 fail three and one diagnostics, the second with four warnings;
3–4 pass. Attempted unrelated-WG generalization fails default recursion/field
goals in probes 5–6, with recovery sorry diagnostics not accepted and two
warnings in probe 6. The final claim does not make that generalization:
probes 7–8 check the complete WG projection and exact package cleanly.
No cap/proof-limit increase or suppression.

## Validation of tag ownership, setter readback and local arming

Scoped builds pass 296, 364 and 333 jobs. The only warning is inherited
Env:865 String.mk. The combined audit checks 2,330 logical roots in 487 proof
modules, including 1,458 public theorem roots, using only standard axioms.
All four fresh kernel replays pass after artifact writers stop. Static checks,
original terminal order, mirror identity and shared-layer boundaries pass.

Against 1fe20f41 this adds 18 theorems, 13 modules and four headlines:
2,262 theorems in all 738 owned modules, 313 headlines. No existing statement
is reshaped or deleted. All H1–H6 remain in progress and the inherited full gate
remains failed, without an unchanged rerun. Reproduce the scoped builds and
fresh replays on Noise.Statements, Config.Statements, TimerDiscipline.Statements
and Config.MultiPeerCoalesceClaims under Leanux.Proofs.WG, through capped and
scripts/in-bundle with 32 Lean threads and 16 QEMU slots. No infrastructure
retry or new mirror-team request.

## H1 continuation: whole-initiation tag ownership

The original consumeInitiation now preserves every optional peer tag on all
normal refusals and changes only its returned peer on success. There is no
required old tag: the source permits a restarted exchange. Both ordered clock
reads, rejection cleanup, arbitrary aliases and all original Stops remain.
No readiness, coherence, residency or reference-budget premise is added.

InitiationTagFrames supplies two narrow local pubkeyLookup/setPeer variants;
actual acquisition derives the retained reference. Source composes the existing
erased consumer and Claims projects the result. Statements adds the literal
headline. The owned ResponseTagFrames.tagMap_write helper is exposed unchanged
and reused, avoiding a duplicate pure proof; no shared file is edited.
Five added theorems in three modules bring H1 to 208 and 26 headlines.
All three capped default-limit probes pass without diagnostics, and the
installed build passes 144 jobs without warnings. Root review finds no issue.

## H6 continuation: actual session-arm events

Both full response callers now retain their original complete observations and
attach an all-mode SessionArmEvent to each reached session cut. Its serial is
the actual pre-session allocation counter plus one, preserved across the hook.
The source derives the resident live peer. A running device has the exact
peerTimerArmEffect; a false running guard preserves the entire WG projection
while still permitting Ambient caller-read/decision effects and original Stops.
Across the hook the physical enqueue counter stays equal or increases by one.

Existing ResponseSessionFacts supplies hook presence exactly when beginSession
returns true and the actual SessionEffect. Its premise is discharged internally
from each original prefix, not assumed by either headline. Incoming response
only needs its message-kind equality; both whole-call preconditions are True.
The claim is at the actual hook cut, not final caller state. It does not imply
survival of an aliased keypair, unique serials across an arbitrary mixed history,
or one physical enqueue per successful session.

SessionArmEventModel holds the event predicate. Frames proves the substantive
counter consequence of the exact arm effect. Source factors the two existing
prefixes by their original decision site and connects the actual hook; Claims
and the two literal terminal wrappers retain the original observations.
Nine added theorems and two definitions in four modules bring H6 to 478 and
58 headlines. No observer, source behavior or shared layer is changed.
Probes 1–3 fail five, three and two mechanical bind/layout/type goals;
probes 4–5 pass the complete and exact split/axiom packages without warnings.
Independent review finds no correctness or domain issue. No proof-limit,
cap or premise increase occurs.

## Validation of initiation tags and session-arm events

The helper build passes 67 jobs, initiation 144 and session events 330;
only the latter reports inherited Env:865 String.mk. The audit covers
1,572 logical roots in 323 proof modules, including 914 public theorem roots,
with standard axioms only. Both final fresh kernel replays pass after
dependency artifact writers stop. Static checks, original terminal order,
mirror identity and shared-layer boundaries pass.

Relative to 2f3e9b7f this adds 14 theorems, seven modules and three headlines:
2,291 theorems in all 753 campaign-owned modules, 316 headlines. All H1–H6
remain in progress; the inherited full gate remains failed and is not rerun
unchanged. Reproduce the scoped builds and fresh replays on
Leanux.Proofs.WG.Noise.Statements and Leanux.Proofs.WG.TimerDiscipline.Statements
through capped and scripts/in-bundle with 32 Lean threads and 16 QEMU slots.
No new mirror-team request, infrastructure retry or warning suppression.

## H3 continuation: rate-limit refusal preserves peers and endpoints

The whole original non-cookie receiver now has an actual strict-prefix
observation of load selection and cookie validation. Normal whole-call return
derives successful execution of that prefix. If its actual verdict is
ratelimited, the final optional peer map and every remote destination equal
their entry values. No load, MAC, clock, allocation, address-family or peer
residency premise is added.

Cookie-secret rotation, rate-limit state, load history and Ambient effects
remain active; whole Device equality is not claimed. The noCookie verdict
alone does not imply rejection, because the unloaded path admits it.
The bad-MAC2 reply path and queued callback provenance remain open. Exact
observer erasure retains all original failures, without claiming a returned
receipt or final state on a stopped call.

RateLimitModel holds the projected observation. RateLimitSource factors the
actual prefix and unchanged suffix and proves observer erasure. RateLimitFrames
contains three narrow local variants of C1 Framing/WGCookie's makeCookie,
ratelimiterAllow and cookieValidatePacket frames, plus actual-prefix peer-map
composition and the refusal suffix frame. Claims and the literal Statements
wrapper complete nine theorems, bringing H3 to 15 headlines and 170 theorems.
No reply/socket layer is copied.

## H5 continuation: recorded batch completion guards hold at return

Every normal original afterBatch call entered with recorded inputs has a
present Device satisfying its five queue-empty tests, zero handshake queue
counter (handshakeQueueLen) and no scheduled NAPI peer. An exact source factor retains the bounded
schedule/peek/send-worker loop, all guard failures and all delivery failures.
The final delivery operation preserves the Device, so the guard facts hold
at actual return without a separate loop-success or readiness premise.

These are precisely the source tests. PtrRing.empty observes its head slot;
it does not establish that every physical slot is free, nor a ring-count
invariant on malformed metadata. No global drain adequacy, fairness,
pendingWork, suspension, record-exhaustion or recordless-path claim is made.
The recordless early branch remains explicitly outside this theorem.

BatchDrainModel holds the exact loop/suffix actions and projected predicate;
BatchDrainFrames has one Device-only local variant of C1
Framing.deliverSent_sameKernel from Framing/EnvLeaves. BatchDrainSource proves
the original recorded factor and suffix guarantee; BatchDrainClaims and its
literal wrapper connect the whole original call. Five theorems bring H5 to
43 headlines and 293 theorems. No broader scheduler frame layer is copied.

### Validation of peer creation, rate-limit rejection and batch completion

Independent full-source reviews of all three packages find no correctness or
scope issue. Peer creation probes 1, 3, 4, 5 and 6 fail with respectively one,
four, four, two and one errors; probes 1, 4 and 5 also have one unused-simp
warning each. Probe 2 checks support and probe 7 checks the full package cleanly.
Probe 8 fails five diagnostics after import narrowing drops Campaign2.Bridge;
the explicit import correction is validated by the integrated 319-job build.

Rate-limit probes 1–3 fail respectively: peer-map projection normalization
and one unused-simp warning; a reserved binder, opaque predicate rewrite and
downstream no-goals diagnostic; an eliminated Unit variable. Probes 4–6 pass
the full candidate, reordered split bodies and standalone pure model cleanly.
The integrated Roaming.Statements build passes 120 jobs without warnings.

Batch-drain probes 1–5 fail respectively: factor/getter/do-layout issues and
three warnings; factor/getter conversion and an unavailable tactic; lift/Stop/bind
normalization and four warnings; final factor/getter conversion and one warning;
two getter pure-reduction obligations. Probe 6 is clean. The first packaging
driver fails because its wrapper already contains only the theorem. The
subsequent 266-job build checks the previous target and is not new-result
validation. Before repairing the driver, every dirty worktree is preserved,
including nonignored untracked files, under
refs/snapshots/campaign2-package-recovery-20261017T074600755913Z; branch tips
and working indexes remain unchanged. The corrected insertion and integrated
Progress.Statements build pass 270 jobs.

The Index and Progress builds report only inherited Env:865 String.mk.
Axiom checks use standard axioms only: Index 1,244 logical roots/255 modules
(824 public theorem roots); Roaming 444/90 (226); Progress 1,147/206 (702).
All three fresh kernel replays pass. Static checks, original 258-name order,
mirror/shared boundaries and the complete owned census pass.
Current totals are 2,122 theorems, 661 modules and 293 headlines. Final proofs
use default limits; no cap increase, infrastructure retry or unchanged failed
source rerun occurs. The inherited full-gate failure remains recorded.

Reproduce with scripts/in-bundle lake build on
Leanux.Proofs.WG.{Index,Roaming,Progress}.Statements, and scripts/in-bundle
lake env leanchecker --fresh on each target, under capped with 32 Lean threads
and 16 QEMU slots. No new mirror-team request arises.

## Remaining general Allowed-IP ownership dependency

Campaign 1 already has native AllowedIps/InsertionRouting contracts for original
insertion success and normal allocation refusal, using represented Patricia trees,
RoutingInvariant, NodesBelow and ResidentLists. That layer is absent here.
A second architecture based on direct node/list preservation would duplicate
the same layer, so it is inventoried rather than copied.

The eventual H4 setAllowedip bridge can reuse insert_routing_outcome,
insert_routing_success and insert_routing_refusal after their landing, retaining
target residency, address/prefix bounds and represented-input premises.
OwnersBelow bounds labels; it does not imply that every labeled peer is resident.
A stronger resident-owner claim therefore needs its own explicit invariant.
This is a proof dependency, not a mirror discrepancy or change request.

## Remaining coherent-ring progress dependency

A positive H5 activation/drain theorem now has a precise proof-layer dependency:
campaign 1's Queues/PtrRing, RingGeometry and RingSteps, available on its branch
but absent here. Their ringOf/Bounds representation relates physical cursors
and stale slots to logical live contents, and consume_preserves supplies the
tail step for arbitrary batch values. Recreating that layer here would cross
the shared-layer boundary, so no copy is made.

The proposed own wrapper would induct on the live list using those pure facts
and existing cookie source continuations. Arbitrary recorded inputs retain
actual Stops; valid stop/reschedule records give drain/yield corollaries,
without clock/allocation records for empty-table cookie misses. Logical count
zero/items empty can then be proved; the retired physical reset-to-empty
claim remains false even for coherent rings. Initial queue-length equality
is needed only to conclude handshakeQueueLen = 0. The alternative direct physical-state
induction would duplicate the same absent ring layer; it was inventoried,
not implemented. This is a proof dependency, not a mirror request or a new H5 result.

## Remaining outer timer-episode dependency

The selected-unit H6 retry sequence does not yet give a retry bound for an
entire runTimers call. The OuterEpisode observer now records every actual turn.
The actual scheduler can interleave clear, crypt and send work with timers,
finish several callbacks at the same wheel step before running send work,
rescan a changed wheel, and reset queuedThisCall only once. A supplied sequence
of timer/send pairs, each beginning with an empty send queue, therefore needs
a separate invariant identifying those pairs inside the actual event sequence.
Normal runTimers completion also does not imply that no timer remains due:
the requireNothingDue check belongs to the enclosing idle/advance path.

[AGENT 2026-10-17] Start with an exact connection to the first actual iteration,
retaining the original remaining loop and final checks. This avoids assuming
callback success and supplies a bounded basis for a later event-sequence proof.
The alternative is campaign 1's Logged/TimerPass observer, whose erasure theorem
already follows the actual timer/clear/send/crypt scheduler. Its Capture and
PrefixLoops dependencies are absent here; copying that layer is outside the
allowed few local variants. Its current receipts also need selected-wheel
information before they can connect to the retry certificates. The source-specific observer now has a checked complete turn chain, but neither
architecture establishes the complete scheduler retry bound.

The enclosing requireNothingDue also reads fixture.hiddenAhead, outside the
campaign Product projection. Comparisons from the same actual product entry
retain that input; equality of projected snapshots alone does not determine
its error classification. No execution state is reconstructed from a projection.
This is a proof obligation, not a mirror finding or change request.

## Historical checkpoint before the split

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
record-suffix claims, other input outcomes and broader call totality were open
at this checkpoint. The later original_begin_session_clock proves actual
birthdate provenance through rotation/publication without readiness; it does
not assert receipts on stopped calls or general totality.

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
The proposed initial-next-below-cursor condition is not yet a proved
fresh-installation history result. Later whole-call tag maps and finite mixed
tag histories cover all seven native tag owners. The owned-source audit below
removes the general failed-consumer release obstacle; fresh-installation
confirmation, reachable slot/key coherence and lifetime closure remain open.

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

The historical pre-split inventory estimated six outer-removal and nine
ingress families, plus a larger decrypt/NAPI layer. That is not the current
blocker count: after the split, owned single-peer removal and consumeData table
contracts are checked. packetReceive/wgReceive retain four deferred header/CPU
families; peerRemoveAll, decrypt/NAPI and environment closure remain broader
dependencies, detailed in the shared-frame follow-up. Most shared contracts
omit the observation rather than being false. Full reference lifetimes,
broader record layouts and whole-runner witnesses remain supporting extensions,
not separate primitive H2 targets.

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

The historical constructed backlog witness refuted no-pending-at-completion
over de62c9d. The current runner and the boundary audit both reject that trace
at the batch-completion guard, as the checked carry report records. The old
acceptance and backlog statements were corrected explicitly during the retrofit;
no accepted final backlog boundary is claimed over b700659. This was a
constructed fixture, not a parsed or captured Linux run.

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


The historical cookie-activation contracts assumed that list/count occupancy
alone described the physical ring. That domain was insufficient. The split
retrofit retires five false count/totality supports and checks concrete
malformed-ring counterexamples in CookieActivationBoundFindings and
CookieItemsFindings. Those witnesses are arbitrary-state refutations, not
initialized accepted executions.

The current original_cookie_activation_outcome gives exact agreement with
cookieHybridRun under the original cookie-only/empty-index premises. It
retains receive, record and occupancy-exhaustion errors; it does not prove
successful drain, strict record decrease or count adequacy on arbitrary ring
metadata. Cookie classification remains an entry premise, not ingress
validation.

The current original_cookie_scheduled_resumption_progress selects the control
branch from pure resolver success, then retains the actual probe, detached
bounded rerun and all their errors. Resolver success is not an execution
success witness and does not imply a drain or a strict suffix. The two
CookieActivationFrames projection equations remain frames; the other files
express operational outcomes.

The current original_cookie_schedule_outcome retains its explicit record
shape and count premises but concludes agreement with the bounded first turn
and actual remainder, including the scheduler's budget guard. It does not
promise successful completion, empty physical queues or the historical
list-based final projection. Positive represented-ring adequacy and initialized
queue/pending-work consistency require the inventoried shared support.

## H6 — Timer discipline

Local contracts cover all seven concrete arm sites, actual clock-plus-delay
wrapping and jitter below 83. H6's finite draw certificates require contiguous
draws; H5 additionally proves arbitrary supplied-record jitter outcomes and
budget adequacy. General arm-record mode can permit placeholders.
There is no distribution claim. The applicable running/live/interval guards qualify each arm;
a final timer value alone does not prove an arm event.

The supplied caller/jitter/arm domain now gives exact Product agreement with
the retransmit hook's actual continuation (original_retransmit_hook_ready).
It retains caller and jitter reads, running/live guards, and timer-clock or
wheel-record refusals. Normal enabled arming has the documented wrapped delay
and full WG wheel/registration effect; an inactive guard follows the actual
skipped path. The supplied domain does not guarantee completion.

The supplied creation/send-tail domain gives exact Product agreement through
actual initiation, send and rearm (original_send_initiation_ready). Existing
creation, cookie, interval, endpoint and allocation conditions remain explicit.
The caller ignores the no-endpoint address-family return, but subsequent arm
refusals remain Stops. No unconditional completion, packet delivery or whole
retry-history claim follows.

The supplied ready domain does prove successful execution of the actual
selected retransmit wheel unit (original_fire_retry_ready). Due/horizon,
identity, records, reference and queue conditions remain explicit. Its full
Product effect includes wheel detachment, pass-step reset, pending-work
filtering and queuedThisCall preservation. This is timerDispatchUnit_variant,
not outer selection or completion of runTimers; the later first-turn and
whole-episode contracts address those original control paths separately.

The named-worker domain gives exact Product agreement through selection,
dequeue, creation, arm, release and section stop (original_send_worker_ready).
Dequeue erases one selected occurrence and derives pending from residual
queue membership: a duplicate may leave it true (original_send_dispatch_path).
Arm, release and section failures stay visible. The theorem does not promise
unconditional worker completion, packet transmission or queue exhaustion.

From a resident device and initially empty send queue, normal selected
timer/send pairs derive same-peer selection, entry attempts at most 18,
enqueue/reference acquisition, detach, increment and worker release.
Consecutive successful same-peer pairs from zero number at most 19. This
excludes 20 such pairs, not a twentieth callback. The immediate original
callback after 19 has exact all-outcome give-up behavior; normal return
preserves identity/count and empty queue. Later episode observers also derive
actual adjacent-pair certificates and qualifying contiguous-block counts;
they do not prove every arbitrary history decomposes into those blocks.

Above the limit with zero-key already pending, give-up is total: retain its
expiry, delete send-keepalive expiry and wheel entry, purge staged packets, add their length to dropped,
and append exact true-give-up/false-zero-key-absent decisions. Hidden records,
clocks, attempts and device queues stay unchanged. No running/live/record-mode
premise is needed.

With zero-key absent, the supplied-record domain gives exact Product agreement
with the actual post-give-up arm continuation (original_giveup_absent_zero_key).
Timer-clock and wheel-record refusals remain possible. A normal enabled arm
retains the original zero-key delay and complete WG timer effects. These
conditions establish neither scheduler selection nor a session history.

Both response callers observe actual session results; the session-derived hook
is reached exactly on true. Traversal compositions cover outgoing initiation,
outgoing response, common initiation/response receive tails, data completion and
data receipt in their stated contexts. Data completion traverses once per
encrypted item/list before its per-packet send loop (`Data.lean:181–194`,
C `send.c:242–260`), not per packet/transmission. Successful nonkeepalive sends
control data-sent; nonzero received length controls data-received. Guarded
recorded wheel effects are established at actual hook cuts. Current observer
erasures preserve original failures; cut facts do not promise final expiry or
delivery. Common response traversal does not require session success.

Zero-key firing queues clearing; it does not immediately erase keys. Give-up
can arm it without session creation, as shown by the local checked finding and
separate initialized runner replay in their stated scopes. Actual session
events tie their hook to beginSession success and the allocation serial, with
zero or one physical enqueue under the guard. Whole timer episodes, actual
adjacent retry certificates and qualifying contiguous same-peer block counts
are now checked. Universal history decomposition and cross-call session-relative
counts remain open. The give-up finding rejects attributing every zero-key arm
to session creation; it does not settle every interpretation of at-most-one
arm per completed session. No mirror discrepancy is established.

## Findings and mirror requests

The [request document](2026-10-14-campaign-2-mirror-requests.md) ranks all three
changes as altitude-preserving. No mirror/kernel edit or upstream report occurred.

| Finding | Evidence and limit | Status |
| --- | --- | --- |
| H5 batch backlog | Kernel-checked accepted constructed fixture and backlog, with symbolic proof locating it at the actual final runner boundary; not parsed/captured Linux | Historical over de62c9d. Main `9db558b` adds completion guard; actual runner/audit refusal carry checks over b700659 |
| H5 nested refill | Evaluated initialized prefix/source review; operation 4 reaches worker occupancy-budget invariant; later suffix incomplete | Neither accepted complete trace nor kernel-proved prefix; callback-aware bound requested |
| H4 dump cancellation | Accepted getter, kernel-checked internal room 3720 versus source-derived C 3724 | Restore pre-nest snapshot; no demonstrated compared-output mismatch. Dead-cursor extension only inspected |

Alias examples, statement qualifications and the 4096 boundary are not
accepted-run findings. H1/H2/H3/H6 have no ranked mirror-change request.

## Validation and trust limitations

The historical pre-split six-target checkpoint passed **482 jobs**. All **258 headlines** and eight new
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

The pre-split full gate at **`69f988a` failed** in inherited
`WG/CounterWindow/Refinement.lean` and `WG/ReplayWindow/Counterexamples.lean`
(counter operands/index-owner carries). Campaign 1 owns repair. The later split-gate failure and its
diagnostics are recorded in the current checkpoint and retrofit report.
Scoped passes are not a full-gate pass; existing shared lemmas were not edited.

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


## H1 continuation: whole-creator tag ownership

The actual createInitiation and createResponse now preserve every optional peer
tag on normal refusal, and on success change only the requested peer's tag.
Response success derives the entry CONSUMED_INITIATION tag from its actual
first peer read and guarded branch. No residency, readiness, reference budget,
coherent owner word or alias restriction is supplied. Missing-device, missing-peer,
NULL-word, hidden-input and index failures keep their actual stopped behavior;
the claims are normal-return contracts, not totality or full-state rollback.

CreationTagFrames holds one named local peer-write variant.
CreationTagSource composes the actual operations and the existing typed index
adapter; CreationTagClaims projects both results, and Statements adds two
literal headlines. Seven theorems and three modules are added, with no data
definition or shared-layer edit. Together with the two whole-consumer tag
contracts, this supplies all four create/consume tag maps. Session/clear
composition and allocation-lifetime confirmation remain separate work.

Probe 1 fails eleven proof/inference diagnostics and seventeen unused-simp
warnings; changed probe 2 passes. The narrowed split-body check and isolated
Frames check also pass without warnings at default limits. Root and independent
source review find no issue. No mirror change is requested.

## H4 continuation: fitting multi-peer getter

The original wgGetDevice now returns the exact ordered JSON for any finite
fitting peer list whose listed peers are resident and have empty allowed-IP
lists. Repeated identifiers and public keys remain repeated visits; endpoint
fields are unrestricted and use the mirror's actual serialization.
The explicit bound is devicePrefixSpace + 168 * length + 20 <= NLMSG_GOODSIZE.
It covers DATA and DONE in one envelope. An empty list uses the actual
cancelled nest and becomes peers=[] through the original coalescer.

MultiPeerDumpModel records the fixed attributes and exact callback result.
MultiPeerDumpSource proves the original finite dump loop and callback,
including cancellation. MultiPeerGetterModel defines the expected JSON;
MultiPeerGetterSource proves the actual queued DATA/DONE drain;
MultiPeerGetterClaims composes the original start, receive and coalescer.
Statements appends one literal projected headline. These eight theorems,
five definitions and five modules reuse the previously checked two-theorem
multi-peer coalescer. Whole Device equality and final socket state are exact.
The selector, idle/empty socket, residency, empty-IP and capacity premises
remain explicit; no callback-success, liveness or reference premise is added.
Multi-peer pagination, nonempty peer IP lists and global owner/list coherence
remain open. This result concerns mirror JSON rather than wire encoding.

Producer probes 1--10 have outcomes PASS, FAIL(1), FAIL(4), FAIL(5),
FAIL(2), FAIL(2), FAIL(2), FAIL(5), exit-zero-with-warning, PASS.
Intermediate failures concern source-loop normalization, record syntax,
arithmetic and default recursion/simplification/heartbeat limits; no limit was
raised. Probes 4 and 8 each have four warnings; probe 9 has five unused-simp
warnings and is not accepted. Getter probes 1--3 fail four, one and one
diagnostics; probe 1 also emits two warnings, including failed-elaboration
recovery from a broken JSON definition. No written or recovered placeholder
is accepted. Corrected probe 4 checks all three getter roots with only standard
axioms and no warnings. Independent review verifies the actual loop,
cancellation, duplicate handling, capacity, socket and whole-getter composition.

The producer build passes 76 jobs without warnings; the combined Noise/Config
build passes 383 jobs with only the inherited Env:865 String.mk warning.
The scoped axiom audit checks 1,467 logical roots in 319 modules, including
972 public theorem roots, using only the three standard axioms.
Fresh replays of both terminal modules pass. Static checks, all 258 original
terminal names/order, diff formatting and mirror/shared-layer boundaries pass.
The census rises from 2,276/745/316 to 2,291/753/319
(theorems/modules/headlines). No infrastructure retry, cap increase, guest
run, merge to main or push occurs. The inherited full-gate failure is unchanged
and is not rerun or presented as passing.

Reproduce with capped scripts/in-bundle lake build on
Leanux.Proofs.WG.Noise.Statements and Leanux.Proofs.WG.Config.Statements,
then capped scripts/in-bundle lake env leanchecker --fresh on each module,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H1 continuation: session, clearing and expiry tag maps

The original beginSession now preserves every optional peer tag on a normal
false return. A true return changes only the selected peer to ZEROED and
derives its actual entry CREATED_RESPONSE or CONSUMED_RESPONSE tag.
The original handshakeClear and whole expireCurrentPeerKeypairs each zero
only the selected peer on normal return. Residency comes from the actual first
read, not a supplied precondition. Missing/NULL owners, hidden clocks, missing
keys and aliased releases keep their actual stopped paths.

SessionTagFrames contains two pure preservation facts: ordered rotation keeps
peer tags through every slot write/release, and validity-only key updates keep
tags. SessionTagSource reuses the exact SessionEffect and configuration expiry
effects; SessionTagClaims contains the three projected contracts. Three literal
headlines bring this package to eleven theorems and three modules, with no
data definition or shared variant. The seven creation, consumption, session,
clear and expiry operations now have whole optional tag-map contracts.
This is not a mixed-history, full-driver or allocation-lifetime theorem.

The full eleven-theorem candidate and narrowed standalone Frames probe each
pass on the first check, with no diagnostics and default limits. Root and
independent review find no issue. The installed Noise closure passes 161 jobs
without warnings. No mirror change is requested.

## H6 continuation: outgoing session-counter origin

The actual outgoing response prefix preserves keypairCounter through the
sender clock/write, response creation and MAC publication. A reached session
cut therefore starts at the original whole-call counter. The projected claim
retains the existing complete outgoing observer and SessionArmEvent. When
that event is an allocation, its serial is entry counter plus one at the
actual hook cut. False session returns and normal creation refusal keep their
existing observations. Exact erasure keeps all stopped executions; no stopped
post-state, final-call counter delta, final key residency or cross-call
uniqueness is asserted.

SessionOriginFrames has two narrow named variants of C1's
WGTransitions.createResponse_spec and addMacToPacket_spec, using only their
counter/frontier observation. SessionOriginSource links the actual prefix;
SessionOriginClaims projects the whole-call observation; Statements has one
literal headline. Five theorems and three modules are added, with no data
definition. The eight-site complete outgoing preservation layer and larger
incoming layer remain inventoried in the shared-frame follow-up, not copied.

Probes 1 and 2 fail two inference and one consumed-binder diagnostics,
respectively. Changed probes 3--5 pass, including narrowed imports and all five
standard-only axiom roots. None emits warnings or raises limits.
Independent review finds the two shared variants were not named after their
C1 counterparts; both names and docstrings are corrected before this commit.
The initial 333-job build and fresh replay pass; the renamed source is rebuilt
and replayed again. This is changed-source validation, not an infrastructure
retry. The reviewer finds no semantic or domain issue.

## H4 continuation: scalar update followed by fitting multi-peer readback

The original scalar request followed by the original getter is now total on
the existing stopped-device/selected-peer reference domain and the finite
fitting getter domain. The response contains every listed occurrence in order,
with arbitrary endpoints; each occurrence of the selected peer reflects the
PSK and keepalive update. The selected peer may be absent from the dump list:
the exact Device still changes but that peer is absent from JSON. A malformed
second request retains the successful first mutation and returns -EINVAL.
No callback-success or post-set invariant premise is supplied.

MultiPeerScalarModel defines the updated peer view.
MultiPeerScalarEffects computes the actual ordered peer-map writes and derives
all getter inputs. MultiPeerScalarClaims composes the two original calls
through their actual intermediate native state and Ambient; Statements adds
one literal headline. Three theorems, one definition and three modules are
added. The existing scalar setter premises remain explicit; arbitrary-list
fwmark composition and multi-peer pagination are separate obligations.

Probe 1 fails two default-heartbeat diagnostics; probe 2 fails record syntax
and a selected-peer goal; probe 3 tries an unnecessary structural TreeMap
equality; probe 4 fails two default-heartbeat diagnostics and the downstream
missing helper. Preserving the actual repeated inserts and reducing explicitly
closes probes 5 and 6, the latter with all three standard-only roots.
No probe warning or limit increase occurs. Independent review finds two form
issues: the substantive helper belonged in Effects rather than Frames, and
the terminal prose did not explicitly distinguish an unlisted target.
Both are fixed without changing any proposition or adding a membership premise.
No mathematical/source-linkage finding remains.

The combined pre-form-correction build passes 534 jobs; the corrected Config
closure passes 308 jobs. Their only warning is the unchanged Env:865 String.mk
deprecation. Final axiom inspection checks 2,387 logical roots in 511 modules,
including 1,507 public theorem roots, using only standard axioms.
Fresh Noise replay passes; final Config and TimerDiscipline replays pass after
all artifact writers stop. Static trust/import checks, all 258 original
terminal names/order, diff formatting and mirror/shared boundaries pass.
The census rises from 2,291/753/319 to 2,310/762/324
(theorems/modules/headlines). All three independent reviews are dispositioned.
No infrastructure retry, cap increase, guest run, merge to main or push occurs.
The inherited full gate remains FAILED and is not rerun unchanged.

Reproduce with capped scripts/in-bundle lake build on the Noise, Config and
TimerDiscipline Statements modules, then capped scripts/in-bundle lake env
leanchecker --fresh on each, with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

A documentation-update guard matched the full H6 label too broadly and
stopped before writing the register. Dirty worktrees, including untracked
files, were snapshotted to recovery refs before correcting that guard. Branch
tips and working indexes stayed unchanged; no Lean validation was rerun for
this documentation-only correction.


## H1 continuation: finite mixed native tag histories

TagSequenceModel describes seven actual native operation kinds, their complete
original results, projected before/after receipts and a linked edge relation.
TagSequenceSource dispatches only to those original operations, reads the
actual snapshots and proves exact computation erasure, including concrete
WireGuard/Ambient state and the first Stop. TagSequenceClaims derives the
linked history from those same runs. Statements adds one literal headline.
No frame file is needed. The package adds five theorems, five ordinary
definitions, three inductives and one structure in three modules.

Every normal finite execution has exactly the supplied operation order and
linked all-peer tag effects. Initiation creation/consumption retain their
arbitrary-tag restart behavior; the response/session old-tag guards remain
derived. Normal refusals stutter the tag map, not necessarily other state.
No residency, readiness, coherence or reference premise is supplied.
A later Stop returns no partial history. This does not establish driver
scheduling, initialized reachability, slot coherence or allocation-lifetime
confirmation, and does not discharge the separate RestartFrames scope issue.

Probes 1 and 2 fail four and six bind/consumed-variable diagnostics, with no
warnings. Changed probes 3--5 pass the full package, narrowed split imports,
five standard-only axiom roots and standalone Model. Root and independent
review find no issue. The Noise closure builds in 164 jobs without warnings.
No mirror change is requested.

## H4 continuation: arbitrary-list mixed fwmark/scalar readback

The actual fwmark request now composes with its scalar suffix and the original
fitting getter for arbitrary finite peer lists. The real captured list drives
all source/cache clears, including repeated visits. The selected peer can be
unlisted; its scalar update still occurs, and its existing source/cache fields
then survive. Every listed occurrence is serialized with the actual endpoint
attributes and the selected scalar change where applicable.

This is Ensures, not total return: missing listed peers in the native setter
and unavailable reset records retain their Stops. The public getter composition
requires listed residency, empty allowed-IP lists, fitting capacity and idle
socket/selector state, with the existing creating-network, stopped-device and
selected-reference premises. A malformed second peer returns -EINVAL only
when the earlier reset prefix normally completes; the earlier mark, generation,
clears and scalar writes remain reflected in the result.

MultiMixedModel defines the pointwise clear store and final effect.
MultiMixedEffects derives resident/dump field effects; MultiMixedFrames
separately preserves fields outside peers relative to the updated base.
MultiMixedSource factors the actual whole setter; MultiMixedClaims joins
the actual setter and getter; Statements appends one literal headline.
Six theorems, two definitions and five modules are added. The final Device
relation is exact outside peers, with pointwise peer contents and existential
final reset times. It is not a per-visit reset transcript or a fixed TreeMap
representation. JSON and socket state are exact. Global ownership and
cross-peer pagination remain open.

Probe 1 fails five congruence/source-record/inference diagnostics and emits
one unused-simp warning. Changed probes 2 and 3 pass source/residency and pure
effects. Probe 4 fails two serialization/projection composition diagnostics;
changed probes 5 and 6 pass the whole set/get and narrowed split package,
including all six standard-only roots, without warnings. No limit is raised.
Independent review finds no defect and confirms the normal-return and
pointwise-effect qualifications above. The installed closure builds 313 jobs,
with only the inherited Env warning.

## H6 continuation: initialized give-up cleanup witness

The [initialized give-up report](2026-10-17-proof-campaign-2-initialized-giveup.md)
records an accepted 23-operation generated history through the actual runner,
using the existing boundary observer and its exact erasure. Nineteen retries
produce twenty initiations; callback twenty gives up and enqueues zero-key
cleanup at stamp 21. Every boundary has zero keypair counter, empty key store
and empty slots, and every per-operation log lacks keypair allocation/session
decisions. Original and audited complete JSON agree.

Source inspection of the C's partial-exchange cleanup agrees with a statement
artefact, not a mirror defect. This is recorded-arm runtime evidence with
generated inputs, not Linux capture, all-mode evidence or a kernel-proved closed
trace. It receives zero theorem/headline credit. The standalone module has
ten private executable definitions plus main; the generator and report carry
the reproducible inputs/conclusion, with no committed logs. The larger
session-relative history theorem remains open.

The scratch run passes first time with --root .; independent review finds no
semantic issue and requests a precise keypair-allocation label, which is fixed.
The installed command also passes without warnings. The standalone module
builds 71 jobs with the inherited Env warning. No failed runtime run or
infrastructure retry occurs.

Final combined audit checks 1,528 logical roots in 337 modules, including
1,007 public theorem roots and the standalone runtime entry, all standard-only.
Fresh replay passes on Noise.Statements, Config.Statements and the standalone
runtime module. Static checks, all 258 original terminal names/order,
diff formatting and mirror/shared boundaries pass. The census rises from
2,310/762/324 to 2,321/771/326 (theorems/modules/headlines).
No cap increase, guest run, main merge or push occurs. The inherited full gate
remains FAILED and is not rerun unchanged.

Reproduce the scoped builds and fresh replays on those three modules under
capped scripts/in-bundle with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
The runtime reproduction command is in its linked report.


## H2 continuation: owner coherence through actual handshake queueing

Both modes of original sendQueuedHandshakeInitiation now preserve
HashedOwnersCoherent on every normal return, with OwnerCoherentSafe as the
sole projected entry invariant. Actual false-mode attempt reset and true-mode
unchanged prefix remain distinct. The existing observers supply the actual
clock and queue-inspection result; their exact erasures identify the same
original run. Repeated peer writes are compared pointwise. Successful
acquisition supplies the reference restored on an already-pending refusal;
no residency, publisher, readiness, queue-state or reference-budget premise
is added. This is neither worker completion nor global reference ownership,
and it asserts no state after a Stop.

OwnerCoherenceQueuedFrames contains the one pure preservation fact for
queuedDeviceAfterInspection. OwnerCoherenceQueuedClaims contains the projected
whole-call theorem; Statements adds its literal wrapper. Three theorems, two
modules, no new definitions or shared variants: H2 reaches 465 theorems and
85 headlines. The obsolete queuedDevice approximation is not used.

Probe 1 fails five proof-form diagnostics and probe 2 fails two; neither emits
warnings. Changed probes 3–5 pass: complete candidate, exact split package
with all three standard-only axiom roots, and standalone narrowed Frames.
The scoped build passes 356 jobs with only inherited Env:865 String.mk.
Independent review finds no issue. No limit change or infrastructure rerun.

## H3 continuation: the original cookie-message branch

Every normal type-3 receiveHandshakePacket call preserves all remote endpoints.
The actual cookie path runs lookup, optional decryption and cookie-field update,
then releases its held reference. Existing generic lookup contracts supply
that reference even for arbitrary aliases and owner words; the new write
preserves both the endpoint and reference. No coherence, residency, clock,
decryption-success, packet-length or reference-budget premise is introduced.
The native frame preserves the full optional Endpoint map; the projected
headline promises remote family/address/port/IPv6 scope. It retains actual
Stops and does not claim totality or post-error rollback.

CookieEndpointFrames holds the native preservation theorem;
CookieEndpointSource is the exact original type-3 source factor, including
errors; CookieEndpointClaims and Statements connect the lifted whole call
through the campaign projection. Four theorems in three modules bring H3 to
190 theorems and 18 headlines. No definition or shared variant is added.
The deferred cookie-reply/socket layer is not needed for this branch.

Probe 1 fails 11 elaboration errors and six warnings; probe 2 fails four
errors without warnings. Recovery placeholders in those failed drafts are not
accepted. Changed probes 3–4 pass the complete candidate and exact split
package with four standard-only axiom roots, without warnings. The scoped
build passes 145 jobs without warnings. Independent review finds no issue;
its scope is this receiver branch, not queue provenance or full H3.

## H5 continuation: recorded idle-wait wheel completion

Every normal recorded idleTimers return stores its actual end-of-wait read
and satisfies TimerWheel.nextDue = none at that read. Device absence is
allowed. The source suffix keeps pass bound and end read separate; this caller
supplies equal values. The actual guard excludes its due branch because all
of that branch's worker/lookahead outcomes stop. The following Ambient-only
clock read cannot change WireGuard state, and the final write changes only
jiffiesLast. No frame lemma is added for that type-given fact.

NoTimerDue means exactly the wheel's nextDue test over resident IDs in
device.peerList and their wheel entries. It does not establish peer-list/store
or wheel/expiry coherence, absence of timers on unlisted residents, successful
execution for arbitrary records, global work emptiness or recordless behavior.
The differing pass bound in afterAdvance is not silently equated with its
end read.

TimerWaitModel holds the predicate; TimerWaitSource contains the actual suffix,
its guard/suffix contracts and exact recorded idle source equation;
TimerWaitClaims and Statements contain the projected claim and wrapper.
Five theorems and two definitions in three modules bring H5 to 301 theorems
and 45 headlines. No shared variant or mirror change is needed.

Development probes 1–6 fail respectively 3, 2, 1, 1, 1 and 1 proof-form
errors; only probe 1 emits warnings (five). Probe 7 passes the guard.
Probe 8 fails four suffix/source proof-form errors; probe 9 fails one and
emits one unused-simp warning. Changed probe 10 passes the complete package;
probe 11 passes the exact split and all five axiom roots, standard only.
All final proofs use default limits, without suppression or cap changes.
The scoped build passes 278 jobs with only inherited Env:865 String.mk.
Independent review finds no issue and confirms the nextDue scope above.

The three-result continuation adds 12 theorems, eight modules and three
headlines: 2,333 theorems in 779 owned modules, 329 headlines. The combined
axiom audit checks 2,041 logical roots in 425 modules, including 1,321 public
theorem roots, standard only and without diagnostics. All three fresh kernel
replays pass. Static trust/import checks, all 258
original terminal names/order, and mirror/shared-layer boundaries pass.
No infrastructure rerun occurs. All H1–H6 remain in progress; the inherited
CounterWindow/ReplayWindow full-gate failure is unchanged and is not rerun.

Reproduce the scoped build and fresh replay for
Leanux.Proofs.WG.Index.Statements, Leanux.Proofs.WG.Roaming.Statements and
Leanux.Proofs.WG.Progress.Statements with scripts/in-bundle under capped,
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. Existing ranked mirror requests
are unchanged; no mirror-team change is requested for these local contracts.


## H4 continuation: endpoint-aware finite IPv4 pagination

The whole original getter now handles arbitrary endpoint fields on its existing
finite single-peer IPv4-list domain. The first capacity includes the actual
endpoint cost, (Q - D - (peerFixedSpace p + 4)) / 28. The progress premise is
D + max 168 (peerFixedSpace p + 32) ≤ Q: it specializes to the previous D+168
bound without an endpoint, while making room for the first IPv4 item with
either endpoint family. First-boundary freshness and DATA/DONE counts use
this capacity. Resumed pages keep the original 44-byte overhead and 28-byte
IPv4 items; their induction and transport remain unchanged.

The claim derives every actual first callback and resumed receive; it does
not assume successful execution. Empty, fitting and arbitrarily many pages
within the calculated 4096-receive bound produce the exact suffixJson,
preserve the whole initial Device and finish the actual selected socket.
Singleton/listed/resident, readable IPv4 nodes, canonical boundary freshness,
capacity and idle/empty selector inputs remain explicit. Repeated IDs away
from cursor boundaries are allowed. This does not prove weighted IPv4/IPv6
packing, multi-peer pagination, ownership or reachability.

Endpoint output means the mirror's original peerFixedAttrs serialization.
AF_INET becomes JSON family 4; any other present family becomes family 6.
Addresses are truncated to the serialized 4/16-byte width, and IPv4 omits
IPv6 flowinfo/scope; source-cache fields are also absent. For an unsupported
family the mirror charges no endpoint attribute space while still producing
its IPv6-shaped JSON. The theorem follows those definitions for arbitrary
states; it does not assert raw-field retention or that such a state is
reachable from initialization. Independent review identified the terminal
docstring's raw-retention wording as a P3 overclaim. The wording was corrected
before the build; the formula and proof did not change. No other finding.

EndpointPaginationModel holds four data definitions, a capacity bound and
exact no-endpoint compatibility. EndpointPaginationFirstSource supplies
the actual endpoint-aware first prefix and fitting/splitting callbacks;
EndpointPaginationCoalesceClaims holds the two finite coalescing laws.
EndpointPaginationTransportSource and Source supply thin start/complete
adapters and compose the existing ipv4ResumeDrain_returns. Claims and
Statements supply the projected whole getter and literal wrapper.
Thirteen theorems in six modules bring H4 to 676 theorems and 91 headlines.
No old signature, existing induction, shared layer or mirror definition changes;
no new frame family is copied.

Probe 1 fails seven parse/arithmetic diagnostics; probe 2 fails one default
recursion-depth check. Abstracting the common continuation head resolves it
without raising limits. Changed probes 3–4 pass the first/whole transport.
Probe 5 fails two no-endpoint constant reductions; changed probes 6–7 pass the
whole claim and exact narrowed split with all thirteen standard-only roots.
No probe emits a warning. The scoped build passes 319 jobs with only inherited
Env:865 String.mk. The closure audit checks 1,127 logical roots in 255 modules,
including 770 public theorem roots, standard only and without diagnostics.
Fresh kernel replay passes. Static checks, original 258-name order and
mirror/shared boundaries pass. No infrastructure rerun or cap/limit increase.

Current totals: 2,346 theorems, 785 owned modules, 330 headlines. All H1–H6
remain in progress. The inherited CounterWindow/ReplayWindow gate failure
remains unchanged. Reproduce the scoped build and fresh replay of
Leanux.Proofs.WG.Config.Statements with scripts/in-bundle under capped,
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. Existing ranked mirror requests
are unchanged; this extension needs no mirror-team change.


## H2 continuation: new-handshake and zero-key callback coherence

Original expiredNewHandshake and expiredZeroKeyMaterial now preserve the
local hashed-owner invariant on normal return, with OwnerCoherentSafe as
their sole projected entry condition. The former composes actual endpoint
source/cache clearing and both-mode handshake queueing. The latter derives
the held reference from successful actual peerGet; its compensating put
therefore cannot be the last release. Actual queue membership and
peekQueuedUnit remain separate inputs to the original branch. The alternate
path records and enqueues clear work. Neither branch assumes the later
worker's release coverage or completion.

Optional Device, arbitrary Ambient, aliases and unpublished owner words
remain allowed. Missing state, zero/overflow reference checks and clock/record
failures retain their original Stops. This is local normal-return coherence,
not queue consistency, reachable global ownership or failed-call rollback.

OwnerCoherenceCallbackFrames holds the endpoint-source preservation variant.
OwnerCoherenceCallbackSource holds the acquisition-effect variant, deriving
residency and count greater than one. Both names cite the corresponding
C1 WGBase helper; proofs reuse owned exact source contracts. CallbackClaims
and Statements supply the two projected claims and literal wrappers.
Six theorems in three modules bring H2 to 471 theorems and 87 headlines.
No new definitions or shared-layer edit.

Probe 1 fails three proof-form diagnostics without warnings; changed probe 2
passes the complete candidate, probe 3 the exact split and six standard-only
axiom roots, and probe 4 standalone narrow support. Independent review finds
no semantic issue. Its two P3 findings are corrected separately: acquisition
is an effect, so it moves from Frames to Source; terminal wording now says
endpoint-source/cache clearing, since the remote endpoint is preserved.
No formula or premise changed. The final source organization is built and
replayed below.

## H4 continuation: endpoint-aware setter/readback composition

The actual mixed fwmark/scalar and private-key requests now compose with the
endpoint-aware finite IPv4 getter. The old no-endpoint claims remain unchanged.
Both new claims derive every getter input from the same actual normal setter
successor and its remaining Ambient inputs; no callback/receive-success
premise is supplied. Explicit readbackFrame contracts transport socket and
selector state, rather than inferring them from Device effects.

The mixed request retains its singleton, creatingNet, lookup/resident,
live/reference-bound and stopped-device domain. It changes the actual
endpoint source/cache fields; only their serialized remote endpoint fields
agree with the pre-clear value. A later malformed peer returns -EINVAL after
the earlier mark and scalar writes, while reset-record Stops remain Stops.
The key request retains its established/changed/no-collision domain and
derives its actual expiry timestamp and ordered key effects. Capacity and
boundary calculations use the effective installed identity, including
clamping and null-key serialization, not the initial identity.

EndpointPaginationCapacityFrames transports freshness and DATA/DONE count
from equal serialized prefix sizes. MixedEndpointPaginationClaims and
KeyEndpointPaginationClaims hold the two projected compositions; Statements
adds two literal wrappers. Five theorems in three modules, no definitions,
bring H4 to 681 theorems and 93 headlines. The endpoint getter and resumed
induction are reused unchanged. Single-peer IPv4 list, fresh cursor boundaries,
capacity, bounded receive count and idle/empty socket premises stay explicit;
global ownership and multi-peer/mixed-family pagination remain open.

Both development probes pass without warnings: full three-theorem composition,
then exact split package with the two wrappers and five standard-only axiom
roots. Independent review finds no issue, confirming same-run linkage,
effective key capacity and serializer rather than raw-endpoint equality.

Combined validation: the Index/Config scoped build passes 523 jobs, then the
terminal wording correction rebuilds Index in 360 jobs. Only inherited
Env:865 String.mk appears. The combined axiom audit checks 2,004 logical roots
in 459 modules, including 1,382 public theorem roots, standard only and without
diagnostics. Fresh kernel replay passes for both changed roots.
Static trust/import checks, all 258 original headline names/order and
mirror/shared boundaries pass. No default limit/cap change, suppression,
infrastructure rerun or unchanged failed-source rerun occurs.

Current totals: 2,357 theorems in all 791 owned modules, 334 headlines.
All H1–H6 remain in progress; the inherited CounterWindow/ReplayWindow gate
failure is unchanged. Reproduce the scoped build and fresh replay of
Leanux.Proofs.WG.Index.Statements and Leanux.Proofs.WG.Config.Statements with
scripts/in-bundle under capped, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
Existing ranked mirror requests are unchanged; these steps request no mirror
change. The two named native helper variants are listed in the shared-frame
followup for eventual unification.


## H2 continuation: both retransmission callback branches

The whole original expiredRetransmitHandshake preserves OwnerCoherentSafe
on every normal return under that sole entry invariant. Retry increments the
attempt count, clears endpoint source/cache fields and queues the handshake
through existing contracts. Give-up deletes the keepalive timer, purges staged
data, and conditionally arms zero-key cleanup through the exact all-mode arm
effect. Owner words and counts survive all of these writes pointwise, with
aliases allowed.

No residency, readiness, running/alive, pending-timer, consistent-wheel,
reference-budget or successful-arm premise is added. The caller clock still
precedes the arm guard; a down/dead guard is not treated as a guaranteed
successful no-op. Missing state, clock/cache/reference/queue and wheel failures
remain actual Stops. This does not establish callback totality, outer timer
selection or the remaining keepalive callbacks.

OwnerCoherenceRetransmitFrames contains the pure arm-effect transport and
three named C1-family variants: WGBase.delTimer_spec and
WGTransitions.purgeStagedPackets_spec/modPeerTimer_spec. The proofs reuse
owned delTimer_exact and GuardedArmingClaims.modPeerTimer_effect; no hidden,
armTimer or wheel-placement implementation layer is copied. Claims and
Statements contain the projected whole-call theorem and literal wrapper.
Six theorems in two modules, no definitions: H2 reaches 477 theorems and
88 headlines.

Development probe 1 fails six proof-form errors and three unused-simp warnings;
probe 2 fails one false-branch normalization error without warnings. Changed
probes 3–5 pass the combined candidate, exact split with six standard-only
axiom roots, and standalone narrow Frames. The scoped build passes 364 jobs
with only inherited Env:865 String.mk. The closure axiom audit checks 1,362
logical roots in 300 modules, including 910 public theorem roots, standard
only and without diagnostics. Fresh kernel replay passes. Independent source
review finds no issue in the whole callback, all arm modes or variant scope.

Current totals are 2,363 theorems in all 793 owned modules, 335 headlines.
Static trust/import checks, original 258-name order and mirror/shared
boundaries pass. No limit/cap change, suppression or infrastructure rerun.
All H1–H6 remain in progress; the inherited full-gate failure is unchanged.
Reproduce build and fresh replay of Leanux.Proofs.WG.Index.Statements under
capped with scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
No new mirror request; the three bounded variants are listed in the existing
shared-frame followup.


## H5 continuation: the actual post-advance wait bounds

The original afterAdvance now has an operational receipt for its actual
lastAdvance pair and non-consuming end peek. Dropping the receipt gives the
complete original operation, including both recordless branches and every
Stop. The recorded normal-return claim has only hidden.isSome as its entry
condition. It derives a present receipt, the final stored end read, and the
original no-due-wheel guard at the pass selected by wrapped timeAfter.

The pass is the end read when timeAfter selects it and otherwise the stored
pre-advance bound. The final clock always stores the end read. No linear time
order, preceding advance execution, record freshness, callback success, device
presence, queue emptiness or totality is assumed or concluded. The source
provenance theorem exposes the real fixture read without extending the
campaign projection or reconstructing a World from it. Peek and consuming
read agree in value on normal return; record identity is not asserted.

AdvanceWaitModel holds the receipt and pure pass function; Source holds the
exact prefix/suffix decorator, erasure and native provenance; Claims and the
literal Statements wrapper use Product. No Frames file is needed: the pure
prefix reads do not mutate state and the existing timer-wait suffix contract
supplies the effect. Six theorems in three modules bring H5 to 307 theorems
and 46 headlines. No shared variant or mirror change.

Draft probes 1–6 fail ordinary congruence, discard, typed-throw, identifier and
state-normalization obligations. Their rejected axiom queries are not accepted
proofs. Changed probe 7 closes the full candidate; probe 8 checks the exact
split and all six standard-only roots at default limits, without warnings.
Independent review finds two documentation errors, both corrected before the
build: a prefix-run typo and wording that failed to distinguish stored end
from checked pass. The formulas do not change.

## H4 continuation: exact mixed-width dump scans

Four new data definitions represent actual per-node space, serialized JSON,
the mapped JSON array and summed space. Six source theorems prove the exact
readNode/getAllowedips result, complete and first-failing weighted scans,
their original sequence/cursor wrappers, and the actual first dump callback's
split. IPv4-width nodes cost 28 bytes and every other stored width costs 40;
the JSON family branch and masking still use the original node fields.
This arbitrary-width source contract is not a valid-IPv6 or topology claim.

Readability is required only for nodes actually read. Duplicate identifiers
and an empty emitted prefix are allowed. A failed node put restores its
incoming skb; the enclosing allowed-IP nest must itself have fit. The
first-callback fact derives the actual fixed peer attributes, endpoint cost,
sequence, next cursor and DATA split. It adds no successful-call premise.
Complete mixed-family getter progress, weighted partitioning, cursor freshness,
transport and coalescing are still to compose; there is no new headline.

MixedDumpModel is data; LeafSource, ScanSource and CallbackSource are source
contracts. No new frame or shared variant is introduced. H4 now has 687
theorems and 93 headlines. The four modules are explicitly scoped roots/support
until the full getter composition imports them.

Development probes 1, 3 and 5 fail ordinary endian/room, Device-field and list
head reductions. Probe 1 also has two unused-simp warnings; probe 4 elaborates
but reports three deprecated lemma warnings. All are fixed. Changed probes
2, 6, 7 and 8 pass leaf/full/narrow packages; probe 9 passes the exact split
with six standard-only axiom reports and no warnings. The final author command
is capped scripts/in-bundle lake env lean --stdin, with LEAN_NUM_THREADS=32
and LEANUX_QEMU_SLOTS=16, no limit overrides; reported exit 0 in 0.93 seconds.
Independent source review finds no issue. The reviewer verifies the source
and logs; root validation below independently builds and replays the package.

Combined scoped build passes 334 jobs, with only inherited Env:865 String.mk.
The closure axiom audit checks 1,424 logical roots in 270 modules, including
866 public theorem roots; all are standard-only, with no diagnostics.
Fresh kernel replay passes for both changed roots.
Static trust/import checks, all original 258 headline names/order and
mirror/shared-layer boundaries pass. No infrastructure rerun, cap/limit
increase or warning suppression occurs.

Current totals are 2,375 theorems in 800 owned modules and 336 headlines.
All H1–H6 remain in progress. The inherited CounterWindow/ReplayWindow full
gate fails as previously recorded; it is not rerun unchanged.
Reproduce the scoped build and fresh replay for
Leanux.Proofs.WG.Progress.Statements and
Leanux.Proofs.WG.Config.MixedDumpCallbackSource under capped with
scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
Existing ranked mirror requests are unchanged; neither package requests a
mirror-team change.


## H2 continuation: a persistent-callback invariant counterexample

The proposed sole-OwnerCoherentSafe preservation claim for the whole
expiredSendPersistentKeepalive callback is false on arbitrary native states.
A checked coherent entry has caller peer 0's current-key slot name keypair 1,
whose peer word names peer 1. Actual staged sending acquires peer 1; dead-peer
data creation then releases caller 0's last reference. The callback returns
normally with a separately hashed keypair still naming the erased peer 0.
The explicit real birthdate record keeps the selected key valid.

The [finding](2026-10-17-proof-campaign-2-persistent-owner.md) gives the concrete
state, actual path and C correspondence. This is a missing slot/caller ownership
relation in a local arbitrary-state invariant. No accepted initialized trace,
mirror divergence or kernel defect is established. The separate send-keepalive
callback subsequently reads the erased caller and Stops on this witness, so
that callback is not refuted by the same normal-return argument. No premise
was silently added to force a positive theorem.

The model holds seven witness definitions and entry coherence; Source proves
the actual complete callback's total return; Claims and Statements refute
preservation over the projection. Four theorems in three modules bring H2 to
481 theorems and 89 headlines, with no frame/shared variant. Both broader
architectures were audited: direct native preservation needs six shared
send-path families, while existing owned fallback contracts cover absent or
invalid keys only. This larger overlap is inventoried rather than copied.

Ten changed-source probes were needed. Probes 1–9 fail respectively on map
lookups (4 errors/2 warnings), optional/total lookup mismatch (4/6), clock
metadata (1/2), passive-section reduction (1/2), signed expiry (1/2), errno
constants (1/1), Index adapter reduction (1/1), Ambient modification (1/2),
and execution witnesses/Except.map (2/2). All warnings are corrected.
Probe 10 passes with all four standard-only roots, no warnings or proof-limit
increase. The final split module organization is independently built below.
Independent source review finds no issue.

## H4 continuation: weighted plans, resumed callbacks and generic coalescing

WeightedPaginationModel greedily consumes exact 28/40-byte costs, proves
prefix decomposition/fit/first-failure maximality, and defines finite resumed
pages whose recursive remainder is strictly shorter. With at least 40 bytes
of node room, every resumed page is nonempty and fits. The first page may
be empty once. Concatenation preserves order and multiplicity; arbitrary
stored widths and duplicate IDs remain allowed. Boundary freshness is defined
against the whole previously emitted prefix and is a later composition
premise, not a property asserted of every plan.

WeightedPaginationSource derives the original resumed callback from its
actual cursor selection, fixed prefix and complete/split scans. Header room
implies at least 124 bytes for nodes. Resident nodes and cursor freshness
discharge every read and choice; no successful callback is supplied.
Claims presents its exact return and preserved Device over the projection.
Five data definitions and eight theorems occupy three modules. Four probes:
1 fails two local-let goals and one unused-simp warning; 2 passes the pure
model; 3 fails two 40+4 room normalizations; 4 passes all eight standard-only
roots without warnings. Independent review finds no issue.

GenericPaginationModel and Claims supply five pure JSON-list constructors
and two actual coalescer equalities. Any adjacent continuation can be merged
before the unchanged remainder, including later errors; every finite page
sequence coalesces to its concatenated entries. Empty/repeated pages and
arbitrary JSON and endpoints are allowed. This is a coalescer contract,
not a claim that a getter produced the pages. The first capped default-limit
probe passes with both standard-only roots and no warnings. Independent
review finds no issue. No existing IPv4 signature is changed.

These ten H4 declarations bring it to 697 theorems and 93 headlines. The
weighted actual first complete/empty branches, full callback/socket sequence,
DONE spill count and final getter composition remain open. The exact receive
count must include a separate DONE when the final DATA has less than 20 bytes
left, including a genuinely empty input. The implementation will reuse the
generic receive-sequence theorem; no resumed IPv4 transport induction or
shared layer is copied.

Combined scoped build passes 400 jobs, with only inherited Env:865 String.mk.
The axiom audit checks 1,533 logical roots in 336 modules, including 1,010
public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes for all three changed roots.
Static trust/import checks, all 258 original headline names/order and mirror/
shared boundaries pass. No cap/limit changes, suppression or infrastructure
reruns. Current totals: 2,389 theorems in 808 modules and 337 headlines.

All H1–H6 remain in progress. The inherited full gate remains FAILED in
CounterWindow/ReplayWindow and is not rerun unchanged. Reproduce the scoped
build and fresh replay of Leanux.Proofs.WG.Index.Statements,
Leanux.Proofs.WG.Config.WeightedPaginationClaims and
Leanux.Proofs.WG.Config.GenericPaginationClaims under capped/scripts/in-bundle
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. No new mirror-team request.


## H5 continuation: actual advance syscall and runner linkage

The complete original wg_advance syscall now has an erased operational
receipt. Every normal return gives result zero and the bounds written by that
same actual advance, with j1 - j0 = ticks.toUInt64. The descriptor, entry guard,
fdput, return work and afterAdvance remain in their original order with every
Stop. If the actual wait returns a recorded receipt, its bounds equal this
advance's bounds; the final clock stores jEnd and NoTimerDue holds at the
distinct wrapped pass. No entry-mode preservation through arbitrary task work
or successful execution is assumed.

AdvanceOperationSource contains three action definitions, actual advance
effects and exact syscall erasure. Claims uses Product. RunnerAdvanceSource
connects the same execution through the real runnerEntry and skipAmbient to
the existing boundary guards. The runner source is imported by Statements,
so its proof is included in that closure. FS fixture preservation is local
reasoning from liftFS writeback, without a named cross-subsystem frame.
Six theorems in three modules bring H5 to 313 theorems and 47 headlines.

Changed probes 1–4 fail ordinary source factoring with error/warning counts
3/2, 5/7, 1/2 and 1/2. Probe 5 closes the three source facts. Probes 6–9 fail
8/1, 2/3, 5/0 and 1/0, from reserved/constructor-like names, discard/tuple
normalization and names eliminated by case substitution. Probe 10 checks the
exact split and six standard-only roots, no warnings. All outputs were
inspected; no rejected recovery declaration counts as proof. Independent
review finds no issue. Root corrects the entry definition's comment, which had
described the broader prefix rather than entry resets and the guard.

## H4 continuation: original first callback and dump start

WeightedStartModel distinguishes empty input from an empty first emitted
prefix of nonempty input. Source derives the original first callback's full
DATA, room, sequence and cursor for empty, complete and split cases. All
inputs need the header bound; only nonempty input needs its allowed-IP nest
to fit, and the first node need not fit. The actual netlinkDumpStart follows
through existing transport contracts to the exact socket. Completion retains
the real inline-DONE versus separate-DONE choice, including empty input.

Claims provides the two projected total-return contracts. The two data
definitions and five theorems occupy three modules; H4 now has 702 theorems
and 93 headlines. The first draft fails seven syntax/shape errors and four
recovery/unused-variable warnings; its recovery axiom output is rejected.
Changed probe 2 passes the exact package and five standard-only roots without
warnings. Independent source review finds no issue. Full receive sequence,
exact envelope count, coalescing and whole weighted getter composition remain
open; no shared variant or copied receive induction is introduced.

H5's scoped build passes 284 jobs, including its source-link import update;
H4's source build passes 120 jobs. Only the inherited Env:865 String.mk
warning appears in the H5 build. The combined audit checks 1,468 logical roots
in 284 modules, including 893 public theorem roots, standard-only and without
diagnostics. Fresh kernel replay passes both changed roots. Static trust/import
checks, all 258 original headline names/order and mirror/shared boundaries
pass. No cap/limit change, warning suppression or infrastructure rerun.

## Completion audit and documentation corrections

H1 already covers all seven tag-changing whole operations and their actual
finite mixed histories. Option-valued slots supply per-slot capacity; they do
not imply distinct slots or a three-key store bound. The current header and
register are narrowed accordingly. Confirmation across reinstallation remains
open; consecutive confirmation is not once-per-allocation-lifetime uniqueness.
Unconditional whole-call totality is not an extra requirement. No Noise
theorem changes in this documentation correction; its comment-only rebuild
passes 164 jobs without warnings.

The H5 audit found two stale present-tense claims: the old cookie paragraphs
still promised arbitrary-ring drain/suffix decrease, and mirror request 1 still
called its corrected-refusal carry pending. Both are corrected in place.
The historical claims/evidence retain their pins; current cookie contracts
preserve bounded outcomes/errors, and the actual backlog trace and audit now
have checked rejection equations. This is a documentation repair, not a new
mirror request or a change to the already checked statements.

[AGENT 2026-10-17] Describe operational refusal with the actual named Stop
constructor rather than treating every refusal as outsideDomain: trailing
records/suspension use hidden and pending NET_RX uses invariant. These are
fail-closed outcomes, not accepted-backlog counterexamples.

Finite recursion/ranges bound the explicit outer iterations provided their
bodies terminate, but a total logical
denotation does not itself prove executable termination of loop-backed helpers.
At this checkpoint the modular-power helper had a checked finite-evaluation
bridge, while arbitrary exact-count allocation remained beyond the single
successful keypair-allocation case. The later exact finite allocation tranche
closes that iteration gap. Further H5 work includes derived-fuel adequacy with callback refill and an
initialized queue/pending-work consistency invariant strong enough to lift
the exact local completion guards to all accepted operations. Fairness,
erasing physical stale ring slots, disarming future timers and unconditional
recordless success are separate stronger questions.

Two architectures remain inventoried: represented-ring/resource composition
using C1 Queues, RingGeometry and RingSteps plus actual record histories; or an
initialized runner invariant using C1 RxRing/RxEnv/JointSyscalls/JointRunner.
Neither is copied locally. Arbitrary malformed-ring counterexamples do not
establish initialized accepted executions. The existing callback-refill mirror
request remains separate from any attempt to increase a budget constant.

Current totals: 2,400 theorems in 814 owned modules and 338 headlines.
All H1–H6 remain in progress; the inherited full gate remains FAILED.
Reproduce the changed closures with scoped build and fresh replay of
Leanux.Proofs.WG.Progress.Statements and
Leanux.Proofs.WG.Config.WeightedStartClaims under capped/scripts/in-bundle,
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H1 continuation: direct reinstallation and the confirmation domain

The broad local wording, confirmation succeeds at most once for a resident
key, is false when arbitrary direct installation-helper calls are admitted.
The checked witness starts with one positively referenced responder key at ID
0, internal serial 17, and one peer with next = 0 and other slots empty.
The original sequence receivedWithKeypair 0 0; addNewKeypair 0 0;
receivedWithKeypair 0 0 returns true twice. The entire resident key, global
keypairCounter and device allocation cursor are unchanged. The final previous
and current slots both contain 0; next is empty. Every Ambient is permitted.

This is a statement-domain finding, not an initialized accepted trace or a
mirror/kernel discrepancy. The arbitrary entry does not establish an
allocation history; the direct helper does not allocate. Consequently the
fresh beginSession installation language and once-per-allocation-lifetime
claim remain open, with their larger transport inventory unchanged. The
existing adjacent-call no-repeat theorem remains valid. No premise is added
to it and no mirror-team repair is requested.

ConfirmationReinstallModel gives the concrete data and entry shape; Source
runs the three actual calls through the existing exact rotation factors;
Claims and the terminal expose the observation over the campaign projection.
Four theorems in three modules bring H1 to 235 theorems and 33 headlines.
No frame or shared variant is added. Independent review corrects “allocation”
to “positively referenced responder key” in the entry description, since
residency and a positive refcount alone do not establish allocation provenance.
No formula/domain issue remains.

Changed probes 1–3 fail on private-write reduction, existential witnesses and
the final peer witness; probe 1 also has four unused-simp warnings. Probes
4–5 pass, the last checking the exact split and four standard-only roots.
The installed scoped build passes 167 jobs without warnings.

## H5 continuation: the actual send-worker completion guard

Normal runSendWorkers return now guarantees absent Device or an empty final
sendWorkQueue, for both record modes and arbitrary entry state. The exact
source factor retains initial Device absence, requireNoCryptWork, queuedThisCall
reset, captured budget, every worker/scheduler call and every Stop. A completed
turn has observed an empty send queue and then run actual deliverSent, whose
existing named Device frame transports that fact to return. Finite-loop
induction follows the actual early-return branch; exhaustion reaches the real
budgetExhausted and cannot be accepted as completion in either mode.

SendCompletionModel contains the projected predicate; Source contains the
concrete loop factor and reasoning; Claims and Statements use Product.Ensures.
This adds five theorems in three modules, bringing H5 to 318 theorems and
48 headlines. It does not prove successful completion, fuel adequacy,
pendingWork/ring consistency, whole-operation emptiness or fairness. No
additional shared frame is copied. Independent source review finds no issue.

Changed probes 1–3 fail respectively with 6/10, 3/0 and 2/0 error/warning
counts, on option matching, lifted reads, eliminated names and budget-error
reduction. Probes 4–5 pass; the exact final split checks five standard-only
roots without warnings. Installed build passes 287 jobs, with only the
inherited Env:865 String.mk warning.

The combined axiom audit checks 1,537 logical roots in 295 modules, including
936 public theorem roots, using standard axioms only and no diagnostics.
Fresh kernel replay passes both changed terminal roots.
Static trust/import checks, all 258 original terminal names/order and mirror/
shared-layer boundaries pass. No proof-limit/cap change, suppression or
infrastructure rerun occurs. Totals are 2,409 theorems in 820 owned modules
and 340 headlines. All H1–H6 remain in progress; the inherited full gate
remains FAILED and is not rerun unchanged.

Reproduce with scoped build and fresh replay of
Leanux.Proofs.WG.Noise.Statements and Leanux.Proofs.WG.Progress.Statements
under capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H5 continuation: final idle waits at syscall and runner return

The original wgSet, wgInject, wgXmit and wgBatch syscall tails now have exact
final-wait observers. The prefix retains actual network entry resets/guard,
dispatch, tail calls, task work, and the correct send/afterXmit worker
continuation. Erasing the receipt yields the original syscall with the same
numeric result and every Stop. A receipt exists exactly when the actual idle
wait entered recorded mode; its value is the clock stored by that wait.
A present receipt proves NoTimerDue at the final syscall state. Recorded mode
at syscall entry is not assumed to survive arbitrary preceding work.

The actual runner operation executes that same observer at runnerEntry,
then its real skipAmbient and completion guards. Ambient stripping preserves
the clock/wheel fact by the lift's writeback type, without a new frame lemma.
Negative syscall returns remain included. wgUp is excluded because routing
work follows its wait. Nothing here establishes queue/ring/pendingWork
consistency, successful execution, future-timer absence or recordless no-due
behavior.

IdleOperationModel names the four accepted syscall forms; Source contains
the exact factors/erasures and read-only observer definitions; Claims contains
the three projected receipt facts; RunnerIdleOperationSource contains the
actual runner link and is imported by Statements. Eight theorems in four
modules bring H5 to 326 theorems and 49 headlines. Independent review finds
three overbroad comments on unrestricted helper definitions/theorems; they
are qualified by HasFinalIdleWait. Exact erasure and the terminal already
have that restriction, so no formula changes.

Six changed-source probes: 1 fails three read-normalization/witness errors
and four unused-simp warnings; 2 passes the first five facts; 3 fails one
projected-mode reduction and one unused-simp warning; 4 fails two uses of
Syscall where the runner needs Operation; 5 passes all eight facts; 6 passes
the reordered exact split and all standard-only roots, without diagnostics.
Recovery declarations from failed probes are not accepted trust evidence.
The installed scoped build passes 291 jobs, with only inherited Env:865
String.mk. The axiom audit checks 1,207 logical roots in 227 modules,
including 738 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes the changed terminal root. The subsequent
comment-only clarification rebuild also passes 291 jobs.
Static trust/import checks, all 258 original terminal names/order and the
mirror/shared-layer boundaries pass. No cap/limit increase, suppression or
infrastructure rerun occurs.

Current totals: 2,417 theorems in 824 owned modules and 341 headlines.
All six results remain in progress; the inherited full gate remains FAILED
and is not rerun unchanged. Reproduce with scoped build, axiom inspection
and fresh replay of Leanux.Proofs.WG.Progress.Statements under
capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: complete finite mixed-width getter

The original wgGetDevice now returns the exact single-peer JSON for a finite
readable allowed-IP list of arbitrary stored widths, under an exact receive
count of at most 4096. Greedy pages use the actual 28/40-byte costs. The count
includes each DATA envelope and an extra DONE envelope precisely when the
final DATA leaves less than 20 bytes. Empty input and a nonempty input with
an empty first fitting prefix retain their distinct raw attribute shapes.
Coalescing preserves every original occurrence in order.

Static premises are one listed resident peer, its exact list and node
residency, first-header and conditional nest room, resumed cursor freshness
against all earlier emissions, an idle empty socket7 and interface selection.
No actual callback/receive success, readiness or global ownership invariant is
assumed. IDs may repeat away from resumed boundaries; endpoints remain
arbitrary. Non-32-bit stored nodes use the original family-6 mask/hex branch,
without claiming those arbitrary widths are valid IPv6 configurations.

The source derives an internal indexed receive receipt from actual first and
resumed callbacks, including exact socket state at every receive. That receipt
is not a public premise. The existing getterReceive_sequence supplies the
only getter-loop induction; no IPv4 drain layer or shared frame is copied.
The final total-return theorem preserves the entire Device and gives the
exact completed, empty socket. The source count is also the number of receives
constructed by that receipt.

WeightedGetterModel holds count/message/freshness definitions and the pure
resumed-prefix equation. WeightedReceiveSource, WeightedTailSource and
WeightedGetterSource hold actual transport, coalescing and whole-call
composition; WeightedGetterClaims and Statements expose the projection.
Five definitions and ten theorems in five modules bring H4 to 712 theorems
and 94 headlines. No new frame is needed. Root independent review of all
files, planner and existing receive contracts finds no issue.

Nine changed-source probes: 1 fails constructor/layout syntax with recovery
warnings; 2 fails an array conversion name; 3 fails transitivity, array
rewrite, positivity and termination arithmetic, plus a deprecated rewrite;
4 fails array normalization and a deprecated integer rewrite; 5–6 fail
nil-array/freshness layout; 7 fails record-update normalization. Failed
recovery/sorry or misleading empty-axiom reports are rejected. Probe 8
passes all ten mathematical roots; 9 passes the corrected literal terminal
namespace. Both final passes have only standard axioms and no warnings.

Root installation also catches a namespace guard mismatch before wiring the
headline. The intervening cached old-root build is not evidence for the new
package. After correcting the installation, the new scoped closure passes
337 jobs, with only inherited Env:865 String.mk. Axiom inspection checks
1,181 logical roots in 273 modules, including 803 public theorem roots,
standard-only and without diagnostics.
Fresh kernel replay passes the changed Config terminal root.
Static trust/import checks, all 258 original terminal names/order and
mirror/shared boundaries pass. No cap/limit changes, suppression or
infrastructure reruns.

Current totals: 2,427 theorems in 829 owned modules and 342 headlines.
Multi-peer pagination, broader mixed setters, ownership and queued cleanup
remain open; no whole charter result is completed. The inherited full gate
remains FAILED and is not rerun unchanged. Reproduce the build, axiom
inspection and fresh replay of Leanux.Proofs.WG.Config.Statements under
capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H2 continuation: successful session publication with an aliased old slot

The [session-alias finding](2026-10-17-proof-campaign-2-session-alias.md)
checks an entry satisfying table safety, hashed-owner coherence and the key
store bound. Its old previous slot names the absent next allocation ID.
The original beginSession allocates that key, releases it during responder
rotation, then publishes its index row and returns true. Its immediate
original lookup stops at the missing owner object. Numeric table safety
survives, but owner coherence does not. Actual allocation/birthdate records
and the derived release readiness retain arbitrary other native/Ambient
fields; no successful intermediate execution is supplied.

This tests a local invariant, not initialized reachability. The checked C
ordering agrees, but no reachable C-state argument is made. No mirror
repair is requested. The alternative positive handoff architecture needs
the existing SessionRotationFresh premise; adding it would name an unresolved
caller obligation, not derive it from the three tested invariants.
The actual-effect witness instead settles their insufficiency without
copying a shared family. Primitive uniqueness, exact lookup and collision
clauses were already checked; broader initialized driver coherence remains
open.

SessionAliasModel gives eight witness/input definitions and the entry
invariants. Source derives the real rotation effect, total session return and
exact lookup Stop; Claims and Statements expose both executions over the
projection. Six theorems in three modules, including one private effect fact,
bring H2 to 487 theorems and 90 headlines. Independent source/domain review
finds no issue.

Probe 1 fails three role/cursor/count reductions with one unused-simp warning;
2 passes the session witness; 3 fails one final throw/string normalization;
4 passes the full finding; 5 passes the exact split and all six standard-only
roots; 6 checks Model alone with its narrower imports. Final probes have no
warnings. No frame or shared variant is added.

## H3 continuation: whole data admission preserves endpoints

The original consumeData now preserves the full optional endpoint map and
every remote destination on normal return, from arbitrary initial state.
Actual lookup and key acquisition derive the references needed by cleanup.
The no-key, dead-peer, successful enqueue, full peer queue and full device
ring arms remain, including EPIPE's real pure-callback publication. Endpoint
presence is retained as well as its full value. Missing owners, NULL words,
overflow, malformed queues and hidden-input failures keep their actual Stops.

This is before decryption and NAPI; it does not establish queued packet
authentication provenance or frame arbitrary later callbacks. Two named
local frame variants match C1 WGMore.enqueuePerDeviceAndPeerRx_spec and
enqueuePerPeerRx_pure_spec. Their SkbM reasoning follows the component
writeback locally. A private pure peer-map fact completes Frames; Source
proves the whole original operation; Claims and Statements use the campaign
projection. Six theorems in three modules bring H3 to 196 theorems and
19 headlines, without new definitions or changed old claims.

Independent review finds no issue and confirms reference effects are derived,
including actual owner-word dereference during EPIPE publication. Probe 1
fails seven record/witness/component-type errors; 2 fails five projection/
metavariable errors and two unused-simp warnings; 3 passes both queue frames;
4 fails one local-predicate unfolding; 5 passes the whole contract; 6 passes
the exact split and all six standard-only roots without warnings.

The broader architectures remain distinct: completing authenticated setter
receipts still needs substantive preservation through send/session/release
suffixes; persistent decrypt/NAPI authentication needs packet occurrence and
queue/lifetime history beyond current optional-endpoint frames. Both overlap
larger C1 layers and are not copied locally. Arbitrary initial CRYPTED packets
or arbitrary callbacks do not establish authentication.

Combined scoped build passes 433 jobs, with only inherited Env:865 String.mk.
The audit checks 1,668 logical roots in 369 modules, including 1,096 public
theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes both changed terminal roots.
Static trust/import checks, all 258 original terminal names/order and mirror/
shared boundaries pass. No proof-limit/cap change, suppression or infrastructure
rerun occurs. Totals: 2,439 theorems in 835 owned modules and 344 headlines.
All H1–H6 remain in progress; the inherited full gate remains FAILED.
Reproduce the scoped build, axiom inspection and fresh replay of
Leanux.Proofs.WG.Index.Statements and Leanux.Proofs.WG.Roaming.Statements
under capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H6 report audit correction

Independent audit found stale base-report prose that promised total success
for four supplied-record contracts now expressed as Product agreement:
retransmit-hook, initiation-send, named send-worker and absent-zero-key
give-up. Those paragraphs now retain the actual clock/wheel/release/section
refusals. The worker paragraph also now derives pending from residual queue
membership rather than claiming every dequeue clears it.

The selected retry-unit theorem remains a successful-outcome theorem under
its stated domain; its report now names that unit instead of outer fireTimer
selection, and includes wheel/pass-step effects. Pending-zero-key give-up
likewise remains total on its own stated domain. Current episode/block
coverage and the narrower meaning of the initialized give-up finding replace
stale gaps. No H6 theorem changed and no new H6 proof credit is taken.

The same audit corrects a stale backlog-table carry status and labels old
validation counts as historical. These are report repairs. Remaining H6 work
includes broader caller-local all-mode hook effects and the inventoried
cross-call lifetime/counter transport. Firing fairness and universal arbitrary
history decomposition are separate stronger questions. No new mirror request.


## H2 continuation: actual session-to-lookup handoff

The original beginSession followed, on true, by the original indexLookup now
returns the newly allocated keypair owner and its peer on every normal return.
Final table safety and hashed-owner coherence are measured after that same
lookup. False session returns skip lookup and preserve the Device exactly;
Ambient rollback is not claimed. Publication is tied to the entry's actual
handshake row.

SessionRotationFresh remains an explicit caller/lifecycle premise alongside
resident peer, table safety, owner coherence and the handshake row. The
session-alias finding proves those other local invariants cannot supply it.
No hidden-record readiness, successful intermediate execution, key-store bound
beyond table safety or reference ceiling is added; overflow and all actual
source Stops remain. This is a local handoff, not an initialized-history
freshness theorem.

SessionLookupSource contains the actual sequencing definition, published-row
lookup fact and composition. SessionLookupClaims and Statements expose the
projection. Four theorems in two modules bring H2 to 491 theorems and 91
headlines. No new frame or shared variant is needed. Independent review finds
no issue and checks every normal-none cause and the post-lookup invariant.

Probe 1 fails ten proof/reduction/field/name errors and seven warnings, including
deprecated/unused simplification; changed probe 2 checks both source facts;
probe 3 checks the exact split and all four roots with standard axioms only
and no warnings.

## H4 continuation: weighted mixed and private-key get-after-set

Both existing mixed fwmark/scalar and established private-key setters now
compose with the whole finite mixed-width getter. Every getter input is
derived from the same actual setter successor. Equal serialized device/peer
prefix sizes preserve the weighted boundaries, freshness and exact receive
count, including empty input, an empty first emitted prefix and separate DONE.
Private-key capacities use the effective installed identity, including clamping
and null-key behavior.

The mixed request retains source/cache clearing and earlier writes before a
malformed later peer returns -EINVAL. The key request retains actual expiry
time and ordered final Device effects. Both claims retain the existing setter
domains and the singleton resident/listed-node, capacity, boundary-freshness,
4096-receive and idle socket/selection getter domain. Endpoints and stored
node widths remain arbitrary; the original serializer supplies mask/JSON
behavior without asserting arbitrary widths are valid IPv6 configurations.
No callback-success or reset-record readiness premise is introduced.

WeightedPaginationCapacityFrames holds the one pure preservation fact;
MixedWeightedPaginationClaims, KeyWeightedPaginationClaims and Statements
hold projected claims. Five theorems, zero definitions and three modules bring
H4 to 717 theorems and 96 headlines. Existing IPv4 signatures are unchanged.
The first default-limit capped probe passes all five roots with standard
axioms and no warnings. Independent review finds no issue.

Combined validation: the scoped build passes 561 jobs with only inherited
Env:865 String.mk. Axiom inspection checks 2,158 logical roots in 497 modules,
including 1,485 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes both changed terminal roots. Static trust/import
checks, all 258 original terminal names/order, and mirror/shared-layer
boundaries pass. No raised limits/caps, suppression or infrastructure rerun.

This package adds nine theorems, five modules and three headlines:
2,439/835/344 before, 2,448/840/347 after. H1, H3, H5 and H6 counts are unchanged;
every result remains in progress with its remaining scope in the top table.
The inherited full gate remains FAILED and is not rerun unchanged. No new
mirror request arises. Reproduce the scoped build, axiom inspection and fresh
kernel replay of Leanux.Proofs.WG.Index.Statements and
Leanux.Proofs.WG.Config.Statements under capped/scripts/in-bundle with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H6 continuation: all-mode authenticated receive traversal

Both original handshake receiver observers now retain their authentication and
recorded-hook facts and add exact immediate persistent-keepalive effects in
either record mode. Normal hook execution derives the resident Device/peer
from its actual read. Nonzero interval, running Device and live peer select
the complete existing peerTimerArmEffect with interval times HZ; otherwise
the WG projection is unchanged. Ambient log rollback is not asserted.

Missing Device/peer and clock/wheel refusals remain actual Stops. In the
nonzero-interval arm, the original clock read precedes the running/dead guard.
The existing capture records the same hook's entry and successor and executes
the real hook once; the clock probe is inspected separately. Disabled paths
do not treat the probe as a required actual read. Existing exact full-receiver
erasures preserve every error, including later sender/session/release failures.
A successful observer receipt concerns its immediate hook boundary, not final
expiry, delivery or a receipt returned after a later Stop.

ReceiveTraversalAllModeModel contains one projected effect predicate;
ReceiveTraversalAllModeSource contains three source/capture facts;
ReceiveTraversalAllModeClaims and Statements contain two projected caller
claims and two literal headlines. Seven theorems in three modules bring H6
to 490 theorems and 61 headlines. No new observer, frame file, shared variant,
readiness premise or change to an old signature is needed. Independent review
checks actual residency, both modes, disabled guards, authentication receipts
and same-run capture, finding no issue.

Changed probe 1 fails three proof-form errors (two unreduced error branches
and a variable removed by substitution), without warnings. Probe 2 checks the
combined proof; probe 3 checks the exact split and seven standard-only roots,
without warnings. Scoped build passes 336 jobs, inherited Env:865 String.mk
only. Axiom inspection checks 1,452 roots in 294 modules, including 826 public
theorem roots, standard-only and without diagnostics. Fresh replay passes
TimerDiscipline.Statements. Static trust/import, original 258-name/order and
mirror/shared boundaries pass. No proof-limit/cap change or infrastructure rerun.

Totals move from 2,448/840/347 to 2,455 theorems/843 modules/349 headlines.
The other five counts are unchanged. Outgoing/data caller all-mode compositions,
cross-call allocation transport and session-relative counts remain open.
Reproduce the scoped build, axiom inspection and fresh kernel replay of
Leanux.Proofs.WG.TimerDiscipline.Statements under capped/scripts/in-bundle
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H2 coverage audit

Independent audit finds the core named-operation clauses checked: numeric
uniqueness is preserved by index insertion, removal, replacement and actual
handshake/session creation; lookup has exact owner/empty/error outcomes;
recorded collisions retry as the source does. The principal terminal contracts
are original_index_insert, original_index_remove, original_index_replace,
original_begin_session_indices, original_index_lookup_success,
original_index_lookup_none, original_index_insert_recorded,
original_index_insert_exhausted and original_session_lookup_handoff.

Here live means simultaneously published receiving-index owners within one
Device. Retained unhashed objects do not reserve their former number, and
peer-supplied remote indices are a separate namespace. Numeric uniqueness,
embedded-owner uniqueness, owner residency and slot/reference lifetimes are
distinct. The session-alias finding is not a duplicate-index or wrong-return
counterexample: numeric safety survives and lookup Stops. Its positive
counterpart explicitly retains SessionRotationFresh.

These local contracts do not establish equivalence to whole initialized driver
histories. The audit distinguishes that broader lifecycle/Runner closure from
the named-operation H2 claim; additional isolated owner-coherence leaves would
not by themselves establish the former. One optional
consolidation would compose existing owned contracts into a finite native
index history from an empty table. The full-driver architecture instead needs
the deferred header/CPU, outer removal, decrypt/NAPI and environment layers;
those are inventoried, not copied.

The aggregate gate is still FAILED, not a scoped pass: inherited
CounterWindow.Refinement references flattened World.steps/World.k and old
monadic runs; ReplayWindow.Counterexamples references Runner.initialKernel,
World.k and old peer-word types. The recorded 62 errors, 22 warnings and
metavariable panic occur before the axiom stage. Campaign 1 owns these repairs.
No whole-result gate completion or initialized-driver theorem is claimed.


## H6 continuation: outgoing and data traversal callers

Outgoing initiation and response, createDataDone and raw consumeDataDone now
retain their existing observations and add exact all-mode immediate traversal
effects. Existing source erasures preserve the original operation, return
values, early exits and every Stop. No new observer or readiness premise is
introduced. Initiation's hook remains conditional on message creation;
response's remains conditional on actual session success. Common received
response traversal, proved in the preceding tranche, does not require that
success.

createDataDone traverses once before its item loop, including an empty list;
the theorem does not count one traversal per packet. Raw consumeDataDone
records its real endpoint/confirmation/keep-fresh prelude, traversal, receipt
gating and original validation/routing suffix. It supplies no upstream
authentication or inner-packet acceptance proof. All effects are measured at
the same actual hook boundary; later sends, release, error or timer changes
are retained, not turned into final-expiry or delivery guarantees.

OutgoingTraversalAllModeClaims and DataTraversalAllModeClaims hold four
projected caller claims; Statements adds four literal erasure/consequence
wrappers. Eight theorems in two modules, no definitions, frames or shared
variants. Root source inspection finds five direct timersTraversal call sites:
two in Handshake and one each in Receive, Data and RxData. The common received
handshake site is exposed by two observer branches, yielding six checked
all-mode caller statements. This local coverage is not global history or
decrypt/NAPI authentication closure.

Probe 1 fails fifteen parser/cascade errors caused by a reserved local name.
Probes 2 and 3 exit zero but each emits one unused-simp warning; both are
rejected as validation. The author corrects an initially mistaken clean-output
status after inspecting the saved logs. Changed probe 4 removes the unused
argument and checks the exact split and all eight standard-only roots without
diagnostics. No warning suppression, limit/cap increase or infrastructure rerun.

The installed scoped build passes 338 jobs, inherited Env:865 String.mk only.
Axiom inspection checks 1,460 logical roots in 296 modules, including 834 public
theorem roots, standard-only and without diagnostics. Independent review finds
no issue. Fresh kernel replay passes TimerDiscipline.Statements; static trust/
import, original 258-name/order and mirror/shared boundaries pass.

H6 now has 498 theorems and 65 headlines. Totals move from 2,455/843/349 to
2,463 theorems/845 modules/353 headlines; the other five counts are unchanged.
Cross-call allocation transport, session-relative counting and broader
history/authentication composition remain open. The inherited full gate
remains FAILED, not rerun unchanged. No mirror request arises. Reproduce the
scoped build, axiom inspection and fresh replay of
Leanux.Proofs.WG.TimerDiscipline.Statements under capped/scripts/in-bundle
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## Coverage audit: H1 and H5

H1's seven whole-call tag maps and finite actual histories cover the native IK
edge clauses. Each slot's Option type gives one value per slot, not pairwise
distinct slots or a three-object store bound. Ordered rotation/clear/expiry
contracts retain aliases and the initiator-with-next arm. The remaining core
confirmation obligation is across fresh installations: consecutive-confirmation
contracts exclude intervening installation, and direct helper reinstallation
is not an initialized accepted-run witness.

The historical six-family transport inventory is no longer the minimum after
newer owned acquisition/cleanup contracts. Actual acquisition supplies a
retained reference for rejected consumption; exact peerPut decrement prevents
deletion of that held peer. The next bounded architecture composes owned
consume/create source shapes and cursor effects, then a finite native history
under an explicit initial next-ID-below-cursor premise. C1's lifetime projection
omits slots and the Device cursor; extending it and all callers is a distinct
larger architecture. This audit takes no fresh-history proof credit.

H5's outer finite recursion is separate from finite execution of its loop-backed
helpers. At this audit the modular-power bridge was checked and general exact-count
allocation remained beyond the single-site successful case; the later exact
finite allocation tranche closes that iteration gap. Total logical denotation
alone is insufficient. Record-budget adequacy is a further separate obligation.
Existing dispatch/turn/resumption contracts connect the recorded choice to the
real activation, including detached-state rerun and all failures. Fairness and
unconditional successful resumption are stronger than relative progress.

Another substantive H5 gap is initialized accepted-operation pending-unit consistency.
RunnerBoundaryClean checks only consumed records, no suspended activation and
netRxRaised=false. afterBatch's recorded guard explicitly omits pendingWork and
relies on an unproved pending-to-queue relation. Later syscall worker/timer tails
also prevent transporting an earlier drain cut directly to the final boundary.

One architecture establishes the initialized relation through queue production,
section-start clearing, physical ring transitions, NAPI, retirement, syscall
tails and Runner.executeTrace. It overlaps C1 Queues/RingGeometry, RingSteps,
RingJournal, RxScheduleHistory, RxEnvBatchHistory, JointSyscalls and JointRunner;
those layers are not copied, and their erasures alone do not supply the relation.
The alternative investigates a current initialized accepted trace with an actual
pending boundary. A rejected prefix or manufactured successor cannot settle
this. Placeholder/recordless bookkeeping must be distinguished from supplied
record execution.

The old accepted backlog is now a proved refusal on the current mirror.
QueueRefill is an initialized executable prefix rejection; arbitrary cookie
ring witnesses refute their stated local domains. None supplies a current
kernel-proved accepted pending-unit trace. Investigation remains open and may
find no witness. Independent audits found no theorem defect in the inspected
coverage. Stale terminal-lag wording in backlog, removal and timer notes is
corrected; no proof counts change and the inherited aggregate gate remains FAILED.


## H1 continuation: exact fresh-installation transport support

Original consumeInitiation and createResponse now preserve the exact pair of
optional allocation cursor and optional tracked-peer next slot on every normal
return. The nested option distinguishes an absent peer from a resident peer
with no next key. Native source transports require no initial bound. Projected
claims carry the named FreshNextBound from a captured entry; they do not derive
it from residency or assert successful creation, fresh allocation or reachability.

Actual lookup supplies the extra reference used by rejected consumption.
The existing exact retained-put contract then proves cleanup cannot delete
that held peer. Ordinary refusal, missing/NULL inputs, overflow and all original
Stops remain. Response creation uses the actual index adapter; no general
deletion-capable release layer is copied.

FreshInstallModel contains the data view and projected bound. After the later
acquisition-contract relocation, FreshInstallFrames contains two native predicates
and five preservation facts; FreshInstallSource contains the acquisition effect
and two whole-operation transports; FreshInstallClaims contains two projected
contracts. Four named variants correspond to shared modifyPeer, pubkeyLookup,
consumeInitiation and createResponse contracts. Owned lookup/retained-release,
crypto, index-adapter and observer-erasure support supplies their substantive
dependencies. Ten theorems and four definitions in four modules; no new H1
headline or fresh-history claim. Independent review finds no issue.

Probe 1 checks five frame roots; 2 fails one implicit transformer inference
without warnings; 3 checks all ten declarations; 4 checks the exact split
proof bodies/import union and ten standard-only roots; 5 checks Model alone.
The last changes before installation are docstrings only. All final checks
are warning-free at unchanged defaults. H1 now has 245 checked theorems and
33 headlines. The finite fresh-installation history remains the next step.

## H5 continuation: accepted placeholder pending identity

The [placeholder finding](2026-10-17-proof-campaign-2-placeholder-pending.md)
checks actual initialized runner acceptance with placeholders=true and no
supplied records. Its final audited boundary retains the receive-worker
pending identity while satisfying the specified queue-empty/count/NAPI tests,
with no suspension or raised NET_RX. The theorem extracts the same actual
audit/cut and uses its exact erasure to the original runner.

This is a mode-specific bookkeeping finding, not evidence of an unexecuted
unit, general physical-ring coherence or supplied-record progress failure.
The actual hidden-input implementation clears pending identities on section
start only in its supplied-record branch; the placeholder branch returns first.
The constructed supplied-record completion control runtime-accepts with no
pending identity. No kernel acceptance theorem is claimed for that control.

PlaceholderBoundaryModel has the two concrete traces and Boolean audit predicate;
Source kernel-checks the predicate; Claims and Statements extract the actual
acceptance and cut. Three theorems, three definitions and three modules add one
headline. H5 now has 329 checked theorems and 50 headlines. Independent review
confirms the mode, same-run extraction and exact test scope.

Seven compiler invocations: 1 fails an invalid diagnostic field; 2 executes a
rejected candidate with an eight-byte UDP steer; 3 runtime-accepts the corrected
four-byte placeholder trace; 4 runtime-accepts the supplied-record control;
5 kernel-checks the Boolean; 6 fails a wrapper matcher rewrite (recovery axioms
rejected); 7 closes all three roots but emits an unused-simp warning, so is not
accepted as clean validation. Removing that argument is checked by the root
installed build. Three distinct trace inputs are tested; no infrastructure
rerun or changed proof limit/cap occurs.

The first combined installed build closes all support but fails the new literal
headline on an unqualified Runner.executeTrace, with two diagnostics. Qualifying
it fixes the packaging error. The corrected build passes 314 jobs, inherited
Env:865 String.mk only. Axiom inspection checks 1,300 roots in 250 modules,
including 779 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes both changed roots. Static trust/import,
original 258-name/order and mirror/shared boundaries pass.

Totals move from 2,463/845/353 to 2,476 theorems/852 modules/354 headlines.
Other result counts are unchanged. The inherited aggregate gate remains FAILED;
no unchanged full-gate rerun or new mirror request. Reproduce the scoped build,
axiom inspection and fresh replay of Leanux.Proofs.WG.Noise.FreshInstallClaims
and Leanux.Proofs.WG.Progress.Statements under capped/scripts/in-bundle with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: actual endpoint setter and weighted readback

The original setPeerCmd endpoint request now has exact normal-return effects
for a found, positively referenced peer on a stopped device, with the explicit
acquisition ceiling. Existing-peer UPDATE_ONLY is covered. Invalid length/family
encodings are ignored; valid IPv4/IPv6 attributes follow the actual defaults and
field conversion. Endpoint comparison omits IPv6 flowinfo, so equality retains
the stored value. A change writes the endpoint, retains the cache slot and
optionally updates its reset timestamp. Acquisition and release stores balance.
No reset-record availability or successful-return premise is supplied.

The whole wgSetDevice composition increments the generation and retains these
writes before a later malformed peer returns -EINVAL. The following actual
weighted getter runs from that same successor. Its capacities, freshness and
exact DATA/DONE bound use the effective post-set endpoint, which may change
family and serialized size. Singleton/readable-node/header-room/idle-empty-socket
premises remain explicit. Exact JSON, final socket and ordered Device effects
are proved, including arbitrary stored allowed-IP widths under the serializer's
existing semantics. This is not a general mixed-request or running-peer theorem.

EndpointSetModel contains ten pure definitions; EndpointSetSource,
EndpointAttributeSource and EndpointRequestSource connect the real operations
and their one local endpoint-attribute factor. EndpointSetEffects proves the
exact resulting fields and serialization, including preservation conjuncts;
it is a substantive effect claim rather than a standalone frame-only layer.
EndpointSetClaims and the two new Statements declarations use the campaign
projection. Existing separate readback/capacity frames are reused. Six new
modules, eleven definitions and sixteen theorems including one private proof;
no shared variants or shared-layer duplication. Independent review finds no issue.

Development uses eleven changed-source probes. Probes 1–10 fail with respectively
2/0, 10/3, 30/2, 6/5, 2/0, 2/0, 7/1, 7/1, 7/0 and 7/1 errors/warnings.
These cover comparison/StateT normalization, attribute/acquisition lookup,
UPDATE_ONLY and device binds, and finally getter field/capacity transport.
The initial ten-probe tranche ends with source contracts closed and getter
composition unresolved; a separate narrowly bounded getter tranche repairs
that proof without changing its premises. Its first probe (11 overall) passes
all fifteen public theorem roots with standard axioms and no diagnostics.
Recovery sorry axioms from failed probes are rejected. No infrastructure rerun,
warning suppression, proof-limit or memory-cap change occurs.

The installed scoped build passes 346 jobs; only inherited Env:865 String.mk
warns. Axiom inspection checks 1,212 roots in 282 modules, including 823 public
theorem roots, standard-only and without diagnostics. Fresh Config.Statements
kernel replay passes. Static trust/import, original 258-name/order and
mirror/shared boundaries pass.

H4 moves from 717/96 to 733 theorems/98 headlines. Campaign totals move from
2,476/852/354 to 2,492 theorems/858 modules/356 headlines; other result counts
are unchanged. Global allowed-IP ownership, initial-to-post-free replace-peers
transport, queued cleanup, general mixed requests and multi-peer pagination
remain open. The inherited full gate remains FAILED and is not rerun unchanged.
No mirror-team request arises. Reproduce the scoped build, axiom inspection
and fresh replay of Leanux.Proofs.WG.Config.Statements under
capped/scripts/in-bundle with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H1 continuation: distinct confirmations across actual installations

A finite language now dispatches the original consumeInitiation, createResponse,
beginSession and receivedWithKeypair calls for one tracked peer. Observations
record the actual consecutive entry/exit projections and full return values.
Unconditional erasure preserves the original computation, concrete states and
first Stop; a stopped execution does not manufacture a successful receipt list.

Under the sole initial FreshNextBound, successful confirmation numeric IDs are
pairwise distinct throughout any normally completed sequence. Actual session
success advances the allocation cursor and sets next to the old cursor or none;
confirmation clears next; the setup calls preserve the cursor/next view.
The induction records prior successful IDs below the cursor and absent from next.
No readiness, reference ceiling, successful-prefix, owner coherence or distinct
slot premise is added. Arbitrary aliases and their release failures remain.

The earlier unrestricted direct-helper reinstallation counterexample remains
valid. This positive theorem excludes that helper, peer recreation and device
reset; it does not claim initialized-driver closure, full handshake-call coverage,
key residency or allocation-lifetime identity beyond this numeric-ID language.
The initial bound is explicit rather than inferred from a reachable-state claim.

FreshHistoryModel holds the operation/receipt data and pure predicates.
FreshHistoryEffects holds five substantive transition/invariant facts;
FreshHistorySource holds the three original-call effect/erasure facts;
FreshHistoryClaims holds two projected contracts. Statements adds one headline.
Independent review identifies the original Frames filename as inaccurate for
changing-state effects; renaming it to Effects and updating its import resolves
that finding without changing a proposition or proof. Semantic review finds no
remaining issue. Four modules and eleven theorems, no shared variants.

Seven development probes: 1 fails four proof errors and two unused-simp warnings;
2 checks the pure support; 3 and 4 each fail two reduction/matcher errors without
warnings; 5 checks the complete candidate; 6 checks the exact split/import
closure and all eleven standard-only roots; 7 checks the narrow Model alone.
Successful probes are diagnostic-free. No limit/cap change or infrastructure rerun.

Both initial and renamed installed builds pass 175 jobs without diagnostics.
Axiom inspection checks 704 roots in 148 modules, including 421 public theorem
roots, standard-only and without diagnostics. Fresh Noise.Statements replay,
static trust/import, original 258-name/order and mirror/shared boundaries pass.
H1 moves from 245/33 to 256 theorems/34 headlines; totals move from
2,492/858/356 to 2,503 theorems/862 modules/357 headlines. Other result counts
are unchanged. The inherited aggregate gate remains FAILED, not rerun unchanged.
Reproduce with the scoped build, axiom inspection and fresh kernel replay of
Leanux.Proofs.WG.Noise.Statements under capped/scripts/in-bundle, using
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 architecture audit: pagination between peers

The existing fitting multi-peer getter and weighted singleton getter cannot
simply be composed. A cross-peer callback retains the last completed peer as its
cursor, acquires the next retained cursor before releasing the old one, and may
omit device metadata on resumed pages. Its Device changes through those reference
stores. A dead held cursor ends the original callback normally with later peers
omitted. The current singleton receive theorem fixes one Device and full metadata;
these are interface restrictions to generalize openly in the owned layer.

Canonical full pagination needs boundary-cursor freshness against earlier peer
occurrences, local allowed-IP cursor freshness, live held peers and the actual
acquisition bounds. Repeated held cursors can temporarily require two extra
references above baseline. Full list/key uniqueness must not be imposed merely
for convenience: completed peers with equal public keys remain separate in the
coalescer; the continuation identifies its own occurrence. Ordered map writes
remain explicit until structural Device equality is actually proved.

[AGENT 2026-10-17] Develop an exact fixed-peer cursor-handoff package first, then
generalize owned receive/coalescing transport. This provides actual multi-peer
pagination without simultaneously adding the nested weighted-IP planner.
The alternative nested planner needs the same cursor/ref transitions plus
lexicographic progress and split-fragment coalescing. Both architectures reuse
the existing peer-loop body and weighted scan leaves; no C1 layer is copied.
This audit adds no theorem credit or accepted-run counterexample. The genuine
remove-all/global-ownership shared dependencies remain separate.


## H6 validation follow-up: give-up execution reduction

The bounded attempt to turn the initialized give-up runtime witness into a
closed execution theorem fails after six development probes; it adds no proof
credit. Actual runtime checks remain true, but decide +kernel cannot reduce
the first wgSet call's proposition. This is neither a semantic counterexample
nor a kernel rejection. The [finding note](2026-10-17-proof-campaign-2-initialized-giveup.md#attempt-to-obtain-a-closed-execution-theorem)
records every failed probe, the rejected recovery axioms and both continuation
architectures: a proved finite-computation bridge or actual per-operation source
composition. Defaults/caps remain unchanged; no infrastructure rerun occurs.
H6 remains at 498 theorems/65 headlines and runtime-only initialized give-up
evidence. No mirror-team request follows from this reduction obstruction.


## H5 audit correction: logical totality and executable loops

Independent review finds the blanket termination justification in two earlier
coverage summaries and the register incorrect; those passages are corrected
in place. The toolchain's Init/While implementation gives repeatM a logical
denotation with a private partial implementation and an implemented_by erased
loop, and Lean.Loop.forIn delegates to it. Function totality alone therefore
does not establish a finite number of executable iterations.

Progress.PowSource supplies a checked fixed-point unfolding and finite-evaluation
bridge for the original modular-power loop. Noise.SessionReadySource supplies
the allocation-loop equation and the exact single successful kzallocKeypair
record case. It does not establish the general exact-n allocation loop over
arbitrary returns, errors and records. This is a proof-coverage/reporting
finding, not an observed nonterminating trace or mirror defect. Stock executable
overrides remain reported and are not used as proof oracles. The following
exact finite allocation tranche subsequently closes this specific iteration gap.

A minimal candidate at this audit was equality of the original allocation loop to a structurally
recursive evaluator with at most n encounters, retaining early false returns and
the first Stop. The actual encounter helpers must then be connected explicitly;
arbitrary callbacks cannot be declared terminating merely from their types.
The scope is WireGuard execution. Generic runner boundary theorems condition on
acceptance; they do not establish termination for all subsystem operations.
For example, the separate FS pipe path has its own loop-backed rounding helper.
Whole-operation fuel adequacy and initialized pending-work consistency remain
separate. No theorem count changes or full-gate rerun accompany this correction.


## H1 continuation: all named handshake lifecycle operations

The existing fresh-confirmation language now includes createInitiation,
consumeResponse, handshakeClear, expireCurrentPeerKeypairs and keypairsClear.
Together with the four previously checked operations, these cover all handshake
create/consume calls, session installation, confirmation, handshake clearing,
expiry and slot clearing for the tracked peer. The existing headline and all
eleven prior theorem signatures are unchanged; the operation/return inductives
and the history claim's coverage are extended.

The sole initial FreshNextBound still suffices. Both additional handshake calls
preserve the exact optional next/cursor view; response lookup derives its held
reference for every normal rejection cleanup. Handshake clearing and expiry
preserve next, while actual keypair clearing supplies the new clearNext effect
without rewinding allocation. Aliased releases and all original Stops remain.
No readiness, coherence, reference ceiling, static release budget or successful
prefix is introduced. This still excludes direct helper reinstallation, peer
recreation and device reset, and makes no global driver/lifetime claim.

FreshLifecycleFrames holds the owner-word/view preservation and ClearRun cursor
fact. FreshLifecycleSource holds the actual lookup acquisition and five whole-call
contracts. Three named shared-family variants correspond to index lookup,
initiation creation and response consumption; they compose existing owned source,
crypto, lookup and retained-release facts. No new shared lookup/crypto/release
layer is copied. FreshHistoryEffects owns the changing clearNext invariant case;
Model/Source/Claims retain the single existing observer/sequence architecture.

Independent review finds one placement issue: lookup derives an acquired reference,
so its mixed effect belongs in Source. The same correction is made for three
older owned acquisition contracts: the response-tag lookup moves to
ResponseTagSource, initiation-tag pubkey lookup to InitiationTagSource, and
fresh-transport pubkey lookup to FreshInstallSource. Their propositions and proof
bodies are unchanged; pure owner/view facts stay in Frames and are made public
where cross-file use requires it. This is a factoring correction, not a new
theorem or an edit to C1's shared layer. Review finds no semantic or domain issue.

Eight new support theorems in two new modules strengthen the existing headline.
Probe 1 fails one cursor definitional-equality application without warnings;
2 checks lookup plus both handshake transports; 3 checks all nine operations;
4 checks the split bodies and nineteen roots standard-only without diagnostics.
The final scratch edits are comments only. No proof-limit/cap changes or
infrastructure reruns occur.

A root packaging script copies the support files but fails while locating the
terminal comment. Incorrect unconditional shell sequencing then launches a build
before the required recovery snapshot; that process error is not treated as a
completed checkpoint. The build passes 177 jobs, but the dirty tracked/untracked
source state is subsequently preserved at recovery ref
refs/snapshots/campaign2-lifecycle-package-recovery-20261017T110512583822Z before
further edits. Corrected scripts validate all edits before writing and fail
closed before dependent commands. The literal comment is fixed and reviewed
acquisition relocations applied. The final Noise build passes 177 jobs without
diagnostics. No source is reset or discarded.

## H5 continuation: exact finite allocation loop

AllocationIterationSource identifies the original fixed-bound while loop with
a structurally recursive evaluator using at most n-k encounter invocations.
Early false returns retain the actual successor state and counter; an error
retains the exact Stop without manufacturing a successor. The generic theorem
does not infer executable termination of an arbitrary callback from its type.

AllocationProgressSource connects every actual hiddenAlloc branch to that
evaluator: exact counts including zero, lax/unrecorded success, below-cut
refusal and unarmed bypass. The record/placeholder choice is captured once at
entry as in the source. The evaluator calls the actual private native helpers;
paired source equations expose their original finite list/byte operations,
record handling and steering failures. No record shape, readiness, success
or state-preservation premise is supplied.

AllocationProgressClaims and the new literal original_allocation_finite headline
state exact projected agreement, including all errors. There are three support
modules, six theorems and three definitions; no frame file or copied C1 Allocation
layer. This closes the general exact-count allocation iteration gap identified
by the preceding audit, rather than using logical totality as a termination
argument. Scheduler fuel adequacy, initialized pending-unit consistency and
all-subsystem runner termination remain separate.

Ten changed-source probes: 1 checks the generic loop; 2 fails an unexpanded
source let; 3 fails five count-case/variable obligations; 4 fails source equality
and warns on an unused simp argument; 5–6 fail generated-matcher equality;
7 fails an alternate forIn spelling; 8 isolates the two Option continuation
matchers. The initial eight-probe tranche stops there. A narrowly bounded
matcher-correction tranche uses bind congruence and Option cases: 9 closes the
source bridge, and 10 checks the exact split package and six standard-only roots
without diagnostics. Failed recovery environments are rejected. No infrastructure
rerun, warning suppression, proof-limit or cap increase occurs. Independent
review finds no issue.

The combined Progress/standalone FreshInstallClaims build passes 318 jobs,
inherited Env:865 String.mk only. The H1/H5 axiom audit checks 1,612 logical roots
in 316 modules, including 985 public theorem roots, standard-only and without
diagnostics. All three fresh kernel replays pass (Noise.Statements,
Noise.FreshInstallClaims and Progress.Statements). Static trust/import, original
258-name/order and mirror/shared boundaries pass.

H1 moves from 256/34 to 264 theorems/34 headlines; H5 from 329/50 to 335/51.
Totals move from 2,503/862/357 to 2,517 theorems/867 modules/358 headlines.
The other results' counts are unchanged. The inherited aggregate gate remains
FAILED and is not rerun unchanged. Reproduce the builds, axiom inspection and
fresh replay of the three named roots under Leanux.Proofs.WG using
capped/scripts/in-bundle with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 attempted cursor tranche: native serializer still open

The ten-probe cursor tranche does not close its requested native milestone.
Only two pure greedy-prefix facts check: decomposition/capacity/first-refusal
and progress when the first peer fits. They are not installed or counted as
native H4 coverage. The first missing source fact is exact arbitrary-room
empty-IP serialization; callback cursor handoff and finite multi-peer transport
are not implemented.

Probe 1 fails six import/type/tactic obligations. Probes 2–3 fail respectively
four and six reduction/default-limit obligations. Probe 4 fails two obligations
around an unavailable progress tactic. Probe 5 fails three obligations beginning
with the symbolic first-put Bool.rec; 6 fails two. Probe 7's small/large helper
split fails three obligations and has two unused-simp warnings. Probe 8 fails
four default reduction obligations. Probe 9 fails an unavailable experimental
vcgen dependency and warns. Probe 10 passes only the pure model, standard-only.
All native recovery axioms and warned/failed drafts are rejected.

Direct path reduction and compositional branch contracts both reach default
simp/heartbeat limits. One separate root diagnostic changes the experimental
tactic to the earlier mvcgen spelling; it fails the same 200,000-heartbeat limit,
also reporting deprecated syntax, an unused simp argument and a downstream
unknown helper/recovery constant. That diagnostic stops after one probe.
No warning suppression, cap/limit increase, infrastructure outcome or rerun
occurs. These are proof-development failures, not semantic counterexamples or
mirror-team requests. A smaller exact source factor with one-put-at-a-time
contracts is the next architecture to assess; no stronger capacity/readiness
premise is introduced to force the original claim through.


## H4 continuation: exact fit or cancellation at arbitrary room

[AGENT 2026-10-17] Factor the fixed put chain and endpoint tail before
reasoning about capacity. Exact equality to the original getPeerDumpTailSource
holds for every context and room, including its resumed allowed-IP path and
all original errors. The proof unfolds only the local source factors and
literal lists; actual puts, branch effects and run semantics remain opaque.

The projected total getter claim assumes a resident peer, a fresh allowed-IP
cursor and an empty stored allowed-IP list. It has no capacity, liveness,
reference, endpoint-validity, record-readiness or supplied-success premise.
At exact sufficient capacity it returns the original attributes, subtracts
peerFixedSpace and resets only nextAllowedip/allowedipsSeq; otherwise it returns
the original skb/context and cancellation. Device and existing messages remain
unchanged. Fixed cost is 136 plus 20 for AF_INET or 32 for AF_INET6.
Other present endpoint families retain the mirror's original serializer and
zero endpoint-space accounting; this is not a reachable-endpoint or Linux
correspondence claim.

FactoredTailModel holds two result definitions. FactoredTailSource holds three
operational factors and their equality to the original. FactoredTailReturns
holds the put-chain induction and the endpoint/original-tail total contracts.
FactoredTailClaims holds the projected native getter claim, wrapped literally
as original_peer_dump_fixed_room in Statements. These are mixed return/effect
contracts; no preservation-only frame or shared-layer variant is added.
No cursor planner, callback reference handoff, multi-peer pagination or socket
transport is claimed by this step.

Nine changed-source probes: 1 fails the final syntax equality, fixed by
reflexivity in passing probe 2; 3 fails five endpoint witness-shape obligations
and warns once; 4 fails two unspecified witness obligations; 5 fails three
Boolean family normalizations and warns twice; 6 fails five composition/result
obligations and warns twice; 7 leaves two; 8 leaves the whole-contract
simplification mismatch. Probe 9 extracts the actual run and normalizes its
result locally, checking all five package roots standard-only without warnings.
The seven failed drafts and their recovery environments are rejected. This
successful architecture does not reclassify the earlier failed cursor or
mvcgen probes. No timeout, cap/limit increase or infrastructure rerun occurs.

The installed Config.Statements build passes 350 jobs, with only inherited
Env:865 String.mk. Axiom inspection checks 1,223 roots in 286 modules, including
829 public theorem roots, standard-only and without diagnostics. Fresh kernel
replay passes. Static token/import/root/default checks, the original 258-name
order and mirror/shared boundaries pass. The inherited aggregate gate remains
FAILED and is not rerun unchanged.

Independent source/domain review finds no issue.

Six new theorems including the headline bring H4 to 739/99 and campaign totals
to 2,523 theorems, 871 owned modules and 359 headlines. Other result counts
are unchanged. The next native obligation is ordered multi-peer cursor
handoff, including acquisition before the previous cursor reference is put;
the fit/cancel result now supplies its exact per-peer capacity behavior.

Reproduce with capped -- scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, axiom inspection of its proof closure,
and capped -- scripts/in-bundle lake env leanchecker --fresh
Leanux.Proofs.WG.Config.Statements, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. No mirror change is requested.

## H5/H6 continuation: exact finite power and curve evaluation

[AGENT 2026-10-17] Connect a successful finite square-and-multiply evaluation
to the original private modular-power loop by induction on evaluation fuel.
This improves the earlier exponent-sized adequacy bridge: a successful
256-step evaluation suffices for these concrete curve inputs without fuel
proportional to their large exponent. Exhaustion gives no conclusion and no
fallback value is used.

Progress/PowEvaluationSource holds the two exact evaluation contracts.
Progress/CurveEvaluationSource factors the original finite ladder immediately
before inversion and connects successful inversion evaluation to the original
X25519 output. The ladder equality is definitional source factoring, not a
cryptographic-specification claim. Progress/Statements adds the literal
original_pow_mod_of_evaluation headline. No frame is added.

TimerDiscipline/InitializedGiveUpCurveSource checks four original curve-output
facts for the tracked initialized give-up recipe: configured secret/basepoint,
secret/remote, ephemeral/basepoint and ephemeral/remote. The latter three
retain both raw and actual caller-clamped inputs. The recipe reuses the same
ephemeral value across initiations; different messages do not mean twenty
different curve inputs. Candidate arithmetic values were obtained at runtime,
but every installed equality is proved by kernel-checked finite evaluation.
There is no runner acceptance or timer-history theorem in this package;
the first initialized operation remains a separate open obligation.

Development: root probe 1 checks both power contracts; probe 2 fails the
ladder equality under rfl, and probe 3 fails two unavailable Id names and
its split. The continuation's probes 1--3 check the source factor, inversion
and configured output. Before probe 4, a recipe-extraction preparation
mistakenly selected a later repeated draw directive and failed before Lean;
using the actual generator's first three directives corrects it. Probe 4
checks candidate outputs. Probe 5 fails three default recursion-depth
obligations while identifying raw and clamped inputs. Probe 6 instead checks
their actual finite inversions independently; all eight support roots pass
standard-only without warnings. Failed recovery environments are rejected.
No warning suppression, limit/cap increase, timeout or infrastructure rerun
occurs.

The combined Progress.Statements/TimerDiscipline.Statements build passes
485 jobs, with only inherited Env:865 String.mk. Axiom inspection checks
2,130 roots in 421 modules, including 1,251 public theorem roots, standard-only
and without diagnostics. Both fresh kernel replays pass. Static checks,
original 258-name order and mirror/shared boundaries pass. The inherited
aggregate gate remains FAILED and is not rerun unchanged.

Independent source/domain/trust review finds no issue in the original loop,
ladder factor, finite inversion or concrete caller inputs.

Nine new theorems, including the one headline, bring H5 to 340/52 and H6
to 502/65; totals are 2,532 theorems, 874 owned modules and 360 headlines.
H1 264/34, H2 491/91, H3 196/19 and H4 739/99 are unchanged. All six
charter results remain in progress. The current summary's previous stale
358-headline count is corrected; the preceding H4 checkpoint had 359.

Reproduce with capped/scripts/in-bundle lake build on the two named
Statements roots, standard-axiom inspection of their proof closure, and
lake env leanchecker --fresh on each, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. No mirror-team request arises from this proof
reduction work.

## H6 follow-up: first initialized operation remains open

The eight-probe first-operation tranche adds no theorem. It keeps all 23
operations, all supplied record batches and future lookahead from the generated
recipe, calls actual runnerInitial with placeholders disabled, then actual
runnerOperation for its first wgSet. The checked predicate would require return
zero, consumed records, no suspended activation and no pending NET_RX; errors
map to false. No state is reconstructed from a projection.

Probes 1--2 fail respectively a request layout error plus two default recursion
limits, then two recursion limits. Probe 3 isolates the curve-rule smoke failure
at the 32-element basepoint map. Probe 4 uses a kernel-proved literal basepoint
equality: curve reduction passes, but the whole operation still hits the default
recursion limit. Probe 5 locates eager expansion of the actual 4,096-slot initial
ring. Probe 6 checks a generic exact initial-ring empty rule, keeping init opaque
to cbv; the operation instead becomes stuck at the original FIB boot insertAlias.
Probe 7 proves its no-leaf logged insertNode equality by reflexivity and passes
that point, but the whole operation again hits the default recursion limit.

Probe 8 enables diagnostic tracing and is deliberately interrupted when it
continues producing no useful diagnosis. Only its verified own Lean PID is
sent SIGTERM. Exit 143 and capped's KILLED/signal banner are a failure, never
a passing or infrastructure-rerun result. No deeper failure location is inferred
from this interrupted probe. All eight outcomes remain failed; recovery axioms
are rejected. There are no warnings, cap/limit increases or infrastructure
reruns. The separately committed curve package retains its own successful
validation and does not receive whole-operation credit.

[AGENT 2026-10-17] Stop this reduction architecture at the bounded tranche.
The next alternatives are exact composition through an independently checked
actual initialization cut, or native setter/record contracts from that state;
do not copy a FIB or shared layer, alter the recipe, or increase limits to force
reduction. The full initialized give-up execution remains runtime-only.
H1--H6 statuses and the 2,532/874/360 census are unchanged. No mirror request
is warranted by a tactic reduction failure.

## H3 continuation: native NAPI owner and first-packet authentication

[AGENT 2026-10-17] Compose the original decryptStep with Env.napiSoftirq
and Env.napiIrqExit, observing the first pre-put poll prefix on its actual
state. Exact unconditional erasure retains both softirq calls, publication,
fixture scheduling choice, all polls, section records, peer release and every
original failure. The observer neither reconstructs state from its projection
nor substitutes a successful callback.

Actual publication derives a resident scheduled owner from the index owner
word. NAPI's own multiple-peer refusal then derives its selected owner,
without an owner-equals-packet-peer assumption. The queue-read contract covers
peeked and physically malformed queues on normal returns. If the observed
first poll reaches an endpoint setter and that owner's actual queue head
at publication is the published packet, packet identity follows; the earlier
authenticated decryption then supplies the AEAD plaintext, accepted counter
and immediate source endpoint. Entry precondition is True. The owner-head
condition is explicit in the conclusion's implication, not silently assumed
for all queue histories.

This is first setter-cut provenance. It does not establish every queued
packet's authentication, later poll iterations, final endpoint preservation
or initialized reachability. Skipped polling, including recordless pre-put
polling, remains possible. No stronger H3 result is inferred.

NapiPublicationModel contains projected cut/fact definitions. Source contains
the original NAPI factors, full observer and five exact source/erasure facts.
Frames contains the one genuine composite Product-to-WG preservation fact;
the Product computation's type alone does not give it. SelectionSource holds
four queue/poll provenance contracts, including PrevQueue_peek_head moved
from the draft frame file because it is a return-value fact. OwnerSource
holds five scheduling/selection contracts. Claims holds the projected
composition; Statements adds its literal original_native_napi_publication_authentication
headline. No shared-layer variant or mirror change is added.

The first twelve-probe tranche closes eight support theorems. Failed probes
1--11 have error/warning counts respectively 3/1, 3/0, 6/3, 1/4, 1/0,
4/4, 3/0, 2/1, 4/10, 4/3 and 1/0; failures cover source/erasure
normalization, getters and queue facts, including default heartbeat failure
in probe 9. Probe 12 passes without warnings. A separately bounded
continuation adds the actual owner linkage and final claim. Probes 13--18
fail with counts 12/0, 1/0, 4/0, 1/0, 3/0 and 8/2; these include
default recursion-depth errors, dependent elimination, singleton/result
normalization and reserved identifiers. Probe 19 closes the full claim;
20 checks all seventeen roots; 21 checks the reordered split bodies.
Those three pass without warnings and with standard axioms. Every failed
recovery environment is rejected. No limit/cap increase, warning suppression
or infrastructure rerun occurs.

Installed Roaming.Statements builds in 259 jobs with only inherited
Env:865 String.mk. Axiom inspection checks 1,098 roots in 225 modules,
including 643 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes. Independent source/domain/trust review finds
no issue. Static checks, original 258-name order and mirror/shared boundaries
pass. The inherited aggregate gate remains FAILED and is not rerun unchanged.

Seventeen new theorems in six modules bring H3 to 213 theorems/20 headlines.
Campaign totals are 2,549 theorems, 880 owned modules and 361 headlines.
H1 264/34, H2 491/91, H4 739/99, H5 340/52 and H6 502/65 are unchanged;
all six charter results remain in progress. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Roaming.Statements, standard-axiom inspection of
its closure and lake env leanchecker --fresh on the same root, with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: native cursor body and ordered reference handoff

The original dump operation now factors unconditionally into its unchanged
header and an exact peer-body computation. The peer body combines the actual
empty/dead-cursor guard, ordered finite peer loop, original cancellation
branches and original cursor-reference finalizer. The body normal-return
contract gives the exact completed prefix, serialized attributes, context,
skb/messages and Device effect. Its cursor acquisition precedes the old
cursor read/release, including when both cursor IDs coincide.

Entry premises are a resident Device, resident selected suffix peers with empty
allowed-IP lists, a fresh allowed-IP cursor and a resident old cursor when
present. There is no capacity, sequence-consistency, liveness, distinct-list,
cursor-membership, reference-budget, record-readiness or execution-witness
premise. Arbitrary raw room is retained, including incomplete outputs whose
saturating ret arithmetic is zero. Successful last-reference release may
erase a peer/unhash its handshake and increment txDropped; original zero,
overflow, queued-work and timer refusals remain outside normal completion.
The body theorem is not totality or a whole-callback contract.

CursorCallbackModel contains seven pure transforms; CursorCallbackSource
contains four exact operational factors and two original equalities.
CursorLoopSource proves the native greedy loop and cursor provenance.
CursorHandoffSource proves successful release and ordered reference effects.
CursorBodySource composes the guard, loop and finalizer. These are mixed
return/effect contracts, not preservation-only frames. Statements imports
the eleven support theorems but adds no headline. Header continuation and
the projected whole callback remain open at this checkpoint.

Twelve changed-source probes: 1--2 fail with error/warning counts 4/5 and 2/2,
including default isDefEq timeout with an invalid draft definition. Probe 3
checks both source equalities but has one unused-simp warning. Probes 4--11
fail with counts 2/3, 1/0, 6/2, 9/0, 4/6, 3/0, 17/0 and 3/2.
They cover run/bind normalization, lookup witnesses, conditional syntax and
the header's default whnf limit. Dependent unknown-helper and self-axiom
recovery output is rejected, including the unaccepted header's misleading
empty-axiom print. Probe 12 checks only the eleven support roots, standard-only
without warnings. It does not reclassify the failed whole-callback draft.

Installation exposes a further module-boundary proof-form error in
CursorBodySource's selected-list join. Three scoped builds fail one error
each: the original general simp, a restricted simp, then explicit bind/list
normalization. An explicit case split on ctx.nextPeer closes it in build 4.
Only this proof changes; original statement and factors stay unchanged.
All failed outcomes remain failures. No limit/cap increase, warning suppression
or infrastructure rerun occurs.

The final Config.Statements build passes 355 jobs, with only inherited
Env:865 String.mk. Axiom inspection checks 1,245 roots in 291 modules,
including 840 public theorem roots, standard-only and without diagnostics.
Fresh replay, static checks, original 258-name order and mirror/shared
boundaries pass. Independent source/domain/trust review finds no issue.
The inherited aggregate gate remains FAILED and is not rerun unchanged.

Eleven new theorems in five modules bring H4 to 750/99; totals are 2,560
theorems, 885 owned modules and 361 headlines. Other counts and all six
in-progress statuses are unchanged. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Config.Statements, standard-axiom inspection of
its closure and lake env leanchecker --fresh on the same root, with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: whole normal callback through the actual header

[AGENT 2026-10-17] Factor the original header into AmbientM before composing
its continuation. Its type supplies unchanged WireGuard state; no extra
preservation frame is needed. A second exact factor exposes one put at a
time, so normal-return reasoning retains each original refusal without
unfolding the entire remaining continuation.

The projected wgGetDeviceDump claim now gives the complete normal callback:
actual first/resumed device attributes, consistency flags, exact successful
header room, ordered peer-prefix serialization/cancellation, prior messages,
cursor context and acquire-before-release Device effects. It retains the
body's explicit resident selected empty-IP suffix, fresh allowed-IP cursor
and resident old cursor. No capacity, live flag, distinctness, membership,
reference budget, sequence consistency, readiness or successful-execution
premise is added. Exact source equalities preserve every original failure.
This is a normal callback contract, not totality or multi-call pagination
progress; arbitrary raw room can still give zero saturating ret when unfinished.

HeaderCutModel holds the successful header skb transform. HeaderCutSource
and HeaderPutSource hold the two original Ambient factors and their exact
equalities plus one-put/branch continuation contracts. HeaderResultSource
holds native Ambient normal output; HeaderLiftSource composes its actual
lift with an arbitrary WG continuation. CursorCallbackClaims contains the
projected whole-call claim, and Statements adds the literal
original_cursor_callback_normal. No native state is reconstructed from a
projection and no shared-layer variant is added.

The bounded header worker's eight full invocations all fail, with respective
error/warning counts 1/2, 1/1, 1/1, 1/0, 3/0, 6/0, 1/0 and 1/1.
Source lift/conditional normalization fails first; direct full-prefix reasoning
then reaches the default whnf limit. Factoring puts closes normal header
output, but an unavailable tactic, bind association, type annotations and
finally the successful Except bind prevent whole-package acceptance. Five
prefix roots are individually accepted in the final failed environment;
that is not counted as a passing invocation. Recovery roots are rejected.

A separate root integration probe removes the unused simp argument and uses
an explicit reflexive Except.ok-bind equality. It closes all eight roots,
including the projected callback and literal headline, on its first run
without warnings or nonstandard axioms. Renaming the native prefix-result
file to HeaderResultSource changes only its classification/import path.
No limit/cap increase, warning suppression or infrastructure rerun occurs.
A documentation guard later expects a period where the register uses a semicolon
and aborts before writing any file. The dirty tree, including new modules, is
preserved under refs/snapshots/campaign2-header-doc-guard-20261017T115038940935Z
before correcting that assertion; branch and index remain unchanged.

Installed Config.Statements builds in 361 jobs with only inherited
Env:865 String.mk. Axiom inspection checks 1,258 roots in 297 modules,
including 848 public theorem roots, standard-only and without diagnostics.
Fresh replay, static checks, original 258-name order and mirror/shared
boundaries pass. Independent source/domain/trust review finds no issue.
The inherited aggregate gate remains FAILED and is not rerun unchanged.

Eight new theorems in six modules bring H4 to 758/100; totals are 2,568
theorems, 891 owned modules and 362 headlines. H1 264/34, H2 491/91,
H3 213/20, H5 340/52 and H6 502/65 are unchanged. All six charter results
remain in progress. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, standard-axiom inspection of its closure
and lake env leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H5/H6 scope audit and dependency-note corrections

Independent read-only audit finds no correctness defect in the inspected
current contracts. For H5, the two finite loop-helper bridges do not by
themselves compose whole-worker finite execution or adequate derived fuel.
Runner completion checks consumed records, no suspension and no raised NET_RX;
the literal queue tests and placeholder pending-marker witness establish
neither supplied-record pending-unit consistency nor its negation. Actual
dispatch/resume source correspondence still needs composition through accepted
runner histories. Fairness is stronger than the charter and is removed from
the register's remaining obligations. The new bounded activation-exit task
addresses actual loop control, not those broader gaps.

The mirror-request note now distinguishes the earlier repeatM.impl reduction
obstruction from the available finite power/curve bridge; QueueRefill's
initialized-prefix equation remains unproved. No runtime finding is promoted
to a theorem, and actual hidden/invariant Stops are not relabelled unsupported.

For H6, the shared-overlap note's eight-site list is corrected to its historical
scope: two origin variants now check locally. Source inspection of C1 at
0268b1fc finds unconditional native snapshot contracts that observe the serial,
including sendBufferToPeer_sameSnapshot. Their lifetime invariant is not a
premise. This branch still has the older shared copies; availability is the
outgoing dependency. Incoming staged/keepalive OrdinaryAction contracts permit
allocation and do not yet supply exact serial preservation. The note records
both the smaller outgoing composition after shared support arrives and the
remaining incoming strengthening. No stopped successor is invented: the
monad returns no final WG state on error. No new mirror request is made.


## H5 continuation: actual bounded activation exits

The original Activation.run now has an exact inspection receipt retaining
occupancy-read, iteration and section-stop errors in their original order.
The last attempted iteration is an actual native call at its actual state;
no snapshot reconstruction or stopped successor is used. Captured occupancy
bounds attempted iteration calls by occupancy plus one. Continuing calls
advance the activation counter; yielding appends exactly the incremented
activation; exhaustion has the original invariant Stop and makes no extra call.

ActivationExitModel contains the projected result and accounting predicate.
ActivationExitSource contains actual-state factorization, erasure and native
last-iteration/section-stop provenance. ActivationExitClaims and the literal
original_activation_exit headline state the projected contract. Its ended
and error branches carry no additional projected phase predicate: their
native provenance is separately checked by activationExitRun_source_facts.
This distinction was clarified after independent review, which found no
correctness defect. No new frame or shared variant is needed.

This is a bounded outer-control result, not callback termination, derived-fuel
adequacy, a complete iteration journal or global progress. Those charter gaps
remain. No existing statement is weakened and no new mirror request arises.

The nine bounded development invocations have outcomes FAIL, FAIL, FAIL,
FAIL, PASS, FAIL, PASS, PASS, PASS. Their failed error counts are 2, 8, 2,
2 and 2; the third invocation also has one unused-simp warning. Bind
normalization and occupancy witness rewriting caused the failures; recovery
axiom roots were rejected. The final exact split package checks all nine
theorems with standard axioms and no warnings. No limit or cap was raised,
and there was no infrastructure rerun.

Installed Progress.Statements builds in 301 jobs; rebuilding after the
documentation clarification also passes. Only inherited Env:865 String.mk
warns. Axiom inspection checks 1,248 roots in 237 modules, including 759
public theorem roots, standard-only and without diagnostics. Fresh kernel
replay, static checks, original 258-name order and mirror/shared boundaries
pass. The inherited aggregate gate remains FAILED and is not rerun unchanged.

Nine new theorems in three modules bring H5 from 340/52 to 349/53.
Campaign totals move from 2,568/891/362 to 2,577 theorems, 894 owned modules
and 363 headlines. H1 264/34, H2 491/91, H3 213/20, H4 758/100 and H6
502/65 are unchanged; all six charter results remain in progress.
Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Progress.Statements, standard-axiom inspection of its
closure and lake env leanchecker --fresh on that root, with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: exact coalescing across a complete-peer page boundary

Three support theorems now prove the actual coalescer's output for two
DATA pages of complete peer records, device fields on the first page only,
then successful DONE. Arbitrary endpoints, repeated IDs/keys and empty pages
are retained. Complete peers stay distinct occurrences; absent allowed_ips
is normalized exactly as before. This is not yet the native two-page getter:
its producer must establish the cursor, second-header shape and receive path.

TwoPageCoalesceSource contains inner-loop/source support;
TwoPageCoalesceClaims contains the exact coalescer equality. Statements
imports it without adding a headline. No frame or shared variant is added.

Nine root development invocations give FAIL, FAIL, FAIL, PASS, FAIL, FAIL,
FAIL, PASS, PASS. The failures have respectively 2, 1, 1, 1, 1 and 1 errors:
a syntax error, unresolved last-element reduction, an unavailable induction
name, and source-function congruence. Invocation six also has two unused-simp
warnings. The final narrowed-import package checks all three roots without
warnings or nonstandard axioms. The first installed build fails because the
new import was appended after the namespace end; placing it at the file start
fixes that error. No limit/cap increase or infrastructure rerun occurs.

The corrected Config.Statements build passes 363 jobs, with inherited
Env:865 String.mk only. Axiom inspection checks 1,261 roots in 299 modules,
including 851 public theorem roots, standard-only without diagnostics.
Fresh replay, static checks, original-name order and mirror/shared boundaries
pass. Independent review finds no defect and confirms the producer-header
obligation above. The inherited aggregate gate remains FAILED.

H4 moves from 758/100 to 761/100; campaign totals move from 2,577/894/363
to 2,580 theorems, 896 modules and 363 headlines. H1 264/34, H2 491/91,
H3 213/20, H5 349/53 and H6 502/65 are unchanged. All results remain in
progress; no mirror request arises. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Config.Statements, closure axiom inspection and
lake env leanchecker --fresh on that root, using 32 threads and 16 QEMU slots.


## H4 continuation: actual two-page complete-peer getter

[AGENT 2026-10-17] Track the actual held-cursor Device between callbacks.
The final Device retains its ordered acquisition/release tree writes; every
peer lookup and every non-peer field are restored separately. Raw TreeMap
representation equality is not established or needed for the readback claim.

The native callback package establishes both complete executions from data
premises: a nonempty maximal fitting front, resident peers with empty allowed-IP
lists, a positive bounded cursor reference, no earlier occurrence of the
resume cursor, a live boundary cursor and a fitting tail. Duplicate other
visits, later occurrences of the cursor and arbitrary endpoints remain.
Initial cancellation and a dead resumed cursor are outside this total domain;
prior exact source and normal-return contracts retain those branches.

TwoPageCallbackModel holds the pure prefix/cursor model; TwoPageCursorFrames
holds four substantive preservation facts; TwoPageCallbackSource derives the
two actual callbacks and their native source contracts. DeviceTransitionSource
generalizes six owned transport contracts to distinct entry/exit Devices.
TwoPageDrainSource composes the actual receives, both inline and separate DONE,
and the original one-plus-4095 receive budget. These source interfaces take
callback/receive contracts as premises; TwoPageGetterClaims now discharges
every one from the stated data conditions. The literal
original_two_page_empty_ips_getter returns exact multiPeerJson, the actual
ordered Device updates and socketReadbackFinal. The coalescer consumes the
produced pages, and the unchanged drain uses two receives with inline DONE
or three with a separate DONE. This covers exactly two complete-peer pages,
not arbitrary page counts or mixed peer/allowed-IP pagination.

The callback worker's twelve development invocations are FAIL, FAIL, FAIL,
FAIL, FAIL, PASS, FAIL, PASS, FAIL, FAIL, PASS, PASS. Failed error counts are
3, 5, 1, 2, 4, 2, 3 and 3. Invocations two through five have respectively
6, 2, 2 and 4 warnings. Failures concern a missing raw-map extensionality
route, reference/lookup reductions, an array simp loop at the default depth,
redundant proof steps, witness/lift shapes, cursor guards, an over-general
induction hypothesis and record layout. All are corrected in the accepted
17-theorem split package, with standard axioms and no diagnostics.

Root's four transport probes give PASS, FAIL, PASS, PASS. The sole failure is
one record-layout parse error. Seven drain probes give FAIL, PASS, FAIL,
FAIL, FAIL, PASS, PASS. The first has a looping-array simp warning and a
default-depth error. The next three failures are kernel-depth errors when
composing the concrete receive range; their recovery self-axiom roots are
rejected. A symbolic remaining-budget factor avoids reducing that range and
then specializes to the unchanged 4095. The final five-theorem package has
only standard axioms and no diagnostics. No proof limit/cap increase,
warning suppression or infrastructure rerun occurs.

The initial installed callback/drain support build passes 135 jobs. Independent
reviews find no correctness, source, domain or factoring issue in the seventeen
callback facts, six transport variants and five drain facts.

The H1 scope header and register also correct two stale notes: actual
nine-operation confirmation history is already checked with its initial
next/cursor bound. Broader initialized-driver/lifetime propagation remains
separate. The documentation-only Noise.Statements build passes 177 jobs.

The final getter's four development probes give FAIL, FAIL, PASS, PASS.
The first has four record-layout/congruArg recovery errors; the second has
two room/cast normalization errors and one unused simp warning. The frozen
claim and literal headline then check without warnings and with standard
axioms. Independent final review finds no mathematical or source issue;
its wording correction is applied: the getter coalesces DATA pages into JSON,
rather than returning pages. Its domain is nonempty, and all actual source
contracts are discharged without execution/readiness premises.

The installed Config.Statements build passes 369 jobs, with only inherited
Env:865 String.mk. Combined Config/Noise axiom inspection checks 1,741 roots
in 402 modules, including 1,155 public theorem roots, standard-only and
without diagnostics. Fresh replays of both terminal modules pass. Static
checks, original 258-name order and mirror/shared boundaries pass. The
inherited aggregate gate remains FAILED and is not rerun unchanged.

Thirty new theorems in six modules bring H4 from 761/100 to 791/101.
Campaign totals move from 2,580/896/363 to 2,610 theorems, 902 owned modules
and 364 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6
502/65 are unchanged; all six charter results remain in progress. Independent
scope audits confirm the currently documented H1/H2 named-operation coverage
and its explicit confirmation/publication qualifications; they do not promote
those results past the inherited failed aggregate gate. No mirror or shared
layer changes, no new mirror request, no main integration or push.
Reproduce with capped/scripts/in-bundle lake build on
Leanux.Proofs.WG.Config.Statements and Leanux.Proofs.WG.Noise.Statements,
closure axiom inspection and lake env leanchecker --fresh on each root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: finite peer-page plan and actual middle callbacks

The arbitrary-page support now checks the actual fixed-peer byte-cost plan,
its maximal fitting prefixes, progressing resumed pages, occurrence-preserving
flattening, boundary freshness and DATA-plus-DONE-spill budget. The first
nonempty peer must fit; an empty first prefix would retain a null cursor and
repeat the first callback. Only the last peer of each nonfinal page becomes
a cursor. Its freshness excludes all earlier occurrences; interior duplicates,
later cursor occurrences, duplicate public keys and endpoints remain allowed.

MiddlePageModel records the held reference over the actual accumulated
Device. MiddlePageEffects establishes acquisition and ordered handoff:
acquire the distinct new cursor before releasing the old one. All non-peer
fields and pointwise peer records return to baseline on final release.
It neither reconstructs the Device nor equates raw TreeMap representations.
MiddlePageSource derives the actual nonfinal and final resumed callbacks
from baseline residency, empty-IP lists, boundary lifetime/reference data,
freshness and actual page room. No successful execution premise is supplied.

PeerPagePlanModel/Claims hold the pure plan; PeerPageCoalesceSource/Claims
prove that arbitrary finite complete-peer pages coalesce in occurrence order.
The prefix-merge equation retains an arbitrary message tail, including its
possible errors. PageTransitionSource proves that receiving the queued page
executes the next nonfinal callback first and retains its exact Device.
These are support for the whole getter, which remains to be composed; no
new headline or arbitrary-page getter claim is added here.

Independent review found no remaining semantic issue. Its factoring finding
moved the two changed-reference invariants from Frames to Effects. A proposed
four-byte empty-nest correction was withdrawn after checking the actual
assignment order: the mirror saves nestStart after charging the nest.
A temporary pure-formula edit was reverted before acceptance. The original
formula is retained with a pointer to the existing DumpCancellation finding;
no new mirror request arises. Empty DATA has no peer nest, a distinct message
shape that the final getter composition must retain.

Development outcomes: pure plan FAIL (two proof-form errors), PASS, PASS,
PASS; middle callbacks FAIL, FAIL, PASS, FAIL, PASS, PASS. The middle failures
were optional/dependent map lookup normalization, a let alias, an unavailable
tactic and record layout; two unused-simp warnings were corrected.
Root coalescer probes FAIL, PASS, FAIL, PASS (a source-step rewrite and list
append normalization); nonfinal receive transport FAIL then PASS (record
layout). Every accepted package uses default limits, standard axioms and no
warnings. Failed recovery proofs were rejected; no cap increase, warning
suppression or infrastructure rerun occurred.

Initial support build passes 112 jobs. The complete installed build and the
two changed-tree review builds each pass 377 jobs, with only inherited
Env:865 String.mk. Final scoped axiom inspection checks 1,316 roots in 313
modules, including 896 public theorem roots, standard-only without
diagnostics. Fresh Config.Statements kernel replay passes. Static checks,
the original 258-name order, and mirror/shared boundaries pass. The full
aggregate gate remains FAILED in the inherited modules and is not rerun
unchanged.

Fifteen new theorems in eight modules bring H4 from 791/101 to 806/101.
Campaign totals move from 2,610/902/364 to 2,625 theorems, 910 modules and
364 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65
remain unchanged; all six results remain in progress. No mirror/shared edit,
main integration or push. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H4 continuation: whole finite empty-IP peer getter

The original getter now handles the complete canonical finite peer-page
sequence, including empty input, a completing first page, any number of
resumed pages and a final separate DONE when its actual room requires one.
The literal original_finite_empty_ips_getter returns multiPeerJson in original
occurrence order, the completed socket and the actual ordered Device writes.
CursorHeld at none additionally gives every baseline peer lookup and all
non-peer fields; it does not claim structural TreeMap equality.

The domain is listed resident peers with empty allowed-IP lists, a fitting
first header and first peer, all-prior freshness and live/positive/bounded
reference data only at computed nonfinal boundaries, selected Device,
idle empty socket and computed DATA-plus-DONE-spill budget at most 4096.
Interior/final duplicates, later occurrences of earlier cursors, duplicate
public keys and arbitrary endpoints remain. The exact static count supplies
a sufficient original receive budget; no instrumented minimal-call count
is claimed. No callback, receive-success or general readiness premise is
supplied. Mixed peer/allowed-IP pagination remains open.

PeerPageStartModel/Source derive actual first DATA and idle start, using exact
summed costs rather than the prior conservative whole-page bound.
PeerPageTailModel/Source induct over the actual greedy suffix, deriving
maximality, freshness, cursor lifetime, ordered handoffs and receives.
PageDrainSource composes symbolic remaining budgets and specializes to the
unchanged 4096 loop. PeerGetterModel/PeerGetterPlanClaims hold pure final
messages/Device and count/coalescer facts; PeerGetterSource derives the
native drain and PeerGetterClaims projects the whole actual getter.
Reference effects stay in the previously checked MiddlePageEffects file;
no shared-layer copy or new frame is needed.

First/start development has seven invocations: FAIL (five errors and one
unused-simp warning), FAIL (one local-alias arithmetic goal), PASS, FAIL
(two record-layout/cascade errors), PASS, PASS, PASS. The accepted split has
four standard-only theorem roots and no diagnostics.
The tail has nine invocations: PASS, FAIL, FAIL, FAIL, FAIL, FAIL, PASS,
PASS, PASS. Failed error counts are eight, three, two, seven and one;
three failed probes also have an unused-termination warning. Failures concern
count/list normalization, dependent-input termination bookkeeping and a
default-depth/default-heartbeat simplification attempt. The ensuing failed
commitConst/recovery outputs are rejected. The final exact split has two
standard-only roots and no diagnostics; no limit was raised.
Pure getter helpers have four invocations: FAIL (four type/list-normalization
errors), then three PASS, the final split/model checks without diagnostics.

Root's drain probes are FAIL, FAIL, PASS with one unused-simp warning, then
PASS without diagnostics. The first two fail with eight and three errors,
including a default-depth array simp loop and missing source names/imports.
Directional rewriting resolves the array normalization without increasing
limits. Root's final glue probes are FAIL (two over-unfolded socket goals and
two unused-simp warnings), PASS with two deprecation warnings, then PASS for
the exact source, projected claim and literal headline without diagnostics.
Every accepted root uses only the three standard axioms. No cap increase,
warning suppression or infrastructure rerun occurs.

Scoped support builds pass 109, 138 and 158 jobs. Config.Statements passes
386 jobs with only inherited Env:865 String.mk. Axiom inspection checks
1,341 roots in 322 modules, including 912 public theorem roots, standard-only
without diagnostics. Fresh Config.Statements replay passes. Independent
reviews of the source layers and final literal theorem find no remaining
issue. Static checks, the original 258-name order and mirror/shared boundaries
pass. The inherited aggregate proof gate remains FAILED and is not rerun
unchanged.

Sixteen new theorems in nine modules bring H4 from 806/101 to 822/102.
Campaign totals move from 2,625/910/364 to 2,641 theorems, 919 modules and
365 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65
are unchanged; all six charter results remain in progress. No mirror or
shared-layer edit, new mirror request, main integration or push. Reproduce
with capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: scalar and mixed setters through finite peer pages

The original selected-peer scalar setter now composes with the full finite
empty-IP peer getter. Its total projected contract retains stopped-device,
selected-key/residency and positive/bounded selected-reference premises,
including partial-error writes before a malformed second peer request.
Pagination conditions name the concrete scalar successor. Every listed
occurrence reflects its effective fields; an unlisted selected target changes
the Device alone. Exact JSON, completed socket, ordered final Device and
CursorHeld at none are returned.

The mixed fwmark/scalar composition derives its page inputs from the same
actual setter successor. Its normal-return contract preserves missing reset
record Stops and retained writes before later EINVAL; it supplies no reset
readiness or successful callback premise. The actual intermediate postSet
satisfies MultiMixedEffect. Getter cursor writes then produce the exact final
Device; the raw setter effect is not falsely transferred to that final map.
All existing duplicate, endpoint, computed-boundary lifetime/freshness and
4096-envelope qualifications remain.

PeerScalarGetterClaims and PeerMixedGetterClaims hold projected claims;
Statements appends their two literal headlines. PeerPageCapacityFrames has
three pure page/count/lifetime preservation facts. PeerMixedGetterFrames
holds the mixed setter's pure residency/reference/liveness/cost preservation.
Review classified that last file as Frames instead of the initially proposed
Effects; only its filename/import changed. No new native observer or shared
variant is introduced.

Review also identified eight older owned native contracts in frame files.
Their statements, proofs and existing options are unchanged: ReadbackFrames
retains its two data declarations, five contracts move to ReadbackSource,
and three contracts with their two data definitions move from
ScalarGetterFrames to ScalarGetterSource. Direct imports follow those source
files. This is a classification correction, not a theorem deletion or a new
state-split retyping. The obsolete scalar frame module is removed solely
because its contents moved, not because compilation failed.

Scalar development: FAIL (one binder-order proof-form error), PASS, then
PASS for the exact claim/literal package with two standard-only axiom roots
and no diagnostics. Mixed development: FAIL (two well-founded/count proof
errors and one unused-simp warning), PASS for the four support facts,
NOT ACCEPTED despite exit zero for three deprecation warnings, then PASS
for the six-fact exact package without diagnostics. All new proofs use
default limits. No cap increase, warning suppression or infrastructure retry.
Independent review finds no mathematical or domain issues. Its scalar
wording clarification and both source/frame classification findings are fixed;
the reviewer verifies the eight moved theorem tails are byte-identical.

The scalar/classification scoped build passes 388 jobs; the installed mixed
build passes 391 jobs. Both have only inherited Env:865 String.mk.
The final scoped axiom audit checks 1,349 roots in 327 modules, including
920 public theorem roots, standard-only without diagnostics. Fresh
Config.Statements kernel replay passes. Static checks, all 258 original
headline names/order and the mirror/shared boundaries pass. The inherited
aggregate gate remains FAILED and is not rerun unchanged.

Eight new theorems and two headlines bring H4 from 822/102 to 830/104.
The source split and four new claim/frame modules bring the campaign from
2,641/919/365 to 2,649 theorems, 924 modules and 367 headlines.
H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65 are unchanged;
all six charter results remain in progress. No mirror/shared edit, new
mirror-team request, main integration or push. Reproduce with
capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
