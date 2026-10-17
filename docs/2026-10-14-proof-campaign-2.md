# WireGuard proof campaign 2

## Current checkpoint

**Campaign-owned state-split retrofit complete over b700659.** Main was incorporated on
the campaign branch; the mirror and existing shared layers remain unchanged.
The branch retains its proof target and gate. All six terminal closures now check; broader charter work resumes with H2.
Main's subsequent b3f56807 documentation-only review/proposal update is also
merged; the executable mirror remains byte-identical to b700659.

| Result | Headlines | Checked support | Split status |
| --- | ---: | ---: | --- |
| H1 Noise | 24 | 196 | Full terminal closure, whole-response entry edge and actual session derivation-clock receipt current; wider caller/lifetime claims open. |
| H2 Index | 78 | 428 | Full terminal closure and ingress/expiry/handshake/peer-creation owner coherence current; reachable whole-driver uniqueness/coherence open. |
| H3 Roaming | 15 | 170 | Full terminal closure and invalid-MAC1/rate-limit rejection preservation current; callback authentication provenance and broader caller coverage open. |
| H4 Configuration | 81 | 590 | Full terminal closure and ordered mixed-peer readback current; global ownership, queued cleanup and general pagination open. |
| H5 Progress | 43 | 293 | Full terminal closure, exact bounded outcomes and recorded batch completion-guard soundness current; global progress/coherent-ring adequacy open. |
| H6 Timers | 52 | 445 | Full terminal closure, first outer timer turn and intermediate retransmit receipt current; whole scheduler episodes, complete caller coverage and session-relative counts open. |

The checked surface is 2,122 theorems in all 661 campaign-owned modules.
The completed retrofit accounts for 1,983: 1,321 retyped, 244 explicitly
corrected, 239 retained and 179 added support/finding declarations. Ninety-five
subsequent H2 declarations add table preservation and local owner coherence.
Eleven H1 declarations add whole-response entry and actual derivation-clock provenance; eight H4 declarations
add mixed fwmark/scalar and ordered peer-attribute readback. Thirteen H3 declarations
add invalid-MAC1 and rate-limit rejection preservation. Five H5 declarations
establish recorded batch completion-guard soundness. Seven H6 declarations
connect the first outer timer turn and its retransmit receipt. Of the 1,831 baseline theorems, 22 frames
were deleted because types supply their facts and five false cookie supports
were separately retired with checked counterexamples. No baseline declaration
remains awaiting retrofit; all 258 original terminal names/order survive,
with two new H1 headlines, twenty-six new H2 headlines, two new H3 headlines,
two new H4 headlines, one new H5 headline and two new H6 headlines (293 total).

The [retrofit report](2026-10-16-proof-campaign-2-state-split.md) records
claim/frame files, corrections, before/after counts and validation.
Scoped builds and the complete 2,980-root standard-axiom audit pass.
All seven final fresh replays pass. The full gate **fails** in inherited
CounterWindow.Refinement and ReplayWindow.Counterexamples; their old state
shapes and failed-elaboration diagnostics remain campaign 1's responsibility.
No shared lemma or mirror implementation was edited. The campaign-owned
retrofit is not a claim that the full gate or any entire charter result passes.

None of H1–H6 is a completed charter result. The timer retry-sequence contracts
concern supplied wheel units and their actual inspection. A separate first-turn
contract now connects actual outer selection to its unchanged continuation;
the complete scheduler-to-retry sequence connection remains open. No new
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
explicit detachment premise at release. The inspected whole-removal path is
not presented here as a newly checked counterexample.

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

The selected-unit H6 sequence does not yet describe an entire runTimers call.
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
information before they can connect to the retry certificates. Neither
architecture currently establishes an entire retry episode.

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
