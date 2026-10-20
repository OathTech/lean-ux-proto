# WireGuard proof campaign 3

## Progress

Current source: source-97 `8fba7fc3` passes 4322 root build jobs and 37 public axiom queries over mirror `3f3879e0`. Source-96 `06271ec7` is the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Main `3308c49a` is merged at `ab65f1fd`; fifty inherited carry paths and 4275 frozen proof hashes match. T2 remains open; the other five outcomes retain their stated boundaries.

[AGENT 2026-10-18] Work begins on `proofs/campaign-3` at `783510e8`, under
the [revised charter](2026-10-18-charter-proof-campaign-3.md). The inherited
proof tree includes campaign 1's GRO carry. At campaign start, no mirror
definition or landed proof had been changed. The source contracts now cover staged nonce allocation, encryption receipts,
cookie egress, native handshake histories and session reference payments. T1, T3, T4, T5 and the amended T6 are complete and validated; T2 remains open.

**C3-F1 is dispositioned as a statement artefact.** The original T6 wording
excluded behavior already represented by R5's coherent initialized replays.
Both reproduce on this branch. [USER 2026-10-18] Resume with the actual TX
admission/RX decryption checks and reference-aware retirement, retaining the
counterexamples. Further wording artefacts are corrected while work continues;
only a blocker, substantive finding, completed campaign or user instruction
stops the work. The last validated checkpoint and the current integration status are recorded below.

| Outcome | Status and remaining obligation |
| --- | --- |
| T1 nonce safety | Complete and validated. `initialized_nonce_safety` joins unique native reservations, actual key-allocation/nonce pairs, bounded serialized AEAD nonces and exact packet/header encoding, including stopped prefixes. Universal native rejection contracts prove invalidation, whole-batch restoration and unchanged drop count; the native rekey contracts expose the guarded helper request. No incoming invariant or campaign-2 premise remains. |
| T2 transmit authorization and conservation | Open. Initialized socket claims bind each ciphertext to its admitted plaintext, selected peer, historical owning key and endpoint; allocation credits are unique. `CompletePrefix.Runner.reached` now derives complete accounting for every prefix of the original normal or stopped journal, including actual guarded deletion, without an incoming carrier or callback premise. `CompleteConsequences` derives the same ledger’s unique status, native ownership predicates, first-terminal evidence and exact receipt converse. Logical-prefix coverage is closed; relating every accounted snapshot to its actual initialized native cut remains open. `CompleteRunner.normal_cut` connects the initialized normal return, and `initialized_dispatch_entry_accounted` derives the actual dispatch entry from a fixed original operation prefix and syscall guards. `initialized_return_callback_accounted` also derives original callback-prefix accounts; the post-transmit crypt/send entries retain the exact initialized continuation. Initialized routed-front, post-transmit scheduler-activation and TX-worker accounts now retain their original source paths and continuations, including the pre-routed receipt interval. Selected return callbacks and post-transmit send drains now connect send-worker entries, nested scheduler activations, TX entries and direct or crypt-ahead encryption callbacks to initialization, retaining the actual selected poll item. Initialized encryption-loop/publication and overflow-prefix cuts now retain their actual source states. Fixed send-drain coverage now uses a concrete delivery source proof and the original scheduler construction; worker and deeper scheduling interiors remain explicit. Preparation, expanded staging, encryption and IPv6 receive have concrete source contracts; the initialized runner retains peer transmit and five dispatch bodies; the handshake worker has concrete source contracts; routed transmit now connects its front return, expanded staging and counted repayment; the flushed protocol sender, four lifecycle and three dump dispatch families are concrete. Timer keepalive uses the expanded staging family and its actual preparation admission. Canonical creation has same-ledger phase coverage, and receive wheel/key/endpoint helpers are concrete. Local staging, allocation, publication, send-loop, selection/dequeue, queue-install and ordered DEAD-cleanup prefixes retain their exact native cuts. Stopped crypted completion retains its matched worker prefix, ledger and cleanup debts; native DEAD erasure uses an explicit pending receipt until its fixed total emission suffix completes. Complete initialized internal-cut composition and the remaining silent intervals stay open. Original transmit refusals retain their exact per-invocation error charge; successful splice is the birth boundary. No eventual-completion claim is made. |
| T3 authenticated effects and silence | Complete and validated. `AuthenticatedEffects.initialized_silence_security_outcome` combines every native append’s own authorization, rooted timer/work effects, latest own handshake admission, authenticated replay and packet-specific GRO delivery. The cookie exception uses actual load/MAC guards: at most one source-bound 64-byte reply per invocation, strictly smaller than its initialized input, without session effects. Refused initialized consumers preserve every WG field modulo map representation; MAC refusal masks only load/cookie-secret/rate-limit bookkeeping, and decryption names the exact pre-AEAD invalidation alternative. Consumer equality is at completed native cuts, retained through later outer Stop; internally stopped effects use prefix observations. No incoming invariant, funding, coherence or H1 premise remains. No global reply-rate, CPU, timing or cryptographic-unforgeability claim is made. |
| T4 handshake replay resistance | Complete and validated. Initialized retained-peer timestamps and exchange epochs are derived. Successful sessions have one actual allocation and clear their handshake; refused sessions preserve the whole WireGuard state. Final role-slot residency now follows the actual final-journal session entry. Actual initialized stale initiation receipts are refused, restore all peer records and preserve sent data. The factored native continuation returns without a response from the exact receipt endpoint; it requires no separate ambient-history join. The final-journal exports also establish response-consumption and session-installation uniqueness by exchange epoch, and exactly one allocation from the same successful session receipt. Named C2 source assumptions stay visible. |
| T5 responder confirmation | Complete and validated. `initialized_responder_confirmation_discipline` joins promotion-label uniqueness, each confirmation's own accepted transport cause and actual responder AEAD after confirmation of the same allocation. Initialized transport covers inner promotion receipts even when the enclosing receive later stops. `PendingPromotion.H1DriverFrames` and `H1ResponderCurrentEdges` remain named local C2 operational assumptions; no incoming carrier, reachability, funding or callback premise remains. |
| T6 key retirement | Complete and validated. `reference_aware_retirement_outcome` packages unconditional native TX/RX checks, invalidation, exact age comparison, initialized R2 access and holder accounting, the session-derived zero timer, selected-arm provenance, actual dispatch and worker unpublication, retained material and final removal. Actual clock/worker runs and residual-reference conditions remain explicit. Universal native RX final release includes authenticated cleanup. No worker-latency or physical-zeroization claim is made. |

## Carry to main `3f3879e0`

The separate inherited-layer carry consists of `74b03922`, `0c8f59fb`
and `7a189c9e`, in that order. It repairs 48 landed modules and adds two
helpers. No mirror file, C3 result directory or existing theorem signature
is changed by those commits; no theorem or frame is deleted.

| Landed change | Carry |
| --- | --- |
| Occupancy plus refills | Align activation copies and exact source equations; record each saved-peer read in the lifetime refill observer. |
| Pending-work lifecycle | Retain pending empty-ring dispatch, propagate its store frames, and include pending-unit refusal in wait and operation completion copies. |
| Dump cancellation | Capture the peers-nest snapshot before reserving the header and align the dump observer and source factors. |
| Dependent proofs | Transport the new atoms through existing preservation contracts; give two expanded runner proofs local heartbeat budgets. |

The public native store/view frame delta is six additions, three repairs
and zero deletions, plus two private read-frame helpers. Source-equation and observer-preservation repairs are separate
from that count. The five scoped C1 result targets pass 970 build jobs; the
anti-replay `Bounds` follow-up passes 102 jobs. The former runner proof
budgets failed before the local increases; these were elaboration and
compilation failures, not mirror findings. The mirror's existing `String.mk`
deprecation remains outside this proof-only scope.

Validation used a detached copy of `3f3879e0` with exactly the three carry
commits, in the order above. Its final gate passes 975 build jobs and 895
terminal declarations across nine roots, with only `propext`, `Classical.choice`
and `Quot.sound`. All eight additional public-declaration axiom queries pass;
fresh root kernel replay exits zero; all twelve counterexample recipes pass,
including both retained-key witnesses. All 983 frozen Lean-source hashes match,
and the clean validation tree matches the parent series on all fifty carry
paths. The earlier two-commit gate failed solely at the old `Bounds` heartbeat
limit; `7a189c9e` repairs that failure.

Reproduction on a detached copy of main `3f3879e0` with only `74b03922`,
`0c8f59fb` and `7a189c9e` applied:

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle scripts/proof-counterexamples
```

The coordinator owns integration into main; no main update or push has been
performed. The separate C3 commit `38efba22` repairs twenty-six campaign
modules and passes the 4181-job root build. Its native source paths retain
both occupancy and refill reads, pending-device selection, section-start
pending-bit clearing and the new completion guards. No security outcome
statement changes. Combined C3 validation passes at source-79 `8d9bfbca`, including all eleven source-78 helpers and forty-seven saved handoff modules. T2's initialized native-cut obligation remains open. Preparation and its initialized worker connection are subsequently closed at source-80 `0fc64409`; the remaining caller graph is still open.

## C3-F1: invalidation and clearing do not cancel previously admitted encryption

**Claim under examination.** Charter section 4, T6, lines 395–409 at
`783510e8`, prohibits transport encryption using an invalid or expired
sending key and extends that prohibition to retained work. Its introductory
reference to use checks supports a narrower, admission-time interpretation,
but the actual-encryption and retained-work sentences are stronger.

**Mirror-first diagnosis.** The checks occur in
`Leanux/WG/Send.lean:247–261`, before `createData` submits the batch.
`Leanux/WG/Data.lean:74–103` subsequently encrypts using the stored key's
bytes and the packet's assigned nonce, without checking validity, age or
the current sending counter. `keypairsClear` drops slot references and
removes index entries; a packet-held reference can preserve the object
until the TX worker releases it (`Keypair.lean:38–49,105–116` and
`Data.lean:221–249`).

The pristine C has the same boundaries: `send.c:356–388` checks at staging;
`send.c:162–219,287–309` encrypts later; `noise.c:112–177` retains material
until the last reference. Campaign 1's
[R5 report](2026-10-13-proof-campaign.md#r5--key-lifetime-enforcement-rule-zero-findings)
and [independent review](2026-10-13-review-r5-counterexamples.md) already
identify this distinction. The review's claim that Linux cannot realize
the delayed schedule was not adopted by the campaign report: kernel
scheduling reachability remains unestablished.

**Concrete existing recipes.** Both run the original initialized runner,
check its acceptance and equality with the observer, and inspect the
intervening native states in
`Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean`. They use generated record
streams with coherent coarse clocks, jiffies and timer-arm records; they
are not Linux captures. The encrypted packet is a transport keepalive
with empty plaintext.

| Recipe | Relevant events and checked outcome |
| --- | --- |
| `r5-delayed-encryption` | Session material is derived at 132 seconds. Nonce 1 is staged at 311 seconds, before the 312-second deadline. At 322 seconds, a later staging attempt invalidates the same sending key. The earlier packet then produces its expected ciphertext before queued handshake work runs. |
| `r5-coherent-post-clear` | The later expiry check occurs at 679 seconds, after the zero timer's bucket becomes due at 678.832 seconds. The clear worker empties the slots and removes the index entry. One queued packet retains the same key allocation and then encrypts; transmission releases the packet and final key reference. |

Reproduction from the campaign worktree:

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-delayed-encryption |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-coherent-post-clear |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
```

**Classification and disposition.** This is a recurrence of an established
statement mismatch, not a newly discovered Linux security defect. It does
not establish a nonce collision, a bound violation in an encrypted nonce,
or a use after the allocation's final release. No upstream-tray entry is
warranted. This disposition does not itself establish a security outcome.

The supported contract records validity and age **at the original TX
admission**, retains that historical certificate with the queued packet,
and permits later encryption under its retained reference. RX enforces its
own checks at the decryption attempt. Retirement distinguishes stopping
new admission, unpublishing slots/index entries, and final store removal.
Those distinctions are needed even with a deterministic timer wheel.

The charter now adopts this clarification. Unpublication from slots and the
index is distinct from final removal from the store: a packet reference keeps
the object resident until release. R2's initialized access-safety theorem
supplies the released-allocation discipline; holder/credit contracts are
needed separately for ownership and reference accounting.
A worker-latency premise would restrict the
claim's domain and must be stated explicitly; it is not needed for the
historical admission contract. Adding a recheck to the mirror would alter
the C's control flow and is not an acceptable proof repair.

T1's section 4 sentence at lines 178–180 has a related source-level concern:
limit rejection blocks further admission, but does not cancel earlier
queued packets. The core nonce-safety goal does not require cancellation.
No initialized nonce-limit counterexample has been reproduced here, so this
was a wording concern, not a second established replay finding. The charter
now distinguishes the limit's admission refusal from already admitted work.

## Proof structure and boundaries

[AGENT 2026-10-19] The six outcomes use initialized claims where history or
identity matters and universal native source contracts at fixed check/release
sites. T1 and amended T6 do not require a second observer merely to restate
those universal contracts. Their operational progress clauses retain the actual
source calls and reference counts explicitly.

The shared parameterized driver follows the native actors, configuration,
lifecycle, timer wheel, deferred drains and initialized Runner. Its observers
retain internal cuts and stopped prefixes, and exact projections recover the
prior observers and original execution. Endpoint equality alone never supplies
an internal invariant. Claims use projections of WGWorld; frame proofs remain
in separate files. The mirror is unchanged. The separate C1 carry repairs
observer definitions and proof bodies while retaining existing theorem signatures.

The source structure records these choices:

- Encryption identity pairs the device epoch with a packet slot; key material
  uses the actual key allocation stamp. A single certified reservation bank
  joins assignment, material, nonce and wire encoding. Numeric slot equality
  alone does not identify an allocation.
- Timer and send-work receipts name actual arms/enqueues and their context.
  Nested lifecycle drains use the shared send callback. Timer scopes close on
  normal callback return; stopped scopes retain their actual unfinished prefix.
  Fixture causes occur only around the guarded local send operations.
- Buffered GRO input has its own candidate, accepted replay and earlier AEAD
  occurrence. The generic history interface accepts complete native-poll and
  handshake contracts so authentication is proved at their real source cuts.
- The existing packet-origin carrier now checks completion entries as well as
  AEAD receipts. Its full initialized transport is reused. A head certificate
  justifies the completion's causal ancestor; it does not substitute for each
  emitted packet's separate ciphertext certificate.
- Nullable key-owner bookkeeping is not immutable. Successful native peer
  acquisition at admission supplies a non-null owner and an exact peer credit;
  current-slot compatibility then identifies that owner with the selected peer.
  The local entry premises stay visible until their initialized join is proved.
- Queue aliases are representations of one obligation. Resident uniqueness
  alone does not prove coverage of all admitted packets. T2 still requires the
  routed/staged occurrence chain and complete pending/terminal accounting.

Campaign-1 reuse is explicit: R1 supplies replay-window facts; R2's
`LifetimeSafety.runner_initialized_access_safety` supplies allocation-lifetime
safety; holder/credit contracts separately establish reference accounting;
R3's `CryptokeyRouting.parsed_initialized_transmit_authorization` supplies
selection-time routing authorization; R5 supplies native admission/attempt
checks and the retained-work counterexamples; R6 supplies the cookie gate's
local contracts. The cookie exception is not a reply-rate bound.
T6's `Outcome.initializedCredits` is a normal-Runner-endpoint census; it does
not assert that census at arbitrary internal cuts. `selectedArm` identifies
the actual prior zero-arm occurrence, while `derivedArm` is the separate
native session-derived contract. Actual successful dispatch, worker and final
release calls and the stated residual reference conditions remain premises.
No fair-drain, no-orphan or bounded-latency result follows from this package.

Campaign 2 remains a read-only dependency. Its report was read at `ca860a24`,
with H1 initially named at `3407cbff`; operational tag/frame interfaces are
pinned at `5177bd9c`. Final claims retain named hypotheses such as
`H1ResponseEdges`, `H1SessionEffects` and `H1ResponderCurrentEdges`. The new local pending-promotion interface names
`H1PendingPromotionEdges` from read-only C2 pin `7ff94e48`; its initialized
transport now closes through the native runner, with the local facts collected
in `PendingPromotion.H1DriverFrames`. No campaign-2 fact is silently discharged and no
campaign-2 file is edited.

[AGENT 2026-10-19] Routing and keepalive births use positions in the same
final journal, packet ordinals, device epochs and peer allocation stamps.
Keepalive preparation is recorded at its actual source; T3 supplies its causal
root separately. Equal payloads do not identify occurrences. Historical key
ownership is retained at admission, since retirement may clear the later owner
word. Complete initialized transports now join staging, allocation, AEAD and
socket receipts without incoming carriers. The live birth bank also supplies
cross-allocation injectivity. These facts do not establish forward conservation.

The [staged-origin review](2026-10-19-review-campaign-3-staged-origin.md) and
[conservation review](2026-10-19-review-campaign-3-t2-completeness.md) remain the
T2 disposition record. Historical ownership is repaired. Local fixed-ticket disposal is proved. First terminal outcomes separated
from later cleanup and initialized stopped caller-local frontiers remain open. Native scheduler/deferred-call proofs supply TX service;
the destructor's disposal cut retains its explicit idle-entry premise.

[AGENT 2026-10-19] Staged disposal uses callback-parametric source cuts for purge
and peer release. Concrete native instances discharge neutrality; generic
contracts retain callback premises. Actual input, disposal and outer send-result
observations extend the final journal, so every positional invariant is paid
against the resulting history. Exact old-journal projection remains required;
token positions across different event vocabularies are not equated.

The original transmit front distinguishes completed invocation refusal from
successful splice admission. `-EPROTONOSUPPORT`, `-ENOKEY`,
`-EDESTADDRREQ` and `-ENOMEM` charge the optional device error projection
once; GSO list length does not multiply the charge. A stopped prefix is not
a completed rejection. The independent raw observer records the actual
socket append, and its exact final-journal projection maps every raw position
to its own authorization receipt, including stopped prefixes.

[AGENT 2026-10-19] Conservation uses one fixed ordered ledger of birth
tickets. A ticket has one pending location or one first terminal result;
terminal results persist through later cleanup. Admission appends only fresh
source-position/ordinal tickets. Native counted purge and final peer release
now settle the exact incoming queue tickets, preserve the ledger and all other
queues, and expose the same native counter increment. The release receipt
precedes the suffix that can stop. Exact frames quantify over missing queues,
so deletion cannot hide an obligation by falsifying a residency premise.

The local ledger and new source factors are included in the current aggregate
build. The factors expose staging take/restore, TX publication and nested
consumer/RX/dump repayments. Allocation is total from a resident device;
there is no fictitious partial-allocation event. The new cuts and their carrier adapters are integrated into the shared final
driver and pass the aggregate gate and fresh kernel replay.
T2 remains open: selected and allocated tickets need native backing, terminal
classification and stopped-frontier transport through the initialized Runner.
The algebra alone is not a conservation claim.

T3's package at `f7370e9d` closes the local per-input cookie cardinality and
complementary refusal-state proof gaps. `RefusalOutside.full` retains every
WG field and complete pointwise peer/keypair records, abstracting only the
maps’ balanced-tree representation. `MacWorld.view` masks only the under-load
timestamp, cookie secret/birthdate and rate-limit tables. Endpoint and session
authorization use the actual pre-effect handshake and replay guards, separately
from the protected timer/work-event predicate. The package assumes no entry
funding, replay coherence, causal well-formedness or C2 hypothesis. The aggregate
gate and fresh kernel replay pass; T3 is complete with the stated boundaries.

The source-44 integration exposes actual staging take/restore, TX publication,
terminal disposal and nested reference release in the final Driver. Exact
native and old-journal projections preserve the completed outcomes. Local
allocation assignment joins selected tickets to the actual distinct allocator
IDs, preserves older pending cells and retains all terminal entries. Native
admission appends fresh source-position/ordinal tickets; refusal and overflow
retain their exact invocation-level counter charges.

A stopped take/borrow result retains the completed take receipt and its exact
selected tickets even when the outer selection receipt never appears. This
closes that local stopped cut. Normal restoration composition still has a
trivial error postcondition and is not a proof of general stopped-frontier
conservation. The first-terminal source facts and local allocation backing
remain conditional on explicit incoming carriers. T2 still needs their
transport through the initialized Runner and the complete fixed-ticket
pending/terminal partition.

The source-45 tranche distinguishes a pending allocated ticket from a terminal
ticket whose native cell awaits cleanup. Converse cell coverage and mixed
pending/debt uniqueness are explicit local carriers. Actual socket/refusal cuts
create the corresponding cleanup debt; ordinary source cleanup discharges it
without inventing another terminal event. Native allocation/publication and
front selection/body contracts compile under visible entry obligations. The
actual front charges one error per refused invocation, independently of segment
count. These local source facts do not establish initialized conservation.

The new core ledger uses a canonical birth list computed from the final journal,
so its domain cannot omit an admission by choosing a smaller list. Native
staging take, restoration and all three keepalive-preparation cases transport
the combined queue and physical carriers. Composition caught an incorrect draft
birth guard: preparation can return true for an already nonempty staged queue.
The corrected domain requires a true result and an empty pre-queue, matching the
native allocation arm and the existing birth relation. This was a proof-model
error, not a mirror finding. The source-45 additions pass aggregate validation below. Exact native allocation,
purge, overflow, final/nonfinal release and routed admission now transport the
combined core ledger. The whole observed front also retains canonical queue
accounting at its last completed stopped checkpoint. Whole completion batches,
stopped ownership frontiers and full initialized transport remain open.

The source-46 continuation adds a concrete selected-batch frontier at the actual
take receipt. Only nonconsuming selection/nonce events may follow while that
frontier owns the batch. Native borrow, checks, reservation and the no-key
prefix preserve it; restoration establishes its own receipt-bound Core cut.
The checked loop supplies the exact ordered plaintext/peer/key batch to its
submission callback. Native refusal disposal, queue installation and whole
completion sequencing have local source contracts with explicit stopped
ownership obligations; concrete callback discharge is continuing. The whole
transmit front now derives Core at normal return or its actual stopped
checkpoint from the incoming Core alone. These additions pass aggregate validation below.

A separate semantic gap in the proof carrier remains explicit: Core's domain,
queue and physical properties alone do not justify arbitrary terminal labels
or bind an allocated ticket to its original birth. Separate source receipt evidence and
birth-to-allocation carriers now compile, including strict birth-before-terminal
ordering and whole-front normal/stopped transport. The richer selected carrier
preserves both through checked nonce traversal, restore and native allocation;
restore/allocation clear every selected location. Initialized transport of these
carriers remains open. No initialized
T2 claim is made from Core alone; this is a proof-surface gap, not a mirror
counterexample.


The source-47 continuation joins a complete initialized entry bundle: Core,
terminal provenance, allocation lineage, empty selected locations, packet
allocation bounds and native TX ownership. Actual front, take, keepalive and
restore now transport that bundle. The selected nonce source retains allocation
preconditions through borrow and checks; actual owner acquisition and allocation
produce the full unpublished entry. The no-key path recovers full entry at its
restore cut. The whole actual staging source now composes those joins; create
and queued-initiation callbacks remain explicit pending their source discharge. Completion now has an indexed cursor sharing the
entry's exact ledger and cleanup debts; its send/free/timer joins remain open.
These local results pass the aggregate checks below; initialized T2 conservation remains open.

Source-48 local joins retain full Entry through native queue admission, both peer-release observers, queued initiation and refusal frees. The actual transmit/keepalive composition now leaves only its creation callback open; completion uses indexed settlement and cleanup. Exact normal refusal-debt restoration, enclosing source transport and historical terminal completeness remain open. These local joins pass the source-48 aggregate checks below; they do not establish initialized conservation.

Source-49 local joins derive pending-ticket evidence at the actual allocator and discharge the real creation callback, including exact original-debt restoration after refusal. Full transmit and keepalive now compose without an assumed creation or queued-initiation callback. Counted purge, encryption, receive maintenance and the family-selected completion send retain the full Entry bundle. Stop certificates remain local source frontiers; initialized transport and the converse historical terminal relation are still open. The 3321-job combined root build and eleven focused standard-axiom queries pass. Source-49 has not yet repeated the aggregate gate or fresh root replay; the last fully validated checkpoint is `13d285cf`.

Source-50 local joins cover actual TX selection and DEAD repayment, all send-result arms and nested completion release, receive finishing and timer callbacks, and native key creation, confirmation and clearing. Idle selection derives its pending batch from empty cleanup debts. Retirement algebra proves that empty native staged/TX ownership leaves no pending ticket; the lifecycle caller must still establish that quiescence before reset. The combined root build passes 3344 jobs and fourteen focused queries use only standard axioms. Whole initialized conservation and the converse historical terminal relation remain open. These local joins pass the source-50 aggregate checks below; they do not close initialized T2 conservation.

Source-51 joins the complete native TX worker up to its explicit crypted-completion contract. Indexed send/free loops retain each settlement and restore empty cleanup debt; disposal retains the actual peer-release successor. All five timer callbacks, native handshake checking paths, configuration metadata and routing edits now have full-entry contracts. Peer creation preserves the exact old staged queues under the visible native peer-slot bound. The combined root passes 3367 jobs and fifteen focused standard-axiom queries. Whole initialized transport and historical terminal completeness remain open; source-50 `78cbb619` remains the last aggregate gate/replay checkpoint.

Source-52 defines receipt-to-terminal completeness on the same ledger, proves exact fresh-position settlement and old-receipt preservation, and pairs it with full Entry in `CompleteCarrier`. Passive reuse requires terminal-quiet history explicitly. Native removal and down now compose counted disposal with the still-explicit handshake-work drain. The combined root passes 3375 jobs and nine focused standard-axiom queries. These are local source and algebra joins; initialized conservation and converse transport remain open. The last aggregate gate/replay checkpoint is source-50 `78cbb619`.

Source-53 composes full Entry through native handshake checking and the complete handshake worker, flushed send/clear workers, saved configuration metadata writes, configuration tail and interface opening. Fresh completion rekeying derives its own borrow and exact nonfinal repayment. Purge and both peer-release observers now retain Entry and terminal completeness on the identical successor ledger, including actual stopped cuts. The combined root passes 3396 jobs and fourteen focused standard-axiom queries. Whole initialized conservation and converse transport remain open. This checkpoint, `51c7344a`, also passes the aggregate gate, fresh root replay, all twelve counterexample recipes, default model build and unit suite.

Source-54 closes the Entry-only crypted completion callback and composes actual peer/device configuration, opening and removal. Native allocation freshness is transported on the same observed run. Admission and creation retain terminal completeness on the same ledger, including refusal and stopped cuts; the release evidence is derived from actual reference funding. The combined root passes 3424 jobs and seventeen focused standard-axiom queries. Initialized conservation and whole-history terminal completeness remain open. The last aggregate gate and fresh replay checkpoint remains source-53 `51c7344a`.

Source-55 pairs terminal completeness with forward accounting through actual front admissions, keepalive births, take/allocation/restore, socket results and ordinary completion cleanup. The paired handshake/send/clear workers, send drain, removal/down and peer/device configuration now compose; staging and keepalive callbacks remain explicit in configuration until their paired whole-source join. The root passes 3460 jobs and eighteen focused standard-axiom queries. Initialized conservation, the remaining completion/staging joins and reset quiescence are open. Source-53 `51c7344a` remains the last aggregate gate and fresh replay checkpoint.

Source-56 closes paired whole staging, keepalive and routed transmit, the crypted completion callback, and concrete configuration. Full receive polling, tagged GRO/stack replies, all five timers and both NAPI paths retain the identical ledger and terminal completeness. The paired product-state carrier and native scheduler composition retain explicit worker contracts; stopped prefixes preserve their actual selected or intermediate-cleanup cut. The combined root passes 3495 jobs and twenty-four focused standard-axiom queries. Initialized conservation, the remaining worker/runner joins and reference-aware reset quiescence remain open. This checkpoint, `5a802513`, also passes the aggregate gate, fresh replay and all twelve counterexample recipes.

Source-57 closes the whole paired TX worker, including DEAD disposal and the original stopped settlement chain. Concrete encryption, ring polling and decryption preparation now join native allocation safety; full NAPI, timer dispatch, deferred and traffic wrappers compose the exact callbacks. Guarded device creation retains the old ledger, and namespace cleanup is a frame. Destruction retains the same ledger after a checked quiescent cut; its reference-accounting premises remain explicit. A new upper bound shares C1's actual holders with the lower funding bound through creation, payment, detachment and receive/stack transfers. The root passes 3532 jobs and thirty focused standard-axiom queries. UDP ingress, remaining administrative/worker joins, initialized reference-account transport and final T2 conservation remain open. Source-56 `5a802513` remains the last aggregate gate and fresh replay checkpoint.

Source-58 closes actual UDP ingress, scheduled TX/send/clear workers, dump cursor callbacks and every retained administrative arm. The concrete scheduler, deferred work and traffic wrappers compose without callback premises. The exact outer syscall composition leaves only the destruction contract explicit; this is not initialized T2 conservation. Native RX acquisition/allocation/selection/payment/free and TX selection/disposal now carry both peer-reference bounds on the same holders, with temporary RX phases separated from stable queued carriers. The combined root passes 3553 jobs and thirty-three focused queries use only standard axioms. Initialized upper-account transport, reset discharge and the final T2 claim remain open. Source-58 `57598814` passes the aggregate gate, fresh root replay and all twelve counterexample recipes.

Source-59 extends the exact peer-reference account through native dump cursors, send/clear drains, single and bulk removal, full handshake workers, TX completion, RX enqueue outcomes and all timer callbacks. Peer configuration now retains the same account through actual lookup/creation, early cleanup, routing edits and removal. The combined root passes 3593 jobs; thirty-eight focused queries use only standard axioms. Whole RX polling/admission, scheduler transport, lifecycle reset discharge and initialized T2 conservation remain open. Source-59 `782432ab` also passes the aggregate gate, fresh root replay and all twelve counterexample recipes.

Source-60 completes the exact peer account through whole RX polling, native ingress and crypt workers, scheduler/deferred composition, complete device configuration, routed transmit and lifecycle controls. Deletion exposes the same account and positive resident references at its actual prepared guard; successful native guards derive the empty RX ledger. The original runner now supports a stronger idle operation entry and a weaker syscall endpoint, using its real final guard and retaining stopped journals. The combined root passes 3633 jobs, the 1523-declaration gate and thirty-eight focused standard-axiom queries. Outer traffic/account transport, the packet-ledger reset join and initialized T2 conservation remain open. Source-60 `d672ba3e` also passes fresh root kernel replay and all twelve counterexample recipes.

Source-61 closes native outer traffic and every syscall companion, actual guarded packet deletion, and initialized accounting for the returned journal. The same-ledger consequence layer adds pending-location predicates, terminal uniqueness and exact receipt cardinalities; the selected branch now retains native ownership at its recorded take. The combined root passes 3671 jobs. The [cuts review](2026-10-19-review-campaign-3-t2-cuts.md) identifies two remaining obligations: all internal prefixes, and an actual source-cut relation for the accounted snapshot. A separate prefix foundation is integrated; neither it nor the endpoint theorem discharges those obligations. Source-61 `9d2511bb` passes the 1523-declaration gate, 243 focused standard-only axiom queries, fresh root kernel replay and all twelve counterexample recipes. All 3624 frozen proof hashes match; the 916 inherited proof modules, main and mirror are unchanged.

Source-62 adds actual normal runner endpoint correspondence, active admission/staging/disposal prefix contracts, source-matched completion projections and concrete snapshot anchors. Product and passive composition retain all earlier logical prefixes; scheduler composition leaves its worker contracts explicit. Native interval provenance and whole initialized prefix coverage remain open. Source-62 `e97ff936` passes the 3700-job root build, the 1523-declaration gate, 132 focused standard-only axiom queries, fresh root kernel replay and all twelve recipes. All 3653 frozen proof hashes match; the 916 inherited proof modules, main and mirror remain unchanged.

Source-63 closes initialized logical-prefix accounting: `CompletePrefix.Runner.reached` and the exported `initialized_every_journal_prefix_accounted` cover every prefix of the original journal on normal completion or Stop. Concrete TX, crypt, receive, handshake, timer, scheduler, traffic, dump, configuration and guarded deletion sources discharge every callback premise. Fixed native selection/dequeue and queue-install prefixes retain their matched same-ledger cuts; this does not yet connect every accounted snapshot to an initialized native cut or cover all silent intervals. The first cuts-review gap is closed; the second remains open, so T2 remains open. Source-63 `eb4f48cc` passes 3801 build jobs, the 1524-declaration gate, 392 focused standard-only axiom queries in 101 delta modules, fresh root replay and all twelve recipes. All 3754 frozen proof hashes match; the 916 inherited proof files, main and mirror are unchanged.


Source-64 `e5d73508` derives initialized native dispatch entry through the original numeric operation prefix and syscall guards, retaining the exact continuation. Partial native allocation retains selected-ticket aliases before its receipt; publication, send and DEAD cleanup retain fixed source intervals and matching accounts. These local cuts still require complete initialized caller composition. T2 remains open. Validation: 3825 build jobs, 1525 terminal declarations, 90 standard-only public theorem queries across 24 new modules, fresh root replay and all twelve witness recipes; all 3778 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-65 `f2a9731f` derives actual initialized return-callback accounts and post-transmit crypt/send entries, preserving their original continuations. Staging now derives take/borrow/guard outcomes and allocation preconditions from its incoming concrete account; failed send-loop prefixes and every ordered DEAD cleanup boundary retain their matched ledger and native source. The full initialized internal-cut composition remains open. Validation: 3848 build jobs, 1526 terminal declarations, 79 standard-only public theorem queries across 23 new modules, fresh root replay and twelve witness recipes; all 3801 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-66 `da445410` connects the initialized routed-send entry and first post-transmit crypt scheduler to their original continuations. Stopped crypted completion now retains a fixed worker prefix, matched ledger and cleanup debts. Native DEAD erasure carries an explicit pending receipt until its exact total emission suffix finishes on the same world; the old resident-cell account is proved inapplicable during that interval. Complete initialized internal-cut composition remains open. Validation: 3868 build jobs, 1527 terminal declarations, 65 standard-or-empty public theorem queries across 20 new modules, fresh root replay and twelve witness recipes; all 3821 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-67 `7e1ea08f` connects the original initialized routed front, its pre-receipt native world, post-transmit scheduler activation and TX-worker entry. The same paths retain fixed bounded loop prefixes, actual crypt-ahead execution, matching worker failure ledgers and original continuations. Local transmit paths also derive staging alternatives and partial-allocation intervals; other initialized caller roots and native interiors remain open. Validation: 3888 build jobs, 1530 terminal declarations, 94 standard-or-empty public theorem queries across 20 new modules, fresh root replay and twelve recipes; all 3841 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-68 `f11eadfe` connects the original selected return callback and post-transmit send drain to send-worker entries and their nested scheduler iterations. Direct encrypt activations and TX crypt-ahead retain the actual selected poll item, intervening softirq state, initialized encryption entry and original continuation; TX entries from both scheduler callers retain matched failure accounts. These are concrete entry bridges, not exhaustive native-interior coverage. Validation: 3904 build jobs, 1534 terminal declarations, 77 standard-or-empty public theorem queries across 16 new modules, fresh root replay and twelve recipes; all 3857 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-69 `2443f3be` connects the initialized routed front to its actual pre-release/trim/splice selection state. Every completed send-list prefix, including prefixes of successful calls, now retains its remaining-batch account, original completion-scope continuation and selected-worker packet capture on the same settlement chain. The combined root passes 3911 jobs and 38 focused standard-or-empty queries across seven new modules. These intermediate helpers do not close native-interior coverage. At that commit they had scoped validation only; source-70 below validates the combined delta.

Source-70 `14a5f051` connects ordered encryption packet prefixes and publication entry to initialization, retaining the original batch and enclosing callback receipt. Actual overflow prefixes retain the same ticket cohort through removal-before-charge, and the initialized overflow receipt restores the complete account before splice. The send drain now has fixed native points and exact normal/stopped execution decomposition, with initialized composition conditional on three named delivery, send-worker and scheduler source contracts. This is not T2 closure. The combined source-69/70 delta passes 3929 build jobs, 1539 terminal declarations, 161 standard-or-empty public theorem queries across 25 new modules, fresh root replay and twelve recipes; all 3882 frozen source hashes match. The 916 inherited files, main and mirror are unchanged.

Source-71 `8526e3e4` derives successful worker selection and every ordinary cleanup erase from initialization, consuming the already-recorded terminal debt at the native free. Encryption reads, byte writes and publication cuts retain the same batch and original runner continuation on normal and stopped paths. Peer release and purge retain their exact ordered cohort across native erasure and the later counted receipt; initialized publication reaches the fixed release prefixes with its original receipt origin intact. Canonical scheduler source points cover native bookkeeping and exact finite loops, conditional on the two named committed iteration and NAPI interior contracts. Other caller roots, remaining intervals and concrete child contracts remain open; this does not close T2. Validation passes 3967 build jobs, 1544 terminal declarations, 181 standard-or-empty public theorem queries across 38 new modules, fresh root replay and twelve recipes. All 3920 frozen source hashes match; the 916 inherited proof files, main and mirror are unchanged.

Source-72 `e1156284` connects initialized routed take, worker socket result and publication release-finish intervals to their original continuations. Silent queue clearing preserves the ordered ticket cohort until the actual receipt transfers it to selection; socket results retain one existing receipt and one settlement on the same ledger. Native take, restore and keepalive classifications preserve exact order, counters and birth ordinals. Peer release-finish covers the timer guard and both work-list writes, including the busy-timer stop with its existing receipt. Other caller roots, concrete child contracts and unexpanded stopped socket-front interiors remain open; this does not close T2. Validation passes 3987 build jobs, 1547 terminal declarations, 131 standard-or-empty public theorem queries across 20 new modules, fresh root replay and twelve recipes. All 3940 frozen source hashes match; the 916 inherited proof files, main and mirror are unchanged.

Source-73 `33251831` connects the initialized native dequeue setter to the original selected worker and runner. The exact cached cohort moves into the selected local on the same ledger before the existing write/removal events; those events add no terminal charge. Native peek/drop cases retain the actual first-read and queue-choice Stops. Canonical worker iteration now structurally fills the scheduler iteration contract, with all normal/Stop executions and source-built remainders; its eight deeper child contracts and external NAPI remain explicit. Other caller roots, child instances and remaining native intervals stay open. Validation passes 4003 build jobs, 1549 terminal declarations, 65 standard-or-empty public theorem queries across 16 new modules, fresh root replay and twelve recipes. All 3956 frozen hashes match; main, mirror and the 916 inherited proof files are unchanged.

Source-74 `e3028f49` connects initialized native peek, routed staging selection and runner boundaries to their original continuations. Canonical NAPI now supplies scheduler NAPI and iteration softirq/IRQ-exit contracts; staging and runner source trees retain exact normal/Stop cases and explicit deeper child obligations. The runner boundary account does not claim all native interiors. T2 and the remaining caller/interval worklist stay open. Intermediate validation passes 4037 build jobs, the 1554-declaration gate and 110 standard-or-empty public theorem queries across 34 new modules; all 3990 frozen hashes match. Main, mirror and the 916 inherited proof files are unchanged. Fresh root replay and all twelve recipes last passed at source-73 `33251831`; they were not repeated for this helper checkpoint.

Source-75 `223c63cf` closes the shared peer-release native point family: read, decrement, test, unlink, queue guard, erasure, receipt and release-finish retain their actual world and original continuation. Each cut has the same account or the exact pending receipt and successor; initialized publication and both NAPI/iteration release children use that proof. Canonical creation adds mark/install, EPIPE and refused-free joins; receive consumption and dispatch gain fixed source coverage, and dispatch composes with initialization. Universal creation/staging phase evidence, deeper native interiors and the remaining caller contracts stay open. T2 is not complete. The frozen 43-module delta passes 4080 build jobs, the 1557-declaration gate and 144 standard-or-empty public theorem queries. All 4033 frozen source hashes and 916 inherited files match; main and mirror are unchanged. Fresh aggregate kernel replay passes with retrieved exit 0, and all twelve counterexample recipes pass. This completes aggregate validation of the combined source-74/75 delta; the preceding full replay/recipes checkpoint is source-73 `33251831`.

Source-76 `62e82ce5` derives every canonical creation point from the original unpublished account and pending batch, retaining a successor of that same ledger. Receive endpoint/key/timer helpers and wheel placement now have concrete source coverage; peer release remains shared. Canonical timer services compose through dispatch and initialization. Delivery has no deeper child and its source points and original remainder are derived without callback assumptions; the send drain uses that concrete delivery contract and scheduler construction. Staging phases, lifecycle and other worker/caller interiors remain open, so T2 is not complete. The 53-module delta passes 4133 build jobs, the 1560-declaration gate and 176 standard-or-empty public theorem queries. All 4086 frozen proof hashes and 916 inherited files match; main and mirror are unchanged. Fresh aggregate kernel replay and all twelve counterexample recipes pass with retrieved exit 0. Aggregate validation completed at that checkpoint.

Source-77 `795e8829` closes every fixed encryption-ring polling point with the same ledger and original remainder. Queued initiation now joins concrete receive helpers, wheel placement and peer release; the initialized receive scheduler retains seven named deeper packet-source contracts. Core lifecycle roots derive their boundary coverage from actual entries, including the stronger retirement guard. Partial staging phases cover take, key borrow, nonce guards, restore and the original creation path; whole staging/keepalive and environment lifecycle wrappers remain open. T2 is not complete. The 46-module delta passes 4179 build jobs, the 1563-declaration gate and 157 standard-or-empty public theorem queries. Fresh aggregate kernel replay and all twelve counterexample recipes pass with retrieved exit 0. All 4132 frozen proof hashes match; main, mirror and all 916 inherited proof files are unchanged. Aggregate validation completed at that checkpoint.

[USER 2026-10-19] Carry main `3f3879e0` into the campaign branch and repair the affected proof frames; main itself and remotes remain unchanged. [AGENT 2026-10-19] Source-78 `df10ef27` preserves eleven helper modules before that carry: concrete environment lifecycle dispatch and scheduled work/service joins. Scoped builds (2836 and 3028 jobs) and all 58 public theorem axiom queries passed against the old mirror. At that intermediate point, source-77 was the last complete aggregate checkpoint and the results lagged the newly carried mirror.

The [native-cut closure review](2026-10-19-review-campaign-3-t2-native-cut-closure.md)
refines the remaining obligation into a finite mutation and caller worklist.
All four findings are accepted. Fixed source-point composition must cover
successful and stopped interiors; current initialized entry bridges and
selected failure witnesses are not that completeness theorem. The conditional
send-drain instance is proved, with its delivery, send-worker and scheduler
child contracts explicit. Their concrete instances and the other caller
families remain open. No mirror defect was identified.

## Validation

Source-80 `0fc64409` derives the complete preparation frame from the actual getters, RX residency and cached publication peer. Every fixed preparation point retains the same ledger and its original continuation, including writes before their access receipts; both outer history projections are carried into the shared hook. The initialized receive scheduler now derives its prepare contract and retains six explicit deeper families: receive staging, routed transmit, IPv6 receive, encryption, peer transmit and handshake. Finer native-atom interiors and the other caller/interval work remain open; T2 is not complete. The seven-module delta passes the 4243-job root build, the 1563-declaration gate across thirteen roots, all 43 standard-or-empty public-declaration queries, fresh aggregate kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4196 frozen proof hashes match. Main, mirror and all fifty validated inherited carry paths are unchanged. Development elaboration and history-normalization failures were repaired before these passing checks; no mirror finding arose. No differential result is added by this proof-only checkpoint. The inherited Env deprecation remains outside scope.

Reproduce the proof and model checks from the campaign worktree:

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle scripts/proof-counterexamples
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle lake build
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The inherited `Leanux/Env.lean:873` `String.mk` deprecation is outside this
proof lane and is neither suppressed nor changed. The gate's nested wrapper
lookup reports that `capped` is absent inside the bundle PATH; the outer
wrapper contains the gate and its children. No differential guest run is
claimed for this proof-only work.

Failed development checks remain failures. Source-69 repaired prefix unfolding, match normalization and an implicit ledger binder in scoped development builds. Its front-path worker also had one failed invocation caused by a missing generated query file; the regenerated focused query and fresh local replay passed before adoption. Source-61 repaired ordinary deletion-wrapper elaboration failures and two tactic timeouts by composing the explicit native prefix, callback and suffix. The final combined build and all trust checks pass. Source-60’s first aggregate gate rejected six uses of a local identifier reserved by the token scanner. Renaming that identifier repairs the failure; the unchanged gate passes. Earlier non-fresh checker runs
exceeded their caps; the fresh-root command above passes. Ordinary local
elaboration, frame and projection failures were repaired without changing the
mirror or weakening statements. In this tranche, the first gate stopped on a
nested terminal namespace; flattening the exports and resolving their names
repairs it, and the complete gate passes. Source-44 aggregate attempts also failed on downstream callback adapters,
missing imports and exhaustive event cases. Those failures were repaired before
the successful complete rebuild; scoped passes did not replace them. Source-45 first failed on two implicit
statement binders shadowed by the new canonical `births` definition; explicit
local binders repair that failure without changing either statement. Source-47
first failed when two completion modules exported the same theorem name; the
release-specific export is renamed and the combined import check passes. New source
files have no warnings. Source-57 initially failed when a new device-creation frame reused an existing campaign-3 packet-creation filename. The previous module was restored byte-for-byte, the new modules renamed, and the combined root rebuilt successfully. No inherited lemma changed.

The earlier unchecked tactic-array panic and later SIGBUS were preserved in
snapshot refs before repair. The SIGBUS followed replacement of a dependency
artifact while Lean had it mapped; all dependency synchronization now occurs
outside active builds. These were infrastructure/development failures, not
counterexamples to the security statements. Their diagnoses and validation
are retained in the branch history.

During this later source integration a worker mistakenly invoked
`lake env leanchecker --help` without `capped`. The tool treated it as work,
grew to about 81 GB and reported a `CausalStackHistory` checking problem.
The verified process was terminated (exit 143); this is a failed invocation,
not validation evidence. All twelve worktrees were audited and the six dirty
trees, including untracked files, preserved under
`refs/snapshots/c3-checker-help-interruption-20261019T100705Z/` before further
edits or builds. Branches and normal indexes were unchanged. The current source passes a coherent rebuild and the documented capped
fresh-root replay; no checker help/flag probes will be used. The dependency-output
audit also identified one child's live links to mutable parent artifacts; those
links were replaced and its dependency closure rebuilt with private output files.

The branch is preserved without merging or pushing. Completed checkpoint
history and its individual validation counts remain in the branch commits.

Source-81 `4656199a` expands the actual key/device lookup, owner dereference and index writeback source points. Reservation getter cuts retain the original captured before-state and the selected cohort on the same ledger. Queued-initiation interiors and complete initialized caller coverage remain open. The four-module delta passes the 4244-job root build, the 1563-declaration gate across thirteen roots and all 33 standard-or-empty public-declaration queries. All 4197 frozen hashes and fifty inherited carry paths match. Fresh replay and the twelve recipes last passed at source-80 `0fc64409`; they were not repeated for this intermediate checkpoint. Main and mirror are unchanged.

Source-82 `1b41a945` extends queued-initiation coverage through its native decision/install source, cached peer reads and writes, and the fixed peer-release points. The same invocation borrow proves repayment nonfinal; the original ledger is retained even before its receipt. Existing restored-staging and keepalive joins carry these expanded points and their original continuations. Universal initialized caller composition remains open. The seven-module delta passes 4247 root build jobs and all 60 standard-or-empty public-declaration queries; all 4200 frozen hashes and fifty inherited carry paths match. The aggregate gate last passed at source-81, and fresh replay plus all twelve recipes at source-80. Development elaboration failures and an unused simp argument were repaired before validation. Main and mirror are unchanged.


Source-83 `19c14c21` joins allocation intervals and canonical creation points to the original selected staging invocation, including keepalive, on the same ledger. Fixed nested key-release points preserve that ledger and the original source continuation; native erasure before its lifetime receipt is included. Nested peer release, refused cleanup interiors and complete initialized caller composition remain open. The nine new modules pass 4256 root build jobs, the 1563-declaration gate across thirteen roots, all 33 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4209 frozen hashes and fifty inherited carry paths match. Development elaboration failures (including failed declaration elaboration) and frame-proof heartbeat failures were repaired before these passing checks; no accepted holes or mirror finding remain. Main's landed carry at `3308c49a` is merged at `ab65f1fd`; it changes only the register note relative to the validated sources, and every frozen proof hash still matches. No differential result is added by this proof-only checkpoint; the inherited Env deprecation remains outside scope.


Source-84 `2621e227` derives refused-cleanup loop entries from the original admission and repayment runs; accepted creation cannot enter this loop. Ordered free cursors retain the same ledger lineage, and both post-erase intervals carry the actual pending terminal receipt. Staging and keepalive joins retain their original continuations without incoming cleanup accounts. Nested peer release and universal initialized caller composition remain open. The four-module delta passes 4260 root build jobs and all fifteen standard-or-empty public-declaration queries; all 4213 frozen sources and fifty inherited carry paths match. The aggregate gate, fresh replay and twelve recipes last passed at source-83. Development namespace, implicit-index and dependent-equality elaboration errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged.

Source-85 `36239b83` joins the five fixed nested peer-release stages, final native erasure, pending lifetime/count records and finish points to the canonical creation call and original staging or keepalive invocation. Each point retains the original ledger lineage and literal continuation; the post-erase account records the actual pending receipts. Creation mutation interiors and universal initialized caller composition remain open. The seven-module delta passes 4267 root build jobs, the 1563-declaration gate across thirteen roots, all 54 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4220 frozen proof hashes and fifty landed carry paths match. Development elaboration and focus/frame errors were repaired before validation; no accepted holes or mirror finding remain. Main and mirror are unchanged. No differential result is added; the inherited Env deprecation remains outside scope.

Source-86 `f52dbdb9` joins creation's silent packet marks and queue installation to their original source paths, deriving live phases before access and queued receipts. The combined creation family includes canonical/key-repayment points, mutation cuts, refused cleanup and nested peer release, with source-only continuations and staging/keepalive joins. Universal initialized caller composition and finer atom interiors remain open. Its five new modules pass 4272 root build jobs and all nineteen standard-or-empty public-declaration queries; all 4225 frozen proof hashes and fifty landed carry paths match. Source-85 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and implicit-index errors were repaired; no mirror finding arose. Main and mirror are unchanged.

Source-87 `650a4aff` assembles the canonical staging tree and its reservation, rejected-key repayment, queued-initiation, allocation and creation children with source-only continuations and same-ledger evidence. The initialized receive scheduler derives its staging contract, leaving five explicit deeper packet families: routed transmit, IPv6 receive, encryption, peer transmit and handshake. Expanded keepalive points preserve their actual preparation admission and supply the timer keepalive contract. Finer primitive interiors and universal initialized caller composition remain open. The seven-module delta passes 4279 root build jobs, the 1563-declaration gate across thirteen roots, all 39 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4232 frozen proof hashes and fifty landed carry paths match. Namespace and source-context elaboration failures were repaired before validation; no accepted holes or mirror finding remain. Main and mirror are unchanged; no differential result is added and the inherited Env deprecation remains outside scope.

Source-88 `08d0e804` supplies fixed encryption callback points from the actual head read, ordered packet loop and publication prefix. Same-ledger accounting includes native peer release and the return before its original receipt. The initialized receive scheduler now retains four deeper contracts: routed transmit, IPv6 receive, peer transmit and handshake. Crypto primitive interiors and universal initialized native-cut composition remain open. The five-module delta passes 4284 root build jobs and 31 standard-or-empty public-declaration queries; all 4237 frozen hashes and fifty landed carry paths match. Source-87 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and syntax errors were repaired; no mirror finding arose.

Source-89 `210bf296` derives the zero-key timer repayment from its executed borrowing prefix. Fixed raw release points preserve the same ledger and history, and that invocation cannot enter final peer erasure. Canonical timer coverage now supplies raw repayment, observed peer release and expanded keepalive children, retaining exact continuations. Initialized caller joins, finer primitive interiors and universal T2 coverage remain open. Validation passes 4289 root build jobs and nineteen standard-or-empty public-declaration queries; all 4242 frozen hashes and fifty landed carry paths match. The latest aggregate gate, fresh replay and twelve-recipe checkpoint remains source-87. Development namespace and proof elaboration errors were repaired; no mirror finding arose.

Source-90 `47030f62` connects the fixed native preparation tree and key-read/scatter prefixes to the original encryption callback and initialized scheduler. Each cut retains the same packet ledger, while resumed execution preserves the original preparation and key-read snapshots in its eventual receipt. The four deeper packet contracts, other primitive intervals and universal initialized caller composition remain open. Aggregate validation passes 4294 root build jobs, the 1563-declaration gate across thirteen roots, 56 standard-or-empty public-declaration queries, fresh root kernel replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4247 frozen proof hashes and fifty landed carry paths match. Development elaboration, namespace and normalization errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged; no differential result is added and the inherited Env deprecation remains outside scope.

Source-91 `4087b2ab` joins the expanded receive scheduler, work services, send drain and concrete timers through all seven service families and the initialized runner. The runner send and post-transmit callbacks now derive their contracts from that graph, retaining the actual mixed-work refusal and pending-work completion checks. Four packet families, the flushed protocol sender, twelve dispatch bodies and remaining primitive intervals stay open. Validation passes 4299 root build jobs and 24 standard-or-empty public-declaration queries; all 4252 frozen hashes and fifty landed carry paths match. Source-90 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source elaboration errors were repaired; no mirror finding arose.

Source-92 `f676d7a0` supplies IPv6 receive from its fixed source: predicate checks, explicit refusals, WG read and inbox write. A structural proof excludes every child callback, and its packet-account frame and original remainder replace the IPv6 premise in the initialized runner. Three packet families, the flushed protocol sender, twelve dispatch bodies and finer native intervals remain open. Validation passes 4303 root build jobs and 21 standard-or-empty public-declaration axiom queries; all 4256 frozen proof hashes and fifty landed carry paths match. Source-90 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source elaboration failures were repaired before validation; no mirror finding arose. Main and mirror are unchanged.

Source-93 `4e53d136` supplies the flushed protocol sender from its fixed original binds, creation receipt, timer helpers, socket call and counted peer repayment. The initialized runner no longer assumes a flushed-sender contract. Three packet families, twelve dispatch bodies and finer native interiors remain open; T2 is not complete. Aggregate validation passes 4307 root build jobs, the 1563-declaration gate across thirteen roots, 31 standard-or-empty public-declaration axiom queries, fresh root kernel replay (retrieved exit 0) and all twelve counterexample recipes (retrieved exit 0). All 4260 frozen proof hashes and fifty landed carry paths match. Source elaboration, layout and normalization failures were repaired before validation; no mirror finding arose. Main and mirror are unchanged; no differential result is added, and the inherited Env deprecation remains outside scope.

Source-94 `a3ba20bf` joins fixture-scoped staging and keepalive, protocol-send drains, counted purge and peer release to the existing create/delete/up/down source proofs and the initialized runner. The stronger deletion entry and native quiescence guard remain intact. Eight dispatch bodies, three packet families and finer native interiors remain open. The sender source also builds with default Lean limits after removing its file-wide increases. Validation passes 4311 root build jobs and 43 standard-or-empty public-declaration axiom queries; all 4264 frozen proof hashes and fifty landed carry paths match. Source-93 `4e53d136` remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and source-normalization errors were repaired; no mirror finding arose. Main and mirror are unchanged.

Source-95 `55c71bde` supplies the three dump dispatch contracts from fixed source witnesses, retaining counted cursor release and the landed header cancellation. Five dispatch bodies, three packet families and finer native interiors (including header/walk atoms) remain open. Validation passes 4314 root build jobs and 32 standard-or-empty public-declaration axiom queries; all 4267 frozen proof hashes and fifty carry paths match. Source-93 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. A namespace elaboration error was repaired; no mirror finding arose. Main and mirror are unchanged.

Source-96 `06271ec7` connects routed transmit from its actual front result through expanded staging and counted repayment. Two packet families and five dispatch bodies remain; the compound front and other finer native interiors are still explicit coverage obligations. Aggregate validation passes 4317 root build jobs, the 1563-declaration gate across thirteen roots, 23 standard-or-empty public-declaration axiom queries, fresh root replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4270 frozen proof hashes and fifty carry paths match. Namespace and rewrite-normalization errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged; the inherited Env deprecation remains outside scope.

Source-97 `8fba7fc3` supplies the handshake worker from its fixed branches, scopes, receipts, timer helpers, expanded keepalive and counted release. Peer transmit is the remaining packet-family premise; five dispatch bodies and finer native intervals, including compound consumers/session/socket atoms, remain open. Validation passes 4322 root build jobs and 37 standard-or-empty public axiom queries; 4275 frozen proof hashes and fifty carry paths match. Source-96 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source decomposition resolved an elaboration timeout at default limits; layout and binder errors were repaired. No mirror finding arose; main and mirror are unchanged.
