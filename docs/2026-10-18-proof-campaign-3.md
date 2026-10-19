# WireGuard proof campaign 3

## Progress

[AGENT 2026-10-18] Work begins on `proofs/campaign-3` at `783510e8`, under
the [revised charter](2026-10-18-charter-proof-campaign-3.md). The inherited
proof tree includes campaign 1's GRO carry. No mirror definition or landed
proof has been changed. The source contracts now cover staged nonce allocation, encryption receipts,
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
| T2 transmit authorization and conservation | Open. `initialized_staged_selection_origins` derives ordered, distinct routing/keepalive positions through the whole native initialized runner, including Stop. `initialized_allocated_staged_occurrences` retains the selected peer allocation, exact plaintext sequence and those prior batch positions. `initialized_encrypted_plaintext_origin` and `initialized_socket_route_key_core_and_endpoint` join that history to each actual AEAD and transport socket receipt in the same final journal, with no incoming carrier or H1 premise. Socket bytes, endpoint, packet peer and historical current-slot sending core are bound. The current tranche also derives historical key-owner equality at the actual allocation entry and joins it to the socket peer through the same AEAD material; that strengthening passes the aggregate gate and fresh replay. Native overflow/purge and creation-refusal arms expose their exact effects. Initialized TX ownership and native work service cover resident cells, scheduling, deferred calls and peer removal; destructor disposal retains its explicit idle-entry premise. `staged_available_ticket_unique` proves allocation-position injectivity under the explicitly named `Staged.Availability.BankValid` premise; the strengthened carrier has native allocation and ordered-birth transfer support. The native initialized Runner now derives the bank and cross-allocation uniqueness without an incoming invariant; scoped validation passes. Complete fixed-ticket pending/terminal conservation remains open. T3 supplies converse native emission coverage separately. Batch-local distinctness and queue aliases do not discharge those obligations. |
| T3 authenticated effects and silence | Complete and validated. `AuthenticatedEffects.initialized_silence_security_outcome` combines every native append’s own authorization, rooted timer/work effects, latest own handshake admission, authenticated replay and packet-specific GRO delivery. The cookie exception uses actual load/MAC guards: at most one source-bound 64-byte reply per invocation, strictly smaller than its initialized input, without session effects. Refused initialized consumers preserve every WG field modulo map representation; MAC refusal masks only load/cookie-secret/rate-limit bookkeeping, and decryption names the exact pre-AEAD invalidation alternative. Consumer equality is at completed native cuts, retained through later outer Stop; internally stopped effects use prefix observations. No incoming invariant, funding, coherence or H1 premise remains. No global reply-rate, CPU, timing or cryptographic-unforgeability claim is made. |
| T4 handshake replay resistance | Complete and validated. Initialized retained-peer timestamps and exchange epochs are derived. Successful sessions have one actual allocation and clear their handshake; refused sessions preserve the whole WireGuard state. Final role-slot residency now follows the actual final-journal session entry. Actual initialized stale initiation receipts are refused, restore all peer records and preserve sent data. The factored native continuation returns without a response from the exact receipt endpoint; it requires no separate ambient-history join. The final-journal exports also establish response-consumption and session-installation uniqueness by exchange epoch, and exactly one allocation from the same successful session receipt. Named C2 source assumptions stay visible. |
| T5 responder confirmation | Complete and validated. `initialized_responder_confirmation_discipline` joins promotion-label uniqueness, each confirmation's own accepted transport cause and actual responder AEAD after confirmation of the same allocation. Initialized transport covers inner promotion receipts even when the enclosing receive later stops. `PendingPromotion.H1DriverFrames` and `H1ResponderCurrentEdges` remain named local C2 operational assumptions; no incoming carrier, reachability, funding or callback premise remains. |
| T6 key retirement | Complete and validated. `reference_aware_retirement_outcome` packages unconditional native TX/RX checks, invalidation, exact age comparison, initialized R2 access and holder accounting, the session-derived zero timer, selected-arm provenance, actual dispatch and worker unpublication, retained material and final removal. Actual clock/worker runs and residual-reference conditions remain explicit. Universal native RX final release includes authenticated cleanup. No worker-latency or physical-zeroization claim is made. |

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
in separate files. The mirror and all existing campaign-1 lemmas are unchanged.

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

## Validation

Source-50 checkpoint `78cbb619` passes the 3344-job aggregate build and 1523-declaration gate across thirteen roots, with only `propext`, `Classical.choice` and `Quot.sound`. Fourteen focused source queries also use only those axioms. All twelve counterexample recipes and fresh root kernel replay pass. The default model build passes 66 jobs; the unit suite passes 131 tests (one configured-kernel skip, 22.657 seconds). All 3297 frozen proof-source hashes match; all 916 inherited proof modules, main at `783510e8` and mirror `77c9b555` are unchanged. The preceding fully validated checkpoint is `13d285cf`.

Reproduce the proof and model checks from the campaign worktree:

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle scripts/proof-counterexamples
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle lake build
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The inherited `Leanux/Env.lean:865` `String.mk` deprecation is outside this
proof lane and is neither suppressed nor changed. The gate's nested wrapper
lookup reports that `capped` is absent inside the bundle PATH; the outer
wrapper contains the gate and its children. No differential guest run is
claimed for this proof-only work.

Failed development checks remain failures. Earlier non-fresh checker runs
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
files have no warnings.

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
