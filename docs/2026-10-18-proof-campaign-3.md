# WireGuard proof campaign 3

## Progress

Branch `proofs/campaign-3` is rebased onto `ac55c7d5`, incorporating the
namespace-pin shared carry (`a4aec70e`, registered by `7f89077d` and
`66188b74`) and the resource rule at `25c89371`. The mirror pin is `218d3ffd`.
The independent landing review (`ad268adc` on `task/review-campaign-3-landing`)
is being dispositioned below. Current validation is pending; the earlier full
pass at `7b8994b1` was over `1f766662`, not this mirror. No mirror edit, merge
to main or push is part of this repair.

The campaign does not establish all six original charter sentences without
qualification. T1/T6 have the October 18 amendment, T2 has declared cut-point
and separate binding scopes, T3 has per-call boundaries, and T4/T5 retain the
explicit undischarged source premises identified below. The Results table in
[the register](proofs.md#results) is the current claim register. Historical
tranche notes have been replaced by these per-result reports; their commits
remain in the branch history, not as current claims or reproduction recipes.

**Resource correction (B1).** The earlier campaign-wide assertion that no
resource limit was raised was false. At review head `7b8994b1`, the whole proof
tree had `maxHeartbeats` directives in **1,337 files**, of which **1,314** had
file-wide directives (1,320 such directives), and file-wide `maxRecDepth`
directives in **462 files** (467 directives). C3's four result directories
accounted for 898 heartbeat-setting files, 879 file-wide, and 428 recursion-
setting files, all file-wide. The counts distinguish files from directives and
all settings from file-wide settings. Existing raises are grandfathered by
[AGENTS.md](../AGENTS.md); every file touched by this repair scopes any retained
raises to individual declarations with reasons. No limit is increased here.

**Statement history (S5).** The October 18 amendment narrowed T1's
post-limit cancellation clause and T6's use-time validity/expiry clause to the
C's admission/decryption checks and reference-aware retirement. Both wordings
and the reason are below and in [decisions.md](decisions.md), with
[USER 2026-10-18] provenance. The fixed-width and namespace carries preserve
the proved claims; that is not a claim that the original targets were unchanged.

All results are about the single-CPU executable mirror, with primitive
cryptographic operations treated as contracts. C simulation, concurrent
interleavings, timing channels and physical key erasure are excluded. The
observer erasure theorems relate runner results/Stops; event-site completeness
for AEAD/session/timer/work journals rests on hook placement and audit. Socket
append coverage additionally has the `Emissions.Inv` theorem. No new
cryptographic or Linux-schedule claim is made.

## T1 — nonce safety

**Architecture and claim.** `TransmitSecurity.initialized_nonce_safety`
combines the initialized reservation ledger, `EncryptionMaterial` allocation
stamps and exact header/AEAD encoding over the final causal journal. Normal
and stopped prefixes have unique reservations and unique allocation/nonce and
serialized nonce pairs; each recorded AEAD nonce is below the rejection bound.
The allocation stamp is `internalId`, not a recyclable store slot. The
packet-to-reservation association is used inside the proof but is not an extra
headline conjunct. Completeness of the AEAD journal is by construction/audit.
Native rejection and guarded rekey contracts are separate function-level claims.
No H1 premise remains in this nonce theorem.

**Both wordings and finding.** Before October 18, the limit clause prohibited
later encryption under a key after its counter reached the limit. The amended
clause rejects further staging admission and restores the batch; an earlier
admission may still encrypt with its unique, below-limit nonce. This changes
the cancellation clause, not uniqueness or the bound on encrypted nonces.
No initialized T1 limit counterexample was reproduced. C3-F1 and R5 give the
related validity/expiry evidence; a counter gap is not a nonce collision.

**Effort.** Substantial shared observer/material work, smaller than T2's source
closure. It shares `TransmitSecurity`, `HandshakeSecurity` and the causal
journal with the other outcomes; file counts are not independent result costs.
Historical wall time was not measured. Landing repair trims the docstring's
unexported packet-assignment claim. Its files include grandfathered raises.

**Ranked mirror changes that would simplify the proof (none adopted).**
1. Factor the existing staging reservation loop and encryption prefix into
   named operational helpers, retaining every choice in order — altitude-
   preserving, but currently disallowed by the mirror rule.
2. Store a proof-only allocation-history certificate in each packet — not
   altitude-preserving; it introduces state the C does not carry.

## T2 — transmit authorization and conservation

**Architecture and claim.** `initialized_transmit_source_conservation` derives
`NativeAccounting.AccountOrRecords` at the tree's declared `SourcePoint` cuts.
It supplies an existential ledger at each point: every admitted ticket has one
pending or terminal status, resident cells have ownership/backing, and terminal
receipts have exact counts. A mutation interval may append only its actual
pending records on the same WG state. The type does not export persistence of
terminal status between two points. `transmit_source_children_are_closed`
proves independence from five extension parameters; it is not a coverage theorem.
The source audit in the [native-cut review](2026-10-19-review-campaign-3-t2-native-cut-closure.md)
justifies the choice of cuts; finer sibling claims remain separately stated.

Binding is also in separate pieces: `recorded_admission_destination` gives the
lookup/admission destination relation; `initialized_socket_route_key_core_and_endpoint`
gives local socket validity, actual emitted bytes and endpoint, historical
key/current-slot selection and key ownership; `initialized_socket_ciphertext_provenance`
gives the earlier AEAD receipt. `Born` gives matching earlier plaintext, not
an occurrence-identity equality tying that birth to the AEAD. `SocketReceipt.Valid`
does not join its post-peer-read world to its socket-call entry. No single
headline composes every peer/key/endpoint/packet edge. T3 supplies converse
coverage of socket appends. Early refusal is charged by the separate
`original_transmit_refusal_charged_once`, once per invocation, not per GSO item.

**Both wordings.** The charter promised one obligation at every run point for
packets admitted at `wgXmit`, and listed early `tx_errors` among their terminal
dispositions. The implemented claim starts admission at a successful staging
splice or creation of a new keepalive and quantifies over declared tree cuts;
early refused `wgXmit` invocations remain outside that ledger and have their
own named errno/one-charge contract. This admission-boundary and coverage
reshaping is recorded here and in the register. Pending work need not finish.
The original composed binding wording is represented by the separate pieces
above; the missing joins are not claimed proved.

**Findings and effort.** No new mirror defect was established. Tray 01's
uncounted disposal paths remain intentional boundaries. This was the dominant
campaign cost: source factoring, receipt intervals, native-point refinement and
review-driven closure, with most of the 3,545 pre-review C3 files shared along
that dependency graph. Historical wall time was not measured; the scale is a
maintenance cost, not evidence of stronger coverage. Its files carry raises.

**Ranked mirror changes (none adopted).**
1. Name existing queue mutation/receipt-adjacent operational phases without
   changing state or branching — altitude-preserving; would reduce copied source
   equations, but requires a separately authorized mirror factoring policy.
2. Replace physical queue aliases by one linear logical-ticket store — not
   altitude-preserving; it erases C data/control structure and makes conservation
   true by representation instead of proving it.

## T3 — authenticated effects and silence

**Architecture and claim.** `AuthenticatedEffects.initialized_silence_security_outcome`
packages occurrence-specific transmission authorization, named `Protected`
effects, timer/work causal roots, handshake admission, replay and GRO provenance.
A fixture root includes effects inside a fixture-initiated operation. It is not
an independent noninterference theorem for each injected datagram. Transport
endpoint learning is supplied by landed C2 H3's
`Roaming.original_initialized_data_consumptions_authenticated_final`; it is
not part of `Protected` or a conjunct of `SecurityOutcome`.

**Both wordings and boundaries.** The charter's global silence wording becomes
whole-run rooting for the enumerated events plus local refusal contracts.
Qualifying cookie behavior is at most one source-bound 64-byte reply per
invocation, smaller than that initialized input, not a run-wide rate bound.
Refused-consumer equality is per completed native call; MAC bookkeeping and
pre-AEAD invalidation exceptions are named. Later Stop retains receipts, while
an internally stopped call is covered only by its prefix observations. No
whole-world isolation or CPU/amplification budget across repeated invocations
is claimed. The cryptographic primitives and cookie unforgeability are excluded.

**Findings and effort.** No new mirror defect. The main work was factoring all
append sites and joining causal timer/work receipts; refusal projections needed
separate maintenance masks. Historical wall time was not measured. Landing
repair makes the per-call scope and H3 dependency explicit. Its files carry raises.

**Ranked mirror changes (none adopted).**
1. Name the existing post-authentication receive suffixes and socket append
   helpers — altitude-preserving when choices and writes stay in order.
2. Attach a proof-only authorization token to every timer and work item — not
   altitude-preserving; the C has no such runtime field.

## T4 — handshake replay resistance

**Architecture and claim.** Timestamp receipts, exchange epochs and session
allocation receipts share the initialized causal journal. The stale-initiation
claims preserve the consumed freshness state and refuse a response; the final
response/session claims distinguish exchange epochs and one installation per
exchange, including before Stop. Refused sessions preserve the WG state.

**Premises and both wordings (S1).** The charter's unconditional replay/install
wording was reported as complete while `H1DriverSourceFacts`,
`H1ConfigurationTagFrames` and `H1TrafficTagFrames` were unconstructed.
`LandedH1TagFrames` and `LandedH1Exchange` now supply direct adapters from C2 H1
on main. The direct adapter checks pass; full-tree validation is recorded below. The final role-slot/material
headline still needs `H1ResponderCurrentEdges` and `H1SessionPlacement`; this
result is conditional on those named local contracts, not complete. The latter
requires final resident material/role slots, stronger than C2's released-slot
freshness condition; the former concerns the complete sending-key core, not
only the slot/tag projections. They need additional projection proofs, not just
substitution of a headline theorem. No false premise or counterexample to them
has been established. The H1 contract comments and adapter modules cite the landed C2 dependency.

**Findings and effort.** No new Rule Zero finding. Exchange tagging and final
journal projection were substantial; direct H1 reuse is bounded adapter work,
not a new replay proof. Historical wall time was not measured. The landing repair constructs the direct
adapters; proving the remaining stronger packages is separate work. Its files
include raises.

**Ranked mirror changes (none adopted).**
1. Factor the original session rotation/clear suffix as a named operational
   helper — altitude-preserving, reducing repeated source inversion.
2. Store exchange epochs in native peer state — not altitude-preserving; the
   epochs are proof-side history and are absent from the C.

## T5 — responder key confirmation

**Architecture and claim.** Pending allocation tickets, promotion labels and
responder key material share the transport journal. The final discipline links
responder AEAD to an earlier accepted confirmation of the same allocation and
requires distinct promotion labels, including retained inner receipts before Stop.

**Premises and both wordings (S1).** The original headline was unconditional.
The implementation took `PendingPromotion.H1DriverFrames` and
`H1ResponderCurrentEdges`. `LandedH1PendingFrames` constructs the direct frame
fields from C2 H1; their direct check passes. Its aggregate still takes
`H1PendingPromotionEdges`, whose confirmation clause names the actual actor and
whose session clause includes bounded/unique pending-store transport. H1's
abstract `Step` alone does not retain the required actor equality. Together
with `H1ResponderCurrentEdges`, these remain unconstructed local premises in
the final claim. Thus the result remains conditional, not complete; replacing
these packages by initialized confirmation as an assumption would be circular.

**Findings and effort.** No new mirror finding. Pending-store frames and journal
transport dominate this outcome; direct frame reuse avoids reproving them.
Historical wall time was not measured. Its files include grandfathered raises.

**Ranked mirror changes (none adopted).**
1. Name the existing promotion and post-confirmation suffixes — altitude-
   preserving; would reduce source-equation duplication.
2. Make a native key type encode that a responder was confirmed — not
   altitude-preserving; it replaces a behavior to prove with a typing assumption.

## T6 — reference-aware key retirement

**Architecture and claim.** `reference_aware_retirement_outcome : Outcome`
has eighteen documented fields, not one end-to-end retirement run theorem.
`txChecks`, `rxChecks` and `ageCheck` are universal native check-site contracts;
rejection fields establish local invalidation. `initializedAccess` cites R2's
initialized audit safety, while `initializedCredits` is a final successful-run
holder account. `derivedArm` is per call, `selectedArm` is initialized timer
provenance, and `timerDispatch` requires a live entry. Worker and release fields
are implications from actual successful calls; final removal requires entry
refcount one. Removed-read/acquire fields concern that call's entry, not
permanent absence. Authenticated RX cleanup obeys the same final-reference rule.

**Both wordings and boundaries.** Original T6 forbade encryption with invalid
or expired sending keys even for retained work. The October 18 replacement
checks validity/age at TX admission and validity/age/count before RX decryption.
Slot/index unpublication does not destroy a packet-held reference. Previously
admitted packets may encrypt after expiry or unpublication, with **no time or
count bound proved**. The headline does not itself link delayed AEAD to its
admission certificate. `initialized_conditional_tx_retirement` and RX companions
are separate runner compositions with supplied dispatch, worker and last-reference
release premises. Neither fairness nor physical memory zeroization is proved.

**Finding and effort.** C3-F1 is the retained statement artefact documented
below, using R5's two existing witnesses. Holder accounting and all release arms
were substantial; unconditional progress was never obtained by hiding scheduling
premises. Historical wall time was not measured. Its files carry grandfathered
raises. The landing repair documents all eighteen domains explicitly.

**Ranked mirror changes (none adopted).**
1. Name each existing clear/unpublish/final-release suffix — altitude-preserving,
   reducing duplicated call inversions without changing ownership.
2. Cancel queued encryption or erase material when a slot is cleared — not
   altitude-preserving and behavior-changing; R5's witnesses exercise the C's
   retained-reference behavior that this would remove.

## C3-F1: invalidation and clearing do not cancel previously admitted encryption

**Target amendment [USER 2026-10-18], recorded for S5.** Before the amendment,
T1's limit clause forbade later encryption under a key once its sending limit
was reached. The replacement forbids further staging admission, invalidates
the key and restores the batch, while permitting earlier admissions to encrypt
with their unique, below-limit reservations. Before the amendment, T6 forbade
encryption with an invalid or expired key, including already admitted work.
The replacement enforces TX validity/age at admission and RX validity/age/count
at the check before decryption; unpublication and final reference release are
separate retirement steps. These are narrower timing/cancellation claims,
adopted on October 18, not a claim that the original statements were proved.
Nonce uniqueness and the bound on encrypted nonces remain unchanged. The
decision and its provenance are in [decisions.md](decisions.md).

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

Individual reproduction from the repository root:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-delayed-encryption |
  cap lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-coherent-post-clear |
  cap lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
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

## Landing-review dispositions

| Item | Disposition |
| --- | --- |
| B1 | Corrected the false campaign-wide resource claim, with the census scope and grandfathering decision above. |
| S1 | Direct landed-H1 adapters are supplied; the remaining named premises keep T4/T5 conditional. The direct adapters elaborate without additional resource settings. |
| S2 | T2 now says declared cuts, per-point existential accounts and audited coverage; headline binders are explicit and both admission-boundary wordings are recorded. |
| S3 | Binding is described as separate pieces, including the plaintext/occurrence and socket-world join boundaries. |
| S4 | All eighteen T6 fields have domain docstrings; the report and register state unbounded retained work and separate conditional runner retirement. |
| S5 | Both T1/T6 wordings and the October 18 user amendment are recorded in the report and decisions file. |
| S6 | T3 names H3's transport endpoint result and the per-invocation, per-call and fixture-root scopes. |
| S7 | Six per-result reports and Results-table rows replace the campaign's tranche logs and stale open/complete claims. |
| S8 | Reproduction uses the current clone's root and scripts, with an optional cap wrapper; private-ref recipes are removed. |

The related N1–N3 notes are reflected in the observer-completeness boundary,
T1's trimmed encoding docstring and function-level rejection wording. None of
these documentation corrections adds a coverage or progress theorem.

## Validation and reproduction

The post-review full gate and counterexample speedbump are pending. Main's
shared carry records one known speedbump lag: C2's `h5-namespace-pin` recipe
still expects parser acceptance that mirror `218d3ffd` intentionally refuses.
This campaign does not edit C2's files or reinterpret that failure as a pass.

Run from the repository root of a clone with Python 3 and the pinned Lean
toolchain on `PATH` (for example through elan, which reads `lean-toolchain`):

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap scripts/proof-gate
cap scripts/proof-counterexamples
cap lake env leanchecker --fresh Leanux.Proofs
```

On a checkout with the optional staged bundle already prepared, insert
`scripts/in-bundle` after `cap`; that is the environment used for the checks
reported here. The plain commands above do not require that bundle.

The counterexample speedbump includes both R5 recipes used for C3-F1. No recipe
requires a private archive ref, an old pre-rebase commit or a worktree-specific
path. The gate checks the complete imported terminal surface, standard axioms
and forbidden trust tokens. Kernel replay is an additional check of the built
root; validation counts and the checked head will be recorded when retrieved.
