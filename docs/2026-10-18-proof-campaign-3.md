# WireGuard proof campaign 3

## Progress

[AGENT 2026-10-18] Work begins on `proofs/campaign-3` at `783510e8`, under
the [revised charter](2026-10-18-charter-proof-campaign-3.md). The inherited
proof tree includes campaign 1's GRO carry. No mirror definition or landed
proof has been changed. The source contracts now cover staged nonce allocation, encryption receipts,
cookie egress, native handshake histories and session reference payments. T1, T4, T5 and the amended T6 are complete and validated; T2 and T3 remain open.

**C3-F1 is dispositioned as a statement artefact.** The original T6 wording
excluded behavior already represented by R5's coherent initialized replays.
Both reproduce on this branch. [USER 2026-10-18] Resume with the actual TX
admission/RX decryption checks and reference-aware retirement, retaining the
counterexamples. Further wording artefacts are corrected while work continues;
only a blocker, substantive finding, completed campaign or user instruction
stops the work. Validation for the current source-contract checkpoint is recorded below.

| Outcome | Status and remaining obligation |
| --- | --- |
| T1 nonce safety | Complete and validated. `initialized_nonce_safety` joins unique native reservations, actual key-allocation/nonce pairs, bounded serialized AEAD nonces and exact packet/header encoding, including stopped prefixes. Universal native rejection contracts prove invalidation, whole-batch restoration and unchanged drop count; the native rekey contracts expose the guarded helper request. No incoming invariant or campaign-2 premise remains. |
| T2 transmit authorization and conservation | Open. `initialized_staged_selection_origins` derives ordered, distinct routing/keepalive positions through the whole native initialized runner, including Stop. `initialized_allocated_staged_occurrences` retains the selected peer allocation, exact plaintext sequence and those prior batch positions. `initialized_encrypted_plaintext_origin` and `initialized_socket_route_key_core_and_endpoint` join that history to each actual AEAD and transport socket receipt in the same final journal, with no incoming carrier or H1 premise. Socket bytes, endpoint, packet peer and historical current-slot sending core are bound. The current tranche also derives historical key-owner equality at the actual allocation entry and joins it to the socket peer through the same AEAD material; that strengthening passes the aggregate gate and fresh replay. Native overflow/purge and creation-refusal arms expose their exact effects. Initialized TX ownership and native work service cover resident cells, scheduling, deferred calls and peer removal; destructor disposal retains its explicit idle-entry premise. `staged_available_ticket_unique` proves allocation-position injectivity under the explicitly named `Staged.Availability.BankValid` premise; the strengthened carrier has native allocation and ordered-birth transfer support. The native initialized Runner now derives the bank and cross-allocation uniqueness without an incoming invariant; scoped validation passes. Complete pending/terminal conservation and converse coverage of every emission remain open. Batch-local distinctness and queue aliases do not discharge those obligations. |
| T3 authenticated effects and silence | Open. R6 supplies the cookie gate's local contracts. Initialized exact timer-arm and queued-work occurrence provenance is proved; each held GRO packet now has its own earlier authenticated replay/AEAD occurrence. Each active handshake context now has its own latest valid native admission; each completion context has its actual earlier allocation parent. Initialized causal scope prefixes are well formed, including nested callbacks and Stop. Every initialized timer arm, work append, TX allocation, transport socket receipt and keepalive preparation now has a finite chain of exact earlier occurrences ending at a fixture or its own authenticated handshake/transport receive, including Stop. Candidate effects carry their own accepted replay and earlier AEAD. The same final driver now records native protocol and cookie socket returns. Each protocol-send receipt has its own initialized causal root and native endpoint/byte emission fact; cookie receipts are native-valid and qualified by actual under-load and MAC decisions on initiation/response input. Successful response lookup followed by refusal restores every peer record without a borrowing premise. Ordered emission accounting now distinguishes every socket append occurrence; actual protocol and cookie sends, handshake receive, queued/direct send workers and timer/work effects preserve it. Final initialized exchange-entry positivity now discharges the resident-positive premise for response-refusal, including later Stop. Initialized cookie-consumer entry positivity and native validity now discharge refusal premises; rejected cookie, response and initiation consumers restore complete peer and keypair records. Exact initialized pre-delivery positions now join strictly earlier authorized native appends, and every retained append ordinal has its own root or qualifying cookie exception. Full internal-append completeness and rejected-replay counter-state preservation remain under audit. |
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

Campaign 2 remains a read-only dependency. Its report was read at `ca860a24`,
with H1 initially named at `3407cbff`; operational tag/frame interfaces are
pinned at `5177bd9c`. Final claims retain named hypotheses such as
`H1ResponseEdges`, `H1SessionEffects` and `H1ResponderCurrentEdges`. The new local pending-promotion interface names
`H1PendingPromotionEdges` from read-only C2 pin `7ff94e48`; its initialized
transport now closes through the native runner, with the local facts collected
in `PendingPromotion.H1DriverFrames`. No campaign-2 fact is silently discharged and no
campaign-2 file is edited.

[AGENT 2026-10-19] The next tranche adds explicit delivery and completed-cookie
observations to the shared proof source. Delivery is observed before the native
operation, so its receipt survives an intermediate Stop; the native operation
is executed once. Exact specialization, projection and history contracts compile.
Outcome-specific adapters and initialized staged-origin linkage pass the
aggregate trust checks. Initialized exchange and cookie entry
positivity discharge complete peer/keypair restoration on refusal for all
three consumers. The native TX scheduler and all deferred-call arms discharge
worker and NAPI callback premises. Terminal conservation and converse emission
coverage remain open.

The preceding checkpoint `3cb2bfc9` adopts T3 `09388dfa`, T4 `224a3beb` and
T6 `a6412499`, matching every adopted preimage. Ordered emission accounting
now crosses native TX completion; the actual delivery entry retains the
pre-clear buffer through Stop. Initialized consumer entries discharge the
positive-reference premises needed for full peer/keypair refusal restoration.
Native TX service crosses all deferred-call arms, full peer removal and
lifecycle endpoints. The destructor's exact before-reset disposal cut retains
its explicit idle-entry premise. Whole-run conservation and full emission
coverage, including delivery-cleared prefixes, remain open.

[AGENT 2026-10-19] T2 retains queue order and duplicate positions at the native
splice, overflow and purge boundaries. Keepalive preparation has its own exact
source contract. Historical keepalive origin uses an actual preparation
receipt in the shared driver. The preparation definition moved to a proof-side leaf to avoid a driver import cycle; its name and native body are unchanged.
This is a provenance decision; T3 must establish causal authorization separately.
The staged-origin carrier uses positions in that same final journal, packet
ordinals, device epochs and peer allocation stamps; equal payloads do not identify
occurrences. Native routing and keepalive hooks introduce fresh positions, selection retains
the saved sequence while clearing its queue, and restoration preserves that
sequence. The complete staging source now preserves this carrier through reservation, restoration, allocation and publication; early restoration has a different intermediate postcondition from a still-held batch. The complete transmit and keepalive source contracts compile. Exact native frames now cover timer placement and metadata, cache/endpoint updates, IPv4/IPv6 socket sends and buffer sends; observed timer effects preserve the staged carrier. Their incoming carriers remain explicit; the native configuration, peer-removal, lifecycle and dump transports now compile as well. The initialized outer transport and allocation/encryption/socket joins now pass scoped builds. Their final claims have no incoming carrier premise.

The staged-origin carrier now crosses the complete handshake, receive
completion, flushed send work and all five timer callbacks. Native peer writes
retain the exact preceding getter; arbitrary setters are not frames. Actual stack replies, both receive-poll forms, replay checks, encryption,
decryption, TX completion and the draining scheduler now preserve the same
carrier. Local source exports retain their entry carriers; the initialized final exports
discharge them through every typed runner operation. The
[independent review](2026-10-19-review-campaign-3-staged-origin.md) identifies
three remaining T2 connections: historical key ownership, cross-allocation
conservation, and converse emission coverage. All are accepted. The current tranche repairs historical key ownership at
the actual successful native admission dereference, retaining the owner word
only in the earlier allocation certificate. Retirement may clear the later
owner word. The initialized socket join passes its 1970-job scoped build
without an incoming carrier or C2 hypothesis. Conservation and converse
emission coverage remain open.

[AGENT 2026-10-19] The next tranche adopts exact owned deltas through T3
`b0b16463`, T4 `a96faace` and T6 `2f840b6c`. Native delivery certificates retain
every ordered pre-clear position, including before a later Stop. Actual boot
and operation prefixes now derive empty suspended-worker entries, including
the first operation. Direct sent-buffer frames cover product adapters, full
and stepped dumps, and namespace cleanup; WGStore framing is insufficient
for that buffer. Complete emission coverage and historical pending/terminal
conservation remain open. Native poll, stack, NAPI, timers and the paired delivery carrier now retain live emission ordinals and all earlier delivery certificates. Descriptor wrappers preserve native TX service and suspended actors. A separate staged-availability carrier proves conditional cross-allocation ticket injectivity: its explicit bank-validity premise is not yet discharged by the initialized runner. Aggregate proof gate, fresh replay, witnesses, model and unit checks pass for this tranche.

The current tranche adopts exact preimages through T3 `0bdd8d7d`, T4
`c43d6d68` and T6 `66514c74`. Native worker, scheduler, traffic, configuration,
lifecycle and actual Runner delivery positions now join their exact earlier
append receipts and causal authorization. Descriptor cleanup, ingress, traffic,
full and stepped dumps and data dispatch carry native TX service and suspended
actors without assumed FS or ambient frames. The strengthened live-credit
carrier now crosses the complete native driver and actual initialized Runner;
`initialized_available_birth_bank` and `initialized_available_birth_unique`
discharge the former bank-validity premise, including Stop. The source build
passes 1487 jobs; aggregate validation for this tranche passes below.

The [forward conservation review](2026-10-19-review-campaign-3-t2-completeness.md)
identifies four accepted gaps which the allocation-injectivity theorem does
not claim to close: fixed-ticket staged-disposal accounting, first terminal
outcomes separated from later cleanup, stopped caller-local frontiers, and
explicit early-error/GSO counting units. No initialized counterexample or
mirror defect was established by that review. Work continues on those exact
source cuts. The T3 audit separately requires internal-append completeness
and rejected-replay state preservation: the existing replay non-reacceptance
property alone does not constrain unseen bitmap bits. An arbitrary malformed
counter is not an initialized counterexample.


## Validation

The current checkpoint passes 2860 proof jobs and the 1506-declaration gate
across thirteen roots, with only `propext`, `Classical.choice` and `Quot.sound`;
all twelve counterexample recipes and fresh root kernel replay pass. The model
build passes 130 jobs and the unit suite passes 131 tests (one configured-kernel
skip, 23.266 seconds). All 2805 frozen proof-source hashes matched; all 916
inherited proof modules, main at `783510e8` and mirror `77c9b555` were unchanged.
The proof root retains its authorized campaign imports.

Reproduce the proof and model checks from the campaign worktree:

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle scripts/proof-counterexamples
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle lake build leanux-model
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The inherited `Leanux/Env.lean:865` `String.mk` deprecation is outside this
proof lane and is neither suppressed nor changed. The gate's nested wrapper
lookup reports that `capped` is absent inside the bundle PATH; the outer
wrapper contains the gate and its children. No differential guest run is
claimed for this proof-only work.

Failed development checks remain failures: earlier non-fresh checker runs hit
the 32 GiB and 64 GiB caps (exit 137), and `--help` unexpectedly selected the
default module prefix and hit 32 GiB. The documented fresh-root command avoids
that task-per-module expansion. Earlier tactic/inference failures and the
earlier completion-source heartbeat exhaustion were repaired without changing
a statement or the mirror. The current delivery/cookie integration and staged-origin
transport had local missing-case, binder and projection errors, all repaired.
An overly broad routing-frame tactic caused heartbeat exhaustion; a native
head guard repaired it without increasing the limit. A new tactic's unchecked expression-array access
produced Lean panic diagnostics during earlier completion-source work; all twelve worktrees
were audited and all seven dirty trees preserved, including untracked files,
under `refs/snapshots/all-dirty-after-tactic-panic-20261019-043500-*` before
repairing it. Checked optional access now rejects nonmatching goals normally.
The subsequent source build and complete trust checks pass. Earlier routing-splice heartbeat exhaustion was repaired with a compact
projection and reducible application. Shared-hook integration initially failed
on an import cycle and missing proof/interface cases; the native preparation
leaf and explicit frames repair those failures. The staged carrier's initial
name, induction, projection and source-composition errors are also fixed. No mirror change or weakened claim
was used. Protocol-socket integration initially failed in two older exchange
projections; compact projection adapters repair those failures without raising
their heartbeat limits. The full gate and fresh replay then pass. The historical-owner and direct-emission tranche repaired local binder, namespace, frame and induction errors; the initialized live-credit bank now discharges its incoming premise. The availability transport repaired one copied tactic-head mismatch; no native statement or mirror behavior changed.

The branch is preserved without merging or pushing. Completed checkpoint
history and its individual validation counts remain in the branch commits.
