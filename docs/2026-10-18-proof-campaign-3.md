# WireGuard proof campaign 3

## Progress

[AGENT 2026-10-18] Work begins on `proofs/campaign-3` at `783510e8`, under
the [revised charter](2026-10-18-charter-proof-campaign-3.md). The inherited
proof tree includes campaign 1's GRO carry. No mirror definition or landed
proof has been changed. The source contracts now cover staged nonce allocation, encryption receipts,
normal cookie egress, native handshake refusal and reference payments. No
complete campaign outcome is claimed.

**C3-F1 is dispositioned as a statement artefact.** The original T6 wording
excluded behavior already represented by R5's coherent initialized replays.
Both reproduce on this branch. [USER 2026-10-18] Resume with the actual TX
admission/RX decryption checks and reference-aware retirement, retaining the
counterexamples. Further wording artefacts are corrected while work continues;
only a blocker, substantive finding, completed campaign or user instruction
stops the work. The inherited validation below describes checkpoint `333f3818`; current
tranche checks are recorded separately as they finish.

| Outcome | Status and remaining obligation |
| --- | --- |
| T1 nonce safety | Open. Existing staging certificates give bounded assigned nonces, but not initialized allocation uniqueness, non-reuse after failure, or the connection to every actual encryption. The complete native staging observer preserves a supplied non-reuse invariant through queue refusal and Stop; native creation preserves it, and admitted counters have injective AEAD encoding. Initialized allocation history and packet transport remain open. |
| T2 transmit authorization and conservation | Open. R3 supplies initialized selection-time authorization; packet/material transport to actual encryption and socket emission, and complete TX dispositions, remain to prove. |
| T3 authenticated effects and silence | Open. R6 supplies the cookie gate's local contracts, not causal closure of all delayed effects. |
| T4 handshake replay resistance | Open. Source inventory and H1 interfaces identified; retained-peer timestamp histories and exchange-linked installation still need initialized execution closure. |
| T5 responder confirmation | Open. H1 now includes initialized confirmation uniqueness; accepted-RX linkage and the prohibition on earlier responder encryption remain to prove. |
| T6 key retirement | C3-F1 concerns the literal actual-encryption clause. R5 supplies the admission/attempt checks. New native put/clear contracts prove exact reference payment, retention and final removal; initialized holder accounting and conditional cleanup remain open. |

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
warranted. The six security outcomes remain unfinished.

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

## Existing proof boundaries and follow-on work

The following are reused facts, not new campaign-3 results:

- `KeyLifetime.original_staging_admissions` establishes actual historical
  key/clock/allocation certificates and bounded submitted nonces, including
  prefixes before a later Stop. It does not transport those facts to every
  encryption or prove non-reuse of abandoned allocations.
- `KeyLifetime.original_receive_attempt_admission` establishes validity,
  the actual unexpired clock comparison and stored-counter bounds at the
  AEAD boundary, whether or not authentication succeeds. Its counter is
  distinct from the incoming wire nonce.
- `CryptokeyRouting.parsed_initialized_transmit_authorization` establishes
  the original selection-time authorization, not subsequent emission.
- Campaign 2 at `3407cbff` has `Noise.original_slot_rotation`,
  `original_confirmation`, `original_begin_session_ordered`, and
  `original_session_allocation_refusal`, plus
  `original_initialized_driver_tags`,
  `original_initialized_confirmation_order` and
  `original_initialized_confirmation_unique`. The initialized uniqueness
  theorem records completed confirmations even before a later Stop and
  distinguishes allocation identity across device recreation. These remain
  unlanded dependencies; no claim here silently imports or discharges them.
  Tag coverage alone does not establish retained-peer exchange identity.

The next useful proof boundaries are a sending-key projection plus nonce
allocation events (including abandoned attempts), packet allocation and
consumption identity through the existing queue observers, and retained-peer
timestamp/exchange histories. The sending projection must not reuse the RX
window or receiving-key-material projection as if it described sending
state. Existing session receipts and actual receive-poll cuts provide the
starting points for confirmation; a slot invariant alone is insufficient.

The design reading adds three constraints to that follow-on work. AEAD coverage
must include `Env.cryptAhead` as well as ordinary encrypt activations, keeping
copied consistency trials separate from committed execution. B3's retirement
premise must use the actual wheel bucket and dispatch, with deletion and
replacement explicit, rather than a fixed delay bound. T3's cookie exception
bounds a reply per qualifying input; the rate limiter runs only after valid
MAC2, so it does not bound the rate of cookie replies.

Three read-only agents independently inspected the statement/source fit,
nonce architecture, and handshake/confirmation interfaces. Their shared
T6 observation is supported by the source references above; the replay is
the concrete check. No shared proof definition requires alteration for this
finding. Ranked mirror changes: none recommended; adding encryption-time
retirement guards would not preserve the mirror's altitude or C behavior.
An independent review of this documentation checkpoint found no actionable
issue after checking the mirror/replay boundaries, registered recipes,
campaign-2 theorem names and unchanged mirror pin. Its C assessment relied on
the earlier audits; the campaign's source inspection used the pinned pristine C.

## Current proof tranche

[AGENT 2026-10-18] Add source contracts before composing initialized execution
coverage. The sending projection uses the native global allocation stamp and
sending counter. `Nonce.reserveObserved_safe` preserves non-reuse under an
explicit entry invariant and records the increment before bound rejection;
`Nonce.stagingObserved_erases` covers the complete original staging control flow.
`Nonce.stagingObserved_safe` preserves the invariant through that whole path,
including refusal and Stop prefixes; `Nonce.create_preserves` supplies the fresh
allocation step. Separate frames cover peer/index/queue bookkeeping and key
reference operations. `WireNonce` proves the actual admitted Nat counters have
injective 64-bit wire and AEAD encodings. These facts do not yet prove initialized
staging coverage or single-use packet transport to AEAD. The encryption
observer now records at most one real result per native call, with actual
preparation/key-read witnesses and exact erasure. A separate preparation frame
connects the AEAD key to the entry-resident allocation; the emitted byte
expression uses the packet nonce in both the header and AEAD. This is local
encryption binding, not staging-to-worker provenance.

`RetirementSecurity/Statements.lean` initially exposed six native contracts: exact payment
of one reference, unchanged material/counter on nonfinal payment, final store
and index removal, immediate unpublication, surviving nonce retention, and
clear's empty slots with surviving-key retention. Actual normal-call premises
and entry counts remain explicit. These are not a credit-ownership proof or a
progress guarantee. The stable implementation originated at child commits
`6254ed0e` and `b6a285af`; only their new proof files were copied into this
branch. The second tranche adds an exact allocation-stamped reference ledger,
creation/get/put accounting, last-credit removal and finite native payment
composition. Tranche `8ef2ac86` connects clearing to the actual three slot
occurrences, including alias multiplicity, and connects RX cleanup and TX batch
disposal to their saved single references. The concrete durable-holder projection
counts slots, RX packets and TX batches and has its actual initialized empty
base case. Whole-run holder preservation and scheduling progress remain open.

`AuthenticatedEffects/Statements.lean` exposes qualifying invalid-MAC2 dispatch
for both initiation and response, the normal Noise/session frame, and bounded
construction and socket-call attempt receipts retained through a later Stop.
The input/source bindings are exact. Tranche `44c2d981` now proves a normal
qualifying original receive appends at most one actual datagram, whose address
and port are the input source and whose bytes come from the actual cookie
construction. Byte length, emitted prefixes through Stop and initialized causal
closure remain open. Stable implementations originated at child commits
`e2c12a6b` and `44c2d981`; only owned proof files were copied here.

`HandshakeSecurity/Statements.lean` now records actual strict timestamp
increases from the full original initiation consumer, without an entry
freshness/coherence hypothesis. It also proves the stale comparison suffix
returns no peer and preserves surviving handshake projections, and that a
receipt survives a subsequent consumption-clock Stop. The compared value is
connected to the actual pre-write timestamp. Initialized lifetime history and
exchange-linked installation remain open. Implementation commits `dcad7f81`,
`3e765ac0`, `d957fa01` and `62423b54` were copied by owned path. The last
tranche also proves full native initiation refusal preserves surviving peers
and transports strict timestamp receipts through the original receive worker.
The child continues toward retained-peer history.

The first 14 new terminal exports passed the full proof gate (990 build jobs,
909 declarations over 12 root modules, standard axioms only). All twelve
counterexample recipes passed again. The extended source tranche builds with
1000 jobs. The next complete checkpoint passed 1009 build jobs and the
922-declaration gate over 13 root modules. The current checkpoint passes 1029 build jobs and 932 declarations over
13 root modules with only standard axioms. Its unit run passes 131 tests
with one kernel-build-dependent skip. All twelve counterexample recipes and
fresh-root kernel replay pass again for this checkpoint, at the default cap.

A supplemental kernel replay invoked without `--fresh` failed at the 32 GiB
cap and again at 64 GiB (exit 137); neither is a pass. Inspection of the shipped
`LeanChecker.lean` showed that this form launches one task per matching module.
An attempted `--help` likewise had no help behavior and selected the default
module prefix, failing at 32 GiB. Dirty worktrees were snapshotted to project
refs with branches untouched. The bounded replacement command is
`capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs`, which
replays the root's complete environment in one task. It passed at 32 GiB
over the 1000-job checkpoint (before the subsequent timestamp extensions).

## Validation

Both explicit coherent replays pass: original runner accepted, observer JSON
equal, lifetime 1 and nonce 1 retained, expected ciphertext emitted, and the
post-clear variant's final reference released. These are interpreter checks,
not kernel-proved universal statements.

The model build passes all 130 jobs. The unit suite passes 131 tests with one
skip: computing the selected kernel build's identity when no such build is
configured. These checks used:

```sh
capped -- scripts/in-bundle lake build leanux-model
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The inherited `LeanuxProofs` build passes all 973 jobs. The full proof gate
passes all 895 declarations over nine root modules, using only `propext`,
`Classical.choice` and `Quot.sound`; its token, import and target checks pass.
The counterexample speedbump passes all twelve recipes, including both coherent
T6 witnesses and W7's full ring. These checks used:

```sh
capped -- scripts/in-bundle lake build LeanuxProofs
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle scripts/proof-counterexamples
```

The builds report the existing `Leanux/Env.lean:865` `String.mk` deprecation;
it belongs to the mirror lane and is not suppressed or changed here. The gate
also reports that its nested wrapper lookup cannot find `capped` inside the
bundle's PATH; the outer `capped` invocation still contains the gate and its
children in the capped cgroup. No differential check or guest was run.

At checkpoint `333f3818`, only documentation differed from main. Current work
adds proof files and root imports; the mirror and existing campaign-1 proof
lemmas remain unchanged. The branch is preserved without merging or pushing.
