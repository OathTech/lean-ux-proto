# WireGuard proof campaign 3

## Progress

[AGENT 2026-10-18] Work begins on `proofs/campaign-3` at `783510e8`, under
the [revised charter](2026-10-18-charter-proof-campaign-3.md). The inherited
proof tree includes campaign 1's GRO carry. No mirror definition or landed
proof has been changed. The source contracts now cover staged nonce allocation, encryption receipts,
cookie egress, native handshake histories and session reference payments. No
complete campaign outcome is claimed.

**C3-F1 is dispositioned as a statement artefact.** The original T6 wording
excluded behavior already represented by R5's coherent initialized replays.
Both reproduce on this branch. [USER 2026-10-18] Resume with the actual TX
admission/RX decryption checks and reference-aware retirement, retaining the
counterexamples. Further wording artefacts are corrected while work continues;
only a blocker, substantive finding, completed campaign or user instruction
stops the work. Validation for the current source-contract checkpoint is recorded below.

| Outcome | Status and remaining obligation |
| --- | --- |
| T1 nonce safety | Open. Existing staging certificates give bounded assigned nonces, but not initialized allocation uniqueness, non-reuse after failure, or the connection to every actual encryption. The complete native staging observer preserves a supplied non-reuse invariant through queue refusal and Stop; native creation preserves it, and admitted counters have injective AEAD encoding. Initialized allocation history and packet transport remain open. |
| T2 transmit authorization and conservation | Open. R3 supplies initialized selection-time authorization; packet/material transport to actual encryption and socket emission, and complete TX dispositions, remain to prove. |
| T3 authenticated effects and silence | Open. R6 supplies the cookie gate's local contracts, not causal closure of all delayed effects. |
| T4 handshake replay resistance | Open. Source inventory and H1 interfaces identified; retained-peer timestamp histories and exchange-linked installation still need initialized execution closure. |
| T5 responder confirmation | Open. Initialized completed consumers and replay entries have earlier native AEAD evidence; responder chronology and the prohibition on earlier encryption remain to prove. |
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

[AGENT 2026-10-18] Source contracts precede initialized execution closure.
The combined TX journal uses a shared parameterized driver with a definitional
nonce specialization and exact internal event projection; output equality alone
is insufficient to connect separate observers’ occurrence histories.
Every claim keeps its native run and entry invariant visible. The register in
[proofs.md](proofs.md) lists the four statement modules and outstanding boundaries.

- T1/T2: the actual global allocation stamp and sending counter support
  non-reuse through complete staging, `wgXmit`, keepalive sending, key creation,
  session establishment, rotation, all five timer callbacks, the full handshake receive worker, receive consumption, the complete poll with actual stack replies, both NAPI entry points, all draining workers, the native scheduler, both wheel passes, fixture injection/flood/batch, direct transmit, full device configuration, interface-up and reference release. Copied-state consistency trials emit no nonce events. AEAD counter encoding
  is injective below the actual admission limit. Encryption receipts preserve
  success/Stop and bind the entry-resident key, original packet nonce and
  actual ciphertext expression. Rekey receipts capture the guarded call to
  the handshake-queue helper after count or recorded-age expiry; the helper's
  own timeout/dead/pending guards still apply. The complete native syscall observers now compose from actual fixture initialization for every typed trace and both placeholder modes: reservation journals are duplicate-free, including failed prefixes, and erasure returns the original JSON or indexed Stop. No entry invariant or valid-trace premise remains. Native batch allocation now binds each returned ID to its original full packet value, and complete encryption/publication preserves peer, key slot, nonce and plaintext. Native worker receipts now bind every recorded AEAD to the actual head-key word and per-packet read, including later Stop. The shared parameterized driver now records allocation/routing, ring selections, actual AEAD receipts and TX dispositions in one chronology. Exact projection to the original reservation observer holds through all callbacks, scheduling, lifecycle and initialized Runner execution, including stopped prefixes. It retains duplicate-free reservations without an entry invariant. Packet ownership from reservation to encryption and TX conservation remain open.
- T6: the exact allocation-stamped reference ledger covers native creation,
  acquisition, release, slot clearing, rotation, confirmation, RX cleanup,
  saved TX batch disposal and complete session establishment. Session funding
  derives the new reference from the actual allocation; entry slot funding
  is now extracted from actual holders; R2 allocation vacancy remains explicit. The concrete holder projection
  counts each slot, RX packet and TX batch reference and has an initialized
  empty base. Native create/get/put, clearing, rotation, confirmation and complete sessions transport that physical projection; an
  outstanding durable holder prevents final removal. The actual clear-worker dispatcher clears its selected queued peer on normal completion, with no incoming holder invariant. Native TX enqueue/disposal now transport the account; current-slot acquisition derives its credit, and native packet allocation derives detachment from C1 packet ownership. Final peer release keeps its slot-readiness premise visible. The clear dispatcher transports the account and derives its own slot readiness. Complete staged allocation/publication now derives packet detachment and peer-release readiness. Native TX completion and the whole TX worker preserve the account under explicit batch separation and final-peer funding. Complete native receive admission derives the index loan, key acquisition, fresh packet detachment, publication and refusal cleanup from the incoming holder account and C1 packet ownership. No post-cut ledger premise remains. The physical TX occurrence inventory derives batch separation for the native TX worker from actual owned queues and selected/unpublished locals; allocator, enqueue, cached selection and disposal preserve it. Whole native createData and its allocation/create suffix now transport the same occurrence inventory through enqueue/refusal cleanup. Full staging now preserves TX occurrence inventory. A separate crypt phase links logical live ring items and active encryption locals to owned UNCRYPTED peer-queue batches, derives uniqueness/residency/disjointness, and transports native admission, poll and encryption completion. Encryption also preserves the holder account and TX inventory. Orphan completeness and initialized phase transport remain open. Whole-run holder transport and conditional clock/dispatch progress
  remain open. Stable child implementations through `046b60e3` were copied
  by owned path, without a branch merge.
- T3: qualifying invalid-MAC2 initiation/response receives produce at most one
  source-bound 64-byte cookie datagram on normal completion and preserve the
  Noise/session projection. Exact append observers retain emissions before a
  later Stop. Invalid MAC1 leaves WGWorld unchanged except under-load
  bookkeeping. The actual MAC/load witness remains explicit. Full Noise refusals follow exact native exits with no egress or authenticated
  suffix, and pre-lookup initiation refusals preserve WGWorld. Post-lookup
  initiation refusal now restores complete peer records, including refcounts
  and timers, from the actual acquisition/repayment chain. Response/cookie refusals now preserve every peer field except the explicitly allowed refcount and index-owner bookkeeping, without an initialized-reference premise. Cookie acceptance receipts precede the first cookie write and survive Stop. Native decryption changes WG state only at the explicit receiving-key invalidation arm; other decrypt outcomes retain the entire WG world. Initialized replay-entry receipts now carry a strictly earlier actual AEAD/publication certificate with matching selected packet bytes, slot and nonce, surviving later internal Stop. This root theorem covers arbitrary typed traces and either placeholder mode without an incoming publication invariant. Native initiation/response acceptance is now observed before the first protocol write; exact full receiver receipts have accepted MAC and Noise evidence for the same bytes and survive Stop. Every native handshake callback now has its own strictly earlier MAC-and-Noise admission for the same peer in that call; callback entries survive internal Stop. Actual session/traversal timer-arm receipts now identify their own enclosing callback by journal index and derive its earlier authenticated admission. Native timer arm/delete and due selection carry their exact occurrence cause under a visible carrier. Response keepalive/staging work append and createData submission receipts carry their own authenticated callback root. Ordered send-work tickets distinguish duplicate peer occurrences; native selection/dequeue preserves order and retains the selected receipt through worker Stop. Their root linkage still requires the explicit queue carrier. Full reference restoration and initialized delayed-effect carrier transport remain open. Stable child
  implementation through `4310965c` was copied by owned path.
- T4: full original initiation receipts strictly increase the actual pre-write
  timestamp, including before Stop; refusal preserves surviving handshake
  state. Native consumer sequences compose timestamp histories. Response and
  session sequences, including mixed sequences, consume at most once under
  named visible `H1ResponseEdges` and `H1SessionEffects`, projections of
  campaign 2's unlanded H1 results. Independent native allocation receipts
  establish at most one creation per session call and exactly one on true
  completion. Full driver/exchange closure remains open. Stable child
  implementation through `7934fb67` was copied by owned path.
- T5: original receive-consumer and poll observers record the native
  confirmation return immediately, before the timer/staged-send/routing suffix
  can Stop; poll receipts carry the actual successful replay check. Every
  initialized completed-consumer occurrence has an earlier successful native
  AEAD with matching bytes, slot and nonce, using campaign 1's receive journal.
  Completed-confirmation uniqueness uses visible `H1InitializedCompletedConfirmation`,
  an explicit projection of named unlanded H1 results. Staging receipts bind
  the actual initial peer/current-key read and key borrow to bounded packet
  admissions. The responder-current projection now has an empty base and exact material continuity through the native staging borrow/read prefix. Local installation/promotion/clear transitions keep H1ResponderCurrentEdges visible. Whole staging, completed consumers and native polls now transport responder authorization, including concrete Stack replies, under visible current-slot/history invariants and named H1 contracts. Both NAPI sites and crypt workers transport the history, while session transport joins C1 configured identity. The complete native handshake receive worker now carries the responder history through actual session, timer and keepalive callbacks. All five timer callbacks, flushed work and both timer dispatcher modes now transport the same authorization. Actual TX workers, scheduling and every deferred variant now transport the same history, as do full peer/device configuration and lifecycle. Remaining initialized actor closure and the prohibition on earlier responder encryption remain open.

The eighth source checkpoint passes all 1284 proof-build jobs and the
1075-declaration gate across thirteen root modules, with only standard axioms.
All twelve witness recipes and fresh-root kernel replay pass at the default
cap. The unchanged model and unit suite retain the prior checkpoint's 130-job
build and 131 passing tests with one kernel-build-dependent skip. All six
outcomes remain open; packet-to-AEAD and end-to-end effect transport
remain work in progress. The shared source and its exact internal reservation projection are validated at this checkpoint.

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

A configuration proof initially exhausted elaboration heartbeats because a
native public-key computation was offered an ambient-only frame. Its existing
whole-WG frame resolves that mismatch without executing the computation during
unification. An ephemeral diagnostic tactic also indexed a binder as an
application and triggered Lean panic diagnostics; all dirty worktrees were
snapshotted before removing the diagnostic. These failed development checks are
not mirror findings or validation passes.
