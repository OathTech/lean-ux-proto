# Proofs about the mirrors

`Leanux/Proofs/` is the repository's proof tree: every theorem about the
executable mirrors lives there and nowhere else. Proofs are a validation
channel for the models beside the differential check, under Rule Zero: the
mirror is never edited to let a proof close; a proof that cannot close is a
report against the mirror, settled by the check. The standing rule and the
gate are in [AGENTS.md](../AGENTS.md); this file is the map of the tree and
the register of its results.

## Layers

The tree is laid out by layer and by result. Shared layers sit at the top,
subject-specific layers under the subject, and each result in its own
directory whose `Statements.lean` is the gated surface.

- `Leanux/Proofs.lean`: the root. It imports every result's `Statements`
  module and the checked counterexamples; `lake build LeanuxProofs` builds
  exactly this closure, outside the mirror's default build.
- `Leanux/Proofs/Framing/`: generic operational framing over the mirror's
  state and monad. `Basic` says which state an action leaves unchanged, with
  the lifetime distinction a reused keypair slot needs; `WP` is the
  weakest-precondition form; `Allocation` names the mirror's private
  allocation helpers for proofs.
- `Leanux/Proofs/Logged/`: logged copies of mirror functions with erasure
  theorems (erasing the log gives back the original run, state, result and
  failure), from the validator (`Basic`, `RxPoll`) through the workers, the
  scheduler, the environment operations and the syscalls to the runner
  (`Runner`). The erasure core (`Outer`, `Tools`) is independent of what is
  logged; today the log carries validator-acceptance events.
- `Leanux/Proofs/WG/Campaign2/`: campaign 2’s WireGuard-only data projection
  (`View`) and universal execution connection (`Bridge`). Its claims/frame
  file map and current factoring status are in the
  [campaign report](2026-10-14-proof-campaign-2.md#claims-frames-and-the-split-boundary).
- `Leanux/Proofs/WG/CounterWindow/`: the receive counter window as a pure
  model of `counter_validate` (`Model`), its refinement to the mirror's
  `counterValidate` (`Refinement`, the S2 theorems), and replay freedom for
  finite sequences of validator calls (`MirrorCalls`).
- `Leanux/Proofs/WG/Keypairs/`: the keypair store projected with allocation
  lifetimes (`Lifetimes`, `LifetimeMirror`), the ordinary steps that may
  allocate or delete a slot but never alter a surviving window (`Ordinary`,
  `OrdinaryHot`, `OrdinaryRules`, `SnapshotRules`); `Frames/` holds the
  per-function frame contracts over that projection for the kernel helpers,
  WireGuard, pipes, the filesystem syscalls and the environment; `Evolution/`
  carries the acceptance-history invariant through the observers, the
  scheduler, the operations, the runner and the syscalls.
- `Leanux/Proofs/WG/ReplayWindow/`: the first result (below).
- `Leanux/Proofs/WG/Noise/`: campaign 2's local handshake-state and session-slot
  contracts; whole-run ownership and lifetime confirmation remain open.
- `Leanux/Proofs/WG/Index/`: campaign 2's owner/index table and recorded collision-prefix contracts;
  whole-driver reachable coherence remains open.
- `Leanux/Proofs/WG/Roaming/`: campaign 2's source-endpoint and remote-destination
  contracts; receive authentication provenance and whole-run coverage remain open.

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

## Results

Campaign 2 incorporates state-split mirror `b700659`; each row distinguishes
its terminal validation from the remaining charter scope. The
[retrofit report](2026-10-16-proof-campaign-2-state-split.md) records baseline
counts, carries, deletions and validation. This branch retains the proof
target and gate removed from main pending campaign 1's landing.
The complete owned retrofit checks 1,983 theorems in 587 modules (1,321
retyped/generalized, 244 corrected statements, 239 retained and 179
support/finding declarations), deletes twenty-two type-given frames, and
separately retires five refuted historical cookie claims. All H1–H6 terminal
modules now check over the split mirror. The full gate fails in inherited
CounterWindow.Refinement and ReplayWindow.Counterexamples.
Subsequent H2 confirmation, local owner-coherence, ingress/removal and release-domain
contracts add 88 theorems and twenty-five headlines; whole-response entry and actual session-clock
provenance add eleven H1 theorems and two headlines; mixed H4 readback adds eight
theorems and two headlines; invalid-MAC1 preservation adds four H3 theorems
and one headline; the first actual outer timer turn and its retransmit
receipt add seven H6 theorems and two headlines. Current totals are 2,101
theorems and 290 headlines in 649 owned modules.
The [cookie-bound finding](2026-10-17-proof-campaign-2-cookie-bound.md)
refutes the old unrestricted activation prediction on malformed ring metadata.
A second checked witness shows that initial logical cookie membership need not
classify the packet exposed by the next physical consume. The corrected source
loop now describes exact bounded execution with actual receive fallback and
retains exhaustion errors; drain adequacy remains open. The full-schedule
witness also checks the actual scheduler refusal on its original domain.
The corrected schedule factors its bounded first turn and actual remainder.
Two further witnesses refute count recomposition and the old logical-only
yield prediction; these make no reachability claim.
The [missing-clock finding](2026-10-17-proof-campaign-2-missing-clock.md)
refutes the old absent-give-up totality on its original input domain. The corrected
give-up contract factors its exact actual arm tail, including errors.
All 52 original H2 terminal declarations and their full Product sequence observations
check; all 258 original audit names remain
in their Statements files.
The [H6 retrofit finding](2026-10-17-proof-campaign-2-timer-carry.md) is a
checked counterexample to the legacy timer-deletion statement after wheel state
was added. A second witness shows that a logical expiry can be due without
a corresponding entry selected by the actual wheel; its scope is arbitrary
model states, not reachability. Projected arming and deletion contracts now describe the complete
current wheel effects; guarded arming and session-derived effects also account
for all wheel changes. Traversal, data-receipt and handshake-completion effects
are corrected too; all seven identified contracts are carried. Their downstream
configuration timer cleanup and recorded-site source effects are also corrected;
jitter and initiation-send arming effects are corrected too. Their timer and worker consumers are also current; complete caller coverage
and whole scheduler episodes remain open.
The [H2 peer-release finding](2026-10-17-proof-campaign-2-peer-release.md)
checks two stopped outcomes within the old totality domain. The corrected
peer-release contract now classifies the exact queue/timer refusal or successful
Device effect under the same premises. Both affected H2 headlines now use checked
projected outcome companions; their full terminal closure and downstream users
are current. No reachability claim is made.
The [H4 queued-handshake finding](2026-10-17-proof-campaign-2-queued-handshake.md)
checks a stale pending-peer prediction after the queue-record change in
`1f0fbeb`; all five queued-send source contracts now carry the actual inspection
result, with exact erasure equalities. Retry, absent/invalid-key staged,
installation and terminal callers now carry the actual observation too.
This inspection does not establish queue-drain completion.
The [H5 backlog carry](2026-10-17-proof-campaign-2-backlog-carry.md) proves
the old accepted fixture now receives the exact pending-work rejection from
the actual runner. General boundary and legacy backlog wrappers are current;
positive global progress remains open.
The [H4 removal finding](2026-10-17-proof-campaign-2-removal-carry.md)
refutes the old quiet/live totality domain using a scheduled NAPI poll and
the actual crypt-work Stop. Its source factor and local removal contracts
are current with their original domains; general ownership transport and
queued cleanup remain open.


| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | 6f1f84c | lagging since 247beec (review item 8 landed 2026-10-13: the two counter-limit tests now carry operands and `CounterWindow/Refinement.lean`'s `counterValidate_execution` expects plain records; the proof campaign repairs it on merge; the index-table entry's `Option PeerId` and `indexLookup`'s store-back, landed 2026-10-14, touch `indexLookup_sameSnapshot` and the `consumeResponse`, `cookieMessageConsume` and `consumeData` frames, repaired on the same merge). Carried from ef7c535 over the epoll landing on 2026-10-13 (the wait-queue, epoll release and epoll system-call frames). |

Campaign 2's working-branch checkpoints (not complete results):

| Result | Checked local surface | Directory | Charter/report | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- |
| H1 Noise session state machine | 24 terminal declarations: state/slot edges; ordered clear/rotation effects and static release budgets; full normal session effects and total recorded success under static post-allocation release readiness; consecutive first-match confirmation; total original initiation creation with exact message/device/record suffix and mode preservation; whole-response entry CREATED_INITIATION to final CONSUMED_RESPONSE; actual derivation-clock receipt through session rotation and publication. | `Leanux/Proofs/WG/Noise/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; 196 checked theorems, projected claims and separate frames. Whole-response entry provenance derives both tags from the actual successful call without coherence/readiness premises. The session receipt derives the actual birthdate from normal whole-call execution; false returns retain their actual prefix, and aliases may erase the allocated key. Remaining whole-call edges/totality and allocation-lifetime confirmation remain open. Session-success premises allow allocation-ID aliases and do not establish final key coherence or reachability. Three standalone restart variants checked; further transport awaits the [scope decision](2026-10-15-campaign-2-shared-frame-followup.md). Split retrofit: all 22 original headline declarations and their closure checked over b700659; scoped build, standard axioms and fresh replay pass. Wider charter gaps remain open; the full gate fails in inherited shared carries. |
| H2 Session index uniqueness | 77 terminal declarations: exact index operations and collision streams; normal lookup outcomes and reference effects; caller/confirmation/consumeData/peerRemove table safety; local owner coherence through lookup, allocation, index operations, releases, session start, confirmation, clearing, consumeData, expiry, all handshake consumers and both creators; session publication and allocation sequences. | `Leanux/Proofs/WG/Index/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; 421 checked theorems, projected claims and separate frames. All original 52 headlines and their closure are current. Scoped build, standard axioms and fresh kernel replay pass. Data ingress adds no reference-budget, readiness or alias restriction; its held references follow from actual acquisition. Response/cookie/initiation cleanup uses lookup-derived retained references, with no entry budget or readiness premise. Both creators preserve coherence under an explicit coherent-publisher premise, including an initially unhashed handshake owner. Handshake clearing and expiry retain arbitrary clocks, missing/NULL inputs and aliased slots under normal-return semantics. Session allocation/rotation conditions and final-peer-release detachment remain explicit caller obligations. Reachable whole-driver uniqueness/coherence and broader [shared frame carries](2026-10-15-campaign-2-shared-frame-followup.md) remain open. Exact lookup/release refusals and full Product observations are retained. The full gate fails in inherited CounterWindow.Refinement and ReplayWindow.Counterexamples. |
| H3 Endpoint roaming | 14 terminal declarations: remote endpoint semantics; actual decrypt/first-poll join; both authenticated handshake cuts retained through continuation failures; every original poll iteration's designated setter attempt and exact outcome audit; invalid-MAC1 whole-call Device preservation. | `Leanux/Proofs/WG/Roaming/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. 161 checked theorems. Invalid-MAC1 normal returns preserve the whole Device, retaining earlier clock failures and arbitrary message shapes; no Ambient rollback is claimed. Queue/callback AEAD provenance, later rejection paths, other callers and broader final endpoint preservation remain open. Inspection and attempted setter do not imply original-call success or completed mutation. Split retrofit: all 13 original headline declarations and their closure check over b700659, with standard axioms and fresh replay. Wider charter gaps remain open; the full gate lags elsewhere. |
| H4 Configuration semantics | 81 terminal declarations: leaves/flags/effective bounded readback; port/fwmark/key effects; removal, collision, REMOVE_ME and REPLACE_ALLOWEDIPS normal converses; post-free remove-all/REPLACE_PEERS phase order; root insertion/transfer and actual dumps; finite IPv4 suffix serialization, original two-chunk socket getter/drain/coalescing and actual scalar set/get composition including partial-error readback; mixed fwmark/peer-scalar JSON set/get and ordered PSK/Allowed-IP/keepalive selected-peer readback. | `Leanux/Proofs/WG/Config/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md), [finding/request 3](2026-10-14-campaign-2-mirror-requests.md#3-restore-pre-nest-tailroom-when-cancelling-the-device-peers-nest) | b700659 | In progress; projected claims and separate frames. Internal cancelled-nest room finding has no demonstrated output mismatch. Actual two-chunk getter has explicit singleton/no-endpoint/IPv4/capacity premises; scalar set/get adds stopped-device/reference premises; The new mixed fwmark/scalar normal-return claim retains reset failures and earlier mutations on later-peer -EINVAL; it concerns mirror JSON, with creatingNet and finite getter premises explicit. Mixed peer readback retains prior PSK/IP writes on normal ENOMEM/EINVAL, with stopped-device/empty-root/list and dump premises explicit. H4 has 590 checked theorems; combined scoped build, standard axioms and fresh replay pass. Global ownership, initial-to-post-free transport, queued cleanup/completion, general mixed attributes and pagination remain open. General insertion ownership awaits C1 AllowedIps/InsertionRouting and its represented-tree/list layer; no parallel copy is added. Split retrofit: all 79 original headlines and their closure check over b700659 with standard axioms and fresh replay. Ten explicit effect/refusal corrections retain original domains; two-chunk socket and scalar readback remain exact. Wider charter gaps remain open; The inherited full gate fails. |
| H5 Termination and progress | 42 terminal declarations: exact accepted runner boundaries and corrected historical backlog rejection; dispatch/resumption inspections; cut budget, flush decrease, modular-power adequacy, drain/poll bounds; index/jitter exact recorded outcomes and budgets; full Product bounded cookie activation, resumption and schedule outcome factors. | `Leanux/Proofs/WG/Progress/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [finding/request](2026-10-14-campaign-2-mirror-requests.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. All 42 headlines and their closure check over b700659 with standard axioms and fresh replay. Six explicit corrections retain original domains. Old cookie drain/totality claims are refuted on arbitrary malformed ring metadata; exact bounded factors retain actual errors and do not establish drain adequacy or reachability. Historical accepted backlog remains attributed to de62c9d; actual runner/audit reject it. Global progress, coherent-ring drain adequacy, whole-worker record decrease and fairness remain open. Native index/jitter claims exclude recordless mode; insertion assumes no owner residency or table uniqueness. Five further continuation/projection leaves check, with two more explicit ring-domain refutations. Five false historical count/totality supports are retired with checked refutations; the valid physical-transform projection is retained. Positive coherent-ring activation has an identified dependency on C1 Queues/RingGeometry and RingSteps; no parallel ring layer is copied. The inherited full gate fails. |
| H6 Timer discipline | 52 terminal declarations: complete local wheel-arm effects, recorded delays and caller compositions; selected wheel-unit/send pairs with inspection and conditional rearming; same-peer bound 19 and immediate give-up continuation; explicit stopped outcomes; exact first actual outer timer turn with the original suffix and an intermediate retransmit receipt. | `Leanux/Proofs/WG/TimerDiscipline/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md), [retrofit findings](2026-10-17-proof-campaign-2-timer-carry.md) | b700659 | In progress; 52 projected headlines and 445 total theorems check over the split mirror. Claims and frames stay separate. Scoped build, standard axioms and fresh kernel replay pass. Its entry conditions are actual initial record/wheel selection, retaining all callback/suffix failures and final checks. The receipt records the first callback effect before later turns and their exact outcome; it adds no callback-success premise. Retry-sequence scope remains supplied units; the bound excludes 20 successful same-peer pairs, not a twentieth callback. Empty-queue eligibility uses the actual inspection bit. Conditional rearm retains complete wheel effects and reference release. Complete caller coverage, whole scheduler episodes and session-relative counts remain open. Full gate fails in inherited CounterWindow.Refinement and ReplayWindow.Counterexamples. |

The gate for every row: `capped -- scripts/in-bundle scripts/proof-gate`
(the build, the axioms of every terminal statement, the forbidden tokens,
the imports and the default targets).

## Result table: claim, theorem, boundary, premises, counterexample, pin

What each result's statements establish and what must not be inferred from
them, per the [pre-release review](2026-10-14-pre-release-review.md) §4. The
landed result's pin is the register row above; the campaign rows are read
from `proofs/campaign` at `ffea367` (not landed; names and counts move with
the branch). "Theorem results" are the property statements; "infrastructure"
counts erasure, evolution, failure-prefix and observer-exactness lemmas
exported beside them; "witnesses" are checked counterexamples or boundary
instances. The split is by declaration name and is indicative.

| Result | Original claim (charter) | Exact theorems (names) | Event boundary | Substantive premises | Counterexample or blocker | Mirror pin |
| --- | --- | --- | --- | --- | --- | --- |
| ReplayWindow S1 (landed) | Every accepted execution has its exact acceptance history and no two events share a lifetime and a wire counter | `S1` | Validator acceptance events of a successful `executeTrace`, keyed by allocation lifetime and wire nonce; includes validator successes whose packets are later dropped | A successful runner execution (the placeholder parameter included); the exactly erased logged execution | None; the theorem is over the executable, not over all Linux executions | 6f1f84c (register row) |
| ReplayWindow S2 (landed) | `counterValidate` returns what receive.c's rule returns and leaves its replay state | `S2`, `S2_acceptance`, `S2_update` | Refinement from `counterValidate` to the Lean `CounterWindow.step` rule | An allocated keypair; a 128-word bitmap (established by reachable allocation) | None; "the C's rule" is a source identification of `step`, the refinement is within Lean | 6f1f84c |
| ReplayWindow S3 (landed) | Every non-receive syscall and every validator call leave every other keypair's window unchanged | `S3`, `S3_nonreceive`, `S3_validator`, `S3_surviving`, `S3_syscall`, `S3_syscall_ambient` | Surviving old cells under nonreceive calls; other keypairs under a validator call; whole-operation evolution including the ambient step | Lifetime-aware framing (a reused slot is a new identity) | None; the literal equality of every keypair store through allocation and deletion was never claimed | 6f1f84c |
| R1 anti-replay | No counter accepted twice under one lifetime; nothing at or below the floor accepted | `pure_uniqueness`, `mirror_uniqueness`, `runner_uniqueness`, `pure_run_floor`, `mirror_floor`, `mirror_run_floor`, `runner_floor`, `pure_run_below_floor` | The window model's runs and the mirror through S2 | As S1 and S2 | `inclusive_boundary_witness`: an unseen counter at exactly highest minus 8128 is accepted; the charter's "at or below" was false of the kernel's rule and corrected to "strictly below" | `ffea367` |
| R2 lifetime safety | The mirror never resolves a dead identity after its release | `keypair_no_resurrection`, `peer_create_fresh_identity`, `packet_*_free_prevents_later_lookup` and the access-safety family (list in `LifetimeSafety/Statements.lean`) | Operation endpoints and failure-retaining access prefixes per call family | Resident and allocation premises; callback premises; the environment's own domain | `stale_cursor_retargets_replacement`: an accepted replay releases a replacement peer through a stale dump cursor after device recreation, a mirror-domain finding (the guest forbids the composition; the matching refusal is the finding-6 fix on task/review-timer). Whole-run closure and saved-reference ownership open | `ffea367` |
| R3 cryptokey routing | Lookup agrees with the insert and remove history; delivery and transmit bound to the owning peer | `pureTree_lookup_correct`, `original_findNode_lookup_correct`, `original_insert_longest_prefix`, `original_add_all_cases`, `original_insert_all_cases` and the insertion family | Represented tries against an independently defined flat-prefix winner | Shape, address-bound, fresh-id and resident-target premises; bounded inputs | None yet; removal, configuration history and the packet-path halves open. A trie winner labelled with a raw peer slot is not yet identity authorization | `ffea367` |
| R4 delivery | Per peer, decrypted packets reach the stack in receive order under any recorded schedule; drops only at explicit arms | `two_carried_slots_*`, `original_enqueue_epipe`, `original_prev_*`, `original_poll_selected_callback_complete`, `original_poll_removal_ordinals`, the ring-journal family | Local queue and poll provenance, selected GRO order, callback entry | Callback entry is not delivery; local ordinals are not global identities; a finite run may end with pending obligations | The original chronological post-GRO order theorem was retired by an accepted replay (`r4-gro-reorder`: a held TCP segment delivered after later packets); normal-before-held is the proved order. Pipeline conservation open | `ffea367` |
| R5 key lifetime | No encrypt or decrypt under a keypair past the reject time or count; expired material zeroed | `original_decryption_admission`, `original_accepted_wire_nonce`, `original_staging_admissions`, `original_zero_timer_preserves_transport_keys`, `receive_guard`, `original_age_*`, `original_receive_attempt_*` | Admission to decryption, admission to staging, the timer's own effect | Admission clocks and counters as recorded; the environment admits worker latencies unbounded by virtual time | Three accepted replays refute the literal wording (a nonce past the limit authenticates before rejection; a queued keepalive encrypts after the recorded expiry; held material is used after a clear): the C's order, [reviewed as statement artefacts](2026-10-13-review-r5-counterexamples.md), no tray entry. "Resolved under Rule Zero" is not "key lifetime enforcement proved" in the charter's sense | `ffea367` |
| R6 flood resistance | Under load, an initiation without a valid cookie MAC never passes the cookie reply; retransmits stop at the limit | `original_invalid_mac2_cookie_only`, `original_invalid_mac2_noise_preserved`, `original_invalid_mac1_drop`, `original_under_load_queue`, `original_under_load_decay` | An actual load-phase execution and MAC predicates; the cookie suffix and Noise preservation on normal completion | `FailedMac2` with its prefix, clock and cookie execution premises | A 19-retry, 20-initiation episode corrects the literal `MAX_TIMER_HANDSHAKES = 18` wording; not itself the corrected universal bound. Not shown: that real load reaches the prefix, CPU or memory bounds, availability | `ffea367` |

| Result | Terminal declarations | Theorem results | Infrastructure | Witnesses |
| --- | --- | --- | --- | --- |
| ReplayWindow | 13 | 10 | 3 | 0 |
| AntiReplay | 9 | 8 | 0 | 1 |
| LifetimeSafety | 143 | 84 | 58 | 1 |
| CryptokeyRouting | 45 | 45 | 0 | 0 |
| DeliveryOrder | 48 | 36 | 8 | 4 |
| KeyLifetime | 13 | 10 | 3 | 0 |
| FloodResistance | 6 | 5 | 1 | 0 |

C memory safety, constant time, cryptographic security and the physical
erasure of secrets are separate claims that no row makes.

## Adding a result

1. Make a directory under the subject, `Leanux/Proofs/<Subject>/<Result>/`,
   with a `Statements.lean` that holds every terminal statement, each with a
   docstring saying in plain words what it claims. Material another result
   could use goes in a layer, not in the result.
2. Import the `Statements` module from `Leanux/Proofs.lean`; the gate fails
   until it does.
3. Run the gate. Add the row above with the charter, the review, the mirror
   commit the result holds over, and the status.
4. The mirror stays as it is. If the proof needs the mirror to be different,
   that is a finding, reported with the path and what the kernel does there.

## Lag and repair

A row names the mirror commit its result holds over. A mirror change may
land while the result lags: the integration record says so, the row's status
becomes "lagging since <commit>", and the repair is a follow-on task on the
proof tree, not a condition on the mirror change. Every claim point reports
the lag.

The tree was restructured from `Leanux/Spikes/` on 2026-10-13; the dated
documents above keep the historical names in their prose.
