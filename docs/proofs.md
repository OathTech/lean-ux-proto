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

Campaign 2 incorporates state-split mirror `b700659`; its earlier rows below
remain historical and lagging during the retrofit. The
[retrofit report](2026-10-16-proof-campaign-2-state-split.md) records baseline
counts, carries, deletions and validation. This branch retains the proof
target and gate removed from main pending campaign 1's landing.
The support tranches check 1,542 theorems (1,090 retyped/generalized, seventy-eight corrected statements,
216 retained, 158 support/finding declarations), and delete twenty-two type-given
frames. H1, H2 and H3 terminal modules now check over the split mirror;
H4, H5, H6 terminal closures and the full gate remain lagging. The [cookie-bound finding](2026-10-17-proof-campaign-2-cookie-bound.md)
refutes the old unrestricted activation prediction on malformed ring metadata.
A second checked witness shows that initial logical cookie membership need not
classify the packet exposed by the next physical consume.
The [missing-clock finding](2026-10-17-proof-campaign-2-missing-clock.md)
refutes the old absent-give-up totality on its original input domain. The corrected
give-up contract factors its exact actual arm tail, including errors.
All 52 H2 terminal declarations and their full Product sequence observations
check; all 258 original audit names remain
in their Statements files.
The [H6 retrofit finding](2026-10-17-proof-campaign-2-timer-carry.md) is a
checked counterexample to the legacy timer-deletion statement after wheel state
was added. Projected arming and deletion contracts now describe the complete
current wheel effects; guarded arming and session-derived effects also account
for all wheel changes. Traversal, data-receipt and handshake-completion effects
are corrected too; all seven identified contracts are carried. Their downstream
configuration timer cleanup and recorded-site source effects are also corrected;
jitter and initiation-send arming effects are corrected too. Remaining timer
and worker consumers are pending.
The [H2 peer-release finding](2026-10-17-proof-campaign-2-peer-release.md)
checks two stopped outcomes within the old totality domain. The corrected
peer-release contract now classifies the exact queue/timer refusal or successful
Device effect under the same premises. Both affected H2 headlines now use checked
projected outcome companions; the full terminal module and downstream totality users remain pending;
no reachability claim is made.
The [H4 queued-handshake finding](2026-10-17-proof-campaign-2-queued-handshake.md)
checks a stale pending-peer prediction after the queue-record change in
`1f0fbeb`; all five queued-send source contracts now carry the actual inspection
result, with exact erasure equalities. Retry and absent/invalid-key staged
callers now carry the actual observation too; remaining installation/staged-send
contracts and terminal wrappers remain pending.
The [H5 backlog carry](2026-10-17-proof-campaign-2-backlog-carry.md) proves
the old accepted fixture now receives the exact pending-work rejection from
the actual runner. General boundary and legacy backlog wrappers remain pending.
The [H4 removal finding](2026-10-17-proof-campaign-2-removal-carry.md)
refutes the old quiet/live totality domain using a scheduled NAPI poll and
the actual crypt-work Stop. Its source factor is corrected; broader removal
contracts remain pending with their original domains.


| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | 6f1f84c | lagging since 247beec (review item 8 landed 2026-10-13: the two counter-limit tests now carry operands and `CounterWindow/Refinement.lean`'s `counterValidate_execution` expects plain records; the proof campaign repairs it on merge; the index-table entry's `Option PeerId` and `indexLookup`'s store-back, landed 2026-10-14, touch `indexLookup_sameSnapshot` and the `consumeResponse`, `cookieMessageConsume` and `consumeData` frames, repaired on the same merge). Carried from ef7c535 over the epoll landing on 2026-10-13 (the wait-queue, epoll release and epoll system-call frames). |

Campaign 2's working-branch checkpoints (not complete results):

| Result | Checked local surface | Directory | Charter/report | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- |
| H1 Noise session state machine | 22 terminal declarations: state/slot edges; ordered clear/rotation effects and static release budgets; full normal session effects and total recorded success under static post-allocation release readiness; consecutive first-match confirmation; total original initiation creation with exact message/device/record suffix and mode preservation. | `Leanux/Proofs/WG/Noise/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. Remaining whole-call edges/totality, exact derivation-clock provenance and allocation-lifetime confirmation open. Session-success premises allow allocation-ID aliases and do not establish final key coherence or reachability. Three standalone restart variants checked; further transport awaits the [scope decision](2026-10-15-campaign-2-shared-frame-followup.md). Split retrofit: all 22 headline declarations and their closure checked over b700659; scoped build, standard axioms and fresh replay pass. Wider charter gaps remain open; the full gate remains lagging in other result/shared carries. |
| H2 Session index uniqueness | 52 terminal declarations: exact index operations/collision streams; all normal lookup outcomes and owner/reference effects; original caller table safety; successful session publication coherence, store bounds and consecutive allocation IDs. | `Leanux/Proofs/WG/Index/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. Reachable hashed uniqueness and owner/peer-word residency through all driver entries open. Outer-removal and [nine-family ingress carries](2026-10-15-campaign-2-shared-frame-followup.md) await scope decisions. Split retrofit: all 52 headlines and their closure check over b700659, with standard axioms and fresh replay. Exact peer-release refusals and the current wheel-unit dispatch scope are explicit corrections. Full Product session observations are restored after review. Wider charter gaps remain open; the full gate lags in other result/shared carries. |
| H3 Endpoint roaming | 13 terminal declarations: remote endpoint semantics; actual decrypt/first-poll join; both authenticated handshake cuts retained through continuation failures; every original poll iteration's designated setter attempt and exact outcome audit. | `Leanux/Proofs/WG/Roaming/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. Queue/callback AEAD provenance, other callers and final endpoint preservation open. Inspection and attempted setter do not imply original-call success or completed mutation. Split retrofit: all 13 headline declarations and their closure check over b700659, with standard axioms and fresh replay. Wider charter gaps remain open; the full gate lags elsewhere. |
| H4 Configuration semantics | 79 terminal declarations: leaves/flags/effective bounded readback; port/fwmark/key effects; removal, collision, REMOVE_ME and REPLACE_ALLOWEDIPS normal converses; post-free remove-all/REPLACE_PEERS phase order; root insertion/transfer and actual dumps; finite IPv4 suffix serialization, original two-chunk socket getter/drain/coalescing and actual scalar set/get composition including partial-error readback. | `Leanux/Proofs/WG/Config/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md), [finding/request 3](2026-10-14-campaign-2-mirror-requests.md#3-restore-pre-nest-tailroom-when-cancelling-the-device-peers-nest) | de62c9d | In progress; projected claims and separate frames. Internal cancelled-nest room finding has no demonstrated output mismatch. Actual two-chunk getter has explicit singleton/no-endpoint/IPv4/capacity premises; scalar set/get adds stopped-device/reference premises; global ownership, initial-to-post-free transport, queued cleanup/completion, mixed attributes and general pagination remain open. Lagging main cb2348e; checked over de62c9d. Scoped build/standard axioms/fresh replay pass; full gate fails in inherited campaign-1 counter/index carries. |
| H5 Termination and progress | 42 terminal declarations: exact accepted runner boundaries and historical backlog at the actual final boundary; dispatch/resumption inspections; cut budget, flush decrease, modular-power adequacy, drain/poll bounds; original index insertion and both jitter sites: exact outcomes and adequate budgets for arbitrary finite supplied records. Separate executable nested-refill prefix evidence. Exact cookie-only empty-index activation outcomes, singleton scheduled resumption and full original schedule completion from bounded supplied reschedule/stop records. | `Leanux/Proofs/WG/Progress/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [finding/request](2026-10-14-campaign-2-mirror-requests.md), [report](2026-10-14-proof-campaign-2.md) | de62c9d | In progress; projected claims and separate frames. Full receive-schedule claim has an explicit contiguous record stream and yield count bounded by queue length; other queues remain unchanged. It establishes neither global quiescence nor fairness; queue classification and counter scope remain explicit. Historical backlog finding complete over de62c9d, not captured Linux. Main's completion guard addresses request 1; exact corrected refusal checks over b700659 in BatchBacklogAcceptance, and the general runner audit and corrected rejection wrappers also check. The old accepted-backlog claim is historical. Nested refill is executable-prefix evidence only. General whole-worker record decrease, detached-activation and global progress open. Index/jitter claims exclude recordless mode; insertion imposes no owner-residency/table-uniqueness premise. Lagging main cb2348e; checked over de62c9d. Scoped build/standard axioms/fresh replay pass; full gate fails in inherited campaign-1 counter/index carries. |
| H6 Timer discipline | 50 terminal declarations: seven local arm sites/recorded delays; original retry/send pairs, same-peer bound 19 and immediate give-up; total pending-zero-key and recorded absent-zero-key give-up; incoming/outgoing session and traversal/data caller hook compositions. Total recorded retransmit hook with exact arm/skip effects. Total original initiation send through recorded retransmit rearm under explicit static no-endpoint/invalid-cookie/zero-keepalive readiness. Total named retry timer dispatch with exact callback, section and queue effects from static record/state guards; total named send-worker dispatch through send/rearm and retained reference release. | `Leanux/Proofs/WG/TimerDiscipline/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | de62c9d | In progress; projected claims and separate frames. Guards qualify arm events. Complete caller coverage, scheduler retry episodes and session-relative counts open; the bound excludes 20 successful pairs, not a twentieth callback. Lagging main cb2348e; checked over de62c9d. Scoped build/standard axioms/fresh replay pass; full gate fails in inherited campaign-1 counter/index carries. |

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
