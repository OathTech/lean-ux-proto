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

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

## Results

| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | 6f1f84c | lagging since 247beec (review item 8 landed 2026-10-13: the two counter-limit tests now carry operands and `CounterWindow/Refinement.lean`'s `counterValidate_execution` expects plain records; the proof campaign repairs it on merge; the index-table entry's `Option PeerId` and `indexLookup`'s store-back, landed 2026-10-14, touch `indexLookup_sameSnapshot` and the `consumeResponse`, `cookieMessageConsume` and `consumeData` frames, repaired on the same merge; the representation batch of 2026-10-15 (the handshake queue as a `PtrRing`, the flood run exactly over `Env.batch` with `floodExact` deleted, the ratelimiter's entry site and two-table uninit, the batch completion guard) touches the flood frames in `Logged/Operations.lean`, `Keypairs/Frames/Env.lean`, `Frames/Kernel.lean`, `Evolution/Operations.lean`, `WGMore.lean:460`, the fuel copies in `Logged/Workers.lean:107-109` and the ring frames in `Logged/{Scheduler,Workers}.lean`, repaired by the campaigns on merge with the `floodExact` parameter removed from their statements). Carried from ef7c535 over the epoll landing on 2026-10-13 (the wait-queue, epoll release and epoll system-call frames). |

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


## Binary adequacy (standalone charter target)

The user-opened [binary charter](2026-10-15-charter-binary-adequacy.md)
authorizes `binary/` separately from the mirror proof tree. Its current
[report](2026-10-15-binary-adequacy.md#milestone-1-function-theorem-and-review-handoff)
quotes the trust base and distinguishes proof acceptance from kernel-entry
realism and physical frame premises.

| Function | Headline theorem / transport | Decoded regions | Named service contracts | Mirror pin | Status |
| --- | --- | --- | --- | --- | --- |
| `wg_index_hashtable_lookup`, including `wg_peer_get_maybe_zero` | `Binary.LookupRelation.lookup_simulation`, `lookup_transport`, `lookup_framed_transport` | 54 (23 lookup, 31 helper) | `TracePcContract`, `TraceCmp4Contract`, `TraceConstCmp4Contract`, `TraceConstCmp1Contract`, `BhEnableContract` | `cb2348e` | Function and bucket-loop composition proved; original ABI return, all accepted helper paths, result and cut frames. Independent review: go with named fixes; F1/F3/F4/F5/F8/F10/F11 implemented for recheck at M2. External export gate PASS at 430ea90 only; updated surface awaits M2 export gate. |

| Allowed-IPs `lookup` and `common_bits`, both families | In progress; no function theorem claimed | 56 (35 lookup, 21 common_bits), plus existing peer-get | Under construction; additional variable cmp1/cmp8 callbacks reached | `cb2348e` | Paused for replanning (2026-10-16). Both-family Pre witnesses execute to RET; complete entry/common_bits/peer-get/return-tail components checked with union cut frames. Bounded loop and function correspondence/transport remain open; recovery record is in the single adequacy report. M2 review will recheck M1 fixes. |

On the separate `task/binary-proof-refactor` branch, the
[sequential sibling experiment](2026-10-16-goal-binary-proof-refactoring.md#sibling-sequential-experiment-result)
adds `Binary.Sequential.lookup_simulation` for the same full index lookup.
It keeps Pre and the image fixed, but exports endpoint effects under
sequential Kraken execution, without internal correspondence or M1's
permission audit. This is an experiment in proof cost, not additional
campaign function coverage or M2 completion; M1 remains available unchanged.

The separate `task/binary-pair-runner` sibling has the following experimental results:

| Result | Headline | Mirror pin | Status |
| --- | --- | --- | --- |
| Executable trie reconstruction and sequential allowed-IPs call | `Binary.Pair.Trie.lookup_checked` (`PairCallAdequacy.lean`); `findNode_checked` and positive `CallWitness.check4` / `check6` / `accepted` | `cb2348e` | Nonempty loop boundary to selected-node exit, both families, preserving the tested reconstruction. Setup and initial invariant now derived from the executable assertion; one interpretation from Names. Reuses existing physical regions and explicit callback/decoder contracts. Concrete headers pass in Lean; both paired suites and fresh kernel replay pass. The earlier boundary result alone did not establish function adequacy. Standard axioms; user external export gate accepted at `a33869e` on 2026-10-17 (`PairBoundaryProof`, `PairBoundaryWitness`). The stack generalization and flag-independence lemma pass fresh local replay; their external gate is pending. Actual captured IPv4/IPv6 entry/header/return tests pass with two seeds and five controls per family. The next increment composes `lookup_checked` from checked entry to return: empty roots, misses and accepted live hits, exact trie/count reconstruction, ABI/callback state and physical frame. Standard axioms; concrete entry and source-acceptance witnesses execute to return. Fresh replay passed; external gate pending. Fresh index-removal calibration adds 54 executed calls, a stale-predecessor counterexample, and three proved instructions in two physical regions; `PairRemoveOwnership.clear_ownership` proves the tested owner-flag update. Full bucket unlink/removal adequacy remains open. This is a sequential sibling, with dying-peer retry explicitly refused by the source; it does not advance the concurrent campaign coverage. [Increment](2026-10-18-plan-paired-call-increment.md). Lags main `77c9b55`. [Report](2026-10-16-plan-executable-binary-correspondence.md#executable-boundary-to-physical-loop-2026-10-17). |

| Paired index-subsystem increment | `Remove.remove_checked`, `Remove.remove_simulation`, `Replace.replace_checked`, `Replace.replace_simulation`, `IndexLookup.lookup_checked`, `IndexLookup.lookup_simulation`, `Sequence.sequence_checked` | `cb2348e` | Complete locally: 25-instruction removal and 41-instruction replacement from tested executable assertions, exporting ABI/callback readiness, reconstruction, owner flags and write frames. Concrete linked/unhashed Pre witnesses and execution theorems check for both; their exact states execute to return, including repeat calls and saturation. 54 paired removal calls, 24 replacement calls and selected-prefix three-way comparisons pass, including collision chains. Lookup now derives the old physical premises from the common executable check and reestablishes all reconstruction/owner flags; 96 paired calls across two recordings pass. Arbitrary finite composition now checks from one executable initial resource check, with explicit caller setup and actual per-call histories. Eight ten-call retained-heap sequences and fresh headline replay pass. Actual removal/replacement captures pass under two seeds, with all captured bytes/registers/PCs and corruption controls. Full-closure fresh replay and the binary trust gate pass; the external export gate passed on 2026-10-18 at `fe596fd0`, root `PairSubsystemSurface` with its full closure, using only the three standard axioms. No new campaign function coverage. Standard axioms; local replay status and cost in the [increment report](2026-10-18-paired-index-subsystem.md). |
| Paired input-driven insertion increment (review fixes validated; final capture and external gate pending) | `Insert.insert_checked`, `insert_simulation`, `InsertSequence.sequence_checked`, `Witness.check`, `Witness.executes`; `RandomService.return_recorded` | `cb2348e` | Full insertion and arbitrary finite mixed composition build with standard axioms, including reinsertion and arbitrary source-accepted retries. Every next Pre follows from the retained heap/provider state; each return exports reconstruction and exact remaining input. Concrete linked/unlinked formal witnesses execute the actual initialized provider and insertion to return. Thirty-two mixed sequences pass (416 calls, 434,064 instructions), including dead peers, preempt wraparound and coverage saturation; the latter exposed and repaired a missing dropped-counter resource. The corrected full capture replay (33,626,368 bytes per seed), fresh full-closure kernel replay and binary trust gate pass; the external export is prepared from `b3d57f17`, root `PairInsertionSurface`, and awaits acceptance. Fresh checkpoint review found a private-role alias that invalidated the old random-service domain, and unchecked capture identities. Both are repaired and independently reviewed: the typed-role assertion rejects the counterexample, valid covers remain accepted, and replay checks identities. Revised builds, trust gate, fresh kernel replay, provider suite, formal witnesses and mixed sequences pass; the corrected full capture and replacement export remain pending. Universal service hypotheses remain unproved. Explicit sequential environment, permission and unproved service/coupling hypotheses remain; no concurrent campaign or external-gate claim. [Review](2026-10-18-review-paired-index-insertion.md). [Charter](2026-10-18-charter-paired-index-insertion.md), [report](2026-10-18-paired-index-insertion.md). |

The concrete frame instance `lookup_snapshot_transport` carries exact
frontier and source-live lifetime/replay fields through lookup, conditional
on their initial representation and untouched-byte separation. It does not
prove physical allocation membership/absence or whole-trace S1–S3/R1–R6/H1–H6.
Those results need their remaining anchors and the milestone-4 entry-realism
check. The mirror proof register's existing lag is unchanged by this work.
