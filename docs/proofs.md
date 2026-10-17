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
Subsequent H2 contracts add 144 theorems and thirty-six headlines;
H1 whole-call tag maps and actual session-clock provenance add forty-six
theorems and ten headlines; H4 setter/readback and pagination add ninety-nine
theorems and fourteen headlines; H3 rejection/cookie preservation adds thirty-three
theorems and five headlines; H5 recorded completion adds thirteen theorems and
three headlines; H6 actual timer receipts, retry blocks and session-arm events
add forty-five theorems and nine headlines. Current totals are 2,363 theorems
and 335 headlines in 793 owned modules. The initialized give-up runtime witness
adds one module and no theorem or headline.
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
| H1 Noise session state machine | 33 terminal declarations: state/slot edges; ordered clear/rotation effects and static release budgets; full normal session effects and total recorded success under static post-allocation release readiness; consecutive first-match confirmation; total original initiation creation with exact message/device/record suffix and mode preservation; whole-response entry CREATED_INITIATION to final CONSUMED_RESPONSE; actual derivation-clock receipt through session rotation and publication. | `Leanux/Proofs/WG/Noise/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; 235 checked theorems, projected claims and separate frames. Whole-response entry provenance derives both tags from the actual successful call without coherence/readiness premises. Both whole consumers now preserve every optional peer tag on normal refusal and change only the returned peer on success, deriving held cleanup references without entry budgets or alias premises. Response success derives the prior created-initiation tag; initiation imposes no prior tag. Both creators now also preserve every tag on normal refusal and change only their requested peer on success; response creation derives its prior consumed-initiation tag. Whole beginSession now preserves all tags on normal false, and on true zeroes only its peer while deriving its required old response tag. Whole handshakeClear and expiry zero only the requested peer, with actual missing/NULL/clock/alias failures retained. The seven contracts now compose into an actual finite mixed native history, with exact operation order, whole projected boundary links and all-peer effects. Observer erasure retains complete original returns, concrete WG/Ambient state and the first Stop; no partial history returns after failure. This is tag discipline for supplied native calls, not Device rollback, driver scheduling or lifetime confirmation. The session receipt derives the actual birthdate from normal whole-call execution; false returns retain their actual prefix, and aliases may erase the allocated key. A checked direct-helper sequence confirms the same resident responder key twice around reinstallation, preserving its entire key, serial, allocation counter and cursor. This is an arbitrary helper-domain counterexample, without initialized or fresh-allocation provenance. Confirmation across fresh reinstallation remains open; the consecutive-call theorem is not once-per-allocation-lifetime uniqueness. Broader driver closure is separate from the checked seven-operation native histories, and unconditional whole-call totality is not an extra requirement. Session-success premises allow allocation-ID aliases and do not establish final key coherence or reachability. Three standalone restart variants checked; further transport awaits the [scope decision](2026-10-15-campaign-2-shared-frame-followup.md). Split retrofit: all 22 original headline declarations and their closure checked over b700659; scoped build, standard axioms and fresh replay pass. Wider charter gaps remain open; the full gate fails in inherited shared carries. |
| H2 Session index uniqueness | 89 terminal declarations: exact index operations and collision streams; normal lookup outcomes and reference effects; caller/confirmation/consumeData/peerRemove table safety; local owner coherence through lookup, allocation, index operations, releases, session start, confirmation, clearing, consumeData, expiry, all handshake consumers, both creators and peer initialization; session publication and allocation sequences. | `Leanux/Proofs/WG/Index/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; A checked whole persistent-keepalive callback refutes sole local hashed-owner preservation on arbitrary states with mismatched current-key/caller ownership: it acquires one peer and releases another final reference, leaving a hashed owner dangling. The explicit real-clock witness is not initialized reachability or a mirror/kernel discrepancy; see the [finding](2026-10-17-proof-campaign-2-persistent-owner.md). 481 checked theorems, projected claims and separate frames. All original 52 headlines and their closure are current. Scoped build, standard axioms and fresh kernel replay pass. Data ingress adds no reference-budget, readiness or alias restriction; its held references follow from actual acquisition. Response/cookie/initiation cleanup uses lookup-derived retained references, with no entry budget or readiness premise. Both creators preserve coherence under an explicit coherent-publisher premise, including an initially unhashed handshake owner. Actual peer creation supplies that premise even on cursor overwrite, without asserting intermediate coherence or reference ownership. The complete quiet-removal counterexample shows that sole local owner coherence lacks a lifecycle detachment/slot relation; no reachable-state defect is asserted. Its positive whole-call counterpart assumes empty key slots and worker queues plus entry detachment only on a last reference; it retains actual refusal paths. A further whole-call contract allows live/aliased key slots under original-slot coverage at a last peer reference; actual clearing derives detachment without a static reference budget. The further arbitrary-list contract drops allowed-IP emptiness using a pointwise masked-peer frame; empty send/clear queues remain explicit. The actual zero-key worker derives final-release detachment under entry slot coverage without queue/list/readiness premises. Actual clear-work dispatch derives its named/head peer and membership; only that selected peer owes entry coverage and positivity. Both modes of original handshake queueing now preserve owner coherence with no additional entry premise, using the actual queue-inspection effect and acquisition-derived references; this does not assert queue consistency or worker completion. Original new-handshake and zero-key callbacks also preserve local coherence under the same sole entry invariant; actual acquisition derives the compensating put's non-final reference, and the zero-key callback only queues the later clear worker. Two named helper variants reuse owned exact effects, with acquisition classified in Source rather than Frames. The actual retransmission callback now preserves owner coherence through both retry and give-up, using the exact all-mode timer effect and staged purge, without pending/readiness/wheel-consistency assumptions. Three bounded variants cover timer deletion, purge and guarded modification; the hidden/arm/wheel implementation layer is reused, not copied. Handshake clearing and expiry retain arbitrary clocks, missing/NULL inputs and aliased slots under normal-return semantics. Session allocation/rotation conditions and final-peer-release detachment remain explicit caller obligations. Reachable whole-driver uniqueness/coherence and broader [shared frame carries](2026-10-15-campaign-2-shared-frame-followup.md) remain open. Exact lookup/release refusals and full Product observations are retained. The full gate fails in inherited CounterWindow.Refinement and ReplayWindow.Counterexamples. |
| H3 Endpoint roaming | 18 terminal declarations: remote endpoint semantics; actual decrypt/first-poll join; both authenticated handshake cuts retained through continuation failures; every original poll iteration's designated setter attempt and exact outcome audit; invalid-MAC1 whole-call Device preservation and rate-limit refusal peer-map preservation. | `Leanux/Proofs/WG/Roaming/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. 190 checked theorems. Invalid-MAC1 normal returns preserve the whole Device, retaining earlier clock failures and arbitrary message shapes; no Ambient rollback is claimed. An actual rate-limit refusal preserves the final peer map and endpoints while allowing cookie-secret/load/rate-limit changes; noCookie alone carries no preservation conclusion. Same-entry receipts now connect MAC-admitted response- and initiation-consumer rejection to endpoint preservation at whole-call return; held references come from actual lookup, and observation erasure retains all errors. The actual type-3 cookie-message branch now preserves every remote endpoint on normal return, including successful cookie writes and lookup/decryption refusals, with only the type premise. Its native frame retains the full optional Endpoint map, and no shared cookie-reply/socket layer is copied. Queue/callback AEAD provenance, later rejection paths, other callers and broader final endpoint preservation remain open. Inspection and attempted setter do not imply original-call success or completed mutation. Split retrofit: all 13 original headline declarations and their closure check over b700659, with standard axioms and fresh replay. Wider charter gaps remain open; the full gate lags elsewhere. |
| H4 Configuration semantics | 93 terminal declarations: leaves/flags/effective bounded readback; port/fwmark/key effects; removal, collision, REMOVE_ME and REPLACE_ALLOWEDIPS normal converses; post-free remove-all/REPLACE_PEERS phase order; root insertion/transfer and actual dumps; finite IPv4 suffix serialization, original two-chunk socket getter/drain/coalescing and actual scalar set/get composition including partial-error readback; mixed fwmark/peer-scalar JSON set/get, ordered PSK/Allowed-IP/keepalive selected-peer readback, mixed port-refusal effects with actual bounded getter, actual private-key update/getter composition, complete finite single-peer IPv4 pagination, and actual mixed/key setter paginated readback. | `Leanux/Proofs/WG/Config/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md), [finding/request 3](2026-10-14-campaign-2-mirror-requests.md#3-restore-pre-nest-tailroom-when-cancelling-the-device-peers-nest) | b700659 | In progress; projected claims and separate frames. Internal cancelled-nest room finding has no demonstrated output mismatch. Actual two-chunk getter has explicit singleton/no-endpoint/IPv4/capacity premises; scalar set/get adds stopped-device/reference premises; The new mixed fwmark/scalar normal-return claim retains reset failures and earlier mutations on later-peer -EINVAL; it concerns mirror JSON, with creatingNet and finite getter premises explicit. Mixed peer readback retains prior PSK/IP writes on normal ENOMEM/EINVAL, with stopped-device/empty-root/list and dump premises explicit. The running-device mixed port collision retains earlier mark/generation/cache writes and bypasses arbitrary later key/replacement/peer attributes; its singleton getter exposes the retained prefix without reset-readiness or reference bounds. Private-key-only readback derives actual expiry time and effective/clamped identity under established-identity/no-collision/singleton dump premises, allowing running state, staged packets and key aliases. The whole actual getter now composes empty, fitting and arbitrarily many IPv4 pages within the exact 4096-envelope bound, including separate DONE. It preserves every occurrence, the whole Device and the final socket; singleton/no-endpoint/readable-node/header-room/idle-empty-socket and canonical-boundary freshness premises remain explicit. No callback/receive-success or global ownership premise is supplied. Mixed fwmark/scalar and private-key set/get now use that finite getter, deriving every post-set input from the same actual run; key capacities use the effective post-install identity. Existing setter domains and partial-error mutations remain. The fitting multi-peer getter now proves actual production, queued DATA/DONE receipt and exact coalescing for an arbitrary finite resident peer list with empty allowed-IP lists. It preserves duplicate visits and arbitrary endpoint fields under the explicit whole-envelope capacity and idle/empty-selector premises, retaining the whole Device and exact final socket. The scalar setter now composes with that actual multi-peer getter, deriving all getter inputs from its exact updated Device and preserving earlier scalar writes before later -EINVAL. Listed occurrences show the selected update; an unlisted target is changed only in the Device. This total composition retains the existing stopped-device/reference domain and makes no fwmark claim. The mixed fwmark/scalar setter also composes for arbitrary finite lists, including duplicate clear/dump visits and unlisted selected targets. Its normal-return claim retains reset Stops; outside-peer fields and JSON/socket are exact, while peer reset timestamps are existential pointwise effects rather than a per-visit transcript. The endpoint-aware whole getter extends finite single-peer IPv4 pagination to arbitrary endpoint fields using their actual first-page space, updated first boundary and unchanged resumed induction. It preserves exact Device/socket state and original getter JSON, including serializer family mapping and field truncation; raw endpoint values and malformed-family reachability are not claimed. No-endpoint capacity/freshness/count compatibility is checked and old signatures remain unchanged. Actual mixed fwmark/scalar and private-key set/get now compose with endpoint-aware pagination from the same setter successor. Explicit socket/selector frames and equal serialized prefix sizes derive all getter inputs. Mixed source/cache clearing and later -EINVAL prefix writes are retained; key capacities use the effective installed identity. Old no-endpoint claims remain unchanged, with no readiness or callback-success premise added. H4 has 702 checked theorems; combined scoped build, standard axioms and fresh replay pass. Six standalone mixed-width source facts now derive exact weighted serialization, complete/split scans and the actual first callback split, including an empty emitted prefix. They preserve actual arbitrary-width masking and require only read-node residency; full mixed-family transport remains open. Weighted finite plans now preserve exact occurrence order and give nonempty fitting resumed pages; an actual resumed callback derives its maximal weighted page under all-prior cursor freshness. A generic JSON coalescer preserves arbitrary finite page contents. No full weighted getter or automatic freshness claim is made. Actual first DATA and netlinkDumpStart now cover empty input, complete pages and an empty first emitted prefix of nonempty input. The exact start socket retains inline/separate DONE under header and conditional nest bounds; full receive composition remains open. Global ownership, initial-to-post-free transport, queued cleanup/completion, general mixed setters and multi-peer/IPv6 pagination remain open. General insertion ownership awaits C1 AllowedIps/InsertionRouting and its represented-tree/list layer; no parallel copy is added. Split retrofit: all 79 original headlines and their closure check over b700659 with standard axioms and fresh replay. Ten explicit effect/refusal corrections retain original domains; two-chunk socket and scalar readback remain exact. Wider charter gaps remain open; The inherited full gate fails. |
| H5 Termination and progress | 48 terminal declarations: exact accepted runner boundaries and corrected historical backlog rejection; dispatch/resumption inspections; cut budget, flush decrease, modular-power adequacy, drain/poll bounds; index/jitter exact recorded outcomes and budgets; full Product bounded cookie activation, resumption and schedule outcome factors; actual recorded afterBatch completion guards at return. | `Leanux/Proofs/WG/Progress/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [finding/request](2026-10-14-campaign-2-mirror-requests.md), [report](2026-10-14-proof-campaign-2.md) | b700659 | In progress; projected claims and separate frames. All 42 original headlines and their closure check over b700659 with standard axioms and fresh replay. 318 checked theorems. Recorded afterBatch establishes its five queue-empty tests, zero handshake counter and NAPI guard at normal return; physical-ring adequacy, pendingWork and recordless execution are not asserted. Six explicit corrections retain original domains. Old cookie drain/totality claims are refuted on arbitrary malformed ring metadata; exact bounded factors retain actual errors and do not establish drain adequacy or reachability. Historical accepted backlog remains attributed to de62c9d; actual runner/audit reject it. Global progress, coherent-ring drain adequacy, whole-worker record decrease and fairness remain open. True normal runTimers return now derives exactly its four final queue tests and Device presence, without physical-occupancy/no-due/pendingWork conclusions. The separate original recorded idleTimers caller now stores its actual end read and establishes nextDue = none at that read, allowing Device absence and preserving all Stops. This wheel test assumes no hidden readiness, but does not prove peer-list/store or wheel/expiry coherence, recordless behavior or global work emptiness; afterAdvance now has its own actual-bound receipt and unconditional whole-call erasure. Recorded normal return stores the end read and checks NoTimerDue at the original wrapped conditional pass, possibly the earlier bound. Native source provenance derives the actual fixture/peek reads without projection expansion; no preceding-advance execution or totality is asserted. A further actual wg_advance syscall receipt now ties modular advance bounds to its own wait receipt when present, with unconditional exact erasure and a source link through the real runner strip/guards. Descriptor/task-work Stops remain; no recorded-entry mode preservation is assumed. Normal original runSendWorkers return now implies absent Device or an empty final send queue in either record mode. Its exact loop factor retains final delivery, scheduler calls and budget errors; no successful drain, pendingWork consistency or whole-operation emptiness is asserted. Mathematical termination is supplied by total definitions; derived-fuel adequacy and initialized runnable-work completion remain genuine gaps. Native index/jitter claims exclude recordless mode; insertion assumes no owner residency or table uniqueness. Five further continuation/projection leaves check, with two more explicit ring-domain refutations. Five false historical count/totality supports are retired with checked refutations; the valid physical-transform projection is retained. Positive coherent-ring activation has an identified dependency on C1 Queues/RingGeometry and RingSteps; no parallel ring layer is copied. The inherited full gate fails. |
| H6 Timer discipline | 59 terminal declarations: complete local wheel-arm effects, recorded delays and caller compositions; selected wheel-unit/send pairs with inspection and conditional rearming; same-peer bound 19 and immediate give-up continuation; explicit stopped outcomes; exact first-turn and complete actual timer-loop receipts with original reset/finish and immediate retransmit effects; actual adjacent dispatch/send certificates and contiguous same-peer retry-block counts. | `Leanux/Proofs/WG/TimerDiscipline/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md), [retrofit findings](2026-10-17-proof-campaign-2-timer-carry.md) | b700659 | In progress; 59 projected headlines and 483 total theorems check over the split mirror. Claims and frames stay separate. Scoped build, standard axioms and fresh kernel replay pass. Its entry conditions are actual initial record/wheel selection, retaining all callback/suffix failures and final checks. The receipt records the first callback effect before later turns and their exact outcome; it adds no callback-success premise. The earlier retry-sequence contract concerns supplied units; the new block theorem derives certificates from actual consecutive episode runs, using the projected chain only for continuity. Its exact attempt growth and bound 19 hold at the last send exit of a qualifying nonempty same-peer block, not after later turns or final delivery. Empty-queue eligibility uses the actual inspection bit. Conditional rearm retains complete wheel effects and reference release. The complete finite-loop observer retains every executed turn, actual current-wheel selection and exact original reset/finish/errors, without a supplied unit list. It does not prove fuel adequacy, no-due completion or that arbitrary histories form such blocks. A complete-WG local fixture also checks give-up arming with an unchanged empty key store/slots and allocation counter zero; Ambient stays arbitrary except unrecorded timer-arm mode. This is no reachable-history counterexample. Both full response observers now retain exact allocation-labelled session-arm events: hook presence follows actual beginSession, the running guard determines exact all-mode WG effects, and physical enqueue changes by zero or one. These facts hold at the hook cut and imply neither final key residency nor later expiry preservation. The outgoing observer now anchors the reached pre-session counter to the actual whole-call entry, so an allocation event has entry serial plus one at its hook cut. Two explicitly named shared-frame variants support this prefix; the larger complete-call frame layer is inventoried rather than copied. An [initialized generated history](2026-10-17-proof-campaign-2-initialized-giveup.md) is accepted by the actual runner with nineteen retries then give-up cleanup, no observed keypair allocation/session decision, and empty keys/slots at all 23 boundaries. This recorded-arm runtime evidence adds no theorem and corrects counting all zero-key arms solely by completed sessions; it is not a Linux capture or a kernel-proved closed trace. Final-call counter preservation, cross-call serial uniqueness, complete caller coverage, general mixed histories and session-relative counts remain open. Full gate fails in inherited CounterWindow.Refinement and ReplayWindow.Counterexamples. |

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
