# Campaign 3: T2 forward conservation review

Review of parent `15a3f2e8`, 2026-10-19. Read-only inspection of the native
transmit paths, shared Driver/final journal, staged availability and disposal
proofs, and the resident TX coverage/service interfaces. No mirror defect or
initialized counterexample was established. The remaining work is a forward
conservation proof; the current attribution and injectivity results do not
supply it. No builds were needed for this source review.

## 1. High: staged disappearance has no terminal record in the shared history

`StagedAvailability.lean:90` quantifies over queues which still exist. Its
`Batch.drop` at line 78 deliberately retains only the suffix, and `Available`
at line 14 excludes previous allocation, not previous disposal. This is useful
for allocation injectivity but cannot account for a birth removed by overflow,
purge or final peer release. Choosing a new existential list of birth tickets
for each retained queue is also insufficient to connect disposal and allocation
when several packet values are equal.

The new `HandshakeSecurity/StagedDisposalSource.lean:84` observers and
`StagedDisposalFrames.lean` prove the exact counted arms, including the release
cut before its potentially stopping suffix. However, neither the shared Driver
nor either current journal calls those observers. Only local support modules
refer to them. The final event type has no staged-disposal constructor.

Consequence: a proof over the current availability predicate may forget a
removed prefix without a terminal classification. This is a limitation of the
predicate, not evidence that the native source loses packets.

Required repair: retain one ordered ghost ticket list for each native staged
queue. Move its exact prefix to terminal records at the actual overflow cut,
its whole list at purge, and its whole list at the counted peer erase. Use the
same list for later allocation; do not choose independent ticket witnesses.
The existing `Partition` gives the peer stamp, device epoch, exact prefix/suffix,
other-peer frame and counter delta needed for these transitions.

## 2. High: first terminal outcome must be distinguished from cleanup

The current postallocation source has real packet-release events:
`Queues/TxDisposition.lean:134` executes the per-packet free observer. They are
valuable evidence, but every successful socket handoff is followed by the same
free loop. Treating both a socket receipt and a release as terminal outcomes
would double count every successful send. Likewise `.removed` at line 126 only
transfers the batch into a caller local, and `.completion` at line 129 records
entry before timers and the first socket call. Neither is a terminal batch
outcome.

The native cases require the following distinctions:

| Native arm | Accounting effect |
| --- | --- |
| `createDataDead` / peer queue `-ENOSPC` (`Send.lean:160-174`) | Actual frees dispose the unqueued batch, without a device drop counter. Keep the rejection reason attached through reference repayment and each free. |
| Device ring `-EPIPE` (`Send.lean:148`, `:167`) | The peer queue still owns the batch; DEAD publication is followed by worker disposal. Ring refusal itself is not the free. |
| Encryption returns `none` (`Data.lean:139-150`) | The entire batch becomes DEAD, including any already encrypted prefix. It stays pending until the actual worker frees it; no drop counter is added. |
| CRYPTED completion (`Data.lean:200-217`) | Each packet gets its own socket outcome. Later frees are cleanup of those terminal outcomes. |
| Socket family unsupported (`Data.lean:179`) | The native call returns false and later frees the packet, but `CompletionSource.lean:60` produces no inner `.socket` receipt. |

The last case needs either an initialized proof that this arm cannot occur for
these obligations, or an explicit named failure outcome at the outer
`sendSkbToPeer` cut. An all-input send-attempt receipt would cover it directly.
A successful `send4`/`send6` receipt already retains native failure results such
as missing socket or routing error; failure is not an emitted datagram.

## 3. High: the forward frontier must retain stopped caller locals

`DriverSource.lean:68-88` removes a staging queue before age checks,
reservations and allocation. A hidden-input Stop can leave the selected batch
held in that source continuation. Similarly, TX completion removes its queue
head before timers and sends; a Stop after a proper prefix of sends leaves a
mixed batch: a terminal prefix and a pending suffix. `TxCoverage` correctly
models native locals, but its initialized exports in
`RetirementSecurity/TxCoverageInitialized.lean:10-29` are normal runner
endpoints. They do not establish a history frontier for an internally stopped
call. The service development likewise does not currently provide that
historical partition.

Required repair: source-phase transitions retain held tickets on selection,
restore, allocation, queue insertion, TX removal, each handoff and each free.
These transitions must survive Stop. Existing selected/allocation/removed
receipts are useful exact cuts. Completion-entry alone is too early to mark
all its tickets terminal. An absence of returned World on Stop is not a
terminal outcome or permission to forget those tickets.

## 4. Medium: the admission domain and counted error unit need explicit joins

`StagedOrigins.Born.routed` is restricted to completed successful `txFront`
receipts. Early `wgXmit` errors (`Device.lean:340-404`) return
`-EPROTONOSUPPORT`, `-ENOKEY`, `-EDESTADDRREQ` or `-ENOMEM` and charge
`txErrors` once for the original call/skb. `Journal.front` retains the completed
error receipt, but the birth predicate does not include it. A list supplied to
the mirror for GSO must not turn that single counter increment into one
increment per logical segment.

The final statement should explicitly connect both the successful admission
cut and these named rejected-entry outcomes to the original invocation. If
all supplied packet positions are obligations before validation, give that
invocation an entry identity before any potentially stopping front operation,
then classify its result. If successful splice is the admission cut, retain
the separate exact early-error theorem rather than silently dropping the
charter's counted error arms.

## Concrete route

Use a forward ghost ledger on the same callback-parametric Driver, with an
exact projection to the current final journal. Its key is the existing birth
position and ordinal (or an entry position until successful splice), paired
with the actual device/peer allocation where resident. Each key has exactly
one logical location: staged, a selected/unpublished local, a peer queue, an
active completion position, or terminal. Device-ring references remain
aliases. A terminal entry records either one socket result or one named
actual disposal; subsequent storage cleanup cannot replace it.

The first implementable slice is fixed-ticket splitting at the three native
staged-disposal cuts and an exact front factor exposing the trim callback.
The existing `front` hook permits that refinement without changing the shared
Driver API. Purge and final-release coverage require their actual source
callers: timer give-up, stop/removal, and nested reference repayment paths.
A blanket native frame over a caller that can free a peer would hide the
needed terminal transition.

Next use the canonical allocation bank to transfer the selected tickets to
allocation-stamped skb positions. Attach the native create/refusal reason,
then use existing queue ownership and packet-release observers to classify
each actual free. An outer send-attempt factor covers unsupported-family
failure and separates terminal handoff from subsequent cleanup. Finally,
transport the combined ledger through the initialized shared source, retaining
all open locals in stopped prefixes. T6's strict before-reset empty-store
result can close device destruction after its actual service and idle-entry
premises are derived there; reset itself must never count as disposal.

The theorem to export is a total partition for every original obligation at
every reached prefix, with an exact one-to-one terminal relation. The existing
allocation, ciphertext, peer and endpoint results then identify its socket
case. Converse emitted-datagram coverage remains the separate T3 integration
needed to show that the journal misses no native emission.

## Dispositions during implementation

[AGENT 2026-10-19] All four gaps are accepted as proof obligations.

1. Local fixed-ticket purge/final-release transitions now preserve every
   ledger identity, settle the same incoming queue list and expose the native
   counter delta. The final journal records staged disposal. Complete nested
   release coverage and initialized ledger transport remain open.
2. The ledger retains the first terminal result and admits no terminal
   replacement. Outer send-result receipts cover the missing failure arm.
   Their join to each actual socket/free occurrence remains open.
3. Native take/restore factors and completion/free frontiers retain source
   locals through Stop. Selected/allocated tickets still need complete native
   backing and initialized transport; ledger membership alone is insufficient.
4. The actual original transmit refusal theorem now gives the named errno and
   one `txErrors` increment per invocation, independent of GSO length. Successful
   splice remains the ticket-birth boundary. The final conservation package
   must include that separate invocation-level result.

The current local disposal and T3 emission-coverage claims pass the aggregate
gate and fresh kernel replay. None of those results closes T2’s complete
forward partition. No mirror edit or claim weakening is used.

Source-92 `f676d7a0` supplies IPv6 receive from its fixed source: predicate checks, explicit refusals, WG read and inbox write. A structural proof excludes every child callback, and its packet-account frame and original remainder replace the IPv6 premise in the initialized runner. Three packet families, the flushed protocol sender, twelve dispatch bodies and finer native intervals remain open. Validation passes 4303 root build jobs and 21 standard-or-empty public-declaration axiom queries; all 4256 frozen proof hashes and fifty landed carry paths match. Source-90 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source elaboration failures were repaired before validation; no mirror finding arose. Main and mirror are unchanged.

Source-93 `4e53d136` supplies the flushed protocol sender from its fixed original binds, creation receipt, timer helpers, socket call and counted peer repayment. The initialized runner no longer assumes a flushed-sender contract. Three packet families, twelve dispatch bodies and finer native interiors remain open; T2 is not complete. Aggregate validation passes 4307 root build jobs, the 1563-declaration gate across thirteen roots, 31 standard-or-empty public-declaration axiom queries, fresh root kernel replay (retrieved exit 0) and all twelve counterexample recipes (retrieved exit 0). All 4260 frozen proof hashes and fifty landed carry paths match. Source elaboration, layout and normalization failures were repaired before validation; no mirror finding arose. Main and mirror are unchanged; no differential result is added, and the inherited Env deprecation remains outside scope.

Source-94 `a3ba20bf` joins fixture-scoped staging and keepalive, protocol-send drains, counted purge and peer release to the existing create/delete/up/down source proofs and the initialized runner. The stronger deletion entry and native quiescence guard remain intact. Eight dispatch bodies, three packet families and finer native interiors remain open. The sender source also builds with default Lean limits after removing its file-wide increases. Validation passes 4311 root build jobs and 43 standard-or-empty public-declaration axiom queries; all 4264 frozen proof hashes and fifty landed carry paths match. Source-93 `4e53d136` remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and source-normalization errors were repaired; no mirror finding arose. Main and mirror are unchanged.

Source-95 `55c71bde` supplies the three dump dispatch contracts from fixed source witnesses, retaining counted cursor release and the landed header cancellation. Five dispatch bodies, three packet families and finer native interiors (including header/walk atoms) remain open. Validation passes 4314 root build jobs and 32 standard-or-empty public-declaration axiom queries; all 4267 frozen proof hashes and fifty carry paths match. Source-93 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. A namespace elaboration error was repaired; no mirror finding arose. Main and mirror are unchanged.

Source-96 `06271ec7` connects routed transmit from its actual front result through expanded staging and counted repayment. Two packet families and five dispatch bodies remain; the compound front and other finer native interiors are still explicit coverage obligations. Aggregate validation passes 4317 root build jobs, the 1563-declaration gate across thirteen roots, 23 standard-or-empty public-declaration axiom queries, fresh root replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4270 frozen proof hashes and fifty carry paths match. Namespace and rewrite-normalization errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged; the inherited Env deprecation remains outside scope.

Source-97 `8fba7fc3` supplies the handshake worker from its fixed branches, scopes, receipts, timer helpers, expanded keepalive and counted release. Peer transmit is the remaining packet-family premise; five dispatch bodies and finer native intervals, including compound consumers/session/socket atoms, remain open. Validation passes 4322 root build jobs and 37 standard-or-empty public axiom queries; 4275 frozen proof hashes and fifty carry paths match. Source-96 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source decomposition resolved an elaboration timeout at default limits; layout and binder errors were repaired. No mirror finding arose; main and mirror are unchanged.

Source-98 `39904f78` gives fixed TX read/dequeue/selection cuts their original worker continuations and same-ledger evidence. The read cut is idle ownership; dequeue transfers the actual queued batch to a selected local, with its pending tickets retained. The existing successful-selection theorem is reused. Peer-transmit composition, five dispatch bodies and send/disposal or other native interiors remain open. Validation passes 4325 root build jobs and 19 standard-or-empty public axiom queries; 4278 frozen proof hashes and fifty carry paths match. Source-96 remains the latest aggregate checkpoint. An exploratory duplicate of the existing selection theorem was removed; a binder error was repaired. No mirror finding arose; main and mirror are unchanged.

Source-99 `438ef973` joins fixed DEAD and ordinary-cleanup loop boundaries and native erase intervals to actual worker selection. Continuations use only source runs; entry accounting derives successor-ledger ownership, the exact pending terminal receipt, or the consumed cleanup debt. Peer-transmit composition, five dispatch bodies and remaining native intervals stay open. Validation passes 4329 root build jobs and 24 standard-or-empty public axiom queries; all 4282 frozen proof hashes and fifty carry paths match. Source-96 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development syntax, namespace and source-normalization errors were repaired at default Lean limits; no mirror finding arose. Main and mirror are unchanged.

Source-100 `def57484` connects both actual cleanup arms to shared key repayment and the nested peer-release observer, retaining its original access histories, before-state and counted receipts. Completed cleanup derives an empty-debt account on the same successor ledger; source-only continuations need no incoming cleanup certificate. Send-completion composition, five dispatch bodies and finer native intervals remain open. Validation passes 4333 root build jobs, the 1563-declaration gate across thirteen roots, nineteen standard-or-empty public axiom queries, fresh kernel replay (retrieved exit 0) and twelve recipes (retrieved exit 0). All 4286 frozen hashes and fifty carry paths match. The first source draft used the wrong peer observer; correcting it to the existing nested observer removed the elaboration timeout at default limits. Namespace and binder errors were repaired; no mirror finding arose. Main advanced to `1a69cebb` during validation and is merged at `66d9ffb7`, retaining both register sections. Its sole mirror delta replaces the deprecated observation string constructor; the subsequent merged-tree gate passed 4333 jobs and 1563 terminal declarations without proof-source changes.


Source-101 `270ef749` derives ordered-send, packet-capture, socket-result/receipt and completion-stage cuts from the original worker selection, retaining both receipt entry worlds and the same ledger lineage. The initialized runner now supplies peer transmit and direct transmit dispatch, including fixture exit and descriptor repayment. Four dispatch bodies and finer native intervals remain open. Validation over main `1a69cebb` passes 4346 build jobs, the 1563-declaration gate across thirteen roots, 109 standard-or-empty public queries, fresh kernel replay (retrieved exit 0) and twelve recipes (retrieved exit 0). All 4299 frozen proof hashes and fifty carry files match. The post-merge source-100 gate also passed; this mirror spelling change required zero proof-frame repairs. Development source-normalization, binder and layout errors and unused arguments were repaired at default Lean limits. No mirror finding or accepted warning remains.


Source-102 `ee479c1a` supplies receive, flood and batch dispatch from their original control flow and concrete shared scheduler/NAPI instances. Fixture-wrapped batch transmit retains the original scope token and routed child. Configuration is the remaining dispatch premise; finer native intervals, including the compound receive-entry atom, remain open. Validation passes 4355 build jobs, the 1563-declaration gate across thirteen roots and 49 standard-or-empty public queries. All 4308 frozen proof hashes and fifty carry paths match. Fresh kernel replay and twelve recipes last passed at source-101 `270ef749`; they were not repeated for this helper checkpoint. A native-token elaboration timeout was resolved by separating kind, result and action, at default Lean limits. No mirror finding or accepted warning remains; main and mirror are unchanged.

Source-103 `a144e4a7` supplies configuration dispatch from its fixed original source witness. `ConfigConcrete.initialized` now derives every declared dispatch-family contract, retaining semantic evidence acceptance and finer native intervals as explicit obligations. Peer creation carries the allocation invariant; saved keepalive and preshared-key writes retain their actual read prefixes; removal reuses the original null guard and concrete after-dead children. Configuration fixture sends retain their own trigger and original scope. T2 remains open. The thirteen-module delta passes 4368 build jobs, the 1563-declaration gate across thirteen roots, 68 standard-or-empty public axiom queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4321 frozen proof hashes and fifty inherited carry paths match. Source decomposition and narrower elaboration resolve the development resource failures at default Lean limits; no warning or mirror finding remains. Main and mirror are unchanged.

Source-104 `308d4c84` joins actual peer reads, family guards, unsupported-family refusal and completed sends to the transmit worker, and carries the exact socket settlement through native byte accounting before its access receipt. Source-only continuations retain the original outer send witness. T2 remains open at socket-route/cache and other finer native interiors, semantic evidence interpretation and universal source coverage. The nine-module delta passes 4376 build jobs and all 54 standard-or-empty public axiom queries without warnings; all 4329 frozen proof hashes and fifty inherited carry paths match. Source-103 `a144e4a7` remains the latest aggregate gate, fresh kernel replay and twelve-recipe checkpoint. Development rewrite and dependent-state errors were repaired at default Lean limits. Main and mirror are unchanged.

Source-105 `e32a4d02` expands the fixed socket front through IPv4 retry, IPv6 routing, cache reads/writes, the saved-peer scan and tunnel preparation. Native source points retain the actual getter prefixes and both original receipt entry worlds; worker entry derives the same packet account. Other native interiors, semantic evidence interpretation and universal source coverage remain open. The ten-module delta (nine new modules, 780 lines) passes 4385 build jobs, the 1563-declaration gate across thirteen roots, 89 standard-or-empty public axiom queries, fresh full-root kernel replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4338 frozen hashes and fifty carry files match. Smaller source witnesses resolve development elaboration timeouts at default limits; no warnings or mirror finding remain. Main and mirror are unchanged.

Source-106 `75bfe606` joins the actual receive-entry guards, RX allocation, admission, refusal cleanup and counted peer releases to receive, flood and batch dispatch. RX allocation and erasure transport the TX account using packet bounds, while source-only continuations retain the original ingress. Native access atoms, other finer intervals and final semantic source coverage remain open. The seven-module delta passes 4390 build jobs and 46 standard-or-empty public axiom queries without warnings; all 4343 frozen proof hashes and fifty carry paths match. Source-105 `e32a4d02` remains the latest aggregate gate, fresh kernel replay and twelve-recipe checkpoint. Main and mirror are unchanged.

Source-107 `01dfbd7d` connects the original overflow iterations, guard, queue removal and pending counter charge to routed transmit and the initialized caller graph. Removed tickets stay on the incoming ledger until the actual overflow receipt; the splice retains its pending routed birth receipt and both original entry snapshots. The front evidence acceptance is explicit. Other native intervals and final semantic interpretation remain open. The seventeen-module delta (four new modules, 272 lines) passes 4394 build jobs, the 1563-declaration gate across thirteen roots, 86 standard-or-empty public axiom queries, fresh full-root kernel replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4347 frozen proof hashes and fifty carry paths match. Development binder, rewrite and argument-order errors were repaired at default Lean limits; no warnings or mirror finding remain. Main and mirror are unchanged.

Source-108 `935b1b13` derives concrete initialized accounting evidence over the WG projection without an abstract safety predicate or semantic-acceptance premises. The new statement preserves selected, allocation and pending-receipt phases. Ordinary and selected current-state partitions give each admitted ticket one status; held plaintext retains its actual take and current vacant queue, without identifying the current world with the earlier snapshot. Finer native coverage and complete interval interpretation remain open. The four-module delta passes 4397 build jobs, the 1564-declaration gate across thirteen roots, fifteen new standard-or-empty public axiom queries, fresh full-root kernel replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4350 frozen proof hashes and fifty carry paths match. Draft elaboration and unavailable-tactic errors were repaired at default Lean limits; no warnings or mirror finding remain. Main and mirror are unchanged.

Source-109 `16daf7e3` interprets every declared initialized phase as a current semantic account or one of fifteen fixed mutation intervals. Current accounts derive one status per admitted ticket, native cell ownership and unique ticket backing, terminal uniqueness and receipt cardinality on the same ledger. A trim guard changes only the ambient trace, so its WG projection reuses the loop interval. Pending cohorts, allocation aliases and receipts remain explicit; per-ticket interval consequences and complete native source coverage remain open. The four-module delta passes 4400 build jobs, the 1565-declaration gate across thirteen roots, 36 new standard-or-empty public axiom queries, fresh full-root kernel replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4353 frozen proof hashes and fifty carry paths match. Explicit world and packet-id binders repair draft elaboration failures at default Lean limits; no warnings or mirror finding remain. Main and mirror are unchanged.

Source-110 `77d0f2ab` derives the current semantic account after the original pending records for all twelve receipt-only interval families: take, restore, keepalive birth, routed admission, trim completion, purge, original and nested peer release, native frees and socket handoff. Each result retains its actual source equation or fixed total record emission on the same native world. Partial allocation, trim-loop progress and complete native source coverage remain open. The three-module delta passes 4402 build jobs and twelve new standard-or-empty public axiom queries; all 4355 frozen proof hashes and fifty carry paths match. Source-109 `16daf7e3` remains the latest aggregate gate, fresh root replay and twelve-recipe checkpoint. An explicit world equality repairs a draft projection rewrite; no warnings or mirror finding remain. Main and mirror are unchanged.

Source-111 `537c7dad` derives the initialized fixed-record completion disjunction without semantic-acceptance premises. Receipt intervals now restore current accounting using only the original records on the unchanged native world. Partial allocation, trim semantics and finer source coverage remain open; validation is recorded in the campaign report.

Source-112 `cc4ef4fd` derives the remaining partial-allocation and trim semantic consequences and joins them into the initialized same-ledger account. Their source intervals no longer remain uninterpreted phase alternatives. The separate finer-native-coverage finding remains open; validation is recorded in the campaign report.

Source-113 `79cd5525` expands the initialized relation through atomic access trees of six UDP-ingress helpers. This is a source-coverage improvement, not closure of the remaining index-lookup and RX queue/publication interiors. The campaign report records the intermediate build and axiom checks.

Source-114 `7207e10d` joins the original index-loop, peer-acquisition and owner-word-write points to initialized ingress accounting. The saved-peer reference write retains its own read and original continuation. RX queue/publication and other finer native interiors remain open; the campaign report records the full validation checkpoint.

Source-115 `328a0d2c` joins RX adapter and queue-admission points to initialized accounting. Allocation and erasure use native packet-bound transport; the adapter does not mutate WG state before write-back. The queue write retains its actual saved peer and source continuation. Publication and other finer interiors remain open. The campaign report records scoped validation and the unchanged aggregate checkpoint.

Source-116 `fe6161d3` joins RX publication through the actual resolution, borrow, guard and saved writes. Ordinary ingress reads and writes now have access-tree points as well. Compound handshake, configuration and lifecycle native calls remain among the open coverage obligations. The campaign report records the full validation checkpoint.

Source-117 `095e3aa7` joins actual saved-peer metadata points for response creation, MAC updates and related handshake timers. The read-derived write preserves peer identity and both TX queues, with its original continuation. Other compound native calls remain open; the campaign report records intermediate validation and the latest aggregate checkpoint.


Source-118 `67607187` joins protocol socket interiors to initialized handshake accounting, preserving the original route/cache source, causal context and receipt entry. Other native families remain open. The campaign report records the passing aggregate gate, fresh replay and twelve recipes.


Source-119 `e9f496fb` joins native session creation/rotation and outgoing initiation/MAC/socket points. The two session receipts retain their original run and order. Compound consumer, cookie, configuration and lifecycle interiors remain open; the campaign report records scoped validation and the latest aggregate checkpoint.


Source-120 `cdf1eda8` joins captured MAC validation, load/rate-limit writes and endpoint metadata to the initialized source relation. Ordinary handshake fallback atoms are expanded. Compound consumers, cookie emission and administrative interiors remain open; the campaign report records scoped validation.


Source-121 `722b7a0e` joins compound initiation, response and cookie consumers, including native authentication, lookup, accepted writes and counted releases under their original captures and receipts. Cookie emission and other administrative/service interiors remain open. The campaign report records the passing gate and scoped checks.


Source-122 `7f9005de` joins complete cookie emission through native routing, tunnel capture, append and receipt points. Exact source equations retain the original capture and journal. Configuration, lifecycle and service interiors remain open; the campaign report records scoped validation and the latest aggregate checks.


Source-123 `5b0a99a1` joins configuration metadata, public-key lookup, peer creation and the delayed send-worker prefix. The original read supplies saved-peer fields, and initialized allocation derives creation freshness. All cuts preserve the same ticket ledger. Configuration routing edits, lifecycle and remaining service interiors remain open. The campaign report records the passing aggregate gate, fresh replay, twelve recipes and scoped axiom queries.


Source-124 `94d177c7` joins newlink through its actual registration write and continuation. The original setup account derives the new empty epoch account with the same ledger. Routing edits, other lifecycle and service interiors remain open. Scoped build and axiom validation passed over `1a69cebb`; the report distinguishes that checkpoint from main `1f766662`, awaiting merge and carry.


Source-125 `333ad8e0` joins configuration routing through fixed source trees, original saved peer-list prefixes, actual list writes and trie adapters. The same packet account holds at each point and the original continuation is retained. C1 removal source factors avoid increasing proof resource limits; C1 files are unchanged by this result. The thirteen C1/C3 roots pass 4462 build jobs, 57 focused and 2321 root/carry axiom queries, and token/import checks. Carry `5b311948` remains the latest scoped fresh replay and twelve-recipe checkpoint over mirror `1f766662`; the aggregate gate is blocked by the C2 word-type carry. Lifecycle/service interiors and the final native-source coverage audit remain open.

Source-126 `b157ac70` joins timer deletion and peer acquisition in the service/work-service point and residual relations. Native read-only trees exclude WG writes by construction; saved-write frames derive the resident identity from the actual read and retain the same ledger. The service allocation companion is also preserved. Validation passes 4467 C1/C3 root build jobs, 84 focused and 2321 root/carry standard-axiom queries, and token/import checks. All 55 carry paths are unchanged; carry `5b311948` remains the latest scoped replay/recipe checkpoint. Lifecycle/receive-helper interiors and the final source audit remain open, with aggregate validation still blocked by C2's word-type carry.

Source-127 `425a7546` replaces canonical whole-call lifecycle metadata atoms with fixed native source trees. Socket setup, handshake/key clearing, routing cleanup, worker retirement and destructor checks retain their original continuations and the same packet account at interior points. The thirteen C1/C3 roots pass 4467 build jobs, 92 focused and 2321 root/carry standard-axiom queries, and token/import checks. Carry `5b311948` remains the scoped fresh-replay and twelve-recipe checkpoint. Receive-helper interiors and the final source-coverage audit remain open; aggregate validation remains blocked by untouched C2 word types.

Source-128 `d8cd4d80` expands canonical receive key reads, age tests, confirmation metadata, receive statistics and ECN source branches. Their native points retain the same ledger and original continuation. Validation passes 4468 C1/C3 root jobs, 70 focused and 2321 root/carry standard-axiom queries, and token/import checks. Other receive helpers and dump header/walk interiors remain open alongside the final source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation is still blocked by untouched C2 word types.

Source-129 `5bec0451` joins receive endpoint, key-release, routing and timer metadata plus the actual maybe-zero peer acquisition. Fixed source points retain original continuations and the same packet account. The thirteen C1/C3 roots pass 4469 build jobs, 76 focused and 2321 root/carry standard-axiom queries, and token/import checks. The source audit still identifies whole-call dump, individual-removal and preparation/socket helpers; those interiors remain open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-130 `16aa23b3` expands dump headers, peer/allowed-IP walks, socket bookkeeping and coalescing through fixed metadata trees, retaining nest cancellation and counted cursor release. Individual removal uses the routing source tree before the existing drain/release continuation. The thirteen C1/C3 roots pass 4470 build jobs, 41 focused and 2321 root/carry standard-axiom queries, and token/import checks. Preparation/socket helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-131 `2363afae` expands preparation metadata, key unhashing, route adapters, socket-port reads and loopback bookkeeping. Fixed native points preserve the packet projection and original journal suffix. The routing adapter source equation retains its read, isolated component call and write-back. The thirteen C1/C3 roots pass 4472 build jobs, 74 focused and 2321 root/carry standard-axiom queries, and token/import checks. Observed-getter interiors and the final source audit remain open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-132 `c7dd5e7e` joins lifetime-observed peer/key/packet getter interiors, including packet-store extraction, component execution and write-back. Each remaining native suffix retains the original access receipt. The thirteen C1/C3 roots pass 4474 build jobs, 23 focused and 2321 root/carry standard-axiom queries, and token/import checks. The audit identifies NAPI and scheduler/service helper interiors still represented as whole calls; those remain open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-133 `e6df1a20` joins NAPI metadata, RX reads and packet-store removal interiors. Source-fixed points retain original continuations; RX removal transports the TX ledger without claiming unchanged RX state. The thirteen C1/C3 roots pass 4476 build jobs, 81 focused and 2321 root/carry standard-axiom queries, and token/import checks. Worker-iteration and scheduler/service helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-134 `0322d3c0` joins iteration peer/packet getter points, the literal rescheduling branches and explicit work-service metadata callers. The packet adapter read uses the read-only source type, preserving the allocation companion alongside the same TX ledger. The thirteen C1/C3 roots pass 4478 build jobs, 99 focused and 2321 root/carry standard-axiom queries, and token/import checks. Scheduler/service guard interiors and the final source audit remain open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-135 `90deabc2` joins scheduler read guards, copied-world consistency trials and timer completion checks through a read-only product source type. Native getter points retain the full allocation companion and original continuation; trial results never replace committed WG state. The thirteen C1/C3 roots pass 4481 build jobs, 151 focused and 2321 root/carry standard-axiom queries, and token/import checks. Ring/wheel getter interiors, remaining explicit helper callers, staging coverage and the final audit remain open. The mirror and C2 files match main. The earlier current-status claim that all 55 carry paths remained unchanged was stale: sixteen inherited files still match, while source-130/131 extended the C3 dump/socket files. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-136 `51a9c7ee` joins the ring-poll device getter, both wheel peer reads and explicit timer/protocol metadata callers that bypassed shared source helpers. The traffic device getter uses the service read tree. Fixed points preserve the same ledger, saved peer and original continuation. The thirteen C1/C3 roots pass 4481 build jobs, 87 focused and 2321 root/carry standard-axiom queries, and token/import checks. Staging and outer helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-137 `20e14972` joins actual staging getter cuts using a source type that preserves both WG and Ambient state. Other non-store helpers factor exactly through Ambient; the original peer/key setters are classified as atomic writes. The phase contract is unchanged. The thirteen C1/C3 roots pass 4485 build jobs, 37 focused and 2321 root/carry standard-axiom queries, and token/import checks. Remaining staging children and outer helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-138 `e9e055a8` joins traffic sender selection, packet construction, pending-work and end-of-wait guards through actual read-source trees. The canonical traffic path also selects native environment, routing and scheduler-peek reads. Original branches, failures and continuations are retained. The thirteen C1/C3 roots pass 4486 build jobs, 11 focused and 2321 root/carry standard-axiom queries, and token/import checks. Remaining staging children, routing/loopback adapters and other outer helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-139 `ed8a1590` joins routing-adapter extraction and write-back plus multicast loopback reads, pending-NAPI checks and NET_RX bookkeeping. Individual writes preserve the full packet-store projection, transporting both the same ledger and allocation companion. Fixed points retain original continuations. The thirteen C1/C3 roots pass 4489 build jobs, 47 focused and 2321 root/carry standard-axiom queries, and token/import checks. Remaining staging children and dispatch/runner helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-140 `18d44866` joins observation guards, fixture inbox clearing, final statistics reads and netlink getter points into dispatch coverage and residuals. The netlink setter is identified as one literal write. The same ledger and allocation companion persist through each point. The thirteen C1/C3 roots pass 4490 build jobs, 49 focused and 2321 root/carry standard-axiom queries, and token/import checks. Mirror and C2 directories match main; all sixteen C1 carry files remain unchanged. Remaining staging children, dispatch control/subsystem adapters and runner helper interiors remain open under the source audit. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-141 `d66c10ba` joins FS/task/seccomp adapter extraction, isolated execution and write-back, plus address/route controls, namespace close, time advance and descriptor wrappers. Canonical dispatch selects the fixed trees and transports the full packet account through their points. The thirteen C1/C3 roots pass 4492 build jobs, 27 focused and 2321 root/carry standard-axiom queries, and token/import checks. MTU, runner helpers and the remaining staging audit stay open. No new resource limit or warning suppression was used. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-142 `47af7b8d` joins MTU range checks, the actual scalar write, routing notifications and descriptor adapters. The existing three-scalar mask preserves packet accounting, identities and allocation metadata; every point retains its original continuation. The thirteen C1/C3 roots pass 4495 build jobs, 61 focused and 2321 root/carry standard-axiom queries, and token/import checks. Runner helpers and the remaining staging audit stay open. No new resource limit or warning suppression was used. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-143 `34eae945` joins runner entry, callback metadata, routing and skip helpers through fixed logged source trees. Every interior point preserves the same packet account, allocation companion and original continuation. The thirteen C1/C3 roots pass 4498 build jobs, 77 focused and 2321 root/carry standard-axiom queries, and token/import checks. Setup, cleanup and the remaining staging audit stay open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-144 `4a88e271` joins runner prefill and routing boot through exact setup factors, preserving error index zero, observation reset and the original remainder. The prefill equation is parameterized over its component call to avoid reducing that implementation; no resource limit is raised. The thirteen C1/C3 roots pass 4499 build jobs, 52 focused and 2321 root/carry standard-axiom queries, and token/import checks. Cleanup and the remaining staging audit stay open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-145 `83ba24ee` joins namespace cleanup, socket replacement, endpoint/cache updates and routing teardown to the initialized runner. Peer writes retain their own getter result; every point preserves the same packet ledger and allocation geometry with its original remainder. The thirteen C1/C3 roots pass 4505 build jobs, 67 focused and 2321 root/carry standard-axiom queries, and token/import checks. Mirror and C2 directories match main; all sixteen C1 carry files remain unchanged. Allocation adapter interiors and the final source audit stay open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.

Source-146 `df291b67` joins the actual allocation adapter's getter, isolated component and write-back points to initialized staging. Each point derives its existing partial-allocation cursor, retaining the same selected-ticket aliases and original batch-receipt capture; its remainder is the actual suffix. The thirteen C1/C3 roots pass 4508 build jobs, 15 focused and 2321 root/carry standard-axiom queries, and token/import checks. The final source audit and extension-parameter closure remain open. Scoped replay/recipes remain at `5b311948`; aggregate validation remains blocked by untouched C2 word types.


## Final dispositions at `decb640d`

The four original conservation findings are fixed within the mirror projection:

1. **Disappearing staged packets.** The shared history now contains the actual
   overflow, purge and final-release receipts. Each settles the same ordered
   ticket prefix or queue; allocation uses the remaining tickets rather than
   choosing independent payload witnesses.
2. **First terminal versus cleanup.** The ledger keeps one first terminal.
   Every outer send attempt has its own result, including unsupported-family
   refusal. Subsequent frees settle cleanup debt and cannot replace a send
   outcome. DEAD and create-refusal frees use their actual named disposal
   reason; device-ring refusal retains the peer-queue owner until disposal.
3. **Stopped caller locals.** The initialized native source relation includes
   selected, unpublished and completion locals before later Stop. Partial
   allocation uses aliases; erasure consumes the actual debt or obligation.
   A write-to-receipt interval names only its original total record suffix on
   the same WG state. Successful interiors are included as well as failures.
4. **Admission and error unit.** Successful splice and newly prepared
   keepalive remain the ticket-admission cuts. The separate
   `original_transmit_refusal_charged_once` theorem retains each named native
   errno and one `txErrors` charge per original invocation, independent of GSO
   length. It is part of the result, not an excluded pre-admission failure.

`initialized_transmit_source_conservation` now supplies the concrete
initialized source account with no incoming account or child-family premise.
Its companion `transmit_source_children_are_closed` eliminates all extension
parameters. The [final source audit](2026-10-19-review-campaign-3-t2-native-cut-closure.md#final-source-audit-at-decb640d)
dispositions normal/Stop coverage, every caller family and the native mutation
intervals separately; the parameter equality does not substitute for that
audit. Existing socket binding and T3 append coverage join conservation to
actual authorized egress. Pending ownership is retained, not a promise of
future completion. The aggregate campaign gate awaited the C2 carry at this checkpoint. Main
`eba3c2b6` supplies it without changing C3's proof sources; current post-rebase
validation is reported in the campaign report.
