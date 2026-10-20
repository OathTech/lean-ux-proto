# Proofs about the mirrors

`Leanux/Proofs/` is the repository's proof tree: every theorem about the
executable mirrors lives there and nowhere else. It includes the shared
layers and results of campaign 1 and the six results of campaign 2. Proofs
are a validation channel beside the differential check, under Rule Zero:
the mirror is never edited to let a proof close. The standing rule and gate
are in [AGENTS.md](../AGENTS.md); this file maps the tree and registers its
claims, premises and mirror pins.

## Campaign 3

The [campaign-3 report](2026-10-18-proof-campaign-3.md) tracks
`proofs/campaign-3` is current over main `3308c49a` at source-89 `210bf296`, after merge `ab65f1fd`. T1, T3, T4, T5 and amended T6 are complete at their stated boundaries; T2 remains open. Main has landed the separate inherited C1 carry (`74b03922`, `0c8f59fb`, `7a189c9e`): 48 repaired modules and two helpers; six public native frames added, three repaired, none deleted, plus two private read frames. Its isolated gate, fresh replay and twelve recipes pass. Source-89 passes 4289 root build jobs and 19 public-declaration queries across five new modules; all 4242 frozen proof hashes and fifty landed carry paths match. Source-87 `650a4aff` remains the latest aggregate gate, fresh root kernel replay and twelve-recipe checkpoint. Campaign-2 source facts remain named hypotheses.

| Outcome | Result, assumptions and remaining boundary |
| --- | --- |
| T1 nonce safety | Complete. `TransmitSecurity.initialized_nonce_safety` joins initialized native reservation uniqueness, actual key-allocation/AEAD nonce uniqueness, bounded counters and exact header/wire encoding, including stopped prefixes. No incoming invariant or H1 premise remains. `HandshakeSecurity.native_nonce_rejection_invalidates_and_restores` and the rejection observer expose the actual invalidation/restoration and unchanged drop count; `TransmitSecurity.original_rekey_count_request` and `original_rekey_age_request` expose the guarded native helper call. |
| T2 transmit authorization and conservation | Open. Initialized socket claims bind each ciphertext to its admitted plaintext, selected peer, historical owning key and endpoint; allocation credits are unique. `CompletePrefix.Runner.reached` now derives complete accounting for every prefix of the original normal or stopped journal, including actual guarded deletion, without an incoming carrier or callback premise. `CompleteConsequences` derives the same ledger’s unique status, native ownership predicates, first-terminal evidence and exact receipt converse. Logical-prefix coverage is closed; relating every accounted snapshot to its actual initialized native cut remains open. `CompleteRunner.normal_cut` connects the initialized normal return, and `initialized_dispatch_entry_accounted` derives the actual dispatch entry from a fixed original operation prefix and syscall guards. `initialized_return_callback_accounted` also derives original callback-prefix accounts; the post-transmit crypt/send entries retain the exact initialized continuation. Initialized routed-front, post-transmit scheduler-activation and TX-worker accounts now retain their original source paths and continuations, including the pre-routed receipt interval. Selected return callbacks and post-transmit send drains now connect send-worker entries, nested scheduler activations, TX entries and direct or crypt-ahead encryption callbacks to initialization, retaining the actual selected poll item. Initialized encryption-loop/publication and overflow-prefix cuts now retain their actual source states. Fixed send-drain coverage now uses a concrete delivery source proof and the original scheduler construction; worker and deeper scheduling interiors remain explicit. Canonical creation has same-ledger phase coverage, and receive wheel/key/endpoint helpers are concrete. Ring polling and queued receive initiation now have concrete source proofs; preparation, expanded staging and the fixed encryption callback now have concrete source contracts, leaving four deeper packet contracts in the initialized receive scheduler. Encryption includes publication and the pending callback return; crypto primitive interiors remain open. Timer keepalive uses the same expanded staging family and its actual preparation admission. Canonical timer coverage now derives raw zero-key repayment from its own borrow and shares observed peer-release evidence, with no remaining timer-child source contract. Core lifecycle boundaries and fixed staging/keepalive phases are proved; deeper child interiors and initialized caller joins remain open. Ordinary cleanup now consumes its matched debt at every initialized native erase. Encryption packet/publication interiors and peer-release cuts retain the original continuation; canonical scheduler point coverage names its committed iteration and NAPI obligations. Local staging, allocation, publication, send-loop, selection/dequeue, queue-install and ordered DEAD-cleanup prefixes retain their exact native cuts. Stopped crypted completion retains its matched worker prefix, ledger and cleanup debts; native DEAD erasure uses an explicit pending receipt until its fixed total emission suffix completes. Complete initialized internal-cut composition and the remaining silent intervals stay open. Original transmit refusals retain their exact per-invocation error charge; successful splice is the birth boundary. No eventual-completion claim is made. |
| T3 authenticated effects and silence | Complete and validated. `AuthenticatedEffects.initialized_silence_security_outcome` combines every native append’s own authorization, rooted timer/work effects, latest own handshake admission, authenticated replay and packet-specific GRO delivery. The cookie exception uses actual load/MAC guards: at most one source-bound 64-byte reply per invocation, strictly smaller than its initialized input, without session effects. Refused initialized consumers preserve every WG field modulo map representation; MAC refusal masks only load/cookie-secret/rate-limit bookkeeping, and decryption names the exact pre-AEAD invalidation alternative. Consumer equality is at completed native cuts, retained through later outer Stop; internally stopped effects use prefix observations. No incoming invariant, funding, coherence or H1 premise remains. No global reply-rate, CPU, timing or cryptographic-unforgeability claim is made. |
| T4 handshake replay resistance | Complete and validated. `HandshakeSecurity` derives initialized retained-peer timestamp and exchange histories, one allocation per successful session, handshake clearing and refusal-state preservation. The final session entry supplies role-slot residency. Actual initialized stale initiations are refused with restored peer records and no sent-data change; the exact native continuation produces no response without an independent ambient-history premise. Final-journal exports prove response-consumption and session-installation uniqueness by exchange epoch, and exactly one native allocation for the same successful session receipt. Visible assumptions include `H1ResponseEdges`, `H1SessionEffects` and operational C2 tag/frame packages at read-only `5177bd9c`; no C2 file is edited. |
| T5 responder confirmation | Complete and validated. `initialized_responder_confirmation_discipline` joins promotion-label uniqueness, each confirmation's own accepted transport cause and actual responder AEAD after confirmation of the same allocation. Initialized transport covers inner promotion receipts even when the enclosing receive later stops. `PendingPromotion.H1DriverFrames` and `H1ResponderCurrentEdges` remain named local C2 operational assumptions; no incoming carrier, reachability, funding or callback premise remains. |
| T6 retirement / C3-F1 | Complete. `RetirementSecurity.reference_aware_retirement_outcome` composes unconditional TX/RX check-site safety and invalidation, initialized R2 access/holder accounting, session-derived zero-arm and selected-arm provenance, actual timer/worker unpublication, retained material and final release. Native final RX cleanup covers authenticated packets too. The holder census is at normal Runner endpoints. Clock/worker runs and residual-reference conditions remain explicit; no bounded latency or physical zeroization is claimed. Both R5 witnesses remain permitted retained work. |

The [staged-origin review](2026-10-19-review-campaign-3-staged-origin.md),
[forward-conservation review](2026-10-19-review-campaign-3-t2-completeness.md),
[cuts review](2026-10-19-review-campaign-3-t2-cuts.md) and
[native-cut closure review](2026-10-19-review-campaign-3-t2-native-cut-closure.md)
record the T2 dispositions and remaining source coverage work. Historical key ownership and initialized
available-credit injectivity are proved. Local fixed-ticket disposal is proved; native transport of stopped caller
locals and the complete pending/terminal partition remain open. Original early
transmit refusals now have their exact invocation-level error charge; a GSO
packet list does not multiply that charge.

Source-50 checkpoint `78cbb619` passes the 3344-job aggregate build and 1523-declaration axiom gate across thirteen roots, using only the three standard axioms; fourteen focused source queries also pass. Fresh root kernel replay, all twelve counterexample recipes, the 66-job default model build and 131 unit tests pass (one configured-kernel skip, 22.657 seconds). All 3297 frozen proof-source hashes match; all 916 inherited proof modules, mirror `77c9b555` and main `783510e8` are unchanged. The preceding fully validated checkpoint is `13d285cf`. The inherited warning and repaired development failures are recorded in the report.

The final Driver now exposes actual take, restore, terminal disposal and nested
reference repayment. Its native projections and completed-outcome adapters pass
the aggregate checks. Local admission creates fresh fixed tickets; native
allocation preserves their backing and injection under explicit entry carriers.
A stopped borrow retains the completed staging take and selected tickets even
without an outer selection receipt. These local facts do not establish the full
initialized pending/terminal partition. The source-45 tranche adds explicit cleanup debts, mixed pending/debt uniqueness,
actual first-terminal source cuts and a canonical journal-derived birth domain.
Native take, restore, keepalive, allocation, purge, overflow, release and routing
transport this combined core. The whole front retains canonical queue accounting
at its stopped checkpoint. These local results pass aggregate checks. General stopped
ownership frontiers, first-terminal transport and initialized conservation remain open. Mirror/C1/C2
claims are unchanged.

Source-46 local joins add the actual selected-take frontier, checked-loop packet
shape, restore cut, whole-front Core checkpoints and result-aware completion
sequencing. Their source callbacks and initialized transport remain open.
Separate terminal receipt evidence and birth-to-allocation carriers now have
whole-front and selected-loop/restore/allocation source joins. Core alone does
not establish those semantic claims; initialized transport remains open. Source-46 passes the aggregate checks above.


Source-47 validated local work adds initialized full Entry, actual take/keepalive/restore
transport, and selected nonce/owner/allocation joins retaining all allocation
preconditions. Canonical completion now uses the same explicit ledger/debts for
its cursor and Entry. Enclosing create, queued-initiation, completion callbacks
and complete initialized transport remain open; local source contracts do not
discharge those remaining commitments.

Source-48 local joins retain full Entry through native queue admission, both peer-release observers, queued initiation and refusal frees. The actual transmit/keepalive composition now leaves only its creation callback open; completion uses indexed settlement and cleanup. Exact normal refusal-debt restoration, enclosing source transport and historical terminal completeness remain open. These local joins pass the source-48 aggregate checks below; they do not establish initialized conservation.

Source-49 local joins derive pending-ticket evidence at the actual allocator and discharge the real creation callback, including exact original-debt restoration after refusal. Full transmit and keepalive now compose without an assumed creation or queued-initiation callback. Counted purge, encryption, receive maintenance and the family-selected completion send retain the full Entry bundle. Stop certificates remain local source frontiers; initialized transport and the converse historical terminal relation are still open. The 3321-job combined root build and eleven focused standard-axiom queries pass. Source-49 has not yet repeated the aggregate gate or fresh root replay; the last fully validated checkpoint is `13d285cf`.

Source-50 local joins cover actual TX selection and DEAD repayment, all send-result arms and nested completion release, receive finishing and timer callbacks, and native key creation, confirmation and clearing. Idle selection derives its pending batch from empty cleanup debts. Retirement algebra proves that empty native staged/TX ownership leaves no pending ticket; the lifecycle caller must still establish that quiescence before reset. The combined root build passes 3344 jobs and fourteen focused queries use only standard axioms. Whole initialized conservation and the converse historical terminal relation remain open. These local joins pass the source-50 aggregate checks below; they do not close initialized T2 conservation.

Source-51 joins the complete native TX worker up to its explicit crypted-completion contract. Indexed send/free loops retain each settlement and restore empty cleanup debt; disposal retains the actual peer-release successor. All five timer callbacks, native handshake checking paths, configuration metadata and routing edits now have full-entry contracts. Peer creation preserves the exact old staged queues under the visible native peer-slot bound. The combined root passes 3367 jobs and fifteen focused standard-axiom queries. Whole initialized transport and historical terminal completeness remain open; source-50 `78cbb619` remains the last aggregate gate/replay checkpoint.

Source-52 defines receipt-to-terminal completeness on the same ledger, proves exact fresh-position settlement and old-receipt preservation, and pairs it with full Entry in `CompleteCarrier`. Passive reuse requires terminal-quiet history explicitly. Native removal and down now compose counted disposal with the still-explicit handshake-work drain. The combined root passes 3375 jobs and nine focused standard-axiom queries. These are local source and algebra joins; initialized conservation and converse transport remain open. The last aggregate gate/replay checkpoint is source-50 `78cbb619`.

Source-53 composes full Entry through native handshake checking and the complete handshake worker, flushed send/clear workers, saved configuration metadata writes, configuration tail and interface opening. Fresh completion rekeying derives its own borrow and exact nonfinal repayment. Purge and both peer-release observers now retain Entry and terminal completeness on the identical successor ledger, including actual stopped cuts. The combined root passes 3396 jobs and fourteen focused standard-axiom queries. Whole initialized conservation and converse transport remain open. This checkpoint, `51c7344a`, also passes the aggregate gate, fresh root replay, all twelve counterexample recipes, default model build and unit suite.

Source-54 closes the Entry-only crypted completion callback and composes actual peer/device configuration, opening and removal. Native allocation freshness is transported on the same observed run. Admission and creation retain terminal completeness on the same ledger, including refusal and stopped cuts; the release evidence is derived from actual reference funding. The combined root passes 3424 jobs and seventeen focused standard-axiom queries. Initialized conservation and whole-history terminal completeness remain open. The last aggregate gate and fresh replay checkpoint remains source-53 `51c7344a`.

Source-55 pairs terminal completeness with forward accounting through actual front admissions, keepalive births, take/allocation/restore, socket results and ordinary completion cleanup. The paired handshake/send/clear workers, send drain, removal/down and peer/device configuration now compose; staging and keepalive callbacks remain explicit in configuration until their paired whole-source join. The root passes 3460 jobs and eighteen focused standard-axiom queries. Initialized conservation, the remaining completion/staging joins and reset quiescence are open. Source-53 `51c7344a` remains the last aggregate gate and fresh replay checkpoint.

Source-56 closes paired whole staging, keepalive and routed transmit, the crypted completion callback, and concrete configuration. Full receive polling, tagged GRO/stack replies, all five timers and both NAPI paths retain the identical ledger and terminal completeness. The paired product-state carrier and native scheduler composition retain explicit worker contracts; stopped prefixes preserve their actual selected or intermediate-cleanup cut. The combined root passes 3495 jobs and twenty-four focused standard-axiom queries. Initialized conservation, the remaining worker/runner joins and reference-aware reset quiescence remain open. This checkpoint, `5a802513`, passes the aggregate gate, fresh replay and all twelve counterexample recipes.

Source-57 closes the whole paired TX worker, including DEAD disposal and the original stopped settlement chain. Concrete encryption, ring polling and decryption preparation now join native allocation safety; full NAPI, timer dispatch, deferred and traffic wrappers compose the exact callbacks. Guarded device creation retains the old ledger, and namespace cleanup is a frame. Destruction retains the same ledger after a checked quiescent cut; its reference-accounting premises remain explicit. A new upper bound shares C1's actual holders with the lower funding bound through creation, payment, detachment and receive/stack transfers. The root passes 3532 jobs and thirty focused standard-axiom queries. UDP ingress, remaining administrative/worker joins, initialized reference-account transport and final T2 conservation remain open. Source-56 `5a802513` remains the last aggregate gate and fresh replay checkpoint.

Source-58 closes actual UDP ingress, scheduled TX/send/clear workers, dump cursor callbacks and every retained administrative arm. The concrete scheduler, deferred work and traffic wrappers compose without callback premises. The exact outer syscall composition leaves only the destruction contract explicit; this is not initialized T2 conservation. Native RX acquisition/allocation/selection/payment/free and TX selection/disposal now carry both peer-reference bounds on the same holders, with temporary RX phases separated from stable queued carriers. The combined root passes 3553 jobs and thirty-three focused queries use only standard axioms. Initialized upper-account transport, reset discharge and the final T2 claim remain open. Source-58 `57598814` passes the aggregate gate, fresh root replay and all twelve counterexample recipes.

Source-59 extends the exact peer-reference account through native dump cursors, send/clear drains, single and bulk removal, full handshake workers, TX completion, RX enqueue outcomes and all timer callbacks. Peer configuration now retains the same account through actual lookup/creation, early cleanup, routing edits and removal. The combined root passes 3593 jobs; thirty-eight focused queries use only standard axioms. Whole RX polling/admission, scheduler transport, lifecycle reset discharge and initialized T2 conservation remain open. Source-59 `782432ab` also passes the aggregate gate, fresh root replay and all twelve counterexample recipes.

Source-60 completes the exact peer account through whole RX polling, native ingress and crypt workers, scheduler/deferred composition, complete device configuration, routed transmit and lifecycle controls. Deletion exposes the same account and positive resident references at its actual prepared guard; successful native guards derive the empty RX ledger. The original runner now supports a stronger idle operation entry and a weaker syscall endpoint, using its real final guard and retaining stopped journals. The combined root passes 3633 jobs, the 1523-declaration gate and thirty-eight focused standard-axiom queries. Outer traffic/account transport, the packet-ledger reset join and initialized T2 conservation remain open. Source-60 `d672ba3e` also passes fresh root kernel replay and all twelve counterexample recipes.

Source-61 closes native outer traffic and every syscall companion, actual guarded packet deletion, and initialized accounting for the returned journal. The same-ledger consequence layer adds pending-location predicates, terminal uniqueness and exact receipt cardinalities; the selected branch now retains native ownership at its recorded take. The combined root passes 3671 jobs. The [cuts review](2026-10-19-review-campaign-3-t2-cuts.md) identifies two remaining obligations: all internal prefixes, and an actual source-cut relation for the accounted snapshot. A separate prefix foundation is integrated; neither it nor the endpoint theorem discharges those obligations. Source-61 `9d2511bb` passes the 1523-declaration gate, 243 focused standard-only axiom queries, fresh root kernel replay and all twelve counterexample recipes. All 3624 frozen proof hashes match; the 916 inherited proof modules, main and mirror are unchanged.

Source-62 adds actual normal runner endpoint correspondence, active admission/staging/disposal prefix contracts, source-matched completion projections and concrete snapshot anchors. Product and passive composition retain all earlier logical prefixes; scheduler composition leaves its worker contracts explicit. Native interval provenance and whole initialized prefix coverage remain open. Source-62 `e97ff936` passes the 3700-job root build, the 1523-declaration gate, 132 focused standard-only axiom queries, fresh root kernel replay and all twelve recipes. All 3653 frozen proof hashes match; the 916 inherited proof modules, main and mirror remain unchanged.

Source-63 closes initialized logical-prefix accounting: `CompletePrefix.Runner.reached` and the exported `initialized_every_journal_prefix_accounted` cover every prefix of the original journal on normal completion or Stop. Concrete TX, crypt, receive, handshake, timer, scheduler, traffic, dump, configuration and guarded deletion sources discharge every callback premise. Fixed native selection/dequeue and queue-install prefixes retain their matched same-ledger cuts; this does not yet connect every accounted snapshot to an initialized native cut or cover all silent intervals. The first cuts-review gap is closed; the second remains open, so T2 remains open. Source-63 `eb4f48cc` passes 3801 build jobs, the 1524-declaration gate, 392 focused standard-only axiom queries in 101 delta modules, fresh root replay and all twelve recipes. All 3754 frozen proof hashes match; the 916 inherited proof files, main and mirror are unchanged.

Source-64 `e5d73508` derives initialized native dispatch entry through the original numeric operation prefix and syscall guards, retaining the exact continuation. Partial native allocation retains selected-ticket aliases before its receipt; publication, send and DEAD cleanup retain fixed source intervals and matching accounts. These local cuts still require complete initialized caller composition. T2 remains open. Validation: 3825 build jobs, 1525 terminal declarations, 90 standard-only public theorem queries across 24 new modules, fresh root replay and all twelve witness recipes; all 3778 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-65 `f2a9731f` derives actual initialized return-callback accounts and post-transmit crypt/send entries, preserving their original continuations. Staging now derives take/borrow/guard outcomes and allocation preconditions from its incoming concrete account; failed send-loop prefixes and every ordered DEAD cleanup boundary retain their matched ledger and native source. The full initialized internal-cut composition remains open. Validation: 3848 build jobs, 1526 terminal declarations, 79 standard-only public theorem queries across 23 new modules, fresh root replay and twelve witness recipes; all 3801 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-66 `da445410` connects the initialized routed-send entry and first post-transmit crypt scheduler to their original continuations. Stopped crypted completion now retains a fixed worker prefix, matched ledger and cleanup debts. Native DEAD erasure carries an explicit pending receipt until its exact total emission suffix finishes on the same world; the old resident-cell account is proved inapplicable during that interval. Complete initialized internal-cut composition remains open. Validation: 3868 build jobs, 1527 terminal declarations, 65 standard-or-empty public theorem queries across 20 new modules, fresh root replay and twelve witness recipes; all 3821 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-67 `7e1ea08f` connects the original initialized routed front, its pre-receipt native world, post-transmit scheduler activation and TX-worker entry. The same paths retain fixed bounded loop prefixes, actual crypt-ahead execution, matching worker failure ledgers and original continuations. Local transmit paths also derive staging alternatives and partial-allocation intervals; other initialized caller roots and native interiors remain open. Validation: 3888 build jobs, 1530 terminal declarations, 94 standard-or-empty public theorem queries across 20 new modules, fresh root replay and twelve recipes; all 3841 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-68 `f11eadfe` connects the original selected return callback and post-transmit send drain to send-worker entries and their nested scheduler iterations. Direct encrypt activations and TX crypt-ahead retain the actual selected poll item, intervening softirq state, initialized encryption entry and original continuation; TX entries from both scheduler callers retain matched failure accounts. These are concrete entry bridges, not exhaustive native-interior coverage. Validation: 3904 build jobs, 1534 terminal declarations, 77 standard-or-empty public theorem queries across 16 new modules, fresh root replay and twelve recipes; all 3857 frozen hashes match. The 916 inherited proof files, main and mirror are unchanged.

Source-69 `2443f3be` connects the initialized routed front to its actual pre-release/trim/splice selection state. Every completed send-list prefix, including prefixes of successful calls, now retains its remaining-batch account, original completion-scope continuation and selected-worker packet capture on the same settlement chain. The combined root passes 3911 jobs and 38 focused standard-or-empty queries across seven new modules. These intermediate helpers do not close native-interior coverage. At that commit they had scoped validation only; source-70 below validates the combined delta.

Source-70 `14a5f051` connects ordered encryption packet prefixes and publication entry to initialization, retaining the original batch and enclosing callback receipt. Actual overflow prefixes retain the same ticket cohort through removal-before-charge, and the initialized overflow receipt restores the complete account before splice. The send drain now has fixed native points and exact normal/stopped execution decomposition, with initialized composition conditional on three named delivery, send-worker and scheduler source contracts. This is not T2 closure. The combined source-69/70 delta passes 3929 build jobs, 1539 terminal declarations, 161 standard-or-empty public theorem queries across 25 new modules, fresh root replay and twelve recipes; all 3882 frozen source hashes match. The 916 inherited files, main and mirror are unchanged.

Source-71 `8526e3e4` derives successful worker selection and every ordinary cleanup erase from initialization, consuming the already-recorded terminal debt at the native free. Encryption reads, byte writes and publication cuts retain the same batch and original runner continuation on normal and stopped paths. Peer release and purge retain their exact ordered cohort across native erasure and the later counted receipt; initialized publication reaches the fixed release prefixes with its original receipt origin intact. Canonical scheduler source points cover native bookkeeping and exact finite loops, conditional on the two named committed iteration and NAPI interior contracts. Other caller roots, remaining intervals and concrete child contracts remain open; this does not close T2. Validation passes 3967 build jobs, 1544 terminal declarations, 181 standard-or-empty public theorem queries across 38 new modules, fresh root replay and twelve recipes. All 3920 frozen source hashes match; the 916 inherited proof files, main and mirror are unchanged.

Source-72 `e1156284` connects initialized routed take, worker socket result and publication release-finish intervals to their original continuations. Silent queue clearing preserves the ordered ticket cohort until the actual receipt transfers it to selection; socket results retain one existing receipt and one settlement on the same ledger. Native take, restore and keepalive classifications preserve exact order, counters and birth ordinals. Peer release-finish covers the timer guard and both work-list writes, including the busy-timer stop with its existing receipt. Other caller roots, concrete child contracts and unexpanded stopped socket-front interiors remain open; this does not close T2. Validation passes 3987 build jobs, 1547 terminal declarations, 131 standard-or-empty public theorem queries across 20 new modules, fresh root replay and twelve recipes. All 3940 frozen source hashes match; the 916 inherited proof files, main and mirror are unchanged.

Source-73 `33251831` connects the initialized native dequeue setter to the original selected worker and runner. The exact cached cohort moves into the selected local on the same ledger before the existing write/removal events; those events add no terminal charge. Native peek/drop cases retain the actual first-read and queue-choice Stops. Canonical worker iteration now structurally fills the scheduler iteration contract, with all normal/Stop executions and source-built remainders; its eight deeper child contracts and external NAPI remain explicit. Other caller roots, child instances and remaining native intervals stay open. Validation passes 4003 build jobs, 1549 terminal declarations, 65 standard-or-empty public theorem queries across 16 new modules, fresh root replay and twelve recipes. All 3956 frozen hashes match; main, mirror and the 916 inherited proof files are unchanged.

Source-74 `e3028f49` connects initialized native peek, routed staging selection and runner boundaries to their original continuations. Canonical NAPI now supplies scheduler NAPI and iteration softirq/IRQ-exit contracts; staging and runner source trees retain exact normal/Stop cases and explicit deeper child obligations. The runner boundary account does not claim all native interiors. T2 and the remaining caller/interval worklist stay open. Intermediate validation passes 4037 build jobs, the 1554-declaration gate and 110 standard-or-empty public theorem queries across 34 new modules; all 3990 frozen hashes match. Main, mirror and the 916 inherited proof files are unchanged. Fresh root replay and all twelve recipes last passed at source-73 `33251831`; they were not repeated for this helper checkpoint.

Source-75 `223c63cf` closes the shared peer-release native point family: read, decrement, test, unlink, queue guard, erasure, receipt and release-finish retain their actual world and original continuation. Each cut has the same account or the exact pending receipt and successor; initialized publication and both NAPI/iteration release children use that proof. Canonical creation adds mark/install, EPIPE and refused-free joins; receive consumption and dispatch gain fixed source coverage, and dispatch composes with initialization. Universal creation/staging phase evidence, deeper native interiors and the remaining caller contracts stay open. T2 is not complete. The frozen 43-module delta passes 4080 build jobs, the 1557-declaration gate and 144 standard-or-empty public theorem queries. All 4033 frozen source hashes and 916 inherited files match; main and mirror are unchanged. Fresh aggregate kernel replay passes with retrieved exit 0, and all twelve counterexample recipes pass. This completes aggregate validation of the combined source-74/75 delta; the preceding full replay/recipes checkpoint is source-73 `33251831`.

Source-76 `62e82ce5` derives every canonical creation point from the original unpublished account and pending batch, retaining a successor of that same ledger. Receive endpoint/key/timer helpers and wheel placement now have concrete source coverage; peer release remains shared. Canonical timer services compose through dispatch and initialization. Delivery has no deeper child and its source points and original remainder are derived without callback assumptions; the send drain uses that concrete delivery contract and scheduler construction. Staging phases, lifecycle and other worker/caller interiors remain open, so T2 is not complete. The 53-module delta passes 4133 build jobs, the 1560-declaration gate and 176 standard-or-empty public theorem queries. All 4086 frozen proof hashes and 916 inherited files match; main and mirror are unchanged. Fresh aggregate kernel replay and all twelve counterexample recipes pass with retrieved exit 0. Aggregate validation completed at that checkpoint.

Source-77 `795e8829` closes every fixed encryption-ring polling point with the same ledger and original remainder. Queued initiation now joins concrete receive helpers, wheel placement and peer release; the initialized receive scheduler retains seven named deeper packet-source contracts. Core lifecycle roots derive their boundary coverage from actual entries, including the stronger retirement guard. Partial staging phases cover take, key borrow, nonce guards, restore and the original creation path; whole staging/keepalive and environment lifecycle wrappers remain open. T2 is not complete. The 46-module delta passes 4179 build jobs, the 1563-declaration gate and 157 standard-or-empty public theorem queries. Fresh aggregate kernel replay and all twelve counterexample recipes pass with retrieved exit 0. All 4132 frozen proof hashes match; main, mirror and all 916 inherited proof files are unchanged. Aggregate validation completed at that checkpoint.

[USER 2026-10-19] Carry main `3f3879e0` into the campaign branch and repair the affected proof frames; main itself and remotes remain unchanged. [AGENT 2026-10-19] Source-78 `df10ef27` preserves eleven helper modules before that carry: concrete environment lifecycle dispatch and scheduled work/service joins. Scoped builds (2836 and 3028 jobs) and all 58 public theorem axiom queries passed against the old mirror. At that intermediate point, source-77 was the last complete aggregate checkpoint and the results lagged the newly carried mirror.

Source-79 `8d9bfbca` combines the separate C3 carry with the eleven source-78 helpers and forty-seven staging, timer and prepare handoff modules. All are connected to the root build. Staging reserve/repayment/queue phases retain the original account and continuation; canonical timer callbacks retain purge and zero-key intervals; prepare retains RX residency and cached-peer obligations. Its canonical frame premise, deeper staging/timer children and the remaining caller contracts are still explicit. T2 remains open. The combined tree passes 4239 build jobs, the gate's 1563 terminal declarations across thirteen roots, 774 standard-or-empty public-declaration queries over the 85-module delta, fresh aggregate kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4192 frozen proof hashes match. Main and mirror are unchanged, and all fifty validated inherited carry paths are unchanged. C3's proved claims are now current over mirror `3f3879e0`, with their named assumptions and boundaries retained.

Source-80 `0fc64409` derives the complete preparation frame from the actual getters, RX residency and cached publication peer. Every fixed preparation point retains the same ledger and its original continuation, including writes before their access receipts; both outer history projections are carried into the shared hook. The initialized receive scheduler now derives its prepare contract and retains six explicit deeper families: receive staging, routed transmit, IPv6 receive, encryption, peer transmit and handshake. Finer native-atom interiors and the other caller/interval work remain open; T2 is not complete. The seven-module delta passes the 4243-job root build, the 1563-declaration gate across thirteen roots, all 43 standard-or-empty public-declaration queries, fresh aggregate kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4196 frozen proof hashes match. Main, mirror and all fifty validated inherited carry paths are unchanged. Development elaboration and history-normalization failures were repaired before these passing checks; no mirror finding arose.

## Current register

The proof tree is current over the namespace-pin landing `218d3ffd`: after
the fixed-width counter carries (campaign 2's owned carry and the shared
carry, landed at `eba3c2b6`), the shared carry for the namespace-pin fix
restates the runner's per-operation step in its seventeen source copies (the
pending-unit refusal in both record modes), the namespace close's and
cleanup's frames and sources (the holders cleared at the close; the teardown
only behind the queued unit), and the parser's copy (the reserved-descriptor
rule), and the gate passes. Request 5 is closed on the mirror side. One lag:
H5's namespace-pin recipe (`Progress/NamespacePinPending.lean`, run by the
counterexample speedbump, not by the gate) asserts the parser's former
acceptance of its reproducer and fails by design until campaign 2's
regression carry, which also owns the unrestricted pending-work clause over
the now-stated domain.

The Results table is the current claim register; historical validation
counts below it are not current pins. Campaign 1's [GRO report](2026-10-18-proof-gro-carry.md)
and [state-split report](2026-10-16-proof-state-split.md) describe the shared
layers, including the environment carry landed at `3308c49a`. Campaign 2's
[report](2026-10-14-proof-campaign-2.md) and [landing review](2026-10-20-review-campaign-2-landing.md)
describe its scope over `1a69cebb`. H5's unrestricted pending-work clause
remains refuted with an open environment request; this is a recorded finding,
not a proved quiescence claim. Each result's row below names its mirror pin.

## Historical state-split retrofit

The completed retrofit was validated over `b3f56807`, whose executable
mirror is identical to split landing `b700659` (the `6089dc4` split). All seven
results passed the complete proof gate and fresh root kernel replay. The
nondefault proof target and gate were retained through the split. R3 now includes initialized
incoming and outgoing authorization. R4 now covers normal initialized ingress dispositions and the named W7
full-ring episode. The six-result campaign has its proved or Rule Zero
counterexample dispositions; chronological GRO order remains refuted.

The validated baseline `00641c6` has 471 Lean files and 7,715 named theorems.
The validated retrofit checkpoint has 452 files and 6,564 theorems: 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added. The independent census accounts for
437 previously unclassified retained claims and removes seven duplicate retained
Enqueue entries. Private and attributed declarations are included; comments,
strings and tactic-local variables are excluded. The terminal surface has
517 declarations: 515 theorems and two definitions.

All 26 generic helpers and the additional update rule retain arbitrary actual
product-action scope. Concrete operations use their native worlds and monads,
with both WG and Ambient endpoints; type-derived foreign-subsystem frames and
their unused support are deleted. The retrofit retained all 141 R3 terminal names. R4 moves
from 129 to 131: its false cleanup-totality compound is withdrawn and three
separately named claims preserve its supported cuts, give the counterexample,
and state the successful-cleanup contract. The
[cleanup finding](2026-10-16-proof-state-split-findings.md#cleanup-totality)
does not refute the stronger actual-ENOSPC specialization or establish an
initialized reachable failure.

Stable receive retains all 39 theorem names and the original product physical
journal scope. Its 45 logical axiom checks and the combined 431-job R4 build,
131 R4 axiom checks and final fresh replay pass. Completed carries have scoped builds, named
axiom checks, fresh kernel replay and independent reviews. The final aggregate
gate passes all 510 build jobs and 517 terminal axiom checks; fresh replay of
Leanux.Proofs passes after compilation. The sole build warning is the existing
mirror-side String.mk deprecation. The [retrofit report](2026-10-16-proof-state-split.md)
records the contract changes, findings, failed development checks and validation.

## R3 extension history

The [current-identity extension](2026-10-17-r3-current-identity.md),
[reached-routing extension](2026-10-17-r3-reached-routing.md),
[current-journal extension](2026-10-17-r3-current-journal.md),
[receive-cuts extension](2026-10-17-r3-receive-cuts.md),
[configuration-cuts extension](2026-10-17-r3-configuration-cuts.md),
[caller-cuts extension](2026-10-17-r3-caller-cuts.md),
[lifecycle-cuts extension](2026-10-17-r3-lifecycle-cuts.md),
[scheduler-cuts extension](2026-10-17-r3-scheduler-cuts.md),
[initialized-owner extension](2026-10-17-r3-initialized-owner.md),
[consume-entry extension](2026-10-17-r3-consume-entries.md),
[publication-closure extension](2026-10-17-r3-publication-closure.md),
[initialized incoming extension](2026-10-17-r3-initialized-authorization.md),
[transmit source extension](2026-10-17-r3-transmit-source.md) and
[initialized transmit closure](2026-10-17-r3-initialized-transmit.md) add
210 modules and 2,595 theorems after the retrofit: 662 proof files and 9,159
theorems. The latest twelve exports preserve all 277 preceding R3 terminal
bodies; R3 has 289 and the full terminal surface has 665 declarations.
The proof gate passes 720 build jobs and 665 terminal declarations in 7.759
seconds. Fresh kernel replay passes in 105.8 seconds with no warnings.
That extension used mirror pin b3f56807; the current pin is in the register.

Native maintenance, receive, peer/device lifecycle and the actual stack
preserve supplied configured/current identity. Existing session, receive,
prepare, NAPI, crypt workers, scheduler and deferred timer/wait journals
preserve positional checks, including Stop prefixes. The fixture establishes
receiving-owner/RX bounds; concrete creation/session/index, admission/cleanup
and decrypt/prepare operations preserve them. The joint owner contract carries
these bounds with current checks and the existing R2 boundary on one journal.
Concrete receive, prepare, NAPI, decrypt/encrypt and transmit observers preserve
this supplied joint invariant. Consume completion and actual stack/poll retain
owner bounds; peer/device configuration and native lifecycle do so jointly
with current identity where creation requires it. Conditional publication
transport permits peer absence; normal consume proves
its own entry residency. Every syscall and the initialized typed runner now
retain both original observation streams without lower callback premises,
with the exact public JSON and indexed errors.
Supplied routing reaches consume and Stack-entry cuts in the same poll suffix.

All concrete outer calls and the original initialized runner preserve joint
current/owner checks for every typed trace and both placeholder modes,
including stopped prefixes. One joint runner journal now supplies those checks,
packet/receipt linkage and routing-completion safety. Actual consume entries
carry positional routing facts through the original poll; successful Some
receipts derive authorization from that exact earlier table.

Publication anchors and peer-frontier bounds now survive native admission,
sessions, handshake reception/sending, queued work, peer removal and actual
poll/Stack. Each consumed poll occurrence obtains a certificate under its
strict earlier history. Fixture, prepare, NAPI, crypt workers and handshake
receive iterations carry the combined owner/publication invariant. Scheduler,
deferred work, configuration, device lifecycle, dumps and every syscall now
carry it through the original initialized runner, for all typed traces and
both flags, including stopped prefixes. Each consumed occurrence obtains its
strict earlier publication certificate. A specified Stack-entry join connects
actual buffer, consume and decrypt positions. The initialized runner now
supplies routing checks at that consume position. Public parsing discharges
its address-shape premise. Thus every selected actual Stack entry has its
strict-prefix source winner and the same configured publication certificate,
including entries before a later Stop. Initialized outgoing authorization now
covers every selected completed staging handoff at its own routing prefix,
through direct, batch and Stack-reply callers, including stopped tails. The
concrete NAPI, crypt workers, scheduler, deferred work and syscall continuations
are connected to the original initialized runner. Public parsing supplies the
configuration shape premise; exact erasure retains JSON and indexed Stops.

## R4 extension history

The [full-ring closure](2026-10-17-r4-full-ring.md) adds five support modules,
one executable witness and eleven terminal exports after the
[initialized live-ring checkpoint](2026-10-17-r4-live-frontier.md):
916 proof files, 12,302 named theorems, 326 R4 terminals and 860 total terminal
declarations (858 theorems and two helpers). All previous theorem statements
and proof bodies remain unchanged. Nine obsolete R3/R4 status comments were
corrected; no theorem was retyped or deleted in this extension.

Every accepted initialized runner exposes original initialization, operation,
syscall and ingress cuts before carrier selection. Each accepted receive
admission has exactly one pending identity or an actual completed-poll
removal/release and named disposition, including admissions removed before
syscall return. Initialized allocation-stamp uniqueness prevents duplicate
Stack entries. Pending carriers are conserved work; eventual delivery or an
empty finite endpoint is not asserted. Chronological GRO order is refuted by
its accepted replay. Stopped prefixes retain the earlier receipt contracts,
without a returned World or a new funded endpoint account.

The named W7 episode is now connected through original batch, staging,
dispatch and activation source cuts. A kernel-proved payload-generic geometry
computes 1022 successes and two refusals from two uncleared carried slots.
The generated explicit-record replay is accepted by the original initialized
runner and checks the same two refused allocations through their later DEAD
head disposal and release, without completion. That concrete check is compiled
execution evidence; it is not a universal initialized TX-disposal theorem or a
Linux capture. Independent review accepts the repaired source connections.
The five-tier Linux comparison remains the mirror lane's separate result.

The complete proof gate passes 973 build jobs and all 860 declarations in
7.912 seconds. The final published W7 replay passes in 14.762 seconds without
warnings. Fresh root kernel replay passes in 112.641 seconds with no warnings.

## Layers

The tree is laid out by layer and by result. Shared layers sit at the top,
subject-specific layers under the subject, and each result in its own
directory whose `Statements.lean` is the gated surface.

Build counts and validation results in the module descriptions record their
original checkpoints. The current mirror/toolchain carry status is in
[Results](#results).

- `Leanux/Proofs.lean`: the root. It imports every result's `Statements`
  module and the checked counterexamples; `lake build LeanuxProofs` builds
  exactly this closure, outside the mirror's default build.
- `Leanux/Proofs/Framing/`: operational contracts over actual subsystem monads.
  `Hoare` supplies generic StateT contracts and exact native execution bridges;
  `Lift` describes the real subsystem and WG component adapters, including
  their Stops and precise field write-back.
  `Basic` and `WP` retain the lifetime distinction needed by reused keypair slots.
  `Allocation` and `Index` expose original source equations.
  `Projection` composes and factors equality views; `Tools` supplies generic
  loop/map rules and checked references to pinned mirror constants.
  Native socket/configuration frames retain the incoming eleven-field WG-owned
  observation in `WGOwned`; their explicit seven-field store view stays separate.
  WG source frames, borrowing contracts and environment frames use their actual
  native or product monads and retain the original store observations. The
  obsolete filesystem, signal, seccomp and
  ambient cross-subsystem layers have been deleted; the retrofit report records
  their type justifications and the unused support removed with them.
- `Leanux/Proofs/Logged/`: logged copies of mirror functions with erasure
  theorems (erasing the log gives back the original run, state, result and
  failure), from the validator (`Basic`, `RxPoll`) through the workers, the
  scheduler, the environment operations and the syscalls to the runner
  (`Runner`). The erasure core (`Outer`, `Tools`) is independent of what is
  logged. Validator observations carry acceptance events; `Checkpoints` observes
  arbitrary projections at committed operation boundaries, with exact erasure
  to the original runner and an exact singleton-append theorem. `Prefix`
  instead retains observations when execution fails, with exact original
  result/World or error erasure and compositional prefix-safety contracts.
  `PrefixOuter` retains observer history outside indexed Runner exceptions,
  with exact run/bind/erasure rules and an explicit two-branch WP bridge.
  `Focus` injects a local observer's new suffix into a combined event stream
  without changing the previous interleaving. `Projected` erases extra local
  accumulator data while retaining the original result, complete World and Stop.
  `ProjectsPrefix` compares two failure-retaining observers by projecting both
  their results and event histories, including every stopped prefix.
  `ProjectsUnder` adds exact invariant-conditional projection, unconditional
  appended-suffix/focus laws and untouched-history frames for joint observers.
  `FocusComposition` distributes focus using actual append contracts, with an
  invariant-conditional interface for lower observers and exact failed-prefix
  composition. It never assumes incoming-history independence.
  `PrefixGro` carries the original GRO state, batches and held packets with
  explicit callback erasure and preservation contracts. `PrefixLoops` gives finite range
  and map/fold composition plus accumulator-dependent list-loop contracts for
  failure-retaining observers. `Capture` retains exact original-action run
  witnesses with erasure and prefix contracts. `PrefixWorkers` composes one
  original worker iteration with explicit step and rescheduling contracts.
  `PrefixBatch` shares exact worker-section observations and callback preservation.
  `TimerPass` observes completed original timer, clear/send-worker and crypt
  scheduler calls, retaining exact before/after Worlds and failure erasure.
  `Advance` preserves the complete original advance syscall, including its
  seccomp/dispatch/task-work prefix and recorded timer-unit observations; its
  placeholder path is lifted without a unit-coverage claim.
- `Leanux/Proofs/WG/CounterWindow/`: the receive counter window as a pure
  model of `counter_validate` (`Model`), its refinement to the mirror's
  `counterValidate` (`Refinement`, the S2 theorems), and replay freedom for
  finite sequences of validator calls (`MirrorCalls`).
- `Leanux/Proofs/WG/Keypairs/`: the keypair store projected with allocation
  lifetimes (`Lifetimes`, `LifetimeMirror`), the ordinary steps that may
  allocate or delete a slot but never alter a surviving window (`Ordinary`,
  `OrdinaryHot`, `OrdinaryRules`, `SnapshotRules`); `Frames/` holds the
  per-function frame contracts over that projection for WireGuard and the
  environment; `Evolution/`
  carries the acceptance-history invariant through the observers, the
  scheduler, the operations, the runner and the syscalls.
  `MaterialOrigin` supplies exact allocation/frontier and receiving-material field rules plus a shared receipt
  journal. `SessionOrigin` captures the original session entry through derivation with actual nullable-word,
  allocation and peer-read linkage, before later zero/rotation/index failures. `Packets/RxOriginCuts` captures
  original admission through allocation and the actual stored getter/decrypt cut, retaining full packet/World
  witnesses, exact AEAD/material and state-only publication equations. Original erasure is unconditional;
  receipt validity is preserved from valid incoming history (empty qualifies). Full R2 projection uses
  its existing AllocationInv on the same projected incoming history.
- `Leanux/Proofs/WG/ReplayWindow/`: the first result (below).
- `Leanux/Proofs/WG/AntiReplay/`: campaign R1, uniqueness and the inclusive
  lower edge; reusable arithmetic is in `CounterWindow/Bounds`, and ordered
  acceptance-history bounds in `Keypairs/Evolution/Bounds`.
- `Leanux/Proofs/WG/Lifetimes/`: generic allocation frontiers, old-identity
  provenance and removal (`Store`), with projection contracts and composition
  over actual original helper executions (`Actions`). `WG/Packets/Primitives`
  covers the eight skb-store helpers within one device epoch;
  `WG/Peers/Primitives` covers getter/setter identity and reference helpers;
  `Peers/Frames` carries live identities through initialization, and
  `Peers/Allocation` gives exact original peer creation and finite-sequence
  allocation/reference contracts. `Lifetimes/Events` expresses
  release-before-access exclusion over allocation stamps. `Peers/Access`
  observes every peer-store access in the original `peerPut` and
  `wgGetDeviceDone`, including prefixes ending in errors; its finite caller
  family contains no allocation or device lifecycle. `Peers/CreationAccess`
  extends it with exact allocation/initialization observations and original
  `peerCreate`, retaining released-history bounds through failing prefixes.
  `Lifetimes/Tagged`, `MixedAccess`, `MixedFrames`, `Acquire` and `Enqueue`
  combine peer, keypair and epoch-tagged packet access histories through the
  original receive-enqueue helper, under an explicit callback contract.
  `KeypairAccess`, `Decrypt` and `DecryptWorker` extend this through packet
  decryption and one original decrypt-worker iteration, including failures.
  `IndexOwnerAccess` observes the actual embedded peer-word getter, the setter's
  fresh owner getter/write and the NULL-sensitive dereference, below the release
  and lookup modules. Dereference resolves the owner only. The `de62c9d` carry
  threads these unconditional erasure and ambient identity contracts through
  lookup, session, maintenance, receive/TX and the separate Logged/joint observers;
  exact put-event histories retain both NULL Stops. Creation accepts optional peer
  words, including `none`; initialized R2/R4 domains are unchanged.
  `ReleaseInvariant`, `KeypairRelease`, `PacketRelease` and `ReleaseCalls`
  add exact acquisition/release observations and finite compositions of the
  original keypair reference, packet-free and keypair-clear calls. `Ambient`
  separates caller preservation from the chosen history invariant;
  `ReleaseAmbient` instantiates enqueue/decrypt with release uniqueness.
  `AllocationInvariant`, `KeypairAllocation` and `PacketAllocation` establish
  complete original allocator observations and safety with slot, lifetime and
  epoch bounds. `AllocationFrames` transports identities, metadata and released
  sets separately; `AllocationInitial` covers runner fixtures and prefill.
  The former FilesystemLocal/FilesystemCalls wrappers and six terminal exports
  are removed. Actual FS operations and taskWorkRun use native monads; their
  product lifts preserve WG by type separation and retain exact FS/Task/Ambient
  outcomes and Stops. Generic observer lifting retains incoming history.
  The dispatcher, complete syscall and Runner compositions now use their
  actual product actions; their scoped carry is checked. Task work keeps
  pop-before-release and its exhaustion Stop;
  fputFinal may queue netnsCleanup, whose later product-level execution is
  supplied by the Env, syscall and Runner layers.
  `AllocationRetention`, `AllocationReleaseFrames` and `AllocationReleases`
  retain allocation bounds across reference/free calls using entry-resident
  release origins. `AllocationAmbient` instantiates shared caller contracts
  for the release family, receive enqueue and decrypt iteration.
  `KeypairRotation` and `Session` cover original keypair rotation, confirmation
  and complete session creation; `SessionFailure` gives the exact retained
  prefix when the birthdate clock fails after allocation. `PeerAllocationFrames`
  and `PeerAllocation` reuse the existing complete peer observer at
  `AllocationInv`, with original creation geometry and slot bounds;
  `PeerAllocationFailure` retains the initial allocation/write at cache-clock
  failure. `LookupAccess` covers optional-peer, index and public-key lookup;
  `ReceiveEntry` covers complete device/peer enqueue and `consumeData`, with
  `ReceiveEntryFailure` retaining the exact queue-record failure prefix.
  `MaintenanceTimers`, `ReceiveMaintenance` and `MaintenanceCalls` cover
  endpoint/cache, receive-timer and queued-handshake calls, including safe
  failure prefixes and the original timer guard's unconditional peer read.
  `TxAccess`, `TxContracts`, `TxEnqueue`, `TxStaging` and `TxStagingCalls` cover
  TX setter events and the seven complete staging callers, with explicit
  scalar-update contracts and concrete allocation-invariant preservation.
  `EncryptWorker` adds complete packet encryption and worker step/iteration
  observers with explicit checksum, softirq and rescheduling contracts;
  `Framing/WGData` discharges the concrete checksum and padding frames. Consumed
  encrypt-ring replacement has its own allocation frame, separate from produce.
  Failed prefixes retain every resolved access; saved-head association and
  ownership are not asserted. Concrete Batch composition now discharges those
  worker callbacks; initialized Runner composition is supplied by RunnerSafety.
  `TxCompletion` and `TxWorker` add the five TX completion helpers, worker step
  and iteration, with complete socket observers and explicit rescheduling.
  Exact failed prefixes include the peer read before a jitter Stop. The shared
  jitter frame is proved over the full Kernel and projected into the legacy
  snapshot interface. Coordinated validation, fresh kernel replay and independent
  frozen-source review pass.
  `HandshakeConstruct`, `HandshakeConsume` and `HandshakeCalls` observe the
  five original Noise constructors/consumers and MAC addition with their actual
  result types, fresh accesses, reference-taking lookups and failure puts. The
  index frame concretely preserves `AllocationInv`; a failed cookie-age test
  retains the earlier MAC1 read/write. Coordinated validation, fresh kernel replay
  and independent frozen-source review pass.
  `HandshakeSend` composes the original buffer send, two timer helpers, initiation,
  response and send worker, retaining ordinary refusals and failed access prefixes.
  Its explicit socket/index/session contracts have concrete allocation instances;
  initialized Runner composition is supplied by RunnerSafety; saved-reference affiliation is a
  separate stronger property.
  `CookieAccess` covers make/create/validate/consume with exact result and failed
  prefix preservation. `Framing/WGCookie` retains the full Kernel except cookie
  secret/birthdate and both ratelimiter tables; legacy frames are projections.
  Ambient cookie stability is explicit and concretely discharged for allocation
  safety. `HandshakeReceive`, `ReceiveWorker` and `ReceiveIngress` compose full
  local receive processing, iteration/bounded workers and UDP/packet entry.
  `BatchNapi`, `BatchActivation`, `BatchScheduler`, `BatchTrials` and `BatchCalls`
  now compose the concrete Batch scheduler with exact erasure and allocation safety.
  Copied-World trial filters have separate execution and access-safety contracts;
  their histories are discarded. `Audit` and `BatchAudit` add a failure-retaining
  sum stream of committed lifetime events and actual consistency-filter entries.
  Saved entries retain their own World/history allocation facts through later
  mutations. The literal filter emits one marker before executing the original
  filter, including empty lists and Stops. Concrete schedule, nested-reschedule
  and receive-worker observers erase unconditionally, project to the existing
  committed observers from an allocation-valid entry, and retain safe prefixes.
  From empty history and local AllocationInv, every recorded entry supplies the
  premise of the exact ordered trial-filter and isolated trial-safety contracts.
  Coverage comes from the source placement and exact filter-entry equation,
  separately from projection. Result-dependent focus and generic finite-loop
  projection support later callers. RunnerSafety supplies initialized whole-run
  access closure; reference affiliation is a separate stronger property.
  `SavedPeerLookup` observes captured-map lookups per scalar peer-list occurrence:
  Some emits one saved read, None emits none, and duplicates repeat. `EnvWorkersAudit`
  composes original queue guards and deferred send/clear/crypt workers through the
  audit scheduler; `EnvTimersAudit` covers full fire/recorded/placeholder dispatch,
  idle and advance with all source bounds and failures. `Environment/TimerSource`
  shares literal post-scan and placeholder cuts, including the original pure fold.
  `Framing/EnvLeaves` gives complete Kernel bookkeeping frames and legacy projections.
  `EnvDeferredCalls` groups fifteen typed originals with unconditional erasure,
  concrete AuditInv failed-prefix preservation and local reached-trial safety.
  `EnvControlsAudit` covers up/down/delete, MTU/address/routes, namespace cleanup
  and the exact observation tail after idle. `Framing/EnvOperations` retains full
  resident stores/frontiers, masking only MTU/inet-family scalars where needed;
  canonical `dropHiddenRecord` keeps the actual World ordinal effect. Legacy
  frames project these contracts. `EnvTrafficAudit` observes multicast loopback,
  the complete inline saved-peer scan, inject and exact flood; every producer uses
  the actual ingress and inline poll, and afterBatch retains actual deferred
  scheduling probes. `EnvBatchAudit` preserves captured device scalars,
  partial CQEs and deferred-worker order. Source-only `ObservationSource` and
  `BatchSource` retain exact original continuations/item loops. `EnvRemainingCalls`
  groups these fifteen originals with unconditional erasure, concrete AuditInv
  failed-prefix safety and local reached-trial facts.
  `SyscallWrappersAudit` composes literal callback-parametric socket/netlink/
  rtnetlink wrappers with original ordinary-negative cleanup and Stop cuts.
  `Framing/Syscalls` supplies the full WG frame for the original four-close
  netnsClose, projecting its legacy snapshot API; queued cleanup stays in Env.
  `SyscallDispatchAudit` covers all 34 typed constructors (35 dispatch arms),
  using concrete FS/seccomp frames, focused WG calls and actual Env observers;
  netlink autobind socket records use the dump mask. `SyscallsAudit` preserves
  the original reset, seccomp entry/tail calls, task work and postworkers.
  Three grouped contracts retain unconditional erasure, AuditInv failed-prefix
  safety and actual reached-trial facts. RunnerSafety supplies initialized composition without parser, ownership,
  valid-descriptor or drain premises.
  `AllowedIpsAccess` observes six original list/removal calls, including every
  demanded saved-map entry interleaved with its hit write, original owner reads,
  and exact failed prefixes. `Framing/WGAllowedIps` masks only nodes/trie roots
  and sequence, retaining full resident stores and all allocation frontiers;
  legacy frames project the canonical contracts. Concrete `AllocationInv`
  discharges node stability and scalar peer-list/hash updates. RunnerSafety supplies initialized composition. This extension's
  coordinated gate, fresh kernel replay and fast-tier validation pass.
  `AllowedIpsInsert` covers complete original add/insert, including exact-owner
  rewrites, demanded saved-map reads, allocation refusals and partial rollback.
  Canonical `Framing/WGAllowedIpsInsert` additionally masks the node frontier,
  retaining all tracked residents and allocation geometry; legacy frames project it.
  `ConfigurationLeaves` and `ConfigurationPeer` cover setPort, setAllowedip and
  complete setPeerCmd with exact ordinary-negative cleanup and failed prefixes.
  `WG/Configuration/PeerSource` shares the literal source stages without lifetime
  or routing imports. Six new grouped exports have concrete AllocationInv
  discharges and no routing/address/attribute-validity premises. Scoped/full
  targets pass 238/372 jobs; independent frozen source/documentation review is
  clear. Coordinated proof gate, fresh kernel replay and fast-tier validation pass.
  `ConfigurationDeviceFrames` and `ConfigurationDevice` extend those same three
  exports to complete original wgSetDevice. Canonical `Framing/WGConfiguration`
  masks only static identity, device cookie/MAC keys, update generation and fwmark;
  legacy frames project it. The existing peer precomputation observer is focused
  into mixed history with concrete metadata transport. Original-only
  `Configuration/DeviceSource` shares the exact preflight/update/private-key/peer
  continuations. Generation-before-error, old-peer put-before-remove, saved-ID
  loops and ordinary-return zero-key records retain their source order, without
  valid-attribute, routing, ownership or progress premises. Component/scoped/full
  targets pass 178/246/386 jobs. Independent frozen source/documentation review
  is clear; coordinated proof gate, fresh kernel replay and fast-tier validation pass.
  RunnerSafety supplies initialized composition.
  `KeyMaintenance` covers reset, handshake clearing, current-key expiration and
  queued clearing; `TimerCallbacks` covers all five expired callbacks and their
  dispatcher. Exact erasure retains clock/getter order and all failed prefixes;
  explicit scalar-index, keypair-release, staging and work-queue contracts have
  concrete `AllocationInv` discharges. Own-timer detachment, reference
  ownership and outer lifecycle composition remain separate. Six new grouped
  exports pass the 226-job scoped Statements and 334-job full proof targets;
  coordinated gate, fresh kernel replay and fast-tier checks also pass.
  `PeerRemoval` composes both flushed workers, the exact 4096-step send-workqueue
  drain, timer stop and complete after-dead/optional/all-peer removal. Queue
  erasure/pending reset precede sections, and both passes retain the saved scalar
  IDs with current-store accesses. Scalar queue/count contracts have concrete
  `AllocationInv` instances; no drain-progress or ownership premise is added.
  Three grouped exports pass the 227-job scoped and 340-job full proof targets;
  independent source/documentation review and coordinated validation pass.
  `DeviceControls` composes socket free/reinit/init, device open/up/stop/down
  and namespace pre-exit, with exact result/World/Stop erasure and concrete
  allocation safety. Saved scalar peer-ID loops preserve each original fresh
  access, and ordinary negative returns differ from Stops. The canonical
  `Framing/WGSocketLifecycle` mask omits only socket labels and incoming port;
  unchanged legacy frames are projections. The socket lifts are separately
  source-inspected for access coverage. Three grouped exports pass the 229-job scoped and 349-job full targets;
  independent review and coordinated validation pass.
  `DeviceRetirement`, `DeviceCreation` and `DeviceLifecycle` cover complete
  guarded create/destruct/delete. Exact retirement events name the actual
  pre-drop peer/keypair/TX/RX stores at the final original `wg := none` cut.
  Successful creation establishes a fresh empty epoch without imposing the
  allocation invariant at provisional setup; existing-device/refusal returns
  and all Stops retain their original behavior. Canonical `WGDeviceLifecycle`
  initialization/ratelimiter frames supply unchanged legacy projections.
  Four grouped exports pass scoped/full targets of 233/362 jobs, independent
  frozen review and coordinated validation.
  RunnerSafety supplies initialized caller coverage.
  `CounterAccess`, `AllowedLookupAccess`, `ReceiveCompletion` and `ReceivePoll`
  cover the complete validator, routing lookup, receive completion and polling
  with an explicit callback contract; `ReceiveFailure` retains the exact
  malformed-bitmap failure prefix. `SavedPeers` records demanded saved-map
  reads with a residency premise; `SocketFrames`, `LoopbackAccess`, `SocketCache`,
  `SocketSend`, `SocketSend4` and `SocketCalls` cover eleven complete
  cache/endpoint/loopback/tunnel/IPv4/IPv6 callers and their failure prefixes.
  The IPv4 observer uses exact source tail stages and retains both endpoint
  accesses before a reset-clock failure. `DeviceXmit` and `StackAccess` observe the
  complete transmit entry, actual stack callback and receive poll using that
  callback. RunnerSafety supplies initialized caller coverage.
- `Leanux/Proofs/WG/NetlinkDump/{Source,DeviceSource}` retain literal original
  serialization/header/peer-walk cuts. `Framing/WGDump` proves complete read-only
  Kernel frames and masks only the two netlink socket records, with unchanged
  legacy projection APIs. `Lifetimes/DumpAccess` covers all seven original dump
  calls with typed exact erasure, demanded cursor/peer observations, ambient
  contracts and concrete allocation-safe failed prefixes. New-cursor acquisition,
  old-cursor put, queue-before-done and pop-before-next-dump retain source order;
  no cursor-affiliation or drain premise is introduced. Component/scoped/full
  builds pass 176/255/401 jobs and independent frozen source/export review is
  clear; coordinated gate, fresh kernel replay and fast-tier validation pass.
- `Leanux/Proofs/WG/LifetimeSafety/`: campaign R2 lifetime safety: keypair store
  absence/freshness at original operation endpoints (`Keypairs/Identity`),
  peer/packet helper-family contracts, and a checked local stale dump-cursor finding with historical runner reachability; its full recipe is now rejected.
  Complete local handshake receive/worker and UDP/packet ingress compose the
  existing observers with explicit rescheduling contracts; concrete Batch scheduling
  discharges its internal worker callbacks. The audit scheduler derives reached
  copied-trial entry invariants locally; the syscall layer carries these facts.
  `RunnerAudit` retains the literal initialized Runner, indexed errors and JSON;
  `RunnerSafety` discharges initialization/prefill and every concrete syscall,
  preserving AuditSafe on success and failure. Its three grouped exports cover
  every typed Trace and both booleans, with no parser, length, progress or success
  premise. Actual reached markers yield saved-entry validity, exact ordered
  filter correspondence and safe isolated trial histories. Source coverage
  remains distinct from erasure; scalar affiliation/credit is not asserted.
- `Leanux/Proofs/WG/AllowedIps/`: width-parametric prefix arithmetic (`Prefix`)
  and exact original-helper execution equations (`ArithmeticMirror`); `Tree`
  proves longest-prefix lookup, canonical-prefix uniqueness and depth bounds
  from local structural validity. `Store` represents exact node values and
  backlinks; `LookupMirror` proves total correctness of the original traversal.
  `Insertion` preserves validity, compression and fresh identifiers while
  replacing exactly the requested canonical prefix in the pure tree.
  `StoreMutation` and `MutationMirror` connect original empty-root insertion
  to that tree, including normal allocation refusal and sequence increments.
  `Context` and `PlacementMirror` prove total original node placement and its
  exact-match, stopped-graft and known-empty-focus relationships to insertion.
  `ChildMutation` and `ChildStore` refine original insertion at a root's immediate
  empty child, preserving both family representations and composing with lookup.
  `DeepChild` and `DeepChildStore` extend the empty-child case to arbitrary
  represented depth using context replacement and ID separation; the original
  `insert` wrapper preserves its sequence update on success and refusal.
  `ListsMirror` gives total original list deletion and exact pointwise effects.
  `ExactMutation` and `ExactStore` refine original exact-prefix replacement at
  arbitrary depth, preserving old node fields and linking insertion to lookup.
  `GraftMirror` and `GraftStore` classify original selected-root graft returns
  and give exact rollback effects, including the consumed node identifier and
  all-peer list filtering. `GraftSuccess` connects both successful selected-root
  grafts to pure insertion, bounds the resulting store, preserves the opposite
  family and composes original actual-root lookup with the flat-list specification.
  `GraftLink` and `DeepGraft` extend nonempty child grafts to arbitrary depth,
  with exact source-tail factorization, normal allocation-refusal endpoints,
  successful representation and actual-root lookup.
  `InsertionCases` reuses the established branch contracts; `InsertionDispatch`
  derives every bounded-input normal-return case from total original placement,
  retaining exact refusal/rollback effects and common successful representation.
  `InsertionMetadata` derives exact peer-map and Device-frame fields for that
  common outcome; `InsertionEntries` supplies binding-ID origin and entry
  correspondence. `InsertionCoherence` derives fresh-ID absence and resident list
  coherence from represented input. `RoutingInvariant` combines both family
  representations, validity/compression/Nodup, coherent lists and node/peer/owner
  frontier bounds; `InsertionRouting` preserves it through original bounded-input
  normal insertion, both normal refusals and complete peer removal. Owner bounds
  allow orphan raw labels; rollback preserves coherent stores pointwise while
  retaining its consumed ID and the wrapper sequence increment.
  `RoutingView` retains device/list absence and exact routing fields;
  `RoutingLifecycle` derives original creation/refusal and raw-release effects
  and invariant preservation. `RoutingInitial` establishes the invariant from
  the original configured fixture. `FlatHistory` uses canonical prefix bits and
  raw owners without node IDs; `RoutingHistory` chains actual normal calls and
  returns, deriving all intermediate coherence/agreement from the fixture.
  Reached-root original findNode returns a flat-history winner and its actual
  raw node owner. Input bounds/residency are explicit only for insertion;
  whole device-command composition is supplied by the later completion layer.
  Later optional-state contracts cover guarded device lifecycle; initialized
  syscall/Runner composition is supplied below, while packet paths remain open.
  `AddressBounds` proves the actual UInt8 fold bound and pins the original private
  parseAllowedIp; `ConfigurationInputs` derives selected-family insertion bounds
  from actual setAllowedip guards and composes normal returns with routing/flat
  preservation. `ClearWalk` factors the original root-list traversal, proves
  normal-return coverage/list clearing and preserves the full list-only frame.
  `ClearSnapshot` retains original node values, current-node submap and resident-list
  provenance/exclusions through both saved-root phases. `ClearEndpoint` derives
  complete normal WG.free: empty represented families and resident lists, seq+1,
  unchanged frontiers/full other fields, and node deletion only. `RoutingCall.clear`
  empties the independent flat tables in initialized finite histories. Enclosing
  configuration closure, traversal totality and failed Worlds are not asserted.
  `RoutingRetains` permits peer deletion while preserving nodes/table/frontiers
  and survivor lists; it derives invariant/flat transport. `RoutingCompletions`
  observes actual whole setAllowedip returns with exact signed results/views and
  semantically valid flat prefixes. `RoutingSendFrames` derives concrete original
  send/cleanup frames. Shared `Configuration/AllowedIpSource` factors the original
  tail; `PeerTailRouting` and `PeerTailCompletion` cover its allowed-IP loop, early
  cleanup and full keepalive/staged-send suffix. Erasure is unconditional; semantic
  prefix safety and normal reached-state agreement use explicit entry routing,
  resident target and local attribute shape. No failed World or enclosing closure
  is asserted.
  `RoutingSocketFrames`, `RoutingHandshakeFrames` and `RoutingFlushFrames` derive
  concrete normal routing frames through both socket families, handshake/key-clear
  work, the actual bounded drain and final peer cleanup. `RoutingAcquire` separately
  derives raw-slot residency from actual lookup/create outcomes. The completion
  sum includes nested removeByPeer; `Configuration/PeerRemovalCompletion` and
  `PeerUpdateCompletion` cover peer death/removal and the complete acquired-peer
  update stage. `PeerCommandCompletion` composes the literal public preflight
  through an internal acquisition suffix, deriving target residency from actual
  lookup/create outcomes. `ParserShape` propagates the actual private parsers and
  operations accumulator through public parseTrace; its literal suffix factor has
  an rfl source equation. Parsed peer commands therefore need no extra address-shape
  premise. `RoutingDeviceFrames` projects existing configuration/socket masks and
  proves endpoint-cache/key-expiry frames. `Configuration/DeviceCompletion` composes
  all four original DeviceSource cuts, including a completed free before both saved
  remove-all loops. Normal clear/remove-all also leaves the journal's flat tables
  empty. Public parsing discharges shape for complete device commands; routed
  present-device entry is retained by those local contracts. `RoutingGlobal` adds
  absence with empty folded tables, without changing completion validity.
  `RoutingDeviceLifecycleFrames` derives guarded creation and deletion-permitting
  down/stop frames from original calls. `Configuration/LifecycleCompletion` proves
  absent whole peer/device commands retain their entry journals, and composes actual
  destruction/deletion with clear before final device drop. Arbitrary fixture rows
  remain permitted; direct invalid allowed-IP completion is not generalized to absence.
  All initial fixture modes and successful seccomp prefill establish optional routing.
  `RoutingTxFrames` and `RoutingRxFrames` derive original TX completion/worker,
  transmit entry, concrete Stack, receive completion/poll and decrypt-worker
  routing retention. Surviving peer lists are preserved while peer deletion is
  permitted. Generic checksum/GRO/IRQ/softirq/rescheduling callbacks require their
  own frames; actual checksum and Stack callbacks are discharged. Whole-call lifts
  preserve optional completion state on normal return and leave the journal
  unchanged on every outcome, retaining only prior history safety on Stop. They
  do not assert a failed World, packet authorization or enclosing scheduler closure.
  `RoutingAdmissionFrames` covers actual index acquisition, receive enqueue,
  consumeData and complete wgReceive, including normal EPIPE/ENOSPC cleanup.
  `RoutingNapiFrames` closes both actual direct poll callers, IRQ-exit placement
  and crypt iterations with concrete checksum/Stack/rescheduling callbacks.
  `RoutingMaintenanceFrames` covers all five timer callbacks and device open/up/
  namespace exit. These original normal-endpoint frames require no residency,
  affiliation, credit, saved-list or drain premise. Their whole-call lifts preserve
  optional completion state on normal return and leave history unchanged on every
  outcome; Stop retains prior history safety without a returned World.
  `RoutingSessionFrames` proves routing equality for the eight original keypair,
  index, session, response and session-timer helpers. `RoutingNoiseReceiveFrames`
  factors the canonical cookie frame and permits peer retirement in incoming
  initiation/response/cookie cleanup. `RoutingHandshakeReceiveFrames` reuses the
  exact cookie/load factor and a local checked MAC/switch cut, deriving complete
  handshake receive, queue-step and actual receive-worker iteration frames.
  No residency, affiliation, credit, valid-packet or drain premise is added.
  Their silent lifts preserve optional state on normal return and retain unchanged
  prior safe journals on Stop, without a failed World or authorization claim.
  `RoutingSchedulerFrames` derives cryptAhead, all activation iterations, complete
  run/dispatch/schedule and nested-reschedule frames by instantiating the exact
  SourceScheduler contracts with a fixed input routing view and extracting through
  erasure. Copied consistency trials keep their original Stops; no successful-trial
  premise is needed. `RoutingEnvWorkersFrames` composes actual deferred workers,
  queue checks and afterXmit, using fresh getter facts at setters.
  `RoutingEnvTimersFrames` shares the exact timer scan/fold source factors and closes
  both timer modes, idleTimers and afterAdvance with concrete callbacks. These
  all-input normal frames add no residency, affiliation, credit or drain premise.
  Their whole-call lifts preserve optional state on normal return and leave the
  journal unchanged on every outcome; Stop retains only prior history safety.
  `RoutingEnvTrafficFrames` closes the complete receive worker with actual nested
  rescheduling, the exact flood path, injection and literal batch item/full submission.
  `RoutingEnvControlsCompletion` factors the exact MTU conversion/control masks,
  observation and namespace worker, and observes actual lifecycle completions inside
  Env.wgDelete after its idle/pending-dump guards. `RoutingDumpFrames` reuses literal
  header/tail cuts and socket/serialization masks through stepped and whole dumps;
  cursor releases may retire peers without a validity or drain premise. These
  silent frames preserve optional state normally and prior safe journals on Stop;
  deletion retains actual completed events.
  `Configuration/SyscallCompletion` observes original socket/netlink/rtnetlink
  wrappers, every dispatch arm and the full syscall suffix. Ordinary negative
  returns keep actual cleanup; Stops retain the completed prefix.
  `RunnerCompletion` returns JSON with the actual final accumulator World and
  proves full-result erasure to a literal source Runner, whose JSON projection
  equals original executeTrace. `RunnerRouting` derives initialized safe history
  on every outcome and normal GlobalCompletionState from TraceAddressShape;
  actual array cursor membership supplies each operation's shape, and successful
  public parseTrace discharges it. Erasure has no shape premise. Earlier executed
  lookup certificates, packet authorization, affiliation and copied-trial packet
  claims remain separate; the final World only supports fresh hypothetical queries.
  `Peers/Affiliation` projects nullable handshake/key words, peer/key frontiers,
  resident slots and packet references. The local invariant permits NULL and absent
  referenced objects; it imposes no index-table bounds or allocation-stamp uniqueness.
  Actual index lookup preserves it through fresh owner store-back, including aliasing,
  and a successful handshake lookup returns that owner. `Keypairs/Affiliation`
  derives optional allocation, aliased slot rotation and original beginSession
  preservation from actual getter facts. `Packets/AffiliationCuts` gives literal
  staging/receive source factors, local acquisition contracts and the exact successful
  decryption field/AEAD equation. OwnerCertificate retains full snapshot records;
  its helper-run premise is separate, and later NULL does not alter those historical
  snapshot facts. Initialized reachability, unique allocation history, complete
  packet affiliation and earlier executed routing certificates remain open.
  `AllowedIps/LookupExecution` refines the original acquiring lookup and both
  address wrappers to a flat winner under local reached-World routing agreement.
  Failed acquisition remains a Stop; a normal answer needs no liveness premise.
  `Packets/AddressShape` derives family/destination-byte shape for every original
  xmitPackets/GSO packet and rst4 reply, and preserves source/family through actual
  ECN rewriting and complete-header trimming. `Packets/RoutingCuts` factors the
  literal consumeDataDone and wgXmit calls. Normal RX output retains its actual
  input/output family and source winner. Normal TX zero return exposes exact
  query/selection/splice/tail Worlds, the original packet list with its supplied
  MTU, and every actual destination guard. This is local staged handoff, not
  initialized history, authenticated key ownership or later wire-send routing.
  Original insert then agrees with actual-root longest-prefix lookup. Supplied
  opposite-family representation is framed without inferring its root linkage.
  `Removal` implements pure ID erasure with exact entry filtering, node-ID
  subsequence, validity/compression and filtered longest-prefix lookup.
  Removal also bounds ID retirement by two under compression and uniqueness.
  `ContextRemoval` derives local compaction and unchanged outer contexts
  under those premises. No original removeByPeer execution is asserted by these pure laws.
  `Origins/State` couples material and nullable keep-or-clear owner to one full
  successful session-front witness. Valid post-key retention permits invalid allocation,
  invalidation, deletion and absence. `Origins/SessionMaterial` recovers the actual entry
  Peer/state/word, installs support at the completed front, and retains it through the tail
  and successful decrypt. Combined local adapters preserve original erasure, same-input R2
  projection under its existing AllocationInv, and receipt truth from valid input history.
  Successful decrypt appends its actual packet/run after a material receipt in that supplied
  journal; incoming support does not establish initialized occurrence provenance.
  `Origins/IndexMaterial` now derives actual owner-acquisition and whole index-lookup
  material retention from exact read/borrow/fresh-store equations, including NULL store-back.
  The existing access adapter preserves supplied session support on normal return and valid
  receipts on Stop. No affiliation, credit or resident-owner premise is added to the source
  frame. Initialized configured identity and uniqueness remain open; owner clearing
  does not identify the packet peer with the session peer.
  `Origins/ReceiptTypes` retains the existing qualified receipt data below the caller import cycle.
  `Origins/HandshakeSources` factors the original response/after-MAC/reception/receive-step source and its
  lifetime observer. `Origins/HistoryAdapters` injects actual session/decrypt receipts once into the persistent
  RX history: both receive-worker entrances and decrypt preparation use it. Same-input projection retains all
  audit events/probes; the old R4 metadata decoders and concrete protocols retain their meanings. Local validity
  requires valid incoming receipts. RX admission injection, configured identity and copied-trial
  origin coverage remain open; initialized committed material support is established below. Protocol.origin is an explicit internal generic API strengthening, discharged by
  both existing concrete R4 instances; it is not implied by the old audit/poll fields.
  `Origins/RetainingLeaves`, `RetainingTraffic` and `RetainingLifecycle` prove concrete normal-return
  retention for full receiving material/stamp/epoch and nullable owner, allowing invalidation and erasure.
  Exact getters justify cached key writes; both concrete NAPI sites and crypt callbacks, Stack/TX/RX,
  clear/removal/flush, five timers and guarded create/destruct/delete are covered. SameSnapshot and
  routing-only frames are not used as material evidence. Supplied `Origins.Inv` transports normally;
  Stop has no returned World. Session installation uses its separate receipt contract; configured identity remains separate.
  `Origins/HistorySupport`, `SupportCallers` and `SupportEnvironment` now compose supplied material support
  on the unchanged persistent observer. Exact strict-prefix checks relate each stored decrypt to its captured
  entry World and earlier full session/material witness; successful decrypt retains its packet/key/AEAD equations.
  Saved filter entries retain the exact prior lifetime projection and support at their saved Worlds, even on Stop.
  Actual session installation, crypt/poll/NAPI, scheduler, deferred/timer, ingress/batch/flood and control paths are
  composed rather than treated as arbitrary quiet audit calls. Normal endpoints preserve state; every outcome
  preserves origin receipt/check validity. R2 validity and invalid-key carrier ownership remain separate.
  `Origins/RetainingConfiguration` covers actual peer/allowed-IP/device configuration, permitting invalidation
  and erasure on every normal return, including ordinary negative errno. `RetainingDump` preserves the full
  material view through actual cursor get/put/done, callback and queue operations, and the bounded whole dump;
  no cursor-validity, residency or drain premise is added. `SupportRunner` composes these with the existing
  concrete syscall wrappers and post-workers. Original empty/absent initialization and successful seccomp
  prefill discharge support for every typed trace and both placeholder flags. Every outcome has checked
  committed receipt history; successful decrypts retain exact stored packet/key/AEAD evidence and an actual
  successful derivation-front receipt in the strict earlier prefix, before any later session-tail Stop. Saved probes retain support at their captured Worlds.
  Original JSON/indexed Stop erasure and full incoming R2 audit/probe projection are unchanged. No failed
  or final JSON-observer World is invented. Ingress admission, configured identity, packet transport, earlier
  routing agreement remain open. Ordered copied-trial origin transcripts are optional separate coverage.
  `Peers/ConfiguredIdentity` adds supplied configured-table coherence and actual creation, lookup,
  retirement, make-dead and fresh owner-acquisition preservation, including aliased/NULL store-back.
  `Origins/ConfiguredSession` couples one actual derivation-front Context/material/owner/table witness;
  whole normal beginSession supplies live/self facts, and the unchanged observer retains its exact receipts.
  `Packets/PublicationIdentity` joins the actual captured ring pop, fresh stored-decrypt receipt and successful
  pre-IRQ publication to that historical configured caller and exact AEAD/packet/stamp evidence. DEAD is separate.
  These local additions pass independent static review and coordinated validation. Supplied support/compatibility, initialized
  configured registry and current-peer/key-frontier transport remain explicit; no cryptographic authenticity is inferred.
  `Origins/CurrentIdentity` couples material and current stamp/static identity in one
  configured receipt; its history-free retention relation supports concrete updates and
  the empty original fixture. `ConfiguredMaintenance` and `CurrentMaintenance`
  carry clear/handshake/expiry calls. `Peers/ConfiguredAllowedIps` and
  `ConfiguredTimers` preserve configured cells through actual clearing/timer calls.
  `Queues/AffiliationCompatibility` derives the nullable compatibility premises.
  `Packets/PublicationPeer` and `PublicationCurrent` establish exact resident
  identity at successful pre-IRQ publication; the original historical certificate follows
  by projection. Initialized current/owner and packet publication transport now
  hold through all concrete callers. Initialized routing now closes the incoming
  Stack-entry join. `Packets/InitializedTransmit` closes outgoing handoff
  authorization through the actual callback chain and initialized runner.
  `WG/CryptokeyRouting/` exports both path halves and the trie result.
  `RemovalSource` retains the original saved-list loop and both continues by an
  all-input equation while importing only the original AllowedIps module.
  `RemovalMirror` proves total exact binary and root-tagged leaf/unary iterations;
  `RemovalStore` gives pointwise map/backlink effects and local RepAt transport.
  `RemovalChildMirror`, `RemovalCollapse` and `RemovalSteps` add total nonroot
  unary, owned-parent leaf and ownerless-parent collapse steps, with both root
  and child final slots and optional absent siblings. The exact collapse-prefix
  equation retains later Stops at the original post-target-free parent reread.
  `RemovalChildStore` gives complete map effects and root/frontier/sequence/list
  metadata. Raw endpoints do not infer actual linkage or owner residency.
  `RemovalContext` derives a focus from explicit target membership and separates
  the two families by encoded width. `RemovalTransport` and `RemovalCases`
  transport all seven source cases through represented contexts, deriving
  residency and ID separation from the input forest. `RemovalDispatch` proves
  total original target-step execution, both-family pure erasure, exact retirement,
  peer-list filtering and complete outside-forest/device/Kernel frames. Original
  actual-root lookup afterward selects the winner among surviving entries.
  `RemovalLists` defines explicit resident-only list coherence and exact saved-ID
  filtering. `RemovalLoop` executes the original fixed saved list, deriving later
  owned membership after each removal. `RemovalPeer` proves complete original
  removeByPeer from that input coherence, preserving it and removing exactly the
  target peer's entries, with the conditional sequence increment and empty target
  list. Original actual-root lookup then selects the surviving peer-filtered winner.
  The separate finite-call history layer now derives initialization and peer
  lifecycle preservation; the later completion layer supplies whole device-command
  composition and guarded device lifecycle; the initialized Runner layer supplies
  enclosing execution. Packet paths remain open.
  Its five exports pass scoped/full builds, independent frozen review and coordinated checks.

- `Leanux/Proofs/WG/Queues/`: original guarded ring production, symbolic
  no-wrap filling and unretired consumption, the concrete two-carried-slot
  witness, and the complete original enqueue helper's normal-return ring
  projection. `RingGeometry` identifies original peek/count/items and physical
  fullness with a stale/live slot representation. `RingSteps` proves exact
  original guarded production and retained/retired consumption, including wrap,
  every batch value and repeated payloads, deriving successor bounds. Size zero
  is separate. `RingJournal` composes exact finite offer/poll histories with
  admitted/consumed/live and consumed/retired/stale conservation. `RingMap` and
  `RingOccurrences` erase fresh per-offer ordinals through original operations,
  including refusal, and prove joint consumed/live ordinal uniqueness from init.
  `EnqueueAdmission` independently derives successful TX/RX entry-ring freedom,
  retaining the existing result API. `RingSource` shares source-journal replay,
  prefix safety and initialized conservation across payload types; `RxRingJournal`
  retains the RX API. `RxRingFrames`/`RxRingCuts` and `TxRingFrames`/`TxRingCuts`
  derive full device-index/ring frames and installed-mutation source endpoints.
  `RxRingEntry` observes complete RX enqueue/consumeData; `TxRingEntry` observes
  TX enqueue/createData. `RxRingWorker` covers decrypt step/iteration, and
  `TxRingWorker` covers encryptPacket and encrypt step/iteration, with explicit
  callback erasure and preservation contracts. Every reached prefix has a finite
  ring replay; only normal returns link its endpoint to the actual World.
  Initialized calls inherit physical conservation and distinct occurrence
  ordinals, including size zero. TX ordinals name whole-list occurrences, not
  constituent packets. `RxRingCallbackFrames`, `RxRingNapi`, `RxRingEncrypt`,
  `RxRingSocket`, `RxRingTx` and `RxRingHandshake` discharge the complete RX-cell
  frames of actual callbacks and non-decrypt workers. `SourceScheduler` shares
  callback-parameterized original run/dispatch/schedule control; `RxRingScheduler`
  instantiates it with unconditional erasure and concrete RX-journal refinement.
  `RxRingTrials` retains exact copied-world decision/filter behavior and certifies
  speculative prefixes separately from committed history. Initialized prior
  journals may describe nonempty current rings. `RxBorrow` proves the adjacent
  original lookupSrc/peerPut cut, retaining the lookup result, exact access/Stop
  erasure and safe failed prefixes. Queue/NAPI/key-slot projections and conditional
  bounded slot-affiliation preservation follow; no initial liveness or trie-validity
  premise is required. Its destination lemma covers immediate repayment only.
  The four new exports pass scoped and coordinated validation.
  `TxDisposition`, `TxDispositionProjection`, `TxDispositionStep` observe actual
  TX admission/publication/drop/completion cuts, with all-input source erasure and
  direct createData access/ring projection. Full-step access projection uses entry
  AllocationInv and concrete helper contracts. `TxDispositionCuts` gives exact
  EPIPE/ENOSPC/DEAD continuations, reached free markers and normal disposal no-send.
  `TxDispositionBorrow` derives strict-acquisition positivity and immediate repayment.
  The six observer/cut exports pass coordinated validation. `TxPublication` now
  retains all full peer TX queues across the actual strict borrow, CPU update and
  work-record interval, deriving nonfinal repayment without peer affiliation.
  `TxDisposal` proves exact normal list erasure and original ENOSPC packet absence.
  `TxDispositionEndpoints` gives normal EPIPE queue retention, DEAD head and unchanged
  ring, plus actual DEAD-head txStep disposal with unchanged socket output. Five
  new exports pass scoped/full targets of 243/365 jobs, independent frozen review
  and coordinated validation.
  Initialized RX carrier/funding/work correspondence through transmit callbacks, W7 transport
  between the local refusal/disposal endpoints and joint receive-pipeline conservation
  remain open; initialized callback-entry uniqueness is closed by the Runner layer below. The RX scheduler extension passed coordinated validation at its preceding checkpoint. `PrevQueue`
  proves original logical FIFO, cached-peek and malformed Stop laws. `RxQueueView` and `RxHelperFrames` retain full receive queues tagged
  by interface index and peer internal ID through original reference, release, replay
  validation and key-confirmation helpers. `RxQueuePrimitives`,
  `RxMaintenanceFrames`, `RxTxFrames` and `RxCompletionFrame` extend these
  concrete contracts through endpoint/timer maintenance, staged transmission
  and complete original receive completion, allowing peer deletion.
  `RxPollPrimitives`, `RxPollPrefix` and `RxPollOrder` prove that the outer
  poll body's observed removals form a prefix of its entry queue, including
  failed prefixes, with an explicit callback `RetainsRx` contract, exact
  source-site append and original erasure laws. `GroCallback`, `GroState` and
  `RxPollGro` carry local occurrence labels and exact completion bytes through
  original GRO normal/held lists, counts and actual callbacks. `RxPollGroOrder`
  preserves the old chronological predicate: its former universal poll theorem
  is false on real GRO, as the accepted `DeliveryOrder/ReplayGro` demonstrates.
  The original helper equation proves held-then-normal input selects
  normal-then-held output when the newcomer bypasses the held flow; a refused
  same-flow merge completes the held packet first. The actual per-list callback
  retains its visited prefix on Stop. `SelectedGro` follows those transitions
  and proves selected callback-prefix order for every
  input World and Stop of one poll, and exact selected-offer/callback-entry list
  equality on an actual original normal return. Its internal count/list and
  held-size invariants are derived from the empty local state; no caller queue
  premise is used. `RxPollTags` proves that buffered ordinal/skb tags form a
  subsequence of observed drops, whose ordinals are consecutive from zero;
  buffered ordinals are distinct. `RxPollProjection` proves exact result/World/Stop
  and removal-log agreement between the tagged and removal-only poll observers,
  including actual callbacks. `RxStackFrames` discharges receive-queue retention
  for the concrete stack callback, including IPv4 TCP replies through original
  transmit entry and loopback errors. `RxPollProvenance` composes the concrete
  entry-queue prefix and buffered skb subsequence, and proves distinct callback
  ordinals with exact buffered-entry/removal-tag origins on every Stop.
  `Logged/ProjectsUnderTo` supports exact projections with mapped results.
  `StampedGro`, `RxPollJoint` and `RxPollJointProjection` carry captured allocation
  stamps through the actual second getter, GRO buffers and focused callbacks,
  with unconditional source/GRO projection and allocation-conditional direct
  lifetime projection. `RxPollStampSafety` retains a fresh local occurrence
  journal beside arbitrary valid prior lifetime history. `RxPollStampPhase`
  proves full stamped callback/removal provenance, distinct removal and callback
  allocation stamps on every reached prefix, and their observed release on normal
  poll completion. Failed callbacks retain their entry and may leave a pending
  stamp. `RxPollCaptureSupport` connects each removal and entered key to the
  original capture read before its removal inside the appended suffix. Allocation
  safety excludes prior releases; normal-return releases belong to this suffix.
  `RxPollHistory` starts each poll with fresh local metadata and exactly the current
  lifetime history, preserving global audit/probe interleaving by appending only
  the new suffix. Its direct audit projection needs no history-neutrality premise.
  `Logged/Capture.captureObserved` runs the existing callback observer once at
  its actual World/history, retaining success and Stop histories. `StampedGro`
  appends a receipt only after normal Stack return; old decoders erase receipts.
  `Logged/Capture.PrefixEnsures.captureObserved` also retains the successful
  result-sensitive precondition at the captured before World and the actual output
  history, before receipt emission. `RxConsumeLink`/`RxPollReceiptLink` derive actual
  selected packet/stamp/peer linkage at consume entry, strict capture-read/removal
  support, and ordered equality of the full consumed receipt and buffered/entered/
  completed Entry. The literal poll supplies every local precondition without a
  World premise. Historical support survives free and held GRO callbacks; consume's
  after World need not equal Stack's before World. Fresh suffix promotion and finite polls
  preserve explicit incoming HistoryLinked, not arbitrary check/Stack-witness
  validity. `RxLinkCallers`, `RxLinkEnvironment` and `RxLinkRunner` propagate linkage
  and separate HistoryReceiptsValid through the unchanged concrete observers. Both
  hold from empty initialization for every typed Trace and both placeholder settings,
  including Stops. Global committed order does not label individual poll boundaries;
  the fresh local suffix contract remains separate. Initialized key/session
  identity and admission credits are supplied by the later R3/R4 compositions;
  no observer hierarchy or old invariant is changed.
  `RxCarrierState`, `RxIngressProtection` and `RxCleanupProtection` separate complete
  resident inventory, exact queue multiplicities and explicit unpaid-credit/reservation
  bounds. Actual lookup and admission derive the loan and key word; vacant allocation
  transfers that reservation into the same ledger. Pure-IRQ publication repays its own
  resolved peer. Original cached-head drop changes queued to selected; positive remaining
  demand derives non-retirement, and paid/free cleanup retains the remaining ledger.
  The actual ENOSPC suffix preserves all three recorded decisions and queue ownership.
  Vacancy and successful key payment are explicit premises of those older local cuts. Whole consumeData
  composition and initialized conservation are supplied by the later contracts;
  ghost phase predicates alone do not establish past payments. `RxProtectionFrames`, `TxRxProtection` and `RxConsumeProtection`
  now retain the same supplied ledger through full original staged-send and consumeDataDone
  normal returns. Actual acquisition/disposal/publication/queued-handshake cuts derive typed
  TX-batch/send-work append deltas and exact balances. Nullable current-key compatibility
  suffices for staging; actual packet-key promotion supplies it inside consume. Timer control
  frames preserve the separate slot/word facts. Funded handoffs derive resident delta owners;
  unfunded generic equations alone do not. No output key compatibility, TX ownership or
  send-pending/work correspondence follows from Handoff. `RxKeyProtection` separately
  proves backwards non-NULL word retention and stamped resident-current provenance,
  allowing deletion and the actual received-key promotion. `RxStackProtection` keeps the
  real destination loan across nonempty typed handoffs and repays it through original
  wgXmit, including negative errno, reply/receive/deliverInner and batches. Its nullable
  RX-key/all-resident-current product needs no validity or allocation-frontier premise.
  `RxPollCarrier` transports the same supplied Inventory/QueueOwners/Protected through
  the unchanged joint poll: cached-head selection, actual consume/GRO, keyPut/peerPut/free
  and completion. On normal return the remaining ledger is the original list filtered
  by actual fresh removal allocation identities; those cells are absent, and the existing
  nondelivery/completed partition has no residual. Last-credit retirement is allowed;
  a subsequent missing getter Stops without a failed World. Uncrypted-head normal exits
  can retain queued carriers. No extra caller/base reservation or totality is assumed.
  Initialized compatibility/funding, admission/ring and lifecycle/work correspondence
  remain open; this is local normal-poll conservation, not initialized pipeline closure.
  `RxAdmissionCarrier`, `RxIngressCarrier` and `RxIngressStable` close whole original normal
  consumeData from supplied CarrierState and packet-allocation validity. The same admission
  witness retains actual lookup/acquisition/peer/allocation, enqueue and finish executions,
  and is appended by the existing receipt observer. Success/EPIPE add the queued carrier;
  ENOSPC repays key/peer references and frees it. StableRx relates all queued carriers to
  logical uncrypted ring contents and only the head of a cold nonempty queue. Whole admission
  preserves it; the existing physical ring observer separately supplies its actual appended
  safe/refined history on the same normal run. Stable ring-empty/NAPI-cold implies empty RX
  inventory/store, including size zero. These local premises do not establish initialized
  ingress injection, decrypt-worker propagation or lifecycle/work funding. The lower receipt
  equation permits a later finish Stop; the public endpoint export assumes normal return.
  `RxPollCompletion` proves ordered entry/valid-return pairs for local polls,
  persistent observed polls and finite poll sequences. Normal returns close all
  entered callbacks; a failed prefix permits one trailing unfinished entry.
  The history-only protocol requires no allocation, residency or progress premise.
  `RxCompletionCallers`, `RxCompletionEnvironment` and `RxCompletionRunner`
  propagate that separate protocol through the existing concrete observers. All
  typed initialized traces and both placeholder settings have valid receipts even on Stop; normal
  returns pair every entry, and receipt stamps inherit entry-stamp uniqueness.
  No operational hierarchy or stronger BoundaryInv is added. Socket arrival and
  receive-pipeline conservation remain separate.
  `RxPollComposition` retains distinct entry stamps across finite poll sequences
  and restores released-entry boundaries on normal return. Its generic focused
  audit frame preserves recorded metadata, without certifying nested poll coverage.
  `RxNapiCuts` factors the complete saved-map scan and short-circuit IRQ scan,
  retaining exact source equations for softirq, inline polling and IRQ exit.
  `RxNapiHistory` uses the stamped observer at both direct source poll sites;
  all three callers erase exactly, project directly to the existing R2 audit
  observer at the identical incoming history, and preserve the entry-stamp
  boundary on normal return and uniqueness on failed prefixes.
  `RxWorkerCuts` factors the nonpolling encryption tail and exact RX publication
  prefix, deriving the cached setter's identity from its original getter.
  `RxWorkerHistory` observes concrete encrypt/decrypt softirq and IRQ callbacks;
  `RxActivationHistory` covers transmit pre-encryption and one actual activation
  iteration, including temporary work queues, suspended bookkeeping and late Stops.
  All four contracts directly project to the existing focused R2 observers at the
  same incoming audit history and preserve normal boundaries/failed-prefix uniqueness.
  `RxActivationRunHistory` observes complete activation runs and dispatch, including
  original occupancy reads, queue selection, section records and failed prefixes.
  `RxScheduleHistory` carries stamped committed polls through actual scheduling and
  nested rescheduling, projecting directly to the existing full R2 audit, including
  exact consistency-filter probe payloads. Copied trial histories stay separate;
  each reached probe supplies allocation validity and exact ordered trial decisions.
  `RxEnvWorkersHistory` observes deferred crypt/send processing and afterXmit;
  `RxEnvTrafficHistory` covers injection, exact flood producers/inline polls and afterBatch;
  `RxEnvBatchHistory` retains batch CQEs and the inline poll inside its original
  NET_RX receive section. Each projects directly to the corresponding full R2
  audit at the same incoming history and preserves normal release boundaries
  and failed-prefix uniqueness. Only inspected poll-free leaves are focused.
  `RxEnvTimersHistory` observes both timer passes and wait continuations, focusing
  only the literal poll-free placeholder timer block with its own saved-peer scan
  proof. Reset/absent-device return precede that block; crypt/send work follows it
  through concrete observers. `RxEnvControlsHistory` observes idle timers before
  the original observation tail and focuses inspected poll-free controls. Explicit
  mappings cover all fifteen deferred and fifteen remaining environment cases,
  with direct same-history full R2 projection and normal/failed boundary contracts.
  `RxSyscallDispatchHistory` and `RxSyscallsHistory` retain every original dispatch
  arm, observation-before-fdget order and normal negative-errno suffix.
  `RxRunnerHistory` composes the initialized Runner with result-sensitive outer
  contracts over each returned accumulator World. Its literal post-initialization
  tail projects directly to the existing full R2 audit, including true probes and
  separately certified copied trials. Every typed trace and both placeholder settings have distinct
  committed callback-entry allocation stamps, including stopped prefixes, without
  parser, length, success or initial-allocation premises. Original erasure remains
  unconditional. `WG/DeliveryOrder/` exports these contracts. The separate completion
  layer proves normal Stack returns; socket arrival, ownership and receive-pipeline
  conservation remain open.

- `Leanux/Proofs/WG/KeyTimes/`: exact original signed clock-test and comparison
  records (`Clock`), receive admission guards and the later wire-counter
  acceptance bound (`Receive`). `ReceiveAttempts` observes the actual AEAD
  boundary, proves admission for every event, and gives exact singleton coverage
  and failed-authentication endpoints. The zero-timer callback's complete
  transport-keypair-store frame is in `ZeroTimer`. `Staging` certifies actual
  completed TX allocations and submitted arguments with original key/clock
  witnesses and assigned-nonce bounds, retaining events on subsequent failure.
  `WG/KeyLifetime/` exports R5's positive local contracts and accepted-run
  counterexamples: nonce R/R+1 authenticates before validation rejects it; queued
  transport keepalives encrypt after recorded expiry or after zero/clear, before
  a new handshake. The new time witnesses use coherent coarse/jiffies/arm
  arithmetic; an earlier legacy witness deliberately does not. All are generated
  mirror inputs, not Linux captures. R5 is resolved as a Rule Zero finding;
  universal TX admission transport and whole-run attempt coverage are not claimed.

- `Leanux/Proofs/WG/Cookies/`: exact original load and post-MAC source factors,
  explicit MAC2 failure against the cookie returned by original `makeCookie`,
  invalid-MAC1 drop, and cookie-only result equality. Reply frames retain all
  device fields except cookie secret/birthdate and TX statistics, plus global
  peer/keypair counters; both secret rotations and IPv4/IPv6 sends are covered.
  `WG/FloodResistance/` exports six R6 terminals and reconstructs one accepted
  retry episode disproving the literal `MAX_TIMER_HANDSHAKES` attempt limit.
  It makes no universal retry-episode or kernel-schedule claim.

The dependency order is CounterWindow, Logged, Framing, Keypairs,
ReplayWindow. The conventions that keep proof work cheap are in
[the future-proof-paths note](2026-10-06-future-proof-paths.md) and
[the window-proof conventions](2026-10-13-window-proof-conventions.md).

The [disposition extension](2026-10-17-r4-dispositions.md) adds 22 modules and
287 theorems: 860 files, 11,727 named theorems, 300 R4 terminals and 834 total
terminal declarations. Source-selected syscall admissions retain actual later
poll dispositions and releases, or exactly one pending packet identity. The
initialized runner supplies every completed poll input invariant and its funded
residual account; complete initialized admission selection remains open.
Actual staged allocation derives fresh item separation, and selected encryption
preserves unrelated packet cells. W7 whole-caller and live-item alignment remain
open. All earlier theorem bodies are unchanged. Gate: 918 jobs/834 declarations,
6.622 seconds; fresh replay PASS in 116.213 seconds with no warnings.

## Results

| Result | Statements | Directory | Charter | Review | Mirror commit | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Receive counter window: replay freedom (S1, S2, S3) | S1: every accepted execution has its exact acceptance history, and no two events share an allocation lifetime and a wire counter. S2: `counterValidate` returns exactly what receive.c's rule returns and leaves exactly its replay state. S3: every non-receive syscall and every validator call leave every other keypair's window unchanged, per call and for whole syscalls including the runner's ambient step. | `Leanux/Proofs/WG/ReplayWindow/` (`Statements.lean`, 15 terminal declarations; `Counterexamples.lean`) | [charter](2026-10-12-charter-window-proof.md) | [independent review, two parts](2026-10-12-spike-window-review.md); the spike's [report](2026-10-13-spike-window.md) and [self-review](2026-10-13-spike-window-self-review.md) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd` |
| R1: anti-replay uniqueness and inclusive floor | No wire counter is accepted twice in one allocation lifetime; every accepted counter is at or above the inclusive lower edge, for pure runs, original validator calls and accepted runner histories. Equality at the charter's floor is intentionally permitted, with a concrete recorded replay. | `Leanux/Proofs/WG/AntiReplay/` (`Statements.lean`, 9 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r1--anti-replay-uniqueness-and-the-inclusive-floor) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd` |
| R2: initialized lifetime safety | For every typed Runner trace and both placeholder settings, committed peer/keypair/packet access histories are safe from release-before-access, including failed prefixes. Every actual reached consistency-filter entry is allocation-valid and supplies exact ordered filter correspondence and safe isolated copied-trial histories. The observer preserves exact original JSON or indexed Stop without parser, array-length, progress or success premises. Original local contracts and endpoint identity refinements remain available. Historical stale-cursor inputs retargeted replacement identities; their current full recipes reject at operation 3 under the pending-dump guard. Raw-reference affiliation/credit is a separate stronger property. The universal quantifier ranges over the events the proof-side observers record; that the observers emit an event at every access, release and allocation site is established by review of their wiring, not by a kernel-checked theorem. | `Leanux/Proofs/WG/LifetimeSafety/` (`Statements.lean`, 202 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r2--lifetime-identity-and-retained-references) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd` |
| R3: cryptokey routing | Trie lookup agrees with the independent flat longest-prefix history for both families, including insertion, removal and lifecycle cleanup. Each initialized Stack entry links to its earlier buffer, consume and configured decrypt/publication occurrences, and its source winner is the consuming peer at that consume prefix. Each initialized outgoing handoff selects the longest-prefix owner of every supplied packet’s destination at its captured native front entry. Actual direct, batch and Stack-reply callers, NAPI, crypt workers, scheduler, timers and syscall continuations are connected. Public parsing discharges configuration address shape; both placeholder settings and prefixes preceding indexed Stops are included. Exact executable erasure and complete old RX-journal projection hold for arbitrary incoming histories. No final-state authorization premise, Noise authenticity or later wire-send property is claimed. Complete caller coverage uses checked source factors and reviewed wiring; selected-occurrence authorization is kernel-proved. | `Leanux/Proofs/WG/CryptokeyRouting/` (`Statements.lean`, 289 terminal theorems) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [incoming report](2026-10-17-r3-initialized-authorization.md), [outgoing report](2026-10-17-r3-initialized-transmit.md), [campaign report](2026-10-13-proof-campaign.md#r3--cryptokey-routing) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd`; trie and both initialized path halves retained |
| R4: ingress conservation, W7 characterization and GRO order finding | Every accepted runner exposes all actual ingress positions, including admissions removed before syscall return. Each accepted carrier has exactly one pending identity or an actual named completed-poll disposition/release; initialized stamp uniqueness prevents duplicate Stack entries. Live logical ring bounds and physical refinement are derived from initialization. Kernel-proved arbitrary-payload geometry and an accepted generated original-run replay characterize the named W7 episode: 1022 enqueues and two refused allocations, later released as DEAD heads without completion. Chronological GRO order is refuted; run-wide pre-GRO order is not claimed, and the order result is the per-poll subsequence theorem `original_poll_buffered_entry_subsequence` (`DeliveryOrder/Statements.lean:537`): the C's first-in-first-out order through the per-peer queue up to `napi_gro_receive` is proved within one poll only. The finite W7 runtime checks are compiled evidence, not universal outgoing-disposal or eventual-delivery theorems. Local cleanup-totality findings remain. The universal quantifier over ingress positions and carriers ranges over the events the proof-side observers record; that the observers cover every admission and poll site is established by review of their wiring, not by a kernel-checked theorem. | `Leanux/Proofs/WG/DeliveryOrder/` (`Statements.lean`, 326 terminal theorems; `ReplayGro.lean`, `ReplayFullRing.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [full-ring report](2026-10-17-r4-full-ring.md), [ingress coverage report](2026-10-17-r4-ingress-coverage.md), [campaign report](2026-10-13-proof-campaign.md#r4--ingress-conservation-full-ring-characterization-and-gro-order-finding) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd`; charter disposition complete |
| R5: key lifetime enforcement; Rule Zero findings | Thirteen local theorems identify exact original clock tests, RX AEAD admission and failed-tag coverage, accepted-wire-nonce bounds, TX staging certificates, zero-timer store framing and timer-pass erasure. Accepted original/observed replays authenticate nonce R+1 before rejection and encrypt queued transport keepalives after recorded expiry or zero/clear before a new handshake, using the same packet-held material. New time inputs have coherent coarse/jiffies/arm arithmetic, without a Linux schedule claim. The original unconditional statement is false; universal replacement transport theorems are not claimed. | `Leanux/Proofs/WG/KeyLifetime/` (`Statements.lean`, 13 terminal theorems; `Replay.lean`, `ReplayDelayed.lean`, `ReplayPostClear.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r5--key-lifetime-enforcement-rule-zero-findings) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd` |
| R6: cookie exclusion and retry-limit finding | Original under-load calculation and rejected-initiation suffix are exact. Invalid MAC2 against the actual original cookie result executes only the cookie reply; invalid MAC1 drops earlier. Ordinary completion preserves full Noise stores, indices and peer/keypair allocation counters. An accepted generated episode has 19 retries and 20 total initiations with MAX=18, then gives up on callback 20; this refutes the literal limit without claiming a universal replacement bound; the give-up behaviour is also shown on Linux by the differentially checked corpus trace `corpus/wireguard/d3_retransmit_gives_up.json` (20 `wg_advance`s in the `wireguard` suite). The whole advance observer has exact original erasure. | `Leanux/Proofs/WG/FloodResistance/` (`Statements.lean`, 6 terminal theorems; `Replay.lean`) | [campaign charter](2026-10-13-charter-proof-campaign.md) | [campaign report](2026-10-13-proof-campaign.md#r6--cookie-exclusion-and-retry-limit-finding) | 218d3ffd | Current: GRO carry validated; the fixed-width counter carry (the four shared modules retyped to the C's words) validated at the gate over `1f766662`; the namespace-pin carry (the runner step copies, the namespace close and cleanup frames) validated at the gate over `218d3ffd` |
| H1 Noise session state machine | 75 terminal declarations: whole-run tag ownership; per-function slot effects; completed confirmation uniqueness. | `Leanux/Proofs/WG/Noise/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | [independent landing review](2026-10-20-review-campaign-2-landing.md) | 218d3ffd | Current. Whole-run edge ownership; rotation, confirmation, expiry and clearing are per-function contracts, with no whole-run slot-change theorem. One keypair per slot holds by the Option type; exactly-once is at-most-once per allocation stamp for successful completed confirmations. Observer-site completeness rests on source construction and review. |
| H2 Session index uniqueness | 162 terminal declarations: initialized endpoint index/owner coherence, lookup and local collision retry. | `Leanux/Proofs/WG/Index/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | [independent landing review](2026-10-20-review-campaign-2-landing.md) | 218d3ffd | Current at normal initialized endpoints; stopped runs and intermediate boundaries are not covered. Lookup has an arbitrary-state contract; collision retry is local and supplied-record-mode only, without a runner-level insertion-draw theorem. |
| H3 Endpoint roaming | 45 terminal declarations: final latest-setter provenance and authentication of observed handshake attempts/data checks. | `Leanux/Proofs/WG/Roaming/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | [independent landing review](2026-10-20-review-campaign-2-landing.md) | 218d3ffd | Current for normal final provenance and observed attempts/checks, not every physical endpoint write. Packet provenance ties the endpoint to the same checked packet source; the outer address is copied, not AEAD-bound. Observer-site completeness rests on source construction and review. |
| H4 Configuration semantics | 217 terminal declarations: mixed scalar readback, initialized getter, flag contracts and ordered configuration effects. | `Leanux/Proofs/WG/Config/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | [independent landing review](2026-10-20-review-campaign-2-landing.md) | 218d3ffd | Current scoped contracts: mixed peer get-after-set is one-directional over internalId, PSK, keepalive and endpoint, under an entry invariant not derived at initialized endpoints; the initialized getter is separate. Replace-peers is flag-only. The charter’s allowed-IP removal flag is recast as peer REMOVE_ME/REPLACE_ALLOWEDIPS because Linux 6.12 has no per-allowed-IP flag. No mixed-request creation/removal completeness or full peer-field readback is claimed. |
| H5 Termination and progress | 280 terminal declarations: finite trace evaluation, operation guards and committed activation receipts. | `Leanux/Proofs/WG/Progress/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | [independent landing review](2026-10-20-review-campaign-2-landing.md) | 218d3ffd | Current finite evaluation preserves every Stop, including budget exhaustion; it is not general budget adequacy. Accepted supplied-mode operation boundaries have empty pending work, but propagation of supplied mode to interior receipts remains unproved. Unrestricted pending emptiness was refuted in placeholder mode by the namespace-pin reproducer; the environment defect is fixed at `218d3ffd` (request 5 closed on the mirror side: the fixture's holders are reserved descriptors, the close runs the teardown only because the pin's release queued it, a pending unit at an operation's end is refused in both modes). Lagging on that recipe: `NamespacePinPending.lean` asserts the parser's former acceptance and fails until campaign 2's regression carry, which also owns re-attempting the unrestricted clause over the now-stated domain. Receipt decrease retains its supplied-entry premise. |
| H6 Timer discipline | 100 terminal declarations: guarded arm effects, hook journals, qualifying retry blocks and session-relative counts. | `Leanux/Proofs/WG/TimerDiscipline/Statements.lean` | [charter](2026-10-14-charter-proof-campaign-2.md), [report](2026-10-14-proof-campaign-2.md) | [independent landing review](2026-10-20-review-campaign-2-landing.md) | 218d3ffd | Current guarded contracts, with no theorem that arming occurs only at the listed sites. Keepalive re-arms are conditional on reaching the hook; caller coverage rests on journal construction and review. Session counting proves at most one completed enqueue per stamp plus a separate give-up cause, not once per session. The bound 19 covers qualifying contiguous retry blocks in one normal timer episode, not arbitrary interleavings. |

The gate for every row: `capped -- scripts/in-bundle scripts/proof-gate`
(the build, the axioms of every declaration of every module the root
imports, the forbidden tokens, the imports and the default targets). The
declarations the gate prints are the terminal statements; current counts are
recorded with validation in the campaign reports. Whole-run observations erase
to the original JSON or indexed Stop. Completeness of observation sites rests
on the reviewed source construction, not erasure alone. The declarations
carrying each result's claim are these:

| Result | Claim-carrying theorems |
| --- | --- |
| Receive counter window | `S1`, `S2`, `S3` (`ReplayWindow/Statements.lean`) |
| R1 | `runner_uniqueness`, `runner_floor` (`AntiReplay/Statements.lean:29`, `:39`); the floor finding `inclusive_boundary_witness` (`:91`) |
| R2 | `runner_initialized_access_safety` (`LifetimeSafety/Statements.lean:1901`), `runner_audit_erasure` (`:1892`) |
| R3 | `parsed_initialized_routing_execution` (`CryptokeyRouting/Statements.lean:2577`), `parsed_initialized_incoming_authorization` (`:4432`), `parsed_initialized_transmit_authorization` (`:4643`) |
| R4 | `accepted_runner_all_ingress_fates` (`DeliveryOrder/Statements.lean:3625`), `original_poll_buffered_entry_subsequence` (`:536`), the GRO finding `original_gro_held_then_normal` (`:430`), `two_carried_full_ring_result` (`:3688`) |
| R5 | the thirteen local contracts of `KeyLifetime/Statements.lean`; no run-wide theorem |
| R6 | `original_invalid_mac2_cookie_only` (`FloodResistance/Statements.lean:41`), `original_invalid_mac2_noise_preserved` (`:53`) |
| H1 | `original_initialized_driver_tags`, `original_initialized_confirmation_unique`, `original_slot_rotation`, `original_confirmation`, `original_expiry_slots`, `original_clear_ordered`, `original_begin_session_ordered` ([Noise/Statements.lean](../Leanux/Proofs/WG/Noise/Statements.lean)) |
| H2 | `original_initialized_index_tables`, `original_index_lookup`, `original_index_insert_recorded` ([Index/Statements.lean](../Leanux/Proofs/WG/Index/Statements.lean)) |
| H3 | `original_initialized_latest_endpoint_origins`, `original_initialized_handshake_attempt_authentication`, `original_initialized_data_check_authentication` ([Roaming/Statements.lean](../Leanux/Proofs/WG/Roaming/Statements.lean)) |
| H4 | `original_mixed_scalar_getter`, `original_initialized_mixed_readback`, `original_replace_peers_completion`, `original_queued_remove_peer_command`, `original_update_only_existing`, `original_configuration_key_stage` ([Config/Statements.lean](../Leanux/Proofs/WG/Config/Statements.lean)) |
| H5 | `original_executeTrace_finite`, `original_accepted_operation_boundaries`, `original_turn_dispatch_runs`, `original_turn_resumes`, `original_initialized_completed_record_decrease` ([Progress/Statements.lean](../Leanux/Proofs/WG/Progress/Statements.lean)); [namespace-pin counterexample and open request](2026-10-20-proof-campaign-2-namespace-pin.md) |
| H6 | `original_guarded_arm`, `original_initialized_session_counts`, `original_timer_actual_retry_block_counts`, `original_giveUp_arms_without_session_creation` ([TimerDiscipline/Statements.lean](../Leanux/Proofs/WG/TimerDiscipline/Statements.lean)) |

The speedbump beside the gate, run at claim points and never blocking:
`capped -- scripts/in-bundle scripts/proof-counterexamples`, which replays
the fifteen published counterexample and witness recipes: campaign 1's twelve
and campaign 2's confirmation-incarnation, namespace-pin and initialized
give-up witnesses. They use `lake env lean --run` or a self-checking `#eval`
for the standalone pin recipe. These interpreter runs sit outside the kernel
and the gate's build closure; the speedbump keeps them reproducible.

The following validation history predates the split. Its checkout mirror was
byte-identical to `cb2348e`. The rows above instead reflect the completed
split retrofit over `b3f56807`, executable-identical to `b700659`.
The R3 configured-identity/session/publication extension adds three groups, preserving all 518 prior
terminal bodies: 521 declarations (519 theorems/two definitions; 141 R3/129 R4). Scoped/full builds pass
474/523 jobs. Coordinated validation passes gate 523/521, fresh kernel replay after compilation, default
60 and 103 tests (21.825s, one skip); exact checks preserve scope, sources, recipes and pins. Independent
static review found no substantive issue. Root review corrected the parsed-routing premise in this register.
The 42 worker calls comprise 40 builds (six clean PASS/34 ordinary FAIL) and two passing exact checks.
Default-limit exhaustion and rejected recovery goals were failures, repaired without raised limits or
source admissions. The report and commit record the process finding, review dispositions and full ledger.
The validated `192c7e7` admission/stable checkpoint retains gate 520/518, fresh replay, default 60 and
103 tests (22.860s, one skip), plus its interruption preservation and corrected scope/process findings.
The preceding validated `b4acf05` committed-support checkpoint passed
gate517/516, fresh replay after compilation, default60 and103 tests (21.784s,one skip); its exit-zero tactic-index
diagnostic and repair remain recorded there. The preceding `f1209f5` normal-poll checkpoint passed gate514/513,
fresh replay, default60 and103 tests (21.635s,one skip), with its44-call ledger retained in the commit.
The preceding `a945ea8` stateful-support checkpoint passed gate511/511, fresh kernel replay,
default60 and 103 tests (22.370s, one skip); it supplied local preservation, initialized by `b4acf05`.
The named preceding `8f9b8a2` callback-protection checkpoint passed its 508-job/508-declaration
permitted-axiom gate, fresh kernel replay, default60 and 103 tests (21.919s, one skip).
The preceding `00c204d` retaining-operations checkpoint passed the 505-job/506-declaration
permitted-axiom gate, fresh kernel replay, default60 and 103 unit tests (21.165s, one skip), with all prior
bodies and frozen Lean hashes retained. The preceding `bc45a9c` RX-credit checkpoint also passed validation.
The validated preceding `60f8ea06` source-injection checkpoint passed its 499-job/501-declaration
proof gate, fresh replay, default60 and 103 tests (21.627s, one skip). The previous
`c0bff5e` initialized R4 linkage checkpoint passed its coordinated 496-job/499-declaration gate,
fresh stock kernel replay, default60 and 103 tests (21.481s, one skip).
The preceding validated `41df9916` owner-material checkpoint passed scoped/full
builds (430/493), its 497-declaration gate, fresh kernel replay, default60 and
103 tests (21.794s, one skip), exact checks and independent review. It closes
local index material retention, not initialized R3 session origin.
The preceding validated `0b1cd078` packet-link checkpoint passed scoped/full builds
(403/492), its 496-declaration permitted-axiom gate, fresh stock kernel replay,
default build and 103 tests (one skip), exact checks and independent review.
The preceding `8f95d45` material-support checkpoint likewise passed its coordinated
checks; its explicit supplied-history limitation remains. The preceding `41df9916`
owner-material checkpoint closes that local frame gap, not initialized R3 origin.
The preceding validated `ba0bbe3e` local RX disposition slice
adds three terminals (492 total, 117 R4), preserving all 489 previous statement
and proof bodies. Scoped/full builds pass (401/488 jobs); full result collected 09:22:10 UTC.
The exact check passes scope, all 489 prior bodies, census, tokens/imports,
tracked/new-file whitespace and mirror identity. Independent final review,
the 492-declaration permitted-axiom gate, fresh stock kernel replay, the 60-job
default build and 103 tests (one skip) pass. The first replay failed because the
coordinator overlapped it with the gate's final recompilation; the sole
infrastructure retry passed after the build finished. New standalone check/consume events are erased by the old audit/GRO/
completion projections; entry/completion decoders retain the full Entry, including
its optional consume receipt. Original/GRO erasure, direct same-history lifetime/
audit projection, prior probes and initialized entry/completion claims are preserved. At that checkpoint the captured allocation-to-consume and same-journal receipt
links remained open. The local contracts and new initialized propagation close those
packet/receipt links; historical key/session origin and admission conservation remain open.

The preceding representation carry passed its 486-job build, 489-declaration
permitted-axiom gate, fresh stock kernel replay, default/executable builds and
126 tests (one skip), plus eleven recipes: nine accepted agreements and two
pending-dump rejections with accepted pre-delete boundaries. Its first exact
checker failed on whitespace in flag-removal normalization; the corrected check
passed without a source change. The carry retained 479 bodies and removed only
`floodExact` binder/call tokens from ten others; no initialized domain changed.
Detailed carry effort and source deltas are in commits `0ed74eb` and `15f0b97`.
The preceding `99e4f88` local session/material/RX-origin tranche passed scoped/full builds (426/486 jobs), with 489 declarations (124 R3,
114 R4; 487 theorems/two definitions), retaining all 487 preceding terminal bodies.
The 489-declaration permitted-axiom gate, fresh stock kernel replay, 60-job default
build and 124 tests (one skip) pass. Exact source checks and independent frozen
source review pass after wording fixes.
The preceding `65e6a6d` initialized R4 callback completion propagation passed scoped/full builds (337/483 jobs), the 487-declaration
permitted-axiom gate, fresh stock kernel replay, the 60-job default build and
124 tests (one skip). Its independent review and exact checks passed, covering
487 declarations (122 R3, 114 R4; 485 theorems/two definitions), retaining all 485
preceding terminal bodies. The separate history-only protocol covers the existing
concrete callers and every typed initialized Runner trace with both placeholder settings,
including Stops. The `ce12402` R3 source-cut checkpoint passed scoped/full
401/480 jobs, the 485-declaration permitted-axiom gate, fresh stock kernel replay,
60-job default build and 124 tests (one skip); independent review was clear.
Its coordinator register selector initially included the separate claim table;
the corrected remaining pin check passed for all seven rows. Baseline `1a5542d`
passed local callback completion with the same checks over 483 declarations.
These historical validations do not replace the new checkpoint.

Baseline `bcbf733` passed the 480-declaration gate, fresh stock kernel replay,
60-job default build and 124 tests (one skip). Its coordinator's first exact
script failed with SyntaxError before checks; the corrected script passed.
The preceding `a0cf252` carry also passed eleven reproductions (nine accepted
agreements, two pending-dump rejections with accepted pre-delete boundaries).
Those eleven Runner recipes were not rerun at the preceding local-origin checkpoint;
the current carry changes their Runner observers and reruns all eleven successfully.
No differential/guest run was part of that extension. At that historical
checkpoint, initialized R3 packet authorization and R4 credits/conservation
were still open; the current register records their later closure.
The supplementary six-checker export covers only its historical 417-declaration
checkpoint, not later changes.

Runner/anti-replay contracts cover both placeholder settings with the original
exact flood path; the deleted floodExact flag is no longer an API parameter. Timer
contracts retain recorded caller-jiffies operands and failure order. Main repairs
the historical R6 IPv6 rate-table lifecycle source discrepancy; the original
proof-side report did not claim an accepted replay or differential finding.

## Historical pre-split contract table

This table preserves the pre-split contract boundary recorded for the
[pre-release review](2026-10-14-pre-release-review.md) §4. Its open R3 obligations
are historical: the current register and initialized incoming/outgoing reports
above record their closure. The R4 rows below also describe the pre-split
checkpoint; current normal ingress accounting is in the register and its
linked reports. Historical open obligations in this table are not current
status.
These rows describe campaign contracts over mirror `cb2348e`. Preceding checkpoints have passed independent
review and coordinated validation. The initialized committed-support checkpoint passed its scoped/full builds,
exact checks, independent review and coordinated gates. The new configured-identity/session/publication rows
pass independent review and coordinated validation. Arbitrary
incoming local histories still require explicit predicates. The new initialized R3 contract discharges committed
material support from empty history, alongside the established R2/R4 initialized contracts. Initialized configured identity,
packet authorization, copied-trial origin transcripts and initialized R4 conservation
remain explicitly open. The earlier review read proof snapshot `ffea367`,
which was a proof-branch commit, not its mirror revision. Names below are
representative exports; each result's `Statements.lean` gives the complete surface.

| Result | Original claim (charter) | Representative theorems | Event boundary | Substantive premises | Counterexample or remaining obligation |
| --- | --- | --- | --- | --- | --- |
| ReplayWindow S1 | Every accepted execution has its exact acceptance history and no two events share a lifetime and wire counter | `S1` | Committed validator acceptances in a successful `executeTrace`, including packets dropped later; copied scheduler trials are separate | A successful original runner execution, for every placeholder setting. The exact logged execution is a conclusion, not an extra premise | No remaining S1 obligation; the theorem concerns the executable mirror, not all Linux executions |
| ReplayWindow S2 | `counterValidate` returns the receive.c rule's result and replay state | `S2`, `S2_acceptance`, `S2_update` | Original validator versus the Lean `CounterWindow.step` rule | A resident keypair with a 128-word bitmap, established by reachable allocation | No remaining S2 obligation. Identifying `step` with the C rule is a source correspondence claim; the refinement is within Lean |
| ReplayWindow S3 | Nonreceive calls and validator calls preserve the other keypairs' windows | `S3`, `S3_nonreceive`, `S3_validator`, `S3_surviving`, `S3_syscall`, `S3_syscall_ambient` | Surviving old cells; other cells at a validator; whole-syscall evolution including ambient work | The stated lifetime-aware invariant and successful original execution; the nonreceive specialization uses its explicit call classification | Allocation/deletion are permitted and reused slots denote new lifetimes; equality of every store cell was never claimed |
| R1 anti-replay | No repeated acceptance under one lifetime; nothing at or below the floor accepted | `pure_uniqueness`, `mirror_uniqueness`, `runner_uniqueness`, `pure_run_floor`, `mirror_floor`, `mirror_run_floor`, `runner_floor`, `pure_run_below_floor` | Pure window runs, original validator calls and accepted runner histories | The corresponding S1/S2 premises | `inclusive_boundary_witness` and an accepted replay show equality at highest minus 8128 may be accepted. The proved exclusion is strictly below the floor |
| R2 lifetime safety | No dead identity is resolved after release | `runner_audit_erasure`, `runner_initialized_access_safety`, `runner_initialized_reached_trials`; prior store, access and caller-family contracts | Original initialized Runner, every typed Trace and both placeholder settings; committed failed histories and separately certified copied trials at actual reached filter entries | No parser, hidden-array length, progress, success or initial allocation premise on the initialized exports. Local helper premises are discharged by original initialization, successful prefill and concrete caller contracts. Erasure holds for arbitrary incoming history; initialized safety starts from empty history | The stated allocation-identity access property is closed; coordinated validation passes. No failed World is asserted. Reference affiliation/credit, routing authorization, pipeline conservation, C memory safety and executable diagnostic output are separate. The raw stale-cursor witness retargets a replacement identity; its historical runner recipes now reject before deletion |
| R3 cryptokey routing | Lookup follows insertion/removal history; incoming and outgoing packets are bound to the owning peer | `pureTree_lookup_correct`, `original_findNode_lookup_correct`, `original_insert_longest_prefix`, `original_add_all_cases`, `original_insert_all_cases`, `pure_removal_entries_and_lookup`, `original_removal_*`, `original_removeStep_forest_*`, `original_removeStep_then_findNode`, `original_removeByPeer_forest_*`, `original_removeByPeer_then_findNode`, `original_insert_routing_preserved`, `original_insert_coherent_peer_maps`, `original_insert_refusal_coherent`, `original_removeByPeer_routing_preserved`, `original_peerCreate_routing_*`, `original_peerPut_routing_preserved`, `original_initialized_routing_history`, `original_initialized_history_findNode`, `parsed_setAllowedip_bounded_call`, `parsed_setAllowedip_routing_preserved`, `original_rootRemove_lists_normal`, `original_free_routing_endpoint`, `original_free_then_findNode`, `original_routing_silent_frames`, `routing_completion_source_erasure`, `setAllowedip_completion_routing`, `original_peerConfigTail_routing_prefix`, `original_peer_update_completion_erasure`, `original_peer_removal_routing_prefix`, `original_peer_update_routing_prefix`, `original_configuration_acquisition_routing`, `original_setPeerCmd_completion_erasure`, `original_setPeerCmd_routing_prefix`, `parsed_trace_peer_commands_routing`, `original_device_configuration_completion_erasure`, `original_device_configuration_routing_prefix`, `parsed_trace_device_configuration_routing`, `original_optional_lifecycle_erasure`, `original_optional_lifecycle_routing_prefix`, `original_optional_routing_initialization`, `original_tx_routing_frames`, `original_rx_routing_frames`, `original_traffic_routing_completion`, `original_receive_admission_routing`, `original_concrete_napi_routing`, `original_timer_device_routing`, `original_session_routing_frames`, `original_handshake_receive_routing_frames`, `original_handshake_routing_completion`, `original_scheduler_routing`, `original_environment_worker_routing`, `original_environment_timer_routing`, `original_environment_traffic_routing`, `original_environment_controls_completion`, `original_dump_routing`, `original_routing_runner_erasure`, `original_syscall_routing_prefix`, `parsed_initialized_routing_execution`, `original_nullable_index_affiliation`, `original_nullable_session_affiliation`, `original_packet_affiliation_cuts`, `original_routing_lookup_and_packet_shapes`, `original_packet_routing_source_cuts`, `original_session_material_receipts`, `original_rx_origin_receipts`, `original_session_material_retention`, `original_decrypt_material_history`, `original_index_material_retention`, `original_origin_history_injection`, `original_origin_history_projection`, `original_material_retaining_leaves`, `original_material_retaining_traffic`, `original_material_retaining_lifecycle`, `original_origin_support_cuts`, `original_origin_support_callers`, `original_origin_support_environment`, `original_material_retaining_configuration`, `original_material_retaining_dump`, `initialized_committed_material_support`, `original_configured_peer_identity`, `original_configured_session_support`, `original_rx_publication_identity` | Represented tries versus an independent flat-prefix winner; pure removal, every raw original removal arm, unified represented-forest target removal and complete coherent peer removal; initialized finite original-call histories and reached-root lookup; local actual-parser/guard insertion cuts and complete normally returned WG.free; whole-setAllowedip/removal completion journal and actual original acquired-peer update, retaining safe earlier completions on Stop; complete public peer command with derived lookup/create residency; public parseTrace supplies every configured peer's address shape; complete original device configuration observes clear before remove-all cleanup, with empty folded tables after normal remove-all; optional-device state through guarded creation/down/destruction/deletion and absent configuration, initialized from every fixture/prefill mode; silent whole TX/Stack/RX calls, receive admission, concrete NAPI/crypt callbacks, timer callbacks, device controls, session helpers and the complete handshake receive/actual worker iteration, full scheduler, deferred workers, both environment timer modes, complete receive worker/ingress/batch/control and stepped/whole dumps retain routing on normal return; Env deletion observes actual lifecycle completions; original syscall wrappers/dispatch/suffixes and initialized parsed Runner retain safe completed histories and normal final-World agreement | Insertion uses the stated address bounds, fresh IDs and resident target. Removal derives local linkage/separation from ForestRep, Compressed, Nodup and explicit target membership; validity additionally supports lookup. Complete peer removal also assumes a resident target and explicit resident-only list coherence, which it preserves. Original insertion covers bounded-input normal returns, including allocation refusals. Explicit RoutingInvariant additionally supplies resident list coherence and node/peer/owner frontier bounds, all preserved by these insertion/removal calls; owner bounds do not imply residency. Finite histories instead derive this invariant from the original configured fixture and actual normal create/insert/remove/release/clear calls; only insertion carries reached-input bounds/residency, and query bounds are explicit. Local parser success derives address shape; setAllowedip guards derive family/CIDR/width bounds. Root-list clearing uses resident-list ownership and a represented subtree. Full clear uses the explicit entry RoutingInvariant and original normal return; its source-derived endpoint empties represented roots/lists, preserves complete peers except lists and other Kernel/device fields except roots/sequence, and permits only node deletions. Neither requires owner residency. Completion-stage semantics use explicit entry RoutingInvariant/flat agreement, resident insertion target and local attribute shape; actual insertion outcomes preserve loop residency, while concrete send/flush/cleanup frames permit later deletion. The complete public setPeerCmd contract derives target residency through actual lookup/create outcomes, requiring only entry routing/flat agreement and local address shape. Successful public parseTrace discharges that shape for its configured peers, without excluding malformed entries. The present-only device contract retains routed entry. The optional lifecycle/configuration contracts use GlobalCompletionState: absence denotes empty flat tables, while presence retains routing/flat agreement. DeviceAddressShape is discharged by successful public parsing; no fixture-authenticity, saved-list, drain or credit premise is added. Actual fixture initialization handles all net/bare flags, and successful prefill preserves it. Silent traffic frames add no resident-owner, credit, affiliation, valid-packet or drain premise; generic callback arguments require RetainsRoutingCall, with actual checksum and Stack callbacks discharged. The concrete NAPI/crypt, admission, maintenance, handshake, scheduler, deferred-worker and environment-timer, ingress/batch/control and dump contracts require no callback, residency, affiliation, credit, cursor-validity or successful-trial/drain premise. Environment deletion starts from GlobalCompletionState and retains its actual pending-dump guard. Full initialized execution derives entry state from original fixture/prefill; both safe-history and normal-state semantics require TraceAddressShape on arbitrary typed traces, discharged by successful public parseTrace. Whole-result erasure to a literal Json × World source Runner and its JSON projection are unconditional for typed traces, both placeholder settings and arbitrary incoming history. Failed outcomes carry safe completed history, not a returned World. New affiliation contracts use local nullable Inv, bounded optional creation input or References for rotation; actual successful acquisition derives non-NULL/positive credit instead of assuming it. The invariant permits slot aliases, absent references and cleared words; it does not establish initialized reachability, index provenance or unique allocation stamps | Initialized configuration-history agreement is proved at the final actual World. New local normal lookup and exact RX/TX source cuts require RoutedView at their actual entry; constructor shape and RX source/family preservation are derived. Connecting those local cuts to earlier initialized history and historical configured-key identity remains open; copied-trial packet transcripts are optional separate coverage. TX handoff denotes staged splice, not later encryption or wire-send. Literal source factors expose local acquisition expressions; a snapshot OwnerCertificate is not an execution/reachability witness. Clear totality and physical-node emptiness are not asserted. New local session/admission/decrypt receipts retain actual connected source runs and complete record/material equations; normal None front receipts do not imply successful derivation/allocation. Full R2 projection requires AllocationInv on the same incoming projected history; original erasure is unconditional, and receipt validity is preserved from valid incoming history (empty qualifies). Local supplied-history material matching is now proved with one material/owner witness and exact earlier-journal decomposition. That premise does not establish initialized occurrence chronology, unique historical allocation or packet/session peer identity. Actual acquireOwner/indexLookup full-material retention now holds for arbitrary normal runs, with no affiliation, non-NULL, credit or residency premise. The existing access adapter preserves supplied session support normally and receipt validity on Stop. Actual session/decrypt cuts now feed the persistent caller history with same-input full audit projection and unchanged R4 predicates. Concrete non-installing traffic, timer, clear/removal and guarded lifecycle calls now retain receiving material at normal endpoints and transport supplied support; no state is asserted on Stop. Supplied material support now composes through the actual session/decrypt, poll, scheduler and complete deferred/remaining Env observers. Every decrypt receipt is checked against its actual captured World and strict earlier session prefix, and saved probes retain the exact prior lifetime history and saved-World support; normal endpoints preserve state and Stops retain checked history only. This origin-only history predicate is not R2 validity or invalid-key carrier ownership. Generic worker wrapping requires its body contract; concrete environment instances discharge it. Concrete configuration and full/stepped dump support now compose through every actual syscall wrapper, dispatch arm and post-worker. Original initialization/prefill discharge committed support for all typed traces and both flags, including Stop, with no added trace or World premise. Each actual successful decrypt has its stored packet/key/AEAD evidence and a successful derivation-front receipt in the strict earlier committed prefix (whole beginSession completion or Noise authentication is not claimed); saved probes retain exact prior lifetime history and captured-World support. New local configured-table/source/session/publication contracts retain a single historical configured Context and actual fresh decrypt receipt, with exact AEAD and pre-IRQ stored-packet/stamp evidence. Their configured support and nullable RX compatibility are supplied premises; whole normal session tail and successful decrypt are explicit. Initialized configured identity, current peer/key allocation continuity, ingress injection, transport to Stack and earlier lookup-history alignment remain open. Ordered copied-trial origin transcripts are optional separate coverage. A raw peer-slot winner is not yet identity authorization; no accepted misrouting counterexample is claimed |
| R4 delivery | Per-peer/key delivery follows receive order for every recorded schedule; loss occurs only at explicit arms | `two_carried_slots_*`, `original_enqueue_epipe`, `original_poll_selected_callback_complete`, `original_poll_removal_ordinals`, RX/TX ring-journal families, `original_rx_scheduler_*`, `original_rx_consistency_*`, `original_lookup_*`, `original_tx_disposition_*`, `original_tx_strict_reference_cut`, `original_create_data_*_endpoint`, `original_dead_tx_step_disposal`, `joint_poll_correspondence`, `joint_poll_fresh_history`, `joint_poll_removal_identity_safety`, `joint_poll_callback_identity_safety`, `joint_poll_callback_removal_provenance`, `joint_poll_callback_entry_prefix`, `joint_poll_capture_read_suffix`, `joint_poll_suffix_lifetime`, `joint_poll_persistent_correspondence`, `joint_poll_boundary_composition`, `joint_poll_finite_sequence`, `original_napi_softirq_joint`, `original_inline_poll_joint`, `original_napi_irq_exit_joint`, concrete crypt-worker/activation-iteration contracts, `original_activation_run_joint`, `original_dispatch_joint`, `original_recorded_schedule_joint`, `original_nested_reschedule_joint`, `original_deferred_workers_joint`, `original_inject_joint`, `original_flood_joint`, `original_batch_joint`, `original_environment_deferred_joint`, `original_environment_remaining_joint`, `original_syscall_family_joint`, `initialized_runner_joint`, `original_callback_return_execution`, `original_poll_callback_completion`, `persistent_poll_callback_completion`, `original_caller_callback_completion`, `initialized_runner_callback_completion`, `original_poll_disposition_receipts`, `original_poll_occurrence_dispositions`, `persistent_poll_disposition_receipts`, `original_poll_packet_receipt_links`, `persistent_poll_packet_receipt_links`, `original_caller_packet_receipt_linkage`, `initialized_runner_packet_receipt_linkage`, `original_rx_credit_transfer`, `original_rx_cleanup_supported_cuts`, `original_rx_cleanup_totality_refuted`, `original_rx_cleanup_normal`, `original_staged_send_rx_protection`, `original_consume_data_done_rx_protection`, `original_stack_rx_protection`, `original_poll_carrier_conservation`, `original_consume_data_carrier_conservation`, `original_consume_data_stable_rx` | Physical ring mutations, reached prefixes, poll removals and selected GRO callback entries; concrete RX scheduler, direct NAPI and crypt-worker callers, complete activation/dispatch/scheduler calls, deferred crypt/send processing, injection, the exact flood path, batch item/full processing, both timer/wait modes, observation, lifecycle/control families, complete syscalls and every initialized typed Runner trace with exact saved trial probes; ordered callback receipts through every typed initialized Runner trace and both placeholder settings | Explicit callbacks for the local worker families; concrete RX scheduling discharges its callbacks. Initialized conservation uses a prior refined ring history; retired/stale structural representation requires positive ring size. The W7 endpoint contracts assume normal return and their stated entry live-peer/capacity/full-ring or actual logical-DEAD-head conditions. The joint poll starts a fresh local metadata journal with arbitrary prior lifetime history satisfying AllocationInv; no per-iteration freshness, queue-uniqueness or release premise is added. Releases are asserted only on normal return. Finite poll composition starts from AllocationInv; its persistent boundary additionally retains audit/probe validity, previous entry distinctness and their observed releases. These boundary properties are derived by initialization and composition, not assumed per poll iteration. The direct NAPI, crypt-worker, complete scheduling and complete local environment-family contracts retain this same entry invariant; their empty-history corollaries require only local AllocationInv. The initialized Runner discharges the boundary invariant from original initialization/prefill and actual returned Worlds, with no parser, array-length, progress, success, drain, credit or initial-allocation premise. Actual saved probes derive allocation validity and ordered copied-trial safety; they are not committed callback entries. Local completion uses only a Closed incoming callback journal; initialized Runner discharges it from empty history for all typed traces/both placeholder settings, with no parser/allocation/residency/progress premise. Failed prefixes retain valid receipts and permit one unfinished trailing entry; completed stamps inherit entry uniqueness | Accepted `r4-gro-reorder` refutes chronological post-GRO order; `SelectedGroSafe` gives the source-selected callback order; the GRO carry replaces the former static normal-before-held partition. Local W7 source cuts and normal EPIPE/ENOSPC/DEAD-step endpoints are checked; initialized transport between those endpoints, initialized ingress/decrypt-worker propagation and joint receive-pipeline conservation remain open. Every initialized Runner normal return has matching ordered entry/receipt lists and actual Stack execution witnesses; they do not imply inbox arrival. Both direct poll sites, their crypt-worker callers, complete local scheduling and all deferred/remaining Env constructors, complete syscalls and initialized Runner execution are observed exactly, including full audit probe correspondence. Capture/read support, exclusion of prior releases, exact audit projection and cross-poll entry uniqueness for finite original-poll sequences are proved; a generic focused audit frame does not observe any polls hidden in its callee. Universal outgoing conservation is additional scope. Fresh local occurrence partition and new receipt validity need no allocation premise; stopped residuals are unresolved selection, the whole unentered selected-offer suffix and at most one unfinished callback. Normal return has no residual. Local captured packet/stamp/peer and strict same-journal whole-receipt linkage are proved; preserving arbitrary prior history requires its explicit HistoryLinked. Initialized linkage and separate checked-receipt validity now hold for every typed trace/both flags, including Stop, with no new World or trace premise. Exact full audit/probes, completion and distinctness are retained. Global strict order does not label same-poll segments; the local fresh-suffix theorem remains separate. Local credit cuts now derive lookup loans, fresh reservation transfer, actual cached-head selection, pure-IRQ balance and successful ENOSPC cleanup from explicit same-ledger inputs. Vacancy and successful key payment remain visible; those older cuts did not assert whole consumeData composition; the new local composition proves it, with initialized carrier protection still open. Full staged-send and consumeDataDone now preserve the same supplied Inventory/QueueOwners/Protected on normal endpoints under nullable current-key/packet-key compatibility respectively, with source-derived exact TX/send-work append/reference deltas. These are not output compatibility, TX ownership or pending-work correspondence claims. Concrete Stack callbacks now preserve that same supplied product, with exact nonempty-delta destination repayment. Separate key-word/current-slot frames preserve nullable compatibility. The original normal poll retains the original ledger filtered by its fresh observed removals, with removed storage absent and normal nondelivery/completion partition; it permits deletion, requires no surviving caller/base reservation or totality, and may retain uncrypted queued carriers. These explicit local premises are not initialized closure. Whole normal admission now joins its exact actual receipt and enqueue/finish witness to the outcome-selected carrier ledger. StableRx preserves all-queued/uncrypted-ring/cold-head structure; the separate actual ring observer supplies its appended safe/refined journal, and stable ring-empty/NAPI-cold forces empty RX inventory/store even at size zero. General IRQ framing, key/session identity, initialized ingress/decrypt-worker and lifecycle/work correspondence remain open. Callback entry is not delivery, local ordinals are not global identities, and a stopped prefix has no retained World |
| R5 key lifetime | No encryption/decryption past the reject time or counter; no use after zeroing | `original_decryption_admission`, `original_accepted_wire_nonce`, `original_staging_admissions`, `original_zero_timer_preserves_transport_keys`, `receive_guard`, `original_age_*`, `original_receive_attempt_*` | Decryption/staging admission, exact recorded clocks, the zero timer's local effect and observed attempts | The stated original-call, recorded-clock and counter premises; the environment admits worker latency unbounded by virtual time | Accepted replays authenticate a past-limit nonce before rejection and encrypt queued material after expiry or clear. These follow the C's order and were [reviewed as statement artefacts](2026-10-13-review-r5-counterexamples.md). Rule Zero resolution does not assert universal enforcement or a universal replacement bound |
| R6 flood resistance | An initiation without valid MAC2 cannot pass the under-load cookie gate; retransmission stops at MAX | `original_invalid_mac2_cookie_only`, `original_invalid_mac2_noise_preserved`, `original_invalid_mac1_drop`, `original_under_load_queue`, `original_under_load_decay` | Actual load-phase execution and cookie suffix; Noise preservation on normal completion | `FailedMac2` with its prefix, clock and actual cookie-execution premises | Accepted 19-retry/20-initiation episode refutes literal MAX=18. No universal corrected retry bound, real-load reachability, CPU/memory bound or availability guarantee is claimed |

The counts below are declaration counts, not counts of completed charter
properties. Exports include semantic properties, refinements, erasure and frame
contracts, failed-prefix statements and concrete boundary witnesses. One theorem
can combine several of those roles, so they are described in the rows rather
than forced into disjoint numerical categories. Runtime replay programs are
checked separately and are not included in the terminal declaration count.

| Result | Current source declarations | Theorems | Helper definitions |
| --- | ---: | ---: | ---: |
| ReplayWindow | 15 | 13 | 2 |
| AntiReplay | 9 | 9 | 0 |
| LifetimeSafety | 202 | 202 | 0 |
| CryptokeyRouting | 289 | 289 | 0 |
| DeliveryOrder | 326 | 326 | 0 |
| KeyLifetime | 13 | 13 | 0 |
| FloodResistance | 6 | 6 | 0 |
| Total | 860 | 858 | 2 |

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
| Paired input-driven insertion increment (paused; external gate pending) | `Insert.insert_checked`, `insert_simulation`, `InsertSequence.sequence_checked`, `Witness.check`, `Witness.executes`; `RandomService.return_recorded` | `cb2348e` | Conditional full insertion and arbitrary finite retained-heap composition, including reinsertion and arbitrary accepted retries. Every return exports reconstruction and remaining supplied input. Thirty-two mixed sequences pass (416 calls, 434,064 instructions); four exact formal-witness executions and the full captured replay pass. Fresh review found an internal private-role alias and missing replay identities; both are repaired and independently rechecked. Revised default/executable builds, trust gate, fresh full-closure kernel replay, provider regression and identity tests pass. Corrected export: `5433d778`, root `PairInsertionSurface` and full closure, `.tmp/binary-pair-insert-reviewed.ndjson`; external acceptance pending. Sequential environment, permission and universal service/coupling hypotheses remain explicit and unproved; no concurrent campaign or external-gate claim. Mirror lags main. [Charter](2026-10-18-charter-paired-index-insertion.md), [report](2026-10-18-paired-index-insertion.md), [review](2026-10-18-review-paired-index-insertion.md). |
| Shared callback image proofs and first-return index clients | `Callback.{pc_contract,cmp4_contract,const_cmp4_contract,const_cmp1_contract,bh_contract}`; `IndexLookup.lookup_first_return`, `Remove.remove_first_return`, `Replace.replace_first_return`, `Sequence.First.sequence_checked`; insertion image corollaries | `cb2348e` | Five existing callback contracts proved from the pinned image, reused by the index family. Lookup/remove/replace and finite non-inserting sequences retain unchanged executable entry/reconstruction and export first-return histories with explicit environment/permission hypotheses. Insertion retains its broader permissions and random contracts. Code builds with standard axioms; generated callbacks, independent function comparisons, exact witnesses and 496 retained-heap sequence calls pass. Complete locally in about two elapsed hours: full trust gate, fresh full-closure replay, independent review and actual captured insertion replay pass; export at `86ea5488` is ready, external acceptance pending. No concurrent campaign coverage claim; mirror lags main. [Charter](2026-10-19-charter-paired-callbacks.md), [report](2026-10-19-paired-callbacks.md), [review](2026-10-19-review-paired-callbacks.md). |
| Allowed-IPs binary scaling (closed partial experiment) | No new completed function and no insertion or subsystem adequacy claim; tested component theorems only | `ac55c7d5` (including fixed-width counters at `1f766662`) | Strengthens the existing lookup to the extended executable reconstruction/heap assertion; reuses `common_bits` at both insertion sites; proves the placement loop, exact-prefix reassignment, empty-root initialization/publication, nonempty initialization, and continuous child attachment from tested local boundaries. Separate return segments remain uncomposed with the whole function. Entry establishment, allocator contracts, covering/intermediate insertion, failure/rollback and full function/sequence composition remain open; neither charter checkpoint completed. Zero newly completed functions at four hours and at closure. The retained generated/recorded/captured tests are distinguished in the report; tests are not adequacy theorems. The sequence-counter mirror defect is fixed on main and all eight unchanged binary witnesses pass, with no Pre/R narrowing. Kraken patch nine (register BT) is pinned and included in the printed trust surface. No external acceptance of the added closure is claimed. Manual insertion work is stopped; typed-heap-view R1 is a separate post-landing increment. [Charter](2026-10-20-charter-binary-allowedips.md), [review](2026-10-20-review-binary-allowedips-charter.md), [closing report](2026-10-20-binary-allowedips.md#experimental-close-and-landing-preparation). |

The isolated landing carry is `task/binary-pair-landing`, rebased onto main
`3308c49a`. It invokes the split mirror through transparent source adapters;
there is no legacy operational mirror copy. Its s5 relocation and current
validation are tracked in the [landing report](2026-10-19-binary-landing-assessment.md).
The rows above describe their original checkpoints, rather than claiming
that their old external gates accept the landing carry. On 2026-10-19 the user
ran the external `lake check --from-export` gate outside Nono on the new export
at code commit `736492453c292ba9caafa78b353ae19f4ce9671b`, rooted at
`LookupSnapshotTransport`, `LookupWitness`, `LookupHitWitness`,
`AllowedipsWitnessPre`, `PairCallbackSurface`, and `PairCallWitness`, including
their complete declaration closure. The Lean default kernel accepted it using
only `propext`, `Quot.sound`, and `Classical.choice`. The standalone gate
is `scripts/binary-proof-gate`; outstanding M1 obligations (including realism,
initial frame representation, and witnesses for the NULL-owner and mode-3
wrong-kind cases) remain open. No concurrent or whole-WireGuard result is added.

The concrete frame instance `lookup_snapshot_transport` carries exact
frontier and source-live lifetime/replay fields through lookup, conditional
on their initial representation and untouched-byte separation. It does not
prove physical allocation membership/absence or whole-trace S1–S3/R1–R6/H1–H6.
Those results need their remaining anchors and the milestone-4 entry-realism
check. The mirror proof register's existing lag is unchanged by this work.

Source-81 `4656199a` expands the actual key/device lookup, owner dereference and index writeback source points. Reservation getter cuts retain the original captured before-state and the selected cohort on the same ledger. Queued-initiation interiors and complete initialized caller coverage remain open. The four-module delta passes the 4244-job root build, the 1563-declaration gate across thirteen roots and all 33 standard-or-empty public-declaration queries. All 4197 frozen hashes and fifty inherited carry paths match. Fresh replay and the twelve recipes last passed at source-80 `0fc64409`; they were not repeated for this intermediate checkpoint. Main and mirror are unchanged.

Source-82 `1b41a945` extends queued-initiation coverage through its native decision/install source, cached peer reads and writes, and the fixed peer-release points. The same invocation borrow proves repayment nonfinal; the original ledger is retained even before its receipt. Existing restored-staging and keepalive joins carry these expanded points and their original continuations. Universal initialized caller composition remains open. The seven-module delta passes 4247 root build jobs and all 60 standard-or-empty public-declaration queries; all 4200 frozen hashes and fifty inherited carry paths match. The aggregate gate last passed at source-81, and fresh replay plus all twelve recipes at source-80. Development elaboration failures and an unused simp argument were repaired before validation. Main and mirror are unchanged.


Source-83 `19c14c21` joins allocation intervals and canonical creation points to the original selected staging invocation, including keepalive, on the same ledger. Fixed nested key-release points preserve that ledger and the original source continuation; native erasure before its lifetime receipt is included. Nested peer release, refused cleanup interiors and complete initialized caller composition remain open. The nine new modules pass 4256 root build jobs, the 1563-declaration gate across thirteen roots, all 33 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4209 frozen hashes and fifty inherited carry paths match. Development elaboration failures (including failed declaration elaboration) and frame-proof heartbeat failures were repaired before these passing checks; no accepted holes or mirror finding remain. Main's landed carry at `3308c49a` is merged at `ab65f1fd`; it changes only the register note relative to the validated sources, and every frozen proof hash still matches. No differential result is added by this proof-only checkpoint; the inherited Env deprecation remains outside scope.


Source-84 `2621e227` derives refused-cleanup loop entries from the original admission and repayment runs; accepted creation cannot enter this loop. Ordered free cursors retain the same ledger lineage, and both post-erase intervals carry the actual pending terminal receipt. Staging and keepalive joins retain their original continuations without incoming cleanup accounts. Nested peer release and universal initialized caller composition remain open. The four-module delta passes 4260 root build jobs and all fifteen standard-or-empty public-declaration queries; all 4213 frozen sources and fifty inherited carry paths match. The aggregate gate, fresh replay and twelve recipes last passed at source-83. Development namespace, implicit-index and dependent-equality elaboration errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged.

Source-85 `36239b83` joins the five fixed nested peer-release stages, final native erasure, pending lifetime/count records and finish points to the canonical creation call and original staging or keepalive invocation. Each point retains the original ledger lineage and literal continuation; the post-erase account records the actual pending receipts. Creation mutation interiors and universal initialized caller composition remain open. The seven-module delta passes 4267 root build jobs, the 1563-declaration gate across thirteen roots, all 54 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4220 frozen proof hashes and fifty landed carry paths match. Development elaboration and focus/frame errors were repaired before validation; no accepted holes or mirror finding remain. Main and mirror are unchanged. No differential result is added; the inherited Env deprecation remains outside scope.

Source-86 `f52dbdb9` joins creation's silent packet marks and queue installation to their original source paths, deriving live phases before access and queued receipts. The combined creation family includes canonical/key-repayment points, mutation cuts, refused cleanup and nested peer release, with source-only continuations and staging/keepalive joins. Universal initialized caller composition and finer atom interiors remain open. Its five new modules pass 4272 root build jobs and all nineteen standard-or-empty public-declaration queries; all 4225 frozen proof hashes and fifty landed carry paths match. Source-85 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and implicit-index errors were repaired; no mirror finding arose. Main and mirror are unchanged.

Source-87 `650a4aff` assembles the canonical staging tree and its reservation, rejected-key repayment, queued-initiation, allocation and creation children with source-only continuations and same-ledger evidence. The initialized receive scheduler derives its staging contract, leaving five explicit deeper packet families: routed transmit, IPv6 receive, encryption, peer transmit and handshake. Expanded keepalive points preserve their actual preparation admission and supply the timer keepalive contract. Finer primitive interiors and universal initialized caller composition remain open. The seven-module delta passes 4279 root build jobs, the 1563-declaration gate across thirteen roots, all 39 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4232 frozen proof hashes and fifty landed carry paths match. Namespace and source-context elaboration failures were repaired before validation; no accepted holes or mirror finding remain. Main and mirror are unchanged; no differential result is added and the inherited Env deprecation remains outside scope.
