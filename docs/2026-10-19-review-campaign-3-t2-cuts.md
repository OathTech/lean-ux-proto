# Campaign 3: conservation cuts review

This source review examined the T2 integration at `2ecd2305`, the native
outer companion at `cb865cce`, and the selected-anchor/consequence extension
at `8ea37838`. References below give declaration locations in those pins.
The review covered the conservation interfaces, their composition, and
representative native mutation intervals. It did not run another build or
kernel replay, and is not an exhaustive verification of every source leaf.

The remaining findings are proof-coverage gaps. No executable-mirror
counterexample was found. The inspected conclusions do not yet establish
T2's conservation requirement throughout the run.

## 1. High: returned-history safety does not cover every internal prefix

At `2ecd2305`, [PrefixEnsures](../Leanux/Proofs/Logged/Prefix.lean#L108)
requires safety of the history returned by the supplied action. Its normal
postcondition concerns the returned state. On failure it retains history
safety, but has no returned-state obligation. This is an appropriate local
contract; it does not quantify over all earlier prefixes of a successful
action. In `PrefixEnsures.bind` at line 141, the successful composition
exports the second action's safety certificate; the first action's
certificate is not retained in the conclusion.

[CompleteProduct.Safe](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteProduct.lean#L16)
does not itself require prefix closure. The generic
[CompleteRunner.initialized](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteRunnerInitialized.lean#L12)
concludes safety only for the history returned by the whole execution
(line 22). Quantifying this theorem over operation lists gives operation
boundaries, not arbitrary intermediate points inside an operation.

The `8ea37838` consequence layer does not fill this gap:
[CompleteConsequences.forward](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteConsequencesPartition.lean#L98)
starts from safety of one history and partitions the births of that history.
It adds useful same-ledger consequences, but no quantifier over earlier
histories. A terminal ledger for the final history also cannot simply be
reused for an earlier history: its birth domain and terminal evidence refer
to events that may not yet have occurred.

**Consequence.** A successful or stopped execution can have an accounted
returned history under these types without the exported theorem supplying
the required account at every earlier internal prefix. This is a missing
theorem, not evidence that the local contracts or kernel-checked proofs are
false.

## 2. High: the accounted branch forgets its actual execution cut

At `2ecd2305`, the `accounted` constructor of
[CompleteTransmit.Safe](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteTransmit.lean#L13)
accepts `Accounted h ledger debts locals w`. Neither its indices nor its
argument relate `w` to a particular execution. Correspondingly,
[Safe.cuts](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteTransmitCuts.lean#L14)
exposes an existential accounted world in its first branch. `Safe.account`
at line 30 forgets still more structure. The description of a connected
native snapshot at line 27 is stronger than the first branch's public type.

`8ea37838` improves the selected branch: `CompleteSelected.Ready` and
`Active` now retain
[NativeAnchor](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteConsequencesSelectedAnchor.lean#L10),
which names the recorded take's after-state and its native ownership
invariant. However,
[CompleteConsequences.safe_cut](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteConsequencesFrontier.lean#L71)
still obtains its accounted world directly from the original constructor.
Its `Cut` structure at line 22 has native ownership predicates, but no
reached-execution relation for that branch. Calling this world a retained
source cut therefore needs an additional source-level theorem or a stronger
certificate.

There is reusable stronger evidence locally. For example,
[CompletionBatch.IndexedFrontier](../Leanux/Proofs/WG/AuthenticatedEffects/AllocatedObligationCompletionIndexedAccounting.lean#L69)
retains the owned state, its history prefix, the actual failing suffix run,
and equalities identifying the last ledger cut. Global conversion to
`Safe.accounted` loses this relationship. The normal native companion in
`cb865cce`,
[Outer.syscall_normal](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteRetiredPeerOuterSyscall.lean#L57),
correctly relates its witnesses to the actual returned world; it covers
normal endpoints and cannot repair this stopped/intermediate-cut interface.

**Consequence.** The abstract partition and native pending-location
predicates are useful, but their existential snapshot alone does not state
that those locations belong to the actual execution point being claimed.

## Native intervals need a separate bridge

Journal prefixes alone do not enumerate native states. At `2ecd2305`,
[CausalJournal.hooks.allocate](../Leanux/Proofs/WG/AuthenticatedEffects/CausalJournalSource.lean#L196)
uses the single `Journal.allocate` receipt around the entire
`packets.mapM newTxSkb`
([JournalSource](../Leanux/Proofs/WG/TransmitSecurity/JournalSource.lean#L83)).
For a batch with several packets, the original source has an intermediate
state after the first cell insertion and before the next allocation, with
no new journal event yet. The proof of
[Allocation.total](../Leanux/Proofs/WG/HandshakeSecurity/StagedConservationAllocationTotal.lean#L12)
explicitly constructs that intermediate state at line 18.

`Allocation.stopped_entry` at line 32 establishes that allocation cannot stop
partway through a resident-device batch. It does not describe conservation
at intermediate points of a completed batch. This is not an allocator
failure or a demand for per-packet runtime events. The selected tickets may
remain the logical obligations while newly created cells are tracked as
their aliases; the required interval/partial-map relationship still needs
to be stated and proved. The same distinction applies to a native mutation
followed by its receipt emission.

## Concrete repair route

Two complementary extensions appear necessary; these are recommendations,
not completed results.

1. Carry a certificate for all journal prefixes alongside the same normal
   ledger carrier. A possible predicate is
   `PrefixSafe h := ∀ p, p.IsPrefix h → Safe p`. Establish it at each actual
   admission, selection, restoration, allocation, socket and disposal cut.
   Prove a common quiet-suffix extension for events that introduce neither
   births nor terminal demands. Bind, list and Runner composition must keep
   earlier certificates instead of forgetting them. These can be parallel
   proof contracts; changing inherited `PrefixEnsures` is unnecessary.
2. Retain a reached-cut certificate indexed by the actual source invocation,
   including its current ledger, debts, caller locals and run relationship.
   Extend it across silent source intervals with ownership-view or explicit
   active-local facts. Existing completion frontiers and the selected take
   anchor are suitable ingredients. The allocator can use a partial-map
   interval lemma without changing the mirror or journal event type.

The first extension handles event chronology. The second connects the
account to the native execution and addresses points between events. Merely
renaming the endpoint theorem, or rolling back terminal positions in its
final ledger, cannot recover the missing native cut relationship. Once the
stronger source contracts exist, a small final theorem can expose the
charter's throughout-execution partition.

## Verified supporting boundaries

The reviewed terminal-demand definition distinguishes an inner socket result
(including errno) from unsupported-family refusal and later cleanup.
Counted staged disposals retain their native cardinality; same-ledger
`Complete`, `Valid` and `Justified` support terminal converse and uniqueness.
The review found no new defect in these distinctions.

The historical authorization join
[Staged.Origins.initialized_socket](../Leanux/Proofs/WG/TransmitSecurity/StagedSocketFinal.lean#L14)
at `2ecd2305` includes the actual socket receipt, intended peer, earlier AEAD
bytes, historical owning peer, selected current key material and routed or
keepalive birth. This review found no additional missing ownership join in
that statement. It remains distinct from the forward conservation gaps.

The final package must also retain the separate original-transmit refusal
charge theorem: the successful-splice birth domain does not by itself
account for early invocation errors or their GSO counting unit. This is the
already-recorded boundary in the earlier completeness review, not a new
source finding.

## Dispositions

[AGENT 2026-10-19] Both findings are accepted. Finding 1 is fixed at
`eb4f48cc`; finding 2 remains open.

1. `CompletePrefix.Runner.reached` retains every logical journal prefix of
   the original initialized execution, on normal completion and Stop. The
   separate contracts retain the certificate through concrete admission,
   staging, completion, receive, timers, workers, scheduler, traffic,
   configuration, dump, administrative and guarded deletion sources. The
   exported `initialized_every_journal_prefix_accounted` has no incoming
   carrier or callback premise. Aggregate gate, 392 focused public axiom
   queries, fresh root replay and all twelve witness recipes pass. This
   closes the logical-prefix gap without treating a final ledger as the
   ledger for earlier history.
2. Selected stops retain the recorded take and native ownership. The accounted
   branch still needs its source-cut relationship preserved through completion
   and outer composition. Comments that described its existential snapshot as
   connected to an execution have been corrected. This documentation repair
   does not close the proof obligation. `CompleteRunner.normal_cut` now
   establishes the actual initialized normal endpoint, while source-matched
   completion projections retain branch-specific frontiers. General stopped
   provenance and native intervals between receipts remain open. Source-63
   also connects fixed actual worker selection/dequeue/disposal and queue
   installation prefixes to their same-ledger cuts. These local bridges do
   not yet discharge the initialized native-cut obligation.
   Source-64 `e5d73508` additionally derives native dispatch entry from the
   original initialized operation prefix and syscall guards, with its actual
   continuation. Partial allocation aliases and fixed publication, send and
   DEAD-cleanup intervals retain local provenance. Complete initialized
   internal-cut composition and remaining silent intervals are still open.
   Source-65 `f2a9731f` connects original return-callback prefixes and the
   post-transmit crypt/send entries to initialization. Concrete staging
   derives its own allocation preconditions; send-loop and ordered DEAD
   cleanup boundaries retain exact local cuts. These additional connections
   still do not close finding 2.
   Source-66 `da445410` also connects initialized routed-send and first crypt
   scheduler entry, plus the exact selected-worker prefix for stopped crypted
   completion. Native DEAD erasure retains a pending receipt with its fixed
   total suffix, rather than an invalid claim that the erased cell remains
   resident. These bridges pass the aggregate gate, fresh root replay and
   twelve recipes; complete initialized internal-cut coverage remains open.
   Source-67 `7e1ea08f` adds initialized routed-front and pre-receipt cuts,
   original scheduler selection/run prefixes, and initialized TX-worker
   entry after crypt-ahead. The gate, fresh root replay and twelve recipes
   pass. Other caller roots and native interiors remain open; finding 2
   is not closed by these supporting connections.
   Source-68 `f11eadfe` also connects original callback/send-drain scheduler
   paths and direct or nested crypt-ahead encryption entries, retaining the
   actual poll item and original continuation. Aggregate gate, fresh root
   replay and twelve recipes pass. This extends the initialized entry
   coverage; successful interior coverage and other native caller roots
   remain open, so finding 2 remains open.
   Source-69 `2443f3be` derives the initialized front selection account and
   every actual completed send-list prefix, including successful calls,
   through the original completion scope and selected worker. Its combined
   build and 38 focused queries pass; aggregate validation remains at
   `f11eadfe`. These are further concrete source points, not closure of the
   universal interior obligation.

   Source-70 `14a5f051` adds initialized encryption-loop/publication and
   overflow-prefix cuts, and a fixed send-drain point contract covering normal
   and stopped executions. The three child-source contracts remain explicit.
   Combined aggregate gate, fresh replay and twelve recipes pass; finding 2
   remains open until concrete child instances and all caller roots close.

   Source-71 `8526e3e4` adds initialized ordinary cleanup interiors, normal
   and stopped encryption-loop decomposition, publication and native release
   continuations, and canonical scheduler points. Fixed scheduler coverage
   still names the iteration and NAPI child contracts. Gate, fresh replay and
   twelve recipes pass; finding 2 remains open across the remaining callers
   and intervals.

   Source-72 `e1156284` adds initialized take, socket result and release-finish
   intervals. The same ticket cohort survives silent native updates, and the
   actual receipt settles it exactly once. The timer guard and separate work
   and timer writes retain the original initialized continuation. Gate, fresh
   replay and twelve recipes pass; finding 2 remains open for other callers,
   concrete child contracts and stopped socket-front interiors.

   Source-73 `33251831` derives the initialized native dequeue account and
   original continuation across its pending write/removal observations. The
   canonical worker source structurally fills the scheduler iteration leaf,
   but retains eight deeper contracts and external NAPI. Gate, fresh replay
   and twelve recipes pass; finding 2 remains open for the remaining caller
   graph and native intervals.

No mirror change or narrower T2 outcome is adopted.

Source-74 `e3028f49` connects initialized native peek, routed staging selection and runner boundaries to their original continuations. Canonical NAPI now supplies scheduler NAPI and iteration softirq/IRQ-exit contracts; staging and runner source trees retain exact normal/Stop cases and explicit deeper child obligations. The runner boundary account does not claim all native interiors. T2 and the remaining caller/interval worklist stay open. Intermediate validation passes 4037 build jobs, the 1554-declaration gate and 110 standard-or-empty public theorem queries across 34 new modules; all 3990 frozen hashes match. Main, mirror and the 916 inherited proof files are unchanged. Fresh root replay and all twelve recipes last passed at source-73 `33251831`; they were not repeated for this helper checkpoint.

Source-75 `223c63cf` closes the shared peer-release native point family: read, decrement, test, unlink, queue guard, erasure, receipt and release-finish retain their actual world and original continuation. Each cut has the same account or the exact pending receipt and successor; initialized publication and both NAPI/iteration release children use that proof. Canonical creation adds mark/install, EPIPE and refused-free joins; receive consumption and dispatch gain fixed source coverage, and dispatch composes with initialization. Universal creation/staging phase evidence, deeper native interiors and the remaining caller contracts stay open. T2 is not complete. The frozen 43-module delta passes 4080 build jobs, the 1557-declaration gate and 144 standard-or-empty public theorem queries. All 4033 frozen source hashes and 916 inherited files match; main and mirror are unchanged. Fresh aggregate kernel replay passes with retrieved exit 0, and all twelve counterexample recipes pass. This completes aggregate validation of the combined source-74/75 delta; the preceding full replay/recipes checkpoint is source-73 `33251831`.

Source-76 `62e82ce5` derives every canonical creation point from the original unpublished account and pending batch, retaining a successor of that same ledger. Receive endpoint/key/timer helpers and wheel placement now have concrete source coverage; peer release remains shared. Canonical timer services compose through dispatch and initialization. Delivery has no deeper child and its source points and original remainder are derived without callback assumptions; the send drain uses that concrete delivery contract and scheduler construction. Staging phases, lifecycle and other worker/caller interiors remain open, so T2 is not complete. The 53-module delta passes 4133 build jobs, the 1560-declaration gate and 176 standard-or-empty public theorem queries. All 4086 frozen proof hashes and 916 inherited files match; main and mirror are unchanged. Fresh aggregate kernel replay and all twelve counterexample recipes pass with retrieved exit 0. Aggregate validation completed at that checkpoint.

Source-77 `795e8829` closes every fixed encryption-ring polling point with the same ledger and original remainder. Queued initiation now joins concrete receive helpers, wheel placement and peer release; the initialized receive scheduler retains seven named deeper packet-source contracts. Core lifecycle roots derive their boundary coverage from actual entries, including the stronger retirement guard. Partial staging phases cover take, key borrow, nonce guards, restore and the original creation path; whole staging/keepalive and environment lifecycle wrappers remain open. T2 is not complete. The 46-module delta passes 4179 build jobs, the 1563-declaration gate and 157 standard-or-empty public theorem queries. Fresh aggregate kernel replay and all twelve counterexample recipes pass with retrieved exit 0. All 4132 frozen proof hashes match; main, mirror and all 916 inherited proof files are unchanged. Aggregate validation completed at that checkpoint.

[USER 2026-10-19] Carry main `3f3879e0` into the campaign branch and repair the affected proof frames; main itself and remotes remain unchanged. [AGENT 2026-10-19] Source-78 `df10ef27` preserves eleven helper modules before that carry: concrete environment lifecycle dispatch and scheduled work/service joins. Scoped builds (2836 and 3028 jobs) and all 58 public theorem axiom queries passed against the old mirror. At that intermediate point, source-77 was the last complete aggregate checkpoint and the results lagged the newly carried mirror.

The inherited carry for main `3f3879e0` is separately validated at
`74b03922`, `0c8f59fb`, `7a189c9e`: 975 build jobs, 895 standard-only terminal
axiom queries, eight focused queries, fresh kernel replay and twelve recipes
pass on a detached copy. No existing theorem signature is changed or deleted.

Source-79 `8d9bfbca` combines the separate C3 carry with the eleven source-78 helpers and forty-seven staging, timer and prepare handoff modules. All are connected to the root build. Staging reserve/repayment/queue phases retain the original account and continuation; canonical timer callbacks retain purge and zero-key intervals; prepare retains RX residency and cached-peer obligations. Its canonical frame premise, deeper staging/timer children and the remaining caller contracts are still explicit. T2 remains open. The combined tree passes 4239 build jobs, the gate's 1563 terminal declarations across thirteen roots, 774 standard-or-empty public-declaration queries over the 85-module delta, fresh aggregate kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4192 frozen proof hashes match. Main and mirror are unchanged, and all fifty validated inherited carry paths are unchanged. C3's proved claims are now current over mirror `3f3879e0`, with their named assumptions and boundaries retained.

Source-80 `0fc64409` derives the complete preparation frame from the actual getters, RX residency and cached publication peer. Every fixed preparation point retains the same ledger and its original continuation, including writes before their access receipts; both outer history projections are carried into the shared hook. The initialized receive scheduler now derives its prepare contract and retains six explicit deeper families: receive staging, routed transmit, IPv6 receive, encryption, peer transmit and handshake. Finer native-atom interiors and the other caller/interval work remain open; T2 is not complete. The seven-module delta passes the 4243-job root build, the 1563-declaration gate across thirteen roots, all 43 standard-or-empty public-declaration queries, fresh aggregate kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4196 frozen proof hashes match. Main, mirror and all fifty validated inherited carry paths are unchanged. Development elaboration and history-normalization failures were repaired before these passing checks; no mirror finding arose.

Source-81 `4656199a` expands the actual key/device lookup, owner dereference and index writeback source points. Reservation getter cuts retain the original captured before-state and the selected cohort on the same ledger. Queued-initiation interiors and complete initialized caller coverage remain open. The four-module delta passes the 4244-job root build, the 1563-declaration gate across thirteen roots and all 33 standard-or-empty public-declaration queries. All 4197 frozen hashes and fifty inherited carry paths match. Fresh replay and the twelve recipes last passed at source-80 `0fc64409`; they were not repeated for this intermediate checkpoint. Main and mirror are unchanged.

Source-82 `1b41a945` extends queued-initiation coverage through its native decision/install source, cached peer reads and writes, and the fixed peer-release points. The same invocation borrow proves repayment nonfinal; the original ledger is retained even before its receipt. Existing restored-staging and keepalive joins carry these expanded points and their original continuations. Universal initialized caller composition remains open. The seven-module delta passes 4247 root build jobs and all 60 standard-or-empty public-declaration queries; all 4200 frozen hashes and fifty inherited carry paths match. The aggregate gate last passed at source-81, and fresh replay plus all twelve recipes at source-80. Development elaboration failures and an unused simp argument were repaired before validation. Main and mirror are unchanged.


Source-83 `19c14c21` joins allocation intervals and canonical creation points to the original selected staging invocation, including keepalive, on the same ledger. Fixed nested key-release points preserve that ledger and the original source continuation; native erasure before its lifetime receipt is included. Nested peer release, refused cleanup interiors and complete initialized caller composition remain open. The nine new modules pass 4256 root build jobs, the 1563-declaration gate across thirteen roots, all 33 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4209 frozen hashes and fifty inherited carry paths match. Development elaboration failures (including failed declaration elaboration) and frame-proof heartbeat failures were repaired before these passing checks; no accepted holes or mirror finding remain. Main's landed carry at `3308c49a` is merged at `ab65f1fd`; it changes only the register note relative to the validated sources, and every frozen proof hash still matches. No differential result is added by this proof-only checkpoint; the inherited Env deprecation remains outside scope.


Source-84 `2621e227` derives refused-cleanup loop entries from the original admission and repayment runs; accepted creation cannot enter this loop. Ordered free cursors retain the same ledger lineage, and both post-erase intervals carry the actual pending terminal receipt. Staging and keepalive joins retain their original continuations without incoming cleanup accounts. Nested peer release and universal initialized caller composition remain open. The four-module delta passes 4260 root build jobs and all fifteen standard-or-empty public-declaration queries; all 4213 frozen sources and fifty inherited carry paths match. The aggregate gate, fresh replay and twelve recipes last passed at source-83. Development namespace, implicit-index and dependent-equality elaboration errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged.

Source-85 `36239b83` joins the five fixed nested peer-release stages, final native erasure, pending lifetime/count records and finish points to the canonical creation call and original staging or keepalive invocation. Each point retains the original ledger lineage and literal continuation; the post-erase account records the actual pending receipts. Creation mutation interiors and universal initialized caller composition remain open. The seven-module delta passes 4267 root build jobs, the 1563-declaration gate across thirteen roots, all 54 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4220 frozen proof hashes and fifty landed carry paths match. Development elaboration and focus/frame errors were repaired before validation; no accepted holes or mirror finding remain. Main and mirror are unchanged. No differential result is added; the inherited Env deprecation remains outside scope.

Source-86 `f52dbdb9` joins creation's silent packet marks and queue installation to their original source paths, deriving live phases before access and queued receipts. The combined creation family includes canonical/key-repayment points, mutation cuts, refused cleanup and nested peer release, with source-only continuations and staging/keepalive joins. Universal initialized caller composition and finer atom interiors remain open. Its five new modules pass 4272 root build jobs and all nineteen standard-or-empty public-declaration queries; all 4225 frozen proof hashes and fifty landed carry paths match. Source-85 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and implicit-index errors were repaired; no mirror finding arose. Main and mirror are unchanged.

Source-87 `650a4aff` assembles the canonical staging tree and its reservation, rejected-key repayment, queued-initiation, allocation and creation children with source-only continuations and same-ledger evidence. The initialized receive scheduler derives its staging contract, leaving five explicit deeper packet families: routed transmit, IPv6 receive, encryption, peer transmit and handshake. Expanded keepalive points preserve their actual preparation admission and supply the timer keepalive contract. Finer primitive interiors and universal initialized caller composition remain open. The seven-module delta passes 4279 root build jobs, the 1563-declaration gate across thirteen roots, all 39 standard-or-empty public-declaration queries, fresh root kernel replay (exit 0) and all twelve counterexample recipes (exit 0). All 4232 frozen proof hashes and fifty landed carry paths match. Namespace and source-context elaboration failures were repaired before validation; no accepted holes or mirror finding remain. Main and mirror are unchanged; no differential result is added and the inherited Env deprecation remains outside scope.
