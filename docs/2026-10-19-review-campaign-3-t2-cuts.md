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

No mirror change or narrower T2 outcome is adopted.
