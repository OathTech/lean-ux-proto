# Campaign 3: remaining native-cut coverage for T2

This review reads the immutable parent tree `7e1ea08f` and the five send-drain
modules in `2a8ab1cc`. It examines the charter's throughout-execution conservation
outcome and finding 2 of the [cuts review](2026-10-19-review-campaign-3-t2-cuts.md).
A final source-only follow-up inspected the five initialized send/schedule/encrypt
entry modules added at `f11eadfe`; it did not repeat the whole review against that
newer tree. This is a source/type review, not another build or kernel replay. No
mirror counterexample was found. The outstanding problem remains proof coverage.

[AGENT 2026-10-19] The closure work should use the existing fixed-ticket account
and literal source-prefix witnesses. The finite worklist below separates caller
entry transport from native mutation intervals, because neither alone implies
conservation at every execution point. No narrower T2 claim is proposed.

## Findings

### 1. Matched failure cuts still do not cover all native points

The newer source witnesses address a real part of finding 2. For example,
`WorkerCompletion.selected_failure` in
[ReachedWorkerCompletionWorker](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteReachedWorkerCompletionWorker.lean)
starts from the actual selected worker path; its result fixes the same ledger,
actual callback failure, and a literal worker prefix reaching the saved cut.
`Completion.completeScoped_stopped_cut` in
[ReachedCompletionPrefixes](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteReachedCompletionPrefixes.lean)
also fixes its prelude, processed-list or finishing prefix.

Their types require an actual failure and produce a cut at the failed callback's
entry. They do not quantify over every point inside a successful callback, or
inside that failed callback before its exception. In particular,
`Sending.LoopStop.iteration_prefix` is a first-failing-iteration decomposition,
not an all-iterations result for successful sends. A callback can execute native
writes before a later hidden-input failure. Its entry account alone does not
account for those writes.

This distinction also applies to the new send-drain `failed` theorem: its
exhaustive front/read/delivery/worker/schedule/finish cases are useful enclosing
source evidence; they do not replace the inner callback's own interval proof.
Normal run equations and completed-prefix lemmas already provide much of the
necessary evidence. The missing final quantifier must include both successful
and stopped executions, rather than only selecting one earlier account on Stop.

### 2. Initialized caller coverage is still a proper subset of the source graph

`RunnerSource.operation_prefix`, `DispatchPath`, and `CallbackPath.entry` already
supply initialized operation, dispatch and literal return-callback entries.
`ScheduledRun.Entry` at the reviewed parent pin specifically enters the
post-transmit crypt branch, and `ScheduledRun.Iteration`/`TxEntry` connect that
root to actual scheduler activations and TX work. These are useful concrete
roots, not yet all roots of the same leaf operations.

The follow-up at `f11eadfe` confirms that `SendRun.WorkerEntry` now reaches the
send worker from the original return callback or post-transmit send suffix;
`ScheduledSource.Entry`/`Iteration`/`TxEntry` cover post-transmit and send-drain
scheduler roots; and `EncryptionRun.Iteration`/`Entry` cover direct scheduling
and TX crypt-ahead. Their `.carrier` and `.original` theorems preserve the actual
entry and initialized continuation. This discharges those specific root joins;
it does not add an all-source-points quantifier or the other caller families
below. See [ReachedDrainInitialized](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteReachedDrainInitialized.lean),
[ReachedScheduleCaller](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteReachedScheduleCaller.lean)
and [ReachedEncryptInitialized](../Leanux/Proofs/WG/AuthenticatedEffects/StagedCompleteReachedEncryptInitialized.lean)
at that pin.

The remaining caller families are explicit in
[DriverSource](../Leanux/Proofs/WG/TransmitSecurity/DriverSource.lean):

| Caller family | Actual children needing reached-entry transport |
| --- | --- |
| Return callbacks and observation | `idleTimersObserved`, `afterAdvanceObserved`, and `observeObserved`; use the original numeric position in `ReturnSource.callbacks`, or the observed dispatch arm. The send-drain root is locally available in `2a8ab1cc` and its two initialized entry families are joined at `f11eadfe`. |
| Timer service | Both `timersObserved` and `placeholderTimersObserved` select timers, clear workers, send workers and crypt scheduling. Retain the actual `nextDue` result, saved device, record budget, wheel-step checks, and list/loop position. The placeholder and recorded branches are separate source paths. |
| Inject/flood/batch | `injectObserved` invokes receive and crypt; flood/batch invoke inline poll, transmit and `afterBatchObserved`. `DeliverySource.afterBatchWith` has its own budgeted schedule/send-one loop as well as its hidden-input-absent crypt/send branch. It is not the send-drain loop. |
| Scheduler receive/NAPI | `iterationObserved` has decrypt and handshake-receive arms, while scheduler choice and encryption/decryption tails can enter softirq. `nativePollObserved` can confirm a key, drain staging, call GRO/stack, and repay a peer. The stack reply path re-enters `transmitObserved`. |
| Handshake/send service | `handshakeObserved` can invoke keepalive and nested final peer release; `sendWorkerObserved` invokes `flushedSend`. The latter also occurs directly in lifecycle drains, without a scheduler activation. |
| Configuration/open/removal/dump | `configTailFinish`, `configKey` and `openObserved` invoke staging/keepalive; removal/down/destruction drain send/clear work and release/purge peers. Dump cursor replacement and completion repay the old cursor and can be final releases. |

These families are needed even when the only packets being followed were
originally admitted by an earlier `wgXmit`: a later timer, receive, netlink or
dump operation can move or dispose those obligations. Conversely, direct FS,
ambient, routing and observation bookkeeping need only source-level preservation
of the relevant projection when they cannot change it. For example,
`Env.netnsCleanup` performs namespace/socket/routing maintenance; it is not the
`wgDestruct` reset and should not be treated as an extra packet-disposal arm.

The exact normal/Stop and logical-prefix contracts for these families already
exist in `StagedComplete*` and `StagedCompletePrefix*`. Their carrier preservation
is reusable at actual successful prefixes. Their existential Stop safety is not
itself a reached-entry or every-native-point certificate.

### 3. Receipt boundaries leave a finite set of native mutation intervals

The following is the concrete mutation worklist. Existing local results are
credited only for what their types expose. A single observer around a whole
native function is insufficient to cover that function's interior.

| Native site | Existing support and remaining interval obligation |
| --- | --- |
| `Device.wgXmit`: trim and splice (`Device.lean:410–418`) | `ReachedTransmit` and `RoutedTransmit.Caller.receipt_account` bind the completed front and its post-splice, pre-routed-receipt world to initialization. Add the original trim-loop prefixes: each oldest-packet removal precedes its counter increment, and the single overflow receipt follows the whole trim. Account for the exact removed prefix while that receipt is outstanding. Retain the new input batch at the splice-to-birth-receipt cut. |
| Keepalive insertion (`Send.lean:273–281`) | The native preparation receipt and canonical birth condition already distinguish a new empty-queue keepalive from a pre-existing queue. Add the successful `setPeer`-to-`keepalivePrepared` interval; allocation failure has no birth. |
| Staged take and restore (`Send.lean:223–242`) | `Take.takePrefix`, `CompleteSelected.taken`, `Staging.selection_cases` and `caller_cases` tie selection/borrow to the original caller. The take erases the resident staged queue before its receipt; restore prepends the batch before its receipt. Retain the same selected tickets across those two emission intervals and the original no-key/over-limit continuation. Borrow/guard failures retain the take anchor, not a returned error world. |
| Native TX allocation (`State.newTxSkb`, staged `mapM`) | `Allocation.allocate_intervals` already tracks every partial batch as ordinal aliases of the same selected tickets, then assigns them at the real batch receipt. Reuse this result at every staging caller; do not redo allocation or replace aliases with independently born tickets. |
| Queue admission and head publication (`Send.lean:108–157`) | `queue_installed` and `admission_queue_stopped_cut` connect the queued cut to the actual create prefix. `publication_recorded` exposes the write before `.published`; `publication_mark_native` supplies the local native account. Complete the same relationship for installation before `.queued` and its lifetime markers, the initial uncrypted mark, and every actual create/encryption publication caller. The unpublished local must be consumed at the queue write, not retained as a second owner until emission. |
| Ring poll and encryption writes (`Data.lean:113–155`) | Ring removal changes an alias while the authoritative peer queue still owns the batch. The per-packet byte writes and final head-state publication retain identity/material ownership but change the full cell view. Transport the account through the actual selected poll, intervening NAPI, ordered packet loop, and publication. An endpoint frame of the whole encryption tail does not by itself certify each write. |
| TX peek and dequeue (`Data.lean:222–239`) | `SelectionPath.dequeue_cuts` already supplies original before/after drop prefixes and selected-local ownership. Preserve the actual peek/write and drop-to-marker intervals as well; queue representation changes must use queue-content/ownership facts, not a false equality of full queue structures. |
| Socket result (`Data.sendSkbToPeer`, `Socket.tunnelXmit`) | `Sending.socket_prefix` ties the completed inner socket receipt to the actual account and first terminal. Add the native result-to-receipt interval, keeping success/errno distinct from unsupported-family refusal. At `Socket.lean:196`, the sent-list append is followed by native return and receipt emission; prove that fixed suffix explicitly. Earlier socket-body failures have not produced this result. |
| Native frees (`Data.lean:241`, `Send.lean:174`) | `DeadIntervals` covers ordered completed labelled frees, and `CleanupPrimitive.Awaiting` covers erasure before the labelled receipt. Its `not_old_accounted` theorem correctly demonstrates why the old pending-cell account is invalid there. Reuse the primitive for create-refusal frees too, with their actual caller. Ordinary crypted cleanup has no new terminal: `CleanupPath.split` covers completed frees, but each primitive's native erase must discharge its existing debt/local at the actual cut before the lifetime marker. `DebtsResident` cannot remain unchanged after the erase. |
| Purge, overflow and final peer release | `purgeStagedPackets` writes the count and queue separately. `StagedDisposal.releaseCut` decrements the reference, checks queue emptiness, then atomically erases the peer and charges its staged length, before emitting its release receipt and entering `releaseFinish`. Add the native mutation-to-receipt relation for these actual cuts, including original and nested observers. Reuse it through timers, consumers, RX cleanup, work drains, configuration and dump cursor repayment. |
| Device reset/recreation (`Device.lean:298`, creation failure cleanup) | Existing quiescence and exact peer-account results establish the necessary no-pending facts at successful checks. Tie those facts to the literal destructor check/reset prefix and its later `retireDeviceUnits`, including Stop after reset. Reset contributes no new terminal. Creation starts from the actual absent-device guard; old terminal evidence persists across the new epoch. |

RX allocation and release need a separate ordinary-frame case even when they
create no TX ticket. `Packets.snapshot` in
[Packets/Primitives](../Leanux/Proofs/WG/Packets/Primitives.lean) contains both TX
and RX cells and their shared allocation frontier. `newRxSkb` and `freeRxSkb`
therefore do not preserve the complete `StagedEntry.view` by equality. Reuse
native packet-bound and TX ownership transport at those actual leaves; do not
add an unnecessary RX terminal to the TX ledger or call the whole view unchanged.

The first, third, fifth and ninth rows illustrate why a blanket old-history
`Accounted` claim is unsafe. Depending on the site, the correct intermediate
representation is a selected local, an allocation alias, a consumed cleanup
debt, or an exact pending receipt. A pending receipt may justify the successor
ledger at its native linearization point only when its actual remaining emission
is proved total and leaves the relevant WG projection unchanged. The report
must distinguish that representation from an event already present in history.

### 4. A final source coverage theorem is still needed

`CompleteConsequences.Cut.partition` is strong once supplied the right cut:
it gives each canonical birth one status, meaningful pending ownership, and
terminal evidence. The companion converse and uniqueness results are reusable.
What remains is to supply such evidence, or the explicit interval variant, at
**each actual source point**. Neither `Safe.cuts` nor generic `Reached.At` does
that. The latter deliberately accepts a supplied monadic decomposition and does
not certify that decomposition is an original source site.

A source-specific point relation should therefore be indexed by the original
invocation and its input state/history. Its constructors should name only the
fixed sites above and actual ordered loop prefixes. It should retain the same
ledger, debts, selected/unpublished locals or pending receipt, plus the original
continuation. Derive coverage from the literal source cases; do not make
coverage an incoming premise of the initialized headline. Existing successful
prefix preservation supplies ordinary leaves, while explicit interval carriers
handle projection-changing sites. The claim is over the mirror's WG projection,
not every implementation detail of the monad or C memory semantics.

### 5. Composition can give this work a sound finite end

A one-caller-at-a-time collection has a finite number of static roots, but that
alone is not a coverage proof. Each root must expose every relevant native
mutation and callback, including successful interiors. A compositional
source-cut contract is the better end condition: it permits the same checked
callback to be used by receive, timers, configuration and the scheduler without
proving its internals again.

The contract should have two parts, kept distinct:

- **Fixed source points and reachability.** For a named source function, define
  its points from its actual body: a named primitive before/after cut, a left
  bind point, a right bind point preceded by the actual successful left run,
  an actual selected branch, or an indexed original loop prefix. A right point
  retains the left result and exact intermediate world/history. A loop point
  retains the original list/range, completed prefix, current accumulator and
  remaining continuation. Neither requires the enclosing invocation to fail.
- **Account preservation at every such point.** From the incoming account,
  every reached point has the same fixed-ticket account or an explicit selected,
  partial-allocation or pending-receipt variant. The normal endpoint additionally
  supplies the account needed by the next bind. An exception supplies no
  synthetic post-world; points before it remain valid and its failing primitive
  needs its own source contract if it mutates before throwing.

In schematic types, for a *fixed named source family* `F`, the main obligation is
`Carrier h w -> PointF args w h site u middle -> Evidence site middle u`.
Its companion is a source-derived coverage decomposition for every normal or
stopped execution of `F args`: each child invocation and each projected mutation
has one of these constructors. `PointF` must not accept arbitrary actions `p`
and `k` with a supplied equation `F args = p >>= k`. A checked decomposition of
the literal definition can establish a constructor; the equation alone does not
make an arbitrary factor an original point. No general `Step -> Complete`
principle is introduced.

A small first implementation should use the already factored send drain:

1. Define `DrainPoint w h site u middle` over the *fixed* `SendDrain.front`,
   `step`, `finish` and original range. Front points retain the successive
   `getWG`, no-crypt-work check, queued-reset and budget runs. Loop points retain
   `indices budget = done ++ index :: rest` and the actual successful prefix
   with its accumulator; the completed-loop/finish point also permits no
   remaining index. The no-device branch is a distinct normal endpoint.
2. Use existing `WorkerPath` and `SchedulePath` for the send-worker and scheduler
   entries. Add the delivery child under the actual empty-queue read, and the
   three child-interior constructors using their supplied *fixed-source*
   contracts. Child successful endpoints feed the next step just as failed
   paths feed the existing error classification.
3. Prove the schematic obligation above from concrete `Carrier` plus the three
   child cut contracts, with native quiet-frame proofs for the front/read/reset
   and budget leaves. Prove source coverage by `source_factor`, `body_list`,
   literal list-prefix decomposition and `ForInStep.done/yield`; then every
   actual successful or failing iteration is covered. This first theorem is
   honestly conditional on the three child contracts, not an initialized T2
   result. It should require no new ledger and no duplicate send-drain driver.

The next reusable instance is `SourceScheduler.{schedule,dispatch,run}`. Its
shared boundaries are occupancy/work checks, record budget and hidden choices,
TX work-list removal, section markers, suspension bookkeeping, committed
iteration and NAPI calls. Its copied-world consistency trials must remain
separate: they are not committed activations and cannot generate disposal or
transmission obligations. The current scheduler source already makes this
distinction explicitly. The iteration contract then has four concrete worker
cases, with nested softirq, crypt-ahead and publication calls exposed as children.

After these two examples, the remaining shared boundaries are the mutation
worklist above plus staging/front/keepalive; receive/admission/poll/stack;
handshake/send/clear; timer/placeholder/delivery loops; configuration/removal/
dump/reset; and the literal dispatch/return-callback/Runner list. Each is a
finite source definition with list or budget induction, not an enumeration of
all possible traces. Mutual caller nesting must follow the existing terminating
source definitions; no circular assumption that all callbacks already satisfy
T2 is sound. Native projection-preserving leaf contracts can be shared across
these families. The final closed dispatch/Runner instance, with no incoming
child contracts, is the completeness argument. Existing manual paths are useful
reachability lemmas for that construction, not a substitute for it.

## Finite closure plan

1. **Fix the common cut interface and quantifier.** Combine accounted,
   selected, partial-allocation and pending-receipt cases in a source-indexed
   evidence type. Add completed-prefix splits for successful send/cleanup paths
   beside the existing failed-source classifications. The exit condition is a
   statement about any declared actual point of a normal or stopped invocation.
2. **Close the mutation worklist once.** Prioritize trim/purge/release,
   take/restore/keepalive, installation and ordinary cleanup. They recur across
   many callers. Reuse the completed allocation and labelled-free primitives.
   Supply a source-local projection-frame argument for remaining silent leaves;
   no new mirror events are required.
3. **Complete the TX cluster.** Join allocation → actual create admission →
   accepted queue/publication or refusal cleanup; join poll/encrypt → publication;
   join selected TX → send/debt cleanup/repayment. Keep the original same-ticket
   successor rather than selecting unrelated existential ledger witnesses.
4. **Close receive and timer caller clusters.** Transport actual NAPI/poll,
   confirmation, stack reply, handshake and timer/placeholder entries into those
   shared primitives. Include the explicit `afterBatchWith` schedule/send loop.
5. **Close administrative/lifecycle callers.** Reuse the same release/purge and
   staging intervals in configuration, open, down/removal, clear/send drains and
   dump cursor calls. Connect existing initialized quiescence to the actual
   device-reset cut; no disposal may be inferred from reset itself.
6. **Join initialization and extract T2.** Reuse `operation_prefix`,
   `DispatchPath` and numeric `CallbackPath`; extend the source-root cases above
   and compose `2a8ab1cc` send-drain paths. Prove every resulting point carries
   the same account/interval evidence, then apply the fixed-ticket partition,
   terminal converse and uniqueness. Retain the separate invocation-refusal
   charge result and the existing socket authorization theorem. No fairness or
   eventual-drain assumption is needed.

This plan is finite because the ownership-changing native sites and the static
caller families are finite; packet counts, operation counts and record budgets
are handled by their original list/range inductions. It does not require another
independent Runner or a new audit gate. Finding 2 should remain open until the
source coverage quantifier and all these caller/interval cases are discharged.

## Review limits and validation

The review inspected declaration types and native/source bodies at `7e1ea08f`
and `2a8ab1cc`, then checked the five initialized entry modules noted above at
`f11eadfe`. Existing proof checks were not rerun, and no mirror or Lean source
was changed. Local documentation links were checked against those immutable
trees. No new substantive executable
behavior defect was identified; the findings concern the scope of the current
certificates and the remaining source joins.

## Disposition

[AGENT 2026-10-19] All four coverage findings are accepted as refinements
of the open native-cut obligation; no narrower outcome is adopted.

1. Successful interiors will be covered by fixed source-point families,
   alongside the existing concrete failure decompositions. A selected stop
   witness will not be reported as universal coverage.
2. The initialized entries at `f11eadfe` remain credited at their stated
   scope. The other caller families stay open until structurally composed.
3. The mutation table is the finite interval worklist. The ongoing front and
   encryption lanes cover their own entries; pending receipts and consumed
   debts remain explicit where an old resident account is false.
4. The final headline will require a closed source coverage instance. The
   conditional send-drain prototype in section 5 is implemented at source-70
   `14a5f051`, with exact normal/stopped decomposition and its three child
   source obligations visible. Its initialized composition and aggregate
   checks pass; it is not itself T2 completion.

Source-71 `8526e3e4` implements the next scheduler source instance with a
Type-valued canonical witness and source-constructed remainders. Its committed
iteration and NAPI contracts remain explicit. Ordinary cleanup, encryption
packet/publication and peer-release native cuts now have initialized source
connections; the counted erasure intervals retain the original ticket cohort.
The aggregate gate, fresh replay and twelve recipes pass. These are progress
on findings 2–4, not their closure: all remaining caller families and concrete
child contracts still require the closed final instance.

Source-72 `e1156284` connects routed take, worker socket-result and publication
release-finish native intervals to initialized callers. Pending queue and
socket receipts retain their original cohort and ledger, and the native
release-finish guard and two writes retain the original remainder. Local
take, restore and keepalive cases include normal and stopped paths. The gate,
fresh replay and twelve recipes pass. Other callers, concrete child instances
and stopped socket-front interiors remain open; findings 2–4 remain open.

Source-73 `33251831` supplies the canonical worker iteration source and its
initialized scheduler adapter. The iteration leaf is now structural; poll,
softirq, IRQ exit, encryption, transmit, prepare, release and handshake
interiors remain explicit children, alongside external NAPI. Native queue
cases and initialized dequeue preserve the actual cached cohort, selected
local, ledger and continuation through the silent setter and existing
write/removal observations. Aggregate gate, fresh replay and twelve recipes
pass. These additions do not close findings 2–4 or the remaining caller graph.

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

Source-88 `08d0e804` supplies fixed encryption callback points from the actual head read, ordered packet loop and publication prefix. Same-ledger accounting includes native peer release and the return before its original receipt. The initialized receive scheduler now retains four deeper contracts: routed transmit, IPv6 receive, peer transmit and handshake. Crypto primitive interiors and universal initialized native-cut composition remain open. The five-module delta passes 4284 root build jobs and 31 standard-or-empty public-declaration queries; all 4237 frozen hashes and fifty landed carry paths match. Source-87 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Development namespace and syntax errors were repaired; no mirror finding arose.

Source-89 `210bf296` derives the zero-key timer repayment from its executed borrowing prefix. Fixed raw release points preserve the same ledger and history, and that invocation cannot enter final peer erasure. Canonical timer coverage now supplies raw repayment, observed peer release and expanded keepalive children, retaining exact continuations. Initialized caller joins, finer primitive interiors and universal T2 coverage remain open. Validation passes 4289 root build jobs and nineteen standard-or-empty public-declaration queries; all 4242 frozen hashes and fifty landed carry paths match. The latest aggregate gate, fresh replay and twelve-recipe checkpoint remains source-87. Development namespace and proof elaboration errors were repaired; no mirror finding arose.

Source-90 `47030f62` connects the fixed native preparation tree and key-read/scatter prefixes to the original encryption callback and initialized scheduler. Each cut retains the same packet ledger, while resumed execution preserves the original preparation and key-read snapshots in its eventual receipt. The four deeper packet contracts, other primitive intervals and universal initialized caller composition remain open. Aggregate validation passes 4294 root build jobs, the 1563-declaration gate across thirteen roots, 56 standard-or-empty public-declaration queries, fresh root kernel replay (retrieved exit 0) and all twelve recipes (retrieved exit 0). All 4247 frozen proof hashes and fifty landed carry paths match. Development elaboration, namespace and normalization errors were repaired before validation; no mirror finding arose. Main and mirror are unchanged; no differential result is added and the inherited Env deprecation remains outside scope.

Source-91 `4087b2ab` joins the expanded receive scheduler, work services, send drain and concrete timers through all seven service families and the initialized runner. The runner send and post-transmit callbacks now derive their contracts from that graph, retaining the actual mixed-work refusal and pending-work completion checks. Four packet families, the flushed protocol sender, twelve dispatch bodies and remaining primitive intervals stay open. Validation passes 4299 root build jobs and 24 standard-or-empty public-declaration queries; all 4252 frozen hashes and fifty landed carry paths match. Source-90 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source elaboration errors were repaired; no mirror finding arose.

Source-92 `f676d7a0` supplies IPv6 receive from its fixed source: predicate checks, explicit refusals, WG read and inbox write. A structural proof excludes every child callback, and its packet-account frame and original remainder replace the IPv6 premise in the initialized runner. Three packet families, the flushed protocol sender, twelve dispatch bodies and finer native intervals remain open. Validation passes 4303 root build jobs and 21 standard-or-empty public-declaration axiom queries; all 4256 frozen proof hashes and fifty landed carry paths match. Source-90 remains the latest aggregate gate, fresh replay and twelve-recipe checkpoint. Source elaboration failures were repaired before validation; no mirror finding arose. Main and mirror are unchanged.
