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
