# WireGuard proof campaign

## Progress

The six-result campaign is complete over main `b3f56807`, executable-identical
to the state-split landing `b700659`. R1, R4, R5 and R6 retain their explicit
counterexamples to the false original wording; the positive claims and named
W7 characterization are validated within their documented scope. R2 and R3
have initialized runner closure. The mirror is unchanged, and the branch keeps
the nondefault `LeanuxProofs` target and `scripts/proof-gate`.

The final [W7 report](2026-10-17-r4-full-ring.md) connects the two actual
refusals to their later releases in the accepted finite episode. It distinguishes
compiled concrete replay evidence from kernel-proved source and geometry
contracts, and conservation from eventual delivery. Current totals are
916 Lean files, 12,302 named theorems and 860 terminal declarations. The gate
passes 973 jobs/all 860 declarations; the original-run W7 reproduction passes.
Fresh root kernel replay passes in 112.641 seconds without warnings. The
report records each review disposition.

The completed retrofit itself changed 7,715 to 6,564 named theorems:
3,197 retyped/generalized, 1,709 deleted, 2,809 retained and 558 added.
Later R3/R4 extensions add statements on the split types. Current status is in
[the register](proofs.md#results); the following checkpoint entries preserve
what was established at each stage, including then-open obligations.

### Earlier checkpoints

Work on `proofs/campaign` in `.worktrees/proofs-campaign` follows
[the charter](2026-10-13-charter-proof-campaign.md). The branch contains main
`b700659` plus documentation-only `b3f56807` and preserves its own proof tree,
nondefault lake target and gate. The executable mirror is unchanged.

The state-split retrofit is complete. Its validated checkpoint census is
471 → 452 Lean files and 7,715 → 6,564 named theorems: 3,197 retyped/generalized,
1,709 deleted, 2,809 retained and 558 added. Independent reconciliation includes
the unchanged pure/product contracts and corrects seven duplicated retained
Enqueue entries. There are 517 terminal declarations, including two definitions.

All seven register rows are current over `b3f56807`, executable-identical to
`b700659`. The complete proof gate passes all 510 build jobs and 517 terminal
declarations, with only the permitted axioms, in 361.55 seconds. Fresh root kernel
replay passes in 100.62 seconds after compilation. The sole build warning is the
existing mirror-side String.mk deprecation; proof warnings are cleared.
Scoped source/axiom checks and independent reviews cover the repairs.
The [retrofit report](2026-10-16-proof-state-split.md) records the exact census,
source/type deletion grounds, failed checks and validation. Its
[findings](2026-10-16-proof-state-split-findings.md) include the withdrawn
unrestricted cleanup-totality claims and checked local counterexamples.
Five failed aggregate gates remain reported as failures; each preceded source
repairs, and none was accepted as a pass. R3/R4 work resumes on the new types.

The first post-retrofit R3 extension adds 58 theorems in eight new modules
and three terminal exports. The tree now has 460 files/6,622 theorems and 520
terminal declarations; all 141 earlier R3 terminal bodies are unchanged.
The complete gate passes 518 jobs/520 declarations in 5.52 seconds, and fresh
root replay passes in 98.01 seconds without warnings. The
[current-identity report](2026-10-17-r3-current-identity.md) records fixture
initialization, native maintenance, nullable compatibility and the same-witness
resident identity certificate at successful publication. Whole-run identity
closure, packet transport and the reached routing/Stack join remain open.

A second current-identity checkpoint adds four modules and 19 theorems:
464 files/6,641 theorems, with 524 terminal declarations and 148 R3 exports.
Session installation and the unchanged observer retain one configured/current
witness; actual prepare carries it to the fresh successful publication receipt.
Native peer retirement permits deletion and retains surviving identity fields;
the fixture and key clearing also preserve nullable affiliation. All 144 prior
R3 terminal bodies are unchanged. Gate: 522 jobs/524 declarations, 2.55 seconds.
Fresh kernel replay: 99.01 seconds, no warnings. Whole-run R3 closure remains open.

The reached-routing checkpoint adds five modules and 73 theorems: 469 files,
6,714 theorems, 528 terminal declarations and 152 R3 exports. Native index
acquisition, bounded peer creation and handshake sending retain current identity.
Actual Stack entries are linked to their earlier consumed receipts and the
supplied flat source winner in the same new poll suffix, even on a later Stop.
Gate: 527 jobs/528 declarations in 2.50 seconds. Fresh replay: 99.55 seconds,
no warnings. The [short report](2026-10-17-r3-reached-routing.md) records the
remaining initialized identity and positional configuration-history joins.

The current-journal checkpoint adds seven modules and 74 theorems:
476 files/6,788 theorems, 533 terminal declarations and 157 R3 exports.
Native receive and lifecycle calls preserve configured/current identity, and
the actual session journal transports it through the original focuses.
Joint primitives retain both existing observation streams from one execution.
Gate: 534 jobs/533 declarations in 7.43 seconds; EOF normalization also passes
the gate with unchanged replayed objects. Fresh replay passes in 102.68 seconds.
The [short report](2026-10-17-r3-current-journal.md) records review findings,
validation and the remaining initialized joins.

The receive-cuts checkpoint adds ten modules and 153 theorems:
486 files/6,941 theorems, 542 terminal declarations and 166 R3 exports.
Native receive/traffic and existing receive journals preserve current identity;
positional checks retain actual decrypt/probe support on Stop prefixes.
The anchored publication certificate reaches the actual consume receipt under
explicit earlier transport, and the joint allowed-IP loop retains both original
observer projections. The real poll retains arbitrary product callback contracts.
Gate: 544 jobs/542 terminal declarations in 41.80 seconds.
Fresh kernel replay passes in 104.09 seconds without warnings.
The [short report](2026-10-17-r3-receive-cuts.md) records the unchanged earlier
statements, independent reviews and remaining initialized joins.

The configuration-cuts checkpoint adds twelve modules and 181 theorems:
498 files/7,122 theorems, 554 terminal declarations and 178 R3 exports.
Actual stack/poll and prepare/NAPI/crypt workers preserve current checks.
Receiving-owner bounds propagate through creation/session/index cuts and local
journals; normal consume recovers entry residency from conditional identity
transport. Complete tail/removal/update observers discharge lower callback
obligations while retaining both original streams. All prior statements remain
unchanged. Gate: 556 jobs/554 declarations; fresh replay passes in 100.86
seconds without warnings.
The [short report](2026-10-17-r3-configuration-cuts.md) records the sole
infrastructure retry, rejected development checks and remaining initialized joins.

The caller-cuts checkpoint adds thirteen modules and 251 theorems:
511 files/7,373 theorems, 566 terminal declarations and 190 R3 exports.
Actual scheduler/deferred journals preserve current checks; receive and decrypt
carry the joint current/R2/owner invariant. Whole device configuration and wgSet
syscall project exactly to both original streams, including errors and waits.
All prior statements remain unchanged. Gate: 569 jobs/566 declarations in
6.416 seconds; fresh replay passes in 108.149 seconds without warnings.
The [short report](2026-10-17-r3-caller-cuts.md) records failed development
checks, the reviewed reuse repair and the remaining initialized joins.

The lifecycle-cuts checkpoint adds thirty-two modules and 331 theorems:
543 files/7,704 theorems, 580 terminal declarations and 204 R3 exports.
All syscalls and one initialized typed runner retain both original journals
and exact JSON/indexed errors. Concrete poll/stack, crypt and transmit workers,
peer/device configuration and lifecycle carry receiving-owner bounds.
All earlier terminal bodies remain unchanged. Gate: 601 jobs/580 declarations
in 6.981 seconds; fresh kernel replay passes in 106.362 seconds without warnings.
The [short report](2026-10-17-r3-lifecycle-cuts.md) records source failures,
reviewed reuse repairs and the remaining initialized joins.

The scheduler-cuts checkpoint adds ten modules and 138 theorems:
553 files/7,842 theorems, 587 terminal declarations and 211 R3 exports.
Actual handshake receive, scheduling and all deferred calls retain joint
owner checks. Prepare establishes selected publication anchors and transports
older ones; normal consume links its exact receipt under the supplied caller
invariant. Earlier terminal bodies remain unchanged. Gate: 611 jobs/587
declarations in 6.631 seconds. Fresh kernel replay passes in
107.325 seconds without warnings.
The [short report](2026-10-17-r3-scheduler-cuts.md) records the conditional
saved-scan architecture, failed checks, review repair and remaining closure.

The initialized-owner checkpoint adds thirteen modules and 171 theorems:
566 files/8,013 theorems, 597 terminal declarations and 221 R3 exports.
Every concrete syscall and the initialized runner derive captured current/owner
checks for all typed traces and both flags, including Stop. Packet publication
now carries a peer-frontier bound; concrete creation/reset/free, completion,
poll and Stack have their stated packet-retention contracts. Gate: 624
jobs/597 declarations in 6.651 seconds. Fresh kernel replay passes in 103.207 seconds without warnings.
The [short report](2026-10-17-r3-initialized-owner.md) records the unchanged
older terminal bodies, failed source checks and remaining packet/routing joins.

The consume-entry checkpoint adds twenty-one modules and 245 theorems:
587 files/8,258 theorems, 611 terminal declarations and 235 R3 exports.
The initialized joint journal combines owner, linkage and routing-completion
checks. Local poll proves contemporaneous consume-entry routing and positional
publication certificates. Native ingress/session/handshake/removal and observed
prepare/NAPI/crypt/receive iterations preserve packet histories. All 221 older
R3 terminal bodies remain unchanged. Gate: 645 jobs/611 declarations in
7.102 seconds; fresh kernel replay passes in 105.212 seconds without warnings.
The [short report](2026-10-17-r3-consume-entries.md) records
validation, independent review and the remaining initialized caller joins.

The publication-closure checkpoint adds twenty-five modules and 339 theorems:
612 files/8,597 theorems, 631 terminal declarations and 255 R3 exports.
The actual initialized runner now derives joint owner/publication checks for
all typed traces and both flags, including stopped prefixes. Each consumed
occurrence has its strict earlier publication certificate. Specified Stack
entries join actual buffer, consume and decrypt positions; initialized
positional routing and transmit handoff authorization remain open. All 235
older R3 terminal bodies remain unchanged. Gate: 670 jobs/631 declarations in
7.012 seconds. Fresh kernel replay passes in 104.127 seconds without warnings.
The [short report](2026-10-17-r3-publication-closure.md) records failed development
checks, independent review and the remaining authorization joins.

The initialized incoming checkpoint adds five modules and 38 theorems:
617 files/8,635 theorems, 639 terminal declarations and 263 R3 exports.
The actual initialized runner supplies routing at every consumed occurrence;
public parsing supplies address shape. Each selected Stack entry now has its
actual earlier configured publication and source winner at consumption, even
before a later Stop. Local transmit authorization covers a completed staged
splice with a subsequently stopped tail. Initialized transmit authorization
remains open. All 255 older R3 terminal bodies remain unchanged.
The proof gate passes 675 build jobs and 639 terminal declarations in 7.319 seconds. Fresh kernel replay passes in 102.759 seconds without warnings.
The [short report](2026-10-17-r3-initialized-authorization.md) records scope,
failed development checks and independent review.

The transmit-source checkpoint adds fourteen modules and 115 theorems:
631 files/8,750 theorems, 653 terminal declarations and 277 R3 exports.
The concrete native observer records actual completed staging handoffs and
retains them through later Stops, with exact old-journal projection. Positional
routing checks authorize each selected receipt at its own strict prefix.
Actual direct/batch/Stack/GRO/poll source factors and concrete Stack transport
are proved; initialized transmit caller closure remains open. All preceding
263 R3 terminal bodies are unchanged. Gate689/653 passes; Fresh kernel replay passes in 105.441 seconds without warnings.
The [short report](2026-10-17-r3-transmit-source.md) records the corrected
routing premise, scoped failures, independent reviews and remaining joins.

The [initialized outgoing closure](2026-10-17-r3-initialized-transmit.md)
adds 31 modules and 409 theorems: 662 files/9,159 theorems, 665 terminal
declarations and 289 R3 exports. All 277 preceding R3 terminal bodies remain
unchanged. Every actual committed transmit caller now reaches the native
handoff observer, with strict-prefix routing and exact old RX/executable
projection through the initialized runner. Parsed traces discharge address
shape; both flags and indexed-Stop prefixes are included. Together with the
trie and incoming results, this completes R3. Gate720/665 passes in 7.759s;
fresh kernel replay passes in 105.8 seconds with no warnings. R4 conservation remains open.

The [R4 stable-boundary extension](2026-10-17-r4-stable-boundaries.md) adds 172
theorems, retaining every prior statement: 674 proof files/9,331 theorems,
143 R4 terminals and 677 terminal declarations overall. Its gate732/677 and
fresh root replay pass (4.483s/104.224s). Whole initialized conservation remains
open; the local closure now includes fixture/drain boundaries, native decrypt
preparation, clear-work reservations and completion/Stack stable transport.

The [R4 poll/work extension](2026-10-17-r4-poll-work-conservation.md) adds 208
theorems in sixteen modules and thirteen exports: 690 files/9,539 theorems,
156 R4 terminals and 690 terminal declarations overall. Every prior theorem
remains unchanged. Concrete poll/NAPI/IRQ/decrypt boundaries and queued-work
payments pass gate748/690 and fresh root replay (4.736s/105.281s). Complete
source-owned funding and initialized conservation remain open.

The [reference-account checkpoint](2026-10-17-r4-reference-accounts.md) adds
thirteen modules and 156 theorems: 703 files/9,695 theorems, 169 R4 terminals
and 703 total declarations. All prior bodies remain unchanged. Source-owned
base/work/TX/cursor accounts retain actual callback acquisitions and payments.
Gate: 761 jobs/703 declarations in 5.238 seconds; fresh root replay passes in
109.546 seconds without warnings. Full initialized conservation remains open.

The [complete-holder flow checkpoint](2026-10-17-r4-holder-flow.md) adds
seventeen modules and 216 theorems: 720 files/9,911 theorems, 182 R4 terminals
and 716 total declarations. All prior bodies remain unchanged. Admission,
whole poll/NAPI/decrypt, work dispatch/drains, dump serialization/socket calls
and encrypted TX completion retain the complete supplied account. Initialized
conservation remains open. Gate: 778 jobs/716 declarations in 4.955 seconds,
after an export-name repair; fresh root replay passes in 106.857 seconds.

The [lifecycle/worker checkpoint](2026-10-17-r4-lifecycle-workers.md) adds
fifteen modules and 158 theorems: 735 files/10,069 theorems, 194 R4 terminals
and 728 total declarations. All previous bodies remain unchanged. Actual
creation/retirement, full TX selection/publication/encryption, dump callers,
session setup and two timers retain the supplied complete account. Initialized
conservation remains open. Gate: 793 jobs/728 declarations in 5.190 seconds;
fresh root replay passes in 110.672 seconds without warnings.

The [scheduler/lifecycle checkpoint](2026-10-17-r4-scheduler-lifecycle.md)
adds twelve modules and 221 theorems: 747 files/10,290 theorems, 206 R4 terminals
and 740 total declarations. All previous bodies remain unchanged. Handshake
acquisition, all timers, nonreceive scheduling, base/caller payments and
allowed-IP edits retain their supplied accounts. Full scheduler/deferred
contracts expose the remaining receive premise. Initialized conservation
remains open. The corrected gate passes 805 jobs/740 declarations in 5.309
seconds after one namespace-qualification failure. Fresh root kernel replay passes in 108.189 seconds without warnings.

The [auxiliary/configuration checkpoint](2026-10-17-r4-auxiliary-configuration.md)
adds eleven modules and 146 theorems: 758 files/10,436 theorems, 215 R4 terminals
and 749 total declarations. All previous bodies remain unchanged. Acquired-peer
configuration pays actual caller/base references; removal and updates retain
structural coherence. Same-run session accounting joins the auxiliary domain;
handshake/Stack/poll/NAPI/crypt retain slot compatibility. Full receive, stronger
scheduler and initialized conservation remain open. Gate: 816 jobs/749
declarations in 5.421 seconds. Fresh root replay passes in 107.381 seconds.

The [source-composition checkpoint](2026-10-17-r4-source-composition.md)
adds fifteen modules and 146 theorems: 773 files/10,582 theorems, 228 R4 terminals
and 762 total declarations. All previous theorem bodies remain unchanged.
The complete native handshake receiver, peer command and device creation
preserve supplied accounts; actual admission outcomes and fresh receipt
observations support finite admission/poll composition. Observed receive-worker,
whole device configuration and initialized conservation remain open. Gate:
831 jobs/762 declarations in 21.831 seconds. Fresh root replay passes in 113.136 seconds without warnings.

The [worker-closure checkpoint](2026-10-17-r4-worker-closure.md)
adds ten modules and 120 theorems: 783 files/10,702 theorems, 236 R4 terminals
and 770 total declarations. All previous theorem bodies remain unchanged.
The original observed receive worker closes the complete auxiliary scheduler's
receive premise. Configured identity enables repeated peer commands; shutdown
retains funding and physical geometry. Both fixture flags establish local
entry facts. Whole device configuration/deletion, dynamic ingress and initialized
conservation remain open. Gate: 841 jobs/770 declarations in 5.755 seconds.
Fresh root replay passes in 112.958 seconds without warnings.

The [ingress-boundary checkpoint](2026-10-17-r4-ingress-boundary.md)
adds twelve modules and 165 theorems: 795 files/10,867 theorems, 247 R4 terminals
and 781 total declarations. Whole native device configuration and guarded
environment deletion retain their supplied accounts. Original receive/NET_RX
execution selects a unique dynamic ledger and combined scheduler entry; actual
crypt/send/afterXmit waits retain it. Completion emptiness follows from the real
decrypt-ring flag. Complete traffic callers and initialized conservation remain
open. All previous bodies are unchanged. Final gate: 853 jobs/781 declarations,
6.072 seconds; fresh replay: 112.728 seconds, no warnings. One reviewed comment
was corrected before final validation.

The [traffic-boundary checkpoint](2026-10-17-r4-traffic-boundary.md)
adds fifteen modules and 207 theorems: 810 files/11,074 theorems, 259 R4 terminals
and 793 total declarations. Whole inject derives its admission ledger and empty
completion; whole flood derives a unique remaining ledger through every actual
occurrence. Native lifecycle/configuration, transmit, all deferred calls and
batch waits retain their complete local entries. Recorded completion derives
empty RX storage; placeholder completion is not asserted. Full batch, global
lifecycle composition and initialized conservation remain open. Previous bodies
are unchanged. Gate: 868 jobs/793 declarations, 6.066 seconds; fresh replay:
115.435 seconds, no warnings. One reviewed Stop comment was corrected.

The [outer-boundary checkpoint](2026-10-17-r4-outer-boundary.md)
adds fifteen modules and 234 theorems: 825 files/11,308 theorems, 275 R4 terminals
and 809 total declarations. Full batch now selects a unique remaining ledger;
whole traffic calls supply the next outer entry. Fixture, lifecycle/configuration,
controls, dump/transmit dispatch and return-to-user waits retain those entries,
including absent devices. A local placeholder completion counterexample makes
no initialized or kernel claim. Initialized admission-to-disposition conservation
remains open. All prior bodies are unchanged. The first aggregate gate failed
on implicit binder collisions; explicit binders repair them. Final gate:
883 jobs/809 declarations in 6.089 seconds. Fresh root replay passes in 112.708 seconds without warnings.

The [initialized-account checkpoint](2026-10-17-r4-initial-account.md)
adds thirteen modules and 132 theorems: 838 files/11,440 theorems, 289 R4 terminals
and 823 total declarations. Every original syscall and the accepted initialized
runner derives its actual source-selected funded residual ledger. Exact erasure
retains JSON/Stops and the original RX journal. Traffic paths locate accepted
positions and local pending-or-removal fates. Peer-queue ENOSPC cleanup and
ring-full EPIPE are now correctly named. Earlier theorem bodies are unchanged.
Gate: 896 jobs/823 declarations, 8.223 seconds. Fresh replay: PASS in 113.801 seconds without warnings.
Initialized admission-to-named-disposition conservation remains open.

The [disposition checkpoint](2026-10-17-r4-dispositions.md) adds 22 modules and
287 theorems: 860 files/11,727 theorems, 300 R4 terminals and 834 total declarations.
Original syscall selections now have named poll fates or one pending identity;
initialized runner removals derive actual same-poll releases and final absence.
Staged allocation and selected encryption advance W7 mark transport. Complete
initialized admission selection and live-item/caller alignment remain open.
Earlier bodies are unchanged. Gate: 918 jobs/834 declarations in 6.622 seconds;
fresh replay PASS in 116.213 seconds with no warnings. The report records failed development checks,
the repaired history-prefix omission and the temporary log-number collision.

The [initialized ingress checkpoint](2026-10-17-r4-ingress-coverage.md) adds
33 modules and 305 theorems: 893 files, 12,032 named theorems, 312 R4 terminals
and 846 total terminal declarations. Every accepted original runner now supplies
actual initialization/operation/source cuts and complete normal ingress coverage,
with a pending or actual completed-poll fate for every accepted admission.
The full adjacent encrypt iteration preserves a fresh full-ring refusal's DEAD
head. Initialized W7 caller transport remains open. No old theorem is retyped,
deleted or changed. The gate passes 951 jobs/all 846 declarations in 6.952 seconds
after one export-name failure and source repair; fresh root replay passes in
113.512 seconds with no warnings.

The [initialized live-ring checkpoint](2026-10-17-r4-live-frontier.md) adds
17 modules and 217 theorems: 910 files, 12,249 named theorems, 315 R4 terminals
and 849 total terminal declarations. Concrete scheduling, traffic, lifecycle,
configuration and every syscall preserve the logical live encryption-ring
bound and physical refinement. Original initialization derives it at every
actual operation entry and the normal endpoint. Earlier theorem bodies remain
unchanged; independent reviews cover the generic and concrete runner joins.
The gate passes 968 jobs/all 849 declarations in 7.832 seconds; fresh replay
passes in 114.850 seconds with no warnings. The same-item W7 refusal-to-disposal
chain remains open.


The pre-split checkpoint validated every baseline result surface over
`cb2348e`. R3 packet authorization is now closed over the current split tree;
R4 normal ingress conservation and the named finite W7 characterization are
closed. Stopped-endpoint funding and universal eventual TX disposal are
stronger properties outside these claims. Earlier positive results and runtime findings retain
their scope below; the [register](proofs.md#results) gives the authoritative
pins and status. No main integration, push, differential check or guest run
was made by this campaign.

| Result | Disposition |
| --- | --- |
| R1 | Replay uniqueness proved; inclusive-floor correction witnessed. |
| R2 | Initialized allocation-identity access safety proved, including failures/trials; affiliation/credits separate. |
| R3 | Trie history refinement and initialized incoming/outgoing cryptokey routing proved for shaped typed traces, including parsed traces and stopped prefixes. |
| R4 | Initialized duplicate freedom and normal ingress conservation proved; named finite W7 two-refusal/two-disposal episode characterized; chronological GRO order refuted. No eventual-delivery or universal outgoing-disposal claim. |
| R5 | Accepted age/post-zero/wire-nonce counterexamples; thirteen positive local contracts. |
| R6 | Cookie exclusion proved; literal MAX=18 refuted, without a replacement universal bound. |

**Pre-split R3 configured-identity extension (validated over `cb2348e`).** Three groups add
actual peer creation/lookup/retirement/make-dead/fresh owner-acquisition contracts, one-witness configured
session support, and successful RX publication identity. All518 prior terminal bodies remain unchanged;
521 declarations (519 theorems/two definitions;141 R3/129 R4). Supplied table coherence bounds
raw slots, permits dangling rows/dead residents, and never bounds process-global stamps by slot frontiers.
A normal whole session, including its actual live/self tail, supplies the configured derivation-front Context;
a Some front alone may precede a Stop. Actual normal prepare identifies the captured ring item/write,
fresh decrypt receipt position, full packet/key/AEAD transformation and state-only publication before IRQ.
DEAD publication does not assert successful decryption. Configured support and RX compatibility remain
supplied premises; initialized configured identity, current peer-allocation transport and the routing/Stack
join remain open. The old original erasures, same-input AllocationInv R2 projections and initialized domains
are unchanged. No cryptographic authentication or accepted counterexample is claimed.

**Pre-split effort and review.** The 42 worker calls comprise 40 builds (six clean PASS, 34 ordinary FAIL)
and two passing exact checks. Scoped/full builds pass 474/523 jobs. Coordinated validation passes the
523-job/521-declaration proof gate, fresh kernel replay after compilation, default 60-job build and
103 tests (21.825s, one skip). Exact checks preserve all 518 prior bodies, four frozen Lean sources,
six-path scope, recipes and mirror pin. Independent static review found no substantive issue; root review
corrected the register to retain parsed routing's parser premise separately from all-typed committed support.
Failures concern annotations, source normalization and observer composition; default 200k exhaustion in
call 26 was repaired structurally. Calls 01/03/17 displayed rejected elaboration-recovery goals, with no source
admission. Two early multi-write shell calls lacked explicit fail-fast chaining; their writes succeeded and
no error was masked. Subsequent edits use one Python call with separate checks. A duplicate collection of
finished call 19 returned an unknown-handle diagnostic without losing a running job. No interruption,
cap/limit increase or infrastructure retry occurred. The commit records the full measured ledger and commands.

**Preceding checkpoints.** `a945ea8` supplied stateful material support, initialized by `b4acf05` for all
typed traces/both flags including Stops. `b4acf05` passed scoped464/full517 and gate517/516, fresh replay,
default60 and103 tests (21.784s/one skip); its16 calls include five clean builds/eight failed builds/one exit-zero
tactic-index diagnostic and two passing exact checks. The checked source-head repair and canonical import
fix, and review's derivation-front/whole-session distinction, remain recorded in that commit.
[AGENT 2026-10-15] Split ordered copied-trial transcripts from configuration/dump plus committed support:
occurrence-indexed alternate executions need their own accounting contract on the existing journal.

`8f9b8a2` validated full staged-send/consume protection (gate508/508, replay, default60,103 tests/one skip).
Review's unfunded ghost-loan finding was resolved by funded transport and resident-owner consequences.
Its initial write/build shell lacked fail-closed chaining; the write succeeded, the process defect was reported,
and subsequent commands were corrected. `f1209f5` validated concrete Stack and normal-poll carrier contracts
(gate514/513, replay, default60,103 tests/one skip;44 calls). Its rejected kernel metavariables/recovery goals
and two corrected scope clauses are recorded there. [AGENT 2026-10-15] Deletion-tolerant normal-poll composition
allows actual positive payment to retire its peer; a later getter may Stop. No invented caller/base reservation
or totality premise simplifies the loop; failed prefixes remain separate from endpoint Worlds.

`192c7e7` validated whole normal admission and stable RX: exact admission receipt/allocation/enqueue/finish,
retained queued carrier on0/EPIPE, paid/freed ENOSPC, logical uncrypted-ring/cold-head structure and stable
ring-empty/NAPI-cold emptiness even at size zero. Its physical ring observer remains a separate correspondence;
initialized pipeline conservation is open. Gate520/518, fresh replay after compilation, default60 and103 tests
(22.860s/one skip) passed. The52 calls comprised49 builds(14PASS/35FAIL) and three exact PASS; default recursion
13/14/25/28/39 and recovery13/16/27/39 were repaired without raised limits. The worker usage interruption followed
finished failed16; root preserved all five dirty worktrees before takeover under
`refs/snapshots/proof-campaign-r4-admission-usage-20261015T194814Z/`, campaign snapshot
`06e337a6c24a24918ab45176d50cdd3f495f9487`. Review corrected a normal-only export's stopped-tail wording;
self-audit disclosed missing fail-fast chaining with successful writes/no masked error, corrected before final checks.

**Current foundations.** The persistent RX journal records actual session/decrypt source cuts and preserves
unconditional original erasure, the same full incoming R2 audit/probes and the established R4 boundary,
completion, receipt-validity and linkage meanings. Local receipt validity requires a valid incoming journal.
Actual ingress admission injection, initialized configured identity, packet transport and earlier routing alignment remain open;
ordered copied-trial origin receipts are optional separate coverage; initialized committed material support is now validated.

**Representation carry (`cb2348e`).** Handshake consumers write the captured returned PtrRing before
running the handler; only normal return reaches the counter decrement. The worker retains its 4097-poll
bound and physical full/produce behavior, including carried slots. Exact flood observers retain the single
sender, all ingress/inline polls, afterBatch, final guards and reached Stop history for arbitrary typed
messages. Rate-limiter allocation/refusal and both uninit tables are framed. Ten terminal bodies lost only
the removed `floodExact` argument; the other 479 were unchanged. The captured-ring callback contract
quantifies over the actual returned ring, with no new initialized validity premise.

**Checkpoint provenance.** Representation carry `15f0b979`; local disposition `ba0bbe3e`;
material retention `8f95d45`; packet/receipt link `0b1cd078`; owner/material frame `41df9916`;
initialized linkage `c0bff5e`; session/decrypt injection `60f8ea0`; RX-credit cuts `bc45a9c`;
material-retaining operations `00c204d`; full RX callback protection `8f9b8a2`. Their commits retain measured
effort, failed attempts, review dispositions and validation counts. At source-injection checkpoint `60f8ea0`, the
501-declaration permitted-axiom gate, fresh kernel replay, default build and 103 unit tests (one skip)
passed. The eleven historical recipes and 23 executable replay tests retain their representation-carry
validation: nine accepted agreements and two expected pending-dump rejections. They are not rerun for
proof-only additions.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build leanux-model
LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The supplementary `b1ec9e8` export passed Lean paranoid, lean4lean, nanoda, con-leche, con-ron and Lean default with
permitted axioms, covering only its 417 terminals/dependencies. `--inadvisably-no-sandbox` makes it a speedbump; plain
`lake check` excludes the non-default proof target. Missing PATH `git` caused one failure; the sole infrastructure retry
added command-local `/usr/bin` and passed within 900 seconds. No global change. Current-export recipe:

```sh
mkdir -p .tmp
capped -- scripts/in-bundle lake env python3 - <<'PYEXPORT'
from pathlib import Path
import runpy, subprocess
names = runpy.run_path("scripts/proof-gate", run_name="proof_gate_names")["terminal_statements"]()
with Path(".tmp/campaign-proof-export.ndjson").open("wb") as output:
    subprocess.run(["leanexport", "Leanux.Proofs", "--", *names], stdout=output, check=True)
PYEXPORT
capped -- timeout --signal=TERM --kill-after=10s 900s scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin"; export PATH; exec lake check --from-export=.tmp/campaign-proof-export.ndjson --paranoid --inadvisably-no-sandbox'
rm .tmp/campaign-proof-export.ndjson
```

**Reproduction provenance.** The generator reconstructs tracked `rx_roam_v6` operations and 40 historical records
formerly in `CONTENDED_ROAM_CMP`; seed/ten generated JSON values matched their pre-carry versions. This repaired
reproduction, not evidence. R2 recipes now check rejection and the accepted pre-delete boundary. R5/R6 synthesize
caller-jiffies from chosen clocks with independent arm-expiry checks. W7 reconstructs caller values from captured
expiry/delay via `with_timer_caller_jiffies`; that clock was not independently captured. Generated accepted streams are
mirror evidence, not captures or Linux schedule proofs.

**Owner-word boundary.** Since `de62c9d`, owner read/acquisition/fresh store-back, including NULL,
is observed in its actual order. Immediate NULL key put Stops before decrement; non-immediate
count-one/NULL writes zero and then Stops before erasure. Neither emits release. These are
arbitrary-World equations, not initialized counterexamples. The lifetime note's unreachable-arm
assertion is not a proof premise.

Builds retain command-local `LEAN_NUM_THREADS=32`, `LEANUX_QEMU_SLOTS=16`, the existing compiler
`-j1` and unchanged 32G cap. Failed elaboration recovery diagnostics, unknown constants and limit
exhaustion are recorded as failures in checkpoint commits; no source admission passes the gate.
No campaign-wide effort total is inferred. Commits use command-scoped Codex attribution; the earlier
`e7b0273` identity mistake remains in history without global changes or ancestry rewriting.

## R1 — anti-replay uniqueness and the inclusive floor

**Original versus proved.** The charter excludes counters at or below highest−8128; the proof excludes strictly below,
permitting unseen equality. The mirror's strict `ctrTooOld`, Linux `receive.c:counter_validate` and `selftest/counter.c`
agree. Arithmetic uses the one-based stored high-water mark; this is an intentional edge, not mirror/kernel
disagreement.

**Architecture.** [Terminals](../Leanux/Proofs/WG/AntiReplay/Statements.lean) compose pure window/S2 refinement,
CounterWindow bounds and `mirrorCalls_refines` with Evolution's `FloorHistory`/lifecycle transport.
`runner_floor`/`runner_uniqueness` cover successful executions, accepted schedules and reuse; committed/probe scope
remains ReplayWindow's. [AGENT 2026-10-13] Keep arithmetic/history in the proof tree.

**Rule Zero witness.** Kernel reduction proves `[8129,1,0,1]` accepts `[8129,1]`. Separately, six accepted Runner
operations establish a session and accept authenticated keepalive counters 8200 and 72 in lifetime 1, with identical
original/logged JSON: `72 = 8200 - 8128`. Records combine the historical session seed with `rx_window.json` datagrams,
widened legacy section identities, adjusted second-data clocks and synthetic site-128 wait bounds. This is
non-placeholder mirror acceptance, not a fresh capture.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r1-inclusive-floor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/Logged/Replay.lean
```

**Effort/review.** Fifteen minutes, five compile passes, sub-second replay; initial pre-import scan failed then rebuilt.
Two reviews corrected counter/ reproduction wording, with no correctness defect or remaining R1 obligation.

**Ranked mirror suggestions.** None. Changing the comparison would not preserve C behavior; adding production proof
history is unnecessary.

## R2 — lifetime identity and retained references

**Original versus proved.** The charter forbids later access to released allocation identities. [Terminal
contracts](../Leanux/Proofs/WG/LifetimeSafety/Statements.lean) now establish this for every initialized typed Trace/both
flags, including failure, without parser, length, progress, success or initial-invariant premises. Raw-reference
affiliation/credits are stronger: a stale scalar may resolve a replacement without resurrecting its old identity.

**Architecture.** [RunnerSafety](../Leanux/Proofs/WG/Lifetimes/RunnerSafety.lean) composes the map's concrete families:

| Layer | Abstraction/refinement |
| --- | --- |
| Store/Actions/Identity, ReleaseInv/AllocationInv | Stamps, slot reuse, resident uniqueness/frontiers; original initialization and preservation discharge allocator premises. |
| Prefix/Focus/Safe, SavedPeers | Histories outside exceptions; demanded captured reads/writes, exact Stops. Failed getters emit no resolved-object access. |
| BatchTrials/Calls, Audit/BatchAudit | Actual reached-filter World/history, exact ordered filtering and isolated safe trials; unevaluated candidates do not run. |
| Concrete FS/socket/configuration/dump/lifecycle/Env/syscall observers; PrefixOuter/RunnerAudit | Original accesses, saved loops, cleanup and indexed failures; literal Runner uses its actual returned World and defaulted arrays. |

[AGENT 2026-10-13/14] Observe actual accesses without invented getters; identity is not ownership. Failed calls retain
history, not a final World. Source-conditioned prefixes retain writes/reads before clock, record, allocation,
authentication or refcount failure; releases follow successful final puts. Erasure/endpoints alone do not prove
coverage. Device drop records residual-map retirement, not per-object C frees; queue scalar frames do not prove credits.

**Historical Rule Zero findings, through `7a92672`.** Eight accepted operations created 28 peers, began a stepped dump,
deleted/recreated wg0 with 27 peers and received a chunk. Saved slot 26/identity 27 (two references) instead released
replacement identity 55 (one reference), leaving peer/public-key entries naming the removed slot. The delivered chunk
was already queued; resume cleanup made the destructive put. A variant assigned replacement `10.0.0.0/8`, leaving an
orphan trie owner. Neither establishes resurrection or packet misrouting.

The guest rejects pending-dump deletion; the mirror omitted that W1/W2 guard. `c047e64` restored it, including queued
DONE. C holds `ctx->wg`; the old mirror resumed against the current device. This was a synthetic accepted-mirror domain
bug, not a Linux lifetime bug. Current unchanged recipes check accepted pre-delete state and exact original/observer
rejection at operation 3. Reduced `stale_cursor_retargets_replacement` separately exercises `wgGetDeviceDone`.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor-orphan |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/ReplayOrphan.lean
```

**Limits/review.** Packet stamps are `(ifindex,id+1)`, not ifindex alone. Occupied-slot behavior has erasure, not safe
allocation. Defaulted-array erasure covers JSON/Stops, not executable diagnostics. C initializes cache/handshake before
increment/insertion; the mirror reverses that order. This is no C memory-safety simulation. Reviews removed an
impossible KDF premise, restored a truncated legacy FS statement and repaired no-device, saved-object, jitter, reply and
hidden-idleTimers coverage. `wgUp`, not `wgOpen`, owns the negative-open reset. No unresolved reviewed source/premise
defect remains.

**Effort.** Caller slices typically 6–33m, saved-scan/socket about 43m. `8fab2ed`: sixteen closure calls, first full
result 10m18s; cursor checks under one second. Commit ledgers retain ordinary failures, an edit during a running
dependency graph, explicit-PID termination and recovery freezes. A coordinator mistakenly overlapped cached build/replay
under the then-serial plan; both exits were collected.

**Ranked mirror suggestions.** (1) If pending-dump deletion returns, retain the actual device lifetime in the cursor:
altitude-preserving, separately validated. (2) Keep named allocation/deletion/same-object updates: altitude-preserving.
No production history field.

## R3 — cryptokey routing

**Original versus proved.** [Terminal contracts](../Leanux/Proofs/WG/CryptokeyRouting/Statements.lean) establish
trie/configuration refinement and both initialized packet-routing halves. Incoming Stack entries carry their
strict-prefix source winner and configured publication certificate; outgoing completed handoffs carry their
destination winner at the actual front entry. Public parsing supplies configuration address shape. Both
placeholder settings and indexed-Stop prefixes are included. Unconditional executable erasure covers all
typed traces. The [outgoing report](2026-10-17-r3-initialized-transmit.md) records complete caller coverage
and its precise selected-occurrence theorem boundary. No R3 Rule Zero counterexample is asserted.

**Configured source cuts (validated).**
[ConfiguredIdentity](../Leanux/Proofs/WG/Peers/ConfiguredIdentity.lean) follows original table insertion,
lookup acquisition, list unlink/table filtering/dead setter, retirement and fresh owner store-back, including
aliasing and NULL. Its supplied invariant permits stale rows and dead residents. Concrete configuration/removal caller closure and initialized captured current/owner
checks now hold; the initialized joins above complete packet authorization.
[ConfiguredSession](../Leanux/Proofs/WG/Origins/ConfiguredSession.lean) couples the same actual front
RunWitness/Context, material/stamp/epoch, owner and configured entry row; actual whole normal session
completion supplies live/self facts before support is retained through the tail. A stopped tail retains the old
observer's receipt, not a configured endpoint claim.
[PublicationIdentity](../Leanux/Proofs/WG/Packets/PublicationIdentity.lean) connects original prepare's
captured ring pop to its actual stored decrypt receipt and pre-IRQ publication. Successful decrypt gives
historical session caller/public key, exact packet/AEAD transformation and preserved allocation stamp;
Some prepare can instead publish DEAD. Arbitrary older receipt history is retained, and the new receipt has
an exact fresh position. The initialized runner now derives captured configured/current support at each decrypt.
A packet peer-frontier invariant handles fresh creation, while local retention connects the earlier
publication to actual normal consumption. Whole-call packet transport now holds through
the original initialized runner for all typed traces and both flags, including stopped
prefixes. The contemporaneous initialized lookup/Stack join is now proved for
all shaped typed traces, with shape supplied by successful public parsing.
Initialized transmit handoff authorization is also proved through the concrete
caller chain; no later wire-send guarantee or Noise authenticity is claimed.

**Architecture.** The [map](proofs.md#layers) details these refinements:

| Layer | Abstraction/refinement |
| --- | --- |
| Prefix/Tree/Winner, pure Insertion/Removal | Independent longest-prefix specification, canonical replacement and ID erasure/compaction. |
| RepAt/ForestRep/contexts and source cases | Values/backlinks plus actual root linkage; CIDR growth derives depth/130-step lookup. All insertion and seven removal cases refine original calls. |
| RoutingInvariant/coherence/metadata | Both roots, compression/Nodup, resident-list correspondence and allocation frontiers; orphan owners remain representable. |
| [RoutingHistory](../Leanux/Proofs/WG/AllowedIps/RoutingHistory.lean), parser/clear | Node-ID-free flat updates, initialized actual-call histories, reached-root winner, parsed bounds and normal clear. |
| Completion/lifecycle/concrete frames, [RunnerRouting](../Leanux/Proofs/WG/Configuration/RunnerRouting.lean) | Actual primitive completions through public commands and every caller to literal initialized Runner; full-result/JSON erasure and actual final-World agreement. |

[AGENT 2026-10-13/14/15] Use structural contexts/exact source factors, preserving raw addresses, allocation order and
unrelated nodes. Survivor frames permit deletion. Record actual completed primitives and return the actual World beside
JSON.

**Local boundaries.** Insertion requires representation/freshness, bounded input and resident target; placement derives
its alternatives. First allocation refusal preserves add's Kernel; second consumes an ID then frees/filters it. Neither
is World rollback; insert increments sequence before success/refusal. Replacement filters all lists then appends once;
fresh insertion does not sanitize dangling lists.

Removal keeps listDel-before-lookup and detach/read/free/fresh-parent-read order. Representation, not raw tags, derives
linkage/separation. Resident-list coherence allows orphan owners; the original saved list drives removal. Its
represented totality is proved, not assumed. Normal clear saves both roots before reset, preserves list provenance and
empties represented forests/lists; physical node emptiness and universal successful termination are not claimed.

Whole setAllowedip normal returns record signed result/views: zero applies possibly-idempotent flatInsert; negatives
retain flat tables, not necessarily sequence/frontiers. Removal is recorded inside peerMakeDead; clear follows WG.free.
Later Stop retains earlier events without failed World or whole-removal success. Lookup/create supplies residency, not
public-key association. Optional routing covers absence/lifecycle/fixture/prefill. Silent traffic/worker/timer/dump
frames allow retirement; unchanged journals are not packet authorization.

**Local nullable affiliation.** The new invariant permits NULL words, missing referents and slot aliases; it bounds
frontiers and resident key/slot/packet compatibility, not index owners or stamp uniqueness. Original lookup preserves it
through fresh store-back, including owner/target aliasing; successful handshake lookup returns its owner. Optional
creation, rotation and beginSession preserve it without distinct-slot/resident-owner/drain premises. Getters justify
cached writes. Literal staging/consumeData factors expose actual acquisition. Strict TX acquisition derives positive
credit and, with local compatibility, the sending peer; RX retains the optional owner. Successful decrypt preserves
peer/key fields and its exact AEAD equation. Staging supplies one peer/key for its constructed batch, not arbitrary
batches or every packet's own encryption argument. OwnerCertificate is a full-record snapshot; execution needs a
separate helper-run premise. A later NULL store-back does not invalidate that historical snapshot or establish
initialized affiliation. [AGENT 2026-10-15] Reuse one nullable projection/source cuts, preserving the stronger old
SlotAffiliation and separating snapshots from run witnesses.

**Actual local routing cuts.** [LookupExecution](../Leanux/Proofs/WG/AllowedIps/LookupExecution.lean) refines normal
original lookup/lookupSrc/lookupDst answers to flat winners under actual entry RoutedView. Failed acquisition is a
Stop, not a None answer; successful termination is not assumed universally. [AddressShape](../Leanux/Proofs/WG/Packets/AddressShape.lean)
derives every xmitPackets/GSO packet and rst4 reply's family/destination-byte shape, preserving truncation of an
unbounded supplied Nat. The actual wgXmit header guard derives address bounds. [RoutingCuts](../Leanux/Proofs/WG/Packets/RoutingCuts.lean)
factors literal consumeDataDone/wgXmit, retaining malformed, ordinary-error and Stop branches. RX returns the actual
input/output family and unchanged source through ECN/trim. TX zero return yields one exact query/selection/splice/tail
World chain and the original packet list with its supplied MTU. Handoff is staged append, not later encryption/wire
transmission. [AGENT 2026-10-15] Reuse local source factors and existing routing frames; add no Runner observer or
initial-trace premise. Arbitrary mixed-family packet lists are not silently treated as constructor output.

**Local historical origin cuts.** [MaterialOrigin](../Leanux/Proofs/WG/Keypairs/MaterialOrigin.lean) records exact
allocation/frontier equations, receiving-material field rules and actual clock/KDF/getter/store derivation steps.
[SessionOrigin](../Leanux/Proofs/WG/Keypairs/SessionOrigin.lean) observes allocation before later failures and normal
front completion before zeroing/rotation/index replacement. Only a Some front receipt denotes derivation: its
connected entry-state/nullable-word/allocation/peer-read chain retains the actual remoteStatic/chainingKey record
and consecutive initializer/derive Worlds. Material is resident at the derivation cut; later deletion is allowed.
The field rules do not establish a global material invariant or initialized handshake self-word compatibility.

[RxOriginCuts](../Leanux/Proofs/WG/Packets/RxOriginCuts.lean) observes the complete admission front through allocation
before enqueue, plus the immediate allocation itself. Its Some receipt exposes actual index lookup, key acquisition,
peer check and full packet construction; a normal dropped front supplies no allocation claim. ENOSPC cleanup and later
Stops retain earlier receipts. The worker captures its actual stored getter/decrypt run once, before payload/state
publication. Successful decrypt identifies the resident key and exact AEAD equation and changes only nonce/bytes;
publication's concrete setter changes only state. No assumption identifies every input with allocation-time ciphertext.

Original erasure is unconditional. Exact full R2 result/World-or-Stop/history projection requires the existing
AllocationInv on the same input World's projected incoming history. Receipt validity is preserved from valid incoming
history (empty qualifies), independently of AllocationInv.
[AGENT 2026-10-15] Reuse captureObserved and existing R2 source cuts with a shared receipt journal; retain the local
projection domain rather than add invalid-history append infrastructure. No initialized origin premise or new Runner
hierarchy was introduced. Initialized committed material/stamp matching is now established below. Configured peer
public-key provenance, ingress/packet transport to poll/Stack and identity closure
are supplied by the later initialized authorization contracts. Copied-trial
origins remain optional separate coverage. A snapshot or raw peer winner alone
does not supply those links.

**Local material retention.** [Origins/State](../Leanux/Proofs/WG/Origins/State.lean) supports every resident valid
receiving key with one full successful derivation-front witness and its keep-or-clear owner; invalid keys require no support.
[Origins/SessionMaterial](../Leanux/Proofs/WG/Origins/SessionMaterial.lean) proves actual front installation/tail
retention and the combined local session/decrypt adapters. Its strict journal-order conclusion uses the supplied
entry support, not an initialized-history provenance theorem. Normal Some-front facts recover the complete entry peer;
decrypt retains the actual stored packet, material and AEAD transformation, without equating packet.peer to that peer.
[Origins/IndexMaterial](../Leanux/Proofs/WG/Origins/IndexMaterial.lean) derives the concrete owner-acquisition and
index-lookup frame, including nullable store-back, and reuses the existing access adapter for supplied support.
The new `RetainingLeaves`, `RetainingTraffic` and `RetainingLifecycle` source contracts extend normal
material retention through concrete non-installing traffic, timers and lifecycle operations. They reuse actual
record getters and stronger canonical masks, with no affiliation/residency/credit or successful-drain premise.
These local material-retention contracts alone do not provide ingress injection
or configured peer/packet provenance. The later initialized authorization
composition supplies both, building on the caller propagation below.

**Actual caller injection.** [ReceiptTypes](../Leanux/Proofs/WG/Origins/ReceiptTypes.lean) keeps existing qualified
receipt/context names while removing the import cycle. [HandshakeSources](../Leanux/Proofs/WG/Origins/HandshakeSources.lean)
has exact original and lifetime-observer factors for response, after-MAC, reception and captured-ring receiveStep.
[HistoryAdapters](../Leanux/Proofs/WG/Origins/HistoryAdapters.lean) focuses actual session/decrypt runs once into the
existing RX history. The decryptStep prepare cut and both activation/whole receive-worker entrances are wired to it;
normal tail/decrement and Stop bypass order remain original. All prior audit/probe history survives projection.
Old metadata decoders erase session/RX receipts; the linkage decoder retains lifetime access events. Its concrete
Protocol instances preserve the existing R4 predicates. Copied scheduler trials retain their isolated R2 observer;
this extension does not claim their session/decrypt receipts. Available admission receipt types do not mean ingress
admission has been injected. That local layer alone does not establish initialized material support; the new Runner composition below does.

**Stateful caller support.** [AGENT 2026-10-15] Keep the existing observer and use positional checks plus
`Origins.Inv (sessions h)` at the actual World; bundle append and state-preservation proofs to avoid repeatedly
expanding the same source continuation. `HistorySupport` composes exact session installation and stored decrypt
receipts with concrete quiet erasure/material frames. `SupportCallers` covers both session sites, crypt preparation,
NAPI, activation, recorded scheduling and nested rescheduling. `SupportEnvironment` covers the complete receive
worker, deferred send/clear/crypt work, both timer modes, ingress/flood/batch and controls. The generic worker wrapper
requires its actual body contract; every concrete typed environment constructor discharges its own contract.
The supplied journal may contain prior receipts only when its explicit validity/support predicates hold. Strict
prefixes distinguish duplicate equal receipt values. Saved-probe entry support does not observe a copied trial's
internal origin events. Those local preservation contracts are now composed by `SupportRunner` through actual configuration/dump,
syscall wrappers, dispatch and source post-workers. The original fixture and successful seccomp prefill discharge
initial support; failed prefill leaves empty safe history. Every typed trace/both flags retain checked committed
history, including Stops. This is an initialized material chain, not a configured-public-key or packet-binding theorem.

**Initialized closure and limits.** Initialized committed support preserves
ordinary-negative cleanup and Stops. Public parsing supplies configuration shape;
the incoming and outgoing authorization theorems connect each selected actual
packet occurrence to its contemporaneous initialized routing history and
configured identity. Whole-run packet transport is supplied by the concrete
caller composition, rather than inferred from a local material certificate.
Copied-trial packet certificates are optional separate coverage, not a prerequisite of the committed charter path claim. Nullable compatibility is insufficient for historical key identity.
Partial failing clear has no completion marker. The historical R2 orphan recipe is now rejected, not a current
misrouting witness; no new accepted counterexample is claimed.

**Effort/review.** Source-cut, local-origin and nullable-affiliation attempts and failed elaboration
diagnostics are recorded in `ce12402`, `99e4f88` and `bcbf733`; material/owner/source-injection
extensions are in `8f95d45`, `41df9916` and `60f8ea0`. The last injection used 23 builds
(three PASS, twenty ordinary FAIL) and two exact checks, with full build collected 53m33s after
acceptance. Independent review corrected creation/None-front wording, protocol linkage, returned-World
claims, valid-history premises and a stale activation header. These corrections are reflected above.
Two after-MAC proofs retain theorem-local 800,000 heartbeats after default-limit failures; no global
or memory-cap increase was made. The rejected generic continuation proof was removed: an arbitrary
callback protocol did not provide its required abort law. No source admission or accepted R3
counterexample resulted from these failed attempts.

**Ranked mirror suggestions.** None. Integer-address refinement needs no production restructure; C byte-layout
correspondence remains informal.

## R4 — ingress conservation, full-ring characterization and GRO order finding

**Current disposition.** The [full-ring report](2026-10-17-r4-full-ring.md)
completes the named W7 episode with 1022 enqueues and two source-connected
refused allocations later released as DEAD heads. Its compiled replay and
kernel-proved source/geometry contracts are stated separately.

**Current initialized account.** The [ingress coverage report](2026-10-17-r4-ingress-coverage.md)
connects original initialization, every actual operation and every accepted
receive position to a pending or actual completed-poll disposition. The
[live-ring report](2026-10-17-r4-live-frontier.md) supplies initialized numeric
bounds and physical refinement. Peer-queue ENOSPC cleanup remains distinct
from ring-full EPIPE's queued DEAD path. Chronological GRO order is refuted.
The named W7 source episode is handled separately in the
[full-ring report](2026-10-17-r4-full-ring.md).

**Original versus proved.** The charter requires accepted-schedule order and no silent loss/duplication.
[Terminals](../Leanux/Proofs/WG/DeliveryOrder/Statements.lean) prove initialized committed callback-entry stamp
uniqueness for every typed Trace and both placeholder settings, including Stops. Chronological GRO order is false. Local/persistent
polls and every initialized Runner normal return pair entries with actual normal Stack returns. Failed histories
retain valid receipts and at most one trailing unfinished entry. Normal
accepted runs have the initialized pending-or-disposed account; no final World
or funded endpoint is asserted for a Stop.

**Local reference protection.** [Carrier state](../Leanux/Proofs/WG/Queues/RxCarrierState.lean),
[ingress cuts](../Leanux/Proofs/WG/Queues/RxIngressProtection.lean) and
[cleanup cuts](../Leanux/Proofs/WG/Queues/RxCleanupProtection.lean) now prove source-acquired loans, fresh allocation
transfer, pure-IRQ repayment, actual queued/selected/paid/free transitions and the successful ENOSPC suffix.
All ledgers are explicit local inputs. Remaining positive demand derives non-retirement; no RetainsRx or retrospective
slack premise substitutes for it. The poll suffix uses its caller pid under the actual earlier packet-peer guard.
Key payment must have returned; key-credit funding is not asserted. The new full staged-send and consumeDataDone
contracts preserve that same RX ledger under nullable operational owner compatibility, with exact typed TX/send-work
handoffs. They derive rather than assume strict acquisition/repayment balance and preserve separate key/slot facts
through promotion and timers. New [key protection](../Leanux/Proofs/WG/Queues/RxKeyProtection.lean)
separately preserves nullable packet/current-key compatibility using backwards non-NULL word retention and tagged
current-cell provenance, allowing deletion and only actual received-key promotion. The [Stack proof](../Leanux/Proofs/WG/Queues/RxStackProtection.lean)
carries the actual positive destination loan across nonempty typed handoffs and its repayment, including normal
negative errno and delayed held-GRO callbacks after packet free. The [normal poll proof](../Leanux/Proofs/WG/Queues/RxPollCarrier.lean)
selects the actual cached queue occurrence, retains its charge until peer payment and its cell until free, then
filters the same original ledger by fresh removal identities. Completion getters and actual GRO/Stack calls remain
in source order. No extra caller/base reservation, residency, totality or key-allocation frontier premise is used.
Uncrypted-head normal return retains unremoved queued carriers. Whole local consumeData admission and its
stable ring/head boundary are proved below. The later initialized account
composes concrete IRQ, base/work/dump, worker and lifecycle contracts; these
local lemmas alone do not derive that initialized protection.
Handoff alone supplies no key-word/slot frame or TX ownership; the new separate source frames supply the local
compatibility needed here. Stopped calls have no claimed final World.

**Whole local admission and stable boundaries.** [Admission](../Leanux/Proofs/WG/Queues/RxAdmissionCarrier.lean),
[ingress](../Leanux/Proofs/WG/Queues/RxIngressCarrier.lean) and
[stable RX](../Leanux/Proofs/WG/Queues/RxIngressStable.lean) now compose the actual original consumeData source.
The exact same receipt/owner witness selects the returned ledger: no admission retains the old ledger, success
and EPIPE add its queued carrier, and ENOSPC returns the old ledger with the new storage absent. Packet allocation
validity is supplied locally; the proof derives vacancy and does not assume surviving caller residency. StableRx
adds all-queued phases, ring-items permutation with uncrypted carriers, and an uncrypted cold-queue head; it does
not forbid dead/crypted tails. The physical journal starts at the existing supplied Refines/Inv premise and its
actual existing observer is preserved independently on the same normal execution, including ring size zero.
Stable drainedness plus ring-empty/NAPI-cold implies empty inventory/store. Arbitrary malformed rings, hidden-none
afterBatch exits and suspended worker locals require their concrete caller
contracts. The later initialized composition supplies compatibility, durable
funding and actual admission occurrences. These local source contracts alone
do not assert an all-prefix endpoint state.

Independent architecture review identified a source-level arbitrary-World countermodel to framing all consumeDataDone
by RX credits alone: P owns a selected credit plus reservation at count two, but its next key belongs to Q; staging
acquires Q and dead-create cleanup pays P, reducing P below demand. This is not an accepted Runner counterexample.
The local consume theorem uses operational packet-key compatibility; the new normal-poll theorem preserves it
and handles reply-triggered TX through all-resident-current compatibility, not cryptographic unforgeability. Paid-phase history and allocation freshness remain separate proof obligations, not inferred from the
three state predicates. No mirror repair is proposed from this arbitrary-state example.

**Local disposition extension.** A fresh poll partitions actual removal occurrences by permutation, with no allocation
premise. Normal return uniquely partitions nondelivery decisions/normal None and completed Stack callbacks. Stop
additionally retains at most one unresolved selection, the entire unentered selected-offer suffix and at most one entered,
uncompleted callback. The suffix includes the second held offer rejected before insertion; it is not a claim that
all residuals are physically stored in GRO. A completed threshold callback stays completed if later put/free Stops.
Nondelivery decisions on Stop do not assert completed cleanup. Normal None has the original keepalive/header/length
or repaid source-peer-mismatch route; cause predicates may overlap. Endpoint normal None is proved impossible;
malformed families/unsupported IPv6 Stop instead. The state predicate is accurately “not crypted,” not assumed DEAD.

**Packet-to-receipt link.** The new literal-poll proof closes the previously missing selected packet/stamp/peer
relation at consume entry, using the original second getter, full-store drop/counter/endpoint frames and actual peer
guard. Strict capture-read/removal support precedes the exact consumed receipt; the identical whole receipt/Entry is
carried through buffered, entered and completed events in that order, including Stop prefixes. The four history
positions are: incoming h0, actual consume output hc, hc followed by consumed, then buffered on Some. This call
appends its consumed receipt only after hc. A delayed callback needs no current packet residency; consume.after need not equal Stack.before.

The original `ConsumePayloadValid`, `BoundaryInv` and completion protocol are unchanged. New HistoryLinked means
ordered receipt linkage, not validity of every check or Stack witness. Fresh suffixes cannot borrow incoming metadata;
persistent promotion retains the exact prior audit seed/probes, and finite polls preserve explicit incoming linkage.
These local contracts need no allocation or World premise. The new `RxLinkCallers`/`RxLinkEnvironment`/`RxLinkRunner`
proofs propagate linkage and separate checked-receipt validity through the existing concrete callers. Every typed Trace
and both placeholder settings derive them from empty initialization, also on Stop. Their global committed order retains
full receipts and the exact R2/probe history, but does not identify poll-local
segments. Initialized identity is supplied by R3; the later R4 account supplies
admission credits and normal carrier conservation.

Independent review checked two potentially false joins. The standalone consume helper accepts arbitrary skb/stamp
labels, so its SelectedAt/peer premises must be discharged by the literal poll; they are. Earlier removal plus final
read support alone permits `[removed k, consumed k r, read k, removed k]`; strict-prefix ReadBeforeRemoval threading
prevents borrowing the later duplicate. This is an arbitrary-journal countermodel, not an accepted Runner trace.
Review also corrected “validity” to “linkage” for the old persistent history and “is not” to “need not equal”
for the consume-after/Stack-before Worlds; no inequality is claimed. The earlier partition helper's
disjointness wording remains qualified: fresh-poll Nodup, not generic Account alone, supplies uniqueness/disjointness.
See [receipt source factors](../Leanux/Proofs/WG/Queues/RxDispositionReceipts.lean) and
[local accounting](../Leanux/Proofs/WG/Queues/RxPollDisposition.lean).

**Architecture.** Refinement chain:

| Layer | Abstraction/refinement |
| --- | --- |
| RingGeometry/Steps, journals/occurrences, RX/TX source journals | Stale physical slots/live FIFO, finite occurrence conservation and original installed mutations; Stop prefixes separate from endpoints. |
| PrevQueue/RxQueueView, poll/GRO tags/provenance | Cached peek, deletion-permitting cell frames and exact bytes/origins; selected order, not chronology. |
| [Joint projection](../Leanux/Proofs/WG/Queues/RxPollJointProjection.lean), stamp phase/support/history | Same execution's original/GRO/lifetime correspondence, actual read support, uniqueness and normal release. |
| [Consume link](../Leanux/Proofs/WG/Queues/RxConsumeLink.lean), [poll/receipt link](../Leanux/Proofs/WG/Queues/RxPollReceiptLink.lean) | Actual selected cell at consume entry; strict read/removal/receipt/Entry order in fresh suffixes, persistent and finite-poll linkage. |
| [Callback completion](../Leanux/Proofs/WG/Queues/RxPollCompletion.lean) | Ordered entry/normal-return pairs; failed prefixes retain at most one unfinished entry. |
| Concrete caller spine, [Runner history](../Leanux/Proofs/WG/Queues/RxRunnerHistory.lean), [completion](../Leanux/Proofs/WG/Queues/RxCompletionRunner.lean), [linkage](../Leanux/Proofs/WG/Queues/RxLinkRunner.lean) | Same-history full R2 audit, isolated trials, actual returned Worlds, initialized entry/completion uniqueness and packet/receipt linkage. |
| Borrow/TX disposition, [endpoints](../Leanux/Proofs/WG/Queues/TxDispositionEndpoints.lean) | Adjacent repayment and original admission/publication/removal/disposal cuts. |

[AGENT 2026-10-14] Prove receive-to-stack duplicate freedom before conservation, plus named W7 drops. Universal outgoing
staged-to-socket conservation is extra scope. Independent erasures do not prove journal correspondence.

**W7.** Two size-1024 produce/consume pairs leave count zero but slots 0/1 occupied. The next 1024 offers accept
1022/refuse two, ending producer/head/tail 0/2/0. The [tier](2026-10-13-w7-full-ring-tier.md) corrected the omitted
keepalive slot; Linux/mirror agree on two EPIPE drops, all producers preceding consumption. The pure witness is not
whole-run refinement. Operations are tracked in `corpus/w7-tier/w7_ring_wrap.json` and extra-ENOSPC `w7_ring_1025.json`;
full hidden streams are not. This recipe checks only the **eight-transmit scheduler regression**, with rearranged
records/synthetic wait bounds and qualified caller-clock reconstruction:

```sh
capped -- scripts/in-bundle bash -o pipefail -c 'python3 -B -c "import json; from evaluator.test_model_replay import W7_CRYPT_AHEAD, with_jiffies_end, with_timer_caller_jiffies; print(json.dumps(with_timer_caller_jiffies(with_jiffies_end(W7_CRYPT_AHEAD))))" | lake env lean --run Leanux/Proofs/Logged/Replay.lean'
```

Physical occupancy differs from live count; retirement clears consumed slots. Positive/zero-size laws and pending
contents are explicit. Tagged refinement exists, not uniquely; ordinals are not allocation stamps and TX occurrences are
batches.

ENOSPC precedes any ring offer; EPIPE can follow queue/packet changes. Pre-installation Stop emits no admission. Normal
EPIPE retains queued item/DEAD head; normal ENOSPC removes supplied packet slots. Actual normal DEAD-head txStep
disposes without socket output. Publication can Stop before EPIPE returns; disposal frees packets then saved
key/supplied peer, retaining earlier releases on later Stop. Duplicate IDs may Stop at a second getter. Intervening
aliases can change the mark: these endpoints do not establish arbitrary-schedule transport. Actual lookupSrc/peerPut
acquisition yields non-deleting repayment and restores semantic Kernel contents without trie/ownership premises, not
total repayment or whole-callback protection. Publication retains all TX queues even for differing peers.

**Accepted GRO counterexample.** The chronological `original_poll_callback_prefix` over `2c7a076` was retired at
`f45bde8`; GroSafe was not weakened. Six generated operations receive nonce 0, one-byte ACK-only TCP 40001→80, then
nonce 1, SYN on flow 40002→443, in one peer/key lifetime. Original/checkpoint/acceptance JSON agrees, validator history
is exactly `(lifetime,0),(lifetime,1)`, and inputs match that receiving key. Original observable ciphertexts instead
contain the SYN RST at outgoing nonce 1, ACK RST at nonce 2. Identity/cleanup checks pass. This is accepted mirror
input, not a capture/kernel schedule proof; checkpoint `3d50a4a`.

```sh
capped -- scripts/in-bundle bash -o pipefail -c 'python3 -B docs/proof-campaign-replay.py r4-gro-reorder | lake env lean --run Leanux/Proofs/WG/DeliveryOrder/ReplayGro.lean'
```

ACK remains held; SYN enters the normal list. `original_gro_held_then_normal` proves callback `[N,H]` under the real
classifier hypotheses. This post-GRO nuance does not reverse WireGuard/decrypt FIFO. C supports these different-flow
inputs (`tcp_offload.c:261,318,379–381`, `gro.h:528`, `dev.c:6385,6388`). Zero-payload `len < mss` flushing and
same-flow held inspection on the normal arm remain unconfirmed source concerns, not differential findings.

**Identity boundary.** Capture uses the same original second successful getter before removal, storing `(ifindex,skb+1)`
without extra reads. From valid prior allocation history, actual capture-read support and safe lifetime projection
exclude prior releases. Fresh local metadata, capture/removal/release phases and full GRO byte/key provenance derive
distinct removal/entry stamps on every prefix, actual suffix releases on normal return. Persistent histories preserve
prior audit/probe events at identical incoming history; erasure/Appends imply no neutrality. BoundaryInv requires normal
releases; failed BoundarySafe does not. Ordinals restart at zero. Held bytes may reach Stack after storage free.
`rxPollFree=false` includes `consumeDataDone=none`; drops and handoffs both free storage, so neither flag nor free alone
gives a disposition.

**Caller coverage.** Polls/IRQ, crypt/cryptAhead, scheduling, flood/batch, timers/controls and syscalls/Runner retain
guards, section order, negative-errno cleanup and Stops. Publication IRQ may free its packet before return; encryption
keeps initial softirq, CryptAhead temporary queues/suspension/late Stops. Filter markers isolate trials. Composition
uses returned Worlds and identical full R2 history, without
parser, length, success, drain, credit, residency, progress or initial-allocation premises.

**Callback completion.** `captureObserved` runs the existing observer once at its actual World/history, preserving
failed journals. Entry precedes Stack; normal return appends actual value/World receipts, erased by old decoders.
Closed/CompletionPrefix prove ordered valid Stack-return pairs through local/persistent polls and the existing
concrete caller/Runner hierarchy. Every typed Trace and both placeholder settings derive the protocol from the empty history,
without parser/allocation/progress premises. Normal return matches all entries; Stops retain valid receipts and at most
one trailing unfinished callback. Completed stamps inherit existing entry uniqueness. Only new local suffixes are
promoted at the same seed; isolated trials remain outside committed pairing. No new operational hierarchy or stronger
BoundaryInv is introduced. Stack return does not prove inbox/reply success or whole-pipeline conservation.

**Source-comment finding.** Independent review (2026-10-15 01:35:32–01:40:05) found `PeerRemove.lean:30,110–122` relying
in prose on `requireNotPending`, actually `State.lean:102`'s `pure ()`. Later inspection found the same in
`Send.lean:17–20,56`, plus obsolete single-item queue scope at `:22–24`. Mirror comments remain untouched; they prove no
quiescence. No accepted loss/ duplication witness was found: arbitrary last-peer erasure is not initialized, and the
poll's last-put candidate Stops at a later getter. No kernel bug claim.

**Closure and limits.** The initialized runner derives its actual funded
residual ledger, complete normal ingress source coverage and completed-poll
release certificates. Every accepted admission has a named fate or exactly
one pending identity, including one removed before its syscall returns. Finite
accepted prefixes may retain work. Stopped admissions have no claimed endpoint
World; an additional funded account for them is not part of this result.
The named W7 replay now follows every producer position and the actual
record-selected encrypt/TX drain to the same two refused packet releases.
The source factors retain the preceding CQE/reset, actual worker selection,
iteration counters, earlier queued items and final poll. Empty work bookkeeping
alone is never the justification. Universal outgoing completion and fairness
are not asserted.

**Effort/process/review.** Earlier ring, receipt and caller ledgers are in `00fafa4`, `57cb46e`,
`c4ef635`, `ec95fa8`, `3dec2c3`, `79dce53`, `1b76322`, `983f84b` and `65e6a6d`;
the subsequent disposition/linkage checkpoints are listed above. Failed tactic searches, rejected
recovery terms and dependent kernel diagnostics were failures and were corrected before validation.
The disposition checkpoint's first coordinator kernel replay overlapped recompilation and failed;
its sole infrastructure rerun after gate collection passed. Fresh replay now follows collected builds.

Two process failures remain disclosed. The initial ring writer resumed after deliberate termination
without snapshot; work stopped and six dirty worktrees were preserved. Later an unnecessary duplicate
Runner build was interrupted (FAIL 130), followed by a corrective edit **before preservation**.
Root then stopped work and snapshotted six dirty worktrees under
`refs/snapshots/proof-campaign-r4-runner-duplicate-20261015T021102Z/`; campaign snapshot
`d5336546034e925211a891d88720e913f971c091` matched the dirty tree, with branches/indices untouched.
Passing validation does not erase either violation. Completion-worker interruptions were preserved.
No R4 memory cap was hit.

Independent reviews required direct provenance and corrected EPIPE-at-return, failed-entry, ownership,
ifindex, uniqueness and census wording. Immediate repayment appends actual steps, not hidden records.
The current initialized conservation and finite W7 claims, and their limits,
are stated above; dated checkpoint reports retain the earlier open stages.

**Ranked mirror suggestions.** None; physical occupancy explains W7 and proof-side observations suffice for the checked
properties.

## R5 — key lifetime enforcement: Rule Zero findings

**Original versus proved.** The unconditional readings below are false in accepted mirror inputs. Thirteen [local
contracts](../Leanux/Proofs/WG/KeyLifetime/Statements.lean) remain; universal TX certificate transport and whole-run
AEAD coverage are open.

| Original wording | Checked boundary |
| --- | --- |
| No encryption/decryption after `REJECT_AFTER_TIME` | RX attempts require the actual unexpired comparison. TX checks at staging; a retained keepalive can encrypt after recorded expiry. |
| No use past `REJECT_AFTER_MESSAGES` | RX tests stored counter before AEAD, wire nonce afterward: R/R+1 authenticate before rejection. TX assigned nonces are certified below R. |
| No material use after zero until a new handshake | Zero queues clear work; even after slots/index clear, a queued packet reference can retain material through encryption/transmission. |

Time witnesses are type-4 transport **keepalives with empty plaintext**, not nonempty inner packets. Linux
`receive.c:242–331`, `send.c:162–219,342–414`, `noise.c:112–177` and `timers.c:105–133` explain
authentication-before-validation, staging admission and refcounted clearance. These are charter-statement artefacts, not
demonstrated Linux security defects; no upstream-tray report is justified.

**Architecture.** KeyTimes/Clock proves signed64 age/operand correspondence, equality expired. Receive factors derive
actual pre-AEAD guards/events; singleton coverage/failure endpoints exclude vacuity. Validator acceptance bounds wire
nonce. Staging certifies actual key/clock/allocation/nonce arguments before createData, including later Stops.
ZeroTimer/Logged TimerPass/Advance preserve complete stores and original syscall erasure; scheduler events are not
per-packet AEAD coverage. [AGENT 2026-10-13] Retain positive local boundaries beside Rule Zero witnesses, without
claiming kernel timing.

**Counter witnesses.** With `R=18446744073709543486`, `r5-rx-wire-limit` uses the tracked session/nonce-R packet;
`r5-rx-wire-past-limit` derives the same session with the harness Noise helper and generates R+1. Original/observer JSON
agrees: stored operands `[0,R]`, successful AEAD, then validator rejection `[R,R]` or `[R+1,R]`, with no acceptance.
This is authenticated decryption and drop, not delivery.

`r5-delayed-encryption` creates a session at 132s; two nonempty receives set the keepalive second-fire flag. Nonce 1 is
admitted at 311s against deadline 312s. At 322s, expiry invalidates sending, stages another keepalive and queues
handshake; crypt encrypts/transmits the earlier packet with unchanged material first. Unit order, identity, references
and new ciphertext are checked directly.

Seven-operation `r5-coherent-post-clear` moves that second expiry to 679s. Zero expiry is 132+540=672s;
its level-4 wheel bucket becomes due at 678.832s. Zero and real
clear work precede crypt. All published key slots are empty, index absent and handshake zero, while the same packet
keeps one reference to the same material. Ciphertext precedes queued handshake work; transmission frees packet and final
key reference. Older five-operation `r5-post-clear-transport` deliberately has incoherent coarse/jiffies clocks and
disabled arm records; the coherent witness does not upgrade that evidence. Its reconstructed wheel schedule
uses a 535-second keepalive and final jiffies 139264, so post-transmit rearming falls beyond the wait.

Both coherent variants check monotone clocks, arm records, exact delays and `J(t)=2^32-75000+250*t`; kind-310/site-128
windows end at 323/680s. TAI follows elapsed coarse time, queue/timer identities remain stable and cache clocks are
disabled. Complete original advance agreement includes product state, decisions, endpoint, jiffies and record exhaustion.
Arithmetic coherence and the late-callback window do not prove Linux scheduling reachability.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-rx-wire-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
python3 -B docs/proof-campaign-replay.py r5-rx-wire-past-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
python3 -B docs/proof-campaign-replay.py r5-delayed-encryption |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-coherent-post-clear |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-post-clear-transport |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayPostClear.lean
```

**Review disposition.** The [independent review](2026-10-13-review-r5-counterexamples.md) of `7fc444d` supports
classification/local statements; clock qualifications are in [review items
7–8](2026-10-13-review-items-7-8.md#proof-domain-qualification). Reviewed witnesses landed in `3d50a4a`. Two supporting
assertions are not adopted: authenticate-then-check is actual, not logically necessary; the witnesses establish no
measured/universal worker-latency bound. Kernel reachability is unestablished, not impossible. Rejection preserves
receiving counter/non-delivery, not the World. The suggested 128-packet staging bound is false: C `device.c:207–217`
trims old contents before excess GSO segments, and 1024 ring slots count batches, not all retained packets. Three
terminals are erasures, correcting the review's count of two.

**Effort.** Receive/time, staging, attempts and timer work used 17/10/4/4 builds, with 10/6/1/2 failures. Thirteen
replay attempts included syntax/record/jitter failures; all five final recipes passed in under nine seconds each. A
forbidden English token was corrected after gate rejection. A provider interruption left no job; dirty worktrees were
preserved before edits resumed. No cap was hit; review corrections are resolved.

**Ranked mirror suggestions.** None required. Existing signed clocks/operand records expose the semantics. A later
encryption-age guard would alter C control flow and is not altitude-preserving.

## R6 — cookie exclusion and retry-limit finding

**Historical source-only lifecycle discrepancy, repaired by main.** Since `c047e64`, IPv6 `table6` was
updated by receive but omitted from initialization and final GC. Linux walks both families. The proof-side
inspection reported this without an accepted Runner reproduction or differential finding. Main's representation
batch (`738caf0`, carried in `cb2348e`) now resets both tables and walks/clears both on final uninit; the current
proof carry follows that original source. This was not a Linux bug claim or a cookie-theorem premise. The campaign
made no mirror change.

**Original versus proved.** Under-load invalid-MAC2 exclusion has an original cookie-only theorem and full Noise frame
on normal completion. Literal `MAX_TIMER_HANDSHAKES` attempts is false: the accepted episode has nineteen retries,
twenty total initiations, MAX=18. C's strict `attempts > MAX` and `timers.c:49` MAX+2 reporting explain the
design/wording nuance, not a mirror/C discrepancy.

**Architecture.** [Six terminals](../Leanux/Proofs/WG/FloodResistance/Statements.lean) refine Cookies/Gate's original
receive factor. FailedMac2 contains actual load/ makeCookie execution, MAC1 equality and MAC2 mismatch against its
cookie. Seven branch records reach only reply, preserving Stops; invalid MAC1 takes five-record drop before
cookie/Noise. Load derives from depth≥512 or unexpired signed decay. Frames mask only secret/birthdate and TX stats,
retaining complete residents/identity/frontiers. Rotations, both families, refusal/socket errors and missing-record
Stops remain. This is local exclusion, not outer-worker or valid-MAC2 rate coverage.

**Accepted retry episode.** `r6-retransmit-limit` derives 23 operations from `d3_retransmit_gives_up`/initiation draws,
with coherent clocks/arm records, advancing TAI and disabled cache clocks. Original acceptance/JSON, stable peer, empty
keys, timer/counter/queues and new initiation bytes are checked. Callbacks 1–19 increment/send/rearm; callback19
compares `[18,18]`, callback20 `[19,18]` and gives up, purges staging, arms deferred zero. This is no capture/ kernel
schedule proof or universal bound through reset/rate/dead/allocation/socket alternatives.

`Logged/Advance` retains the original syscall/seccomp/task-work prefix, result, normal World and Stop. Recorded units
are observed; lifted placeholder execution has no unit-coverage claim. The same interface supports the coherent R5
witnesses.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r6-retransmit-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/FloodResistance/Replay.lean
```

[AGENT 2026-10-13] State exclusion over actual rejection executions and retain the literal retry counterexample; do not
substitute an unproved universal episode bound or promote generated records to measured schedules.

**Effort/review.** Cookie proofs used thirteen builds, ten failures; the load factor avoided broad expansion without
weakening the view. Retry/Advance used nine calls, four compile/assertion failures, including a corrected reply
endpoint. Final checks pass; all exits were collected without cap/interruption. Review corrections are resolved;
`66df779` records the review/tray carry.

**Ranked mirror suggestions.** None for the proved properties. Changing the retry comparison would alter C behavior and
is not altitude-preserving. The historical IPv6 lifecycle discrepancy was repaired and validated by main; this carry changes only proofs/docs.
