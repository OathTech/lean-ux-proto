# WireGuard proof campaign

## Progress

Work on `proofs/campaign` in `.worktrees/proofs-campaign` follows [the charter](2026-10-13-charter-proof-campaign.md),
over unchanged mirror `de62c9d`. Local R3 lookup/address/source cuts compile; initialized R3 packet authorization
and R4 receive-pipeline conservation remain open. The [register](proofs.md#results) holds pins/counts; the
[model map](proofs.md#layers) supplies refinement details. No main integration, push, differential check or guest run
was made by this campaign.

| Result | Disposition |
| --- | --- |
| R1 | Replay uniqueness proved; inclusive-floor correction witnessed. |
| R2 | Initialized allocation-identity access safety proved, including failures/trials; affiliation/credits separate. |
| R3 | Parsed initialized routing histories, local nullable affiliation and actual lookup/handoff cuts; initialized packet binding open. |
| R4 | Initialized entry uniqueness and callback completion; chronology refuted; receive-pipeline conservation open. |
| R5 | Accepted age/post-zero/wire-nonce counterexamples; thirteen positive local contracts. |
| R6 | Cookie exclusion proved; literal MAX=18 refuted, without a replacement universal bound. |

**Validation.** Initialized R4 callback-completion propagation passes scoped/full builds (337/483 jobs), the
487-declaration permitted-axiom gate, fresh stock kernel replay, the 60-job default build and 124 tests
(24.017s, one skip). Independent frozen review and exact source checks pass. Current source has 487 declarations
(485 theorems/two definitions; 122 R3/114 R4), retaining all 485 preceding terminal bodies. The preceding `ce12402`
R3 source-cut checkpoint passed scoped/full builds (401/480 jobs), the 485-declaration permitted-axiom gate,
fresh stock kernel replay, the 60-job default build and 124 tests (22.976s, one skip). Baseline `1a5542d` passed the
same checks for local callback completion (483 declarations). `bcbf733`'s first coordinator exact script failed
with SyntaxError before checks; the regenerated script passed.

Carry `a0cf252` passed eleven recipes: nine accepted agreements and two pending-dump rejections with accepted
pre-delete boundaries. Those Runner recipes were not rerun: their observers are unchanged. No differential/guest run
was made. Historical ledgers: `6010243`, `bcbf733` and Lean 4.35 carry `b1ec9e8`.

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

**Owner-word carry.** `de62c9d` embeds the optional word in its handshake/keypair. Low-level `IndexOwnerAccess` observes
owner read, acquisition and fresh setter getter/write, including NULL store-back, without inventing a pointed-peer
getter. Initialization observes its new read/write. Masks preserve actual stores; the index mask omits only the scalar
table.

Put events depend on immediate-unreference and the optional word: immediate NULL Stops before decrement; non-immediate
count-one/NULL writes zero, rereads and Stops before erasure. Neither emits release. Zero-count cases retain the earlier
NULL Stop versus decrement-first warning. These arbitrary-World equations are not initialized counterexamples; the
lifecycle note's unreachable-arm assertion is not a premise.

[AGENT 2026-10-15] Preserve initialized R2/R4 domains and same-history projections, generalizing creation to include
None. `a0cf252` enumerates ten local repairs to put/failure events, allocation and owner-based families; all 477
names/other 467 bodies survive. The session getter follows existing premises; Logged/TX/RX/time copies retain actual
observations. `RxBorrow.KeyRef` remains local. Review corrected the mistakenly some-only routing creation conjunct.

**Effort/trust.** Carry outcomes/timings remain in `a0cf252`. Earlier builds failed with recovery sorry terms, rejected
metavariables or dependent unknown constants; these were failures, not admissions or passes. Corrected source passed
gates. Narrow cuts replaced broad searches. R2 reused its established local two-million-heartbeat Runner limit;
ineffective earlier R3 limit escalation was replaced by a default-limit proof. No global/cap changes or inferred
campaign total.

[AGENT 2026-10-14] Condense historical validation into checkpoint references. Command-local `LEAN_NUM_THREADS=32`
schedules Lake; per-Lean `-j1` remains. Infrastructure reruns are limited to one; ordinary failures are not
infrastructure. [AGENT 2026-10-14] Use command-scoped Codex attribution. `e7b0273` mistakenly inherited default Git
identity; subsequent commits correct attribution without global changes or ancestry rewriting. Snapshot-rule violations
remain under R4.

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

## R3 — cryptokey routing (in progress)

**Original versus proved.** [Terminal contracts](../Leanux/Proofs/WG/CryptokeyRouting/Statements.lean) establish
trie/configuration refinement and parsed initialized completion history, not full RX/TX identity binding. Public parsing
supplies address shape required for failed-history validity and normal endpoint agreement. Unconditional erasure covers
all typed traces/both flags. No R3 Rule Zero counterexample is asserted.

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

**Remaining obligations.** Initialized syscall/Runner composition preserves ordinary-negative cleanup and Stops; parser
shape follows the operation cursor. Local entry agreement still needs connection to earlier actual initialized lookup
history. Historical session/key/public-key ownership and packet origin, initialized RX/TX identity binding and
copied-trial packet certificates remain open. Nullable compatibility is insufficient for historical key identity.
Partial failing clear has no completion marker. The historical R2 orphan recipe is now rejected, not a current
misrouting witness; no new accepted counterexample is claimed.

**Effort/review.** Earlier failures remain in checkpoint commits. A denied /tmp
diagnostic was unavailable; planning interruptions were snapshotted, no R3 build interrupted. Prior rejected
metavariables/unknown constants/recovery diagnostics are retained in those ledgers. The affiliation tranche used 28 capped calls, 26 builds
(7 PASS/19 FAIL), two exact checks PASS; full result 04:25:43, 28m58s after acceptance, handback 04:35:08. Call 6 had
three kernel application-type mismatches; calls 2/10 rejected recovery goals; call 16 reported `declaration uses sorry`
during failed elaboration. No source admission; corrected builds are clean. No limit/cap/interruption/rerun. Review
corrected creation overstatement, snapshot/execution wording and a missing TX parent-source factor. Frozen review
04:29:36–04:33:40 is clear after correcting blanket-validation wording; metadata reconciliation 04:34:47–04:34:51 is
clear.

**Source-cut effort/review.** Lease 05:28:00, measured acceptance 05:28:32 UTC; scoped PASS collected by 06:00:22.
Full PASS was collected by 06:02:30; exact PASS by 06:03:27. Final worker ledger: 26 capped calls,
25 builds (5 PASS/20 ordinary FAIL), one exact check PASS. Call 7 reported recovery `declaration uses sorry` after
ambiguous andM; calls 22/23 had tactic syntax failures and downstream kernel unknown-constant diagnostics. No source
admission, limit/cap change, interruption or infrastructure rerun. Review required explicit RX input/output protocol
linkage; corrected before scoped PASS. Exact check 26 verifies all six paths, 483 byte-identical prior terminal bodies, 485 total/122 R3, tokens/imports,
whitespace/EOF, empty index and mirror pin. Independent frozen review 05:57:08–06:08:11 found no defect; it retains
the normal-zero TX boundary, raw RX peer identity and outstanding caller composition. Root gate, fresh replay,
default build and units passed on their first calls. Root's source/scope/body/token/import checks passed, but its
final register selector incorrectly included the separate claim table and failed; the corrected remaining pin check
passed for all seven rows. This was a check-script defect, not an infrastructure retry. No source changed after the
worker's successful builds; subsequent edits only reconcile report/register metadata.

**Ranked mirror suggestions.** None. Integer-address refinement needs no production restructure; C byte-layout
correspondence remains informal.

## R4 — queue, poll and delivery-order components (in progress)

**Original versus proved.** The charter requires accepted-schedule order and no silent loss/duplication.
[Terminals](../Leanux/Proofs/WG/DeliveryOrder/Statements.lean) prove initialized committed callback-entry stamp
uniqueness for every typed Trace and both flags, including Stops. Chronological GRO order is false. Local/persistent
polls and every initialized Runner normal return pair entries with actual normal Stack returns. Failed histories
retain valid receipts and at most one trailing unfinished entry; joint conservation remains open.

**Architecture.** Refinement chain:

| Layer | Abstraction/refinement |
| --- | --- |
| RingGeometry/Steps, journals/occurrences, RX/TX source journals | Stale physical slots/live FIFO, finite occurrence conservation and original installed mutations; Stop prefixes separate from endpoints. |
| PrevQueue/RxQueueView, poll/GRO tags/provenance | Cached peek, deletion-permitting cell frames and exact bytes/origins; selected order, not chronology. |
| [Joint projection](../Leanux/Proofs/WG/Queues/RxPollJointProjection.lean), stamp phase/support/history | Same execution's original/GRO/lifetime correspondence, actual read support, uniqueness and normal release. |
| [Callback completion](../Leanux/Proofs/WG/Queues/RxPollCompletion.lean) | Ordered entry/normal-return pairs; failed prefixes retain at most one unfinished entry. |
| Concrete caller spine, [Runner history](../Leanux/Proofs/WG/Queues/RxRunnerHistory.lean), [completion](../Leanux/Proofs/WG/Queues/RxCompletionRunner.lean) | Same-history full R2 audit, isolated trials, actual returned Worlds, initialized entry uniqueness and return pairing. |
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
concrete caller/Runner hierarchy. Every typed Trace and both flags derive the protocol from the empty history,
without parser/allocation/progress premises. Normal return matches all entries; Stops retain valid receipts and at most
one trailing unfinished callback. Completed stamps inherit existing entry uniqueness. Only new local suffixes are
promoted at the same seed; isolated trials remain outside committed pairing. No new operational hierarchy or stronger
BoundaryInv is introduced. Stack return does not prove inbox/reply success or whole-pipeline conservation.

**Source-comment finding.** Independent review (2026-10-15 01:35:32–01:40:05) found `PeerRemove.lean:30,110–122` relying
in prose on `requireNotPending`, actually `State.lean:102`'s `pure ()`. Later inspection found the same in
`Send.lean:17–20,56`, plus obsolete single-item queue scope at `:22–24`. Mirror comments remain untouched; they prove no
quiescence. No accepted loss/ duplication witness was found: arbitrary last-peer erasure is not initialized, and the
poll's last-put candidate Stops at a later getter. No kernel bug claim.

**Remaining obligations.** Affiliation/credits, worker-local ownership and RX
conservation, including relevant TX callbacks. Stores/rings/queues/locals/GRO overlap; counts cannot be added. Named
rejection, validation, keepalive, purge/free and handoff dispositions need proof. Queue idleness does not empty
stores/peer queues; finite prefixes retain pending obligations. W7 item/mark transport remains open.

**Effort/process/review.** Current propagation grant 06:11:24, acceptance 06:12:04. The first Env build failed on
an unqualified batch type and broad tactic searches reaching the existing 200k heartbeat limit; rejected elaboration
printed `declaration uses sorry`. Explicit constructor proofs repaired it without source admission or raised limits.
The existing Runner observer is reused, and its history-only completion proof closes at the default limit.
Full result collected 06:25:19 (13m15s after acceptance): seven capped builds, six PASS and one ordinary FAIL.
A metadata edit script separately failed ValueError on a stale heading; it was repaired before the next build.
The eighth capped call passed exact scope/count/body checks at 06:26:16; ownership returned at 06:27:23.
Independent frozen review 06:23:53–06:27:59 found no defect. Root gate, fresh replay, default build, units and
exact checks all passed on their first calls, preserving all 485 prior terminal bodies and seven current pins.
No cap, interruption, infrastructure rerun or source change after successful builds occurred; final edits only
reconcile validation metadata.
Earlier R4 ledgers are in `00fafa4`, `57cb46e`, `c4ef635`, `ec95fa8`, `3dec2c3`, `79dce53`, `1b76322`,
`983f84b`. Earlier joint-poll failures 16/23 printed recovery sorry terms; call 20 hit the existing two-million-heartbeat
limit; corrected source passed gates. Receipt work: grant 04:47:00, acceptance 04:47:40, full-build result collected
05:16:10 (28m30s), handback 05:18:34. Eleven worker builds had four passes/seven ordinary failures; its exact check
passed. Coordinator gate, fresh replay, default build and units passed. These are collected effort times, not compile durations.
Call 03 printed two `declaration uses sorry` recovery warnings and rejected a kernel declaration with metavariables
after namespace/elaboration errors. Corrected builds are clean; no source admission, limit/cap change or interruption.

Runner work used fifteen calls/29m04s to full success, including interrupted FAIL130. An unnecessary duplicate build
followed a failed edit script and was deliberately interrupted; a corrective edit then occurred **before preservation**,
violating the standing rule. Root stopped work and snapshotted six dirty worktrees under
`refs/snapshots/proof-campaign-r4-runner-duplicate-20261015T021102Z/`; campaign
`d5336546034e925211a891d88720e913f971c091` matched the dirty tree, branches/indices untouched. No build intervened;
resumption followed release. Passing validation does not erase this process failure.

The initial ring writer separately resumed after deliberate termination without snapshot; work stopped and all six dirty
worktrees were preserved before resuming. Completion-worker interruptions were preserved. These were not ordinary
compile failures; no R4 memory cap was hit. Symbolic algebra replaced large reduction. Reviews required direct
provenance, qualified EPIPE-at-return/failed-entry claims, corrected uniqueness/ownership/ifindex/scope/census wording
and noted that immediate repayment appends steps, not hidden records. Findings are dispositioned.

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

Seven-operation `r5-coherent-post-clear` moves that second expiry to 673s. Zero expiry is 132+540=672s; zero and real
clear work precede crypt. All published key slots are empty, index absent and handshake zero, while the same packet
keeps one reference to the same material. Ciphertext precedes queued handshake work; transmission frees packet and final
key reference. Older five-operation `r5-post-clear-transport` deliberately has incoherent coarse/jiffies clocks and
disabled arm records; the coherent witness does not upgrade that evidence.

Both coherent variants check monotone clocks, arm records, exact delays and `J(t)=2^32-75000+250*t`; kind-310/site-128
windows end at 323/674s. TAI follows elapsed coarse time, queue/timer identities remain stable and cache clocks are
disabled. Complete original advance agreement includes Kernel, decisions, endpoint, jiffies and record exhaustion.
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

**Source-only lifecycle discrepancy.** Since `c047e64`, `ratelimiterAllow` creates/updates IPv6 `table6`, but
`ratelimiterInit` resets only `table` and `gcEntries false` walks/clears only IPv4 while reporting no IPv6 entries.
Local Linux `ratelimiter.c:55–83,205–221` walks both families, clears all entries on last uninit and allocates empty
tables on reinit. The mirror therefore appears to retain IPv6 rate state across last uninit/reinit. This source
comparison arose during R2 lifecycle work; **no accepted Runner reproduction or differential finding is established**.
It is neither a Linux bug claim nor a cookie-theorem premise. The mirror remains unchanged. Follow-up should exercise
IPv6 cookie admission, device deletion/recreation and admission from the same source /64.

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
is not altitude-preserving. The IPv6 lifecycle discrepancy needs its own reproduction/validation, not a proof-driven
edit.
