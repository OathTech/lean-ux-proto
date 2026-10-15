# WireGuard proof campaign

## Progress

Work on `proofs/campaign` in `.worktrees/proofs-campaign` follows [the charter](2026-10-13-charter-proof-campaign.md),
with representation batch `cb2348e` carried and validated. All seven rows are current there, including the local R4
packet-to-receipt link extension, local R3 owner-acquisition material frame and initialized R4 linkage.
The session/decrypt source injection is validated with the original caller, audit and R4 contracts preserved.
The local RX reference-transfer/discharge extension passes coordinated validation.
The full staged-send/consume callback protection contracts pass coordinated validation.
Session/material/RX-origin receipts and local support
are retained; initialized R3 packet authorization
and R4 receive-pipeline conservation remain open. The [register](proofs.md#results) holds pins/counts; the
[model map](proofs.md#layers) supplies refinement details. No main integration, push, differential check or guest run
was made by this campaign.

| Result | Disposition |
| --- | --- |
| R1 | Replay uniqueness proved; inclusive-floor correction witnessed. |
| R2 | Initialized allocation-identity access safety proved, including failures/trials; affiliation/credits separate. |
| R3 | Parsed initialized routing histories, local lookup/affiliation cuts and actual session/RX-origin receipts; initialized packet binding open. |
| R4 | Initialized entry/completion uniqueness and packet/receipt linkage; chronology refuted; receive-pipeline conservation open. |
| R5 | Accepted age/post-zero/wire-nonce counterexamples; thirteen positive local contracts. |
| R6 | Cookie exclusion proved; literal MAX=18 refuted, without a replacement universal bound. |

**Current R4 callback protection (validated).** Two grouped exports
preserve all 506 prior terminal bodies: 508 declarations (506 theorems/two definitions; 132 R3/125 R4).
[Protection frames](../Leanux/Proofs/WG/Queues/RxProtectionFrames.lean),
[TX handoffs](../Leanux/Proofs/WG/Queues/TxRxProtection.lean) and
[consume protection](../Leanux/Proofs/WG/Queues/RxConsumeProtection.lean) cover full original
sendStagedPackets and consumeDataDone on normal return. Actual acquisition, TX allocation, disposal,
publication and queued-handshake paths derive typed queue-append/reference deltas. The same supplied RX
Inventory, QueueOwners and Protected ledger survives, including its explicit reservations and new durable
charges. Staging assumes nullable current-key compatibility; consume needs only its packet key's nullable,
receiving-validity-independent compatibility. Actual promotion and timer frames establish the staging cut.

The exact balance is endpoint accounting, not TX packet ownership, send-pending/work correspondence or
an output key-compatibility frame. Generic unfunded Handoff equations admit ghost loans; independent review
identified this and the funded transport/resident-owner consequences now supply the contextual meaning.
No reservation is inferred from spare refcount. Stops retain their source behavior without a returned World.
Whole consumeData admission, arbitrary IRQ/Stack callbacks, surviving poll-caller credits and initialized
carrier conservation remain open. The earlier `00c204d` material-retention checkpoint remains validated;
its normal-only nullable-owner/support contracts do not imply initialized R3 origin.

**Current effort.** Acceptance 14:49:10 UTC; initial 90 minutes/48 capped calls, final 20 minutes/10 calls reserved.
[AGENT 2026-10-15] The coordinator extended this same six-path tranche by 40 minutes/24 calls to finish
actual callback composition; total 130 minutes/72 calls, reserve 16:39:10 or call 62, deadline 16:59:10.
Scoped call 49 passes 428 jobs; full call 50 passes 508, collected 16:12:04 UTC (82m54s after acceptance).
Fifty builds comprise twelve PASS and thirty-eight ordinary FAIL. Failures include source-factor/WP
normalization, tuple/record projections, private-helper and result-type errors. Call 20's rejected Kernel-indexed
representation produced recovery warnings and two kernel declaration-has-metavariables errors; it was reverted.
Calls 17/38 displayed recovery placeholders. Call 45 exhausted the default simp-step bound. No source admission
or raised limit remains: all final proofs use defaults. The initial write/build shell lacked fail-closed chaining;
the write succeeded, but this was a process-rule failure, reported and corrected for subsequent commands.
No interruption, infrastructure retry or cap failure occurred. Lake scheduling uses command-local threads 32,
QEMU slots 16 and the unchanged 32G cap; existing per-compiler -j1 is unchanged. All owned jobs are collected.
The final worker ledger is 52 capped calls: fifty builds (12 PASS/38 ordinary FAIL) and two passing exact checks.
Exact 51 preserves all 506 prior bodies, 508 total/132 R3/125 R4, the six-path scope, imports/tokens/EOF,
whitespace, mirror/pins and empty index; exact 52 reconciles only final review/ledger metadata and the six hashes.
Independent source/export/docs review is clear: the staging pass was 15:59:22–16:01:35 UTC and final continuation
16:11:09–16:15:28. The earlier unfunded-loan finding is fixed by funded transport and resident-owner consequences;
no unresolved finding remains. Worker ownership ended at 16:16:15 UTC (87m05s); final metadata review
reconciled at 16:16:27. Coordinated validation passes: 508-job/508-declaration permitted-axiom gate,
fresh kernel replay collected at 16:19:41 after gate compilation, default build (60 jobs), and 103 unit
tests (21.919s, one skip). The exact checks retain all four frozen Lean hashes and every prior terminal body.
The full per-call ledger belongs in the checkpoint commit, not this short report.

**Current foundations.** The persistent RX journal records actual session/decrypt source cuts and preserves
unconditional original erasure, the same full incoming R2 audit/probes and the established R4 boundary,
completion, receipt-validity and linkage meanings. Local receipt validity requires a valid incoming journal.
Actual ingress admission injection, initialized material/configured identity, earlier routing alignment and
copied-trial origin receipts remain open.

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
material-retaining operations `00c204d`. Their commits retain measured
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

## R3 — cryptokey routing (in progress)

**Original versus proved.** [Terminal contracts](../Leanux/Proofs/WG/CryptokeyRouting/Statements.lean) establish
trie/configuration refinement and parsed initialized completion history, not full RX/TX identity binding. Public parsing
supplies address shape required for failed-history validity and normal endpoint agreement. Unconditional erasure covers
all typed traces/both placeholder settings. No R3 Rule Zero counterexample is asserted.

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
hierarchy was introduced. Initialized session-to-later-key allocation matching, peer public-key provenance, packet transport to
poll/Stack, copied trials and initialized identity closure remain open. A snapshot or raw peer winner does not settle them.

**Local material retention.** [Origins/State](../Leanux/Proofs/WG/Origins/State.lean) supports every resident valid
receiving key with one full successful session witness and its keep-or-clear owner; invalid keys require no support.
[Origins/SessionMaterial](../Leanux/Proofs/WG/Origins/SessionMaterial.lean) proves actual front installation/tail
retention and the combined local session/decrypt adapters. Its strict journal-order conclusion uses the supplied
entry support, not an initialized-history provenance theorem. Normal Some-front facts recover the complete entry peer;
decrypt retains the actual stored packet, material and AEAD transformation, without equating packet.peer to that peer.
[Origins/IndexMaterial](../Leanux/Proofs/WG/Origins/IndexMaterial.lean) derives the concrete owner-acquisition and
index-lookup frame, including nullable store-back, and reuses the existing access adapter for supplied support.
The new `RetainingLeaves`, `RetainingTraffic` and `RetainingLifecycle` source contracts extend normal
material retention through concrete non-installing traffic, timers and lifecycle operations. They reuse actual
record getters and stronger canonical masks, with no affiliation/residency/credit or successful-drain premise.
Whole-admission and stateful material-support propagation, plus initialized provenance, remain unfinished.

**Actual caller injection.** [ReceiptTypes](../Leanux/Proofs/WG/Origins/ReceiptTypes.lean) keeps existing qualified
receipt/context names while removing the import cycle. [HandshakeSources](../Leanux/Proofs/WG/Origins/HandshakeSources.lean)
has exact original and lifetime-observer factors for response, after-MAC, reception and captured-ring receiveStep.
[HistoryAdapters](../Leanux/Proofs/WG/Origins/HistoryAdapters.lean) focuses actual session/decrypt runs once into the
existing RX history. The decryptStep prepare cut and both activation/whole receive-worker entrances are wired to it;
normal tail/decrement and Stop bypass order remain original. All prior audit/probe history survives projection.
Old metadata decoders erase session/RX receipts; the linkage decoder retains lifetime access events. Its concrete
Protocol instances preserve the existing R4 predicates. Copied scheduler trials retain their isolated R2 observer;
this extension does not claim their session/decrypt receipts. Available admission receipt types do not mean ingress
admission has been injected. Local validity and source linkage do not establish initialized material support.

**Remaining obligations.** Initialized syscall/Runner composition preserves ordinary-negative cleanup and Stops; parser
shape follows the operation cursor. Local entry agreement still needs connection to earlier actual initialized lookup
history. Historical session/key/public-key ownership and packet origin, initialized RX/TX identity binding and
copied-trial packet certificates remain open. Nullable compatibility is insufficient for historical key identity.
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

## R4 — queue, poll and delivery-order components (in progress)

**Original versus proved.** The charter requires accepted-schedule order and no silent loss/duplication.
[Terminals](../Leanux/Proofs/WG/DeliveryOrder/Statements.lean) prove initialized committed callback-entry stamp
uniqueness for every typed Trace and both placeholder settings, including Stops. Chronological GRO order is false. Local/persistent
polls and every initialized Runner normal return pair entries with actual normal Stack returns. Failed histories
retain valid receipts and at most one trailing unfinished entry; joint conservation remains open.

**Local reference protection.** [Carrier state](../Leanux/Proofs/WG/Queues/RxCarrierState.lean),
[ingress cuts](../Leanux/Proofs/WG/Queues/RxIngressProtection.lean) and
[cleanup cuts](../Leanux/Proofs/WG/Queues/RxCleanupProtection.lean) now prove source-acquired loans, fresh allocation
transfer, pure-IRQ repayment, actual queued/selected/paid/free transitions and the successful ENOSPC suffix.
All ledgers are explicit local inputs. Remaining positive demand derives non-retirement; no RetainsRx or retrospective
slack premise substitutes for it. The poll suffix uses its caller pid under the actual earlier packet-peer guard.
Key payment must have returned; key-credit funding is not asserted. The new full staged-send and consumeDataDone
contracts preserve that same RX ledger under nullable operational owner compatibility, with exact typed TX/send-work
handoffs. They derive rather than assume strict acquisition/repayment balance and preserve separate key/slot facts
through promotion and timers. Whole consumeData admission, arbitrary Stack/IRQ callbacks, surviving poll-caller and
base/work/dump reservations, ring/carrier correspondence and initialized protection remain open. No output compatibility
or TX ownership is inferred from the reference delta.

Independent architecture review identified a source-level arbitrary-World countermodel to framing all consumeDataDone
by RX credits alone: P owns a selected credit plus reservation at count two, but its next key belongs to Q; staging
acquires Q and dead-create cleanup pays P, reducing P below demand. This is not an accepted Runner counterexample.
The local consume theorem now uses exactly such operational packet-key compatibility; whole-poll closure still needs
retention and reply-triggered TX compatibility, not cryptographic unforgeability. Paid-phase history and allocation freshness remain separate proof obligations, not inferred from the
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
full receipts and the exact R2/probe history, but does not identify poll-local segments. Key/session/public-key identity,
admission credits and carrier conservation remain open.

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

**Remaining obligations.** Affiliation/credits, worker-local ownership and RX
conservation, including relevant TX callbacks. Stores/rings/queues/locals/GRO overlap; counts cannot be added. Named
rejection, validation, keepalive, purge/free and handoff dispositions still need initialized admission-to-carrier composition
beyond the proved local post-removal partition. Queue idleness does not empty
stores/peer queues; finite prefixes retain pending obligations. W7 item/mark transport remains open.

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
The remaining initialized conservation obligations are stated above.

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
