# WireGuard proof campaign

## Progress

Worktree `.worktrees/proofs-campaign`, branch `proofs/campaign`. The
[charter](2026-10-13-charter-proof-campaign.md) defines the campaign. Main
`57f8f34` (seccomp and the QEMU-default update) is carried into this branch
under the charter's non-prerequisite authorization. The mirror and kernel
match it exactly; all registered components are current. Subsequent main
`d65288d` adds the two named-prerequisite design documents only and is not
merged pending the user's landing paste. No integration into main, push,
differential check or guest run.

| Result | Progress |
| --- | --- |
| R1 anti-replay | Complete with the intentional inclusive-floor correction; recorded replay and independent review checked. Seccomp frame carry checked. |
| R2 lifetime safety | Store identities, failure-retaining allocation/release and caller composition cover session/rotation, peer creation, receive entry/maintenance/completion, callback-parametric receive polling, TX staging, decrypt iteration and ten socket/cache/loopback calls; stale-cursor finding checked. Actual stack callbacks, remaining callers, lifecycle and whole-run internal-access coverage remain in progress. |
| R3 cryptokey routing | Original prefix arithmetic and total longest-prefix lookup over represented trees, pure insertion, original empty-root, arbitrary-depth empty-child and exact-prefix insertion with sequence wrappers, and total original placement proved. Selected-root graft normal endpoints and rollback effects checked; successful graft representation, general mutation/history and path refinements remain open. Path proofs follow R2. |
| R4 delivery | Not started; drop characterisation waiting on W7 full-ring tier's explanation of the two drops. |
| R5 key lifetime | Not started; time half waiting on review items 7 and 8 on the timer model. |
| R6 flood resistance | Not started. |

**Current validation.** The full proof gate passes 214 build jobs and 158
terminal statements (ReplayWindow 15, R1 9, R2 107, R3 27), with only permitted
axioms. The default model build passes 60 jobs; the unit tier passes 93 tests
in 22.077 seconds with one skip. The R1 explicit-record witness was rechecked
at the seccomp carry; both R2 variants were rechecked with the exact-prefix
checkpoint. All agree with the original runner.
Independent reviews cover peer creation, the seccomp carry, mixed enqueue,
decrypt execution, keypair/packet releases, ambient caller composition,
allocation and release-bound composition, session creation and rotation,
the mixed peer-creation bridge, receive entry, maintenance, completion and polling,
TX staging, pure trie
insertion, original empty-root and arbitrary-depth empty-child insertion with
its wrapper, exact-prefix replacement, list deletion, placement and selected-root
graft endpoints/rollback, saved-peer scans and the ten-call socket family.

**Shared carry.** Signal/task and pipe helper frames, seccomp entry/tail frames
and arbitrary prefill preservation keep the seven-field WG projection intact.
The runner observers include the child fixture and prefill success/error paths;
no seccomp-free trace premise was added. The BPF converter proof shares compiler
continuations and proves progress of its integer pass counter before framing
the repeat loop. This carry took 17 compile passes over 36m34s; an independent
reviewer checked source correspondence and final deltas in two passes, and
another worker checked the loop architecture. That checkpoint also passed
`capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs`.

## R1 — anti-replay uniqueness and the inclusive floor

[AGENT 2026-10-13] Reuse the existing pure counter-window model, exact S2
refinement, finite mirror-call refinement and committed runner observer for
R1. Add arithmetic bounds in the reusable `WG/CounterWindow` layer and export
the result from `WG/AntiReplay/Statements.lean`. This keeps the new proof
obligation at the small replay-state projection.

The original wording excludes counters **at or below** highest seen minus
8128. The proved wording excludes counters **strictly below** that boundary;
an unseen counter at equality may be accepted. Both the mirror's strict
`ctrTooOld` comparison and Linux `receive.c:counter_validate` implement this
inclusive edge, and Linux's `selftest/counter.c` explicitly tests acceptance
of zero after counters 1 through `COUNTER_WINDOW_SIZE`. This is an intentional
design nuance, not a mirror/kernel disagreement. The arithmetic statement
uses the one-based stored high-water mark to avoid natural-number subtraction
at an empty window.

**Architecture and refinement.** `CounterWindow/Bounds` proves the arithmetic
guard and preserves the 128-word bitmap through finite calls. The existing
`mirrorCalls_refines` identifies those calls with `accepted` and `finish`,
including the exact projected final state. `Keypairs/Evolution/Bounds` adds
`FloorHistory`: every earlier accepted nonce is at most 8128 above every later
one in the same allocation lifetime. `Inv.remembers` supplies the old
high-water bound; the validator's acceptance guard supplies the new bound.
`Evolution.floor` composes this through lifecycle and validator transitions;
the outer runner proof carries the invariant through the already checked
observer. `runner_floor` discharges all syscall contracts. Together with
`runner_uniqueness`, it quantifies over every successful original execution,
including arbitrary accepted record schedules and slot reuse. No new observer
copies or history fields were added. Committed-call coverage and discarded
scheduler probes retain the independently reviewed ReplayWindow interpretation.

**Rule Zero boundary witness.** A six-operation trace configures and brings up
wg0, observes its initiation, injects the recorded response, then injects valid
keepalives with wire counters 8200 and 72. Both return true in allocation
lifetime 1. The second is exactly at `8200 − 8128`. The record stream is a
reconstruction from the tracked `CONTENDED_ROAM_CMP` capture, with the two
authenticated datagrams from `rx_window.json`, widened legacy section identities
and monotonically adjusted clocks for the second data operation. This is an
accepted **non-placeholder mirror replay**, not a new Linux capture. The
original and logged runners produce identical JSON. The terminal theorem
`inclusive_boundary_witness` separately proves, by kernel reduction, that the
pure empty-window run `[8129, 1, 0, 1]` accepts exactly `[8129, 1]`.

Reproduce the recorded replay without QEMU or retained dumps:

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r1-inclusive-floor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/Logged/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

**Validation and effort.** Current validation is recorded above. The initial
build failed because its dependency scan preceded the newly added root import;
a fresh build resolved that dependency. Five local compile passes
resolved proof syntax and elaboration issues. R1 took roughly fifteen elapsed
minutes with bounded worker investigation and proof implementation; replay itself
took under one second. No differential check or guest was run.

**Independent review.** A worker uninvolved in the R1 implementation reviewed
the proof/source correspondence and observer coverage in two read-only passes.
No correctness defect was found. Its two reporting requests are addressed
above: distinguish the pure and runner witness counters, and identify the
record stream as reconstructed rather than a fresh Linux capture. It did not
run the build or gate; those results are the coordinator's checks.

**Ranked mirror-shape recommendations.** None: the existing named validator,
replay-state projection and proof-side lifetime evolution already make R1
routine. An observer/history field or a changed comparison in the mirror
would not preserve altitude and is not proposed.

## R2 — lifetime identity and retained references (in progress)

**Architecture decisions [AGENT 2026-10-13].** Separate resolved allocation
identity from ownership of saved numeric references. Share frontier algebra
between stores, and frame unrelated operations once over the seven-field WG
kernel projection. Keep observation history outside the exception layer so
failed prefixes survive. Strengthen access safety separately with release
uniqueness and then allocation/epoch bounds; share caller proofs through
explicit ambient contracts instead of duplicating each invariant's proof.
Observe saved peer-map entries at the demanded predicate evaluation, retaining
the saved stamp and proving it remains resident; do not insert a new getter.

**Checked model and refinement.** `Lifetimes/Store` and `Actions` describe
slot/stamp transitions over original executions. `Keypairs/Identity` uses the
existing whole-syscall evolution to exclude reintroduction of absent old keypair
identities at operation endpoints. Peer and packet primitive contracts extend
that algebra; the packet primitive result is within one device epoch. These
endpoint results alone do not establish internal-access coverage.

`Logged/Prefix` preserves the exact original result, successful World or Stop
while retaining prior events on failure. `Focus` injects local suffixes into one
mixed peer/keypair/packet stream. Packet stamps include `(ifindex, id + 1)`.
`LifetimeEvent.Safe` excludes reads and writes after release of the same stamp.
Failed getters resolve no object and emit no access. `ReleaseInv` adds resident
uniqueness across each family, including both packet stores. `AllocationInv`
adds separate slot and lifetime frontiers, current packet-frontier bounds and
past-epoch bounds. Those premises supply allocator vacancy; all-input erasure
still reproduces malformed occupied-slot overwrites without calling them safe.
Every runner fixture initializes the invariant, and seccomp prefill preserves it.

The source-observed complete calls currently cover `peerCreate`, `peerGet`, `peerPut`, dump completion,
keypair creation/acquisition/release/clearing/rotation/session creation, TX/RX
allocation and free, optional-peer/index/public-key lookup, complete receive
enqueue and `consumeData`, packet decryption and one decrypt-worker
iteration. Twelve endpoint/cache, timer, queued-handshake and receive-key-refresh
calls also preserve safe prefixes; Boolean guard/modifier results are retained.
Seven complete TX staging calls cover CPU selection, peer/device enqueue,
`createData`, staged-packet purge/send and keepalive. Their `TxContracts`
companion retains cached identity predicates through scalar device updates,
with a concrete allocation-invariant instance; CPU and enqueue results remain
`Nat` and `Int`. `PrefixLoops` shares finite range and map composition.
`CounterAccess` observes the complete validator on all inputs, with no bitmap-size
premise. `AllowedLookupAccess` observes peer acquisition after the original node
search. `ReceiveCompletion` composes rotation, staging, maintenance, source lookup,
reference release and statistics; `ReceivePoll` adds the original queue traversal
and cleanup with an explicit observed callback. Its ambient and allocation
contracts require callback preservation; the actual stack remains a follow-on.
`SavedPeers` gives exact short-circuit scan events under an explicit saved-stamp
residency premise. `LoopbackAccess`, `SocketCache`, `SocketSend` and `SocketCalls`
cover ten complete cache/endpoint/loopback/tunnel/IPv6 calls. Their all-input
erasure retains results and Stops; generic safety has an explicit device-statistics
contract, instantiated for allocation bounds. A cache-miss clock failure retains
exactly its preceding peer read. Generic record-consumer frames live once in
`Framing/KernelEffects`, with older interfaces derived by projection.
Shared bind and finite-loop laws compose these per-call contracts. Generic enqueue/decrypt
contracts admit explicit observed softirq, IRQ-exit and rescheduling callbacks;
they are instantiated at the allocation invariant. Peer creation reuses its
existing observer unchanged, with original slot/metadata geometry transporting
the stronger invariant. `AllocationRetention` uses surviving entry residents
and explicit release origins to retain bounds through releases.

Exact event equations cover pending-worker and refcount failures, including
writes before zero-refcount rejection and releases only after successful final
puts. Conditional whole-call equations retain six events before session birthdate
clock failure, and allocation/write before peer initialization's first cache
clock failure. Receive queue-record failure retains exactly five accesses,
including the packet setter's nested read. These equations are not accepted-run
witnesses. Lookup preserves the first matching index's exit even if its kind is
wrong; receive entry preserves the ENOSPC Stop and EPIPE's pure callback.
Handshake-completion clock failure retains four accesses before the Stop.
The timer guard's nested peer getter is evaluated unconditionally before
`andM`; its observer preserves that elaborated order. Coverage is
checked against actual source calls; erasure or an unchanged-Kernel theorem
cannot certify that a lifted helper contains no reads. TX observations retain
the setter's read/write pair, both restoration getters and the nonce write
before rejection. Duplicate cleanup IDs remain admitted, including a later
Stop after an earlier free. The keepalive allocation-record failure equation
retains its initial peer read. Plain staged packet values have no resident
TX/RX store identity until `newTxSkb` runs. Shared filesystem frames
also end at return, leaving queued task work for its later caller proof.
The poll retains both `dropPeeked` getters, releases keypair then peer then RX
packet, and invokes its callback only after the final peer update. Its budget
and malformed-queue Stops remain in domain. An exact empty-bitmap failure equation
retains the validator's initial keypair read and no write; this is an original
getter-conditioned failure, not an accepted-trace finding. Safe access prefixes
do not establish delivery, order or reference ownership.

**Remaining claim.** Full caller, device-lifecycle and scheduler closure remain
unproved. The actual stack callback, encrypt/TX workers, IPv4 socket send/setup, handshake
execution and timer callbacks, peer removal, netlink and direct resident scans
need coverage. Saved scalar-reference
ownership is a separate obligation: aliased or dangling IDs may legitimately
stop after earlier safe accesses. No distinct-keypair-slot premise is hidden in
rotation or clearing. The stale cursor below does not resurrect the old stamp,
so it does not refute the endpoint identity theorem or settle charter R2.

**Concrete reference finding.** An eight-operation accepted mirror run creates
28 peers, starts a stepped dump, deletes wg0, creates a new wg0 and 27 replacement
peers, then receives a chunk. The dump retained slot 26, old identity 27, with
two references. Its continuation cleanup releases replacement identity 55,
which has one reference, removing it while the peer list and public-key table
still name slot 26. The received message is the already queued first chunk;
continuation generation performs the destructive release. Old identity 27 does
not return: this is reference retargeting and table incoherence.

The guest rejects deletion with a pending dump (`wg_delete_with_dump_pending`),
and the W1/W2 design requires that restriction. `Env.wgDelete` checks worker
idleness but omits the dump guard. C retains `ctx->wg`; the mirror resumes a
Boolean-held cursor against the current device. This is an accepted-mirror
domain bug, not evidence of a Linux lifetime bug. The explicit non-placeholder
records are synthetic, not a fresh capture. Five runner checkpoints, their count
and original JSON equality are checked. The kernel-reduced
`stale_cursor_retargets_replacement` separately exercises `wgGetDeviceDone`;
the full replay reaches the same bad put through dump-resume cleanup.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

A second accepted eight-operation variant gives replacement peer 26 an IPv4
`10.0.0.0/8` binding before the stale continuation releases it. The final
checkpoint follows the actual device root: that prefix still names slot 26,
while resident identity 55 is absent. It checks eight checkpoint emissions,
five specified projections and original-runner JSON equality. The records are
again synthetic and explicit. This rules out unconditional owner-residency
invariants; it neither resurrects identity 27 nor by itself demonstrates
packet misrouting or disagreement with insert/remove history. The original
witness is unchanged.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor-orphan |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/ReplayOrphan.lean
```

**Effort and review.** Each reproduction takes under one second. The main caller
checkpoints took roughly 6–25 minutes each, with 4–19 compile passes; TX
staging took fourteen passes over 24m44s: two passed and twelve failed before
correction. Receive completion/poll took fourteen passes over 23m50s: three
passed and eleven failed before correction, ending with the full 206-job build.
Saved scans and the ten-call socket checkpoint took twenty invocations over
about 43 minutes: three passed and seventeen failed before the final 214-job
build. IPv4 send erasure/safety attempts failed at proof-search heartbeat
limits; its unused observer was removed. It remains an open caller obligation,
with a second architecture prepared using explicit tail-call stages to retain
shared continuations. This is a proof failure, not a mirror finding.
Counts and failed
passes are retained in the checkpoint history; current validation is above.
Failures were proof elaboration/simplification failures, not passes or mirror
findings. One earlier tactic loop was stopped by its verified PID and repaired.
Independent source reviews cover every listed checkpoint and its final deltas.
They corrected scope wording and identified an unused impossible KDF-failure
premise; that vacuous lemma was deleted. The maintenance review also corrected
the draft no-device frame argument to `modifyDev`'s actual no-op behavior.
The TX review checked the seven callers against the mirror and C, and clarified
that the per-call contracts compose through existing laws without exporting a
new sequence runner. No remaining correctness finding is reported for the
checked components. The completion/poll review checked all-input source order
and callback scope; it moved a generic conditional law into `Logged/Prefix`
and narrowed a docstring to the safety theorem's actual conclusion.
The socket review corrected saved-stamp and cache-flag scope wording, checked
all ten calls and their six exports, and reconciled the shared frame and
conditional-law moves. Its frozen source hashes match the validated tree.
C initializes cache/handshake before its
peer-counter increment, whereas the mirror increments/inserts first: the proof
follows the mirror, without claiming a C simulation or a lifetime counterexample.

**Ranked mirror-shape recommendations.** (1) Restore the documented pending-dump
deletion rejection: altitude-preserving fixture-domain enforcement. (2) If that
domain is expanded, retain the actual device lifetime in the cursor as C does:
altitude-preserving, requiring separate validation. (3) Keep named allocation,
deletion and same-object update boundaries: altitude-preserving operational
structure. No production history field is proposed; mirror edits remain outside
this campaign.

## R3 — cryptokey routing (in progress)

**Architecture decisions [AGENT 2026-10-13].** Use width-parametric prefix
arithmetic, one inductive Patricia tree and one pure insertion algorithm.
Contexts describe structural paths without adding another executable algorithm.
Keep raw addresses and original allocation order. At original mutation boundaries,
require freshness throughout the node store, including unrelated entries and
the opposite address family.

**Checked model and refinement.** `Prefix` defines leading bits and branch
selection arithmetically. `ArithmeticMirror` refines original `commonBits`,
`prefixMatches` and `choose`, retaining their branch effects and entire Worlds.
`Tree.Valid` requires bounded addresses/CIDRs and local edge constraints. The
independent flat-list `Winner` specification selects a longest matching owned
prefix. Pure lookup satisfies it without compression or node-ID uniqueness.
Strict CIDR growth bounds height by width plus one.

`Store.RepAt` gives exact node values, children and backlinks, allowing unrelated
store entries. `LookupMirror` proves that original `findNode` terminates normally,
returns the pure answer and preserves the Kernel; the actual 130-iteration bound
is discharged rather than assumed. Original `nodePlacement` likewise terminates
and yields an exact or stopped context, preserving the source's ordered exits
and allowing exact matches on ownerless nodes. External root linkage remains an
explicit caller obligation, not part of `RepAt`.

`Insertion` preserves validity/compression, replaces exactly the requested
canonical-prefix owner and accounts for all old/new node IDs by permutation.
The first fresh ID names the requested node; a needed ownerless intermediate
gets the second. Exact overwrite retains the old ID and raw address. Lookup
agrees with the independently updated flat binding list.

`MutationMirror` refines original empty-root insertion. `ChildMutation` and
`ChildStore` handle the root's immediate empty child; `DeepChild` and
`DeepChildStore` extend that case to arbitrary represented depth. Context
replacement requires the local root ID to remain fixed. Initial whole-tree
`Nodup` separates the changed parent from retained ancestors/siblings, while
`NodesBelow` protects them from fresh allocation. Exact source-stage contracts
compose allocation, peer-list append and connection; original traversal derives
the placement premise. The resulting state represents the existing pure
insertion, retains validity/unique IDs and links to the actual device root.
Original lookup from that root satisfies the updated flat-list `Winner`.

These mutation contracts distinguish normal allocation refusal from success;
arbitrary bad records may still Stop. `add` refusal preserves the Kernel.
The original `insert` wrapper advances the sequence once before either normal
outcome, including refusal. Exact equations preserve opposite root values and
any supplied opposite-family representation; existing opposite-root linkage
is preserved, not inferred. The statements describe exact endpoint states,
not mutation-event order. Peer-list append is exact without yet proving list
coherence or ownership.

`ListsMirror` gives the total original `listDel` endpoint as the source's
saved-peer fold, with pointwise filtered lists and unchanged identities and
allocation metadata. `ExactMutation` and `ExactStore` handle exact-prefix
replacement at arbitrary represented depth. They preserve the old node ID,
unmasked address and structure, allocate nothing, and append once to the
post-filter target list. They require representation and unique node IDs, but
no old-owner liveness or coherent peer-list premise. Total original `add`,
actual-root lookup and `insert` sequence advancement refine the same pure
insertion. This remains an endpoint refinement, not a resident-access observer.

`GraftMirror` stages the original selected-root nonempty graft; `GraftStore`
derives placement from the represented input and classifies every normal return.
It distinguishes first allocation refusal, second refusal with exact source
rollback, and the one-node/two-node success endpoints. The `insert` wrapper
retains its sequence increment in each case. Rollback advances the node frontier
once, restores node lookups under whole-store freshness, and filters that ID
from every resident peer list. It preserves any supplied tree representation;
whole-device equality and peer-list freshness are not assumed. Bad records may
Stop: these are normal-return endpoint contracts, not failed-prefix observers
or reachability claims for all alternatives.

**Remaining claim.** Successful nonempty-graft representation, post-success
freshness and lookup, deeper grafts, removal and general configuration histories
remain open. Parsed-input
bounds and history invariants still need propagation through all mutations.
Both packet paths follow R2. Owners are raw peer slots, not allocation or
cryptographic identities; no liveness/ownership claim follows from tree lookup.
The R2 orphan-owner replay above is a constraint on any proposed ownership
invariant, not yet an R3 counterexample. No R3 statement has been reshaped
and no Rule Zero finding is claimed.

**Effort and review.** Arithmetic, pure-tree and original traversal work took
5, 6 and 20 compile passes; pure insertion took 13. Empty-root insertion took
12 passes over 11m44s. Placement took 21 over about thirty minutes, including a
failed monolithic child-insertion attempt. Its staged replacement closed in
19 passes over eighteen minutes; that proof failure was not a mirror finding.
Arbitrary-depth insertion plus its wrapper took eight capped builds over 11m49s:
five passed, three failed during ordinary proof development, with no cap hits.
Exact-prefix replacement and list deletion took 21 capped builds over about
eighteen minutes: seven passed and fourteen proof iterations failed before
correction; the final full build passed 195 jobs. Selected-root graft endpoints
and rollback took 40 capped invocations over 35m28s: six passed and 34 failed
during proof compilation, with no cap hits; the final full build passed 208
jobs. Independent review corrected a draft `freeNode` contract that omitted
node residency, and wording that confused normal-return classification with
reachability. Successful graft refinement remains a follow-on, with no semantic
obstruction identified. Independent reviews checked each layer
and final terminal scopes; no correctness finding remains. Reporting corrections
separated root values from linkage, endpoint equations from event order, and
successful Worlds from failing Stops. Current validation is above; reproduce
with `capped -- scripts/in-bundle scripts/proof-gate`.

**Ranked mirror-shape recommendations.** None from these components. The named
arithmetic helpers and integer address encoding admit refinement without
production changes; correspondence to C byte layout remains informal.
