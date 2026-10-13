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
| R2 lifetime safety | Keypair operation endpoints, peer allocation/reference helpers, packet primitives, failure-retaining peer creation/release, mixed receive-enqueue/decrypt iteration, keypair/packet release families, and complete keypair/TX/RX allocation with fixture initialization, plus stale-cursor finding checked; caller/lifecycle and whole-run internal-access coverage remain in progress. |
| R3 cryptokey routing | Original prefix arithmetic and total longest-prefix lookup over represented trees, pure insertion, original empty-root insertion and total original placement proved; general mutation/history and path refinements remain open. Path proofs follow R2. |
| R4 delivery | Not started; drop characterisation waiting on W7 full-ring tier's explanation of the two drops. |
| R5 key lifetime | Not started; time half waiting on review items 7 and 8 on the timer model. |
| R6 flood resistance | Not started. |

**Current validation.** The full proof gate passes 172 build jobs and 103
terminal statements (ReplayWindow 15, R1 9, R2 64, R3 15), with only permitted
axioms. The default model build passes 60 jobs; the unit tier passes 93 tests
in 22.566 seconds with one skip. Both explicit-record witness replays below
were rechecked at the seccomp carry and agree with the original runner.
Independent reviews cover peer creation, the seccomp carry, mixed enqueue,
decrypt execution, keypair/packet releases, ambient caller composition,
allocation, pure trie insertion, and original empty-root insertion and placement.

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

[AGENT 2026-10-13] Separate store identity from retained-reference provenance.
Absence of a released allocation does not establish that a saved numeric slot
still denotes the allocation whose reference was acquired. Keep both obligations
visible; a finding about the latter does not settle the former.

**Architecture and checked scope.** `Keypairs/Identity` derives allocation
frontier monotonicity, old-identity provenance, absence preservation and fresh
reuse from the existing `Evolution`. ReplayWindow's S3 discharges its contracts
for original syscalls and their ambient step. A later successful getter cannot
return an already absent, previously allocated identity. These are operation
endpoint statements, not safety of every internal access.

`Lifetimes/Store` abstracts slots and allocation stamps. `Transition` preserves
old-identity provenance; `Retained` permits only removal. `Actions` composes
contracts over actual original executions. `Peers/Primitives` covers lookup and
reference helpers; its raw setter contract requires the replacement's stamp to
match the current resident. `Peers/Frames` carries that correspondence through
initialization. `Peers/Allocation` proves the complete original `peerCreate`:
an ordinary error result leaves the identity store unchanged; success advances
the frontier once and inserts the fresh stamp. It does not assume an empty
`nextPeer` slot in arbitrary malformed Worlds. Finite helper sequences include
creation and get-unless-zero and preserve boundedness and old-identity absence.

`Packets/Primitives` gives exact runs for all eight TX/RX allocation, lookup,
update and free helpers. Its invariant bounds stored ids by `nextSkb`. Following
an actual free, no successful primitive sequence can make a getter at that slot
succeed. This covers one device epoch and does not assume TX/RX disjointness;
post-free exclusion uses same-slot emptiness.

[AGENT 2026-10-13] Share allocation-frontier algebra and projection contracts
between stores; retain the fixed-device packet scope until lifecycle closure.
Raw skb numbers alone do not identify allocations across device replacement.

`Framing/Projection`, `WGKernel` and `FSFileRefs` prove six original file-reference
helpers once over the seven dedicated WG kernel fields, then derive keypair,
peer and packet contracts by projection. These frames end at successful return:
`fput` can queue task work whose later effects require separate proof. The
remaining filesystem hierarchy has not yet been migrated. `KernelEffects`
now shares the hidden-allocation/clock and four refcount contracts; `Kernel`
frames 42 original helpers over the full WG view. All 277 theorem signatures
in the four affected legacy modules are unchanged projection interfaces.
Shared loop/map tooling and private-name references have no dependency back
into that legacy hierarchy. These contracts likewise prove endpoint equality,
not internal-access coverage.

[AGENT 2026-10-13] Share filesystem preservation over the full WG kernel view
rather than duplicate its operational proof hierarchy for each lifetime view.

**Internal access prefixes.** `Logged/Prefix` puts observations outside the
exception layer: failure retains events already made, while erasure returns the
exact original error or successful value and World. `Lifetimes/Events` forbids a
read or write after release of the same allocation stamp. `Peers/Access`
observes the original `peerPut` at both getters (including `requireNotPending`),
the setter and the inline store erasure; `wgGetDeviceDone` uses that observer.
The exact event equation covers every input: a pending-worker rejection retains
one read, a zero refcount retains two reads and the write before rejection, and
a successful last-reference release has read/read/write/release. Failed getters
resolve no object and emit no access event.

The release-only exports give exact result/log equality and safety of every
prefix of finite sequences of those two complete original calls, including
failures. Their invariant states safe past history, unique resident stamps and
absence of previously released stamps; it does not assert future safety.

`Peers/CreationAccess` adds the complete original `peerCreate`, observing its
first insertion as allocation/write and every getter/setter in destination-cache
reset, handshake-clock reset, static-key precomputation and handshake
initialization. `PrefixEnsures` carries result-dependent contracts through
failures. The stronger invariant bounds resident and previously released stamps
by the allocation frontier, so an arbitrary initial history cannot label a future
allocation as already released. Five terminal exports cover exact erasure, core
allocation observations, an initializer record-failure prefix, and finite sequences
of creation, put and dump completion. The failure-prefix theorem concerns the
helper after core creation, not a whole-runner counterexample. Ordinary create
errors and `Stop` failures retain their actual effects and observations.

These contracts do not require an empty `nextPeer` slot: a malformed occupied
slot can be overwritten without an old-object release event. They prove ordered
resolved-stamp accesses, not vacancy, complete release coverage or ownership of
a saved raw slot reference. The stale-cursor finding below can satisfy them.
Whole-run coverage, dump-resume cleanup, other callers and device lifecycle remain
open.

**Mixed receive enqueue.** `Logged/Focus` injects only a local observer's new
suffix, preserving prior interleaving. `Lifetimes/Tagged` uses a sum of complete
peer/keypair/packet event families; packet stamps are `(device ifindex, id + 1)`.
`MixedAccess` and `MixedFrames` give exact getter/setter observations and preserve
the other families' identity views. `Acquire` records the original `peerGet`:
no resolved access on lookup failure, one read before pending-worker rejection,
two reads before refcount rejection, and two reads plus a write on success.

`Enqueue` observes the complete original `enqueuePerPeerRx`. Its proof retains
the cached peer's identity through the RX update and checks the peer write
before the interrupt callback. Afterward, `peerPut` uses fresh getters; the
callback need only preserve the mixed invariant, not the entire identity view.
Five terminal exports cover all-input erasure, callback-parameterized safety,
the no-op specialization, exact acquisition events and a keypair-lookup failure
retaining the preceding packet read. The last is a helper failure equation,
not an accepted-trace counterexample.

The mixed invariant requires safe histories and absence of released identities,
plus the peer uniqueness needed for release. It does not establish packet/keypair
allocation freshness or uniqueness. Concrete callback coverage, device lifecycle,
scheduler closure and retained-reference ownership remain open. In particular,
`mixed_lift` is an endpoint frame; every concrete use must also be checked for
unobserved internal accesses. The independent review checked those uses in this
helper and its exact source-call order.

**Decrypt execution.** `KeypairAccess` proves the mixed setter contract from
equality with the current resident stamp. `Decrypt` observes the original
`decryptPacket`, including its second keypair read before a rejection update.
The lifted clock, allocation and branch helpers contain no lifetime-store
accesses. An exact failure equation retains the first keypair read if the
rejection expression fails; it is a helper equation, not a new trace finding.
`DecryptWorker` observes the complete original step and iteration, with softirq,
IRQ-exit and rescheduling callbacks in source order. `Logged/PrefixWorkers`
shares the generic iteration composition. Callback contracts require safe
appended histories and the mixed invariant on success, permitting identity
changes. Five terminals export packet and iteration erasure/preservation plus
the failure equation. Concrete callbacks and whole scheduler closure remain open.

**Keypair and packet releases.** `ReleaseInvariant` adds keypair and packet
resident uniqueness to the mixed invariant. Packet uniqueness spans both TX and
RX slots. `KeypairRelease` observes every original `keypairGet` and `keypairPut`
access, with all-input event equations. A zero-count put reads and writes before
its refcount error, without a release; a count of one releases after the write.
`PacketRelease` records the successful getter before each TX/RX free. A failed
getter records neither access nor release. Raw erase leaves require current
residency to interpret their release labels; the complete callers establish it.

`ReleaseCalls` follows the complete next→previous→current `keypairsClear` caller,
including both peer getters and its setter in each round. Its five-constructor
family composes acquisition, put, both packet frees and clear, retaining safe
histories on every outcome and the invariant on successful return. Repeated
keypair references need no distinctness premise: a later dangling lookup stops
with its earlier events retained. Seven terminals export the finite-family
contracts and exact helper equations. Allocation freshness, device lifecycle,
concrete callbacks and whole-run closure remain open.

[AGENT 2026-10-13] Carry release uniqueness through the existing `MixedSpec`
identity-predicate parameter in a separate `ReleaseInv`. Getters and same-stamp
updates need less than release, so existing enqueue/decrypt callback contracts
retain their weaker invariant; no additional generic framing mechanism is needed.

**Release-aware caller composition.** `Ambient` separates a history-dependent
invariant from the temporary identity predicates used for cached getter results.
Its contracts cover the actual getter/setter, peer-reference and access-free
kernel actions used by enqueue and decrypt. The decrypt queue update has its
own explicit preservation premise: identity-view equality alone cannot preserve
an arbitrary allocation or release-history invariant. `ReleaseAmbient`
instantiates these contracts with `ReleaseInv`; two terminal exports compose
enqueue and decrypt iteration with callbacks at that stronger invariant. The
original observer definitions, erasure proofs and weaker `MixedInv` terminal
contracts are unchanged. Concrete callbacks, allocation and scheduler closure
remain open.

[AGENT 2026-10-13] Generalize the enqueue/decrypt preservation bodies once over
explicit ambient primitive contracts, then instantiate release uniqueness. The
earlier separate `ReleaseInv` remains sufficient for primitive release proofs;
caller composition additionally needs callbacks to receive that stronger
invariant. A callback requiring uniqueness cannot be supplied through a contract
that assumes only `MixedInv`.

**Allocation and initial state.** `AllocationInvariant` adds separate slot
and lifetime frontiers to `ReleaseInv`, including peer creation bounds and
released-history bounds. Peer/keypair slot bounds and the shared TX/RX packet
frontier imply all four destination slots are vacant. Packet identities retain
the device epoch; current-epoch released stamps are bounded by `nextSkb`, and
all released epochs precede `netIfindexNext`.

`KeypairAllocation` factors the complete original creation into the hidden
allocation choice and its exact insertion core. `PacketAllocation` shares one
proof between the original TX/RX helpers. Both record allocation followed by
initialization write, preserve safe prefixes and the stronger invariant, and
have all-input erasure and event equations. Failed creation and normal keypair
allocation refusal retain the incoming history exactly. Emitting these events
at successful return is valid because the exact source equations show no
possible failure or further object access between insertion and return. Unlike
peer creation, these helpers have no fallible post-insertion initialization.
Malformed occupied-slot worlds are still reproduced by the equations; those
equations do not certify release coverage for an overwritten old object.
Safety separately assumes the invariant that excludes occupied destinations.

`AllocationFrames` separates identity equality, a small metadata projection and
transport of released-history sets. Its access contract permits a conditional
frame, needed for raw setters whose same-stamp premise comes from a getter.
`AllocationInitial` establishes the invariant for every original runner fixture
and preserves it through successful seccomp prefill. Eight terminals expose the
allocator contracts, vacancy and fixture initialization. An allocation-aware
ambient instance, release-family composition, concrete callers and device
lifecycle remain open.

[AGENT 2026-10-13] Keep allocation safety in a separate stronger invariant with
both slot and stamp frontiers, rather than strengthening existing access-only
interfaces. Track packet epoch and per-device frontier independently so later
device creation can distinguish old released identities from new slots.

**Concrete reference finding.** An eight-operation, explicit-record accepted
mirror run creates 28 peers, starts a stepped dump, deletes wg0, creates a new
wg0 and 27 replacement peers, then receives a chunk. The receive returns the
already queued first chunk; its continuation generation performs the destructive
release. The dump retained slot 26, old identity 27, with two references. Device
deletion leaves the cursor active. Replacement slot 26 has identity 55 and one
reference; resumed cleanup calls `peerPut` on it, removing its store entry while
the configured peer list and public-key table still name slot 26. Old identity
27 does not return. This is reference retargeting and table incoherence, not
reading a released old object.

The guest rejects deletion with a pending dump (`wg_delete_with_dump_pending`),
and the W1/W2 design calls for the mirror to do likewise. `Env.wgDelete` checks
worker idleness but not the dump. Linux retains `ctx->wg`; the mirror retains a
Boolean and resumes against the current device. This is an accepted-mirror
domain bug, not evidence of a Linux lifetime bug. No kernel experiment was run.

`Logged/Checkpoints` observes one projection after each original operation,
including ambient processing and guards; erasure preserves the complete JSON or
indexed error, and a separate theorem proves exact singleton append. The replay
checks five relevant checkpoints, their total count and original JSON equality.
Its records are synthetic, explicit and non-placeholder, not a Linux capture.
The terminal `stale_cursor_retargets_replacement` is a separate kernel-reduced
witness of the actual `wgGetDeviceDone` callback. The full replay reaches the
same bad `peerPut` through `wgGetDeviceDump` resume cleanup; these are distinct
call sites.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

**Validation and effort.** Current validation is recorded above. The recorded
replay accepts and checks its assertions in under one second. Earlier checkpoint
commits carry their own counts. No mirror semantics or kernel source changed.

Most effort is caller coverage and reusable framing. Peer allocation took six
compile passes, shared file frames four, failure-prefix observation nine,
the shared kernel-frame migration three, and peer creation ten over about
twenty-one minutes. Mixed receive enqueue took nineteen compile passes over
about twenty-five minutes. Decrypt execution took ten compile passes over
fourteen minutes and twenty-two seconds. The release checkpoint took thirteen
compile passes over fifteen minutes and twenty-three seconds. One full build
failed after a proof-script simplification cleanup; explicit rewrites repaired
it, and the next full build passed. The ambient generalization took four
compile passes over six minutes: three passed, and one predicate-shape
elaboration failure was repaired before the full 167-job build. Allocation
took eighteen compile passes over twenty minutes and thirty-one seconds;
projection and elaboration failures were repaired before two passing full
172-job builds.
Failed passes exposed proof elaboration or simplification errors. One earlier
anonymous-hypothesis tactic loop was stopped by verified PID and repaired.
Independent read-only reviews found no correctness defect in these components;
their scope corrections and allocation-history requirement are incorporated
above. Coverage is checked against source calls, not inferred from erasure.
The decrypt review corrected one wording issue: the setter's same-stamp premise
does not establish raw-reference provenance. Its final review also checked the
new failure equation and terminal scopes. The release review checked exact source
accesses, failing prefixes, packet epochs, the clear caller and all seven exports;
it found no defect. Its raw erase-leaf interpretation caveat is documented above.
A final proof-script cleanup delta was independently reread. The ambient review
checked primitive contracts, source order, failed prefixes, both stronger
exports and unchanged weaker APIs; it found no correctness or scope defect.
The allocation review checked all five modules and eight exports. Its one
wording finding was fixed: packet allocation increments the frontier while
preserving allocation bounds. No correctness or source-coverage finding remains.

One source-order limitation remains: C `peer.c` initializes destination cache
and handshake before incrementing `peer_counter`; the mirror increments and
inserts before those helpers. The allocation theorem follows the mirror. This
is a C-correspondence limitation, not an accepted-trace lifetime counterexample
or a C-simulation claim.

**Ranked mirror-shape recommendations.** (1) Restore the documented rejection
of deletion with a pending dump: altitude-preserving fixture-domain enforcement.
(2) If that domain is intentionally expanded, retain the actual device lifetime
in the cursor, following C: altitude-preserving, requiring separate mirror
validation. (3) Keep named allocation, deletion and same-object field-update
boundaries: altitude-preserving operational structure that reduces framing.
No production history field is proposed. All mirror changes are outside this
campaign's edit authority.

## R3 — cryptokey routing (in progress)

[AGENT 2026-10-13] Prove width-parametric prefix arithmetic before constructing
an inductive Patricia tree and its representation in the original node store.
The independent trie half can proceed while R2 caller coverage is in progress.

**Checked arithmetic component.** `WG/AllowedIps/Prefix` models a prefix by
integer division and the following branch bit by quotient parity. Its 23
lemmas establish highest-set-bit bounds, the IPv6 high/low split, prefix
nesting and opposite branches at the common prefix of distinct addresses.
`ArithmeticMirror` proves exact execution equations for the original
`commonBits`, `prefixMatches` and `choose`, including every branch record and
the entire resulting World. The three terminal statements export maximal
common-prefix length, equality-based matching, and the next branch bit.
Address bounds and CIDR bounds are explicit representation premises; no trie
invariant or history theorem has yet discharged them for all runner inputs.

**Checked pure-tree component.** `AllowedIps/Tree` retains node labels, unmasked
addresses, CIDRs and optional owners. Its independent flat-list `Winner`
specification says that the result is a matching owned prefix with maximal
CIDR, or that none matches. `Valid` requires only bounded node addresses/CIDRs
and local edges: a child has a longer prefix, extends its parent and has the
appropriate branch bit. Structural induction proves `lookup_spec`, canonical
prefix-key uniqueness and unique-winner characterization. Compression and
node-ID uniqueness are not premises of lookup correctness. Strict CIDR growth
also proves height at most width plus one; IPv6 leaves room within 130
iterations for every node and an empty-cursor check. The three new terminals
explicitly describe this intermediate model, not the original traversal.

**Original traversal.** `Store.RepAt` records exact reachable node values,
children and parent backlinks, permitting unrelated store entries. It contains
no lookup premise. `LookupMirror` proves total correctness of the original
`findNode`, with exceptions forbidden: every represented valid IPv4/IPv6 tree
and bounded query returns the pure longest-prefix answer normally and preserves
the whole Kernel. Its loop invariant keeps the current subtree, earlier best
match and actual remaining-range budget. Strict height decrease rules out
exhaustion of the 130-iteration loop. The action retains its branch effects in
the returned World; the export does not separately characterize those records.

**Remaining claim.** The traversal starts at the represented tree's root;
general mutation histories must establish device-root linkage and preservation
by insertion/removal. Configuration-history agreement and both packet paths
remain open. Owners are raw peer slots,
not cryptographic identities or allocation stamps. Peer liveness and reference
ownership are not asserted. No R3 statement has been reshaped and no Rule Zero
finding is claimed here.

**Pure insertion.** `Insertion` adds one recursive Patricia insertion algorithm,
using a local graft at stopped placement. It preserves local validity and
compression and replaces exactly the requested canonical prefix's owner.
Lookup agrees with the independently specified flat binding list after that
replacement. Exact-prefix overwrite retains the old node ID and unmasked
address. A new owned node receives the first fresh ID; when needed, the
ownerless intermediate receives the second. A permutation theorem accounts
for every old and new node ID, deriving uniqueness and the advanced frontier
from explicit initial uniqueness and freshness premises. These are pure-tree
results: general original `add`, peer lists, backlinks, allocation failure and
history refinement remain open. In particular, freshness within this tree does not
imply freshness throughout the node store, which may also hold the other
address-family tree and unrelated entries.

[AGENT 2026-10-13] Keep the insertion algorithm singular; recursive structural
evidence describes it without introducing a second executable tree model.
Preserve raw addresses and allocation order for later original-store refinement.

**Original empty-root insertion.** `StoreMutation` supplies lookup-based
representation framing and `NodesBelow`, which bounds every stored node ID by
the allocation frontier. `MutationMirror` proves original allocation, list-tail
and root-connection contracts, then normal-execution equations for `add` and
`insert` on an empty selected root. Successful insertion installs exactly the
pure leaf, appends its ID to the existing target peer, and connects its backlink
to the chosen root. The exact Kernel equation retains allocation's initial
root4 backlink write and connection's subsequent write, including for IPv6.
Normal `add` allocation refusal preserves the Kernel; `insert` increments the
sequence number before either outcome. Missing or malformed records may still
produce `Stop`; normal completion is not asserted for arbitrary record streams.

The two terminal exports establish the new root's linkage and valid represented
tree and preserve both the opposite root value and any supplied opposite-family
tree representation. They preserve a caller's existing opposite-root linkage;
they do not derive that linkage without a premise. Whole-store freshness protects
unrelated entries as well as the opposite family. General nonempty insertion,
intermediate-allocation rollback, removal, owner liveness and history remain open.

[AGENT 2026-10-13] Require whole-store node freshness at the original mutation
boundary: freshness only within the selected tree cannot protect other stored
nodes from allocation overwrite.

**Original placement.** `Context` records a hole along the request's path,
with strictly shorter matching ancestors and their selected bits. `PlacementEnd`
keeps the original exit order: empty focus, CIDR too long, prefix mismatch, then
exact match after updating the parent. Exactness includes ownerless nodes.
`PlacementMirror` proves total original `nodePlacement` using the represented
subtree and its height against the actual remaining loop range. Its false
exception post rules out dangling getters, invalid selectors and exhaustion.

Three exports connect this traversal to insertion: the exact flag agrees with
zero pure allocations; a nonexact result identifies the structurally graftable
focus and its reconstructed insertion; and a known empty focus determines the
precise returned parent. These calls start at the supplied tree's root. `RepAt`
does not itself establish that a device root field or external slot points there;
an `add` caller still needs that linkage. No second executable placement
algorithm was introduced.

The optional proof of insertion at an empty immediate child **failed** to close
its repeated getter and Kernel-state equality goals and was removed. It establishes
no new mutation case and supplies no Rule Zero finding. The next attempt will
compose exact allocation, peer-list, getter and child-connection contracts in
smaller stages. The checked empty-focus traversal lemma is retained.

**Validation and effort.** The arithmetic took five compile passes, the pure
tree six, and the store/traversal refinement twenty over about eighteen minutes.
Pure insertion took thirteen build invocations over about sixteen and a half
minutes, including its targeted and full builds.
The original empty-root bridge took twelve capped builds over eleven minutes
and forty-four seconds, including seven corrected compile failures.
Placement took twenty-one capped builds over about thirty minutes: five passed
and sixteen failed during proof development, including the failed optional
mutation attempt. The final full proof build passed.
Failed passes exposed proof elaboration or simplification errors. Current
validation is recorded above. Reproduce with
`capped -- scripts/in-bundle scripts/proof-gate`.

**Independent review.** Read-only reviews found no correctness defect in the
arithmetic, pure tree or total original traversal. The arithmetic retains exact
World effects and IPv6 branch order. The traversal derives normal completion
rather than assuming it, and its representation supplies actual node/data/child
coherence and node widths. Bounds still need propagation from parsed inputs
through original mutations. Compression and globally unique node identifiers
are not required by lookup; pure insertion preserves them from explicit
premises, without yet establishing reachability. Owner labels need not denote live peers.
Correspondence to C byte layout remains informal: this is not a C simulation.
A separate read-only insertion review checked the successful structural cases,
canonical-prefix replacement, exact fresh-ID permutation and final terminal
scope, finding no defect. Its whole-store freshness obligation is retained
above; it did not run builds or the gate.
A separate read-only review checked the original empty-root helper, wrapper and
terminal contracts, including the normal-error sequence update and IPv6 backlink.
It found no mathematical defect and corrected one wording issue: the opposite
root value and supplied representation are preserved separately; their initial
linkage is not derived by the theorem.
The placement review checked source condition order, totality, context/insertion
correspondence, empty-focus uniqueness and the three final exports, finding no
defect. It retained the same external-root linkage obligation for later mutation.

**Ranked mirror-shape recommendations.** None from this component. The current
named arithmetic helpers and integer address encoding admit exact refinement
without production changes.
