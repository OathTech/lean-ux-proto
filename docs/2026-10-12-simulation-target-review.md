# Is lean-ux-proto's mirror a suitable simulation target?

Assessment, 2026-10-12. **Verdict: suitable with named changes.** The basic
altitude is right. The trie, file tables, handshake body and timer callbacks
provide useful operational targets for per-function C proofs. The current
whole-system runner is not yet a satisfactory target for a compositional
simulation covering single-CPU WireGuard. Some restrictions are ordinary proof
preconditions; others substitute fixture facts for kernel computation or erase
state that determines later C branches. Those require changes, not stronger
assertions about the existing tests.

**[AGENT, 2026-10-12] Assessment recommendation:** retain the thin-layer design;
repair queue state/identity, suspended execution, lifecycle composition and the
oracle boundary before extending the affected mirror paths. This is a proposed
direction, not an approved implementation plan or a change to standing rules.

## Scope and evidence

This review is of `6903c69c8324fcd8dc329192d2ea124d0564ccd5`, on
`task/review-sim-target` in `.worktrees/review-sim-target`. It does not assess
unmerged work in `w2`, `w7p2` or `wgen`. The charter authorizes only this report;
there are no mirror, harness, kernel or working-practice changes.

Repository references below are paths and line numbers at that commit. `Linux`
means the local source under `/home/dev/projects/lean-ux-proto/.deps/linux`,
Linux 6.12.110 as pinned by `dependencies/sources.lock.json:3–6`. `cerberus-sl`
means the read-only neighboring repository, observed at
`ab11fb5fbd1131b53e62d4b7433de5b9353d47a3`. Line references to those two trees
refer to the inspected local sources, not to a claim that their entire build
chains have been verified.

The starting requirements are `AGENTS.md`, the data/control-flow rules in
`docs/2026-09-29-way-forward.md:129–189`, the adopted conventions in
`docs/2026-10-06-future-proof-paths.md`, and the choice-stream, dispatch-order
and interface documents dated October 3 and October 11. The assessment includes
a structural survey of the four function classes and detailed examination of
the three requested samples and their dependencies. It is not an exhaustive
audit of every mirrored function.

No builds, tests, differential checks or QEMU guests were run. Findings are
source comparisons and proof-design analysis. In particular, counterexamples
below are source-level constructions, not reports of newly observed guest
failures. The project's three gates remain useful operational checks; passing
them does not supply the representation, ownership or interference arguments
described here.

## 1. What the proposed proof actually needs

A separation-logic triple can carry a mirror value as a logical parameter and
relate it to owned C memory. It need not embed C byte-level semantics in Leanux.
The useful granularity is a C function or a lock-protected region, with local
invariants between its choice points. Several C stores can correspond to one
mirror update, provided their temporary state is described and no intervening
observer can distinguish it. Equality of every field after every C instruction
is unnecessary; reconstructing the function's decisions from its return value
would be too weak.

The relation needs five distinguishable components:

1. **Live objects and ownership.** An embedding from mirror identities to C
   allocation/provenance-bearing pointers, injective on live objects; field
   projections, list/ring membership, and ownership of each allocation once.
   Alias edges do not own a second copy of the allocation.
2. **Execution and lifetime.** Current activations and locals, queued versus
   running work, references held by packets/work/timers, locks/BH state, and
   retired objects awaiting RCU reclamation. These matter even on one CPU.
3. **Environment services.** Contracts for allocation, clocks, randomness,
   routing, crypto, copies, synchronization and stack entry/re-entry. Each
   contract names its state footprint and any callbacks it can run.
4. **Oracle history.** Which source reads have occurred, their values, and the
   remaining tape. A valid tape witnesses an actual admissible C execution;
   arbitrary bytes are not automatically a possible kernel execution.
5. **Observations.** Return values, transmitted bytes, counters and the intended
   control-flow trace. Instrumentation metadata may be ghost state, but a
   choice that changes execution cannot be erased as logging.

These components can be projections of the existing `World`; a large physical
record split is not required to start. The important separation is contractual.
`World` currently mixes all five (`Leanux/Kernel/Defs.lean:951–1116`), and some
of its ostensibly environmental fields are kernel state.

The proof must cover each admitted concrete execution with the corresponding
mirror execution, including error returns and repeated calls. A statement only
about runs where the mirror happens to return successfully would leave all
`unsupported` and fuel failures outside its conclusion. That restricted result
can be useful, but does not establish the project's complete single-CPU target.
Admission conditions must describe C states, inputs and schedules independently
of whether replay succeeds, and remain valid across composed operations.

### Fit to cerberus-sl

The requested style is a good fit to the host's procedure contracts and local
label invariants: `cerberus-sl/docs/INTERFACE.md:323–328` and
`CerberusSL/CerberusSL/Triple.lean:30–56`. Its existing mirror representation
work uses identity-to-pointer embeddings and ownership precisely in the needed
way. In particular, `CerberusRefined/CerberusRefinedMixed/MirrorRep.lean:107–142`
requires injectivity on the live store, allowing allocation and address reuse.
Leanux's keyed node, peer and keypair stores are compatible with this approach.

There is nevertheless a substantial **proof-host gap**, independent of the
mirror's altitude. The documented adequacy is for a certified sequential
fragment, not current Linux concurrency, atomics, stored function pointers,
external I/O or all GNU C constructs (`cerberus-sl/docs/INTERFACE.md:41–67,
707–715`). The kernel uses those facilities. One CPU with `PREEMPT_NONE` and
Tiny RCU (`kernel/config-x86_64-net-choice:110–130,258`) still has interrupts,
softirqs, sleeping calls and scheduling points.

An initial body proof can assume suitably specified primitives and exclusive
ownership while the body runs. Linking such proofs to actual kernel executions
also needs a justified scheduler/interrupt and synchronization semantics, or a
proved reduction to sequential regions. Unsupported frontend features need
semantics or explicit abstraction contracts. This cannot be obtained by merely
calling each worker a sequential function. Nor is a bare guarded triple over
uncertified Core sufficient; the host explicitly warns about that distinction
(`cerberus-sl/docs/INTERFACE.md:345–359`).

The host's delivered-result `malloc` specification also cannot be reused
unchanged for Linux allocators returning `NULL`: its current OOM allowance is a
different outcome (`cerberus-sl/docs/INTERFACE.md:52–59`). Linux allocator
contracts must preserve the error branches the mirror already models.

## 2. Altitude by function class

| Class | What is already a useful simulation target | Where the correspondence stops being local |
| --- | --- | --- |
| Syscall and request handlers | File descriptor reservation, table expansion and pointer installation are distinct operations, with the C choices in order (`Leanux/FS/File.lean:96–164,183–193`). Pipe head/tail are real wrapping `UInt32` positions (`Leanux/FS/Pipe.lean:48–60`). Allowed-IPs insertion follows the trie algorithm, including failed split allocation and cleanup (`Leanux/WG/AllowedIps.lean:115–184`). | User-copy success and nonblocking/no-wait domains need explicit preconditions: eventfd has a counter update before the copy-out fault point, with that fault fixed false on the fixture (`Leanux/FS/EventfdOps.lean:70–115`). Environment transmit setup precomputes GSO segments before the mirrored C helper call (`Leanux/Env/IpStack.lean:169–188`; `Leanux/WG/Device.lean:281–315`). These are not general syscall specifications as they stand. |
| Workers | Handshake send preserves the rate test, state changes, crypto calls, MAC, timer actions, send and final reference drop (`Leanux/WG/Handshake.lean:458–478`). Encrypt/decrypt workers retain the consumption and packet-processing loops (`Leanux/WG/Data.lean:104–132`; `Leanux/WG/RxData.lean:96–116`). | Device rings are logical lists, shared skbs are duplicated values, and execution may run a suspended worker's remainder early (`Leanux/WG/Send.lean:101–141`; `Leanux/WG/Receive.lean:312–348`; `Leanux/Env/Batch.lean:29–56`). Those lose state or order needed by the body proof. The receive load-decay branch is replaced by a fixture assumption (`Leanux/WG/Receive.lean:222–240`). |
| Timer callbacks | Callback bodies closely follow their C counterparts: retransmit/give-up, keepalive re-arm, new handshake, clear-work enqueue and persistent keepalive (`Leanux/WG/Timers.lean:27–79`; Linux `drivers/net/wireguard/timers.c:41–142`). Pending state is cleared before dispatch (`Leanux/Env.lean:337–366`). | The scheduler admits only selected callback placements (`Leanux/Env.lean:379–407`), and arm-time reconstruction adopts the recorded expiry with a one-tick consistency rule (`Leanux/WG/State.lean:65–88`). Cancellation, due-time/wrap semantics and callbacks during waits need external contracts; the body alone does not establish them. |
| Lifecycle | Setup, stop, peer removal and destruct preserve much of the call skeleton and error handling (`Leanux/WG/Device.lean:79–103,172–275`; `Leanux/WG/PeerRemove.lean:100–144`). Refcounts and keypair/peer stores are explicit. | Delete requires an idle crypt/NAPI state; two crypt flushes and NAPI shutdown are comments under that restriction (`Leanux/Env.lean:564–570`; `Leanux/WG/PeerRemove.lean:105–118`). RCU retirement is immediate erasure from live stores. Dispatch address maps survive owner destruction. Ratelimiter teardown assumes empty tables even though receive can populate them. These prevent unrestricted lifecycle composition. |

The answer is therefore not uniformly yes or no. Much of the synchronous core
can support per-function simulation without recovering control flow from
outputs. The principal obstructions are retained state and composition between
those functions, with a few genuine branch substitutions inside them.

Some helper summaries are sensible cuts. For example, public-key lookup uses a
logical search rather than exposing the hashtable's entire bucket traversal
(`Leanux/WG/Peer.lean:207–212`). Such a summary can have a C helper contract;
it cannot simultaneously count as a per-comparison mirror of that traversal.
The boundary of the claim should say which of these is intended.

## 3. Environment boundary: promising structure, impure contracts

### 3.1 Recorded source reads are the right idea

`hidden` checks the expected source site, byte length and padding and consumes
the tape in order (`Leanux/Kernel/Defs.lean:1277–1316`). `branch` and
`branchCmp` return computed outcomes and append observations; they do not
normally take branch outcomes from the oracle (`:1226–1235`). Random ephemeral
keys, timestamps and allocation outcomes are legitimate parameters. Queue and
dispatch records that identify the actual work object are a substantial
improvement over assuming FIFO execution across peers (`:1355–1387`). Current
`Batch.condResched` does resolve the recorded tx-worker identity
(`Leanux/Env/Batch.lean:126–133`); older descriptions of that omission do not
describe this baseline.

The missing ingredient is an explicit admissibility contract. A clock result
must come from that clock at that execution point; an allocation outcome must
come with fresh ownership on success; a dispatch must refer to a queued live
unit and transfer its execution/reference resources. The tape is a witness to
those effects, not a replacement for their specification. Returning observed
data is sound as an abstraction only when its source and effects are related
to C independently of the desired mirror outcome.

There are also several execution modes. Placeholder reads synthesize values;
unarmed exact allocation sites and `laxZero` sites answer success
(`Leanux/Kernel/Defs.lean:1282–1304,1499–1513`); `harnessEnv` answers true
(`Leanux/Runner.lean:730`). A proof must name the mode and its success/no-read
assumptions. It must not claim that every nondeterministic input was captured
merely because the run had a hidden tape.

### 3.2 Cuts need effects, not just permission to discard records

`skipCutSites` consumes any leading run of listed sites, rejecting observed
failed allocation cuts; `allocCuts` is the global collection of every
below-cut allocation site (`Leanux/Kernel/Defs.lean:1405–1456`). This is a useful
replay mechanism, but not yet a local C contract. Passing the whole collection
to unrelated operations obscures which callee could have produced the reads.
`skipAmbient` can also consume ambient events and deferred worker stops at many
places (`:1263–1274`).

For each named cut a proof needs: inputs/results, owned memory it may change,
allocation/free/retirement effects, lock and callback effects, and which source
reads belong to its execution. Skipped values must either be irrelevant to the
retained state or represented by a specified summarized effect. A compact
description beside each helper is enough to establish the intended boundary;
no new certificate format or large gate is warranted.

Not all skipped records are semantically irrelevant even now. The transmit
error path uses the presence of an `icmpCredit` record to choose a loopback
NET_RX action (`Leanux/WG/Device.lean:291–300`). That is a contracted event with
a state effect, not an erasable random draw. Similarly, `hidden` itself clears
`pendingWork` on section entry (`Leanux/Kernel/Defs.lean:1312–1315`). Move such
execution effects into named scheduler/service operations; keep the tape
decoder responsible for decoding and advancing the tape.

### 3.3 IP/stack models can be parameters, with re-entry made explicit

Constructing fixture input packets in `Env/IpStack.lean` is appropriate.
`checksumHelp` is a good example of a helper summary with a concrete result and
explicit unsupported cases (`Leanux/Env/IpStack.lean:200–217`). Its C proof can
sit below the WireGuard proof. A source-address placeholder is tolerable only
while a relation establishes that the unknown bytes are not observed; a later
guard alone does not establish that fact (`:105–129,211–212`).

GSO is less clean: `xmitPackets` supplies already segmented packets and
`wgXmit` reconstructs the GSO choice from their count, then asks whether the
segmentation call succeeds (`Leanux/Env/IpStack.lean:169–188`;
`Leanux/WG/Device.lean:281–315`). This admits a helper-level abstraction, but
requires a relation to the original super-skb and a separation between pure
segment calculation and allocation/publication effects. A better interface
passes that original descriptor and invokes a segmentation service at the C
call site, as encrypt already receives `checksumHelp` as a parameter.

`Env/Stack.lean` legitimately summarizes TCP/IP behavior, including a reply
that re-enters `WG.wgXmit` (`Leanux/Env/Stack.lean:60–96`). Consequently an IP
delivery contract cannot frame the entire WireGuard state unchanged. It must
describe callback/re-entry effects on queues, ownership and the tape. Similar
fixture policy currently lives inside `WG.State.loopbackSoftirq` and its
neighbors (`Leanux/WG/State.lean:110–174`). Routing rules reside in
`World.route4/route6/routeLookup` in the kernel definitions
(`Leanux/Kernel/Defs.lean:1149–1197`). Their location is less important than
making them explicit service implementations, rather than implicit universal
WireGuard semantics. This can be done incrementally, without mirroring all IP.

### 3.4 Flood processing leaks kernel logic into the environment

This is a semantic repair, not just an interface cleanup.

`Env.flood` discards producer sections and invalid-packet processing, installs
only the leading valid messages, and supplies `floodDepth` to the receive body
(`Leanux/Env.lean:773–813`). `receiveHandshakePacket` computes the load test
from the shortened queue plus this synthetic depth. On the decay path it reads
the clock and ignores its value, forcing `underLoad := true`
(`Leanux/WG/Receive.lean:222–240`). C compares the saved time and clears
`last_under_load` when the decay expires (Linux
`drivers/net/wireguard/receive.c:112–120`). The discarded tail also does not
reconstruct the last saved timestamp in kernel state.

A precondition that the generator always injects within the decay window can
justify one restricted path. It does not justify the complete receive function
or composition with a later packet after the window. Restore the actual
load-decay calculation/reset, put `lastUnderLoad` in kernel state, and remove
`floodDepth` from the WG body's decision. Either retain the actual queue state
or give the bulk producer/consumer summary a precise effect contract that
maintains that state and timestamps. Calling the summary an environment input
cannot hide WireGuard's own choices.

### 3.5 Dispatch order needs suspended activations

`Batch.runWorker` finishes a yielded worker in the mirror, and may defer only
its stop record until the tape catches up. Its comment explicitly assumes the
remaining work commutes (`Leanux/Env/Batch.lean:29–56`). `condResched` rejects
some noncommuting nesting using `queuedWork` (`:70–80,154–164`). This is a
useful fail-closed restriction, but queue emptiness and absence of hidden reads
are not a complete commutation argument. Empty polling can itself read or
update queue metadata; peer references and recorded branch/operand order also
belong to the footprint.

For a restricted scheduler, establish the exact permitted remainder and show
its state effects and observations can move across every intervening action.
For the intended expanding single-CPU domain, preserve a worker continuation
at each yield, including its local packet/keypair and held references; resume
the recorded activation rather than completing its body on the host call
stack. Function bodies can remain direct sequential code between yield points.
This is the largest recommended change, confined mainly to execution structure
and the few yield boundaries. It avoids accumulating special commutation rules
as new work is added.

Dispatch records do not yet determine every placement. `napiIrqExit` consumes
an extra `napiBeforePut` choice with a false default
(`Leanux/Env.lean:697–718`). The checker runs all-after and all-before variants,
then selects operand evidence per section from those two runs; it does **not**
execute the combined selected vector (`evaluator/check.py:1138–1223,
1337–1360`). Matching control-flow shape and isolated operand differences is
useful evidence, but does not establish that one combined execution realizes
all the selected sections and final state.

A proof could take a supplementary complete schedule as a witness and justify
its effects. For the project's deterministic-from-records objective, recording
the ambiguous placement at its kernel source is cleaner. As an immediate
validation improvement, replay the selected complete vector once instead of
treating the stitched evidence as such a replay. This is a focused correction,
not a request for additional long-running gates.

### 3.6 Timer reconstruction mixes inputs and computed results

`armTimer` accepts the recorded expiry if `expires - recorded_jiffies` equals
the requested delay or one less, then installs that expiry
(`Leanux/WG/State.lean:65–88`). The source input is the caller's jiffies read;
expiry is a program computation. The rule needs a witness for that earlier
read and a justified bound on time advancing between the reads. Single CPU
does not by itself prove the one-tick bound, and the comparison excludes wrap.

Prefer recording the caller's operand and computing expiry in the mirror;
use the arm record to check publication/identity. Alternatively state and
justify the exact two-read contract. A whole timer wheel is unnecessary, but
the service must enforce pending/due state, cancellation and permitted
interrupt placement. Current idle-window bounds and a recorded callback are
not by themselves those guarantees (`Leanux/Env.lean:337–407,439–441`).

## 4. Structures and constructs that affect proof difficulty

### 4.1 Device rings lose branch-relevant state

The mirror's encrypt/decrypt device queues are lists. Ring-full tests use
`length >= MAX_QUEUED_PACKETS`; consuming an item immediately removes the head
(`Leanux/WG/Send.lean:124–141`; `Leanux/WG/Receive.lean:312–327`;
`Leanux/WG/Data.lean:104–112`; `Leanux/WG/RxData.lean:96–106`).

Linux `ptr_ring` has producer, consumer-head and consumer-tail cursors, a batch
size, and physical occupied slots (Linux `include/linux/ptr_ring.h:30–40`).
Produce fails when the producer's slot is non-null (`:104–116`). Consumption
leaves stale occupied slots until a batch, or the end of the ring, clears them
(`:247–289`). For this configuration a 1024-slot ring has batch 16: the cache
line is 64 bytes, pointers are 8 bytes, and the batch formula is twice the cache
line divided by pointer size (`kernel/config-x86_64-net-choice:270–271`;
Linux `include/linux/cache.h:12–14`, `include/linux/ptr_ring.h:474–484`;
`drivers/net/wireguard/device.c:348–354`).

**Source-level counterexample to the list helper abstraction:** enqueue one
item in an empty ring, consume it, then enqueue 1023 items without consuming.
The producer has wrapped to slot zero, which consumption has not cleared.
The next produce fails in C although the logical queue length is 1023. The
mirror's length test permits it. This needs neither parallel CPUs nor weak
memory. A whole-WireGuard execution still has to satisfy the surrounding
per-peer and scheduler preconditions; the example already refutes a generic
ring contract based on list length alone.

**Required repair:** retain slot occupancy and the three cursors/batch rule,
with queued packet identities. The logical FIFO may remain a derived view.
This is a bounded structural change, and must precede further full-ring,
refill or multi-worker claims. Increasing fuel or strengthening R over only
the current list cannot make its wrong full test correct.

### 4.2 Shared packet values need one owner

Nodes, peers and keypairs have identities and stores; packets do not have the
same discipline. The device queues and per-peer queues contain copied
`DataPacket`/`RxPacket` values (`Leanux/WG/Types.lean:150–175,259–262,430–436`).
Publication updates a copy found by keypair/nonce for transmit, or the first
uncrypted packet of the keypair for receive
(`Leanux/WG/Send.lean:101–112`; `Leanux/WG/Receive.lean:330–348`). C updates
the very same skb reached by both queue links.

This can be related under strong uniqueness and FIFO/interleaving invariants;
it is not automatically unsound. But the proof must repeatedly recover
identity from content and reconcile copies, especially across failed crypto,
peeked heads and suspended workers. That is avoidable work and is fragile as
the domain grows. Introduce a packet/skb identity and an owned-once store;
queues and worker locals hold identities, and publication changes one state
field. Linked lists of packets can remain logical lists of identities.

Other uses of lists are not inherently problematic. Trie peer-membership lists
can represent intrusive lists with uniqueness, link and ownership invariants;
`listDel`'s global scan is a locality inconvenience, not an algorithmic blocker
(`Leanux/WG/AllowedIps.lean:83–94`). The per-peer `PrevQueue` preserves peeked
and stub state (`Leanux/WG/PrevQueue.lean:1–75`), unlike the device ring. Its
fixed false producer-in-progress arm (`:59`) still needs a critical-section
argument excluding observation between the producer's link writes. Do not
justify that solely by saying “one CPU.”

### 4.3 Lifetimes must compose across deletion and recreation

`recordQueued` binds `(worker kind, peer id)` permanently to the first address;
`resolveUnit` returns the first address match
(`Leanux/Kernel/Defs.lean:1355–1387`). No retirement removes these entries when
`peerPut` erases a peer (`Leanux/WG/Peer.lean:38–47`) or `wgDestruct` erases the
device (`Leanux/WG/Device.lean:240–258`). The map persists across operations
(`Leanux/Runner.lean:821–833`), while fresh devices restart local peer IDs
(`Leanux/WG/Types.lean:408–425`).

Two consequences follow directly from the lookup rules. Reusing an old work
address for a new peer can select the old peer and fail the queued-peer check.
Recreating a device with peer zero at a different address can fail the
same-owner address check. These are legitimate allocation lifetime changes,
not evidence of an invalid oracle. This is a concrete replay/composition
defect, not merely future proof inconvenience.

Use lifetime-scoped identities, or retire the association when its owner is
released and distinguish device generations where necessary. Clear or retire
the corresponding timer and pending-work associations consistently. The
relation should require stable addresses only during a live object's lifetime,
just as cerberus-sl's store embedding does.

There is a second lifecycle composition defect. `ratelimiterAllow` inserts and
updates actual entries (`Leanux/WG/Receive.lean:137–160`), but `gcEntries false`
always reports empty bucket lists and removes no entries, and last-device
uninit calls it without an emptiness guard (`Leanux/WG/Device.lean:130–166`).
C uninit calls GC with NULL, causing every entry to be removed (Linux
`drivers/net/wireguard/ratelimiter.c:55–82,205–218`). Init also does not reset
the mirror table. Thus “receive under load; delete last device; recreate” does
not have a preserved table relation. The checker may reject the differing
coverage; that would not fix the missing mirror transition. Implement the
teardown and eventual GC effects; an explicit unsupported guard is only an
interim way to make the narrower domain honest.

RCU erasure is a distinct issue. Removing an object from the mirror's live
store need not mean that C memory is already freed. Keep retired C ownership
in the relation until callbacks/grace periods dispose of it, and show no
subsequent live access depends on omitted fields. `call_rcu` is not `free`.
If callbacks touch retained state or can race with an outstanding activation,
their effects must appear in the model/service contract. Examples are trie
removal/free (`Leanux/WG/AllowedIps.lean:218–225,270–277`) and peer/keypair
final puts (`Leanux/WG/Peer.lean:38–47`; `Leanux/WG/Keypair.lean:31–41`).
This is tractable with retirement ownership; it is not a reason to model C
allocation bytes inside Leanux.

### 4.4 Fuel, stops, repeatable decisions and numeric representations

| Construct | What the refinement argument needs | Assessment and proposed treatment |
| --- | --- | --- |
| Structurally bounded traversal | A representation invariant tying the bound to C progress. The 130-step trie search follows strictly increasing prefixes with IPv6 width at most 128 (`Leanux/WG/AllowedIps.lean:98–112`). | Tractable. Keep a safe structural bound and explain its source. Check the final empty-iteration allowance as well as the number of nodes. |
| Arbitrary retry fuel | A universal C loop cannot inherit a small constant bound merely because failures are unlikely. Index insertion stops after 64 collisions (`Leanux/WG/Peer.lean:125–138`); jitter after 256 rejections (`Leanux/WG/Handshake.lean:353–358`). | A tape with 64 collisions followed by a free index is enough to defeat the first bound. Use an explicit execution budget/resumable loop or fuel derived from a supplied finite witness, separately from semantic failure. Probabilistic termination is not needed for finite-prefix simulation. |
| Size and scheduler fuel | `subtree` and `rootRemovePeerLists` use one million total iterations (`Leanux/WG/AllowedIps.lean:231–267`); a peer cap does not bound its number of prefixes. Worker loops use ring capacity plus one although yields can permit refill (`Leanux/WG/Data.lean:104–132`). Scheduling uses depth 4 and at most 16 nested runs per hook (`Leanux/Env/Batch.lean:112–169`). | Derive traversal fuel from actual reachable node count; distinguish bounded simultaneous occupancy from total work during a dispatch. Make execution budget exhaustion resumable or explicitly a runner limit. Do not label these arbitrary limits C invariants. |
| `invariant` and `unsupported` | Prove the former unreachable under R; for the latter give an independently stated path restriction, or extend the mirror. A rejected kernel behavior is not simulated behavior. | Good fail-noisy engineering, but neither is an acceptable catch-all proof postcondition. The table above identifies several currently overstrong domains and mislabeled budget failures. |
| Stop semantics | `M = StateT World (Except Stop)` discards the intermediate world when stopped (`Leanux/Kernel/Defs.lean:1119–1137`). C has not rolled back earlier updates or freed every allocation. | Fine for a checker that rejects the whole run and a proof of in-domain completion. A prefix/open-boundary simulation needs residual state, local phase and remaining tape on stop. Do not interpret an exception as C transactional rollback. This change is optional if the proof remains explicitly success-domain only. |
| Repeatable decisions | An induction over actual loop iterations and the real branch order, independent of compressed coverage evidence. `branch` itself preserves occurrences (`Leanux/Kernel/Defs.lean:1226–1235`); repeatability is checker metadata (`Leanux/Kernel/Decision.lean:1868` onward). | Usually not proof-hostile. But the checker retains first-occurrence order and later outcome sets, not full repetition order (`evaluator/check.py:861–897`). GC even emits only the first bucket's decisions (`Leanux/WG/Device.lean:134–149`). Treat that trace as a projection, or move reporting compression out of the body if exact events are part of the target. No need to add a gate for every occurrence. |
| Lists and flattened structs | A field projection plus lengths, uniqueness, membership, alias and ownership invariants. Flattened peer handshake/cookie fields can still map to distinct C subobjects (`Leanux/WG/Types.lean:209–302`). | Usually tractable; no blanket conversion to raw-pointer structures or dependent types. Packet aliasing and `ptr_ring` are the specific exceptions needing redesign. Keys represented as byte lists need length invariants, not new C memory semantics. |
| Natural/integer arithmetic | Relate C widths, signedness, overflow and time comparisons to the Lean operation. `dstCacheGet` uses ordinary `>` for C's wrap-aware `time_after` (`Leanux/WG/Socket.lean:152–165`). Sequence numbers and statistics are often `Nat` (`Leanux/WG/Types.lean:48,372–373`). | Use word operations at wrap-sensitive sites or explicit bounded-execution assumptions. The FS ring already shows how to retain wrapping semantics. Long-lived universal claims cannot silently inherit short-test no-wrap assumptions. |

The lack of `partial` definitions in the inspected Leanux sources is helpful,
but totality obtained by rejecting a legal long run is not C termination or
simulation. Likewise, partial-correctness adequacy in the proof host does not
turn a successful C return into permission for the mirror to stop early.

## 5. Worked samples

These are sketches of relations and simulation steps, not theorem statements
or proofs. Each names both the first extra contract needed and any actual
representation/semantic obstruction, so an ordinary library cut is not
mistaken for a reason to abandon the target.

### 5.1 Allowed-IPs trie insertion

**C/mirror pair:** Linux `drivers/net/wireguard/allowedips.c:181–250,281–300`;
`Leanux/WG/AllowedIps.lean:115–184`.

**R sketch.** Root slots relate to `root4/root6`; each live `NodeId` embeds into
one allocated `allowedips_node`, and each `PeerId` into the corresponding peer.
Node fields relate peer, children, prefix length and copied address bits.
`Slot` represents the parent-slot identity, including the tagged parent
encoding; the C layout/alignment facts belong in the representation predicate.
The stored integer's bit ordering relates to C's endian-adjusted byte array.
Reachability is acyclic, child prefixes strictly increase, widths/array lengths
are valid, and every peer-owned node appears exactly once on that peer's
intrusive list. Own node allocations once and frame unrelated peers/nodes.
The caller owns the update lock and supplies a valid peer and address buffer.

**Step sketch.** Relate the wrapper's sequence increment and address conversion;
take the CIDR/null-peer guards and empty-root test in the same order. For a
nonempty root, maintain the current node and last matching parent along
`nodePlacement`. At exact match, change the peer and move its list link. At
insertion, extend the embedding at successful allocation, put the node on the
peer list, then relate the no-child, covering-prefix or split cases. A failed
second allocation removes/frees the new leaf while leaving the original trie
and the already incremented sequence number as C does. The entire operation
is not rolled back on `-ENOMEM`.

**First place the naive fieldwise sketch breaks:** successful `allocNode`
already installs `newNode key cidr bits peer` (`Leanux/WG/AllowedIps.lean:61–80,
123–127`). C has only a zeroed allocation at line 190, tests it, then assigns
peer/list/CIDR at lines 193–195. The mirror initializes fields before that
choice point and changes their relative order with list insertion. The same
issue occurs at the other allocations.

This is a local, tractable mismatch. Either split allocation and initialization
at the C sites, or use a private, not-yet-published node ownership/phase
predicate and match the combined initialization region. The latter requires
checking that no callback or observer can see it during the region. Splitting
the helper is cheap and simplifies the proof, but no trie algorithm redesign
is needed. Subsequent obligations are the list helper contract and the
strict-prefix invariant supplying search fuel; the million-node free limit is
a separate problem for composition with teardown.

### 5.2 Handshake send worker

**C/mirror pair:** Linux `drivers/net/wireguard/send.c:21–53` and
`noise.c:516–581`; `Leanux/WG/Handshake.lean:160–194,458–478`.

**R sketch.** A live peer embedding connects `work` to that peer's embedded
`transmit_handshake_work`; the queued/running-work relation carries the reference
that the final `peer_put` releases. Relate identity/key lengths, handshake
state, chaining key/hash, index-table entry, endpoint/cache/socket state,
last-sent clock and pending timers. Separate owned secret buffers and local
message storage from the peer's persistent state. Hold the necessary lock
resources when entering each noise region. The oracle suffix supplies clock,
ephemeral-key, timestamp, index and jitter reads in source order. Crypto and
socket services have byte-result and ownership/effect contracts.

**Step sketch.** Resolve the recorded unit and transfer queued work to a running
activation (`Leanux/Env.lean:226–236`). Relate the rate-limit test; on success,
update `lastSentHandshake`, run the initiation's chain/DH/encryption/index
sequence, and propagate creation failure. Add MACs, perform traversal and
keepalive timer actions, take the second clock read, send the buffer, and arm
the retransmit timer. Finally release exactly the work-held peer reference.
The allocation-failure path of buffer send must preserve the caller's actual
continuation: the worker does not turn an ignored send failure into failure of
the whole operation (`Leanux/WG/Handshake.lean:416–433,458–478`).

**First external contract:** C's `wait_for_random_bytes` and lock acquisition
precede the noise work (Linux `noise.c:527–530`). An initialized RNG and an
appropriate exclusion/wait contract make these tractable cuts; C primitive
crypto correctness is also an outstanding dependency, not supplied by matching
test vectors.

**First hard break on an otherwise valid, fresh-lifetime successful path:**
index insertion caps its collision search at 64. Supply 64 occupied draws then
an unused 65th: C continues searching, while `indexInsert` stops
(`Leanux/WG/Peer.lean:125–138`; Linux `peerlookup.c:119–163`). The arbitrary
bound cannot follow from R. Replace it with budgeted/resumable execution or a
finite-witness-derived bound. The 256-draw jitter cap creates the same issue
later, followed by the timer-arm contract described above.

For a recreate/reuse trace the sketch can fail even earlier, at dispatch
resolution because the address map still names a dead owner (§4.3). For a
restricted fresh peer with bounded draws and specified services, the worker
body is already a good target. Its C control flow does not need to be recovered
from the emitted handshake bytes.

### 5.3 `wg_delete`

**C/mirror pair:** the `RTM_DELLINK`/unregister wrapper and Linux
`drivers/net/wireguard/device.c:115–135,242–270`, `peer.c:94–150,167–220`;
`Leanux/Env.lean:564–570`, `Leanux/WG/Device.lean:79–103,240–275`,
`Leanux/WG/PeerRemove.lean:100–144`.

**R sketch.** Own the device registration/update resources, socket references,
peer/list/trie/keypair stores, work and packet queues, timers and references
held by pending/running activations. Include route/address state in a separate
unregister-service relation. Keep already retired objects in a retirement
resource until RCU callbacks run. Successful return removes the live device,
accounts for all release/drain effects, and leaves future creation possible;
it does not require erasing arbitrary framed objects.

**Step sketch.** The no-device case returns `-ENODEV`. Otherwise, if up, follow
`wgDown/wgStop`: mark down, purge staged packets, stop timers and clear
handshake/keypair state. The unregister core performs its specified
notifications/backlog/RCU work. Destruct clears creating-net/port/socket state,
removes allowed-IPs and marks all peers dead, drains the relevant queues and
disables NAPI, releases peers, destroys workqueues, purges packet queues,
waits for RCU callbacks, tears down the last ratelimiter user and frees the
device. Each wait needs a contract that can run the work it waits for.

**First break for general deletion:** `Env.wgDelete` calls `requireIdleDevice`
before entering the mirror body (`Leanux/Env.lean:565`). Legal C deletion with
crypt work/NAPI pending is excluded. In the body, the two crypt flushes and
NAPI disable/delete remain omitted under that exclusion
(`Leanux/WG/PeerRemove.lean:110–113`). The mirror cannot simulate those C
effects for the general entry state; a scheduler/drain interface is needed.

**Inside the restricted idle domain:** the first integration obligation is the
unregister/stop service's callback and sleep contract. During peer removal,
`AllowedIps.free` erases nodes at the `call_rcu` point
(`Leanux/WG/AllowedIps.lean:270–277`). A naive relation equating the live store
with all allocated C memory breaks there. A retired-ownership component repairs
it without moving the whole C allocator into the mirror. At the eventual
barrier, callbacks must consume that ownership, not merely satisfy a
`mayHaveSlept` marker.

Two further failures remain even after that repair: last-device ratelimiter
cleanup does not remove populated entries, and dispatch identity associations
survive the destroyed device (§4.3). These make the postcondition insufficient
for a following create/queue operation. Thus `wg_delete` is a useful skeleton,
but currently the weakest of the three complete simulation targets. Adding
more deletion cases without repairing lifetime and drain semantics would
increase proof cost substantially.

## 6. Further obligations that should shape the design

**Initialization is part of R.** Several pre-trace secrets/hash keys are zero
placeholders, explicitly marked unknown (`Leanux/WG/Types.lean:357–368`;
`Leanux/Kernel/Defs.lean:346–358`). Relating them by equality to a live kernel
is unjustified. Capture initial values where observable, parameterize initial
state, or represent knowledge/validity and establish that unknown fields are
unobserved until initialized. There need not be a proof of the entire boot
sequence, but there must be a realizable entry relation.

**Synchronization is an effectful boundary.** Locks, reference-count operations,
RCU and workqueue barriers are not all interchangeable no-ops in a one-CPU
build. The relation must say who owns each field across callbacks and sleeping
allocation, and which interrupts are disabled. Refcount saturation and
`get_unless_zero` require their actual integer/atomic contracts. A carefully
bounded sequential-region reduction is plausible; assuming all such calls
preserve the entire WG state is not. The queue/store and continuation changes
make these ownership obligations substantially easier to state.

**Representation is not security.** Relating mathematical crypto outputs to C
calls still requires correctness of those implementations or an explicit
trusted primitive boundary. Logical disappearance of keys is not itself a
constant-time or memory-erasure guarantee. Keep the adopted named primitive
and secret-lifetime conventions, but do not silently broaden a behavioral
simulation into those separate security claims.

**Instrumented Linux versus Linux.** The kernel identity gate selects the
intended executable. It does not prove that recording/steering instrumentation
preserves the semantics being claimed. A later result must name whether it is
about that configured instrumented kernel, or also about an uninstrumented
kernel with an erasure/admissible-steering argument. Source locations, compiler
transformations and record arming are part of this connection. This is a
trusted-boundary accounting task, not a proposal to build proof-audit machinery
now.

## 7. Ranked changes and when to make them

The ranking favors proof leverage per implementation cost, while distinguishing
the larger changes that still cannot safely be deferred. Costs are relative
engineering estimates, not measured schedules. **Before expansion** means
before adding more mirror behavior on the named surface; independent local
body work can continue. These are recommendations, not authorizations to modify
code or standing practices.

| Rank | Change | Proof leverage / cost | Timing and concrete completion criterion |
| --- | --- | --- | --- |
| 1 | Repair lifetime-scoped dispatch identities and populated ratelimiter teardown (§4.3). | Very high / low–medium. Removes real failures of operation composition. | **Before more lifecycle or multi-peer composition.** Release/recreate may reuse an address or a logical ID without stale resolution; last-user teardown accounts for every table entry. |
| 2 | Restore load-decay computation/reset and remove synthetic flood depth from WG decisions (§3.4). | Very high / medium. Restores a missing C choice and an actual kernel state variable. | **Before more receive/load behavior.** The saved clock and queue relation determine the same decay/clear decisions for both within-window and expired cases. Bulk processing has an explicit state effect. |
| 3 | Preserve `ptr_ring` cursors, occupancy and batch clearing (§4.1). | Very high / medium. No representation invariant can repair the current full test for general rings. | **Before more bulk/refill/full-ring behavior.** Consume-then-wrap-refill takes the C success/failure branch, including uncleared slots. |
| 4 | Give skbs/packet lists stable identities and one mutable store (§4.2). | Very high / medium–high. Removes repeated alias reconstruction and enables ownership transfer across yields. | **Before broadening shared-queue interleavings.** Device queue, peer queue, peeked head and worker local refer to the same packet; publication updates it once. Implement alongside rank 3 where practical. |
| 5 | Specify service footprints, oracle modes and live/retired ownership; separate decoding from execution effects (§§1,3.1–3.3,4.3). | High / medium, incremental. Makes every later function proof local and identifies the actual trusted cuts. | **Before adding new cuts or hidden inputs.** Each has a concise contract description covering reads, state changes, callbacks and failures. Retrofit existing lifecycle/stack cuts first; avoid a generic all-allocation-site permission where the callee's sites are known. |
| 6 | Preserve suspended activations and resume by recorded schedule; resolve NAPI ambiguity with a complete execution (§3.5). | Essential / high. Removes the largest structural obstacle to compositional worker and deletion proofs. | **Before extending nontrivial worker nesting, refill-during-yield or pending-work deletion.** A worker pauses with its locals/references intact; no early semantic completion is represented by a delayed stop record. In the interim, replay the selected NAPI vector and state the restricted commutation contract explicitly. |
| 7 | Separate runner budgets from semantics; derive structural bounds and permit arbitrary finite retry witnesses (§4.4). | High / low–medium. Prevents legal finite C executions becoming mirror invariant failures. | **Before increasing scale or claiming complete loop coverage.** Trie traversal uses reachable size; retry/yield exhaustion can resume or has an explicit bounded claim. Occupancy is not a total-dispatch work bound. |
| 8 | Record timer input operands; implement word/time arithmetic where C wraps; make initial unknowns explicit (§§3.6,4.4,6). | High / medium. Removes hidden temporal and initial-state assumptions. | **Before broader timer, long-lifetime or wrap claims.** Expiry is computed from the corresponding source read; initialization and time-order relations are stated independently of replay success. |
| 9 | Align small initialization regions and local helper ownership: trie allocate/init order, intrusive-list locality, GSO call-site service (§§3.3,4.2,5.1). | Moderate–high / low–medium. Reduces local proof bookkeeping without changing the altitude. | Do when touching these helpers or preparing their first body proof. Splitting trie allocation/init is a particularly cheap improvement; no global rewrite into C-shaped memory is needed. |
| 10 | Establish the Linux-to-proof-host path and the trusted primitive scope (§§1,6). | Essential to an end-to-end proof / high. Primarily outside Leanux. | Plan before claiming formal verification; prototype a supported synchronous body, then state how synchronization, callbacks, GNU C/atomics and instrumentation connect. This does not require delaying every independent mirror addition until the host verifies Linux. |

Do not respond to these findings by adding theorem scaffolding, a proof-audit
pipeline, exhaustive assertion tables or more integration gates. The immediate
work is semantic representation and small, explicit interfaces. Ordinary
targeted validation should accompany future fixes under the existing three
gates; this assessment has neither implemented nor validated them.

## Reproducing the source assessment

The durable artifact is this conclusion with its source locations. Inspection
can be repeated without a build or guest, for example:

```sh
git show 6903c69:Leanux/Env/Batch.lean | nl -ba
git show 6903c69:Leanux/Kernel/Defs.lean | nl -ba
git show 6903c69:Leanux/WG/AllowedIps.lean | nl -ba
git show 6903c69:Leanux/WG/Handshake.lean | nl -ba
git show 6903c69:Leanux/WG/Device.lean | nl -ba
git show 6903c69:evaluator/check.py | nl -ba
nl -ba /home/dev/projects/lean-ux-proto/.deps/linux/include/linux/ptr_ring.h
nl -ba /home/dev/projects/cerberus-sl/docs/INTERFACE.md
```

Use the pinned revisions when resolving the other references; neighboring
repositories and the main branch may advance independently. No run dumps or
new evidence bundles are needed to retain this assessment.
