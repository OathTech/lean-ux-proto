# WireGuard proof campaign 2

## Progress

Work is confined to `.worktrees/proofs-campaign-2`, branch `proofs/campaign-2`.
H1, H3 and H4 have local contracts; their whole-operation/whole-run claims
remain open. H4 also has a checked reachable internal dump-accounting finding. H5 has a checked batch-completion counterexample and open progress
obligations. H6 has twelve local timer contracts; whole-run site coverage and
retry/session counting remain open.
H2 was unblocked by the user's landing notice for `de62c9d` on 2026-10-15.
Main was merged into this branch at `5033f7a`. No result is claimed complete.
The existing campaign-2 terminal declarations build over `de62c9d` and
pass standard-axiom inspection. The changed Noise and configuration modules
also pass fresh stock kernel replay. The full gate remains failed in inherited
campaign-1 files; campaign 1 owns their repair.

[USER 2026-10-15] The index-lookup fix has landed at `de62c9d`; merge main
into the campaign branch, carry the index frames and permit H2 to start.
Guest slots default to 16; concurrent capped runs are allowed. No merge to
main or push.

[USER 2026-10-15] “Pay the frames” means campaign 2's own results. Existing
shared lemmas remain campaign 1's. Any necessary local replacements belong
inside the result directory, named as variants of the shared lemma; report
rather than copy a layer if more than a few would be needed. Scoped validation
continues with inherited breakage recorded. The existing standalone C2 contracts
suffice for this carry, so no shared-layer copy is needed.

[AGENT 2026-10-15] Carry the local Noise, expiry and staged-send contracts
through the embedded-owner representation. The internal expiry-prefix total
contract is now a normal-completion contract: a NULL handshake peer word
stops before clearing. The public successful-expiry statement is unchanged;
its assumed original run establishes prefix success. This is a statement-domain
correction for the landed mirror, not a new mirror finding. Index removal uses
owner identity even when the owner's peer word is NULL. No shared definition
or lemma has been edited. Independent read-only review found no correctness
issue in the six-file carry. The queue-refill reproduction still reports its
expected operation-4 invariant failure. No cap hit or infrastructure rerun.

[USER 2026-10-14] Work H1, H3 and H4 before H2; start H2 only after the
index-lookup fix lands and its landing is relayed. Merge other main landings
into the campaign branch and carry proofs; never integrate into main or push.

[USER 2026-10-14] Put any requests for the mirror team in a document in this
tree and notify the user. The first request is the
[batch-completion guard](2026-10-14-campaign-2-mirror-requests.md); the user has
been notified.

The initial full proof-target build failed in inherited
`WG/CounterWindow/Refinement.lean`: its execution equation still uses the
old counter-limit branch records. That shared repair belongs to campaign 1.
New result modules are checked independently until the shared carry lands;
this does not count as a passing full proof gate.

## H1 — Noise session state machine (in progress)

[AGENT 2026-10-14] Start with a small peer/slot projection and exact original
operation contracts, then compose caller coverage. Keep normal endpoints
separate from event coverage and successful initialized executions. No existing
shared lemma or definition is edited.

Source qualifications to retain in the statements: create/consume initiation
can restart from any prior state. Initiator rotation with an existing `next`
demotes that pending key to `previous` and puts the old current; without a
pending key it demotes current. These are the C's explicit arms, not findings
against the mirror. The original charter wording “as the code implements them”
requires all of them. Confirmation's once-per-lifetime property will require
allocation/slot provenance, beyond an immediate second-call result.

Architecture: `Basic` defines a peer/slot projection and normal-execution
contracts; `Slots` proves all rotation arms, confirmation, clearing and exact
handshake zeroing; `KernelFrames` and `PeerFrames` isolate hidden-input,
allocation and index-operation frames; `StateEdges` and `ConsumeEdges` prove
tag endpoints. Eleven terminal statements cover these local contracts.
The consume statements establish the returned peer's tag, not failed-prefix
framing or authentication provenance. `beginSession`'s tag contract is checked;
its complete allocation/rotation contract is still open.

Remaining H1 work: source-call coverage of owned edges through the runner;
fresh-allocation provenance for session installation and confirmation once per
allocation lifetime; exact keypair-put events and expiry's sending-key effect.
The immediate second-call confirmation theorem is deliberately not presented
as the lifetime theorem. Slots are individually optional values, not a bound
of three on the entire store: outstanding packet references can retain keys.

The read-only source review found no new mirror/C discrepancy. It also
identified a necessary invariant boundary: an initiator rotation can free old
current before overwriting its slot, so live-slot coherence belongs at completed
rotation cuts, not every primitive assignment. No accepted-run counterexample
is claimed here.

Two whole-run architectures were reviewed: a source-call observer with exact
erasure and event-completeness equations, or direct structural execution
derivations with primitive silent rules. Neither may infer empty history merely
from equal endpoints. Campaign 1's existing replay-window projection omits
slots and handshake tags, so its whole-run theorem cannot discharge this work.
The local operational and WP composition variants are standalone because
importing the existing generic shared layer also imports the lagging refinement.

Effort: capped scoped elaboration iterations, an initial full-target build and
two full proof-gate runs. All full runs failed at inherited counter refinement;
the gate's token and import checks passed. The initial eight terminal statements
passed axiom inspection (only the three standard axioms) and stock kernel replay.
The expanded checkpoint's eleven H1 and five H3 statements pass scoped builds,
axiom inspection (only `propext`, `Classical.choice`, `Quot.sound`) and stock
kernel replay, run separately with `capped -- scripts/in-bundle lake env
leanchecker --fresh Leanux.Proofs.WG.Noise.Statements` and the corresponding
`Roaming.Statements` command. A combined `--fresh` invocation was rejected by
the checker because it accepts one module; the separate runs both exited zero.
The full proof gate remains failed as described above. No cap hit, mirror edit,
differential check or guest run.

Ranked mirror suggestions: none at this checkpoint.

## H2 — Session index uniqueness (in progress)

[AGENT 2026-10-15] Separate numeric-index uniqueness from embedded-owner
uniqueness, then prove exact contracts over the original operations before
composing reachable-state coherence. The landed representation keeps owner
identity in each table row and its optional peer word in the owner object.
The two are not interchangeable on arbitrary states.

Fifteen terminal statements cover removal, the keypair-removal specialization,
handshake replacement, normally completed insertion, lookup owner/table
provenance, total matched-entry NULL/zero-reference/live lookup effects, and
recorded collision-prefix completion, a corpus-draw two-call instance and
bounded allocation freshness, three original handshake-operation numeric
uniqueness contracts, and total absent/disallowed lookup. Removal and replacement return under device residency. Replacement
preserves numeric indices and every owner object's peer word; preserving owner
uniqueness additionally requires the destination keypair not already hashed.
Insertion first removes this owner's old row, then inserts a fresh numeric
index at the head, preserving both uniqueness properties. No unconditional
insertion-success claim is made for absent or exhausted draws. The landed
mirror has no `indexRemoveKeypair` declaration: its operation is now
`indexRemove (.keypair id)`, also used by `keypairPut` after a peer-word
dereference. The removal statement does not claim a NULL dereference succeeds.

`LookupSource` proves the original scan stops at the first equal numeric
index, including a disallowed kind; `Lookup` composes that scan with the
original reference-acquisition/store-back suffix. The general terminal lookup
postcondition says any returned owner comes from an initial row at the
requested index and allowed kind, and the table is unchanged. `PeerWords`
adds total contracts when the first matching row has a permitted kind and
a resident owner: a NULL word returns nothing; a resident zero-reference peer
returns nothing and stores NULL; a positive, bounded reference count returns
the owner and stored peer identity, increments the reference, then stores back
the word. The exact post-state retains the increment when handshake-owner and
referenced-peer identities alias. Missing objects and reference overflow are
excluded by explicit premises matching the original stops. These local effects
remain separate from reachable owner/peer coherence. `LookupMiss` also proves
that no first matching entry, or a disallowed kind on that first match, returns
nothing and leaves the entire device unchanged; lookup does not continue past
a disallowed equal-index entry.
`Collision` proves bucket walking tests exact numeric membership in the whole
table. `Insert` factors the original draw loop and proves freshness on normal
completion by induction over its budgeted iterations. `DrawRecords` proves
that any finite contiguous sequence of colliding four-byte draws followed by
a fresh draw completes the original insertion: the original record-derived
budget suffices, each collision yields to the next original iteration, and
the unused hidden-record suffix is preserved exactly. The collision premises
refer to the table after unhashing the inserting owner; repeated collisions
and arbitrary trailing records are allowed. Independent review found no
correctness issue and prompted the explicit “contiguous” qualification.
Interspersed ambient records, streams without a fresh draw, explicit branch-log
counting and the `s2_index_collision` runner instance remain open.

`CorpusDraws` instantiates two original insertions from an empty table with
`s2_index_collision`'s three steering values (0x0a0b0c0d twice, then
0x11223344), preserving an arbitrary unused suffix. This is local operation
composition: the actual runner has other operations between those insertions.
`Allocation` proves the original keypair allocator's exact normal effects,
copying its optional peer word and establishing freshness from explicit bounds
on resident and hashed keypair IDs. Both bounds are preserved. Their
initialization and preservation through all callers remain obligations.
Independent review found no correctness issue in these two increments.
The concrete composition initially failed kernel checking with deterministic
timeouts; factoring the generic two-call proof before applying concrete draws
resolved that elaboration problem. These were failed proof iterations, not
infrastructure outcomes or successful checks.

`HandshakeFrames` composes numeric uniqueness through original
`createInitiation`, `createResponse` and `beginSession`, including allocation,
slot rotation, displaced-key removals and owner replacement. These contracts
cover normal completion, including early returns; they do not characterize
stopped prefixes. Independent review found no correctness issue and confirmed
that numeric uniqueness needs no destination-owner freshness premise for
replacement: labels change while numbers remain fixed. These new result-local
index contracts do not edit or copy campaign 1's shared receive-state layer.

The table invariant is about hashed entries; this checkpoint does not yet establish all-driver reachable-session
uniqueness or initialize/preserve owner-store coherence through every caller.

Independent read-only review found no semantic defect. Its wording finding was
fixed: the terminal lookup docstring now describes its exported provenance
postcondition, leaving stronger first-selection semantics to the internal
scan contract. The fifteen statements pass scoped build, standard-axiom inspection
and fresh stock kernel replay (`capped -- scripts/in-bundle lake env leanchecker
--fresh Leanux.Proofs.WG.Index.Statements`). The full proof gate still fails in
inherited `CounterWindow.Refinement` and `ReplayWindow.Counterexamples`;
token/import checks pass. The subsequent shared index frames remain campaign
1's carry. No mirror edit, cap hit, infrastructure rerun, guest or differential
run. Ranked mirror suggestions for H2: none at this checkpoint; no mirror
change has been requested to simplify the proofs. Independent review of the
three matched-entry contracts found no correctness issue; it checked owner
aliasing, missing-owner versus NULL distinctions, and the exact refcount bound.

## H3 — Endpoint roaming (in progress)

[AGENT 2026-10-14] Observe the remote destination `(family, address, port,
IPv6 scope)`. The charter's “endpoint changes only” is read as remote roaming:
the full record also carries local-source caches, which routing and cache
clearing legitimately change, and flowinfo, which `endpoint_eq` ignores.
This preserves the intended remote-roaming claim; it does not claim full-record
get-after-set equality. `n1_flowinfo_only.json` already exercises that distinction.

Five terminal local contracts establish source conversion, setting a supported
remote destination, clearing source caches without roaming, and the composed
packet-source setter, plus exact successful data decryption under the resident receiving key. IPv6 link-local scope comes from the arrival interface.
The proof follows the original functions, including the endpoint-equality
early return and destination-cache reset; no mirror changes.

The read-only source review identifies the receive authorization cuts: Noise
consume success for initiation/response, and crypted publication followed by
replay acceptance for data. Data roaming precedes inner-IP/AllowedIPs checks;
authenticated malformed inner packets and keepalives may roam. Outer source
identity is not authenticated by the data AEAD. Cookie messages do not roam.
These source observations are not yet theorems about the whole receive path.

Remaining work: derive crypted-publication provenance from successful AEAD,
carry it through queue/poll execution, cover the handshake and netlink callers,
and frame remote destinations across the remaining runner operations. Arbitrary
Worlds may contain forged crypted packets; they are not accepted-run findings.
Callbacks require their actual concrete framing contracts, not an assumed
authentication result. No Rule Zero finding or mirror-team request yet.

Ranked mirror suggestions: none at this checkpoint. Effort: a read-only source
review and capped scoped proof builds; ordinary elaboration failures repaired.

## H4 — Configuration semantics (in progress)

Thirty-nine terminal declarations cover configuration leaves, peer flags, bounded
readback, normal-return guarantees, one sequential partial-error case, and
fwmark/cache frames. `Validation`, `Identity` and `Port` prove invalid allowed-IP
rejection, exact allowed-IP serialization, private-identity normalization,
static-static precomputation and stopped-device port setting. `Flags` proves
missing-peer remove/update-only and self-key no-ops, invalid flag/protocol
rejection, and acquired-peer removal precedence. The removal equation is a
stage result, not a complete lifecycle theorem.

`PeerScalars`, `PeerDump` and `RoundTrip` compose the original peer setter and
getter for an existing peer while down: the requested preshared key and
keepalive interval read back exactly. The dump has a fresh cursor, an empty
allowed-IP list and at least 168 bytes remaining (enough for the largest fixed
encoding, with IPv6). `Returns` and the local `*Returns` variants additionally
prove actual normal-return existence when the reference count is positive and
its increment is strictly below `2^31`. The broader `Ensures` statements remain
partial-correctness contracts without that count bound.

`DeviceScalars` reaches the original outer `wgSetDevice`: an index-selected
request updates one existing peer, then encounters a malformed peer entry.
It returns `-EINVAL` normally, retaining the scalar writes and device-generation
increment. A following peer dump returns and reads back the retained writes.
This is a proved partial-update case, not an atomic-update guarantee or an
accepted runner trace. `EndpointSources` proves exact local-source clearing,
cache-slot removal, and preservation of other peers and other device fields.
`Fwmark` proves a fwmark-only outer set writes the mark and increments the
generation, preserving every other device field outside the peer store.
`ClearedSources` joins the literal loop to the outer setter and proves every
listed peer ends with cleared source fields and no cache slot. `FwmarkEffects`
strengthens this to exact pointwise peer-store effects: unlisted peers are
unchanged, listed peers retain all other fields, and duplicate list entries
retain the last reset timestamp. Reset timestamps are existential; their record
provenance and consumption are not proved. These fwmark contracts concern normal
completion. `SocketPorts` proves actual normal return
and an exact device update for socket replacement and for initialization at a
nonzero port in an existing namespace: conflicts return `-EADDRINUSE` without
a device change, success replaces both sockets and the incoming port.
`RunningPort` and `DevicePorts` compose this with the original port setter and
outer configuration request: a different port clears listed peer sources/cache
before binding, so a bind error retains those effects. An equal-port inner
request leaves the device unchanged; an equal-port outer request still increments
the generation. The outer theorem assumes an existing namespace; the inner
contract also covers namespace failure. `RandomPort` proves port-zero success
selects within 32768..60999 and, for a supplied padded four-byte draw with a free
first candidate, proves an actual return installing exactly the computed port.
The generic zero-port theorem remains partial: missing records or a collision
can stop. `ZeroPort` composes normal port-zero behavior through the outer setter,
including stopped/running behavior and the equal-zero no-op. `RecordedPort`
strengthens the supplied-draw success theorem to exact final record-tail
preservation and proves an occupied first candidate raises the mirror's declared
outside-domain collision stop. This is a modeled-domain boundary, not a kernel
bind-error or collision-retry claim.

`PrivateKey` adds actual-return guarantees for identity installation, cookie-key
precomputation and an unchanged-key-only outer request. Unchanged means the raw
requested bytes equal the stored clamped bytes; repeating an unclamped request
can execute the update again. `Precomputation` preserves the complete surrounding
device and models the ordered peer-store writes, including DH output followed
by zeroing when necessary. `ExpiryEffects` gives the exact normal-completion
store transformation: handshake entries removed, handshake fields zeroed, slots
preserved, and next/current sending validity cleared without changing other
keypair fields. Its pointwise theorem handles aliased IDs. Missing targets stop
the original operation; the pure transformation's missing-target fallback is
not an executable-equivalence or return guarantee. The weak existential-time
contract leaves last-sent time unrestricted. `ExpiryClock` separately closes
that gap by exposing the actual prefix and reset-clock read from the original
run and using the returned clock in the final state, with wrapping arithmetic.
Independent review confirmed that relation. The read may use placeholders where
enabled; captured-record provenance is not established by this theorem.

The private-key installation block now composes identity installation,
cookie-key recomputation and the snapshotted peer-list loop for both staged-send
settings. Its ordered relation records resident peers and intermediate stores,
allowing repeated peers and aliased keypair slots. An unconditional source
equality connects the factor to the original configuration continuation.

Expiry invalidates current sending material before staging. The original
staging contract proves exact Device effects: an empty staged list is unchanged;
otherwise packets are restored, temporary key references preserve lookups, and
handshake queueing resets attempts and may retain a queued peer reference.
Already-pending work balances its temporary reference. The original handshake
queue function separately exposes the actual age-test clock read; the staging
and loop relations retain only existential clocks. Expiry alone does not imply
queue eligibility without a relationship between supplied clock values.
Dangling current slots cannot complete with nonempty staging. Records and
reference-count bounds may also stop execution. These are normal-completion
Device contracts, including the send-work queue, not descriptions of World
bookkeeping or record consumption. Independent reviews found no semantic defect
in the staging, per-peer, loop or installation increments and confirmed these
scope limits. The original outer private-key-only setter now composes that
relation when the raw key changes and no generated-public-key table entry
matches. It returns zero on normal completion and includes the generation
increment. The earlier unchanged-key total contract covers the no-op key arm;
collision removal and later peer attributes remain separate obligations.

[AGENT 2026-10-15] Compose private-key updates from a baseline after optional
self-peer removal: removal may flush other peers' work under the old identity,
so an unrestricted surviving-peer frame against the initial request state would
be false. Prove the key-only block before composing later peer attributes.

[AGENT 2026-10-14] Get-after-set means the effective configuration established
by the C: keys are clamped, prefixes masked, running port-zero may allocate a
port, and flowinfo-only endpoint changes are ignored. The configured flag is
`REPLACE_ALLOWEDIPS`, not a per-prefix removal flag. These qualifications keep
C semantics; they do not authorize narrowing accepted traces.

Local source factors are copied from campaign 1 at c4ef635 (`PeerSource`,
`DumpSource`) and ec95fa8 (`DeviceSource`), with definitional original-function
equations. The coordinator can unify them after landing; no existing shared
lemma is changed. Independent review found the first full-room dump premise
could not apply after the caller's headers; the sufficient-tailroom theorem
resolves that finding. Review of the normal-return and partial-error increment
found no defect. The fwmark/socket review found one wording error: a supplied
IPv4 socket assigns its port, which need not change the previous value. The
statement documentation now says assignment/preservation. No further defects
were found. Independent review of the port composition and recorded-draw
increment and subsequent outer-zero/record-tail/collision increment found no
defect. Review of the identity/precomputation/expiry leaves found no semantic
defect and identified the weak existential-time and missing-target scope limits
recorded above.

The outer getter is now composed for a single resident peer with no allowed
IPs and sufficient chunk room. Exact local source equations connect the
callback and receive-loop factors to the original definitions. The proof
carries the callback through dump start, data plus DONE queueing, receive and
coalescing; it proves total return of the exact canonical JSON, unchanged
device, and a drained, finished socket 7. The socket initially has an empty
queue and no running dump, and interface lookup selects this device. Its bound
flag is unrestricted. The loop proof exposes its first receive and proves the
finished tail immediately breaks, without expanding 4096 iterations. The
canonical peer includes `allowed_ips: []`. Independent architecture review
confirmed these premises and the distinction from multipart snapshots. A second
read-through of the completed increment found no semantic defect; its premature
validation sentence was corrected before the checks completed.

`ReadbackFrames` and `ScalarGetter` now carry socket 7 and fixture interface
selection through scalar configuration, then compose the original `wgSetDevice`
and `wgGetDevice`. For one resident, live peer on a stopped device, with a
bounded temporary reference count and no allowed IPs, the public getter returns
the new preshared key and keepalive interval in the exact canonical JSON. The
full Device includes the generation increment and balanced reference; the socket
is drained and finished. With a malformed second peer entry, the setter returns
`-EINVAL` and the same first update is read back. This is a total contract for
the composed original operations under the named premises, not an accepted
runner-trace witness or a general multipart theorem. Independent review found no
correctness defect and confirmed the retained partial-update semantics; public
key/table coherence is not assumed or claimed.

`AllowedLists` and `AllowedListView` prove the original list deletion and its
pointwise peer-list effect. `AllowedRemovalSource` factors the unchanged trie
removal loop; `AllowedRootRemoval` closes its singleton root-leaf path.
`AllowedReplacement` composes that path with lookup acquisition/release and the
original public device setter. The new terminal contract replaces a stopped
peer's owned singleton root leaf with an empty allowed-IP list: the node is
erased, its family root is cleared, all peer lists lose the node, the trie
sequence and device generation each advance once, and the lookup reference is
balanced. Ordered map writes remain explicit; no structural map equality is
inferred from pointwise lookup equality. This is a bounded successful-operation
contract, not general trie validity, ownership preservation through arbitrary
insertion, or multipart readback. Independent read-only review found no
correctness defect and confirmed that the extra root/owner premises specialize
the stronger operational helper to the advertised case.

Remaining: private-key collision removal and mixed-attribute outer composition; full peer
removal/replacement and allowed-IP ownership, other partial-error combinations,
and general dump chunks/coalescing. Deferred removal work can change other
peers' dynamic state, so no unrestricted removal frame is claimed.

Rule Zero finding: the empty-device dump retains four bytes of a cancelled
peers-nest reservation. A one-operation getter trace is accepted from the
ordinary fixture; the original callback returns room 3720. C's pre-reservation
snapshot and cancellation give room 3724. Two independent source reviews agree.
This is a reachable internal accounting mismatch, not a demonstrated compared
output difference or kernel finding. The three `DumpCancellation` equations are
kernel checked; the C correspondence is source inspection. Statement-artefact
check: both the C and the mirror's own design require restoring pre-nest room.
[Request 3](2026-10-14-campaign-2-mirror-requests.md#3-restore-pre-nest-tailroom-when-cancelling-the-device-peers-nest)
gives the witness and reproduction command. Ranked mirror suggestion 1:
correct the saved cancellation snapshot (altitude-preserving).

Validation: all fifty-six statements pass scoped build, standard-axiom inspection
(only `propext`, `Classical.choice`, `Quot.sound`), and `capped --
scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Config.Statements`.
The full proof gate fails in inherited `CounterWindow.Refinement` and
`ReplayWindow.Counterexamples` after the index landing; token/import
checks pass. Effort includes repaired proof-elaboration failures, including two
local heartbeat limits resolved by simplifying put calculations before their
continuations. The suggested `vcgen` replacement failed with a missing toolchain
constant; the existing `mvcgen` proofs were retained and rechecked. A direct
scalar-frame proof hit its heartbeat limit; the staged lookup/update/release
contracts closed the same frame without raising the limit. No cap hit, infrastructure rerun, mirror edit, differential
check or guest run. Builds use full Lake module parallelism with
`LEAN_NUM_THREADS=32`; gate runs use `LEANUX_QEMU_SLOTS=16`, without a cap change.

## H5 — Termination and progress (finding; remainder open)

The requested operation-end drain property is false on an accepted constructed
record stream. A two-operation trace starts from the runner's ordinary fixture,
brings wg0 up and batches one correctly sized cookie message. NET_RX queues the
receive worker, but its records contain no worker dispatch. `executeTrace`
accepts; the original syscall-world replay ends with one handshake receive
item, length counter 1 and pending receive-worker identity 1. No hidden record,
suspended activation or raised NET_RX remains.

`Progress/BatchBacklog` defines the exact trace and replay; the two terminal
statements prove runner acceptance and the state summary by `decide +kernel`.
The replay explicitly follows the runner's fixture initialization, syscall
calls and ambient skips; no arbitrary preloaded World is used. This is an
accepted mirror record stream, not a captured Linux execution. The
[mirror-team request](2026-10-14-campaign-2-mirror-requests.md) locates the omitted
handshake-queue drain check in `Env.afterBatch` and gives the reproduction.

Ranked mirror change: add the missing environment completion check
(altitude-preserving). The mirror is unchanged here. The progress claim is not
weakened to permit this backlog. Remaining H5 work includes committed scheduler
dispatch/resume coverage, record-budget productivity and the other operation
completion paths; the finding does not settle those obligations. Effort: one
read-only source review, model-only evaluation and kernel-reduction proofs.
A separate critical read-only review found no material defect. It checked the
runner/replay correspondence, ordinary parser bounds and that the remaining
queue satisfies the scheduler's runnable-work predicate. It also confirmed
the boundary: two checked equations, not a theorem exposing the runner's final
World, and no claim about capture feasibility. No findings required disposition.

Validation for the H4/H5 checkpoint: all seven new terminal statements build,
print only the three standard axioms, and pass separate stock kernel replays
with `leanchecker --fresh`. The full proof gate fails at the same inherited
counter-window refinement; token and import checks pass. No mirror changes,
guest runs or cap failures.

H5 continuation: `Progress/Scheduler` now proves the original resumption
probe's exact outcome and World preservation, its success/mismatch iff
contracts, and the empty/productive worker-iteration equations. Five additional
terminal statements make seven in H5. A successful probe runs an activation on
a copy; it does not itself resume it. In `schedule`, actual resumption first
removes that activation from `suspended`. Equating the probed and actual runs
needs a frame for that removal, because `cryptAhead` reads `suspended`.

A second investigation reproduced an invalid occupancy premise: a nested NAPI
callback inside the encrypt worker generates a reply and refills that worker's
queue. `QueueRefill` retains the initialized-prefix executable reproduction;
[request 2](2026-10-14-campaign-2-mirror-requests.md#2-account-for-nested-queue-refill-in-activation-budgets)
gives the exact evidence boundary, source locations and altitude-preserving
correction requested. The user was notified. This is an evaluated model-prefix
finding, not an accepted-run termination counterexample or a kernel-reduction
theorem. Both JSON-based reduction and a typed-trace reduction were attempted;
the latter exposes the remaining non-reducing arithmetic-loop implementation.
No proof oracle or added assumption substitutes for that missing proof.

Ranked mirror requests are now (1) the missing batch completion check and
(2) a callback-aware activation bound, both altitude-preserving. A read-only
independent review confirmed the second source path and required the explicit
prefix-only qualification above. That qualification is incorporated in the
request and witness documentation. The full scheduler has two candidate proof
architectures: an erased dispatch/resume event observer, or source-factorized
single-turn execution followed by a bounded iteration relation. Neither is
claimed complete. Kernel-checked local contracts do not establish termination
of every transitive arithmetic loop or full dispatch/resume completeness.

The seven H5 statements pass scoped build, standard-axiom inspection and
stock kernel replay (`leanchecker --fresh Leanux.Proofs.WG.Progress.Statements`,
through the capped bundle). The
full gate was rerun and fails at the same inherited counter refinement; token
and import checks pass. The separate executable refill reproduction succeeds.

## H6 — Timer discipline (in progress)

[USER 2026-10-14] Resume the interrupted H6 work, then H5, remaining H4 and
H2 when its prerequisite landing is relayed. The interrupted dirty worktrees
were preserved under snapshot refs without moving branches or working files.

`TimerDiscipline/Arming` proves exact recorded arming, deletion, the
running/live guard, and peer effects of traversal, session derivation, data
receipt and handshake completion. `Jitter` proves that every successful
jitter draw is below `HZ / 3 = 83`, including the rejection loop, and frames
the entire kernel. Twelve terminal statements include the two authenticated
packet hooks that delete timers and the retransmit callback counter rule. The arm equation uses UInt64 addition and
the signed zero-or-one-tick admissibility gap; it is not a firing-time claim.
All contracts concern original functions on normal completion. They do not
assert that malformed record streams succeed.

`Retry` factors retry-mode queueing through the original common suffix and
proves the original retransmit callback's counter transition: counts through
18 increment, including 18 to 19; counts above 18 stay unchanged on give-up.
Normal completion preserves peer allocation identity and the retransmit-timer
field, including rate-limited/dead-peer returns and already-queued reference
balancing. The callback itself does not re-arm retransmission; the worker's
`timersHandshakeInitiated` hook does. Independent review found no issue.
This is not a completed 19-retry episode: scheduler detachment, actual worker
rearming and the reset paths still need composition.

The charter's wording needs these source qualifications, with universal
caller coverage still open: “re-arms on every authenticated traversal” means
at the traversal hook with nonzero interval, running device and live peer.
“Once per session” is the session-derived hook's guarded arm attempt; the
retransmit give-up path separately arms absent zero-key timers. The zero-key
callback queues clear work, rather than clearing keys synchronously. None of
these local endpoints proves the absence of other arming sites in a whole
runner execution. The literal once-per-session count remains unproved, not
silently replaced by the local theorem.

Architecture: standalone weakest-precondition contracts, with a local map
composition rule and exact peer-update factorization for handshake completion.
These avoid the inherited shared import failure; existing shared lemmas remain
untouched. Remaining work: all seven source arming sites with exact delay and
caller provenance, completed retry-episode counting, and source-complete caller
coverage for traversal and session derivation. No H6 mirror mismatch has been
established; ranked mirror suggestions: none.

Effort: capped elaboration, repaired syntax/composition errors and one local
heartbeat exhaustion; no memory-cap failure. Scoped build and axiom inspection
pass for all twelve statements using only the three standard axioms. Stock
kernel replay also passes: `capped -- scripts/in-bundle lake env leanchecker
--fresh Leanux.Proofs.WG.TimerDiscipline.Statements`. The full
proof gate remains failed at inherited `CounterWindow/Refinement.lean` and
`ReplayWindow/Counterexamples.lean`;
its token and import checks pass. No full-gate success or complete H6 result is
claimed. No mirror changes or guest runs.

Independent H6 review disposition: no mathematical defect found in the eleven
local contracts. Fixed the traversal docstring's “exactly when re-arms” wording:
the endpoint theorem does not observe arm-event occurrence when an old timer
was already present. Removed the jitter docstring's unproved exhaustion clause;
its proposition only covers normal completion. Added the source qualification
that `createDataDone` invokes traversal once per encrypted item/list, before
its per-packet send loop (`Data.lean:181–194`, C `send.c:242–260`), not once per
individual packet or necessarily a successful transmission. These corrections
change claims in prose, not theorem propositions. Whole-run event coverage and
failure characterization remain explicitly open.
