# WireGuard proof campaign 2

## Progress

Work is confined to `.worktrees/proofs-campaign-2`, branch `proofs/campaign-2`.
H1, H3 and H4 have local contracts; their whole-operation/whole-run claims
remain open. H5 has a checked batch-completion counterexample and open progress
obligations. H6 has eleven local timer contracts; whole-run site coverage and
retry/session counting remain open.
H2 is waiting on the index-lookup
dead-peer-store fix and the user's landing notice.
No result is claimed complete. The branch has carried main through ca6b22e;
that landing adds documentation and binary-validation scaffolding but leaves
the WireGuard mirror unchanged.

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

Twenty terminal declarations cover configuration leaves, peer flags, bounded
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
These two side-effect contracts concern normal completion; joining the loop
to the claim that every listed peer is cleared remains open.

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
found no defect. Actual outer dump composition remains open.

Remaining: running-port/socket and complete private-key effects, full peer
removal/replacement and allowed-IP ownership, other partial-error combinations,
and general dump chunks/coalescing. Deferred removal work can change other
peers' dynamic state, so no unrestricted removal frame is claimed. No H4
mirror mismatch or mirror-team request; ranked mirror suggestions: none.

Validation: all twenty statements pass scoped build, standard-axiom inspection
(only `propext`, `Classical.choice`, `Quot.sound`), and `capped --
scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Config.Statements`.
The full proof gate fails in inherited `CounterWindow.Refinement`; token/import
checks pass. Effort includes repaired proof-elaboration failures, including two
local heartbeat limits resolved by simplifying put calculations before their
continuations. No cap hit, infrastructure rerun, mirror edit, differential
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
the entire kernel. Eleven terminal statements include the two authenticated
packet hooks that delete timers. The arm equation uses UInt64 addition and
the signed zero-or-one-tick admissibility gap; it is not a firing-time claim.
All contracts concern original functions on normal completion. They do not
assert that malformed record streams succeed.

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
pass for all eleven statements using only the three standard axioms. Stock
kernel replay also passes: `capped -- scripts/in-bundle lake env leanchecker
--fresh Leanux.Proofs.WG.TimerDiscipline.Statements`. The full
proof gate was run and fails at inherited `CounterWindow/Refinement.lean`;
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
