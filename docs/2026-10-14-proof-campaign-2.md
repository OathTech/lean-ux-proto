# WireGuard proof campaign 2

## Current checkpoint

Work is on `proofs/campaign-2` in `.worktrees/proofs-campaign-2`, over mirror
`de62c9d`, Lean v4.35.0. It is **lagging main's representation batch
`cb2348e`**; no merge or push has occurred during this resumption.
**None of H1–H6 is complete.** Scoped validation passes; the full proof gate
remains failed in inherited campaign-1 files.

| Result | Headlines | Established checkpoint | Still open |
| --- | ---: | --- | --- |
| H1 Noise | 20 | State/slot contracts, ordered clearing and rotation, static release budgets, full normal session effects and consecutive first-match confirmation | Whole-call edge coverage, session totality, exposed derivation-clock provenance, allocation-lifetime confirmation |
| H2 Index | 48 | Exact index operations, original caller table safety, successful session publication coherence | Reachable store/slot/owner coherence, wider record layouts, corpus runner composition; outer-removal frames await decision |
| H3 Roaming | 9 | Data publication/first-poll join and response-caller authentication at the actual pre-setter cut | Initiation, failed-call prefix retention, general queue/caller coverage, final endpoint preservation |
| H4 Configuration | 64 | Configuration leaves/flags, bounded public readback, port/fwmark/key effects, allowed-IP removal and live-key peer removal | Collision and queued-work removal, mixed attributes, ownership and general multipart readback |
| H5 Progress | 32 | Historical backlog counterexample, source-connected scheduling inspections, cut/pow/drain bounds | Whole-worker record decrease, full operation-end coverage and global termination/progress |
| H6 Timers | 35 | Local arm/delete rules, recorded delays, actual retry/send pairs and consecutive same-peer count bound | Complete caller/site coverage, scheduler episodes and session-relative arm counting |

Total: **208 headlines**. The factoring checkpoint `69f988a` preserved all 153
then-existing headlines. Recent mathematical checkpoints include `3bf25a9`
(H3 response), `bfd6f76` (H2 coherence) and `420c419` (H5 drain);
`64d23eb` removes only an extra EOF blank line.

[USER 2026-10-15] Resume before the split lands; factor claims over a
WireGuard-only view and separate frames, then continue the charter. On the
eventual split, delete frames made trivial or unstatable and retype substantive
claims. No shared-layer edits, merge or push. This supersedes the earlier pause
at `aeece72` and earlier authority to merge the index fix, which already landed
on this branch at `de62c9d`.

[USER 2026-10-15] Shared layers remain campaign 1's. Necessary local variants
must be named for the shared lemma and live in result directories. Report an
overlap larger than “a few” before copying it. The
[six-family outer-removal request](2026-10-15-campaign-2-shared-frame-request.md)
is **pending**; those variants have not been implemented.

[USER 2026-10-14] Write mirror-team requests in this tree and notify the user.
The [three existing requests](2026-10-14-campaign-2-mirror-requests.md) have been
reported; no new request arises from the latest increments.

[AGENT 2026-10-15] Use a genuine WG data projection and a separately named
ambient context, with universal execution contracts over concrete realizations.
Keep normal return, total return and exact outcomes distinct. Observations start
at the actual same entry and compose through actual successors; independent
existential runs are never spliced. Inspection totality is not original-operation
success. Public statements name neither `World` nor `Kernel`.

### Claims, frames and the split boundary

Paths below are under `Leanux/Proofs/WG/`; `.lean` is implicit. Public claims
remain the six result `Statements` modules. Their concrete source proofs are
connections to the current executable mirror, not replacement interpreters.

| Area | Data / claims / source connections | Separate frame support |
| --- | --- | --- |
| Common C2 | `Campaign2/View` is data-only; `Campaign2/Bridge` defines projection and universal execution contracts. | No shared campaign-1 layer is changed. |
| H1 | `Noise/Model`, `Statements`, `Slots`, `StateEdges`, `ConsumeEdges`, `ClearModel`, `ClearEffects`, `ClearSource`, `RotationModel`, `RotationEffects`, `RotationSource`, `SessionModel`, `SessionSource`, `ConfirmationSequenceModel`, `ConfirmationSequenceEffects`, `ConfirmationSequenceSource`; `Execution` holds the concrete monad connection; `AccessSource` holds accessor read/write contracts, reexported by `Basic`. | `KernelFrames`, `PeerFrames`, `SlotFrames`, `ClearFrames`, `RotationFrames`, `SessionFrames`. |
| H2 | `Index/View`, `TableModel`, `OwnerWordModel`, `AllocationModel`, `ReleaseModel`, `LifecycleModel` and pure release effects/bounds; `Statements`, `HandshakeClaims`, `OwnerUpdateClaims`, `LifecycleSource`, `LinkSource`, `SendSource`, `DispatchSource`, `ResponseSource`, `ConsumeSource`, `StagedSource`, `ReceiveOperations`, `ReceiveSource`, `ClearSource`, `TimerSource`, `FlushSource`, `SessionCoherenceModel`, `SessionCoherenceEffects`, `SessionCoherenceSource` and the other operation/source modules. | `IndexFieldFrames`, `OwnerFieldFrames`, `StoreFieldFrames`, `LifecycleFrames`, `NewlinkFrames`, `SendFrames`, `DispatchFrames`, `ResponseFrames`, `ConsumeFrames`, `StagedFrames`, `ReceiveFrames`, `ClearFrames`, `TimerFrames`, `FlushFrames`, `SessionCoherenceFrames`; the old `HandshakeFrames` and `OwnerFrames` paths are import-only reexports, not duplicated lemmas. |
| H3 | `Roaming/Model`, `View`, `Statements`, `EndpointClaims`, `EndpointSource`, `Authentication`, `PublicationModel`, `PublicationSource`, `PublicationClaims`, `PollEndpointModel`, `PollEndpointSource`, `PollEndpointClaims`, `ResponseModel`, `ResponseCryptoSource`, `ResponseConsumeSource`, `ResponseLookupSource`, `ResponseCallSource`, `ResponseCallClaims`. | `Roaming/Frames`, `PublicationFrames`, `PollEndpointFrames`; `Basic` reexports the endpoint source connection. The response increment needs no new frame support. |
| H4 | `Config/Model`, `AllowedRemovalModel`, `AllowedPairsModel`, `AllowedPairsEffects`, `AllowedRemovalConverseSource`, `AllowedRemovalConverseClaims`, `QuietModel`, `LiveRemovalModel`, `LiveRemovalSource`, `ClaimView`, `Statements`, `SourceClaims`, `ObservationBridge`, and existing substantive effect/source modules. | `ConcreteFrames` isolates six whole-kernel endpoint contracts; `OperationFrames` isolates seven generic helpers; `ReadbackFrames` retains socket/fixture preservation; `AllowedListFrames`, `AllowedRootFrames`, `AllowedRemovalFrames`, `AllowedPairsFrames`, `QuietFrames`, `LiveRemovalFrames`, `KeyFieldFrames` isolate within-WG preservation. |
| H5 | `Progress/Model`, `View`, `Statements`, `SourceClaims`, `ObservationBridge`; `ControlLaws` is generic state/error control and `ControlSource` connects it exactly to the original worker; the scheduler/source modules retain actual execution factors. `CutModel`, `CutSource` and `CutClaims` establish original cut-loop progress; `FlushQueueModel`, `FlushQueueSource` and `FlushQueueClaims` establish original flush effects and count decrease; `PowModel` and `PowSource` connect a finite evaluator to the original arithmetic loop. `DrainModel`, `DrainOperations`, `DrainSelectionSource`, `DrainAuditSource`, `DrainEffects` and `DrainClaims` connect a phase audit and queue bound to the original workqueue drain. | `StackFrames` isolates caller-guard preservation; `CutFrames` isolates record/error-location preservation; `FlushQueueFrames` isolates queue preservation through worker bodies and release. Probe/filter/no-work contracts also establish outputs and remain substantive source claims. |
| H6 | `TimerDiscipline/Model`, `View`, `SendView`, `Statements`, `ObservationBridge`, `ObservationClaims`, `SourceClaims`, `SendDispatchModel`, `SendDispatchClaims`, `RetryDispatchModel`, `RetryDispatchClaims`, `RetryRearmModel`, `RetryRearmClaims`, `RetrySequenceModel`, `RetrySequenceClaims`, and `*Source` operational proofs. | `SourceFrames`, `RecordedFrames`, `RecordedJitterFrames`, `SectionFrames`, `SelectionFrames`, `RetryFrames`, `JitterFrames`, `InitiationFrames`, `InitiationPreservationFrames`, `SendCutFrames`, `SendPeerFrames`, `SendSocketFrames`, `SendBufferFrame`, `SendWorkerFrame`, `SendDispatchFrames`, `RetryDispatchFrames`, `RetryRearmFrames`, `WorkStateFrames`. |

A compound exact effect is not a disposable frame merely because its name
contains “frame”: mark/generation updates, cleared-peer accumulation, reference
decrements and dump/UDP payload results remain substantive claims. The seven
H4 dump/UDP helpers with arbitrary kernel predicates are concrete source
contracts that also establish outputs. After the mirror split, delete only
structural preservation made trivial or unstatable; retain and retype those
outputs and meaningful within-WG preservation. H6's reference-decrement proof
is therefore in `SendWorkerSource`, separate from send preservation.

## H1 — Noise session state machine

The original state-edge, slot, clearing, rotation, confirmation and session
contracts are checked. Create/consume initiation can restart from any prior
state; the claim is the code's edges, not a single linear handshake. An
initiator with an existing next key demotes that next key to previous and puts
old current; without next it demotes current. Responder installation goes to
next. Slots are optional values, not a bound of three on the entire key store:
outstanding packet references can retain keys.

`ClearRun`, `RotationRun` and `ConfirmationEffect` preserve exact ordered
writes, puts, unhashing, reference changes and possible erasure. Normal effects
derive their execution evidence from the original call. Separate total-return
contracts use static `ClearReady`, counting every repeated release. Aliases are
allowed; no owner/peer equality, global reference ownership or fresh allocation
is silently assumed.

`SessionEffect` covers the complete original `beginSession`. False returns
preserve Device and allocation counter even if records were consumed. True
returns derive the accepted tag, live peer, non-NULL handshake peer word,
counter increment, allocation overwrite, role/remote-index and KDF fields,
handshake zeroing, ordered rotation and actual hashed-handshake replacement.
Birthdate remains existential; exposed derivation-clock provenance is open.
H4's expiry contracts supply slot validity, zero/unhash and actual reset-clock
observations without duplicate H1 proofs.

This does not establish retained-slot residency. For example, old next=current
may name a key with one reference and a non-NULL peer word, with previous empty.
Initiator rotation demotes next and releases current, leaving previous naming
the erased key. Confirmation can similarly release an old previous alias of
the received key. These are local invariant boundaries, **not accepted-run
findings**. Live-slot coherence belongs at completed rotation cuts, not every
primitive assignment.

The actual finite `ids.mapM (receivedWithKeypair pid)` sequence now has normal
and total contracts. On normal return, the first input matching the initial next
slot is the sole true result and supplies the exact single `ConfirmationEffect`;
all other calls return false. If nothing matches, the device is unchanged.
Result length is preserved. Normal effects need only the initial resident peer;
total completion adds `ClearReady d [p.keypairPrevious]` only when some input
matches the initial next slot. Later duplicate IDs remain allowed, and a match
leaves next empty. These are consecutive calls without another installation,
not confirmation once per allocation lifetime.

Whole-run edge ownership, session totality, reachable allocation/slot coherence
and confirmation once per allocation lifetime remain open. Exact source-call
observers with event completeness and structural execution derivations were
both considered; equal endpoints cannot justify an empty event history.
Campaign 1's existing snapshot omits the required tags/slots.

## H2 — Session index uniqueness

[AGENT 2026-10-15] Interpret “no two live sessions share an index” as no two
**simultaneously hashed receiving-index owners within a device** sharing it.
Unhashed objects retained by references do not reserve their former number.
The C unhashes before release and does not clear the stale numeric field
(`noise.c:131–139`, `peerlookup.c:192–197`); insertion tests currently hashed
entries (`peerlookup.c:119–163`). In the mirror, local ownership is in
`Device.indexTable`; `remoteIndex` is the separate peer-supplied namespace.
This is a source-grounded statement clarification, not a mirror counterexample.

Numeric-index uniqueness and embedded-owner uniqueness are separate invariants.
Owner identity and its optional peer word are also distinct. Lookup stops at
the first equal index, including a disallowed kind. Returned ownership comes
from that original row; matched-entry contracts cover NULL, zero-reference
store-back of NULL, and bounded positive-reference acquisition. They require
the relevant owner/peer residency; absent/disallowed rows have separate total
contracts. No owner=referenced-peer equality is assumed.

Removal, specialized keypair removal, replacement, allocation and release have
exact contracts. The landed keypair removal operation is
`indexRemove (.keypair id)`, not a separate declaration. Replacement preserves
numeric indices; owner uniqueness additionally needs a fresh destination owner.
Insertion first removes the old owner row and then installs a fresh index.
Recorded-collision results retain their contiguous draw/layout hypotheses,
arbitrary suffixes, retries and exact exhausted-stream error. The corpus-draw
two-call instance does not constitute general runner coverage. Errors expose
no final state.

`TablesSafe` combines both uniqueness properties with the hashed-key-owner
allocation bound. It is preserved on normal return through original lifecycle,
creation/deletion, initiation/response sending and consumption, staged/keepalive
sending, handshake reception, receive iteration, clear workers, timer dispatch,
workqueue draining, timer stop and post-death removal. These contracts do not
promise readiness or completion.

The session-coherence headline combines the exact H1 effect and table invariant
from the same original run. With an initially resident caller, a self handshake
peer word and exclusion of the allocation ID from its actual rotation releases,
a true return leaves the key resident with one reference, places it in the
role-selected slot and uniquely publishes it at the former handshake index.
Other aliases and overwriting an unhashed object remain allowed.
`TablesSafe` bounds hashed owners, not every stored key or live slot; these
static premises are not yet reachable invariants.

Whole-driver coherence, reference/slot lifetimes, broader record layouts and
runner composition remain open. Outer `peerRemove`/`peerRemoveAll` table closure
awaits the documented six-family decision; no workaround copies that layer.

## H3 — Endpoint roaming

[AGENT 2026-10-14] “Endpoint changes only” means remote roaming:
family, address, port and IPv6 scope. Local source caches legitimately change
during routing/clearing, and `endpoint_eq` ignores flowinfo. Full-record
get-after-set is not claimed; `n1_flowinfo_only.json` exercises the distinction.

Source conversion and original endpoint setters are checked. Authentication
requires actual consume/AEAD evidence, not tag endpoints or MAC admission alone.
The outer source address is not an AEAD input. Data roaming occurs before later
inner-packet checks; these contracts do not assert delivery.

For a CRYPTED publication, the decrypt publication cut retains actual AEAD
plaintext and historical key provenance before the original callback; dead
publications do not assert plaintext provenance. The first-poll endpoint cut
includes the original budget and an actual true counter-check result, not a
proved counter-window invariant. Their join is from the same execution
and conditional on matching the actual packet identity. It neither supplies a
general queue invariant nor assumes packet-peer/key-owner equality. Softirq and
stack callbacks remain arbitrary; there is no final endpoint or scheduler claim.

For response-kind packets, exact source and decorated-observation equations
connect the full original caller to the actual pre-setter cut. A missing cut selects a
pure suffix; a present cut invokes the setter immediately and retains session,
timer, keepalive, statistics and release continuations. For a present cut on
normal full return, the contract derives actual under-load/MAC admission,
separately recorded owner/reference,
same-entry lookup, both DH checks, exact derived AEAD key/AAD, empty plaintext,
and consumer state recheck/commit. Cutting before the setter matters because
its later cache-reset read can fail after the endpoint write.

Initiation coverage, retained prefix evidence after failed full calls, general
queue provenance, netlink/whole-run caller exclusion and final endpoint
preservation remain open. Forged crypted packets in arbitrary states are not
accepted-run findings. Exact consume transcripts were chosen over a larger
crypto-dataflow frame layer; no new shared variants were needed for the response.

## H4 — Configuration semantics

[AGENT 2026-10-14] Get-after-set means the effective configuration: private-key
clamping, allowed-IP masking, an allocated zero port and ignored flowinfo follow
the C's operations. Set is not transactional: earlier updates survive a later
parse error. The claims retain those outcomes rather than asserting raw-input
identity or rollback.

Checked leaves include validation/flag errors, absent remove/update-only and
self-key no-ops, removal precedence, identity and cookie precomputation, peer
scalars and expiry. The bounded public readback composes scalar set with the
original getter, including a later malformed entry: one resident peer on a
stopped device, a positive reference count with its temporary increment below
2^31, matching public-key and interface selection, no allowed IPs, sufficient
chunk room, and idle socket 7 with an empty queue. A fixed peer dump needs at
least 168 bytes; the complete getter additionally budgets device and nest
overhead. General multipart dump composition is open.

Port effects distinguish stopped devices, existing creating namespaces,
unchanged ports, nonzero replacement and zero-port allocation. Supplied-record
zero-port return/collision contracts retain their explicit draw assumptions.
An occupied first recorded candidate is an outside-domain stop, not ordinary
bind failure or proved retry. Bind failure retains preceding source/cache
clears; equal outer-port requests still increment generation. Fwmark effects
preserve remote destinations while clearing source/cache fields; reset
timestamps remain existential, including duplicate-list effects.
Private-key installation composes identity/cookie keys with ordered per-peer
precomputation, expiry and optional staged sending; full outer effects cover
the noncolliding request. Normal-return effects are not completion guarantees.
Existential expiry timestamps and actual reset-clock observations remain
separate contracts. The unchanged-key arm compares raw requested bytes with
stored clamped bytes.

[AGENT 2026-10-15] Compose private-key updates from a baseline after optional
self-peer removal: removal may flush other peers’ work under the old identity,
so an unrestricted surviving-peer frame against request-entry state would be
false. Prove the key-only block before composing later peer attributes.

Allowed-IP removal has total contracts under supplied `RemovalEffect` witnesses
and normal converses deriving those witnesses from an initially resident named
peer under `NodePairs` (every resident node has two child slots). This is a static representation condition, not proved
reachable trie validity, ownership or acyclicity. Peer death removes list/public
identity membership and sets deadness. Live-key removal admits aliases under
multiplicity-aware release budgets, positive peer references/count and empty
send/clear work queues. The outer total removal still takes a supplied
`RemovalEffect`; the after-death contract additionally requires initial deadness.
The final release may retain a dead peer when references remain. The normal
converse does not import these totality premises.

The cancelled-nest finding below is internal accounting, not a demonstrated
output mismatch. Private-key collision removal, queued-work removal, mixed
attribute composition, global ownership and general getter round trips remain
open. The actual predecessor-state removal relation was retained rather than
postulating an independent operational witness for the converse.

## H5 — Termination and progress

The literal no-pending-at-completion claim is historically refuted on this
branch by the accepted constructed batch-backlog witness below. The remaining
proofs distinguish original executions, generic worker laws and total
inspections. Probing an activation does not establish successful execution after
detachment; scheduler claims retain actual dispatch/resumption, NAPI and
caller-stack busy/idle/error branches. Nested callback refill remains an
obstacle to the old queue-occupancy bound.

The recorded cut proof derives its budget before ambient stripping and includes
the final empty/non-cut observation. Prefix-only allocation acceptance gives
total return; allocation rejection keeps its exact original stop. Original
send/clear flush effects erase one matching queue occurrence, allow duplicates
and retain final reference release, including peer deletion.

The whole-drain audit has unconditional exact correspondence with the original
4096-turn drain, preserving selection priority, hidden/placeholder behavior,
all errors and successful final state. It is an inspection at unchanged entry,
with the original outcome inside its datum. Below 4096 initial queued items,
actual selector membership and original flush effects bound loop turns begun
by count+one and exclude only the drain's own exhaustion. Selector/worker errors
are tagged by their actual call, not their text, and have no final-state field.
Normal completion with `upTo = none`, under the stated resident-device and
queue-count entry premises, leaves both queues empty; requested-clear completion
may leave other work. Exactly 4096 removals leave no extra turn to
observe empty queues: this is a source boundary, not an accepted witness.

The original modular-exponentiation loop has a finite evaluator with sufficient
fuel `e + 1`, proved by its checked fixed-point equation and induction. Zero
exponent and zero modulus preserve the original behavior: it returns 1 at
exponent zero even modulo 1, so unrestricted equality with stock `Nat.powMod`
would be a statement artefact. This is local operational adequacy, not an
algebraic, compiler or whole-run theorem.

Whole-worker record decrease, full operation-end coverage, detached-activation
progress and global termination remain open. No successful drain/dispatch or
complete scheduler run is inferred from total inspection.

## H6 — Timer discipline

Local contracts cover the original arm/delete guards and all seven concrete
arming sites, exact wrapped caller-read-plus-delay equations, traversal/session/
data/handshake hooks, and jitter below 83. Recorded arming uses the actual caller
read and arm record; arm-record mode may still permit placeholders. The separate
finite supplied-record jitter success/exhaustion claims require contiguous
rejected/accepted records and exclude ambient interleavings/placeholders. No
distribution claim is made.

Persistent keepalive remains conditional on its interval and running/live
guards. A final timer value alone does not prove an arm event occurred.
`createDataDone` invokes traversal once per encrypted item/list before its
per-packet send loop (`Data.lean:181–194`, C `send.c:242–260`), not once per
individual packet or necessarily a successful transmission. Zero-key firing
queues asynchronous clearing; it does not immediately prove key erasure.

The exact original timer/send pair starts with a resident device and empty
send queue. Successful selection derives the same peer, retry eligibility,
entry attempts at most 18, fresh enqueue/reference acquisition and timer detach.
The callback increments attempts; the worker preserves that count, releases the
acquired reference and leaves an empty queue and false pending flag. This is
not a proof of global reference ownership or network transmission.

Conditional rearming uses the actual before-arm state, its running/live and
arm-record conditions, actual caller read and bounded jitter. Exact expiry
survives retained release and section stop; the clock-gap conclusion stays at
its established pre-release cut. Consecutive successful pairs use adjacent
actual states. When all select the same initially resident peer, attempts grow
by their length and a nonempty sequence is bounded by 19 from zero. This
excludes 20 such successful pairs, not a twentieth timer callback. An empty
sequence preserves the whole snapshot.

Complete traversal/session caller coverage, scheduler retry episodes and
whole-run arm-site/session counting remain open. The give-up path also arms
zero-key material; one syntactic session hook cannot prove once-per-session.
No H6 mirror mismatch has been established.

## Findings and mirror requests

All requests are in the [mirror-team document](2026-10-14-campaign-2-mirror-requests.md).
The mirror and kernel were not edited. No finding has been classified as a
kernel defect or sent upstream.

| Finding | Evidence and limit | Status / ranked change |
| --- | --- | --- |
| H5 batch backlog | Kernel-checked accepted constructed fixture trace, plus separate replay summary. Not a captured Linux run. | Historical over `de62c9d`; main `9db558b` adds the completion guard. Carry and corrected-refusal proof remain pending. H5 request 1, altitude-preserving. |
| H5 nested queue refill | Evaluated initialized prefix and source review; operation 4 reaches the worker occupancy-budget invariant, with later suffix incomplete. Not an accepted complete trace or kernel-proved prefix. | H5 request 2: callback-aware activation bound, altitude-preserving. |
| H4 dump cancellation | Accepted getter and kernel-checked internal room 3720 versus source-derived C room 3724. Concrete empty-list case; dead-cursor extension is inspection only. No demonstrated compared-output difference. | H4 request 1 (document request 3): restore pre-nest cancellation snapshot, altitude-preserving. |

Other local alias examples, the 4096-turn boundary and statement-domain
qualifications are not accepted-run findings. H1, H2, H3 and H6 have no ranked
mirror-change request at this checkpoint.

## Validation, effort and trust limitations

All headline declarations use only `propext`, `Classical.choice` and
`Quot.sound`; structural/token checks pass. Source factoring, ordered effects,
WP composition and finite induction were used without changing mirror
definitions. Ordinary elaboration/normalization failures were corrected;
their detailed iterations remain in commit history, not duplicated here.

Latest affected checkpoints have scoped builds, headline axiom inspection,
fresh stock kernel replay and independent review. H1 confirmation sequence:
140 build jobs and 20 headline checks; H3 response: 59 build jobs;
H2 coherence: 206; H5 drain: 196, with 32 headlines plus four exact-source
equations checked. H5's public-scope finding was fixed by making exact
correspondence unconditional and confining the queue bound to the progress
conjunct; the changed interface was rebuilt and replayed. Its staged EOF
whitespace finding was corrected in the next commit. H4's 64-headline and
H6's 35-headline results also retain their recorded scoped/replay checks;
later shared C2 spine changes were checked in affected H2/H5/H6 runs.
The six-target scoped build passes together (336 jobs), with existing unused-simp
and deprecated-tactic warnings. Combined inspection covers all 208 headlines. This does **not**
constitute a passing full gate.

The full gate was last actually run at `69f988a` and **failed** in inherited
`WG/CounterWindow/Refinement.lean` and `WG/ReplayWindow/Counterexamples.lean`
(counter operands and index-owner carries). Campaign 1 owns those repairs.
No existing shared lemma was edited.

**Exactly one infrastructure rerun**, at `84355d1`: a combined import overlapped
an active rebuild and found `ReceiveFrames.olean` absent. One retry after
confirmed build completion passed. Source corrections and parsing the same
wrapped axiom output are not infrastructure retries. There have been no memory
cap hits, cap increases, guest runs or guest timeouts.

A bounded read-only trial kernel-checked one original
`curve25519 (List.replicate 32 17) basePoint` equation through the finite
evaluator bridge (`decide +kernel`, about 0.334 s, standard axioms). Candidate
bytes from ordinary evaluation were not proof. The **single reduction trial of
`executeTrace QueueRefill.concreteTrace` failed**, exit 1, at stock simplifier
step exhaustion, using the checked original-pow rewrite. This was capped stdin
with 32 threads, unchanged limits and a 120-second trial budget. Its
failed recovery declaration printed `sorryAx`; no theorem or source file was
obtained or committed. There was no retry, timeout, limit increase or rebuild.
This does not show the target equation false or establish full-prefix throughput.

Stock trust-surface annotations are recorded explicitly: `repeatM` uses
`implemented_by repeatM.erased`, and stock `Nat.powMod` has an external
implementation annotation. The finite proof uses logical definitions, a checked
fixed-point equation and induction, not those executable overrides as oracles.
No project axiom or forbidden trusted-code declaration was added.

Reproduce scoped validation with the six targets (default memory cap unchanged):

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build \
  Leanux.Proofs.WG.Noise.Statements Leanux.Proofs.WG.Index.Statements \
  Leanux.Proofs.WG.Roaming.Statements Leanux.Proofs.WG.Config.Statements \
  Leanux.Proofs.WG.Progress.Statements Leanux.Proofs.WG.TimerDiscipline.Statements
# Print every headline's axioms; inspect that only the three standard axioms occur:
python3 - <<'PY' | LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake env lean --stdin
from pathlib import Path
import re
areas = ['Noise', 'Index', 'Roaming', 'Config', 'Progress', 'TimerDiscipline']
for area in areas:
    print(f'import Leanux.Proofs.WG.{area}.Statements')
for area in areas:
    source = (Path('Leanux/Proofs/WG') / area / 'Statements.lean').read_text()
    namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
    for name in re.findall(r'^theorem (\w+)', source, re.M):
        print(f'#print axioms {namespace}.{name}')
PY
# Replay each module separately; leanchecker --fresh accepts one module:
for area in Noise Index Roaming Config Progress TimerDiscipline; do
  LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake env leanchecker --fresh "Leanux.Proofs.WG.$area.Statements" || exit $?
done
# Full gate: expected inherited failure, not reported as a scoped pass:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The gate already supplies the headline discovery/axiom-check procedure; no
additional audit infrastructure was introduced. After the split lands by paste,
retype claims and delete structural frames that the new types make unnecessary.
