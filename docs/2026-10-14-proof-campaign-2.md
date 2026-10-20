# WireGuard proof campaign 2

## Namespace-pin closure, 2026-10-20

The branch is rebased onto main `ac55c7d5`, including shared namespace-pin
carry `7f89077d` and integration record `66188b74`, over mirror `218d3ffd`.
The earlier fixed-width carry is already on main with the shared repair at
`eba3c2b6`. No mirror or shared-layer change is made here.

Request 5 is closed. Its original JSON is retained as a refusal regression:
both parser and validator now exclude the fixture's literal pin descriptor.
Direct typed execution, which bypasses parsing, and the exact boundary audit
both refuse at operation 1 before teardown because no cleanup was queued.
The recipe no longer exercises the later operation-end pending guard.

H5's `RunnerBoundaryClean` is strengthened to unconditional pending-unit
emptiness. The existing `original_accepted_operation_boundaries` composition
then covers every cut of every accepted typed trace in either record mode,
including negative syscall returns. No parser-validity or entry-invariant
premise is added. The theorem applies beyond the parser's stated domain;
queue emptiness, scheduled NAPI and budget adequacy remain separate claims.
The source equations preserve the native hidden-record and invariant Stops.

The three isolated source adaptations are subsumed by the landed carry:
`Progress/RunnerFiniteSource` already has the same unconditional completion
guard, and `Noise/PendingEnvironmentSource` and
`Index/LifecycleCleanupRuleSource` use its proved cleanup walk. The latter
two unfold the pending-device query before walking its reads, so the local
query-head branches and their extra imports are redundant and removed.
Their statements are unchanged; the Noise cleanup docstring is corrected.
The boundary-audit overlap keeps the landed proof formatting. All six results
are current over mirror `218d3ffd` against the shared carry, with H5's
stronger boundary predicate and refusal recipe retained. The three former
WIP source adaptations are validated in their landed form.

Aggregate validation passes: `scripts/proof-gate` completes all 3,141 build
jobs and checks 1,774 terminal declarations across 15 root modules; only
`propext`, `Classical.choice` and `Quot.sound` occur. The forbidden-token and
import/target checks pass. `scripts/proof-counterexamples` passes all 15
recipes, including the retained H5 refusal regression. This supersedes the
previous inherited build/import failures. The earlier four scoped boundary
axiom checks and three existing fixture-validator tests also passed.

Reproduction commands:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-counterexamples
```

Both aggregate commands exit zero. The existing memory cap is unchanged;
there were no compiler warnings, KILLED banners, guest timeouts or retries.
All six result directories retain grandfathered Lean resource-limit settings;
this carry changes none, and none of its edited Lean files contains a raise.

The six summaries below describe the landing scope, with H5's pending-unit
clause strengthened over `218d3ffd`, and supersede broader completion wording
in the dated history. The
[independent landing review](2026-10-20-review-campaign-2-landing.md) requires
no new theorem. Claims use the campaign projection, frames are separate,
and the mirror is unchanged. Observer erasure preserves original outcomes;
coverage of all relevant observation sites rests on source construction and
review, not an independent completeness theorem.

## H1 summary — Noise state machine

Architecture: tag-edge and slot models connect to native operation contracts;
allocation-stamped confirmation journals compose through the initialized
runner. `original_initialized_driver_tags` proves whole-run tag ownership;
`original_initialized_confirmation_unique` concerns successful completed
confirmations, including prefixes before an outer Stop. Rotation, confirmation,
expiry and clearing have per-function contracts. One keypair per slot follows
from the three Option fields; they may alias or name absent keys.

Wording pairs: “all state/slot transitions occur only at the owning functions”
becomes whole-run tag-edge ownership plus local slot effects, with no whole-run
slot-write discipline theorem. “Confirmed exactly once per keypair” becomes
at most once per allocation `internalId` among successful completed consume
receipts; it asserts neither existence nor confirmations inside a stopped
consume. “Unique by raw store key across recreation” is refuted and replaced
by uniqueness of the persistent allocation stamp. Local fresh-history variants
retain their named freshness bounds and finite operation language; they are
not unrestricted driver claims.

The [recreation recipe](2026-10-18-proof-campaign-2-confirmation-incarnations.md)
confirms raw slot 0 twice with stamps 1 and 2. This is a statement artefact,
not a mirror defect; the counterexample remains alongside the corrected
identity theorem. Effort: 1,597 theorems, 75 headlines, 279 modules, including
projection retrofit and whole-run composition. Ranked mirror changes: none
requested; identity already exists in the mirror. Shared source factors and
local proof decomposition provide the needed support without changing altitude.

## H2 summary — Session index uniqueness

Architecture: local index source equations and reference/slot accounts establish
numeric and owner uniqueness, hashed-slot coverage and store bounds. The account
is carried through actual callers to normal initialized endpoints, with no
entry-invariant premise on `original_initialized_index_tables`. Lookup has its
own native contract. Collision retries are proved locally in supplied-record
mode; the illustrative collision composition is not an accepted runner trace.

Wording pairs: “no two live sessions share an index” is indexed-entry uniqueness
at normal initialized endpoints; unindexed stale fields are not live local
indices. “Every collision retries as C does” is a local records-mode insertion
contract, not an occurrence theorem for insertions throughout accepted traces.
“Local hashed-owner coherence suffices for preservation” becomes a reachable
account that also relates slots, allocation cursors and owners. Stopped final
states and every intermediate boundary are not covered.

The [persistent-owner witness](2026-10-17-proof-campaign-2-persistent-owner.md)
uses mismatched caller/keypair owners; the [session-alias witness](2026-10-17-proof-campaign-2-session-alias.md)
puts a newly allocated key through a dangling previous slot, then publishes a
dangling row. Both refute insufficient arbitrary-state invariants, not initialized
execution. “Positive reference implies peerPut returns” was corrected to exact
success/refusal under the same premises: [queued-work and pending-timer witnesses](2026-10-17-proof-campaign-2-peer-release.md)
force final-release Stops. Effort: 1,532 theorems, 162 headlines, 428 modules.
Ranked mirror changes: none open; the earlier index-owner lookup correction
was an altitude-preserving prerequisite already landed before these claims.

## H3 summary — Authenticated endpoint provenance

Architecture: failure-retaining handshake setter attempts and ordered data checks
compose with a latest-setter journal through the initialized runner. Every
observed committed handshake attempt has successful MAC/consumer checks; every
observed data check has earlier decrypt/configured-session authentication.
Normal final remote endpoints have a latest configuration or authenticated
packet setter, with the packet's source and no later setter/reset for that
location. The outer source address is copied, not cryptographically bound.

Wording pairs: “an unauthenticated datagram never moves an endpoint” becomes
authentication of the observed setter attempts/checks plus normal final
latest-setter provenance. This is not a theorem about every physical endpoint
write; a transient change later undone is not excluded by these headlines.
“The endpoint is that packet's source” retains same-packet source equality
for the authenticated provenance witness. “Complete caller coverage” means
the reviewed observer placement, with proved erasure and occurrence relations
inside that construction, not a separate proof that no source site is omitted.

No new mirror or kernel finding was established in this result. Equal-value
setter attempts and attempts followed by Stops remain represented. Peer survival,
cached local source fields and final states after Stop are outside the claim.
Effort: 1,305 theorems, 45 headlines, 266 modules, covering local authentication,
caller composition and final provenance after the state split. Ranked mirror
changes: none requested; the remaining distinction is claim scope, not a
proposal to alter the mirror or add a premise to hide a discrepancy.

## H4 summary — Configuration contracts and readback

Architecture: ordered mixed-request receipts and ownership accounts connect
actual setter stages to a bounded multi-message getter and its proof-side JSON
serialiser. Device fields relate to the request; peer scalar agreement is
one-directional for surviving actual cells `(internalId, psk, keepalive,
endpoint)`. The initialized getter theorem is separate from set-then-get.

Wording pairs: “a dump after a set reflects the set” becomes mixed scalar
readback under `OwnerConfiguration.ProjectedEntry` and explicit readability,
capacity, freshness, reference and receive bounds. No headline derives that
entry invariant from initialization for the composed setter/getter. Expected
peer creation/removal completeness, public keys, allowed IPs and protocol
version are not in this mixed peer agreement. “Replace-peers semantics” has a
flag-only replacement contract, not arbitrary mixed replacement completeness.
“The allowed-IP removal flag” is recast as peer `REMOVE_ME` and
`REPLACE_ALLOWEDIPS`: Linux 6.12 exposes no per-allowed-IP removal flag.
Port, fwmark and private-key effects retain their concrete source contracts.

Historical corrections retain counterexamples: “already pending means no new
handshake queueing” becomes the actual queue-record-dependent effect
([duplicate queue witness](2026-10-17-proof-campaign-2-queued-handshake.md));
“resident-peer removal returns” becomes exact refusal or successful cleanup
under the same domain ([scheduled-NAPI witness](2026-10-17-proof-campaign-2-removal-carry.md)).
Effort: 2,084 theorems, 217 headlines, 594 modules. Ranked mirror changes:
no open H4 request; rank 1 was restoring pre-header nest cancellation tailroom
([request 3](2026-10-14-campaign-2-mirror-requests.md#3-restore-pre-nest-tailroom-when-cancelling-the-device-peers-nest)),
fixed at `3f3879e0`, altitude-preserving. No stronger readback is claimed here.

## H5 summary — Finite evaluation, service and pending-unit completion

Architecture: finite replacements for nonstructural loops compose to exact
`executeTrace` equality; committed dispatch/resume receipts preserve failures.
Normal accepted runs have normal receipts, and a receipt with supplied records
at its own entry strictly consumes them. The staged Prefill bridge solved the
conversion blocker without increasing Lean limits on that finite-evaluation path.
The exact operation-boundary audit now proves pending-unit emptiness in both
record modes and accounts for every operation, in order.

Wording pairs: “every operation terminates” is finite evaluation preserving
all results and Stops, including exhausted budgets; it is not general fuel
adequacy. “Dispatched/resumed work runs” has actual branch/source and receipt
contracts; propagation of supplied mode to interior receipts remains unproved.
“Every accepted operation ends without pending units” now holds for every
typed trace accepted by the native runner, with no extra domain premise.
The original informal “unsupported” refusal wording becomes the exact native
Stop: hidden-record error with supplied records, invariant error without them.
This does not assert empty packet queues or absence of scheduled NAPI.

The [namespace-pin recipe](2026-10-20-proof-campaign-2-namespace-pin.md) retains
`dup(9); wg_netns_close; close(ref 0)`. On the affected mirror, it exposed
premature teardown at operation 1 and pending cleanup at operation 2. Main
`218d3ffd` resolves the environment defect: parsing refuses the literal pin,
and direct typed execution refuses at operation 1 before teardown. The
recipe checks these refusals and native/audit agreement. Earlier backlog,
nested-refill and supplied-pending defects are also fixed and retained as
refusal/pass regressions ([requests 1, 2, 4](2026-10-14-campaign-2-mirror-requests.md)).
Historical “cookie count/class alone ensures draining and predicted yields”
claims were refuted by bad-tail, extra physical-slot and hole witnesses;
exact bounded outcomes replace two predictions, and five false supports
remain retired ([cookie findings](2026-10-17-proof-campaign-2-cookie-bound.md)).

Effort remains 1,742 theorems, 280 headlines and 373 modules: the existing
boundary predicate and proofs are strengthened, with no new terminal theorem.
Ranked mirror changes: no open H5 request. Request 5's fixture reservation,
queued-cleanup and unconditional pending guards were altitude-preserving;
requests 1, 2 and 4 were also altitude-preserving and are closed.

## H6 summary — Guarded timer effects and session-relative counting

Architecture: actual arm/clear contracts retain wheel state and recorded clocks;
hook/session journals compose through the initialized driver. Local contracts
prove the guarded C delay at reached sites. Session stamps connect one derived
hook call to each successful session; normal completed enqueue deltas are zero
or one. Qualifying contiguous retry/send blocks within one normal timer episode
have the proved bound 19; arbitrary interleaved or multi-episode histories do not.

Wording pairs: “timers arm only at the C sites” becomes local guarded arm
effects with inspected C correspondence, not an exclusivity theorem.
“Persistent keepalive re-arms on every authenticated traversal” becomes the
guarded effect if the hook is reached; all-site coverage is the reviewed journal
construction. “Zero-key timer arms once per session” becomes at most one
completed session-derived enqueue per allocation stamp, plus a separate give-up
cause. Guards or unchanged expiry permit zero enqueues.

The [initialized give-up recipe](2026-10-17-proof-campaign-2-initialized-giveup.md)
has 19 retries then give-up at callback 20 with no session allocation. Retrofit
wording pairs are also retained: “delete changes expiry only” becomes expiry
and wheel deletion; “logical due means dispatcher-selected” becomes actual
wheel selection ([wheel witnesses](2026-10-17-proof-campaign-2-timer-carry.md));
“valid caller/arm records ensure return” becomes exact arm-tail execution,
including a missing base-clock Stop ([clock witness](2026-10-17-proof-campaign-2-missing-clock.md));
“empty send queue implies no requeue” becomes record-dependent queueing, with
a checked matching-record counterexample in the retrofit report.

Effort: 1,183 theorems, 100 headlines, 267 modules. Ranked mirror changes:
none requested for these statement/representation artefacts. No firing fairness,
universal retry-history bound or stronger site-completeness theorem is claimed.

## Landing-review disposition, 2026-10-20

[USER 2026-10-20] Apply the seven landing-review corrections without new
theorems, changed statements or mirror edits; keep recipe guest slots at 16.
The review is retained unchanged from `task/review-campaign-2` at `38ed7fb5`;
its N8 resource note is superseded by that guidance.

| Item | Disposition | Commit |
| --- | --- | --- |
| S1 | Six short status rows distinguish proved scope and exclusions; no run narratives | `90656358` |
| S2 | Rows moved into Results with Review cells, six claim-carrying entries, repository-relative intro and no campaign checkpoint narrative | `e505e329` |
| S3 | Pin finding/request 5 identify operation-1 teardown, silent skip, supplied-mode refusal and two unchosen mirror-lane fix shapes | `8a09c592` |
| S4 | Three recipes added; both helper modules imported into the built Progress terminal module | `4d8c94d4` |
| S5 | Six opening summaries give architecture, both statement wordings, findings, effort and ranked mirror requests | `5ed9ea4a` |
| S6, N4 | Eleven missing docstrings added; two concrete-evaluation headlines clarified | `52e861eb` |
| S7 | Supplied-pending finding marked as a mirror defect fixed at 3f3879e0, with regression retained | `8e24451b` |

Validation after all seven commits:

- `capped -- scripts/in-bundle scripts/proof-gate`: PASS, **3,141 build jobs,
  1,774 terminal statements**, only `propext`, `Classical.choice`, `Quot.sound`;
  actual exit zero.
- `capped -- scripts/in-bundle scripts/proof-counterexamples`: PASS,
  **15 recipes**, including confirmation incarnations, namespace pin and
  initialized give-up; actual exit zero.

Both runs used `LEAN_NUM_THREADS=32` and `LEANUX_QEMU_SLOTS=16` with the
unchanged outer memory cap. The bundle's inner capped-discovery notice does
not remove that outer cap. No failure, infrastructure rerun, KILLED outcome
or Lean-limit change occurred. Fresh kernel replay was not repeated for this
imports/docstrings-only Lean change; the pre-review replay remains historical.

Lightweight checks confirm all 879 owned terminal theorems have docstrings;
all Lean declaration/proof tokens match `3dbf9a02` after removing comments
and import lines; the review copy is byte-identical; the six Results rows,
six claim-carrying entries and their document links are present. No new
proof, statement change or mirror fix was needed. The owned census remains
9,443 theorems / 879 headlines / 2,210 modules. H5 request 5 remains open as
a recorded mirror defect; these corrections do not prove pending quiescence.

## Pre-review checkpoint, 2026-10-20

The staged Prefill proof is integrated without increasing any Lean resource
limit. Unconditional finite evaluation of the complete typed trace is closed.
The final H5 service increment also passes the full gate: accepted initialized
traces have normal actual committed activation receipts, and each receipt with
supplied input strictly consumes that input without a separate success premise.

The unrestricted pending-work completion claim is **refuted** by the accepted
[namespace-pin alias trace](2026-10-20-proof-campaign-2-namespace-pin.md).
It is a fixture/environment finding, mirror request 5, with original execution,
parsed-input execution and exact boundary-observer checks. The mirror remains
unchanged by this campaign. Requests 1–4 are fixed on main.

Main `1a69cebb` is incorporated at merge `6e91c19a`. Its only mirror change
replaces the deprecated observation string constructor; it requires no proof
body or frame repair. The full carry gate and fresh whole-tree kernel replay
pass; every row below is current over that mirror.

| Result | Current mirror | Status | Headlines / theorems / modules |
| --- | --- | --- | --- |
| H1 Noise | 1a69cebb | Current whole-run tag ownership and completed allocation-stamp uniqueness; slot effects are local, and site completeness is reviewed | 75 / 1597 / 279 |
| H2 Index | 1a69cebb | Current normal initialized index/owner coherence; lookup and records-only collision retry are local contracts | 162 / 1532 / 428 |
| H3 Roaming | 1a69cebb | Current observed authenticated attempts and normal final provenance; no per-write theorem | 45 / 1305 / 266 |
| H4 Configuration | 1a69cebb | Current one-directional four-scalar readback under an uncomposed entry invariant and getter bounds; flag-only replacement | 217 / 2084 / 594 |
| H5 Progress | 1a69cebb | Current finite evaluation and scoped service; no general budget adequacy; unrestricted pending emptiness refuted, request 5 open | 280 / 1742 / 373 |
| H6 Timers | 1a69cebb | Current reached-hook effects, qualifying retry blocks and at-most-one enqueue per stamp; no site-exclusivity theorem, caller placement reviewed | 100 / 1183 / 267 |

Campaign total: **9,443 theorems, 879 headlines, 2,210 modules**, including
three campaign projection modules. Claims remain over the campaign projection;
physical frames remain separate. No shared campaign-1 lemma or mirror file is
edited by this campaign.

Pre-review validation: full gate **3,137 jobs / 1,774 terminal statements**, with
only the three standard axioms; fresh whole-root kernel replay exits zero.
The separately built helper modules also pass their 12 axiom inspections and
fresh replay at the `AmbientRetentionFrames` and `SuppliedRecordSource` roots.
Final scoped build **1,341 jobs**, following the 524-job normal-completion base
build, passes without warnings. The namespace-pin recipe checks original and
parsed execution plus the exact boundary audit; Python harness validation
also passes. Heavy checks use `capped` at the unchanged memory cap, with
`LEAN_NUM_THREADS=32` and `LEANUX_QEMU_SLOTS=16`.
The earlier 12 unchanged counterexample recipes passed at `e901e03d`; that
count is historical, not a new claim about this carry.

Reproduce the final gate with
`capped -- scripts/in-bundle scripts/proof-gate`, and replay with
`capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs`.
The helper roots use the same replay command with
`Leanux.Proofs.WG.Progress.AmbientRetentionFrames` and
`Leanux.Proofs.WG.Progress.SuppliedRecordSource` respectively. The finding's
linked report gives the standalone recipe command.

## Landing assessment and H5 disposition, 2026-10-20

The campaign meets the charter's finding-completion criterion and is ready
for landing review. No implementation or validation work remains for this
disposition; merge to main and push remain unperformed.

The original H5 pending claim is left unproved with its concrete counterexample,
as charter section 3 permits. A supplied-only completion variant is **not
proved**: whole-syscall mode propagation and propagation to interior receipt
entries remain follow-up work. The new strict-decrease headline retains its
receipt-entry supplied-mode premise. An independent review identified this
positive join explicitly; its disposition is the charter's counterexample
option, rather than claiming an unproved replacement theorem. [AGENT 2026-10-20]
The campaign stops at this validated finding disposition; a stronger positive
variant is a follow-up, not an additional claim of this landing.

Actual service coverage rests on the original dispatch selection/start/run
and scheduler guard/detach/resume source equations, and on the concrete
factories installing the same receipt callback at both committed activation
sites. Each callback emits exactly one receipt even on Stop. The initialized
normal-completion theorem then rules out failed/exhausted receipts when the
whole trace succeeds. A yielded call is normal; this does not assert every
activation reaches its final section stop. Send, clear, timers, NAPI and
namespace cleanup retain their separate source/completion contracts.

The finite evaluator preserves exact JSON and every indexed Stop for every
typed trace and both placeholder settings. Practical runtime bounds, server
termination, universal activation fuel adequacy and scheduling fairness are
outside that claim. Independent source review found no omitted nonstructural
callback, including copied consistency trials and return-to-user task work.

Only open mirror request: **rank 1, altitude-preserving**, resolve the namespace
pin's retained-alias domain and last-release cleanup scheduling. The request
and executable recipe are linked above. A mirror fix can be carried later;
no kernel discrepancy or Linux capture is asserted here.

## Final H5 service composition, 2026-10-20

`CommittedCompletionModel.lean` distinguishes normal receipts from failed
receipts. The normal continuation invariant is `NormalHistory`; the predicate
on stopped histories is `True`, so failed receipts remain visible. Existing
scheduler, deferred, traffic, syscall and initialized-runner preservation
factories compose that distinction without a new observer or callback-success
assumption. Exact original erasure derives success of the observed initialized
run from the original result.

Claims are in `CommittedCaptureClaims.lean`,
`CommittedInitializedCompletionClaims.lean` and `Statements.lean`. Source
composition is in the five new `Committed*CompletionSource.lean` files.
`AmbientRetentionFrames.lean` and `DeferredOuterSuffixFrames.lean` hold the new
physical frames; `DeferredOuterSuffixSource.lean` supplies concrete normal
wait-tail suffix contracts, and `SuppliedRecordSource.lean` transports a suffix
contract into a mode contract. Those helpers do not close whole-syscall mode
propagation. `NamespacePinPending.lean` is a fail-noisy interpreter recipe.

Relative to `6531c47e`, this increment adds **42 theorems, three headlines and
13 modules**; 9,401 existing theorem declarations are kept, none retyped or
deleted. The main carry changes no state type, so there is no frame deletion.
The new source and claims compile at existing limits. The frame cluster's
earlier binder/lift/continuation elaboration failures were corrected before
its scoped pass. Two direct reductions of the namespace witness did not close;
no failed theorem was retained, and the witness is reported as runtime evidence.
No infrastructure rerun or KILLED outcome occurred. The former inherited
`String.mk` warning is removed by the landed main change.
The auxiliary axiom-output parser initially rejected three wrapped lists;
normalizing their continuation lines validates all 12 expected declarations
from the same Lean output, without rerunning the check.

## Whole-trace finite evaluation, 2026-10-20

`DispatchFiniteSource.lean` explicitly covers every constructor and
substitutes finite FS, configuration, lifecycle, traffic and Seccomp-install
callbacks. `SyscallFiniteSource.lean` supplies a local
`syscallWith_taskWork_variant` of the shared boundary, exposing precisely
the missing task-work callback. It uses `FsFinite.taskWorkRun`, which is
needed because native final file release can reach a pipe repeat. The
shared factory is unchanged; this is one small variant, not a copied layer.

`RunnerFiniteSource.lean` exposes syscall in the existing operation factor,
then composes the finite initialization, operation-array traversal,
presentation and finish. `RunnerFiniteClaims.lean` and three new headlines
state unrestricted projected dispatch/syscall agreement and exact
`executeTrace` equality. Source equations retain full native states; the
public claims do not name global state types. No new frames or deletions.

The retained leaf audit found these concrete bounds:

| Retained computation | Bound or reduction |
| --- | --- |
| Complete and stepped dumps | 4096 receives or one dump invocation, finite peer/route lists |
| Runtime Seccomp and concrete MiniInterp | filterCount + 1 and program instruction count |
| FIB lookup, updates and boot tables | key-length/resize fuel and finite lists |
| Packet admission, transmit and inline NAPI | finite packet/list/poll loops; four static lax-zero allocation sites |
| Namespace cleanup | finite endpoint/socket updates, FIB teardown and record cuts |
| Presentation and JSON | finite lists/arrays |

The nonstructural curve, translator, exact-count allocator and pipe paths
are reached through the already proved finite replacements. Scheduler
consistency trials use the same finite activation implementation. An
independent read-only review of actual source and callees found no omitted
dependency or weakened source equation. This proves mathematical evaluation
of one trace; it does not promise successful service, exclude a native
exhaustion Stop, or terminate the input server.

The tranche adds 13 theorems, three headlines and four modules: H5
1,700 / 277 / 360; campaign 9,401 / 876 / 2,197. Scoped builds pass
801 and 807 jobs. An initial dispatch proof left a definitionally equal
lift unresolved; an explicit reflexivity finish closes it. Full gate:
3,129 jobs / 1,771 terminal statements, standard axioms only. Fresh
whole-root replay exited zero. No limit increase or infrastructure rerun.

## Prefill, initialization and traffic integration, 2026-10-20

The approved two-stage bridge is now in
`SeccompPrefillFiniteSource.lean`: a native program-parametric wrapper
admits the reflexivity bridge, then the generic creator equality is applied.
`installWith` exposes translation independently of bounded filter insertion;
`RunnerInitialFiniteSource.lean` exposes prefill independently of original
fixture initialization and finite boot operations. No resource limit,
mirror definition or shared proof changes.

`TrafficFiniteSource.lean` instantiates the existing traffic factories with
finite crypt/send/scheduler callbacks. Injection, batch completion, flood
and batch preserve complete native outcomes without a success premise.
Admission, transmit, inline NAPI, multicast and guard leaves retain their
bounded native computations and the established static allocation
reductions. These equations alone do not establish useful service or
exclude an activation's exhaustion Stop.

Claims are in the three corresponding `*Claims.lean` files and the seven
new headlines in `Progress/Statements.lean`. Source adapters are in the
three `*Source.lean` files; no new frames. The tranche adds 32 theorems,
seven headlines and six modules. H5 is 1,687 / 274 / 356; the campaign is
9,388 / 873 / 2,193 (theorems / headlines / modules).

Validation: Prefill 40-job, initialization 81-job and traffic 716-job scoped
builds pass. The full gate passes 3,125 jobs and 1,768 terminal statements
with only the standard axioms. Fresh Progress-root kernel replay exits zero.
Three initial build attempts failed on two multiline record-layout errors;
the corrected definitions pass. No infrastructure rerun, KILLED job or
limit increase occurred. The inherited mirror `Env.lean:873` deprecation
warning remains outside this lane.

Reproduce the trust checks with the full gate command above and
`capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Progress.Statements`.
Remaining H5 work is complete syscall/Runner composition and record-relative
progress, with fuel adequacy and placeholder pending-work coverage stated
separately from finite evaluation.

## Prefill investigation and recommendation, 2026-10-20

The isolated closed generic creator specialization passes. The failed
conversion is between Prefill.translated and its callback-parametric
wrapper. A native wrapper that abstracts the program while retaining the
original creator admits a reflexivity bridge; the finite creator rewrite
is applied while that program is still variable. Their transitivity proves
the same exact requested equality. Both generated-matcher and ordinary
match-syntax forms pass without changing any Lean limit. The recommended
ordinary proof uses only the standard three axioms; fresh kernel replay
exits zero. Two independent read-only reviews found no scope weakening or
trust expansion. The [investigation report](2026-10-20-proof-campaign-2-prefill-investigation.md)
contains the tested source, measured reducibility heights, alternative
routes and the failed diagnostic outcomes, including the stopped equation
generator (KILLED, exit 143). This is a proposed fix, not an H5 completion.

Only documentation changes are committed for this investigation. The proof
tree, all 866 terminal declarations and the 9,356-theorem census are
unchanged; its latest full gate remains the e901e03d validation. No full
gate is rerun for this documentation-only checkpoint. H1–H4/H6 retain their
recorded status; H5 awaits agreement on integrating the bridge and resuming
its remaining work.

## Landed shared carry and Prefill stop, 2026-10-19

Main 3308c49a merges cleanly at a9845661. The previously uncommitted
DispatchRecordSource adapter adds the owned callback-factor unfold; its
statement is unchanged. LifecycleEnvironmentFiniteSource now imports
Queues.JointDelete and directly uses Configuration.envDeleteWith and
Configuration.envDelete_factor. The temporary local definition/theorem pair
is removed because the shared source is available, not because a proof failed.
The exact-result/whole-state ActivationRefillFrames remain stronger than the
new shared product-store frame and are retained. No frame is deleted.

Eight owned scheduler atom contracts now include the landed refill-read
field, using the actual account/publication contracts where their invariants
require them. DriverTagSchedulerSource also erases that read in its existing
source equation. Noise/PendingSchedulerFrames reuses the landed completion
guard frame. Progress/SchedulerRecordFrames adds the hidden-record suffix
frame for the pending-device read; DispatchRecordSource applies it to the
three device-worker eligibility reads. SchedulerRecordSource explicitly
imports its existing owned getDev run equation. All existing claim headers
are unchanged. The new frame remains in a separate Frames file.

The comment-aware declaration census corrects the previous report's H5
count, which was one too high. Before/after this carry: campaign 9,356 →
9,356 theorems, 866 headlines and 2,187 modules; H5 1,655 → 1,655 theorems,
267 headlines and 350 modules. One redundant deletion source theorem is
removed and one pending-device record frame is added. No terminal claim is
weakened or dropped, and no mirror or shared proof is edited.

The one post-merge stock-limit Prefill reproduction fails at the exact
SeccompPrefillFinite.translated_source declaration, with kernel maxRecDepth
512. Its generic source equality has only standard axioms, but the closed
specialization is not accepted. The [blocker report](2026-10-19-proof-campaign-2-prefill-blocker.md)
contains the full reproduction and diagnostic. No workaround or further H5
composition follows this reproduction. This is a blocked proof, not a claim
that the native function diverges. Concrete traffic/syscall/Runner
composition remains unproved despite its shared dependencies now being available.

The first post-merge gate fails in four owned modules (the two Roaming
scheduler constructors, Noise/PendingSchedulerFrames and
Progress/DispatchRecordSource). After those repairs, the second fails in
Progress/SchedulerRecordSource and Noise/DriverTagSchedulerSource. Both
exit one, skip their axiom phase and pass token/import checks; neither is a
pass. These are source-repair builds, not infrastructure reruns. The third
gate passes 3,119 jobs and all 1,761 terminal axiom inspections with only
propext, Classical.choice and Quot.sound. Fresh whole-root kernel replay
exits zero, and all 12 existing counterexample recipes pass. No resource
failure or infrastructure rerun occurs in this carry. Independent read-only
review found no issue in the eight atom contract updates, guard/record
frames or blocker report. The mirror, shared proof layers and gate match
3308c49a; all 866 owned terminal declarations are unchanged.
The inherited Env.lean String.mk warning remains outside this campaign's
allowed mirror edits; no warning is suppressed.

## Environment lifecycle and outer timer finite callers, 2026-10-19

Environment down and delete now have exact finite evaluators for every entry,
including absent/already-down returns, idle and pending-dump refusals, routing
notifications, finite down/destruction and every Stop. The five remaining
concrete deferred callers also close: runTimers, runTimersPlaceholder,
afterXmit, idleTimers and afterAdvance. Observation composes the actual idle
wait with the existing shared bounded native tail. Their captured bounds,
actual device reads, worker selection, pending/drained checks and distinct timer pass/end
bounds remain in native order. These are exact finite-outcome claims; they
do not by themselves establish useful service or initialized global termination.

Claims are in LifecycleEnvironmentFiniteClaims, DeferredFiniteOuterClaims
and ObservationFiniteClaims.
Source equations and callback factors are in their Source/Factors companions;
no frame is added or deleted. The unchanged owned environment-down factor
moves to Noise/DriverTagEnvironmentFactors. Four existing owned deferred
source definitions gain callback parameters once, and ten legacy declarations
move to the light native module with their original headers retained. The
shared-enum aggregate and the old higher-layer observers remain lagging;
mechanical unfold changes there do not count as rebuilt dependent proofs.

[AGENT 2026-10-19] Use exactly two local deletion variants,
envDeleteWith_variant and envDelete_factor_variant, of the shared
Configuration.envDeleteWith/envDelete_factor. Their original observer import
closure is lagging; the small variants retain its exact source without
copying a layer. Replace them with the shared declarations when their carry
lands. Traffic still needs five shared factories plus their erasure layer;
that larger copy remains outside this approach and is requested in the
shared carry note.

Eight new terminal wrappers bring H5 to 1,656 theorems / 267 headlines /
350 modules. The campaign totals are 9,357 / 866 / 2,187; Noise remains
1,597 / 75 with 279 modules. All legacy claims retain their stated scope.

Validation: environment lifecycle passes a 397-job scoped build; outer
deferred claims and three changed direct clients pass 367 jobs; observation
passes 365 jobs. The scoped audits check 45 declarations, including the exact
eight new terminal bodies, with only the three standard axioms and no
warnings. Fresh EnvironmentOuterReplay and ObservationNativeReplay both
exit zero. The full gate fails at actual exit one in only the same five
shared modules, with 3,117 planned jobs. Its terminal axiom phase is skipped;
token/import checks pass. Skipped dependent claims remain unchecked.
Independent source review found no mismatch in either package, finite
callback coverage or unchanged legacy headers. Down/delete drafting had
four probes: an inherited-import failure, a clean down proof, a corrected
doc/universe form error and a clean combined proof. Outer drafting had
15 probes: 12 clean and three corrected proof/probe-composition failures;
rejected intermediate axioms were not accepted. A handoff serialization
syntax error occurred before any file write. No infrastructure rerun, cap
increase or mirror/shared-layer edit occurs in this tranche. The inherited
Env String.mk deprecation and RxDrainBoundary unused-simp warning remain
reported under their owners; neither is suppressed here.

A separate source audit found seven Runner-reachable nonstructural loop
sites: pipe free/read/write/rounding, hidden allocation, curve exponentiation
and the Seccomp converter. Each has a concrete finite replacement. Remaining
work is their caller substitution through traffic, syscall dispatch and
task work, then executeTrace and the Prefill specialization. Namespace cleanup, native packet/data paths after
static allocation reduction, routing and non-install Seccomp paths are
bounded. This inventory is source review, not a completed global theorem.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.LifecycleEnvironmentFiniteClaims Leanux.Proofs.WG.Progress.DeferredFiniteOuterClaims Leanux.Proofs.WG.Progress.ObservationFiniteClaims Leanux.Proofs.WG.Progress.AdvanceWaitClaims Leanux.Proofs.WG.Progress.AdvanceOperationClaims Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The ignored EnvironmentOuterReplay root imports the lifecycle and outer
modules, includes seven exact terminal bodies, and audits their support and
the changed legacy source/advance/first-turn theorems. ObservationNativeReplay
imports ObservationFiniteClaims and audits its source equation, projected
claim and exact terminal body. Compile each with lake env lean and replay
with leanchecker --fresh under capped/scripts/in-bundle. The native full
tree cannot yet replace these scoped replays.

## Whole configuration and concrete native callers, 2026-10-19

Complete setPeerCmd and wgSetDevice now agree with finite evaluators for
arbitrary mixed attributes, states and record modes. The same execution
retains validation, allocation refusal, negative cutoffs, partial writes,
queued removal, private-key collision/install, allowed-IP insertion and
keepalive/staging. No normal-success or invariant premise is supplied.
Device open/up and its environment caller now have exact finite evaluation,
including socket refusal and running-flag rollback. Native selected send,
crypt scheduling and bounded send drain also close. The namespace-holder
close sequence uses finite close/final-release and task work after each of
the four original descriptors; later namespace cleanup is a separate caller.

New claims: ConfigurationFiniteClaims, LifecycleFiniteClaims,
DeferredFiniteNativeClaims and FsNamespaceFiniteClaims. Native factors and
finite equations stay in Source/Factors files; no physical frame is added.
Nine terminal wrappers bring H5 to 1,627 / 259 / 343. Four native lifecycle/send
supports bring Noise to 1,597 / 75 / 278 without changing its headline scope.
The campaign is 9,328 / 858 / 2,179 (theorems / headlines / modules).

Peer creation's existing definitions move to PeerCreationFiniteCoreSource;
its source theorem uses the landed low-level Peers factor. Four existing
peer claims now build through that core. The two BaseCreation-facing legacy
factors remain unchanged in the old importing module, still dependency-lagged.
The native deferred split relocates 22 declarations, 19 with exact bodies;
the three equivalent adapters retain their headers. All 69 legacy headers
in that package remain unchanged. Shared-enum/placeholder observer wrappers
are retained in their existing lagging modules. No shared layer is copied
or edited. The proposed opportunistic lifecycle-frame rewrite was omitted;
that existing file remains unchanged.

Validation: a 572-job scoped build covers configuration, recovered peer
claims, lifecycle and native deferred claims. Namespace close passes 84
jobs. All 62 audited declarations, including nine exact new terminal bodies
and six recovered existing terminal bodies, use only standard axioms.
Fresh ConfigurationNativeReplay exits zero. Independent review found no
mismatch in lifecycle/deferred or namespace-close source correspondence;
configuration integration received an author audit. Configuration drafting
had six probes (two corrected dependency/form failures, four clean passes),
lifecycle two clean probes, and deferred five probes (one corrected
projection failure, four clean passes). Namespace close built on its first
attempt. No infrastructure rerun or limit increase occurs.

The full gate fails in the same five shared modules, with 3,109 planned
jobs and no reported owned failure. Axiom inspection is skipped after the
build failure; token/import checks pass. Skipped dependents remain unchecked.
Traffic was tried through both shared factories and the owned tag/committed
instances. Both reach TrafficSource/BatchItemSource's shared observer imports,
which depend on DeviceSource or BatchActivation. Five factories plus their
erasure layer would need duplication, so no local copy is made. The exact
boundary is in the shared carry request. Remaining native timer/idle callers
are being handled through small owned source cuts; global termination and
all whole-run carry rows remain open/lagging.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.ConfigurationFiniteClaims Leanux.Proofs.WG.Progress.PeerFiniteClaims Leanux.Proofs.WG.Progress.LifecycleFiniteClaims Leanux.Proofs.WG.Progress.DeferredFiniteNativeClaims Leanux.Proofs.WG.Progress.FsNamespaceFiniteClaims
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The ignored ConfigurationNativeReplay root imports those claims, includes
the exact fifteen terminal bodies and all 62 axiom inspections, and is
compiled with lake env lean before leanchecker --fresh under capped/scripts/in-bundle.

## Native activation and scheduler carry, 2026-10-19

The concrete activation evaluator now uses the owned carried source factors:
occupancy and refills are read in native order, the captured bound is their
sum plus one, and dispatch retains pending empty device units. Reception uses
the concrete finite handshake evaluator; encrypt/decrypt/transmit and their
NAPI/Stack dependencies retain bounded native operations. The four packet
allocation sites reduce to the already-checked laxZero leaves. Those paths
queue later handshake work rather than executing an unaccounted creator.
Copied consistency trials use the same finite run and discard successors;
the existing scheduler turn and captured record budget are reused.

Four unchanged receiver declarations move from HookSchedulerWorkersSource
into TimerDiscipline/HookSchedulerReceiveSource. Three callback parameters
are exposed in the existing owned activation-step, loop and dispatch-suffix
factors; their native specializations retain their original headers. The
five projected finite claims and their terminal statements are unchanged.
No frame, theorem or headline is removed or added; one module brings the
campaign to 9,287 / 849 / 2,166 and TimerDiscipline to 267 modules. H5 remains
1,590 / 250 / 332. All 77 retained declaration headers/types in the handoff
were checked unchanged.

The real isolated activation build passed but its scheduler file failed on
an omitted final reflexivity step; the combined stdin context had hidden
that requirement. Restoring the original step fixes it. A subsequent client
build also exposed one old step name left in a simp list and reached three
inherited shared failures; it failed, not partially passed. The corrected
303-job scoped build passes activation/scheduler claims and all four affected
cookie/exit clients. An audit of 47 declarations includes the exact five
terminal bodies and the private cookie support; all use standard axioms.
Fresh ActivationCarryReplay exits zero. Agent drafting had nine probes:
three corrected form failures and six clean passes. No infrastructure rerun
or limit change occurs.

The enum-dependent observer family remains lagging. DispatchRecordSource
also sits behind inherited source failures; its one-line unfold adaptation
is uncommitted pending validation. None of these skipped modules is counted
as checked by the scoped build. The latest complete gate remains the
3,096-job failed attempt recorded above; all six whole-run rows remain lagging.

Five further root Prefill probes included three clean name/expression
inspections and two failed proofs at stock recursion depth. The stored native
body and a literal candidate body compare syntactically equal, yet even their
closed reflexivity bridge exceeds the kernel limit. The rejected theorem
placeholders consequently report a self dependency in axiom inspection;
these failed probes are not trusted code or accepted results. No limit is
raised, and no mirror change is proposed for the proof-form issue.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.ActivationFiniteClaims Leanux.Proofs.WG.Progress.SchedulerFiniteClaims Leanux.Proofs.WG.Progress.ActivationExitSource Leanux.Proofs.WG.Progress.CookieBoundedSource Leanux.Proofs.WG.Progress.CookieActivationSource Leanux.Proofs.WG.Progress.CookieActivationBoundFindings
```

Fresh replay uses an ignored ActivationCarryReplay root with those imports,
the exact five terminal bodies and 47 axiom inspections, compiled with lake
env lean and replayed by leanchecker --fresh under capped/scripts/in-bundle.

## Private-key stage and full Seccomp installation, 2026-10-19

The complete private-key stage now agrees with a concrete finite evaluator
for every input state and record mode. It retains absent/unchanged-key exits,
curve generation, collision lookup and caller payment, queued peer removal,
identity/cookie installation, and the saved peer traversal with precomputation,
expiry and staging. The full Seccomp installation caller likewise retains all
flags, mode selection, validation, locking, attachment, synchronization, cache
preparation, release, refusals and Stops. Neither claim assumes success.

Claims live in Progress/KeyConfigurationFiniteClaims and
SeccompInstallFiniteClaims, with five Source modules and seven exact terminal
wrappers in Statements. These are projected exact-evaluation claims, not yet
whole-run termination. No new physical frame is needed.

[AGENT 2026-10-19] Generalize the existing owned key callback factors once,
retaining their original native wrappers and all 40 existing theorem headers.
Separate already-proved native factors from their observer imports instead of
copying inherited scheduler/removal layers. Twenty-one declarations, including
nine theorems, move into Index/FlushFactors, Noise/DriverTagFlushFactors,
DriverTagRemovalFactors, DriverTagControlFactors and Config/KeyStageFactors.
No frame is deleted and no shared lemma is edited. The key-stage factor is
adapted to the callback generalization; the other moved bodies are unchanged.
Seven former large heartbeat overrides are removed; the builds use stock
limits for those declarations.

The five factor modules add no theorem. The concrete callers add 27 theorems,
seven headlines and five Progress modules: H5 is 1,590 / 250 / 332 and the
campaign is 9,287 / 849 / 2,165 (theorems / headlines / modules). H1, H2, H3,
H4 and H6 theorem/headline counts are unchanged. The new file split adds three
Noise modules, one Index module and one Config module.

The maintenance/key scoped build passes 444 jobs; the installation and adapted
key-request/readback/collision clients pass 183 jobs. The audit checks 85
declarations including all seven exact terminal bodies, the new supports,
maintenance contracts, moved theorems and adapted key-client proofs; every
audit reports only the three standard axioms. Three rejected audit-root drafts
used inaccessible or incorrectly encoded private names. The corrected audit
selects each private declaration uniquely from the environment and prints its
actual name; none is omitted. Fresh KeyInstallReplay exits zero.

Key drafting had 19 probes: twelve clean passes, two warning-only drafts
corrected before installation, and five corrected proof/test-alias failures.
Installation drafting had four probes: one extraction-layout failure with
cascading heartbeat errors, then three clean passes. Test aliases are absent
from the trusted tree. No infrastructure rerun occurs. Independent review of factor placement and
Seccomp installation found no mismatch; all 341 retained named theorem
headers across the dirty files remain unchanged. The key finite package
received an author integration audit, not independent review. Import
isolation removes higher-level observer dependencies, not every transitive
frame import.

The new full gate fails with 3,096 planned jobs in exactly the same five
inherited modules: Logged.Scheduler, Logged.Checkpoints, Lifetimes.BatchActivation,
Queues.RxDrainBoundary and NetlinkDump.DeviceSource. No owned failure is
reported; blocked dependent modules are not validated, and the axiom stage is
skipped. Token/import checks pass. All six whole-run rows remain lagging.

The remaining Seccomp syscall audit retains native handlers: strict child
setup selects opcode 0 (or prctl mode 1), query selects only opcodes 2/3,
and neither reaches filter translation. Self/child execution uses bounded
MiniInterp and filter-count walks; signal/task helpers are acyclic or finite
list traversals. This is a source-closure audit, not a new termination theorem;
whole syscall composition still needs the finite task-work substitution.

A second Prefill architecture separates the generated matcher and the whole
creator function. Its generic equality and symbolic apply factor pass, but
specializing the native closed 3,990-instruction constant still exceeds the
kernel recursion limit. Seven further probes include two clean passes, three naming/layout
failures and two failed closed-specialization proofs; the last failed probe
also checked its generic matcher/function equalities successfully.
The generic supports are not installed as a completed Prefill result. This
is an exact open proof-form obligation, not a mathematical counterexample;
no mirror change or recursion-limit override is retained.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.MaintenanceFiniteClaims Leanux.Proofs.WG.Progress.KeyConfigurationFiniteClaims Leanux.Proofs.WG.Progress.SeccompInstallFiniteClaims Leanux.Proofs.WG.Config.KeyRequest Leanux.Proofs.WG.Config.KeyReadbackFrames Leanux.Proofs.WG.Config.CollisionRequestSource
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The ignored KeyInstallReplay root imports those modules, includes the exact
seven terminal bodies and all 85 axiom inspections, and is compiled with
lake env lean before `leanchecker --fresh KeyInstallReplay`, under
capped/scripts/in-bundle. Whole peer/device configuration, traffic,
Prefill/Runner composition and global termination remain separate obligations.

## Remaining FS entries and concrete filter preparation, 2026-10-19

Finite evaluators now cover duplication, synchronous close and epoll_wait.
The close path uses finite final release before the original restart-errno
handling; ordinary duplication cleanup still queues its native deferred fput.
The epoll scan preserves its captured list, cutoff, ready-list effects and
original timeout/would-sleep Stops. Filter preparation now includes its
separate filter-object allocation and finite program creation. The pure
translation check retains rejection, Stop, agreement and disagreement; it
asserts evaluation equality, not translation correctness.

Claims: FsFinalCallerFiniteClaims, SeccompFilterFiniteClaims and
SeccompTranslationFiniteClaims; their four Source modules hold the exact
native factors/equalities. Seven terminal wrappers are added. Native claims
use the product projection; the translation check retains its pure result.
These add 32 theorems, seven headlines and seven Progress modules.

The six native initiation factors and their source theorem move unchanged
to TimerDiscipline/InitiationTraversalFactors. Its observer Source imports
that file, as does InitiationCallerFiniteSource. Independent comparison found
the moved 2,566-byte block identical, with unchanged qualified names and
headers. This removes the finite caller's accidental observer dependencies;
it deletes no frame and copies no shared layer. One module is added without
changing the theorem count. H5 is 1,563 / 243 / 327; the campaign is
9,260 / 842 / 2,155 (theorems / headlines / modules).

The initiation-factor build passes 60 jobs, followed by the combined
125-job caller build. A 37-declaration audit includes the exact seven new
terminal bodies and the moved source/finite initiation contracts; all use
standard axioms. Fresh FinalCallersReplay exits zero. Independent review
found no source, dependency or scope mismatch. The four final-FS probes
were clean. No shared or mirror file is changed; the full gate remains
failed on the previously reported shared carry, and all rows remain lagging.

Prefill is still a proof-form obligation. Its source uses a closed
3,990-instruction fixture. The earlier 21-call exploration had six passes
(three diagnostics), fourteen proof-form failures and one deliberately
terminated diagnostic, exit 143. A root probe with declaration-local
maxRecDepth 8192 began expensive closed normalization (about 24 GB RSS at
52 seconds) and was also deliberately terminated at its verified PID;
capped reports KILLED, exit 143. Both are failures, not passes or successful
reruns; no memory cap was raised. The larger recursion option is not retained
in trusted source. The dirty source tree was preserved in
refs/snapshots/proofs-campaign-2/2026-10-19-prefill-depth-stop before further
edits. No mathematical counterexample or mirror discrepancy is claimed.
A different proof factorization is being investigated.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.FsFinalCallerFiniteClaims Leanux.Proofs.WG.Progress.SeccompFilterFiniteClaims Leanux.Proofs.WG.Progress.SeccompTranslationFiniteClaims Leanux.Proofs.WG.Progress.InitiationCallerFiniteClaims
```

Fresh replay used an ignored root importing those modules, with the seven
exact terminal bodies and all 37 axiom prints, compiled with lake env lean
and replayed using `leanchecker --fresh FinalCallersReplay` under
capped/scripts/in-bundle. Native installation and Prefill/Runner composition
remain separate obligations.

## Owned pagination carry and finite program/epoll callers, 2026-10-19

The complete-peer page model now restores the four-byte reservation for an
empty first callback. The mixed raw scan and recursive plan stay post-nest;
only the actual first callback applies empty-device cancellation. The mixed
receive count is a conservative sufficient budget, not a minimal actual
count: the proof explicitly bounds actual DONE spill by that budget. Whole
peer and mixed getter statements are unchanged. Of 18 existing declaration
headers in the carry, only wgGetDeviceDump_guard_returns changes, from
post-nest to pre-nest room. No frame is deleted.

Concrete native and Local Seccomp migration/preparation/program creation now
agree exactly with finite evaluators. An explicit native operation value
replaces allocation, including allocations inside the classic checker; no
global instance is changed. Installation and Prefill remain separate callers.
Five fcntl layers use finite pipe rounding and preserve actual resize,
accounting and refusal behavior. Finite epoll creation and ADD/DEL/MOD
composition retain all four allocation sites, cleanup and original bounded
nested polling, including exhaustion Stops. No successful-service or
return-to-user completion theorem follows merely from these equalities.

Claims: SeccompProgramFiniteClaims, FsFcntlFiniteClaims and
FsEpollFiniteClaims, plus 13 Statements headlines. Their seven Source files
contain native factors and full-state source equalities. Public native claims
use the product projection; Local claims retain its full result/state.
There are no new frames, shared edits or mirror changes. This adds 81
theorems, 13 headlines and ten modules: H5 1,531 / 236 / 320; campaign
9,228 / 835 / 2,147 (theorems / headlines / modules).

Scoped builds pass 207 jobs for pagination, 57 for program/fcntl and 51 for
epoll. ProgramFcntlReplay checks 38 standard-axiom declarations including
11 exact terminal bodies; PaginationEpollReplay checks 66 including two
new epoll and two existing whole-getter terminal bodies. Both fresh scoped
replays exit zero. Independent review of the caller additions since the
native carry found no source/scope mismatch or surviving unbounded native
leaf beneath the named evaluators; older pipe evaluator internals were reused
dependencies rather than independently re-reviewed.

Pagination drafting had nine probes: six corrected proof/dependency
failures and three passes. One rejected broader probe propagated sorryAx
from its failed peer getter proof; this was a failure, never accepted evidence.
The corrected final 21-name audit and real scoped replay are clean.
Seccomp program drafting had five probes (two corrected form failures),
fcntl checked cleanly, and epoll had seven clean probes. No memory-cap or
proof-limit increase, resource failure or infrastructure rerun occurs in this
tranche.

The subsequent full gate fails on Logged/Scheduler, Logged/Checkpoints,
WG/Lifetimes/BatchActivation, WG/Queues/RxDrainBoundary and
WG/NetlinkDump/DeviceSource. It finds no further owned failure; it does not
validate owned dependents skipped behind those failures. Token/import checks
pass and the terminal axiom stage is skipped. Inherited compiler warnings
in those shared files and the mirror remain for their owners. All six rows
remain lagging main 3f3879e0.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Config.PeerGetterClaims Leanux.Proofs.WG.Config.MixedGetterClaims Leanux.Proofs.WG.Progress.SeccompProgramFiniteClaims Leanux.Proofs.WG.Progress.FsFcntlFiniteClaims Leanux.Proofs.WG.Progress.FsEpollFiniteClaims
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The two fresh replays used ignored roots importing those claim modules and
copying the exact terminal bodies, compiled with lake env lean and replayed
with `leanchecker --fresh ProgramFcntlReplay` and
`leanchecker --fresh PaginationEpollReplay`, under capped/scripts/in-bundle.

## H5 finite FS callers and owned dump carry, 2026-10-19

Eighteen further concrete callers now have exact finite evaluators: fd-table
expansion and descriptor allocation, eventfd creation, all six read/write
entry layers, and pipe inode/file/descriptor creation through sysPipe2.
Allocation refusals, two-turn descriptor exhaustion, cleanup and copy faults
retain their original result and Stop. Ordinary fput still queues its native
deferred release. No success or callback premise is assumed. Native source
equalities retain all FS fields; public claims use the product projection.

Claims are FsDescriptorFiniteClaims, FsReadWriteFiniteClaims and
FsPipeCreationFiniteClaims; their five Source files hold the finite bodies
and exact native equalities. Eighteen Statements headlines are added.
No new frame, mirror change or shared-layer edit occurs. This adds 54
theorems in eight modules: H5 1,450 / 223 / 310; campaign 9,147 / 822 / 2,137
(theorems / headlines / modules).

The owned multi-peer/socket factors now restore the cancelled four-byte nest
reservation. The cursor model and source use the pre-nest snapshot for empty
lists and dead cursors; only the scanning branch reserves the nest. Two model
result interfaces, including the cursor headline, are corrected accordingly.
The whole multi-peer getter JSON/socket contract is unchanged. Outer peer
and mixed-page pagination remain the next carry step.

Scoped builds pass 111 jobs (dump callers), 154 jobs (cursor and descriptor /
read-write callers) and 59 jobs (pipe creation). A combined root checks 72
declarations with standard axioms only, including the exact 18 new terminal
bodies and the corrected cursor terminal; fresh CallerCursorReplay exits
zero. Descriptor/eventfd drafting used five probes (one corrected form
failure); pipe drafting used four (one corrected form failure). Read/write
and cursor drafts checked cleanly; earlier dump dependency/proof probes were
corrected before the real builds. No resource failure, infrastructure rerun
or increased limit occurs in this tranche. The full-tree gate remains failed
pending the remaining owned carry and campaign-1 source observers.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Config.MultiPeerGetterClaims Leanux.Proofs.WG.Config.SocketReadbackSource Leanux.Proofs.WG.Config.CursorCallbackClaims Leanux.Proofs.WG.Progress.FsDescriptorFiniteClaims Leanux.Proofs.WG.Progress.FsReadWriteFiniteClaims Leanux.Proofs.WG.Progress.FsPipeCreationFiniteClaims
```

Fresh replay used an ignored root importing those modules and copying the
19 exact terminal bodies, compiled with lake env lean and replayed with
`leanchecker --fresh CallerCursorReplay`, under capped and scripts/in-bundle.

## H5 finite allocation and Local conversion, 2026-10-19

Eight concrete file/anonymous-inode allocation callers now agree exactly
with finite evaluators. All original allocation-site order, publication,
rollback, errno and Stop paths remain. Their source equations retain full
FS/task/Ambient results; the public claims use the existing product projection,
which deliberately exposes fewer FS fields. No allocation-success or
normal-return premise is supplied.

The actual Local Seccomp converter now agrees with three bounded outer
passes. A single polymorphic owned instruction factor serves both concrete
instances; Local branch truthfulness supplies the same decreasing pass rank.
Its allocation operation is already structural. The concrete Seccomp.M
interfaces remain unchanged (23 legacy declaration headers). An arbitrary
SeccompM instance is not claimed to terminate, and installation, prefill and
Runner callers remain separate obligations.

Claims: FsAllocationFiniteClaims and SeccompLocalFiniteClaims, with nine
new Statements headlines. Sources: FsAllocationFiniteSource,
FsAnonymousFiniteSource, SeccompLocalFiniteSource and the two existing
Seccomp source factors. No new frame or shared/mirror edit. This tranche adds
39 theorems, nine headlines and five modules: H5 1,396 / 205 / 302; campaign
9,093 / 804 / 2,129 (theorems / headlines / modules).

The real scoped build passes 55 jobs. All 55 audited declarations, including
the exact nine new terminal bodies, use only the three standard axioms;
fresh scoped kernel replay exits zero. A scratch-file open of an unimported
namespace failed once and was removed; all theorem bodies already checked.
The FS draft used five probes (two corrected form failures, three passes);
the Local draft used seven (three corrected form failures, four passes).
No resource failure, infrastructure rerun or increased limit occurred in
this tranche. Independent FS review found no source/scope mismatch. The
Local author re-audited that part; it is not counted as independent review.
Root reviewed the factor and the concrete pass/allocator premises.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.FsAllocationFiniteClaims Leanux.Proofs.WG.Progress.SeccompFiniteClaims Leanux.Proofs.WG.Progress.SeccompLocalFiniteClaims
```

Fresh replay used an ignored root importing those three modules and copying
the exact nine new terminal bodies, compiled with lake env lean and replayed
with `leanchecker --fresh FsLocalReplay`, under capped and scripts/in-bundle.
The full gate remains failed on the previously recorded inherited/owned
carry; these scoped results do not make any whole-run register row current.

## Environment-fix carry, 2026-10-19

The branch merged main 3f3879e0 after checkpoint 46b6089c. The owned native
Runner audit now exposes the fourth completion check: any accepted cut that
has supplied records has no pending identities. The statement concerns the
actual cut's mode; all-mode pending emptiness and propagation of the trace's
initial record mode are separate obligations. Both native source factors
retain the exact new guard and every original Stop.

Activation exits now retain the actual occupancy read, the following refills
read, and both values. The source observer includes a distinct refill-read
failure. Its previous occupancy-plus-one bound is replaced by occupancy plus
refills plus one, matching the new source. This alone is not a proof of fuel
adequacy or useful service. Dispatch and placeholder selection now include
the three device pending bits. Their old queue-only no-work premises are
replaced with queue emptiness plus the corresponding absent pending bits.
The selected-worker headlines refer to selection from the actual snapshot.

The empty-dump regression now proves room 3724 rather than 3720 and agrees
with cancellation to the pre-nest-reservation snapshot. The owned dump source
cut moves that snapshot before reservation. The placeholder regression now
proves pendingWork=[] at its actual accepted cut; its terminal is renamed
`original_placeholder_pending_cleared`. The old positive pending-identity
statement is historical, not retained as a current claim. The same recorded
traces now test exact missing-redispatch refusal and accepted empty redispatch
with drained audited queues. The old committed eight-receipt comparator and
its two helper definitions are retired from the executable regression; their
historical evidence remains in the supplied-pending report and checkpoint.
A current receipt comparison waits for the shared observer carry.

Claims remain in the owned Claims files and Statements. Native source cuts
and projected observation models are separate; physical frames remain in
Frames files. No frame is deleted merely because it failed to compile.
No mirror or shared campaign-1 file is changed.

The initial scoped build failed in twelve modules: eight owned and four
shared (`Logged/Scheduler`, `NetlinkDump/DeviceSource`,
`Lifetimes/BatchActivation`, `Queues/RxDrainBoundary`). The first owned repair
build passes 147 jobs; observation/boundary and native-regression builds pass
94 and 80 jobs. Dump wrappers pass a further 108-job build; activation record
decrease, decrypt adequacy, receive terminal cuts and cookie callers pass a
260-job build. The scoped root checks ten exact terminal bodies plus 149
support declarations, all using only the standard axioms. Fresh scoped kernel replay passes at actual exit zero. The full gate fails in five inherited modules (the four
above plus Logged/Checkpoints) and two additional owned modules:
Config/MultiPeerDumpSource and Config/SocketReadbackSource. Its token/import
checks pass; its whole-tree axiom phase is skipped after the build failure.
Those two owned dump carries are being repaired.

One checker invocation failed with exit 137 and the 32 GB KILLED banner:
`lake env leanchecker --help`. Inspection of the toolchain source showed
that this tool has no help flag; with no module argument it started parallel
project-wide replay. The failed invocation is not a validation pass. The
cap is unchanged, the dirty owned tree was preserved to a snapshot ref, and
the corrected validation uses an explicitly named fresh scoped root. No
unchanged-command rerun is made. The inherited Env String.mk warning now
appears at line 873; it is outside this campaign's ownership.

The record/decrypt carry adds ActivationRefillFrames (two actual-state read
frames); existing projected receive and decrypt claims keep their headers.
The old malformed-tail cookie activation and scheduler exhaustion witnesses
now prove exact successful endpoints. The count-versus-physical-tail contrast
remains an arbitrary-state fact, with no initialized-reachability assertion.

Within the 37 changed existing Lean files, 516 theorem headers are unchanged,
27 are corrected, and four historical names are replaced by four corrected
regression names. Two new frame theorems raise the surface from 9,052 to 9,054
and owned modules from 2,123 to 2,124; the 795 headlines are unchanged in
number. No frame is deleted. Header identity does not by itself assert
unchanged meaning: the observed models and actual guards are described above.

Draft validation failures were corrected rather than suppressed: the
record/decrypt/receive package used ten probes (five passes, four proof-form
failures, one missing inherited object); the cookie package used sixteen
(five passes, eleven proof-form failures). Neither raised a limit or retried
an infrastructure outcome. Narrowing two owned imports removed unnecessary
dependence on broader shared scheduler layers. Further dump carry remains. The replay root imports 41 carried/support
modules and copies the ten exact changed terminal bodies; all 159 axiom
checks pass, followed by fresh kernel replay at actual exit zero.

Reproduce the scoped source build with the following targets (full parallel
build scheduling, default memory cap):

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.ActivationRecordSource Leanux.Proofs.WG.Progress.DecryptOccupancyClaims Leanux.Proofs.WG.Progress.ReceiveTerminalClaims Leanux.Proofs.WG.Progress.CookieScheduleClaims Leanux.Proofs.WG.Progress.CookieScheduleFindings Leanux.Proofs.WG.Config.IdentitySourceClaims
```

For the scoped replay, generate an ignored `CarryReplay.lean` importing the
changed non-Statements modules and their Claims clients, with the exact seven
changed Progress headline bodies and three empty-dump headline bodies. Print
their axioms and those of the imported carried public supports, compile with
`lake env lean --root=.tmp/c2-wheel -o .tmp/c2-wheel/CarryReplay.olean
.tmp/c2-wheel/CarryReplay.lean`, then run
`lake env sh -c 'LEAN_PATH=".tmp/c2-wheel:$LEAN_PATH" leanchecker --fresh CarryReplay'`.
Both commands run through capped and scripts/in-bundle. This scoped replay
is not a replacement for the failed full-tree gate.

## H5 finite cleanup, deferred and subsystem callers, 2026-10-19

Complete finite counterparts now cover flushed handshake work, its bounded
drain, timer stop, after-dead/single/bulk removal, destruction, stop and down.
They instantiate existing source factories with finite handshake sending;
clear work, reference release and trie cleanup retain their bounded native
paths. The actual guards and drain exhaustion remain unchanged.

Both keepalive-reaching timer callbacks now use finite allocation, and all
five callbacks retain their exact native outcomes. Recorded dispatch keeps
worker/unit checks, wheel detachment and pass metadata; the placeholder pass
keeps its captured finite scan. All fourteen deferred constructors compose
these callbacks with finite sending and scheduling, including copied
consistency trials. Their original delivery, guards, record budgets and every
Stop remain. One short local timer-dispatch source variant and the placeholder
pass expose concrete callback substitution; no shared layer is edited.

The filesystem counterpart now covers pipe read/write iterator dispatch,
final pipe reference payment, release dispatch, final/synchronous file puts
and bounded task-work execution. Exact native FS equalities preserve all FS,
task and ambient effects before the campaign projection; the projection does
not expose every filesystem field. Native epoll cleanup uses finite lists and
only queues later ordinary fput work. Task-work exhaustion is retained; no
successful drain or sufficient-budget theorem is claimed.

The concrete Seccomp.M converter now agrees exactly with a three-pass
finite evaluator. Every continuing pass increments its original Int counter
and survives the overflow guard, strictly decreasing its remaining rank.
The input-array instruction scan is bounded and remains in a single source
factor. Its kcallocAddrs encounter uses the existing finite allocator.
Every errno and Stop is preserved without validation or success premises.
The Local instance and surrounding preparation/installation/prefill callers
are separate obligations, not consequences of this concrete instance.

Claims are in `MaintenanceFiniteClaims`, `DeferredFiniteClaims`,
`FsCallerFiniteClaims` and `SeccompFiniteClaims`; their source modules contain
native equalities and finite composition. `TimerFiniteSource`,
`SeccompPassSource`, `FsPipeCallerFiniteSource` and `FsReleaseFiniteSource`
are source factors, not physical frames. No existing support, shared proof,
frame or mirror file changed. Twenty-one new projected headlines are in
`Statements.lean`; all 175 preceding H5 heads retain their names and order.

Independent timer/deferred review found no retained nonfinite callback:
both keepalive arms, native sender, committed scheduler and copied trials
use finite counterparts. Root reviewed the maintenance, FS and Seccomp exact
source cuts and their transitive finite leaves. This closes evaluation for
these callers, including native exhaustion. Configuration, remaining FS and
Seccomp callers, traffic/lifecycle and initialized Runner composition remain.
The newly landed environment fixes now permit the completion-guard carry.

Validation: the real split-module build passes 1,191 jobs. Two terminal
builds failed because the newly exported wrappers lacked namespace qualifiers;
the second corrected only some of those names. A prematurely launched full
gate also failed on the remaining four unqualified wrappers. All qualifiers
are now explicit and the corrected terminal build passes 1,550 jobs.
The final gate passes 3,054 jobs and 1,690 terminal statements with only
standard axioms. Fresh whole-tree kernel replay passes at actual exit zero. All failures are
reported as failures. The inherited Env:865 String.mk warning is unchanged.

Draft ledger at stock proof limits and the unchanged capped memory limit:
maintenance, five probes (one corrected optional-argument elaboration failure,
one missing rebuilt dependency artifact, its single successful infrastructure
rerun, and two clean audits); FS callers, five probes (two corrected proof-form
failures, three clean); Seccomp, sixteen probes (five clean, eleven exploratory
or corrected failures, including four stock-heartbeat failures); timer/deferred,
five probes (three clean, one missing definitional reduction and one namespace
error corrected). The final narrow audits use only standard axioms. No KILLED
outcome or guest run occurred.

This tranche adds 92 theorems, including 21 headlines, in eleven modules.
H5 now has 1,355 theorems / 196 headlines in 296 modules; campaign totals are
9,052 theorems / 795 headlines / 2,123 owned modules. Other result counts
and documented scopes are unchanged. Current validation holds over 783510e8;
all six results are marked lagging the newly landed 3f3879e0 pending carry.

## H5 finite activation, scheduler, peer and allowed-IP calls, 2026-10-19

The original activation iteration, occupancy-bounded run and dispatch now
agree with finite concrete evaluators. The existing worker factories use
finite handshake reception; transmit and NAPI retain their bounded native
packet computations. Their four concrete copy/checksum allocation sites
reduce to `pure true`; queued handshake work is not executed recursively.
The full scheduler now uses finite evaluation in both committed activations
and copied consistency trials. A copied successor is still discarded;
hidden-input mismatches reject a candidate and other Stops still propagate.
The captured scheduler budget and ambiguity/exhaustion outcomes are unchanged.
Finite evaluation does not establish adequate activation occupancy or service.

Exact finite counterparts also cover static-static precomputation, private
identity installation, handshake initialization and complete peer creation.
The raw private bytes still feed public-key generation while stored private
bytes are clamped. Maximum-peer refusal precedes allocation, and cache reset,
initialization, timestamp and publication retain their source order. Allowed-IP
allocation, add and insert now use finite allocation encounters at all three
node sites, preserving replacement, intermediate-node rollback, sequence
increments and family selection without shape or successful-return premises.

Claims are in `ActivationFiniteClaims`, `SchedulerFiniteClaims`,
`PeerFiniteClaims` and `AllowedFiniteClaims`, with 12 new projected headlines
in `Statements.lean`. Corresponding source files hold exact native equalities;
`PacketAllocationFiniteSource` records the four statically finite packet sites.
Owned scheduler and allowed-IP source factors expose small callback parameters,
retaining the old definitions as default adapters. All 57 preexisting support
headers and all 163 earlier H5 terminal headers remain unchanged. Existing
owned `PendingAllowedInsertionFrames` and `AllowedFrameSource` remain physical
frames; no frame was deleted and no shared layer or mirror was changed.

Independent source/dependency review found no mismatch in activation, peer or
allowed-IP coverage. Root reviewed the concrete scheduler and its unchanged
default adapters. The remaining whole-run closure includes configuration,
cleanup, deferred timer/traffic/lifecycle calls, filesystem and Seccomp callers,
and syscall/runner composition. Their composition is independent work; H5
useful-work completion still waits for the confirmed environment fixes.

Validation passes on the exact final tree. The first scoped build failed only in the
allowed-IP source equality, which needed a final definitional reduction under
its actual split imports. The corrected terminal build passes 1,514 jobs.
The first full gate failed in three owned allowed-IP clients because their
unfold lists omitted the new adapters, producing derivative unused-simp
warnings. Unchanged statements with the corrected proofs pass a 1,065-job
focused build. A trailing blank line found by the staged whitespace check
was also removed. The final gate passes 3,043 jobs and 1,669 terminal statements, all on
standard axioms; fresh whole-tree kernel replay passes at actual exit zero.
The inherited Env:865 String.mk warning remains unchanged.

Draft ledger, all at unchanged capped and proof limits: activation, three
clean probes; peer, four probes (one corrected syntax/import failure, three
clean); scheduler, nine probes (four clean, five corrected tactic/elaboration
failures, including artificial combined-import effects absent from the actual
split modules); allowed-IP, three clean combined probes followed by the
recorded split-import build correction. No KILLED or guest outcome occurred.
No infrastructure retry was used for this checkpoint.

This tranche adds 45 checked theorems, including 12 headlines, in ten new
modules. H5 has 1,263 theorems / 175 headlines in 285 modules. Campaign totals
are 8,960 theorems, 774 headlines and 2,112 owned modules; other result counts
and documented completion scopes are unchanged.

## H5 complete finite handshake calls, 2026-10-19

All four original Noise create/consume calls now agree exactly with finite
counterparts on every entry and input mode. The helpers substitute the
existing finite Curve25519 evaluator, with an explicit impossible-exhaustion
Stop ruled out by its unconditional source theorem. Original null-result,
missing/malformed-record, role and authentication refusals remain unchanged.
Index insertion keeps its original captured finite range, including
placeholder mode; the separate supplied-record index theorem alone is not
used as an all-mode evaluation argument.

The complete initiation and response senders, queued handshake send worker,
and keepalive caller now have exact finite counterparts. The existing finite
session evaluator supplies keypair allocation. Buffer and keepalive allocation
use the existing finite encounter evaluator; original MAC, timer, routing,
queueing and reference-release paths remain. Queuing future work does not
execute it recursively, and successful transmission is not assumed or claimed.

The rate limiter, cookie validation, uncached reply sender and cookie sender
also have exact finite counterparts, substituting only their actual allocation
loops. The complete handshake reception composes these with the finite
consumers, response creation/session/sending and keepalive. It reuses the
shared dispatch body. The original native receive step retains its ring update
before reception and its queue-length payment only after normal return,
including the empty-ring result and every Stop. Two short source factors
expose validation and reception callbacks; no shared source is edited.

Public contracts use `Campaign2.AgreesOn True`; stronger native source
equalities preserve complete outcomes before projection. This establishes
finite call evaluation, including original exhaustion and other Stops. It
does not establish useful service, practical cost bounds, activation occupancy
adequacy or global operation completion. Those remain separate H5 obligations.

Claims are in `InitiationFiniteClaims`, `ConsumerFiniteClaims`,
`SendBufferFiniteClaims`, `ResponseSenderFiniteClaims`,
`InitiationCallerFiniteClaims`, `KeepaliveFiniteClaims`, `CookieFiniteClaims`
and `ReceptionFiniteClaims`, with 15 new public heads in `Statements.lean`.
Their corresponding source files contain the finite composition and exact
source equations; `HandshakeFiniteSource` holds the shared finite curve
helpers. Existing owned initiation and consumer stages gain small callback
parameters with their old definitions retained as exact default adapters.
All existing headers and meanings are retained. Three inherited elevated
proof-limit settings in the two consumer source files were removed after
stock-limit checks; no proof limit was raised. The existing owned
`PendingTicketWorkerFrames` and `InitiationCoverageFrames` remain frame
files and needed additional adapter unfolds; `HookInitiationSource` needed
the same source adaptation. No frame was deleted, and no mirror/shared layer
was changed.

Independent dependency and exact-source reviews found no semantic defect.
The audit checked every reachable curve/allocation leaf and the finite
crypto, lookup, index, socket, routing, timer, staging and release tails.
It also checked all existing modified-source signatures and default callback
meanings. The finite claims do not follow merely from the earlier normal-result
record measures. The next independent step is finite activation composition,
then copied-world scheduler consistency and the outer scheduler.

Validation of the exact final tree passes. Scoped builds pass the real
split imports, including complete reception. An initial broad terminal build
failed in the owned pending-ticket frame because its source simp list omitted
the new adapter; a clean stock-limit repair probe and focused build corrected
it. The corrected terminal build passes 1,501 jobs. The first full gate
then failed in `InitiationCoverageFrames` and `HookInitiationSource` for the
same omitted adapter unfolds, with a resulting unused-simp warning. Their
unchanged statements passed a 978-job focused build after the proof edits.
The final gate passes 3,033 jobs and audits 1,657 terminal declarations with
standard axioms only. Fresh whole-tree kernel replay passes at actual exit zero.
The two initially
overlapping scoped builds used identical source inputs;
no source changed while they ran. No failure is treated as infrastructure noise.
The inherited mirror Env:865 String.mk warning remains unchanged.

Draft ledger at unchanged capped and proof limits: initiation helpers/creator,
five probes (four clean, one corrected factor-unfold failure); consumers,
six clean probes; initiation sender/worker, one clean probe; cookie/rate/reply,
four probes (two corrected form failures and two clean). Root response,
buffer, keepalive, reception and frame repair used eight probes (six clean,
two corrected failures): a reserved binder name and an incorrectly qualified
private source name, the latter also exhausting the stock heartbeat while
checking its ill-formed source equation. The corrected source checks and
all final narrow axiom audits pass with standard axioms only. No infrastructure
rerun, guest run or KILLED outcome occurred.

This tranche adds 56 theorems, including 15 public heads, in 19 new modules.
H5 has 1,218 theorems / 163 headlines in 275 modules; three reusable source
specializations bring H3 to 1,305 / 45 without changing its claim scope.
The campaign has 8,915 / 762 in 2,102 modules. All 148 preceding H5 terminal
names and order remain. H1–H4 and H6 retain their documented complete scopes;
H5 global completion still waits for the confirmed environment fixes.

## H5 send, timer and batch outer budgets, 2026-10-19

The actual send-worker loop now reaches its real completion marker and an
empty send queue on every normal result within its captured
`records.length + 1` budget. Its complete caller retains record suffixes,
and removing only the unreachable exhaustion continuation preserves every
original outcome and Stop. The original absent-device and crypt-work guards,
queue reset and captured loop remain in that source equation.

Every normal original timer episode now has a final actual done turn at its
captured budget, or takes the original absent-device branch. The proof uses
the existing wheel observer, its exact erasure and the concrete yielding-turn
measure. It creates no operational walker. A stopped episode retains its
original Stop; this non-prefix observer supplies no partial turn list on Stop.

The actual recorded batch loop retains suffixes before its drain suffix.
Every continuing turn consumes records through its actual scheduler and send
worker. Adding arbitrary extra fuel beyond the original record-derived bound
preserves the exact original outcome and projected final state, including
callback errors. A done turn may also consume records; strictness is not an
if-and-only-if characterization of yielding. Neither this loop theorem nor
the other budget claims asserts callback finite evaluation, activation
occupancy adequacy, recordless adequacy or the later completion guard.

Claims are in `SendLoopRecordClaims`, `TimerBudgetClaims`,
`BatchLoopRecordClaims` and `BatchBudgetClaims`; public heads are appended in
`Statements.lean`. Physical send frames are in `SendLoopRecordFrames`.
`TimerBudgetModel` supplies the pure receipt predicate; the corresponding
source files connect the unchanged original calls. `RecordBudgetSource`
factors the owned finite-forIn induction. The existing owned scheduler budget
theorem now uses it with an unchanged statement; no shared lemma is edited.
No mirror changes, frame deletions or proof-limit increases are made.

Independent source review checked send and timer composition, batch suffix
preservation and appended-fuel source equality. The sole batch finding was
the overstrong strictness comment, corrected as above; no semantic finding
remains. A separate scope audit confirms finite callback composition is still
meaningful independent H5 work before the environment fixes land. The next
tranche connects existing finite curve/index/allocation evaluators to actual
handshake callers; the current normal-result measures do not claim this.

The exact final tree passes the full gate: 3,014 jobs and 1,642 terminal
statements, with only the three standard axioms. Fresh whole-tree kernel
replay passes at actual exit zero. The scoped terminal build passes
1,474 jobs, including the real split-file imports. The preceding
send/timer and batch-suffix scoped builds also passed. The inherited
mirror-owned Env:865 String.mk deprecation remains unchanged.

All draft checks use unchanged capped limits and stock proof limits. Send
composition used 14 probes: five clean and nine corrected proof-form failures.
Timer budgets used six: five clean and one corrected failure. Batch suffix
preservation used three: two clean and one corrected Hoare presentation
failure. Batch extra-fuel adequacy used seven: five clean and two corrected
constructor/import/projection failures. All new declarations' narrow axiom
checks use only the three standard axioms. No infrastructure rerun, guest run
or KILLED outcome occurred.

This tranche adds 35 theorems, including eight public heads, in 11 new modules.
H5 has 1,165 theorems / 148 headlines in 256 modules; the campaign has
8,859 / 747 in 2,083 modules. All 140 preceding H5 terminal names and order
remain unchanged. H1–H4 and H6 retain their recorded scopes and counts;
H5 global termination still waits for the confirmed environment fixes.

## H5 scheduler and timer record measures, 2026-10-19

The original dispatcher now retains supplied-record suffixes and strictly
consumes records when it reports work. Every normally continuing scheduler
turn strictly consumes records, including the actual guarded NAPI and
resumption paths. Copied consistency trials retain their original state and
do not count as committed progress. Whole scheduling and fixture delivery
have concrete normal suffix contracts.

The five original timer callbacks retain suffixes. A normal timer section and
the exact wheel-dispatch unit strictly consume records through their original
guards, callback and pass-step reset. The actual whole timer loop retains
suffixes through every send, clear, crypt, delivery and refusal branch.
Every actual normally yielding timer turn now strictly consumes records. Clear,
send and timer paths use their concrete section calls; the crypt path yields
only when its state-preserving next-site read changes, forcing a strict suffix.
These are normal-result contracts; the arbitrary worker/timer parameters of
the section leaf alone do not assert actual wheel selection.

Each normal committed activation receipt in the initialized journal now
strictly decreases its own actual supplied record list. The source evidence
comes from that receipt's original native call, with the same final
projection. Earlier receipts remain available when an enclosing operation
later stops. No stopped final state or discarded-probe progress is invented.

The scheduler's captured outer budget is adequate: its actual
`records.length + 1` turns cannot normally exhaust with the noncompletion
marker. The exact original schedule agrees, on all supplied-record outcomes,
with its existing bounded loop followed by unit return, retaining every
callback Stop. This does not establish callback finite evaluation,
activation occupancy adequacy or global completion.

Claims are in `SchedulerRecordClaims`, `SchedulerBudgetClaims`,
`DeliverySuffixClaims`, `TimerCallbackSuffixClaims`,
`TimerUnitRecordClaims`, `TimerLoopRecordClaims`, `CommittedRecordClaims`
and `TimerTurnRecordClaims`, with public heads in `Statements.lean`.
Physical frames are isolated in `SchedulerRecordFrames`,
`TimerLoopRecordFrames` and `TimerTurnRecordFrames`;
`TimerTurnRecordEffects` holds the pure strict-suffix inference. Source proofs reuse the existing original
scheduler, timer-loop and journal factors. No mirror or shared layer changes,
new operational walker, frame deletion or proof-limit increase is made.

Independent source reviews found no semantic mismatch in scheduler, delivery,
timer-unit, timer-loop or committed-receipt correspondence. One duplicate
local invariant frame was replaced by `product_invariant_retains`.
Root review also checked the scheduler budget induction and exact
all-outcome source equation.

The combined gate passes 3,003 jobs and 1,634 terminal declarations with only
the three standard axioms. Scoped terminal and isolated timer-turn builds also
pass. Fresh whole-tree kernel replay passes at actual exit zero.
The only build warning is the already recorded
mirror-owned Env:865 String.mk deprecation; the mirror remains untouched.

Draft checks were capped at the unchanged default limit. Scheduler measures:
25 probes, nine clean and 16 corrected proof-form failures, including one
stock heartbeat and one stock recursion failure. Delivery: two probes, one
corrected inference failure and one clean result. Timer-unit strictness:
four probes, two corrected form failures and two clean results. Scheduler
fuel: nine probes, five clean and four corrected form failures; a separate
empty-input orchestration launch did not deliver draft source and has no
claimed proof result. Root timer callbacks, timer frames, abandoned unit
drafts, outer suffix and committed-receipt joins used 17 probes: five clean
and 12 corrected failures, including two stock heartbeat failures in broad
unit unification. The successful narrow unit proof replaced those drafts.
Timer-turn proofs: 13 probes, six clean and seven corrected form failures.
A root installation script incorrectly treated the timer-turn handoff list as
a mapping, then prematurely attempted its missing build target (exit one).
The schema was inspected, source installed, and the corrected build passed;
this is an input/integration failure, not an infrastructure rerun.
No infrastructure rerun, guest run or KILLED outcome occurred in this tranche.

This tranche adds 74 theorems, including 13 public heads, in 20 modules.
H5 now has 1,130 theorems / 140 headlines in 245 modules; the campaign has
8,824 / 739 in 2,072 modules. All previous terminal names and order remain.

## H5 concrete whole-worker record contracts, 2026-10-19

[AGENT 2026-10-19] Use ambient-sensitive contracts over the existing
source factories for record measures. Store-only framing cannot establish a
property of the hidden input stream. Keep the old owned store contracts as
same-header instances of the more precise rules.

The original IPv4 FIB lookup and all route queries, IPv6 receive, loopback,
socket sends, WireGuard transmission and complete inner delivery now preserve
a suffix of supplied records on normal return. Their actual lookup, allocation,
namespace, checksum and routing leaves are discharged. No callback premise
remains in these concrete endpoints. Original Stops and failed normal return
values retain their source behavior.

Complete handshake creation, consumption, session installation, initiation,
response and packet reception have the same concrete suffix contract. Index
insertion reuses the existing finite collision-search evaluator. All actual
poll/GRO, softirq, inline NAPI and IRQ-exit paths now have concrete inner-delivery
dependencies. Actual receive, encrypt, decrypt and transmit activations strictly
consume
supplied records whenever they return normally; receive no longer needs an
empty starting ring. Yielded exits consume reschedule records, ended exits
consume section-stop records, and continued iterations preserve suffixes.
Transmit includes its actual cryptAhead encrypt/NAPI prelude and complete
packet disposal/reference payments. Original selected send dispatch likewise
strictly consumes records through its real selection, dequeue, pending test, callback and section wrapper.

These are normal-result measures, not successful evaluation, adequate fuel,
recordless execution or global termination. Scheduler measures and initialized
useful-work progress remain
under development. H5 global termination still waits for the confirmed
environment fixes. The earlier pending-identity and refill findings remain
recorded without a mirror edit or weakened statement.

Projected claims are in HandshakeSuffixClaims, EncryptSuffixClaims,
SocketSuffixClaims, StackLeafSuffixClaims, RoutingIPv4SuffixClaims,
StackSuffixClaims, NapiSuffixClaims, TransmitRecordClaims and Statements.
Physical frames are in
EncryptSuffixFrames, StackSuffixFrames and PollSuffixFrames. Other new files
connect the unchanged original source and existing observers; no new
operational walker is introduced. Four old Index theorem headers stay
unchanged while their bodies instantiate the new precise rules. The shared
campaign-1 layers, mirror and gate remain unchanged.

Independent review found no source mismatch or termination overclaim.
A crypt-module comment was corrected to identify its still-explicit local
NAPI/IRQ obligations; the separate concrete module now discharges them.
Duplicate integer-clock support was removed in favor of the existing fact.
The generic throw fact is reused directly. The physical ambient-update frame
is also reused from the existing clear-worker
layer, rather than duplicated. These reuse cleanups are not state-split
deletions justified by a type change.

This tranche adds 265 theorems and 29 headlines in 38 modules. H2 gains ten
generic supports in two modules, reaching 1,532 theorems and 162 headlines
in 427 modules. H5 reaches 1,056 theorems and 127 headlines in 225 modules.
H1 1,593/75, H3 1,302/45, H4 2,084/217 and H6 1,183/100 are unchanged.
The campaign now has 8,750 theorems and 726 headlines in 2,052 modules.
All previous terminal names and order survive; no baseline frame is deleted.

Validation: the final scoped terminal build passes 1,428 jobs. The reviewed
full gate passes 2,983 jobs and 1,621 terminals with standard axioms only.
Fresh whole-tree replay passes at actual exit zero. Earlier candidates
passed 2,980/1,616 and 2,983/1,621 before the final reuse cleanup; they are
not substituted for validation of the final tree. Exploratory
failures included stock heartbeat limits in initial FIB/socket/lookup proof
composition, generated continuation handling, operation-lift normalization,
missing imports and ordinary proof-form mistakes. Narrow source composition
and exact-head application close these at unchanged limits. Root initially
omitted RoutingSuffixSource from a requested build target; the dependent
real-import probe failed for its missing artifact and passed on one identical
repeat after the explicit target built. A pre-Lean pseudo-terminal setup
permission failure had no confirmed sandbox provenance; ordinary pipe
execution worked. No KILLED banner, guest timeout, cap increase or mirror
change occurred. The only compiler warning is the inherited Env String.mk
deprecation.
The transmit package's proposed filename collided with the already-installed
wgXmit suffix module; root caught it before writing and installed the new
module as TxWorkerSuffixSource, preserving the existing file.

Reproduce with LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 and capped --
scripts/in-bundle scripts/proof-gate, followed by capped -- scripts/in-bundle
lake env leanchecker --fresh Leanux.Proofs. No new mirror-team request:
the already-confirmed completion fixes remain the ranked prerequisite.

## H6 initialized allocation counts and independent H5 suffixes, 2026-10-19

[AGENT 2026-10-19] Carry the persistent allocation frontier through the
existing complete hook journal. Count physical enqueue increments at normal
session-derived hook exits, where the projection supplies an actual successor.
The separate give-up arm and stopped internal writes are not assigned to that
count.

The original scheduler, every deferred constructor, every syscall and the
initialized runner now have strictly ordered successful session stamps.
Their exact observed histories have no duplicate successful allocation stamp;
each stamp has at most one session-derived hook invocation. Paired history
retains equality of session and derived-hook occurrence counts, including a
derived hook that stops. Normal derived-hook wheel effects give zero or one
enqueue, so their full-history sum for any stamp is at most one. This is not
exactly one physical enqueue: disabled guards and an unchanged-expiry shortcut
can contribute zero. The existing give-up cleanup witness remains a distinct
cause. A stopped hook has no projected final wheel state, so its internal
writes are not covered by the completed-enqueue sum.

The counted history is committed execution: discarded consistency trials
retain their original native actions but contribute no committed labels.
These claims use the same original execution, preserve exact JSON/indexed
Stops, and require no supplied callback, invariant, readiness or successful
execution premise. A normal endpoint additionally bounds every observed
successful stamp by its actual final counter. Source composition covers
configuration and inline maintenance, lifecycle, traffic, poll/NAPI,
crypt/transmit, scheduling and all deferred tails. The new state-dependent
rules reuse the existing observer definitions; the three poll and nineteen
scheduler/deferred legacy proof bodies become adapters with unchanged headers.
No shared proof layer or mirror definition changes.

H5 independently closes the actual empty receive-step and ended-iteration
cuts, empty-start activation strict decrease on normal completion, and the
actual final empty iteration/section-stop audit. The final-iteration measure
does not describe earlier nonempty iterations. Actual consumeDataDone now
retains a suffix of supplied records on normal return, with concrete endpoint,
allowed-IP lookup, confirmation, timer, staging and repayment dependencies.
None of these partial-correctness measures asserts executable termination,
successful service or nonempty-worker decrease. Global termination still waits
for the confirmed environment fixes; routing/Stack and socket suffix work
continues independently.

Claims are in HookCountedClaims and Statements for H6, and
ReceiveTerminalClaims, ConsumeSuffixClaims and Statements for H5.
HookCountedModel, ReceiveTerminalModel and SessionEnqueueEffects express the
projected result and pure history arithmetic. Physical/history frames are in
SessionCounterFrames, PollCounterFrames, HookStateFrames,
HookStateNativeFrames, HookTrafficFrontierFrames, HookOuterFrontierFrames and
HookMaintenanceHistoryFrames. Other new modules connect the unchanged source
factories and their concrete callbacks. The two new snapshot lemmas were
factored into HookStateNativeFrames before the final gate. No existing frame
was deleted.

This tranche adds 173 theorems and ten headlines in 28 modules. H3 gains
three generic owned poll rules; H5 is now 801/98 in 189 modules and H6
1,183/100 in 265 modules. The campaign is 8,485 theorems, 697 headlines and
2,014 modules. All prior terminal names and order survive. The mirror and
shared proof layers remain byte-identical to main 783510e8.

Validation: the terminal scoped build passes 1,638 jobs. The full gate passes
2,945 jobs and 1,592 terminals using only the standard axioms, after the
frame-only factoring; the prior gate also passed 2,944 jobs. Fresh whole-tree
Leanux.Proofs replay passes at actual exit zero. The only compiler
warning is the inherited Env String.mk deprecation. Root integration failures
were missing PtrRing and frontier-model imports, then misplaced terminal
imports and a docstring/open order error. These were corrected and rebuilt;
the failing attempts are not passes. Exploratory failures were proof-form
errors, including generated continuations and projection normalization.
Poll factoring also encountered stock heartbeat limits; physical projections
and narrower rules closed it without raising any limit. The isolated audits
and final build have no owned warnings or proof escapes. No KILLED banner,
guest run, infrastructure rerun, cap change or mirror edit occurred.

The new H5 source/terminal review found no mismatch or termination overclaim.
Independent H6 reviews found no defect in enqueue arithmetic or the initialized
same-execution frontier/count composition; one stopped-hook comment was
corrected to distinguish missing final-state information from absence of
partial effects. Reviews were read-only and did not substitute for the gate.
The ranked mirror request remains the already-confirmed completion fixes
(altitude-preserving); this tranche adds no mirror-team request.

Reproduce with LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 and capped --
scripts/in-bundle scripts/proof-gate, then capped -- scripts/in-bundle lake
env leanchecker --fresh Leanux.Proofs. Default memory and proof budgets remain
unchanged.

## H6 initialized caller coverage and local allocation uniqueness, 2026-10-19

The common hook/session observer now follows the complete original initialized
runner. It observes configuration-triggered inline send drains, bulk removal,
stop/down/destruction, traffic injection/flood/batch, observation waits, all
scheduler/deferred callbacks and every syscall tail. The original factories
execute once; erasure retains exact JSON or indexed Stop. Valid receipts,
adjacent successful-session/derived-hook pairs, per-label count equality and
each normal derived-hook's local wheel effect hold even before later failure.
Copied consistency trials remain outside the committed journal.

The complete response, reception and receive-step callers now have a stronger
allocation contract. Their successful session stamps are strictly increasing
and distinct; each stamp labels at most one successful-session receipt and at
most one derived-hook attempt. Normal returns bound those stamps by the actual
final global counter. Stops retain the history facts without inventing a final
state. This local state invariant is not yet transported through the full
initialized driver, so global per-session enqueue counting remains open.

Independent source review found no missing silent hook caller in the concrete
scheduler or retained dispatch arms. Device-down is explicitly observed.
Namespace cleanup and route setup do not call a hook or beginSession. Device
deletion is observed because it can flush send work despite idle crypt/RX queues.
The observe syscall's idle prefix and original post-dispatch waits remain
observed. Reviews distinguish receipt occurrence from termination, allocation
uniqueness and firing. The generic scheduler reviewer authored its generic layer;
independent review here concerns root's concrete composition and source coverage.

Claims: HookInitializedClaims and SessionFrontierClaims. Frames:
SessionFrontierFrames. HookConfigurationSource, HandshakeMaintenance*Source,
HookTrafficSource, HookOuterRulesSource and HookSyscallSource instantiate the
existing configuration, lifecycle and traffic factories. HookRunnerSource is a
generic proof around the existing paired initialized runner; it introduces no
interpreter. SessionFrontierModel/Effects hold the pure allocation invariant;
SessionFrontierSource connects it to actual callbacks. No shared lemma, mirror
file or frame deletion. Additions: 187 theorems, seven headlines, sixteen modules.
The preceding nine headlines now have explicit plain-language docstrings; their
statement headers are unchanged.

Validation: split source build passed 1,223 jobs, wrapper and syscall builds
1,197 and 1,220, and corrected terminal build 1,379. Full gate passes 2,917 jobs
and 1,582 terminals using only standard axioms; fresh TimerDiscipline replay
passes. New source has no warnings; the inherited mirror Env String.mk warning
remains. No infrastructure rerun, killed job, guest timeout or cap increase.

Probe ledger: generic configuration 2 (one corrected append-shape failure);
maintenance 11 (six corrected form/name/inference failures, five clean);
traffic 2 (one corrected default-argument inference failure); allocation
frontier 12 (eight corrected failures, including a default-heartbeat search
replaced by existing frame use, four clean audits). Root runner used two
probes after correcting a generated trailing literal escape; outer wrappers
two after unfolding their native socket factory; syscall two after explicit
predicate inference; initialized composition one clean. Initial terminal
installation failed on missing namespace qualification and was corrected.
Failed recovery environments and warning-bearing failed definitions were
discarded, never counted as checked evidence. Proof limits stayed unchanged.

## H6 concrete scheduler coverage and local session wheel effects, 2026-10-19

The original full poll, softirq, inline poll, IRQ exit, scheduler and all fourteen
deferred-operation constructors now retain the common hook/session journal.
Every native result and Stop agrees with the original execution. All four actual
worker callbacks are supplied; copied scheduler consistency trials retain their
execution without adding committed events. Hook validity, adjacent session/hook
pairs and equal per-counter occurrence counts survive later failure.

Each successful-session pair now describes its actual normal derived-hook wheel
effect: either the old optional wheel entry is retained with no enqueue, or one
fresh entry is installed at the recorded allocation counter of the wheel.
The old entry can be absent in arbitrary states with a matching expiry. These
facts concern the local hook exit, not the final caller or later wheel survival.
Session identifiers and wheel enqueue counters are distinct. Counts here are
invocation occurrences; initialized uniqueness and enqueue/firing bounds remain
open. Independent review found the source cuts and this restricted scope sound.

Claims: HookSchedulerClaims and SessionWheelClaims. Frames:
HookDerivedFrames and SessionWheelFrames. HookCommonSource,
HookNapiCommonSource and HookSchedulerCommonSource supply actual callbacks;
HookSchedulerWorkersSource, HookSchedulerSource and HookDeferred*Source reuse
the existing generic worker and environment factories. The owned H3 poll spine
is factored once into PollCallbackSource; existing poll theorem headers survive.
Two obsolete local lift proofs use the landed framing lemma instead. No frame
fact is deleted and no shared or mirror file changes. Net additions: 198 theorems,
nine headlines and eighteen modules; H3 gains nine support theorems, H6 189.

Validation: scoped common poll/NAPI build passed 1,733 jobs. The full gate
passes 2,901 jobs and 1,575 terminals with standard axioms only; fresh whole-tree
replay passes. Earlier scoped builds failed on two existing H3 proof forms;
the first full gate failed on existing DataDoneClaims and PollBoundSource forms.
Explicit equality elimination, generic-body unfolding and bind association
repair these failures without changing claims. The first PollBound repair
still failed on association; the corrected scoped build passed. The inherited
mirror Env String.mk warning is unchanged; new source is warning-free.

Probe ledger: scheduler 3 (one corrected form failure); derived frames 4
(three corrected form/default-heartbeat failures); focus 3 (one corrected
failure); common callbacks, common NAPI, scheduler instance and claims one clean
probe each. Generic poll used 15 (seven failures, two warning-bearing passes
corrected, six clean passes); wheel and append used 15 (nine corrected failures,
including a discarded tactic prototype with bounds-panic diagnostics); deferred
used two clean probes. The handoff corrected an OS argument-length limit and
dict/list reader mismatches before installation. All failed recovery environments
were discarded. No proof-limit or memory-cap increase, infrastructure rerun,
killed job or guest timeout occurred.

## H5 clear dispatch and H6 complete caller receipts, 2026-10-19

The actual clear callback preserves a supplied-record suffix on normal return,
including last-reference deletion. The actual selected clear-worker dispatch
strictly consumes records through selection, dequeue, sections, clearing and
reference payment. Neither contract assumes callback success or residency.
They are normal-return measure facts; global termination still waits for the
confirmed environment repairs.

All eight hook families now have normal immediate wheel effects in both input
modes. The jittered initiation and data-sent proofs include disabled guards,
bounded actual jitter, and the already-pending data-sent shortcut. The existing
recorded-jitter argument is one generalized mode proof with its previous public
header retained as an adapter.

Complete initiation sending, its worker and selected environment dispatch,
consumeDataDone, and the complete transmit iteration now retain each reached
hook receipt even when a hook or later suffix stops. The transmit adapter is
a local callback variant of shared TxDisposition.stepSource; it reuses the
unchanged disposal suffix and worker wrapper. No shared lemma or operational
loop was copied. Receive receipts describe the four actual caller hooks and
their peer; arbitrary consume arguments do not imply upstream authentication.

Complete response sending, handshake reception and receiveStep retain the
actual successful/refused session cut. A successful cut is immediately paired
with its session-derived hook invocation and the same native WG cut, including
a hook Stop. The counts of successful-session and derived-hook receipts agree
at every persistent-counter label. This is local occurrence accounting:
global serial uniqueness, enqueue/firing counts and initialized scheduler
coverage are separate obligations. The generic deferred send wrapper keeps
its scheduler premise explicit and receives no completeness headline.

Claims are ClearWorkerRecordClaims, JitterHookClaims, HookInitiationClaims,
HookSendEnvironmentClaims, ReceiveHookClaims, HandshakeJournalClaims and
HookTransmitWorkerClaims. Frames are ClearWorkerRecordFrames and the generalized
RecordedJitterFrames. Model/Bridge/Effects files hold projected receipt data,
hidden native witnesses and pure receipt consequences; Source files execute
the existing caller cuts. Independent review found no source mismatch or hidden success premise in the complete transmit iteration; its silent socket, disposal and queued-send paths contain no hook call. No frame was deleted. Additions are 14 H5 and 117 H6
theorems, including twelve headlines, in twenty-two new modules.

Validation: the scoped headline build passed 1,522 jobs before the transmit
iteration addition; split receive/send and handshake builds passed 814 and
226 jobs. Full gate and fresh Progress/TimerDiscipline replay results are
recorded at the checkpoint above. New files introduce no warning; the inherited
mirror Env String.mk deprecation remains outside this branch's edit scope.
No infrastructure rerun, killed job or guest timeout occurred.

Proof-development ledger: clear dispatch used five probes (two corrected form
failures, one pass with an unused simp warning subsequently removed, two clean
passes); initiation used three (one association failure, two clean passes);
receive used nine (six corrected failures, including default-heartbeat proof
search replaced by explicit composition, three passes); selected send dispatch
used two (one inference failure, one clean pass); handshake pairing used
twenty-three (four interrupted diagnostic probes, fourteen corrected failures,
five passes, with a final clean split audit). Transmit used twelve (ten corrected
elaboration/composition failures, two clean passes). Failed environments with
recovery sorryAx were discarded, never accepted evidence. The jitter probes
corrected an unnecessary product-state construction, equality/mode shapes and
binder/record syntax; the installed split also corrected import order and five
unused simp arguments before its clean 185-job build. Handoff installation
corrected a dict/list schema mismatch before the receive/send split build.
All proof limits and memory caps stayed unchanged.

## Independent H5 evaluation and H6 hook receipts, 2026-10-19

The complete original pipeRead and pipeWrite now equal finite evaluators for
arbitrary inputs and FS/Task/Ambient states. The read measure combines remaining
bytes with UInt32 ring occupancy: a positive copy reduces the former, while a
zero-length buffer is released and advances the latter. The write wrapper reuses
the previous inner evaluator. Actual branch records, short copies, packet-buffer
handling, release/cache behavior, wake callbacks, timestamp updates and original
Stops remain exact. The wake recursion is already bounded by fuel and finite
entry lists; other suffix leaves have fixed control and finite hidden-input
lookup. These claims do not assert successful blocking service or fairness.
Independent read-source review found no mismatch or missing unbounded leaf.

Queue primitives, queued initiation, staged send and keepalive now preserve a
recorded suffix on normal return, with concrete release, allocation, timer and
queue dependencies. The owned staging proof was generalized once to retain
Ambient facts as well as WG facts. Its eleven existing public theorem headers
remain literal adapters, and the old private WG-only proof helpers are replaced
by the general source rules. This is proof factoring, not deletion of frame facts
based on compilation. No shared lemma changed. These are suffix contracts, not
strict worker decrease or termination claims.

All eight timer hooks now have exact projected receipts retained on success or
Stop. Six families have their concrete local effects; the two jittered hooks retain
exact source linkage but their broader all-mode wheel claims remain separate.
Session-derived receipts preserve the allocation stamp and enqueue zero or one
wheel entry; no cross-call counting follows from that fact alone. The complete
createDataDone caller reuses its existing item traversal and observes traversal,
authenticated-send and the conditional data-sent hook. Every reached hook receipt
survives a later failure, with exact original outcome agreement. This is one full
caller connection, not initialized completeness for all hook callers.

Claims: PipeReadClaims, PipeWriteOuterClaims, StagingSuffixClaims,
HookJournalClaims and HookTransmitClaims. Frames: PipeReadFrames plus the owned
PipeFreeFrames release-shape strengthening; the old release_ring header is intact.
StagingAmbientRulesSource, QueueSuffixSource and StagingSuffixSource supply the
single generalized proof composition and its native instances. HookJournalModel
holds receipt data, HookJournalBridge hides native evidence, and the Source files
supply actual execution. No frame is deleted. Net additions are 65 H5 theorems,
six H2 support theorems and 25 H6 theorems: 96 total, seven headlines and fifteen
modules. The H2 support count includes 21 generalized declarations replacing
fifteen old private helpers; its headline claims are unchanged.

Validation ledger: pipe-read 19 capped stock-limit probes (seven pass, twelve
corrected failures); outer write one clean probe; queue/staging 21 (nine pass,
twelve corrected failures); hook receipts eight (three pass, five corrected
failures); transmit caller three (one pass, two corrected unfolding failures).
Failed Lean recovery environments were discarded; none is an accepted axiom audit.
One combined scoped build failed because the coordinator requested a not-yet
installed pipe-read target after a handoff-schema error. Correct installation
passes the 1,651-job H5/Index build; the headline build passes 1,500 jobs.
One fresh replay command failed because --fresh accepts only one module; the
corrected separate fresh Progress and TimerDiscipline replays pass. The combined
gate passes 2,861 jobs and 1,554 terminals with only standard axioms. No
infrastructure retry, raised limit, warning suppression or mirror/shared-layer
edit occurred; the inherited mirror String.mk deprecation remains.

## H6 initialized wheel-episode journal, 2026-10-19

The actual initialized runner now retains an ordered receipt for every reached
runTimers invocation through idle, after-advance and observation callers, with
the same JSON or indexed Stop as the original runner. Every deferred constructor
has the same exact-outcome contract. Each receipt records the real entry projection
and actual invocation outcome. A normally completed episode retains its actual
wheel-selection chain and the existing per-turn discipline certificate. A failed
episode retains its exact Stop; this observer does not retain the partially
completed inner turn list. Earlier completed episodes survive a later outer Stop.
Placeholder timer passes have a separate source and are not wheel-episode receipts.

EpisodeJournalModel contains projected receipt data and normal-outcome facts;
EpisodeJournalBridge hides native source witnesses behind that view. The four
Source files wrap the existing episode observer once and instantiate the existing
deferred, syscall and initialized-runner factories. EpisodeJournalClaims contains
the projected claims. No operational runner or scheduler is duplicated, and no
frame file is added or deleted. There is no invariant, callback-success or normal
execution premise on the initialized claim. This closes wheel-episode caller
coverage, not all hook invocation histories, cross-call session serial uniqueness
or global termination. Independent source review checked every native
runTimers route and found no mismatch. It prompted a headline-comment correction
to distinguish reached runTimers calls from silent placeholder passes. The
existing per-turn inspection probes are unchanged; this layer does not claim to
eliminate those probes or derive chronology from ValidHistory alone.

This tranche adds 29 support theorems and two headlines in seven modules. Eight
capped stock-limit probes comprised four corrected proof-shape failures and four
clean passes. The first split build failed on two unused namespace opens; removing
them closes the 1,275-job scoped build. No limit increase, infrastructure retry or
mirror/shared-layer edit occurred. The combined gate passes 2,846 jobs and 1,547
terminals; fresh TimerDiscipline kernel replay passes. The only emitted warning is
the inherited mirror Env.lean String.mk deprecation, which this campaign cannot edit.

## H5 finding checkpoint and remaining closed contracts, 2026-10-19

The [new supplied-record witness](2026-10-19-proof-campaign-2-supplied-pending.md)
is accepted by the actual initialized runner and leaves pendingWork equal
to the encrypt identity after the enumerated queues drain. Its complete
committed journal explains nested requeue followed by resumption, and an
extra empty encrypt dispatch is rejected. This refutes literal pending-identity
emptiness in supplied-record mode. It is not a nontermination result, an
unexecuted-packet theorem, or a Linux capture. Statement artefact is considered
first: pending identities and useful work are different propositions. The
charter is not silently narrowed. The campaign stops at this new finding;
request 4 in the mirror-team document records the follow-up.

Already closed work is retained at this checkpoint. The actual complete
pipeWriteToOut equals its finite evaluator for arbitrary inputs and every
FS/Task/Ambient realization. Every yielded iteration strictly decreases the
remaining copy count; the unchanged full-buffer arm returns or preserves its
original blocking Stop. The sole allocation loop is replaced using the exact
concrete hiddenAllocFinite equality. The merge prefix, short-copy, SIGPIPE,
allocation refusal, page/slot failures and saved-head check remain exact.
This is finite helper evaluation, not universal successful writes or the
outer pipeWrite wakeup/caller composition. Independent review found no
semantic defect in this result.

Concrete arming/wheel placement, caller jiffies, deletion and all eight timer
hooks now preserve recorded suffixes on normal return. These discharge the
receive-completion timer premise without a callback oracle. Clock/unit/wheel
and all other Stops remain exact. Typed source decomposition proves shared
continuations once, avoiding proof-search expansion at default limits. These
are H5 suffix dependencies, not new H6 complete-history or timer-discipline
claims. The attempted queued-work extension failed and is not installed.

Claims: PipeWriteClaims and TimerSuffixClaims, with Source files supplying
original-source factors and exact native execution. PipeWriteFrames contains
the environment-read execution equation, following the existing PipeFreeFrames
convention. RecordedPending is a fail-noisy executable diagnostic; it adds
zero theorems. Seven modules add 43 support theorems and three terminal claims.
H5 is 684 / 86 headlines / 171 modules; the campaign is 7669 / 650 / 1908.
H1 is complete (75 / 1593), H2 complete (162 / 1522), H3 complete (45 / 1290),
H4 complete (217 / 2084), all within their documented scopes over 783510e8.
H5 stops at this finding with global termination/decrease and pipe-read/caller
composition still open; H6 remains 65 / 502 with whole histories open.

Validation: scoped build passes 1348 jobs, including the exact accepted
counterexample and rejected control. The combined gate passes 2839 jobs/1545 terminals with only standard
axioms; fresh Progress kernel replay passes. The preceding initialized-provenance tranche passed
2831 jobs/1542 terminals and fresh Progress plus Index replay. Mirror/shared
layers and gate remain byte-identical to main; all seven new modules are
reachable from the proof root. No theorem/frame deletion is introduced.

Pipe-write used sixteen capped probes (nine passes, seven corrected failures),
with two final clean audits of 23 supports. Its early unused-binder warning
and broad-simplification heartbeat failure were corrected. Timer source used
six probes (three passes, three failures); the final 18-theorem audit is clean,
and the failed queued-work draft was discarded when the finding stop condition
was reached. The root's earlier timer draft failed at default heartbeats with
truncated display; it is separate from those six probes. The uninstalled
pipe-read measure had two probes: one missing-lemma/normalization failure and
one clean UInt32 modular-decrease proof. It is not counted as a result and
requires future whole-loop composition. The finding construction used twelve
probes (four candidate record failures, three elaboration failures, five
successful diagnostics). Independent review corrected the report's initial
all-packet-work wording to the exact tested queue fields; Peer.staged and
arbitrary packet-store emptiness are not asserted. No unchanged retries,
resource raises, infrastructure reruns or KILLED outcomes occurred. The only
build warning is the inherited Env.lean String.mk deprecation; the mirror is
unchanged and no new proof warning is left.

## H5 initialized receipts, source provenance and finite teardown, 2026-10-19

[AGENT 2026-10-19] Extract the owned receipt-preservation arguments once as
predicate-parametric rules, preserving all 24 old theorem headers. Generalize
five owned receive-completion proofs over the existing WG/Ambient prefix
relation and retain their old WG-only signatures as instances. This supplies
Ambient-sensitive suffix facts without duplicating either operational walk.

Every original syscall and the initialized runner now retain the exact ordered
committed dispatch/resume receipt prefix, including before indexed Stops. Their
original JSON and errors agree unconditionally. Each retained receipt has an
actual native entry whose projected before/exit fields match that receipt's
own activation, and derives its activation-specific exit facts. This evidence
does not certify arbitrary caller labels or history positions. Copied consistency
trials, native inner calls and cryptAhead's separate iteration remain outside
the committed Activation.run journal. No initial invariant, callback law or
successful-execution premise is supplied.

Actual peer/key release, responder confirmation, counter validation, receive
queue primitives, cut consumption and timer jitter now have recorded-suffix
contracts. Jitter consumes a strict suffix; the other contracts assert normal
return preservation and keep original Stops. Concrete stats, dishonest and full
ECN leaves close; receive completion still names its unresolved real timer,
queued-send, staged-send and lookup callbacks. No activation or callback
termination follows from these normal-return contracts.

The original freePipeInfo now equals a structurally finite evaluator on every
FS/Task/Ambient state. Its bound counts the stopping test and decreases through
the real buffer-release calls; the selected ring size is preserved on their
normal returns. Accounting, missing-state failures, cache/page-put alternatives,
last temporary-page release and final erasure remain exact. This establishes
finite teardown, not successful freeing or whole-syscall termination. The pipe
read/write bridges and concrete worker/caller composition remain open.

Claims: CommittedSyscallClaims, CommittedInitializedClaims,
CommittedInitializedReceiptClaims, ReleaseSuffixClaims, CutJitterSuffixClaims
and PipeFreeClaims. Source/bridge/model files retain their corresponding native
composition, receipt projection and initialized observer. PipeFreeFrames holds
execution equations and the ring-size frame; no unrelated frame is mixed into
a claim. ReceiveCompletionRulesSource is an owned Index source-rule extraction;
ReceiveCompletionSuffixSource supplies its concrete and conditional H5 instances.
No mirror/shared-layer change or theorem deletion is introduced.

Twenty modules add 122 support theorems and ten headlines: H5 grows by 117
theorems to 638 / 83 headlines / 164 modules; the owned H2 rule extraction adds
15 supports, giving 1516 / 162 / 424. The campaign is 7623 / 647 / 1901.
H1–H4 retain their completed scopes; H5–H6 remain in progress. No new finding
or mirror-team request arises in this tranche. The current pending-unit/queue
relation remains a genuine initialized supplied-record obligation; the older
placeholder and nested NAPI refill findings remain distinct records.

Validation: the initialized scoped build passes 1332 jobs after
correcting an unused/nonexistent namespace open in its split model file; the
expanded provenance/freePipe build passes 1338 jobs. The combined gate passes 2831 jobs and 1542 terminals with standard axioms;
fresh Progress.Statements and Index.Statements kernel replays pass. The first
installation assertion incorrectly compared the new generic rule prefix with
the old wrapper header; it failed before applying the replacements. A subsequent
shell command built only the prior reachable tree, which is not validation of
the uninstalled changes. The corrected installation separately verifies all
literal headers and performs the expanded build.

Probe accounting: initialized runner six probes (four corrected failures,
two clean); release/RX eight (three corrected failures, five clean); cut/jitter
two clean; pipe-free eighteen (sixteen corrected drafts, two clean), followed
by independent source review; provenance four clean, auditing 29 new and 24
existing declarations. Its initial handoff exceeded the shell argument limit
before running or writing, then used a single checked JSON transfer. Receive
completion used eight probes (four corrected failures, four clean), auditing
25 new and five existing declarations. One failed receive diagnostic exceeded
the tool display budget; this capture loss is recorded. An independent review
of the release/cut/jitter contracts found no semantic defect. All final audits
use only standard axioms. All heavy work is capped at the unchanged memory
limit, with stock proof limits and 32 threads/16 guest slots; no infrastructure
rerun or KILLED outcome occurred. A separate uninstalled timer draft failed
at the default heartbeat limit and its diagnostic was also truncated; its
broad matching is being replaced, not counted as a result.

## H5 caller receipts and native finite/suffix composition, 2026-10-19

[AGENT 2026-10-19] Reuse the existing callback factories and extract the five
owned traffic erasure arguments once as generic rules. Retain the original
H1 theorem headers exactly. Keep record consumption, call provenance and
finite executable evaluation as separate obligations.

All fourteen original deferred constructors and the original inject, flood,
batch-item, mixed batch, afterBatch and observe paths now retain the ordered
committed Activation.run journal. Original outcomes and Stops are unchanged;
earlier receipts survive later failures. Native admission, transmission,
multicast, inline NAPI and guard leaves are lifted only where their source
has no Activation.run call. ValidHistory remains exit accounting only, not
standalone provenance of arbitrary receipts. Syscall/initialized runner
coverage, all worker dispatches and cryptAhead's separate iteration remain
outside this tranche.

The original allocation helper now preserves a recorded suffix using its
existing exact finite evaluator, retaining placeholder, unarmed, count and
cut branches. Native decryptPacket and the existing exact RX preparation and
publication cuts preserve suffixes. The proofs operate over the actual
nested WG/Ambient stack; explicit ambient contracts replace any temptation
to infer this property from store-only frames. IRQ/NAPI, final release and
receive completion remain concrete dependencies. These are normal-return
contracts, not assertions that a normal return occurs.

A separate generic activation rule composes iteration suffix preservation
and strict consumption on yield into strict consumption by any normally
returning actual activation. Continued iterations compose suffixes; ended
iterations consume the real section-stop record; yielding retains its
already-strict suffix across the original suspension append. Occupancy is
read-only. The concrete per-worker iteration premises remain unproved here;
this rule is deliberately not a new terminal whole-worker claim.

Unconditional finite evaluators now equal the original X25519 and its curve
wrapper on arbitrary byte lists, preserving clamping, decoding, encoding
and the null-point flag. The existing exact ladder and inversion bridge are
reused. The original pipe roundup helper also has a finite evaluator for
every Nat input, with a proved final value at least the input. Nat doubling
is its actual source semantics; caller UInt32 conversion and overflow guards
are unchanged. No successful-evaluation premise or cryptographic validity
claim is added. Whole-Runner termination still needs the three remaining
pipe loop bridges and concrete caller composition. Read-only source audit
identified decreasing measures for those loops but is not a kernel proof.

Claims are CommittedDeferredClaims, CommittedTrafficClaims, DecryptSuffixClaims,
ActivationRecordClaims, CurveFiniteClaims and PipeRoundupClaims. The corresponding
Source files supply actual-source composition; NativeSuffixSource supplies
Ambient-aware native composition and primitive contracts, and AllocationSuffixSource
uses the existing allocation evaluator. ActivationRecordFrames contains the
single explicitly named ambient-sensitive occupancy-frame variant. PipeRoundupModel
holds its exact finite evaluator. TrafficErasureSource generalizes five owned
arguments; DriverTagTrafficSource retains all five old headers byte-for-byte
as instances. No shared counterpart layer, operational walker, mirror change
or existing theorem deletion is introduced.

Seventeen modules add 106 support theorems and thirteen headlines. H5 is
521 theorems / 73 headlines / 145 modules; the campaign is 7,491 / 637 / 1,881.
H1–H4 counts and scopes are unchanged; H5–H6 remain in progress. No new finding
or mirror-team request arises here.

Validation: the expanded Progress/Noise scoped build passes 1,585 jobs;
the combined gate passes 2,811 jobs and 1,532 terminal statements with standard
axioms. Fresh Progress.Statements and Noise.Statements kernel replays pass.
The initial replay invocation incorrectly supplied two modules with --fresh;
the checker rejected that invocation before replay, and separate corrected
commands passed. This was a command error, not an infrastructure retry.
The initial deferred/curve split build found one
root-added headline namespace error; after correction it passes 795 jobs.
Deferred source used three stock-limit capped probes (one corrected failure,
two clean); traffic used five (three corrected failures, two clean), replacing
unrestricted matching after default heartbeat exhaustion without raising limits.
Curve used three (one corrected let-reduction failure, two clean). Native suffix
used twelve (eight failed drafts, four clean), including one default-heartbeat
proof-search failure. One native probe's output was accidentally truncated by
the tool output cap; another changed-source probe repeated an unresolved
helper diagnostic before the preceding output had been inspected. Those were
capture/sequencing errors; the final two audits had complete output and no
warnings. Root's activation composition used four probes (one corrected
elaboration failure, three clean). Pipe roundup used five (three corrected
proof/import/warning drafts, two clean). Final individual support audits use
only the standard three axioms. No KILLED banner, guest timeout, raised limit,
infrastructure rerun or unchanged-input retry occurred. Independent review of
deferred, native-suffix and activation packages found no semantic mismatch.
Root inspected traffic extraction and both finite evaluator packages; the five
old H1 headers were checked byte-for-byte. The inherited Env String.mk warning is outside the owned tree.

## H5 concrete decrypt occupancy, committed runs and record suffixes, 2026-10-19

[AGENT 2026-10-19] Separate queue-fuel adequacy, record consumption and
actual call coverage. Reuse the existing physical ring representation,
activation-exit inspector and scheduler callback factories for each argument.

The original decrypt step now returns the actual physical consume result
through concrete NAPI, IRQ, publication and reschedule callbacks. From a
represented resident ring, a normal iteration ends exactly when its live
FIFO is empty and otherwise consumes its head. The captured live count plus
one excludes the existing activation inspector's own exhaustion branch.
Arbitrary stale slots and batch sizes remain covered; positive capacity and
physical representation are explicit. Earlier callback and section-stop
errors remain possible. Initialized reachability of this representation and
finite executable evaluation of callbacks are separate remaining obligations.

The original scheduler now has an ordered projected journal of the two
committed Activation.run callback sites: dispatch and resume. Each receipt
uses the actual callback entry and the existing activationExitRun once,
retaining its original outcome and receipt even on Stop. The dispatcher
records entry after actual selection/section-start work; resumption records
entry after actual detachment. Copied consistency trials retain their exact
original behavior and contribute no committed-call receipt. This tranche
does not include NAPI calls, cryptAhead's separate iteration, attempted
dispatches that never enter a run, or outer initialized-runner coverage.
ValidHistory states exit bounds/counter/suspension facts only: it is not an
arbitrary receipt's origin/entry provenance certificate. Concrete source
linkage is supplied by the actual observer and run_exact, not by that
predicate alone.

Actual recorded hidden reads now leave a strict suffix, including passive
stripping and the source's NET_RX/pending-work bookkeeping. Passive stripping
and peeking leave suffixes. Every normal arbitrary-worker condResched leaves
a suffix; true consumes a strict suffix, while false may consume passive
records. Missing, malformed and unsupported cases retain their Stops.
Recordless inputs are outside these suffix predicates. Pure composition
rules and a single local Ambient-to-product contract lift support subsequent
whole-worker composition; store-only frames cannot imply Ambient properties.

Claims are CommittedRunClaims, DecryptOccupancyClaims and RecordSuffixClaims;
their Model files contain projected data/predicates and pure deductions.
CommittedRunSource, DecryptOccupancySource and RecordSuffixSource contain
source correspondence/composition. DecryptOccupancyFrames and RecordSuffixFrames
hold the physical frames. The local reschedule frame was moved into Frames;
an unused draft projection identity was omitted. No existing theorem or
frame was changed or deleted, and no shared layer or mirror was edited.

Eleven modules add 46 support theorems and seven headlines. H5 is 402
theorems, 60 headlines and 128 modules; the campaign is 7,372/624/1,864.
All other result counts are unchanged. H1–H4 remain complete within their
recorded scopes; H5 and H6 remain in progress. No new finding or request to
the mirror team arises from this tranche.

Validation: journal split build passes 521 jobs, decrypt split build passes
298, and successive Progress.Statements builds pass 756 then 760 jobs.
The inherited Env String.mk warning remains; no owned warning remains.
The full gate passes 2,794 jobs and 1,519 terminal statements; fresh
Progress.Statements kernel replay passes. Root's journal
used eight capped stock-limit probes: three clean and five corrected proof
failures. Decrypt used eight: two clean, one warning draft corrected, and
five corrected failures; broad simplification reached the default recursion
limit once and was replaced with direct constructor reasoning without a
limit increase. Record suffixes used fourteen: three clean and eleven
corrected proof-form failures. Final audits cover all new support declarations
with standard axioms only; failed recovery terms were rejected, never counted
as checked results. No KILLED banner, guest timeout, cap increase,
infrastructure rerun or unchanged retry occurred. Independent reviews found
no semantic defect and confirmed the explicit scope limitations above.

## H4 completion: normal-outcome partition and rejected-update readback, 2026-10-19

[AGENT 2026-10-19] Close the remaining getter cases by the existing actual
request grammar and projected state equality. Keep validation rejection,
port refusal and the key-stage continuation as explicit normal alternatives.

Every normal request from a resident initial device has one of three
source-derived outcomes: no completed update receipt and unchanged WG
state; an actual nonzero-port refusal whose result and WG state are the
whole request's final result and state; or a completed key stage.
A reached port request derives namespace permission from the actual
entry guard. Consequently a completed refused port cannot be zero:
normal zero-port completion returns zero; unsupported random collisions
and missing records retain their Stops. This imposes no global
creatingNet assumption.

The empty-history setter/getter now returns the canonical mixed JSON and
exact final socket, paginated device and cursor effects from the initial
readable state and static getter bounds. The actual set/get pair uses the
setter's resulting Ambient; neither Ambient equality nor getter success
is a premise. This covers early lookup, flag and permission refusals,
including a zero-port request after namespace exit.

The exhaustive normal scalar result joins that partition to original-entry
header, listen-port and private-key semantics and the ordered surviving-cell
fold. The key-stage branch includes negative later peer returns. Together
with the previously checked refused-port readback and mixed key-stage
getter, all normal request branches now have their documented get-after-set
composition. The result remains about actual effective values and
nontransactional updates. Routing effects retain parsed/address-shape and
coherence conditions; total getter completion retains concrete page-space,
cursor/refcount, idle-socket and receive-budget bounds. H5 owns general
operation progress. No final state on Stop is claimed.

RequestTerminalEffects contains four pure language deductions.
RequestTerminalClaims contains the projected endpoint partition and actual
request observer; RequestEmptyReadbackClaims contains getter and original
set/get consequences. RequestCompleteClaims holds the projected exhaustive
result and its two same-request compositions. No new frame or operational
walker is introduced.

The existing charter correction is retained: the configured Linux version
has no per-allowed-IP removal flag, so the checked removal operations are
peer REMOVE_ME/REPLACE_ALLOWEDIPS and device REPLACE_PEERS. The historical
DumpCancellation report remains an internal tailroom correspondence
observation with no externally compared JSON/branch divergence; its
temporary later proof-formula correction was withdrawn, not that report.
There is no new semantic finding or request to the mirror team.

Four modules add twelve support theorems and two headlines. H4 is
2,084/217/593; campaign total 7,319 theorems, 617 headlines and 1,853
modules. No theorem or frame is deleted. All other result counts are
unchanged.

Validation: the first and strengthened terminal builds each pass 2,088 jobs.
The first and strengthened full gates each pass 2,783 jobs and 1,512 terminal
statements with standard axioms. The inherited Env String.mk warning is
unchanged; there are no owned warnings. Fresh replay of the strengthened
Config.Statements passes. The case/empty-getter package used five capped
stock-limit stdin probes: two clean passes, two corrected elaboration failures
and one corrected warning draft. All ten final declarations use standard
axioms. Root's exhaustive-result package passed two clean stock-limit probes,
including the reviewed strengthening, with standard axioms. No resource
failure, proof-limit change, cap increase or infrastructure retry occurred.
Independent review found no issue in the case split, permission deduction,
same-run Ambient linkage or static getter conditions. Its one packaging point
is fixed: the refused-port arm now includes the exact initial-derived errno,
header, cleared-peer, port-bound, socket and selector effects from the existing
same-receipt theorem. The exhaustive scalar apex does not itself assert total
getter success; that remains in the separate same-state getter joins with
static bounds. H4's charter scope is complete at this documented boundary.
H5 whole-worker record decrease/global progress and H6 caller/scheduler
coverage and session-relative counts remain in progress.

## H4 source-selected scalar fold and mixed getter, 2026-10-19

[AGENT 2026-10-19] Compose the existing whole-command contracts along
the same request's WG receipt chain. Keep each update's full actual entry
Peer for the endpoint guard, and use allocation-labelled cells for the
computed scalar expectations.

Every completed peer command now supplies an actual scalar action:
backward retention, an edit to its lookup-selected resident, or a birth
at its missing-key cursor with the actual counter plus one. Exact
selected effects and nonselected retention are applied to the same native
run. The existing index account and device presence transport through
the completed receipt chain for arbitrary attributes; no routing-address
shape premise enters this scalar fold. Action positions agree with the
original peer-attribute positions and returned errno values.

The fold retains stamp, PSK, interval and normalized serialized endpoint.
Negative returns retain earlier PSK/endpoint writes and skip the interval
update. Each endpoint decision uses the actual full peer, including cached
source fields; it is not recomputed from the normalized expected map.
Birth overwrites the selected expected cell. Quiet steps may perform work
or delete peers. The computed map may retain stale cells for deleted peers;
the claim is exact agreement for every actual surviving cell, not an
exact physical-store map or a unique chronological write-event journal.

Completed key-stage retention supplies the expected map from the original
request entry. Normal outcomes identify the chain endpoint with the final
WG state. Stopped requests retain the endpoint of their completed peer
prefix only; an interrupted command's internal effects are not asserted.
The actual mixed getter is then joined at that same normal endpoint:
original header/port/private-key fields, complete JSON, socket and cursor
effects, plus the surviving-cell fold. Other dump fields still come from
the actual final peers; the tracked cell does not determine an entire row.
Routing shape/coherence and static page capacity, cursor funding, idle
socket and receive-budget conditions remain explicit.

ScalarExpectationModel/Effects contain pure actions, updates and fold
transport. ScalarCommandExpectationModel/Effects contain source inputs,
paired receipts and pure WG-chain induction; its Frames file contains
only the WG-cut account/presence transport. Source connects the original
commands and carries the account through the actual chain; Claims exposes
prefix, normal endpoint and input-position consequences.
RequestScalarReadbackClaims derives the original-entry expectation and
joins the unchanged getter contract. No observer, operational traversal,
serializer or shared layer is copied.

Eight modules add 30 support theorems and four headlines. H4 is
2,070/215/589; campaign total 7,305 theorems, 615 headlines and 1,849
modules. No theorem or frame is deleted. Independent review identified
one organization issue: command_input composed a whole original-call
contract in Frames. It was moved unchanged into Source with its imports;
the physical cut transport remains in Frames. Semantic review found no
defect in selection, endpoint guards, identity, chain linkage or scope.

Validation: both the first split and the split after that file move pass
1,536 jobs. The first terminal build found a name collision between the
new Step predicate and an existing Config Step type in one headline;
the explicit qualification corrects it. Corrected terminal build passes
2,084 jobs. The full gate passes 2,779 jobs and 1,510 terminal
statements with standard axioms only. Fresh Config.Statements kernel
replay passes; no owned warnings remain, with the inherited Env String.mk
deprecation unchanged.
The held pure layer used three capped stock-limit probes (two passes,
one corrected failure); the newly joined source used ten more (four
passes, six corrected failures). The three previously reported account
extraction calls are not counted again. All 27 final package declarations
use only standard axioms. Root's three final-entry/getter supports passed
their first stock-limit probe with standard axioms. No resource failure,
limit change or infrastructure retry occurred.

Coverage review found no additional flag, routing or key-effect gap at
the documented boundary. One final join remains: package getter readback
after empty rejected-update histories and prove the normal-outcome
partition into rejection, refused port and completed key stage.
A supplied port with creatingNet=false is rejected before setPort, so this
is a validation-path composition task, not a new semantic finding.
Independent review of the final getter join found no mismatch: the same
actual middle state supplies both scalar agreement and the serialized d;
ReadbackMatches supplies no getter-success premise.
No mirror-team change is requested.

## H4 request-entry scalars and arbitrary peer-command classification, 2026-10-19

[AGENT 2026-10-19] Generalize the existing owned pre-key observer and
peer-tail preservation rules once, retaining their old interfaces as
adapters. Use the smaller index configuration account for scalar selection:
routing readiness is not used by that proof.

The actual request prefix retains allocation stamp, PSK, interval and the
getter-visible endpoint for every surviving peer through generation/fwmark
writes, source-cache clearing, port handling and queued replacement.
Every completed key-stage receipt has this relation both before and after
its actual key operation, including when a later request suffix stops.
The claim requires no initial funding, network mode, device-presence or
success premise. Deletion remains possible and no stopped final state is
asserted.

The original arbitrary peer command classifies its normal endpoint from
actual validation and the original lookup table. Validation refusals and
REMOVE_ME retain every surviving scalar cell. An existing edit supplies
the actual selected key, slot and full entry Peer; every other surviving
cell is unchanged. A missing target supplies the actual entry cursor and
retains every other cell, but does not by itself assert allocation.
The separately proved creation/scalar effects distinguish quiet, refusal
and birth. The account derives selected residency and positive references;
no address-shape, empty-work, survival or numeric slack premise is added.
Original source branches and Stops remain unchanged.

RequestKeyEntriesModel/Source hold the projected entry predicate and the
generic live-prefix/history composition. RequestKeyScalarEffects/Frames
separate cache normalization and physical port/socket/clear-source frames;
RequestKeyScalarSource/Claims discharge the original prefix.
Noise/PortControlSource extracts the existing owned port traversal.
CommandScalarRulesSource extracts four owned metadata spines;
GetterScalarOtherModel/Frames/Source/Claims separate classification,
physical nonselected retention, actual command branches and projected claims.
No shared lemma or mirror definition is copied or changed.

The selected-peer lookup and scalar completion proofs now use the index
account directly. Their old routing-ready interfaces remain exact adapters;
the stronger premise had not contributed to either derivation.

Twelve modules add 58 support theorems and two headlines. H1 gains one
source support and is 1,593/75/273. H4 is 2,036/211/581.
Campaign total: 7,271 theorems, 611 headlines and 1,841 modules.
No theorem or frame is deleted. Twenty owned legacy headers remain
unchanged across the five source edits.

Validation: the first physical split passes 1,526 jobs without owned
warnings. Terminal build passes 2,076 jobs and the full gate passes
2,771 jobs/1,506 terminal statements with standard axioms only. Fresh
Config.Statements kernel replay passes. The inherited Env String.mk
deprecation is unchanged; no owned warning remains.
The pre-key/port extraction used seven capped stock-limit stdin probes:
four clean passes and three corrected rejected drafts (unused binder,
projection/import form and missing checker import). The failed checker
draft's recovery declarations were rejected; all 39 final audit names use
only standard axioms.
The command classification used twelve probes: four clean passes and eight
corrected code/proof failures. All 35 final names, including four old
adapters, use standard axioms. The two account extractions used three
probes: a namespace-warning draft was rejected, followed by two clean
passes, with four standard-axiom declarations. There was no resource
failure, cap change, proof-limit increase or infrastructure retry.

Independent command-classification review checked actual validation,
lookup/acquisition, creation cursor/footprint, endpoint guards and queued
removal/payment. Independent pre-key review checked receipt capture,
actual port branches, source-cache normalization and deletion-aware
replacement. Neither found a semantic defect. Root separately inspected
the source rules and old adapters.
The final expected-map fold and its mixed getter composition remain in
progress, including readback after an empty rejected-update history. The pure expectation draft is still uninstalled pending that
source connection. No mirror-team change is requested.

## H4 actual creation and private-key scalar retention, 2026-10-19

[AGENT 2026-10-19] Expose the existing owned initialization and allocation
source factors once, and reuse the landed creation/acquisition account.
Generalize the existing owned final-header key-stage rules for scalar
retention while preserving their old interfaces.

The actual peer allocator returns ENOMEM with unchanged WG state, or uses
the actual device allocation cursor and the entry peerCounter plus one.
The selected peer has requested/default PSK, zero keepalive and absent endpoint.
This arbitrary-state local claim does not assert global freshness or cursor
vacancy. The full valid-header, missing-target setPeerCmd then retains
UPDATE_ONLY/self-key quiet exits, allocation refusal, or actual
creation/acquisition/update. The successful branch derives the selected
reference funding and final residency from that same run. Its full endpoint,
PSK and return-dependent keepalive formula includes arbitrary later mixed
attributes; no final successor, survival, allocation success or empty-work
premise is supplied. REMOVE_ME and malformed-header classification are
separate existing/source-composition branches.

The actual private-key stage retains the tracked getter scalars for every
surviving incarnation. Its collision path includes actual lookup, release,
removal and queued work; installation includes cookie keys, precomputation,
expiry and staged sending. Pure expiry effects and the original exact
precomputation/identity effects supply the frames. The generic key-stage
source rule is extracted from the owned final-header proof, whose two
existing contracts remain exact-header adapters. No second key loop is
introduced. Normal completion is required; no stopped final state is claimed.

Files: Noise/PeerCreationRuleSource owns the generalized creation composition;
Noise/PeerInitializationSource exposes its initialization factor once.
Roaming/RemoteBirthSource keeps its old theorem as an adapter.
CreationScalarModel/Effects/Frames/Source/Claims and CreationCommandSource
provide defaults, scalar congruence, native selected-field transport, actual
allocation and the complete missing-target command. KeyScalarEffects/Frames
separate pure expiry effects from native retention; KeyScalarSource/Claims
instantiate the generic KeyStagePreservationSource. Existing
RequestFinalHeaderSource.collision/stage headers remain unchanged.

Twelve new modules and 37 theorems add 34 supports and three headlines.
H1 gains two source supports and is 1,592/75/272; H4 is 1,977/209/570.
Campaign total: 7,211 theorems, 609 headlines, 1,829 modules. No theorem or
frame is deleted. Mirror, shared layers and build/gate files are unchanged.

Validation: the corrected split passes 1,523 jobs. The first installed split
failed because CreationScalarFrames lacked its explicit
PeerScalarRetentionFrames import; correction changes no statement.
Terminal build passes 2,064 jobs. The full gate passes 2,759 jobs and
1,504 terminal statements, with standard axioms only. Fresh
Config.Statements kernel replay passes. The inherited Env String.mk
deprecation is unchanged; there are no owned warnings.
Creation had 18 capped stock-limit stdin invocations: six clean passes and
12 corrected failures. Temporary incomplete drafts and elaboration recovery
diagnostics were rejected and never installed; the final 22-declaration
audit, including two old adapters, has standard axioms only.
Root's key-stage work had six stock-limit probes: two corrected structural
or simplification failures and four clean passes. The final 14 new
declarations and two old adapters audit with standard axioms only.
No resource failure, cap increase or infrastructure retry occurred.

Independent creation review checked the actual mirror/factory, allocation
stamp, quiet/refusal alternatives, reference payment and endpoint scope;
no mismatch was found. Independent key-stage review checked actual queued
collision cleanup and every installation callback, with no finding. Old
header preservation is checked at the owned source extractions.
H4 remains in progress for the final source-classified scalar fold and
mixed-peer readback. The pure expectation draft remains uninstalled until
its source connection closes. No mirror-team change is requested.

## H4 funded nested routing and serialized-scalar retention, 2026-10-19

[AGENT 2026-10-19] Propagate the original configured account through the
already-proved WG receipt chain. Strengthen the owned socket view to retain
the scalar fields needed by the getter, reusing its existing operational
proofs rather than introducing another send traversal.

For every completed peer receipt, the outer request grammar first supplies
a completed key stage. Its actual original-entry effect funds the chain.
Each native peer-command contract is then applied to that same valid receipt,
transporting only WG state across intervening branch logs. Thus original
ProjectedEntry and DeviceAddressShape derive each peer's entry/exit account,
input position and nested routed completion certificate. No per-peer routing,
shape or account premise remains. The canonical represented binding tables
are chosen at the actual entry; different trie representations are not claimed
to have identical list ordering. Completed earlier receipts remain covered
when later work Stops; interrupted peer internals remain outside this observer.

The new getter scalar projection tracks allocation internalId, PSK, keepalive
interval and endpoint normalized only by clearing cached src/srcIf. It retains
IPv6 flowinfo and scope. A checked serializer equation shows that this
normalization leaves peerFixedAttrs unchanged for the same peer. The projection
does not include remoteStatic, counters, last handshake or allowed-IP rows;
its equality is not equality of arbitrary full dump rows.

Actual initiation senders preserve the projected map. Their final worker
release, queued clear workers, bounded work drains, timer stop, single and
bulk removal retain each surviving incarnation's scalar value. Deletion is
allowed. These are normal-return contracts with no funding, empty-work,
readiness or survival premise; they assign no final state to Stop.
The full scalar result for an existing selected command is mapped into this
same getter projection, retaining its exact return-dependent interval effect.

Files: RequestFundedCommandsModel/Effects give the receipt domain and pure
grammar/representation facts; Frames transports the account between actual
WG-equal snapshots; Bridge records the native account witness; Source/Claims
compose the chain and original command contracts. GetterScalarModel/Effects
define the normalized projection and pure effects; Frames contains physical
preservation; Source composes the actual sender/drain/removal calls; Claims
exposes six projected contracts. ScalarCommandClaims adds the exact existing
selected result in this projection. Existing H6 SendView/SendSocketFrames
and the H3 remote projection are strengthened locally; no shared layer is
copied or edited.

The socket enrichment semantically retypes 31 existing declarations: nine
definitions/aliases and 22 theorem interfaces. Their theorem header text is
unchanged, but the enriched aliases make the full types stronger; this is
not a claim of definitionally unchanged types. Existing leading projections
stay in place, and the former trailing remote projection gains one tuple
selection. No theorem or frame is deleted. Eleven new modules and 73 new
theorems (65 supports, eight headlines) bring H4 to 1,942/206/559 and the
campaign to 7,174/606/1,817. Other result theorem/headline counts are unchanged.

The corrected installed split passes 1,527 jobs. Its first three attempts
failed on unnecessary namespace opens in the split Model/Effects and a missing
GuardedArmingClaims import; these were corrected without changing statements.
The terminal build passes 2,052 jobs and full gate 2,747 jobs/1,501 terminals;
fresh combined-root replay passes with actual exit zero. The funded-routing
package had four capped,
stock-limit stdin probes: one corrected inference/simp failure and three
clean passes, with all 18 axiom audits standard. Getter retention had nine
probes: seven corrected source/proof/temporary-namespace failures and two
clean passes; its final 44-theorem audit uses only standard axioms. The root
projection adapter had one corrected Endpoint namespace error and one clean
pass, including its three axiom checks. Temporary recovery diagnostics were
failures, never accepted results. Six critical old socket projections checked
in the agent's temporary combined draft; installed dependent builds are the
integration check. No cap increase or infrastructure retry occurred.

Independent review found no mismatch in the queued-work source coverage or
endpoint normalization. Its scope reminder is retained above: tracked scalar
equality does not assert equality of all serialized peer fields. Root reviewed
the funded chain and same-native-call account extraction. The previous optional
private/readback extension independently reviewed without findings after its
commit. H4 remains in progress for whole creation and final stamped mixed-peer
readback; H5 and H6 remain next in order. No mirror-team change is requested.

## H4 nested commands, state adjacency and optional-key readback, 2026-10-19

[AGENT 2026-10-19] Compose the existing outer request and inner peer
inspections through the same native execution witness. Identify only their
WireGuard projections across intervening branch logs; Ambient snapshots are
not equal. Generalize owned source rules once and retain the old interfaces.

Every completed outer peer receipt now determines a nested whole-command
inspection with the exact same before/after snapshots and return code. Both
the outer peer position and inner allowed-IP position correspond to the
original attributes. A negative completed allowed-IP call determines its
peer's errno and makes that peer the last completed outer peer receipt.
Original Stops are unchanged. An interrupted peer has no completed outer
receipt here; this result does not reconstruct its internal routing prefix.
The optional routed composition still requires shape and represented tables
at that actual peer entry; deriving them across the request is next.

Completed key and peer receipts form a source-derived WireGuard-state chain:
the first peer begins at the key-stage exit, adjacent peers share WG state,
and on normal return the last peer ends at the actual final WG state.
With no completed peers, normal completion retains the key-stage WG state.
Stopped requests retain a completed chain without any stopped final state.

The complete public existing-target peer command now derives the acquired
reference and target residency from initial ownership and the actual table
lookup. With valid headers and REMOVE_ME clear, arbitrary later attributes
give the exact final allocation stamp, PSK and full endpoint. A negative
allowed-IP result retains the previous keepalive interval; a nonnegative
finish applies its optional requested interval. There is no queue-empty,
refcount-slack, intermediate-success or final-survival premise. Creation and
early exits remain separate. The final account is ConfigurationInput:
arbitrary malformed addresses do not establish stronger routing ownership.

Optional private-key handling now covers absent as well as supplied keys in
the same final-header/readback claim. The absent case retains original bytes;
the supplied case follows the original unchanged-byte guard or clamping.
The actual mixed setter/getter pair derives readable final data from initial
ownership and address shape. Capacity, cursor lifetime, socket and receive
bounds remain explicit. This is not setter totality or unconditional getter
completion.

Files: RequestCommandEffects contains pure cutoff consequences;
RequestCommandBridge/Source/Claims connect the nested actual inspections.
RequestWgChainModel/Effects define and reason about projected chains;
RequestRecordSource extracts the existing completed-receipt rule;
RequestWgChainSource/Claims connect the actual request. ScalarCommandEffects,
Source and Claims add the whole existing-target scalar result. Owned
QueuedRemoveSource.command_lookup_cut and KeyHeader.record_rule keep their
exact headers as adapters to the generalized rules. Optional-key definitions
and claims extend RequestFinalHeaderModel/Claims and ConfiguredReadbackClaims.
No new frame file is needed, and no mirror or shared layer changes.

Twelve new modules add 61 support theorems and seven literal headlines.
H4 is 1,869 theorems / 198 headlines / 548 modules; campaign
7,101 / 598 / 1,806. H1–H3 remain complete within the register's scope;
H4–H6 remain in progress.

Validation: the exact split build passes 1,870 jobs and Config.Statements
passes 2,041. The full gate passes 2,736 jobs/1,493 terminals; fresh
combined-root replay passes with actual exit zero.
Only the inherited Env:865 String.mk deprecation appears.
The nested-command probes were two clean passes and one corrected binder/list
lemma failure. The scalar-command probes were two clean passes and one
corrected import-assembly failure; a separate shell quoting error occurred
before Lean started. The WG-chain probes were four clean passes and three
corrected proof-form failures. The two optional-key/readback probes passed
cleanly. All audited declarations use only the standard axioms.
Root independently reviewed nested witnesses, WG adjacency and existing-target
source composition. No cap/heartbeat increase, resource failure, guest run
or infrastructure retry occurs in this tranche. Reproduce with the three
capped commands at the top of this report.

## H4 whole-command order, exact scalar returns and final-header readback, 2026-10-19

The unchanged whole setPeerCmd observer now establishes arbitrary-attribute
routing completion order. Nonempty histories have one source-selected target
and either the requested flags or the mask applied after actual creation.
This is source-derived grammar, not an acquisition receipt: empty histories
do not reconstruct validation, lookup or allocation choices. Actual input
positions and first-negative cutoff hold through later Stops. The same run
also supplies the exact routing fold under the existing explicit shape and
initial representation premises.

The complete non-removal acquired update now derives exact PSK and full
endpoint effects and final selected-peer residency from its actual initial
account, base occurrence and resident peer. Optional replacement and every
allowed-IP malformed/negative exit are included. A negative actual return
retains the prefix interval; nonnegative completion applies optional keepalive.
Actual staging and caller payment remain in the same run. The two existing
owned allowed-IP loop contracts are generalized once to result-indexed exits,
with exact old headers retained as adapters. This is not yet the whole-command
selection/birth theorem, and it reports no discarded final state on Stop.

Normal mixed requests with a completed key stage now derive final name/index,
selected mark, generation and port from the original request entry. The exact
private-byte formula retains the original raw unchanged-key guard before
clamping. Absent or unchanged key attributes retain the full original identity.
The same-request mixed getter reads those values and exact JSON/cursor effects;
its selector and socket eligibility are transported from the original entry.
Readability is now derived from initial coherent ownership, actual normal
setter preservation, base-list uniqueness and funded residency. Shape, static
page/cursor/reference capacity and the finite receive bound remain explicit.
A later peer-command errno is allowed; no total setter success is asserted.

**Files and counts.** CommandOrderModel/Effects/Source and InspectionBridge/
InspectionSource/Claims reuse the original command observer/factories.
ScalarAllowedFrames and ScalarTailModel/Effects/Frames/Source/Claims carry the
physical scalar frames, result-indexed effects and actual update composition.
The owned Index/ConfigurationPeerModel and ConfigurationAllowedRulesSource
gain the generic result predicates/rules; both old theorem headers are exact.
RequestFinalHeaderModel/Frames/Source/Claims/ReadbackClaims separate unchanged
header frames from original-entry consequences. ConfiguredReadbackClaims
reuses the common original-outcome adapter and joins readability/readback.
Eighteen modules and 12 headlines add 69 theorems: H4 is 1,801/191/536 and
H2 is 1,501/162/423 (two generic supports); campaign 7,033/591/1,794.
No theorem/frame deletion, mirror edit or shared-layer counterpart.

**Validation.** Whole-command order used eight capped stdin probes: four
clean, four corrected failures, including two default-limit proof-search
timeouts corrected structurally. All 19 audits are standard. Scalar update
used 13 probes: five clean and eight corrected failures, including one
default-limit inference timeout fixed by an explicit local type. Its 22
audits cover 20 new supports and two exact-type old adapters. Final-header
work used ten probes: four clean and six failures; one was a missing-artifact
infrastructure outcome, and its single unchanged retry reached ordinary proof
errors. The other failures were corrected source/form errors; all 14 final
audits are standard. Root readability/composition used four probes: one
corrected binder/projection failure and three clean passes; the final four
audits are standard. No limit or memory-cap increase.

The split passes 1,856 jobs. The first terminal build failed because the
temporary headline extractor stopped at a record-field assignment; it also
reported an ambiguous namespace open. Both were corrected without suppression;
the terminal build passes 2,029 jobs. The full gate passes 2,724 jobs/1,486 terminals;
fresh combined-root replay passes with actual exit zero.
Independent reviews of scalar update, final-header effects and derived
readability found no semantic mismatch; root source review of the whole-command
factory composition found no mismatch. Existing header checks pass. The
inherited Env String.mk warning remains; no KILLED or guest run.

Remaining H4 scope is actual whole-command scalar selection/birth, same-request
nested routing/peer semantics, stamped scalar retention through later removal
drains and general final mixed-peer readback. Full endpoint retention is local
to the acquired update; arbitrary queued socket sends can clear cached source
fields. Whole-request serialization must retain IPv6 flowinfo/scope and use
the actual endpoint-equality guard, which does not compare flowinfo. H5/H6
follow. No new semantic finding or mirror-team request.

## H4 request-to-key continuity, allowed-IP order and funded finish, 2026-10-19

The actual original request now connects every completed key-stage entry to
its original device name, index and identity, one generation increment and
the selected fwmark. With no listen-port attribute it retains the original
port; a nonzero selection is exact; zero selects the actual same/down zero
or the recorded running allocation within the ephemeral range. The required
namespace permission is derived from the actual validation path rather than
assumed. These facts survive later Stops; an internally stopped key stage
has no completed receipt. PortOrigin names an actual successful port receipt
in the same certificate, without separately exposing a numeric predecessor
index.

The existing acquired-update routing observer now has exact arbitrary-attribute
order: REMOVE_ME bypasses replacement/allowed-IP work; completed replacement
precedes input processing; malformed input returns EINVAL without a completion;
the first negative completed attribute is last. Each completion matches its
input position, including a prefix before later cleanup Stops. The same run
also has the exact flat routing fold under the existing explicit address-shape
and initial routed/resident-target premises. The unrestricted order theorem
has none of those routing premises. This remains an acquired-update result;
the public-command wrapper and caller-derived effective flags are next.

The actual normal finish now pays the caller and derives final selected-peer
survival from the same reference account and preserved base-list membership.
It retains the same allocation stamp, PSK and full endpoint, and stores the
optional keepalive interval. Both running branches, actual staging/keepalive
and final peerPut are included, with no readiness, empty-queue or final-survival
premise. This starts at the successful allowed-IP finish cut; earlier negative
or malformed exits and the whole scalar suffix remain separate composition.

**Files and counts.** RequestKeyHeaderModel/Effects/Frames/Source/Claims carry
the projected header history, scalar extraction, physical port/header frames
and original request equations. AllowedOrderModel/Effects/Source and
InspectionBridge/InspectionSource/Claims reuse the unchanged C1 observer.
RemainingLoopSource generalizes the existing owned remaining-list induction
once; the old private RequestOrderSource header is an exact adapter.
ScalarFinishModel/Effects/Frames/Source/Claims join original accounting and
backward retention to derived residency. Seventeen modules and ten headlines
add 106 theorems: H4 is 1,734/179/518; campaign total 6,964/579/1,776.
No frame deletion, shared counterpart, mirror edit or limit increase.

**Validation.** Allowed-order development used 19 capped stdin probes:
six clean passes, one accepted candidate with warnings later fixed, and
12 corrected proof/form failures. Its 48 theorem audits use standard axioms.
Request-key headers used 15 probes: five clean, two with warnings later fixed,
and eight corrected proof/form failures; all 35 audits are standard.
Finish used six probes: two clean passes, one with an unused-simp warning
later fixed, and three corrected elaboration failures; all 13 final audits
are standard (two axiom-free). No infrastructure rerun occurred in these
three development packages.

The first split failed because RequestKeyHeaderFrames did not directly import
the existing owned getDev frame. Adding RequestOrderFrames fixes it; the
corrected split passes 1,525 jobs. The first terminal build failed on a missing
Configuration namespace open in the new routing headline; its corrected build
passes 2,012 jobs. The full gate passes 2,707 jobs/1,474 terminals and fresh
combined-root replay passes. Independent review found one organization error:
finish_value is an operational result equation, not a physical frame. Its
unchanged declaration now lives in AllowedOrderSource; the empty misclassified
file is removed, with zero theorem deletions. The refreshed terminal build
passes 2,011 and gate 2,706/1,474; fresh replay of this final placement passes.
All 65 existing RequestOrderSource theorem headers are unchanged. Independent
reviews of request-entry fields and funded finish found no semantic mismatch;
the allowed-order review found no semantic issue beyond that corrected placement. The inherited Env
String.mk warning is unchanged. No KILLED, cap increase or guest run.

H4 still needs whole-peer-command order/scalar linkage, exact mixed suffix
effects, original-entry final-header/key composition and general successful
readback. H5/H6 follow. No new semantic finding or mirror-team request.

## H4 acquired scalar cuts, retained peer fields and key readback, 2026-10-19

The original acquired-peer update now exposes its completed PSK/endpoint prefix.
The exact source equation retains the REMOVE_ME bypass; the cut claim assumes
that bit is clear and starts with the actual resident selected peer. It records
the ordered PSK write and endpoint/cache effect before the unchanged replacement,
allowed-IP, keepalive, staging and final-payment suffix. Later errno returns or
Stops retain a completed cut. A Stop inside the prefix has no completed cut;
no discarded final state is fabricated. The cut's keepalive interval, reference
count and allowed-IP list still equal the entry values. This is the acquired
update boundary, not a complete whole-peer-command scalar theorem.

The existing owned staging view now also carries PSK, keepalive interval and
the full optional endpoint. Its original physical and operational proofs carry
these fields through actual staged-send and keepalive preparation. Every
surviving peer retains its incarnation and those fields; this does not assert
survival. The full endpoint includes IPv6 flowinfo and local endpoint fields.
These particular functions prepare or enqueue work and do not execute socket
transmission; no stronger claim is made for arbitrary socket sends.

The actual mixed setter/getter pair now reads back the final key-stage identity
and complete JSON/cursor effect under coherent-data and static getter bounds.
Identity still refers to the actual stage-entry device and collision baseline.
A single original-outcome/Returns composition lemma is factored from the older
refusal proof and reused; all three existing refusal claim headers are unchanged.
The new claim does not yet derive requested mixed peer scalar values.

**Files and counts.** ScalarPrefixModel/Effects/Source/Claims separate the
projected cut, pure update effects, original source equation and outcome claims.
PeerScalarRetentionModel/Frames/Claims project the existing staging proof.
Only three existing staging files change: Index/StagingRichModel's cell,
StagingPreservationSource's matching image type, and the final tuple projection
in Roaming/RemoteTransportFrames. Existing theorem headers remain unchanged.
RequestReadbackReturnSource and KeyIdentityReadbackClaims compose actual
outcomes and key readback. Nine modules and four headlines add 20 theorems:
H4 is 1,628/169/501; the campaign is 6,858/569/1,759. No frame deletion,
mirror edit or shared-layer counterpart.

**Validation.** Scalar-prefix work used eight capped stdin invocations:
two clean passes, five elaboration failures subsequently corrected, and one
missing-artifact infrastructure failure. Exactly one unchanged retry followed
that infrastructure outcome and reached elaboration; it failed and is counted
among the five elaboration failures. All 11 final theorem audits are standard.
The staging carry used five probes, three clean and two corrected failures;
68 audits cover 65 carried supports and three new theorems, all standard.
The actual edited-file theorem headers and all three refusal headers were
checked unchanged. Root readback factoring/composition used three clean capped
probes, standard axioms, including the legacy adapter. No limits were raised.

The scalar-prefix split passes 1,383 jobs. The combined enrichment/readback split
passes 1,827, including existing H2 core and H3 remote consumers. The terminal
build passes 1,994 jobs and the full gate passes 2,689 jobs/1,464 terminals.
Fresh combined-root replay passes. Independent source/scope review found no mismatch;
it confirms the cut-only, deletion-aware and post-set getter-bound scopes above.
The inherited Env String.mk
warning remains unchanged; no KILLED, guest or extra infrastructure rerun.

Remaining H4 work is initial-to-key header continuity, the mixed allowed-IP
order/flat-effect join, whole-suffix scalar retention with actual caller payment,
and general successful readback. H5/H6 follow. No new semantic finding or
mirror-team request.

## H4 final identity, getter context and UPDATE_ONLY, 2026-10-19

Every normal arbitrary device setter preserves its optional device-associated
getter socket and selector-table observation. A resident original entry gives
final residency and exact socket/table equality, including errno returns.
Absent observations make no independent socket assertion. The actual identity
and cookie initialization spines are factored once into exact full execution
equations; their old Returns headers remain unchanged adapters.

The completed funded key stage now determines the normal final static identity
after arbitrary later peer attributes. Existing pure key-peer observations
preserve the header through precomputation, expiry and staged fallback, including
the actual queue inspection. The identity relation retains the real
post-collision-removal baseline. A null private key retains that baseline's
public bytes while clearing identity presence; unchanged raw-key comparison is
kept distinct from changed-key clamping. The private-key corollary states this
exact guard/clamp formula. Its before-device is the actual key-stage entry,
not yet the outer original request entry. No final state is asserted on Stop.

UPDATE_ONLY now has whole-command contracts. On a funded existing target,
toggling its bit preserves the complete original outcome, including overflow
Stops and decision logs; both requests explicitly contain a flags attribute.
On a valid command with no public-key table match, it returns zero with
unchanged WG state despite arbitrary later attributes. Header refusals retain
the actual validation priority: missing public key, unsupported flag bits,
then unsupported protocol. Their normal decision logs remain visible; they
do not classify later operational failures.

**Files and counts.** GetterContextModel/Frames/Source/Claims separate the
projection, physical equalities and original factory composition.
KeyObservationFrames contains pure header preservation; KeyIdentityModel/
Effects/Claims carry the installed identity relation, consequences and
same-request final linkage. UpdateOnlyModel/Source/Claims separate flag algebra,
actual source equality and projected contracts. Eleven modules and seven
headlines add 52 theorems. H4 is 1,608/165/492; the campaign is
6,838 theorems, 565 headlines and 1,750 modules. No frame deletion or shared/
mirror change; the two owned PrivateKey legacy headers are unchanged.

**Validation.** Context used four capped stdin probes: two clean and two
corrected failures; all 21 audits (19 additions plus two adapters) are standard.
The root identity work used seven probes: three failed drafts, three clean
passes and one exit-zero audit with two deprecation warnings subsequently
fixed; the final 13 audits are standard. A large definitional-equality proof
was replaced by direct header simplification at the default limit rather than
raising it. UPDATE_ONLY used ten probes: three clean and seven corrected
failures, including two default-limit failures and a simplifier-step failure.
One overbroad rename's diagnostic was tool-truncated; it was not rerun
unchanged. All 13 audits are standard. These probes used stock limits.
The existing PrivateKey file retains its pre-existing 800,000 heartbeat
setting; no limit was increased.

The first split build failed because the narrowed identity-model import did
not provide an unused opened namespace. Removing that open fixed it; the
corrected combined split passes 1,516 jobs; the terminal build passes 1,985.
The full gate passes 2,680 jobs and 1,460 terminal declarations, standard
axioms only. Fresh combined-root replay exits zero. Independent review found no semantic mismatch in the key identity
or original context composition, and prompted a corrected module sentence
distinguishing optional from resident context. Root source review of the
UPDATE_ONLY comparison confirms actual lookup errors are retained and
no absent-flags/log equivalence is asserted. No KILLED or guest run.

During the next scalar-prefix draft, a probe encountered a dependency output
being rebuilt. Its sole unchanged retry reached elaboration and failed;
subsequent corrected proof drafts continue without another infrastructure
retry. No evidence from a failed probe is counted as a proof.

Remaining H4 scope is initial-to-key header continuity, ordered mixed peer
scalar/allowed-IP effects and successful general readback. H5/H6 follow.
No new semantic finding or mirror-team request.

## H4 funded key effects and arbitrary refusal readback, 2026-10-19

Completed key-stage receipts now derive their funding from the original
request entry. The same actual observer supplies their before/after account,
zero return and all-branch key effect. Later arbitrary malformed peer
attributes or Stops preserve these historical facts; no live account is
claimed across that suffix. The original-entry ProjectedEntry premise is
explicit, rather than an unconditional initialized-request funding claim.

Completed key-stage exits and peer-command entries/exits now agree on getter
metadata. On a normal whole-request return they agree with the final metadata.
Early outcomes without these receipts make no metadata assertion; absent-device
observations do not separately assert socket equality. This bridges the key
stage to later peer commands but does not yet derive all requested peer fields.

The complete original mixed getter now runs from an actual initialized endpoint
using derived readability and pagination freshness. Selector, page/header space,
cursor lifetime/reference headroom, idle/empty socket and receive-count bounds
remain explicit. This is the native getter from the returned projection, not
a theorem that an appended runner syscall always succeeds.

Arbitrary mixed requests refused at a completed nonzero-port cut now compose
with the actual subsequent getter. Under the static plan bounds on the
computed generation/fwmark prefix, the pair returns that prefix's exact JSON
and cursor effects. Both operations share the original native entry and
ambient inputs; all other outcomes retain exact provenance. No supplied getter
success or desired final device is used. The older specialized port-refusal
statement keeps its exact header and becomes an adapter to one factored getter
continuation.

**Files and counts.** KeyStageEntryModel/Source/Claims carry historical funding
and actual request composition. RequestMetadataModel/Effects/Frames/Source/Claims
separate metadata history, pure reasoning, physical frames and source linkage.
InitializedReadbackClaims joins initialized data with the existing getter.
MixedGetterFieldClaims factors the getter continuation; RequestReadbackModel/
Bridge/Claims supply projected pair effects and exact original outcome matching.
Thirteen new modules and six headlines add 56 theorems. H4 is 1,556 theorems,
158 headlines and 481 modules; the campaign is 6,786/558/1,739. No frame is
deleted; no mirror or shared layer changes.

**Validation.** The funded-entry package used five capped stdin probes:
one missing-artifact infrastructure failure, its single unchanged retry
(which reached elaboration and failed), then three corrected clean passes.
All 18 theorem audits are standard. Metadata used six probes, two clean and
four corrected elaboration failures, with 27 standard-axiom audits. The
initialized getter join used two probes, one corrected let-binder failure
and one clean pass. Refusal readback used thirteen probes, eight clean and
five corrected failures; all five audits are standard, including the
unchanged-type legacy adapter. The split build passes 1,817 jobs and the
terminal build 1,974. The full gate passes 2,669 jobs and 1,453 terminal
declarations, standard axioms only. Fresh combined-root replay exits zero.
Independent review found no mismatch in funding, metadata provenance or
the initialized same-state getter join. All builds and probes use the
unchanged cap and stock limits; no KILLED or guests. The inherited Env
String.mk warning remains unchanged.

Remaining H4 work: successful mixed peer-field semantics, ordered allowed-IP
prefixes, and general successful mixed readback. H5 and H6 follow. No new
semantic finding or mirror-team request.

## H4 request-entry fields, key stages and derived getter inputs, 2026-10-19

Every completed port receipt in an arbitrary request is now linked to the
original entry across generation increment, optional fwmark assignment and
source/cache clearing. For a normal refused nonzero-port request, the final
header is exactly that entry's generation/fwmark-adjusted header; the result,
cleared sources and unchanged bind/socket/selector context are derived. The
proof handles duplicate saved peer-list entries. Completed receipt input facts
remain available before later Stops; no stopped final state is asserted.

The complete private-key stage now classifies absent/unchanged keys, public
generation, actual collision lookup/repayment/queued removal and ordered
installation from the actual post-removal baseline. First identity, negative
generation result and real staged-send decisions remain in the effect.
A failed public generation skips collision lookup but still reaches installation.
The source contract preserves the real account. Its receipt form currently
requires that account at the recorded key-stage entry; deriving it from the
outer initial request is the next join.

Initialized endpoint coherence now supplies resident serialized peers and
allowed-IP nodes plus unique peer/node lists. Those unique lists imply
freshness at every computed pagination boundary. Total proof-side lookups
have fallbacks, but the proof establishes they are unused on serialized
occurrences. The canonical mixed getter therefore drops separately supplied
readability/freshness premises when these derived facts are available.
Space, cursor lifetime/refcount headroom, socket idleness/emptiness, selector
eligibility and the receive-count bound remain explicit. This is not
unconditional initialized getter completion.

The actual arbitrary peer command preserves getter header/socket/selector
metadata on every normal return, including errno returns. Peer fields and
queued work may change. When the device is absent the optional observation
is absent, so it gives no separate socket assertion.

[AGENT 2026-10-19] Resolve the deferred seven-counterpart metadata draft by
reusing owned proof spines and existing projections. Generalize precompute's
exact execution and public-key lookup once; move the existing owned handshake
init/reset spines once into generic contracts; project existing cache/endpoint
effects. Keep nine old theorem headers unchanged. The rejected draft is never
installed; no permission exception or shared-layer copy is needed. The
[follow-up request](2026-10-19-campaign-2-getter-frame-followup.md) is resolved.

**Files and counts.** GetterReadyModel/Claims and GetterFreshEffects carry the
projected getter data and pure occurrence reasoning. KeyStageModel/Source/Claims
carry semantic key effects and actual source composition. GetterPeerCommandFrames/
Source/Claims instantiate reused leaves and original factories; the generic
initialization spine is Noise/PeerInitializationSource. RequestInputModel/Effects/
Source/Claims carry projected entry links. Substantive fwmark effects are in
RequestInputFieldSource; physical equalities are in RequestInputFrames.
RequestOrderSource now has one reusable validation-entry rule; three old
request theorem headers remain unchanged adapters. Eight headlines and
sixteen modules add 87 theorems: H4 is 1,500/152/468; H1 is
1,590/75/271; H2 is 1,499/162/423. The campaign is 6,730 theorems,
552 headlines and 1,726 modules. No frame is deleted.

**Validation.** Getter input reasoning used four capped stdin probes: two
passes and two corrected proof/typing failures. Key-stage reasoning used
eight: three clean passes and five corrected failures; all ten theorem
axioms are standard. The first metadata architecture used six probes
(four exits zero, one with a warning subsequently corrected, and two failed
drafts); it was not installed. The replacement reuse architecture used six
further probes, four clean and two corrected failures; its 37 theorems and
one pure definition audit use only standard axioms. Request-input reasoning
used thirteen probes: five clean passes and eight corrected failures;
its 35 new and three adapted theorem audits are standard.

Scoped getter, key-stage and metadata builds pass 1,696, 1,421 and 1,380
jobs. The initial request-input split failed on an omitted clear-loop import;
explicit dependencies fix it and the split passes 436 jobs. A superseded
terminal build failed when an overlapping build replaced an output artifact;
the already-running current terminal build then passed 1,961 jobs. This
failure is not a pass, and no additional unchanged run was launched for it.
The combined gate passes 2,656 jobs and 1,447 terminal declarations with
standard axioms only; fresh combined-root replay exits zero. No cap/heartbeat raise,
KILLED or guest run occurs; the inherited Env String.mk warning remains
unchanged.

Independent reviews found no mismatch in key-stage effects, getter occurrence
freshness, initial-to-port fields or the metadata reuse architecture. The
metadata review also checked ten old theorem types, including unchanged
removal, against the prior commit. The next funded-entry draft separately
hit a missing dependency artifact; its one unchanged infrastructure retry
reached elaboration and failed on proof-form errors. Three corrected probes
then passed with standard axioms; that next package awaits installation.
There was no further infrastructure retry.

No new semantic finding or mirror-team request. Remaining H4 work is the
outer-account-to-key-stage join, successful key/peer suffix fields and
arbitrary mixed readback. H5 and H6 remain next in the charter's order.

## H4 initialized ownership and exact refusal endpoints, 2026-10-19

Every normally returned parsed initialized runner now has a represented routing
tree for each present device, and every exact representation has configured,
resident owners with node membership in their allowed-IP lists. Parsing supplies
the actual configuration address bounds. Both placeholder modes, arbitrary mixed
syscalls, device absence/recreation and the real residual account are included.
The account and ownership proofs identify the same retained final state of the
paired runner; returned JSON equality is not used to identify states. No supplied
callback, invariant, final representation or successful allocation premise remains.
This is normal endpoint ownership, not a final-state claim for indexed Stops.

Arbitrary mixed requests now additionally expose exact nonzero-port refusal
endpoints. A completed port receipt with nonzero result fixes the whole normal
request's result and entire projected WG state to that receipt's endpoint.
Source-clearing and zero/nonzero-port field effects are derived from actual
same-request receipt membership. They remain available if later stages Stop.
A successful port receipt alone does not determine final fields because later
configuration continues. Effects still start at the receipt's entry; linking
that entry to the original request across fwmark clearing remains work in progress.

[AGENT 2026-10-19] Factor the owned dispatch and staging traversals once, retaining
all fifteen existing theorem headers as adapters. The staging proofs now use
stock limits; remove their two elevated-limit directives and redundant resets.
No shared layer or operational/account observer is copied. No frame is deleted.

**Files and counts.** InitializedOwnerModel/Claims define the projected endpoint
property and parsed/normal claims; InitializedOwnerSource joins the actual
paired runner. OwnerDriverBridge/Source carry the ledger and optional ownership
through every syscall; OwnerDriverFrames holds physical transport. The owned
DispatchRulesSource is reused by the unchanged-type Roaming adapters.
RequestRefusalModel/Effects/Source and RequestReceiptEffectBridge/Claims supply
the receipt and endpoint reasoning; RequestRefusalFrames is the physical
predicate frame. Index/StagingPreservationSource is the single source traversal;
GetterStagingFrames/Source instantiate metadata preservation. Eight headlines
and sixteen modules add 108 theorems. H4 is 1,422/144/453; H2 is
1,492/162/423; H3 is 1,290/45/265. The campaign is 6,643 theorems,
544 headlines and 1,710 modules.

**Validation.** The dispatch package used eight capped probes: five passes and
three corrected draft failures. The staging package used ten: four passes and
six corrected failures, with all eight old theorem headers retained and the
unmodified later staging source preserved. Its 39 theorem checks and two
contract-definition checks use standard axioms. The receipt package used eleven
probes: six clean passes and five corrected failures; all 37 theorem audits
use standard axioms. The root's first split build failed on an omitted
NoRefusal.append import; the explicit effects import fixes that file boundary.
The corrected receipt split passes 404 jobs. Initialized ownership passes its
first actual module build, 1,608 jobs, and all six new support axiom checks.
Two earlier runner-join drafts had one corrected import/elaboration failure
and one clean pass. The complete Config terminal build passes 1,937 jobs.
The combined gate passes 2,640 jobs/1,439 terminal statements, with standard
axioms only; fresh combined-root replay passes with exit zero. No infrastructure retry, cap change, KILLED or guest
run occurs. All new proofs use stock limits; the inherited Env String.mk
warning remains unchanged and reported.

Independent receipt review found no semantic/source mismatch, including the
normal-only final WG equality, exact zero/nonzero distinctions and completed
effects before later Stops. Independent review of the root's initialized endpoint composition found no
mismatch in state identity, shape transport, absence handling or nonvacuous
representation. The driver author's integration check is not an independent
review of that author's own dispatch proof.

No new finding or mirror-team request. A separate, uninstalled peer-command
metadata package would need counterparts to seven shared structural contracts;
the [interface request](2026-10-19-campaign-2-getter-frame-followup.md) records
their exact names and the missing fields. Owned reuse is being investigated;
the package is deferred under the shared-layer rule, not copied into this tree.
H4 remains open for arbitrary mixed
field/readback composition and initial-to-receipt links, including first-identity
and collision paths. H5 and H6 follow in the charter's order.

## H4 arbitrary request order and queued REMOVE_ME, 2026-10-19

The actual arbitrary DeviceAttrs request now has a projected certificate
for every original outcome, including Stop. Its observer reuses the existing
device factories and preserves the exact original result. Completed stages
occur in source order: generation entry, source-clearing callbacks, optional
listen-port call, replacement, completed key stage, then the peer prefix.
A nonzero port result cuts off replacement/key/peers. Completed peer commands
have the same input-list indices; the first negative peer result ends that
prefix, and malformed input is distinguished from an executed peer command.

The first nonempty receipt is the actual generation operation. Its before-WG
is the request entry and its after snapshot changes exactly the optional
device generation, preserving Ambient at that operation. A normal empty
history preserves the entry WG state. The certificate also ties the whole
receipt list to one actual observation; validity of an isolated receipt alone
would not establish occurrence in this request.

This is completed-call coverage. A key-stage receipt does not imply a key
was installed: absent/unchanged keys can complete that stage. Internal
iterations of a key stage that later Stops, and internal effects of a peer
command that later Stops, are not individual receipts here. The fwmark
write remains an exact silent source step; its clear callbacks and subsequent
phase states are observed. This tranche does not claim arbitrary mixed-field
readback or a final state after Stop.

Whole REMOVE_ME now derives zero return, exact configured-list/public-key-table
filtering and absence of the selected peer from every exact represented
route tree. Its initial lookup match plus the real funded account supplies
residency and positivity. Actual queued drains and reference payments remain;
there is no empty-work, refcount-ceiling, successful-callback or successor-state
premise. Removal takes precedence over arbitrary later attributes, even
malformed allowed-IP entries. Other resident stores may change during drains.

Optional configured ownership now survives actual open/up/stop/down/preexit,
guarded creation, destruction and environment up/down/delete/namespace cleanup.
A separate projected account join derives resident route-owner/list coherence
from optional ownership and the exact initialized residual account.
The final initialized ownership transport through shaped syscalls is still open.

[AGENT 2026-10-19] Export the three reusable physical request frames once under
RequestOrder.Internal when splitting the checked observer, and keep the other
private helpers with their clients. Generalize the existing owned environment
delete proof once, retaining its old Roaming theorem header as an instance.
No observer, accounting interpreter or shared proof layer is duplicated.

**Files and counts.** RequestOrderModel/Effects contain the pure projected
receipt data and language. ReceiptBridge, Source and InspectionBridge/Source
connect original calls and exact observations; RequestOrderClaims and
Statements expose the projected claims. RequestOrderFrames contains physical
equalities. QueuedRemoveModel/Source/Claims define and prove the configured
removal effect. ConfiguredLifecycleFrames/Source carry optional ownership;
Index/LifecycleDeleteRuleSource supplies the shared owned proof spine, and
Roaming/RemoteLifecycleSource retains its old type. InitializedOwnerAccountClaims
joins the same endpoint account. Five new headlines and fifteen modules add
142 theorems: H4 is 1,340/136/438; H2 is 1,467/162/422; the campaign is
6,535 theorems, 536 headlines and 1,694 modules. No frame is deleted.

**Validation.** The request observer used 47 capped draft probes: fifteen
clean passes, one warning-bearing pass corrected, and 31 failed proof drafts
corrected. The exact module split then passed four additional probes,
including minimal model/effects imports and all 110 theorem axiom prints.
The split exports 91 theorem supports and keeps nineteen private, without
duplicating helpers. All final axiom checks use only the standard three.
Queued removal used eight probes, four passing and four corrected draft failures.
Optional lifecycle used five probes: three passes, one corrected proof-form
failure and one missing-olean infrastructure failure before elaboration.
That infrastructure failure received exactly one unchanged-source retry
after the dependency build completed; it passed. The initial lifecycle split
then failed on a missing imported declaration and passed after the explicit
narrow dependency was restored. The account join had one missing-import
draft failure and a clean final audit. Scoped builds pass 1,448 and 1,921
jobs; the combined gate passes 2,624 jobs/1,431 terminal declarations with
standard axioms only. Fresh combined-root replay passes with exit zero.
All new proofs use stock limits and the unchanged memory cap; no KILLED or
guest run occurs. The unchanged inherited Env String.mk warning remains reported.

Independent source reviews found no mismatch in request ordering or queued
removal. The request certificate records clear-callback phase order, not
positional completeness over the saved peer list. The removal review checked
actual lookup funding, selection before later attributes, queued cleanup and
final payment. Exact represented-tree existence makes route-owner exclusion
nonvacuous; physical store deletion and universal successful return are not
claimed.

No new semantic finding or mirror-team request. Remaining H4 work is
initialized ownership, receipt-to-field/final-state links and arbitrary
mixed readback, including first-identity and key-collision paths.

## H4 complete command ownership and queued readback, 2026-10-19

The complete original peer and device commands now preserve configured
routing ownership together with the actual H2 reference account. They cover
lookup and creation, update-only and removal, private-key conflict cleanup,
expiry and staged sends, port refusal, replacement, malformed attributes
and negative peer/allowed-IP results. Address shape is required only for
actual attribute-list members. No successful allocation, final representation
or successor-account premise is introduced. The resulting account derives
resident route owners and their exact allowed-IP-list membership.

Flag-only REPLACE_PEERS now composes the actual queued cleanup with the
complete getter. Normal cleanup derives the empty configured peer/public-key
list and represented routes, while preserving the original header apart
from the generation increment and retaining the initial socket/selector
context. A separate readiness theorem exposes that derived successor.
Every concrete realization of it admits the getter under the initial
capacity and socket-idleness bounds. The combined contract returns the
generation-adjusted empty-peer JSON and exact final socket. It does not
assert that arbitrary recorded cleanup succeeds or that allocated physical
stores become empty.

Ownership now also survives all current original inject/flood/batch,
dispatch/schedule and fourteen deferred worker/guard/timer calls. The proof
joins C1 routing retention and exact base-list framing on the same run.
It establishes the initial ownership predicate for every literal initial
fixture. Initialized lifecycle/syscall composition is still being completed.

[AGENT 2026-10-19] Generalize the existing owned MAC and three key-stage
proof spines once and retain their old statement headers as thin instances.
The new getter and configuration predicates use those same rules. Local
metadata frame variants cover root-list cleanup, keypair release and peer
release; their original refcount, nullable-word and queued-work behavior
remains intact. Three named local variants of C1's NormalRunnerInvariant
rules add actual-trace syscall membership while retaining the final World;
this is the small shared adaptation needed for parser-derived address shape,
not a copied shared layer.

**Files and counts.** Projected claims are in ConfiguredCommandClaims,
ConfiguredDeviceClaims, GetterCleanupClaims and QueuedReplacementReadbackClaims,
with five new terminal wrappers in Statements. Their data is in the existing
configured boundary plus ConfiguredOptionalModel and
QueuedReplacementReadbackModel; native joins are in the corresponding
Source/Effects files. Physical equalities are isolated in
ConfiguredCommandFrames, ConfiguredDeviceFrames, ConfiguredOptionalFrames,
GetterCleanupFrames/TimerFrames/WorkerFrames/MacFrames and the existing
Noise/ResponseMacFrames. Noise/MacSource and
Index/ConfigurationKeyRulesSource contain the single generic source rules;
Index/ConfigurationStageSource retains the three old key theorem types.
OwnerRunnerNormalSource contains the three named local shared-rule variants.
No frame is deleted and no mirror/shared declaration is edited.
This tranche adds 116 theorems, five headlines and 23 modules. H4 is
1,199/131/424; H2 is 1,466/162/421; H1 is 1,588/75/270. The complete campaign
is 6,393 theorems, 531 headlines and 1,679 modules.

**Validation.** Scoped builds pass 1,389 and 1,879 jobs for command/MAC,
959 for metadata, 1,295 for optional ownership, 1,899 for queued readback,
1,396 for the full device package and 1,906 for the final Config root.
The optional module split first failed on an unnecessary namespace open;
the corrected split passes. Metadata used fourteen capped stdin probes:
six passed and eight draft failures were corrected. Full device ownership
used eight: three passed and five failed drafts were corrected, including
a default-heartbeat timeout. The first failed device diagnostic was captured
but truncated in the tool response; it was not repeated unchanged.
Failed drafts with recovery declarations or failed axiom audits were failures.
Final metadata/device audits cover all 47/31 declarations with standard
axioms and no owned warnings. The command and MAC audits pass; optional
ownership needed two corrected draft errors before its all-eleven audit,
and queued readback needed one substituted-name correction before the
three-claim audit. The three shaped runner variants pass at stock limits.
Combined gate passes 2,609 jobs/1,426 terminals. A separate 122-declaration
support audit passes with standard axioms and no warnings; its two scanner/
quoting setup errors occurred before Lean and were corrected. Fresh combined-root replay
passes with actual exit zero.
The sole build warning is the unchanged inherited Env String.mk deprecation.
No infrastructure retry, guest, KILLED outcome or cap increase occurs.

Independent read-only reviews found no mismatch in complete peer-command
ownership or the same-run queued replacement/getter proof and identified the remaining H4 scope: initialized ownership,
arbitrary mixed field/readback composition, queued REMOVE_ME exact effects,
and first-identity/collision readback. These are open tasks, not new semantic
counterexamples; the register does not count ownership preservation as their
completion. No request to the mirror team arises.

## H4 selected-peer ownership and endpoint joins, 2026-10-19

The actual creation call preserves represented configured ownership and
publishes the returned slot on success. The actual allowed-IP removal keeps
configured ownership, deriving its target resident from the normal run.
The complete selected-peer allowed-IP/keepalive/staged-send tail now carries
the real H2 account and preserves configured ownership through malformed
entries and negative insertion results, paying its selected caller occurrence
on every normal return. Initial selected membership and the current account
are explicit; the enclosing command must derive them from its actual lookup
or creation. That enclosing command and the full mixed device wrapper remain open.

Exact structural representation is now unique for a fixed node store and
root. Consequently, the endpoint account and configured ownership can be
joined to any exact routing representation of the same device. Funding
derives resident owners and their exact allowed-IP-list membership. This
uses structural equality, not an inference from extensional lookup agreement.

[AGENT 2026-10-19] Generalize the existing owned allowed-IP tail rule to
require an address contract only for actual list members. Move its existing
forIn control lemma unchanged into a dependency-neutral owned module and
retain the old rule's exact type as an adapter. There is one loop proof
spine; the shared configuration/account layers are untouched.

The getter support now derives actual finite empty-peer readback from an
empty configured list, retained header and ordinary initial selector/socket/
capacity conditions. Its exact JSON contains the unchanged device header
and an empty peers array. This is the getter leg, not yet the complete
queued replacement composition. Physical peer allocations are arbitrary.

**Files and counts.** ConfiguredBoundaryModel/Effects/Bridge/Claims define
the projected account/ownership boundary and endpoint join.
ConfiguredTailSource/Claims compose concrete source calls.
ConfiguredRepresentationEffects proves structural uniqueness.
EmptyMetadataGetterModel/Effects/Claims supply the pure JSON, header
congruence and actual getter. Index/ConfigurationAllowedRulesSource houses
the one moved control lemma and its membership-aware rule; the original
ConfigurationPeerSource keeps the unchanged-header adapter.
No physical frame file or shared-layer edit is needed here. Eleven modules
and four headlines add 34 theorems: H4 is 1,088/126/403; H2 gains one support
and is 1,462/162/420; campaign totals are 6,277/526/1,656.

**Validation.** Scoped builds pass 237, 1,382 and 1,873 jobs. The selected-tail
draft used six capped stdin probes: three failed, three passed; failures
were corrected proof form, a qualified-name collision, and projected-witness
syntax. The failed witness audit printed a compiler recovery declaration;
that invocation failed, and the final all-22 audit passes with standard
axioms and no warnings. Getter support had one failed and one passing probe;
representation uniqueness likewise had one syntax failure and one passing
four-support audit; the endpoint join passed its one-support audit first time.
All new proofs use stock limits. Full gate passes 2,586 build jobs and 1,421
terminal declarations, standard axioms only. Fresh combined-root replay passes with actual exit zero.
No infrastructure retry, guest, KILLED outcome or raised cap.

No new semantic finding or mirror request. Complete peer/device command
ownership, initialized ownership transport and queued replacement readback
remain the next H4 obligations.

## H4 queued cleanup and configured-owner removal, 2026-10-19

Normal complete peer removal now preserves configured ownership of both
represented allowed-IP families. The make-dead proof recovers the selected
resident from the actual removal cut after unlinking, then uses campaign 1's
exact represented erasure. Cleanup preserves the configured list and routing
representation even when reference payments delete resident peer objects.
This boundary membership result needs initial routing and configured owners;
it does not assume empty work, future readiness or a supplied successful callback.

The original flag-only REPLACE_PEERS request now derives zero return and
empty configured peer/public-key lists and represented IPv4/IPv6 routes
after its actual two saved cleanup passes. Initial funding, receive stability,
base coherence, represented routing and interface selection are explicit.
The same empty endpoint is proved for original peerRemoveAll. These are
normal-return claims: Stops remain, physical allocation stores need not be
empty, and attributes after replacement can legitimately create new peers.
The getter composition and general mixed request remain open.

[AGENT 2026-10-19] Extend the existing owned socket observation with the
configuration header, netlink socket and device-selector table for H4 readback.
Project cached and uncached sends from that observation instead of copying
a shared socket proof layer. All previous socket claims and downstream
projections still build. The optional observation retains absence and does
not separately assert socket preservation when no device exists.

**Files and counts.** ConfiguredRemovalFrames contains the physical route
frame; Source/Claims contain actual removal effects and projected contracts.
ReplacementCompletionModel/Source/Bridge/Claims contain boundary predicates,
same-run completion joins and projection contracts; ReplacementCompletionFrames
contains generation frames. GetterMetadataModel/Frames contain the pure view
and socket projections. Ten new modules and three headlines add 27 theorems.
Six existing owned socket/projection files change, with no lemma deletion.
H4 totals 1,055 theorems/122 headlines/393 modules; the campaign totals
6,243/522/1,645. Mirror, shared layers, gate and build target remain unchanged.

**Validation.** Scoped builds pass (1,852 removal jobs, 88 and 1,852
socket/dependent jobs, 106 metadata jobs, 1,290 completion jobs and 1,861
integrated H4 jobs). One split-only namespace error was corrected before the
removal build passed. The removal draft had three failed and two passing
stdin probes; the last pass audited seven supports with standard axioms.
One failed probe printed compiler recovery declarations after elaboration
errors; it was a failure, and the corrected declarations pass without them.
Metadata had one failed namespace probe and one passing four-support axiom
audit. Completion had eight corrected elaboration failures, four exit-zero
probes, and one missing-artifact infrastructure failure while the owned socket
dependencies were rebuilding. Its exact final audit was rerun once after
the build completed; all thirteen supports use only the three standard
axioms. No guest, KILLED outcome, raised cap or further infrastructure rerun.
Full gate passes 2,575 build jobs/1,417 terminal declarations, standard axioms
only. Fresh combined-root replay passes with actual exit zero.

No new semantic finding or mirror request. This closes flag-only normal
cleanup completion, while mixed-request ownership transport and complete
replacement readback remain the next H4 steps.

## H4 initialized routing/account endpoint and owner preservation, 2026-10-19

The initialized configuration inspection joins the existing joint routing journal
to H2's exact endpoint through an identity result projection. It preserves the
original JSON or indexed Stop and completed routing history. Normal parsed
executions derive represented routing, base-list uniqueness, public-key-table
membership, residency of every listed peer, index coherence and the actual
residual reference account at that same endpoint. Parser success supplies the
existing routing address-shape condition. No final-state invariant is assumed.

[AGENT 2026-10-19] Keep owner-to-base membership as a separate boundary
predicate: the represented routing invariant permits orphan raw labels and
does not establish it. The predicate requires every represented allowed-IP
owner to belong to the configured peer list. Initial funding then derives
actual owner residency, and represented list coherence supplies the owner's node membership.
The original allowed-IP setter preserves both configured and resident ownership
for both families, including invalid attributes and ENOMEM. Its initial ownership,
selected configured peer and listed-residency conditions remain explicit.
Insertion/transfer and selected-removal algebra are checked. These local facts
do not yet establish owner-to-base membership throughout initialized execution;
unlinking during removal requires a temporary allowance at its internal cut.

**Files and counts.** ConfiguredOwnerModel/Effects/Source/Claims carry the boundary
predicate, pure effects, funding bridge and projected setter contracts.
InitializedRoutingModel/AccountSource/Source/Claims carry the projected inspection
and reuse landed routing, H2 and funding contracts without another runner walk.
The account consequences are source lemmas, not physical frame lemmas; an unused
reflexive projection helper from the draft was omitted. Eight owned modules and
three headlines add 22 theorems. H4 totals 1,028/119/383; the campaign totals
6,216 theorems/519 headlines/1,635 modules. No shared or mirror file changed.

**Validation.** Two capped scoped builds pass, 914 and 1,849 jobs. Six capped stdin
probes comprise four passes and two corrected proof-form failures; all 20 audited
draft supports use only the three standard axioms, with one unused support omitted
at integration. Independent review found no defect in the configured-owner
contracts. Full gate passes 2,565 build jobs/1,414 terminal declarations with
standard axioms only. Fresh combined-root replay passes with actual exit zero.
No infrastructure rerun, limit/cap increase, KILLED result or guest run. The
inherited mirror deprecation is unchanged. No new Rule Zero finding or mirror-team
request. Existing source factors and the landed routing/account interfaces suffice;
no mirror restructuring is requested.

## H3 initialized handshake caller coverage, 2026-10-19

The concrete failure-retaining handshake observer now reaches every committed
caller through the actual deferred, traffic, socket, dispatch, syscall and
initialized runner factories. Every projected attempt records the exact
journal position and is authenticated at its real setter-entry peer state.
The inspection preserves the original JSON or indexed Stop, and membership is
equivalent to the exact event occurrence. There is no supplied callback,
invariant, readiness or successful-run premise.

The source inventory checks the two incoming handshake setter sites in
Receive.lean through receiveStep and the Env.Batch receive activation. Native
send/timer/control/transmit leaves do not execute those setters; admission
queues the handshake rather than executing it. Their existing RX observers
therefore remain unchanged. Deferred waits and traffic paths use the new
concrete scheduler. Copied consistency trials keep their original RX probes
and remain outside this committed-attempt list. An attempt may be equal-value
or fail before writing. The separate initialized data certificates and normal
latest-origin result close the remaining H3 remote-destination scope; no
physical-write enumeration or final state on Stop is asserted.

**Architecture and counts.** Nine new owned modules add 105 theorems, including
two headlines. HandshakeAttempt{Deferred,Traffic,Outer,Syscall,Initialized}Source instantiate
existing factories; no walker
or physical frame family is copied. HandshakeInitializedModel/Bridge separate
the projected occurrences from native journals, Source proves their exact
positions, and Claims publishes authentication and coverage. Total checked
surface is 6,194 theorems/516 headlines/1,627 modules; H3 is 1,289/45/265.
Other H1–H6 counts and the mirror/shared layers are unchanged.

**Validation.** Three capped scoped builds: 593-job pass, one explicit-alias
unfolding failure corrected, then 1,685-job pass. Eight agent stdin probes:
five passes, three corrected integration failures; an early declaration-form
warning was corrected. All support axiom audits use only the standard three.
No new infrastructure rerun, cap/limit change, KILLED result or guest run.
Full gate passes 2,557 jobs/1,411 terminals. Fresh combined-root replay passes
with actual exit zero. Independent charter-scope review found no semantic defect
or remaining material H3 gap within committed executions and remote destinations.
It checked the concrete emitter and all callers, exact emitted-occurrence wording,
stopped attempts, and the separate normal final-origin contract. The inherited
mirror deprecation is unchanged. No new Rule Zero finding or mirror-team request arose.

## H3 initialized checks, latest origins and handshake scheduler attempts, 2026-10-19

Five new projected headlines establish initialized data-check authentication
and occurrence coverage, normal final latest-setter provenance, and actual
handshake receive-step and committed-scheduler attempt authentication. H3
remains open only for initialized outer transport of handshake attempts.
The original JSON/indexed Stop and local exact outcomes are preserved.

The data certificate comes from the original checkedEndpoint journal entry,
including when its enclosing consume or later runner stops. Its decrypt is at
a strict earlier position and carries the original configured session material.
Current peer identity is conditional on residency; historical authentication
does not imply survival. The outer packet source is copied, not AEAD-bound.

Chronology now composes through the actual poll/GRO/NAPI, workers, scheduler,
deferred work, configuration, traffic, dispatch and initialized runner. Focus
maps only the freshly appended RX suffix; it retains earlier configuration and
birth events. Equal-value setter calls remain explicit, successful birth resets
the returned store location, and deletion remains permitted. The latest-origin
certificate excludes a later setter or reset and fixes both its outer position
and the nested data record's filtered RX position. This covers surviving remote
destinations on normal completion, not cached source/flowinfo fields or stopped
final states.

The concrete handshake overlay reuses the original callback factories. It
records after source conversion and before setPeerEndpoint, even when the setter
or cache-reset suffix stops. Authentication is tied to the actual setter-entry
device. Exact projection recovers the unchanged local and full RX histories;
the pure queue peek is removed by equality, including missing-device Stop.
The instantiated receive callback transports attempts through complete actual
activation, dispatch, scheduling and resumption. Copied consistency probes
remain unchanged in the RX projection; their discarded trial bodies do not
contribute to the committed-attempt journal. Generic projection alone is not
an occurrence-completeness theorem: the concrete emitter and receiver supply
that correspondence. No new Rule Zero discrepancy or mirror-team request arose.

**Files and reuse.** Public claims are RemoteChronologyClaims,
PollAuthenticationCheckClaims and HandshakeOverlayClaims, exposed by Statements.
Their projected models and native bridges remain separate. Physical retention
facts are in PollAuthenticationFrames, RemoteChronologyWorkerFrames and
RemoteChronologyRunnerFrames. Generic configuration and socket/netlink source
rules replace owned duplicated proof bodies; contextual handshake factories
reuse the existing native cuts. Two old packet proof-limit overrides were
removed. No existing shared definition or lemma changed, and no frame was
deleted on the basis of a failed compile. Forty-eight new owned Roaming modules
add 340 theorems, including five headlines: campaign totals 6,089/514/1,618;
H3 totals 1,184/43/256. Other result counts are unchanged.

**Validation and review.** Thirteen capped scoped builds comprised five passes
and eight corrected integration failures; the final scoped build passes 1,676
jobs. Ninety-five capped stdin invocations comprised 49 observed successes,
45 corrected proof-draft failures and one output-parser failure whose Lean
result was not counted. That parser failure received the single recorded
infrastructure rerun; the corrected wrapper reported exit zero and all 64
local-overlay axiom checks. Earlier warning drafts were corrected, and new
proofs use stock limits with the unchanged memory cap. The full gate passes
2,548 jobs and 1,409 terminals, standard axioms only. Fresh combined-root replay
passes with actual exit zero. No KILLED result, guest run, cap increase or shared/mirror edit.
The inherited Env.lean String.mk deprecation remains outside this lane.

Independent review closed one certificate-precision gap by requiring the
nested data occurrence index to equal the selected prefix's RX length. It found
no further defect in the whole chronology, concrete handshake overlay,
instantiated scheduler inspection or projected data certificates. Twelve
directly compared old interfaces retain their statements. Independent review
also checked all 29 headers in eight modified source files; the refactored
old helpers are thin instances.

## H3 reached setters and chronological caller support, 2026-10-19

[AGENT 2026-10-19] Keep stopped-attempt authentication separate from normal
completed-call chronology. Reuse the original RX observer and the landed
publication contracts; strengthen the owned selected-poll composition once.

Three new projected headlines identify the single authenticated setter of a
completed receive call, including equal-value invocations, and inspect every
reached setter of the original initiation and response callers. Attempts are
recorded after source conversion and before the actual setter. Their MAC,
consumer-authentication and source facts survive a later setter/cache-reset or
continuation Stop. The inspection preserves its entry and the original exact
success/failure outcome. This is local caller coverage, not yet initialized
whole-driver attempt coverage or a physical-write trace.

The unchanged data-poll journal already records the endpoint-conversion cut.
New source contracts derive its selected CRYPTED packet and a strictly earlier
actual decrypt/publication certificate, including when consume later stops.
These contracts require the reached publication invariant at poll entry.
They preserve the original observer and its history; initialized transport of
the strengthened endpoint certificate is still open. Current peer identity
can be recovered with residency at the setter input; no later consume-success
premise is used for the certificate.

The chronological model selects the latest relevant setter occurrence for a
surviving destination. Equal-value invocations remain explicit; successful
peer creation resets the returned store location; silent deletion is allowed.
Existing configuration, birth and completed receive observers now preserve
this model. Generic focus rules require an actually inert appended suffix;
historical value coverage alone is insufficient. Whole-driver chronological
composition remains open, so H3 stays in progress. No new Rule Zero
counterexample or mirror-team request arises.

**Architecture and counts.** Twenty-one new owned Roaming modules and one
owned Noise composition generalization add 116 theorems, including three
headlines. Totals are 5,749 theorems, 509 headlines and 1,570 modules.
H1 has 1,587 theorems/75 headlines; H3 has 844/38. Other results are unchanged.
The original poll_checks header and five previously recorded legacy headers
are unchanged. All new modules are reachable from the combined proof root.

Claims are in HandshakeAttemptClaims and ReceiveStepSetterClaims, with
projected Model files and terminal aliases in Statements. EndpointAttempt,
HandshakeAttemptAuth and the PollAuthentication Source files connect actual
calls; their native witnesses remain in Bridge/Effects files. RemoteChronology
Model holds the ordered effect algebra; its Bridge, Classification, Capture,
Inert and Journal Source files connect existing receipts and observers.
Weaker focus rules are thin adapters to the common history-inert proof.
There are no new physical frame families, shared edits, frame deletions,
mirror edits or observer/accounting walks.

**Validation.** The final scoped build passes 1,627 jobs. The full combined
gate passes 2,500 jobs and 1,404 terminal declarations, standard axioms only.
Fresh combined-root replay passes for this checkpoint with actual exit zero.
The unchanged Env.lean String.mk deprecation remains outside campaign scope.

The closed-support ledger has 45 capped stdin invocations: 18 clean passes
and 27 corrected failed drafts. Root integration has 18 scoped builds:
11 pass and seven failed drafts corrected before the final build. Failures
were proof decomposition, bounded tactic search, imports or elaboration;
limits were not raised. One JavaScript syntax failure invoked no Lean.
No infrastructure retry, KILLED outcome or guest run occurs. Independent
reviews found no semantic defect in the new projected claims or capture
adapters. One maintainability issue was corrected by making the weaker
focus rules use the stronger common proof. The census verifies mirror/shared
identity, legacy headers and root reachability. Later held drafts are outside
this checkpoint's counts and validation.

## H3 initialized whole-driver destination provenance, 2026-10-18

[AGENT 2026-10-18] Compose the existing actual source factories with a
destination-origin invariant. Reuse the original RX history and add receipts
at completed configuration setters, peer creation and receive-worker calls.
Keep native execution witnesses behind bridges and public claims over the
campaign snapshot.

This closes the normal initialized endpoint-provenance tranche, together
with the earlier completed-call authentication contracts. Every present final remote
destination comes from an actual completed netlink setter, authenticated
handshake caller or authenticated data consume in the same execution. Initial
fixtures have no peer endpoint to supply an unexplained origin. The public
projection preserves the original JSON result and indexed Stop in both record
modes. No invariant, callback contract, queue alignment, authentication or
successful future execution is supplied as a premise.

The proof discharges the whole caller graph: actual receive selection;
configuration with arbitrary mixed attributes; outgoing workers and transmit
completion; removal, shutdown, recreation and namespace cleanup; all dump
wrappers; unchanged poll/GRO/NAPI and crypt iterations; scheduler and deferred
work; traffic, every dispatch arm and the full syscall/initialized runner.
Configuration receipts use the real conditional setter effect, including
unsupported families and endpoint-equality no-ops. Birth clears exactly its
returned location, including cursor overwrite; deletion may remove entries.
The exact original RX journal supplies strictly earlier AEAD, historical
receiving-key and source-conversion evidence for every selected data origin.
Handshake origins retain actual queue selection and the whole caller's
authentication observation. The observer executes each underlying action once.

The statement is final-value provenance, not an internal-write trace or a
chronological last-writer theorem. A matching earlier authorized destination
can explain a final value; endpoint presence, identity continuity across raw
store reuse and every stopped internal write are not claimed. Completed
receipts survive later outer Stops, but there is no returned final state on a
Stop. Packet endpoints are the recorded outer sources; AEAD does not bind those
outer addresses. These boundaries are explicit and do not finish the literal transition-level
H3 charter. No new Rule Zero counterexample or mirror request arises.

**Architecture.** Seventy new owned modules add 397 theorems: six reusable
Noise source supports and 391 Roaming declarations, including ten headlines.
H3 has 729 theorems and 35 headlines; H1 has 1,586 and 75. The other result
counts are unchanged. Campaign totals are 5,633 theorems, 506 headlines and
1,549 modules, all current over 783510e8.

Public claims are in ReceiveStepRemoteClaims, RemoteBirthClaims,
RemoteControlClaims, RemoteSilentClaims and RemoteProvenanceClaims; terminal
aliases are in Statements. Pure origin, birth, setter and map predicates are
in the corresponding Model files. Native witnesses and execution connections
are in Bridge files. Physical frames remain in the separate ReceiveStepRemote,
RemoteBirth, RemoteConfiguration, RemoteDispatch, RemoteDriver,
RemoteDriverTraffic, RemoteDriverRunner, RemoteLifecycle, RemoteMaintenance,
RemotePoll, RemoteSilent and RemoteWorker Frames files. Source and Effects
files compose actual operations; they do not introduce a replacement driver,
accounting interpreter or scheduler walk.

Three small Noise source modules expose predicate-parametric contracts and
replace repeated owned proof bodies for timer arming, socket sending and transmit processing. Five
existing H1/H2 theorem headers remain byte-identical. No shared lemma or
mirror file changes, and no frame is deleted. Seven trailing blank lines from
the preceding commit are corrected here. All seventy new modules are reachable
from the proof root.

**Validation.** The final scoped Roaming Statements build passes 1,606 jobs.
The combined gate passes 2,479 jobs and 1,401 terminal declarations, standard
axioms only. Fresh combined-root replay passes with actual exit zero. The only inherited compiler
warning is Env.lean:865's String.mk deprecation, outside this campaign's scope.

Development used capped probes with default new-module limits. The per-tranche
ledger records 92 stdin invocations: 45 exit-zero checks (two draft warning
runs were corrected) and 47 failed drafts corrected before integration.
Failures were elaboration/projection form or bounded proof-search problems;
exact callback-head dispatch and smaller existing source cuts resolved the
search failures without increasing limits. Twenty scoped builds include one
failed native-model packaging attempt, corrected by its namespace imports;
nineteen pass, including all affected H1/H2 roots. No infrastructure rerun,
KILLED result, cap increase, guest run or differential check occurs. One
read-only scope-census assertion initially omitted the six already-authorized
campaign root imports; the corrected census verifies shared and mirror
identity and all new root reachability. Independent review confirmed the
final-origin/source connection but found a reporting overclaim: final-value
provenance alone does not prove every endpoint transition authorized. The
register is corrected to in progress. Two independent reviews found no additional theorem/source mismatch. Both
identified one further comment overclaim: the receive-step headline included
normal rejected/cookie calls, so its docstring now makes authentication
conditional on a roaming cause. The theorem is unchanged. Fresh combined-root
replay preceded this comment-only correction; the final gate passes again afterward, with the same counts.

[AGENT 2026-10-18] Keep H3 open after the normal-origin tranche. The next
claim must connect authentication to reached data setters whose containing
consume later stops, and express chronological caller ownership. An older
equal authorized value is insufficient evidence for a particular transition.
Existing handshake attempt audits and complete poll-attempt observations are
the starting points; no mirror change is requested. H4 follows this remaining
H3 work in charter order.

## H3 whole handshake calls and initialized data consumption, 2026-10-18

This step adds four headlines and 119 theorems in 31 owned modules.
H3 now has 25 headlines and 338 theorems. H1 and H2 remain complete at
their stated normal/completed-call boundaries; H4–H6 retain their earlier
status. The campaign totals are 5,236 theorems, 496 headlines and 1,479
owned modules. Every row is current over 783510e8. H3 remains in progress:
the complete driver's final destination provenance, configuration/birth
coverage and effects after a consume returns still require outer composition.

The new all-kind handshake observer executes the existing actual typed
observers for initiation and response, and the original call for every
other message kind. Its erasure is exact on success and Stop. Normal
returns keep the actual MAC/AEAD consumer evidence, prove that the prefix
did not change the remote map, and carry the packet-source setter update
through the entire continuation. A normal no-cut, cookie or other call
preserves the entry map exactly; admitted unsupported kinds retain the
original Stop. No kind, callback, readiness, funding or suffix-success
premise is supplied.

For data, the complete ordered initialized consume list is reused from H1,
with membership equivalent to the actual history occurrences. An
event-only endpoint protocol uses the landed C1 caller composition and
the owned counter/poll factor. C1's publication certificate supplies a
strictly earlier actual successful decryption, its receiving key,
ciphertext and plaintext, and the supporting configured peer incarnation.
The source conversion derives the actual endpoint argument and supported
family. The final theorem applies the complete native consume contract to
that same receipt, including normal nondelivery and completed calls before
a later outer Stop. It assumes no publication head, queue alignment,
caller invariant or successful future operation.

**Statement precision.** `RemoteRetained` says every final present remote
destination comes from the entry map after the actual selected update.
It permits peer/endpoint disappearance and asserts no identity continuity
across recreation. The stronger wording “the endpoint remains present”
has not been asserted. Cached local addresses are deliberately omitted
from the remote tuple; the original endpoint equality does compare those
local fields. IPv6 flowinfo is omitted by both. Outer source addresses are
copied through decryption, not bound as AEAD inputs. Failed consume
prefixes emit no completed consume receipt; their internal writes and
later poll/stack effects are outside this step. Existing failure-retaining
handshake audits remain separate. This is no new Rule Zero discrepancy.

**Architecture and split.** Claims are the six new
`RemoteSessionClaims`, `ConsumptionAuthenticationClaims`,
`ConsumptionDestinationClaims`, `HandshakeRemoteClaims`,
`HandshakeRemoteProductClaims` and `HandshakeRemoteWholeClaims` files;
four terminal aliases are in `Statements.lean`. Pure predicates live in
the five new `*Model` files. Physical effects/frames are
`RemoteSessionEffects`, the nine `Remote*Frames` files and
`HandshakeRemoteFrames`, `HandshakeRemoteProductFrames` and
`HandshakeRemoteOtherFrames`; native witnesses and source composition
live in the remaining seven `*Source`/`*Bridge` files.

[AGENT 2026-10-18] Extend the existing owned socket and staging observations
with one remote-destination component so both callers reuse their established
proof spines. Two old tuple selectors and the local-cache clearing proof
were adjusted; no existing shared lemma changed. All old H1/H2 statement
types remain unchanged. One socket projection covers both cached sends
and uncached replies; one staging projection covers keepalive, staged send
and queued initiation. Existing session/rotation effects, generic creator,
response and receive-completion contracts, timer effects and balanced
lookup/repayment contracts close the remaining continuations. There is no
second publication invariant or driver interpreter.

**Validation.** The scoped Roaming Statements build passes 1,328 jobs. The full gate
passes 2,409 jobs and 1,391 terminals; fresh combined-root
`lake env leanchecker --fresh Leanux.Proofs` exits 0. All 31 new modules
are reachable from the proof root, and all 48 existing theorem headers in
touched files are unchanged. Only the standard three axioms remain.
Commands are in the current-checkpoint section above.

This closed step used 35 capped stdin checks: 14 clean passes and 21
corrected draft failures (root 5/5 pass/fail, clear-source support 2/2,
handshake core 1/3, handshake callers 3/6, initialized data 3/5).
Seventeen scoped builds gave nine passes and eight corrected failures.
Failures were source association, namespace/import, type inference,
projection/tuple selection, parser or local proof issues; draft proof-limit failures were
corrected with explicit projections/types rather than larger limits.
No limit or memory cap was raised. There was no infrastructure rerun,
KILLED outcome or guest run. The final gate and fresh replay each ran
once and passed.

Independent read-only reviews found one inaccurate comment about the
original endpoint equality, corrected above, and no semantic mismatch in
the checked remote core or same-receipt data/authentication/final-state
composition. A separate reviewer also checked all eight whole-handshake modules, the
actual receiver and every new headline, with no further finding.
The mirror, C1 shared layers and gate remain unchanged. The inherited
mirror `Env.lean:865` String.mk deprecation is still reported; this
campaign does not edit the mirror. No new mirror-team request is needed.
The ranked architecture preference remains reuse of typed field groups
and existing callback factors (altitude-preserving); adding proof-only
mirror observers or weakening real branches would not preserve altitude
and is not requested.


## H2 initialized store, slot and owner coherence, 2026-10-18

H2 now closes at normal initialized runner endpoints. The original runner
supplies IndexCore: unique numeric indices and indexed owners, hashed-key slot
coverage, resident positive owners and discharged retirement obligations.
Its actual residual account supplies resident store bounds and current-slot
compatibility. The initialized corollaries take no invariant, callback or
readiness premise. Their Product projection preserves original JSON and every
indexed Stop in both record modes. Stops supply no final-state conclusion;
neither termination nor empty residual work is claimed.

This completes the reachable-state obligation behind the existing lookup,
index insertion/removal/replacement and collision-stream claims. Unhashed
objects and stale numeric fields are outside hashed-session uniqueness.
Earlier arbitrary-state counterexamples remain recorded with their original
domains. There is no new mirror discrepancy or request to the mirror team.

The proof joins concrete source contracts with campaign 1's accounting on
the identical execution. Ordinary preservation contracts still have explicit
Entry/Aux preconditions. Admission derives a new actual ledger; fixed calls
rebase only their actual removal suffix. Inject/flood/batch convert Entry to
Aux after real device-presence guards; batch retains its captured Device.
Actual dispatch and return-to-user tails discharge the final runner
obligations, including ordinary errno returns.

Data ingress derives cleanup references from lookup/acquisition; pure-IRQ
publication separately acquires and repays its selected owner. Poll permits
selected-peer deletion internally and restores Ready through its original
completion getter. TX derives the selected queue loan before completion and
exact disposal. Dumps retain funded cursor replacement. All scheduler
callbacks and fourteen deferred Aux cases are concrete. Six outer deferred
contracts additionally cover absence and ledger rebasing; this is not
all-fourteen AnyEntry coverage.

[AGENT 2026-10-18] Reuse landed accounting/source factors and generalize owned
traversals once. Keep the source-selected account as an exact-run witness
behind the projection; do not reconstruct native state or assume empty work.

| Role | Files under Index unless qualified |
| --- | --- |
| Claims | PollCoreClaims, DumpCoreClaims, WorkerCoreClaims, ReachedSchedulerClaims, DataIngressClaims, ReachedDeferredClaims, ReceiveIngressCoreClaims, ReachedInitializedClaims, Statements |
| Models/bridges | PollCoreModel, DumpCoreModel, DataIngressReferenceModel, ReachedSchedulerModel/Bridge, ReachedControlBridge, ReachedInitializedModel/Bridge; its Source defines the native execution witness |
| Frames | PollCoreFrames, TxSelectionFrames, EncryptCoreFrames, DumpCoreFrames, TimerProductCoreFrames, ReachedControlFrames, ReachedProjectionFrames, ReachedSchedulerFrames, DataIngressReferenceFrames, DataIngressFrames, ReceiveIngressCoreFrames, ReachedTrafficFrames |
| Effects/source | PollCoreEffects, DumpCoreEffects, DataIngressEffects and the new Source/RuleSource families; Noise/DataCompletionRulesSource and existing owned Noise adapters |

Eight bounded local shared variants cover poll peek/counter/composition,
the saved timer scan, three admission-front frames and the socket wrapper.
They stay in Index; no shared layer is copied or edited. No theorem/frame
is deleted. Fifteen legacy type texts compare identically; review also
checked all 228 old declaration headers in modified files. Six poll-operation
proofs moved unchanged from Frames to PollCoreNativeSource after review.
A second wording correction distinguishes conditional preservation from
initialized derived invariants.

The tranche adds 294 theorems, 25 headlines and 66 modules. H2 rises from
1,172/137 to 1,461/162; H1 gains five supports, retaining 75 headlines and its
completed scope. Totals: 5,117 theorems, 492 headlines, 1,448 modules. Every new
module is reachable from the combined root. Independent source/domain reviews
found no semantic defect; authorship was distinguished from independent review.

Development used 98 capped stdin checks: 45 exit-0 results and 53 failures.
One exit-0 control draft had a warning corrected before acceptance. Package
pass/fail counts: poll 5/9, TX 8/16, encrypt 1/1, scheduler atoms 1/0,
scheduler 2/1, dump 9/5, timer product 2/3, controls 4/1, projection 1/1,
deferred 3/2, data ingress 5/10, receive front 2/2, traffic/runner 2/2.
New modules use default heartbeat limits; factoring/reuse resolved proof-shape
and heartbeat failures.

Two missing-olean failures arose when probes overlapped a dependency build.
Each had one infrastructure rerun: scheduler passed; ingress reached a real
proof failure, then passed after correction. TX probe 16 accidentally repeated
unchanged input after an in-memory append failed. This violated the rerun
rule; it is a failed process step, not infrastructure or additional proof
evidence. Later probe construction asserted the intended declaration was
present. No KILLED result or memory-cap increase occurred.

Thirteen integration builds yielded seven passes and six failures corrected
for imports, namespace opens, declaration placement, projection fields and
explicit Lean.Json qualification. The final scoped build passes 1,609 jobs.
The first gate passed 2,361 jobs/1,378 terminals and fresh root replay passed.
The completed tree passes 2,378 jobs/1,387 terminals with standard axioms only;
a second fresh combined-root replay passes (actual exit 0). The only compiler
warning is inherited Env String.mk deprecation; the mirror is unchanged.
No guests ran. Reproduce with the commands above.

## H2 workers, transmit and lifecycle, 2026-10-18

Eight projected headlines cover original wgXmit, inner Stack delivery,
create/open/up/stop/down, and destruction. Transmit and Stack retain current
slot compatibility and IndexCore; the five ordinary lifecycle calls retain
the supplied actual account/configuration/slot/index package. Destruction
asserts absence on normal return without asserting completion. Its separate
account contract requires an empty ledger, empty external loans and inactive
cursors. The actual Env deletion guards derive ledger emptiness on their
normal path; original Env up/down and netnsPreExit retain their supplied
current-cut package.

The transmit proof joins the rich physical frame with campaign 1's exact
same-run transfer: the lookup loan and payment are derived from execution.
Actual creation, stopping and namespace exit reuse the existing source
factors, retirement work and selected send loans. The plain Unit stop journal
is an erasure/composition aid, not a new receipt or stopped-state claim.

Decrypt preparation now preserves IndexCore. Its complete iteration transports
the actual prepare/IRQ/payment/softirq cuts and their remaining-ledger suffix;
the two original NAPI Ready contracts remain explicit premises. The accounting
proofs are reused at those cuts. The source-spine decomposition parallels
HolderDecryptHistory.step_normal/iteration_normal, without copying their
accounting derivations. Original TX disposal frees packets, releases its saved
key and pays the supplied stamped head loan in that order. Full TX selection,
poll/NAPI, dumps and the initialized syscall join remain open.

[AGENT 2026-10-18] Generalize six owned source proofs once and keep their legacy
interfaces unchanged; reuse the existing acquisition and device-field
contracts instead of adding duplicate crypt helpers. Keep native cut evidence
out of the projected headline statements.

Claims are TransmitCoreClaims, LifecycleCoreClaims and eight Statements
declarations. TransmitCoreModel and CryptCutModel contain pure views/native
cut interfaces. TransmitCoreFrames, CryptCoreFrames, LifecycleCoreFrames and
LifecycleEnvironmentFrames contain physical transports. The RuleSource,
PreparationSource, CutSource, DisposalCoreSource, MaintenanceSource,
ControlSource, DeviceSource and EnvironmentSource modules contain actual
source composition. No frame or old theorem is deleted: all 4,737 previous
declarations remain. Six legacy type texts compare identically. The 86 new
declarations in 19 modules bring H2 to 1,172/137 and the campaign to
4,823/467 in 1,382 modules. Other result counts/statuses are unchanged.

Independent review finds no correctness issue in crypt cuts, TX disposal,
transmit/Stack and the projected lifecycle wrappers. The native lifecycle
composition was reviewed by root; its author's integration check is not
counted as independent review. Every claimed result remains a normal-return
contract; stopped paths retain only their already stated journal properties.

Development used 43 capped stdin checks for these packages: 18 passed,
25 failed before correction. One accepted draft's unused-variable warning
was corrected before final acceptance. A default-heartbeat failure was
resolved by factoring declarations/reusing existing source cuts; no proof
limit or memory cap was increased. Scoped builds pass 1,368, 1,376 and 1,506
jobs. One integration build failed on the new destruct snapshot field name
and was corrected from dev to device. The sole remaining compiler warning is
the inherited Env String.mk deprecation. The combined gate passes 2,312 jobs
and 1,362 terminals with the standard three axioms only. Fresh combined-root
replay passes (actual exit 0). No guest run or infrastructure rerun occurs in this
committed tranche. Reproduce with the commands above.

## H2 receiver, data completion and mixed configuration, 2026-10-18

Four projected headlines now cover the original handshake-ring receive step,
complete native data completion, clear-worker dispatch and whole mixed device
setter. Their inputs are the current snapshot-level invariants; none claims
initialized driver closure or termination. ReceiveInput and ConfigurationInput
existentially realize the exact WG snapshot with the native cut. Snapshot
injectivity proves equivalence for every actual realization, so a different
funded state or favorable execution cannot discharge the premise.

The incoming arms retain the actual allocation/account/slot cut through
lookup, session/response work and final payment. Cookie consumption derives
its held reference from the original lookup; cookie generation and replies
preserve the relevant physical fields. The native receiver covers the load
and MAC decisions, both arms and queue pop/decrement. The existing receive
observer is joined with Core on that identical execution. Its receiveIteration
uses the original condResched callback; nested scheduler/deferred worker
closure remains separate. Stops retain the existing OwnerChecks.Safe journal
contract and supply no endpoint state.

Data completion follows the original endpoint, confirmation, optional
handshake-complete/staged-send, preparation and source-validation order.
Current-slot compatibility is retained at the actual staging cut. Balanced
source lookup/payment uses the existing full-peer restoration contract.
No arbitrary peerPut preservation, successful leaf result, packet
authentication or caller-reference budget is assumed. Independent review
finds no source or invariant mismatch; scope wording now distinguishes source
validation from later GRO/stack delivery.

The full mixed setter now discharges its prior continuation premise. Actual
lookup or creation supplies the stamped caller loan and base membership.
Removal, conflict, PSK, endpoint, allowed-IP replacement/insertion, malformed
attributes, port/scalar changes, private-key updates and bulk replacement
compose in their original order. Every normal errno result retains its actual
preceding changes and cleanup. The projection/claim review finds no mismatch;
the source integration recheck is identified as an author recheck rather than
an independent authorship review.

Clear and funded-send dispatch and all five timer callbacks also retain the
actual reached account observer, including its returned journal and exact
remaining-ledger suffix. They reuse existing account machinery, with no new
scheduler or funding interpreter. Decrypt/TX, poll/NAPI, lifecycle, dump and
the concrete syscall join remain open.

[AGENT 2026-10-18] Extract the owned lookup, cookie, allowed-IP and receive-tail
source compositions once and instantiate their old interfaces. Keep source
cuts and exact physical frames separate, and share the device-field modifier
between receiver and data completion instead of copying it.

Claims are ReceiverCoreClaims, ReceiveCoreClaims, ConfigurationCoreClaims
and four Statements declarations. ReceiverCoreModel/Bridge and
ConfigurationCoreModel/Bridge connect native cuts to the projection.
IncomingCallerModel/Frames/Source separate allocation/account cuts from
endpoint/timer framing. LookupRetirementEffects/Claims and
CookieCoreModel/Frames/Claims separate lookup/held-peer transport;
CookieHeldSource contains the generic cookie composition.
ReceiverCoreFrames/Source and ReachedReceiverSource contain physical
reply/cookie frames and actual receive/account joins. ReceiveCompletionSource
is the generic owned tail composition; BorrowIndexFrames and ReceiveCoreFrames
are physical frames, while ReceiveCoreSource supplies the concrete contracts.
AllowedFrameSource, ConfigurationAllowedFrames/Source,
ConfigurationPeerModel/Source and ConfigurationEndpointFrames separate the
allowed-IP/peer update cuts. ConfigurationCreationSource, CommandSource,
PeersSource and DeviceSource complete the actual setter.
ReachedWorkersSource joins the original dispatch and callback observers.

All 4,593 prior theorem statements are kept. Fourteen modified legacy type
texts compare byte-for-byte, and their traversals are replaced with instances
rather than retained in parallel. There are 144 new theorems in 34 modules:
H2 is 1,086/129, H1 is 1,575/75; campaign 4,737/459 in 1,363 owned modules.
No frame is deleted, no mirror/shared file is changed, and no new semantic
finding or mirror-team request arises. Two trailing blank-line defects in
the prior confirmation files are corrected in this commit.

Validation: scoped builds pass 1,328, 1,340, 658, 1,404 and 1,455 jobs. Two split/statement builds fail on unnecessary
namespace openings and an incorrectly qualified Reservations type; both are
corrected. Sixty-eight capped stdin probes produce 41 passes and 27 corrected
draft failures. Final axiom audits use only the standard three; failed-draft
recovery diagnostics are never accepted as proof results. Early drafts hit
default heartbeat limits while resolving inference/automation; the corrected
proofs use the unchanged defaults. A source-splitting script assertion is
corrected before validation. No cap increase, infrastructure rerun, KILLED
outcome or guest run occurs. The inherited Env String.mk deprecation remains
the sole build warning.

The combined gate passes 2,293 jobs and all 1,354 terminal declarations.
Fresh combined-root kernel replay exits zero for this exact source tree.
H1 remains complete at its stated boundary; H2–H6 remain in progress.
The landing estimate remains 5–10 focused working days.

## H2 timer callbacks, configuration cuts and confirmation, 2026-10-18

Two projected headlines add full index preservation for original confirmation
and all five original timer callbacks. Confirmation retains arbitrary retirement
reservations through its exact existing rotation certificate; the combined
contract has no success, alias-distinctness or extra reference-budget premise.
Timer callbacks preserve current slot compatibility together with IndexCore.
Queued initiation uses the actual closed handoff; persistent and ordinary
keepalive use the completed staging contract. The zero-key callback derives its
extra reference from its own actual acquisition before either compensation or
queue insertion.

The six previous table-only callback traversals become exact-type instances
of one generic original-source family. The concrete Core instance discharges
every callback obligation. Its same-run account join retains the actual ledger
and incoming loans, using C1's existing callback account; it does not construct
an output observer history. The former callback file's 800000-heartbeat option
is removed: the replacement rules and instances check at default limits.

Configuration support follows actual selected cuts. Public-key lookup returns
its stamped loan and base selection. Private-key conflict pays the lookup loan
before selected base removal; remove-me retires the base occurrence before
paying its caller loan. Both preserve the source order and permit genuine final
deletion. The original changed-key suffix retains the account and slots through
identity replacement, per-peer precompute/expiry and staged sending. The peer
finish suffix retains them through the cached interval update, optional
keepalive, staged send and final payment. Its saved peer is reused only across
an exact WG-state frame of the intervening recorded decisions.

The complete private-key source rule still takes the original peer-command
continuation contract explicitly. Neither it nor these native cut contracts
claim the whole setter or initialized driver invariant. Remaining allowed-IP,
peer-attribute, receive and scheduler composition is separate work.

[AGENT 2026-10-18] Generalize the owned callback traversals once and retain the
old table interfaces as instances. Compose configuration at its actual selected
loan cuts using the landed account contracts and exact source factors.

Projected claims are ConfirmationIndexClaims and TimerCoreClaims, with two
Statements declarations. ConfirmationRetirementEffects contains the pure
rotation transport. CallbackRulesSource and TimerCoreSource contain the actual
callback composition, with TimerCoreModel and TimerCoreFrames separate.
ConfigurationIndexModel/Effects/Frames hold the local account/projection and
physical transport; ConfigurationLoanSource, ConfigurationStageSource,
ConfigurationUpdateSource and ConfigurationTailSource compose actual calls.
No mirror or shared-layer edits, no deleted frame, and no source/account
interpreter copy.

All 4,530 prior theorem statements are kept. The six changed callback type
texts are checked byte-for-byte. This adds 63 theorems in 14 modules:
H2 is 943/125; campaign 4,593/455 in 1,329 owned modules. Independent
configuration review finds no source/account mismatch and confirms the
remaining continuation premise is explicit. The timer source follows its
original callback branches and actual acquisition cut. No new semantic
finding or mirror-team request arises.

Validation: scoped builds pass 1,318, 1,134 and 1,421 jobs. One timer split
build fails on an overbroad namespace opening and a missing owned-frame import;
both are corrected. Twenty-four capped development probes produce nine clean
passes and fifteen corrected failures. The final 27 configuration, 37 timer
(including six replacement-interface checks), and three confirmation axiom
audits use only the standard three. One early failed timer diagnostic was
truncated; it is a capture failure, with no unchanged rerun. All new code
checks at default limits and the unchanged memory cap. No infrastructure
rerun, KILLED outcome or guest run occurs. The inherited Env.lean String.mk
deprecation is the sole build warning.

The combined gate passes 2,259 jobs and all 1,350 terminal declarations.
Fresh combined-root kernel replay exits zero for this exact source tree.
H1 remains complete at its stated boundary; H2–H6 remain in progress.
The landing estimate remains 5–10 focused working days.

## H2 staged sending, response sending and lookup payment, 2026-10-18

Four projected headlines preserve the combined index component through original
staged sending, keepalive, response sending and public-key lookup. Staging and
keepalive need only current slot compatibility alongside IndexCore. The original
closed handoff supplies peer survival, allocation stamps and nondecreasing
reference counts; the richer source frame supplies table inclusion, surviving
slot/owner cells and positive hashed keys. This excludes the recorded arbitrary
current-key/caller mismatch through the existing slot invariant, without a new
readiness or funding premise. The earlier counterexample remains unchanged.

The single owned staging traversal is enriched once. Its 17 legacy interfaces
are exact projection wrappers, and every old declaration type remains unchanged.
The complete key-release certificate replaces the old release traversal;
keepalive has one generic original-source rule. Two queue/list source helpers
and their table corollaries move from Frames into Source without changing names
or types. The arbitrary-value legacy key setter remains weaker and unchanged;
the new getter-conditioned setter carries the richer cell. No second staging
interpreter or shared-layer variant is introduced.

Response sending composes the actual timestamp, creator, MAC, session, timer
and socket sequence. Its local projected entry names slot/store bounds and
nullable caller compatibility. The reached adapter derives compatibility from
the actual charged stamped loan and returns the same native account together
with Core; it does not claim a new output observer journal. Allocation refusals
and original Stops remain. The existing sender-cell coherence argument is
extracted once, keeping its previous public theorem type unchanged.

Public-key lookup supplies its actual extra reference on success. Immediate
held-reference payment and funded account payment are separate: the former
uses the still-held nonfinal count, while the latter consumes the exact head
loan and permits final deletion under empty retirement. Neither assumes a
reference budget survives arbitrary intervening work.

[AGENT 2026-10-18] Preserve the existing staging interfaces as projections of
one richer traversal and use C1's actual closed handoff for forward survival.
Keep the native account/cut joins distinct from the projected local claims.

Claims are StagingIndexClaims, ResponseIndexClaims and LookupCoreClaims, with
four new Statements declarations. Physical support is StagingRichFrames,
ResponseIndexFrames and the retained StagedFrames. StagingRichModel/Effects,
StagingIndexModel/Effects, ResponseIndexModel/Effects and LookupCoreModel/Effects
hold projections and algebra. StagedSource, StagingIndexSource,
ResponseIndexSource and LookupCoreSource connect original operations.
No mirror or shared file changes; no frame or prior statement is deleted.

All 4,459 prior theorem statements are kept. The new tranche adds 71 theorems
and 16 modules: H2 is 880/123 and the campaign is 4,530 theorems, 453 headlines
and 1,315 owned modules. The 42 existing theorem signatures in the three
modified support modules are checked byte-for-byte, including moved helpers.
Independent review finds no source or account mismatch in response/lookup,
and checks faithful staging integration. Whole initialized driver closure
remains open. No new finding or mirror-team request arises.

Validation: scoped builds pass 1,028, 1,257 and 1,405 jobs. Two integration
builds fail on a misplaced doc comment and a missing model import, both
corrected. Thirty-three capped development probes yield eighteen passes and
fifteen corrected proof-form failures, with complete final standard-axiom
audits; one early failing diagnostic was truncated and its source corrected
before the next probe. New support uses default limits. Six retained staging
traversals keep their inherited 800000-heartbeat/4096-recursion limits, reset
before new keepalive support. No cap increase, infrastructure rerun, KILLED
outcome or guest run occurs. The sole build warning is the inherited Env.lean
String.mk deprecation.

The combined gate passes 2,245 build jobs and 1,348 terminal declarations,
with standard axioms only. Fresh combined-root replay passes with exit zero. H1 remains complete at its documented boundary; H2–H6 remain in progress.
The landing estimate remains 5–10 focused working days.

## H2 incoming consumption, expiry and outer composition, 2026-10-18

Three projected headlines retain the combined index component through both
original incoming handshake consumers and original key expiry. Consumer
lookup success supplies the extra reference used by rejection cleanup.
The handshake-only response lookup's failed owner-word stores preserve key
coverage and retirement even without owner coherence. Both new underlying
coverage/retirement contracts require neither funding, readiness, successful
authentication nor extra reference budget. The combined headlines join
existing table and owner contracts on the same actual run.

The prior owner-coherence family's two crypto traversals and public-key
lookup traversal are extracted into generic source rules. Their three legacy
theorem type texts are byte-for-byte unchanged; their bodies now instantiate
those rules. New slot/retirement contracts instantiate the same rules.
No shared source or second new crypto interpreter is added. Successful
consumption retains its acquired reference, leaving final caller payment a
separate obligation; rejection pays only that actual acquired reference.

Expiry uses the existing exact Config effect. Handshake unhashing, zeroing,
timestamp reset and validity-only key writes retain the index component.
Optional next/current aliases are allowed. Actual normal execution supplies
the peer and clock cut; missing-peer/key, NULL handshake-owner and record
Stops remain. Absent optional key slots skip. No new
expiry source traversal or ready-record condition is introduced.

The outer proof support establishes the literal initial index component and
pairs it with C1's initialized account. A syscall adapter uses the original
source-selected ledger and safe journal on the same execution. The existing
paired runner then transports this existential entry, conditional on concrete
syscall index-preservation contracts. Those contracts remain explicit.
This closes the outer composition mechanism, not initialized H2: incoming
caller tails, staged/data paths and configuration/scheduler leaf composition
still need to discharge its premise. No new observer or accounting walk is
defined.

[AGENT 2026-10-18] Generalize the owned owner-coherence source traversals and
retain their interfaces as instances. Reuse the existing paired runner and
source-selected accounts for outer composition rather than a separate ledger
or execution model.

IncomingIndexClaims and ExpiryIndexClaims hold projected claims, with three
new Statements declarations. IncomingIndexModel contains the local transport
predicates, and IncomingIndexEffects and ExpiryIndexEffects contain pure
effects. Physical frames are IncomingIndexFrames, ExpiryIndexFrames and
ReachedRunnerFrames. IncomingConsumeSource and IncomingIndexSource connect
the original consumers. ReachedInitialSource, ReachedRunnerBridge and
ReachedRunnerSource contain initialization and conditional outer composition.
No shared layer or mirror changes, and no frame is deleted.

All 4,425 prior theorem statements are kept; none is retyped or deleted.
This adds 34 theorems, including three headlines, in 13 modules. H2 is
809/119; the campaign is 4,459 theorems, 449 headlines and 1,299 owned modules.
All prior headline names and order remain. Independent review finds no
semantic mismatch in the consumer source, exact legacy interfaces, expiry
or conditional outer composition. No new finding or mirror-team request arises.

Validation: final scoped builds pass 739, 668 and 1,389 jobs. Two split builds
failed on an extraneous namespace opening and a missing owned-frame import;
both are corrected without changing claims. Twelve capped stdin probes
produce eight clean passes and four corrected proof-form/import failures.
Recovery axiom diagnostics in a failed draft are discarded; final named
support audits and terminal checks use only the standard axioms. New modules
use default heartbeat limits and the unchanged memory cap. No infrastructure
rerun, KILLED outcome or guest run occurs. The sole warning remains inherited
Env.lean String.mk deprecation.

The combined gate passes 2,229 build jobs and 1,344 terminal checks with
standard axioms only; fresh combined-root replay passes with exit zero.
The reproduction commands above apply. H1 remains complete at its stated
boundary; H2–H6 remain in progress, with the landing estimate unchanged.

## H2 session, creation and reached-account composition, 2026-10-18

Three projected headlines extend actual session and peer-creation preservation.
The session now retains retirement reservations alongside coverage and owner
coherence; its successful source guard proves the caller nondead. The new
published row therefore introduces no dead-owner obligation. Initial coherence
and the surviving handshake row identify its owner, while existing slot/store
bounds protect allocation and rotation. False returns retain Device and Stops
remain unchanged. No extra caller-live or stamped-retirement entry condition
is introduced.

Configured peer creation derives vacancy at its actual allocation cursor.
The existing footprint and geometry preserve every old hashed key's owner,
slot and allocation stamp. Normal errno results retain Device; normal
successful creation retains coverage, owner coherence and retirement.
No final-state, successful-allocation or record-readiness premise is supplied.

Complete single-peer removal now joins the original make-dead and after-dead
calls. Base coherence and funded alignment derive one exact selected
occurrence, which is transferred and paid through the real drains. The
live-resident variant derives base membership; an arbitrary already-dead
resident is not treated as a fresh base payment. The NULL branch retains its
actual recorded decision. These native support contracts retain prior
retirement obligations and loans, without callback hypotheses.

The combined index component includes table uniqueness/bounds, hashed-slot
coverage, positive owner coherence and empty retirement at ordinary driver
boundaries. Nonempty retirement lists remain local to removal. A new bridge
pairs this component with C1's actual source-selected account and separately
retained base coherence. A real present-device guard chooses the fixed-cut
domain. Its current slots and allocation fields supply the bounds at that
same cut; no runner endpoint fact is used backwards. Returning to an outer
entry or rebasing retains the exact removal suffix and remaining ledger.
Admission may choose a new ledger, so the existential domain does not freeze
the pre-admission account.

The first complete client is the original session observer: its existing
account, base relation and combined index component are proved on the same
normal execution. A Stop retains the existing safe journal, without a
manufactured final state. This is local preservation, not yet a proof that
every initialized driver path establishes the combined invariant. Incoming
handshake tails, staged/data paths and outer configuration/scheduler
composition remain the substantive H2 work.

[AGENT 2026-10-18] Carry the reached C1 account together with the index
component, deriving bounds and funding from each actual cut. Use its existing
ledger rebase instead of an independent observer or fixed admission ledger.

Claims are RetirementSessionClaims, CreationIndexClaims, ReachedIndexClaims
and the three new Statements declarations. CreationIndexModel and
ReachedIndexModel contain projected predicates; ReachedIndexBridge contains
the native account adapters. RetirementSessionEffects and CreationIndexEffects
contain pure effects. The only new physical frame file is ReachedIndexFrames.
The three new Source modules connect actual creation, single-peer removal
and the paired session observer. No shared layer or mirror is edited.

All 4,393 prior theorem statements are kept; none is retyped or deleted.
This adds 32 theorems, including three headlines, in 12 modules. H2 is
775/116; the campaign is 4,425 theorems, 446 headlines and 1,286 owned modules.
All previous headline names and order remain. Independent review found no
semantic mismatch in the source joins; no new finding or mirror-team request
arises.

Validation: scoped builds pass 1,278, 1,369, 959 and 1,374 jobs. Thirteen
capped stdin probes produce ten clean passes and three corrected proof-form
failures; all 29 added support declarations have standard axioms only.
New modules use default heartbeat limits and the unchanged memory cap.
There is no infrastructure rerun, KILLED outcome or guest run. The sole
warning remains the inherited Env.lean String.mk deprecation.

The combined gate passes 2,216 build jobs and 1,341 terminal checks with
standard axioms only; fresh combined-root replay passes with exit zero.
The reproduction commands above apply. H1 remains complete at its stated
boundary; H2–H6 remain in progress, with the landing estimate unchanged.

## H2 complete initiation sending and funded removal, 2026-10-18

Two projected headlines cover the complete original initiation sender. It
preserves supplied hashed-slot coverage and retirement reservations, and
preserves global positive hashed-owner coherence together with the selected
caller's nullable self identity and positivity. Rate-limited and no-creation
normal returns are included. No successful delivery, non-NULL caller, callback
contract or completion premise is supplied.

The existing owned H6 socket observation now also retains all three key slots,
refcount, handshake owner word, allocation stamp and deadness. The unchanged
socket traversal proves the stronger observation; C1's existing material
retention supplies the key store and device identity. H1's tag and next-slot
projections are adjusted to the richer cell. No second socket proof family is
introduced and no shared layer is edited.

The selected sender's actual funded loan derives caller positivity.
Configured identity supplies its nullable self word. These facts instantiate
the original sender contract on the same execution, so the native initiation
obligation is discharged. Actual queued and flushed sends keep their original
dequeue, pending-bit update and payment, including queue selection derived
from the funded account.

RetirementWork combines the existing account/remainder with configured/base
identity, coverage, owner coherence and explicit dead-owner reservations.
The actual removal prefix keeps the paid loan while clearing its key slots
discharges its retirement root. Both actual drains retain every still-unpaid
occurrence. The final original peer payment consumes the selected loan.
The full bulk-removal theorem derives its real saved list from the first pass,
marks those occurrences, and performs the original cleanup pass in order.
Duplicate occurrences remain count-based. No sender callback hypothesis
remains in the final native after-dead or bulk contracts.

These are normal-return preservation contracts with explicit initial funding,
identity and index invariants. They do not establish those invariants along
an initialized driver execution, guarantee completion, or derive coherence
from funding. Stops remain the original outcomes. Independent review found
no semantic or source mismatch in the sender, selected payment or bulk joins.
The previous report's descriptions of creator positivity and bounded-session
preservation are corrected for precision; their checked statements were
already correct. No new finding or mirror-team request arises.

[AGENT 2026-10-18] Strengthen the existing owned socket observation and derive
the funded sender obligation from the actual selected loan. Reuse C1's
accounting and original source factors for both removal passes.

Projected claims are SenderIndexClaims and the two new Statements declarations.
SenderIndexModel, SelectedSendRetirementModel and RetirementWorkModel hold
observations and predicates. SenderIndexEffects and SelectedSendRetirementEffects
hold pure changed-state arguments. Physical frames are SenderIndexFrames,
SelectedSendRetirementFrames, RetirementWorkFrames and RetirementWholeBulkFrames.
The remaining new Source modules connect original calls, including
InitiationIndexSource's unconditional native joins. No frame is deleted.

The stronger observation retypes 18 existing support declarations: 13 in H6
and five in H1. The other 4,318 prior theorem statements are kept; none is
deleted. This adds 57 theorems, including two headlines, in 17 modules.
H2 is 743/113; the campaign is 4,393 theorems, 443 headlines and 1,274 owned
modules. All previous headline names and order remain.

Validation: scoped builds pass 1,154, 1,164, 823, 1,169, 1,182 and 1,362 jobs.
The first final join build failed on two mistaken namespace qualifications;
correcting those names leaves the statements unchanged and the build passes.
Thirty-four development stdin probes produced 19 clean passes and 15 corrected
proof-form failures. A later clean-import join attempt failed before elaboration
because a dependency artifact was temporarily absent during the concurrent
root build. Its single authorized identical-source infrastructure retry passes
after the combined build completes; a separate audit of all 21 integrated
sender support theorems also passes with standard axioms only. The sender
prototype inherited the existing socket modules' 800,000-heartbeat setting;
the new Index modules build at the toolchain default. No limit is increased,
and no guest or KILLED outcome occurs. The sole warning remains the inherited
Env.lean String.mk deprecation.

The combined gate passes 2,204 build jobs and 1,338 terminal checks with
standard axioms only; fresh combined-root replay passes with exit zero.
The reproduction commands above apply. H1 remains complete at its stated
boundary; H2–H6 remain in progress, with the landing estimate unchanged.


## H2 creator publication and actual retirement cuts, 2026-10-18

Four projected headlines connect both original creators to nullable caller
compatibility, hashed-slot coverage and retirement; discharge a retirement
obligation after actual key clearing; and preserve supplied session
coverage/coherence using the smaller slot and resident-store bounds available at
initialized normal endpoints.

Each creator now has one generic traversal over its four actual operations:
chain writes, secret writes, its tag write, and consecutive owner dereference
and index insertion. The two previous coherent-publisher theorem statements
are byte-for-byte unchanged and instantiate those traversals. No second
creator interpreter or copied crypto traversal is introduced. The weaker
caller contract allows NULL and adds positivity only for the selected
resident, alongside the existing positive hashed-owner coherence premise. Successful publication derives non-NULL and self identity
from that actual dereference; early refusal paths need no such guarantee.
The independent coverage/retirement instances require neither positivity nor
coherence because adding a handshake row creates no keypair-row obligation.

Key clearing now discharges the selected retirement occurrence: coverage
would put every threatening hashed key in the paid owner's slots, contradicting
their actual emptiness. Equality of stamped owners supplies the necessary raw
slot equality; no additional allocation-stamp premise or distinctness of
reservation lists is assumed. This removes an index obligation, not a funded
loan: the later original peer payment still performs the accounting.

The removal adapter reuses original allowed-IP free and C1's saved entry
contract, derives the actual saved peer list from the initial base occurrences,
and applies the previously checked mark-pass transfer. Its exact factor keeps
the first pass's terminal false branch and the complete cleanup/payment pass
in the original suffix. Every normal bulk removal supplies the actual
prefix/suffix cut and transferred account at that cut. Final cleanup and
coverage/coherence there remain separate obligations.

The bounded session claim uses only CurrentSlots compatibility and resident
key bounds to derive rotation freshness and hashed allocation bounds. It
composes existing original-session contracts on the same run. It does not
identify these smaller facts with full affiliation, return endpoint bounds,
or assert retirement preservation or initialized driver closure.

Independent review finds no semantic/source mismatch in the generic creators,
their unchanged legacy interfaces, retirement discharge, bounded session step
or actual first-pass factor. The remaining substantive composition is native
initiation and selected worker payment through the removal drains. No new
finding or mirror-team request arises.

[AGENT 2026-10-18] Replace the two owned creator proof traversals with generic
actual-operation rules and instantiate both the legacy and new contracts.
Use the landed entry/account effects for the removal cut and avoid requiring
full affiliation where its slot/store fragments suffice.

Claims are CreatorCompatibleClaims, CreatorIndexClaims,
RetirementDischargeClaims, BoundedSessionClaims and the four new Statements
declarations. OwnerCoherenceCreatorClaims now contains the unchanged legacy
interfaces as short instances. CreatorCompatibleModel is data-only.
CreatorCompatibleEffects, CreatorIndexEffects and RetirementDischargeEffects
contain pure changed-state arguments. CreatorSource, CreatorIndexSource and
RetirementFirstPassSource connect original operations. The sole added physical
frame file is RetirementFirstPassFrames. No shared lemma or mirror file is
edited; no frame is deleted.

All 4,312 prior theorem statements are kept; none are retyped or deleted.
This adds 24 theorems, including four headlines, in 12 modules. H2 is 686/111;
the campaign is 4,336 theorems, 441 headlines and 1,257 owned modules. The
legacy creator statement texts and all prior headline order were checked.

Validation: scoped builds pass 962 and 1,330 jobs. Thirteen capped stdin
probes produced eight clean passes, four corrected proof-form failures and
one kernel-accepted candidate with an unused simp warning, corrected before
integration. Final inspected axioms are standard only. The gate passes 2,187 build jobs
and 1,336 terminal checks; fresh combined-root replay passes with exit zero
for this exact tree. There is no cap/heartbeat increase,
infrastructure rerun or guest run. The sole warning is inherited Env.lean
String.mk deprecation. The three reproduction commands above apply.
H1 remains complete at its stated boundary; H2–H6 remain in progress,
with the landing estimate unchanged.

## H2 clear workers and funded retirement, 2026-10-18

Three new projected headlines cover the complete queued clear worker, its
flushed wrapper, and general detached peer release. Each retains hashed-slot
coverage, owner coherence and the supplied retirement reservations on the
same normal execution. The clear worker derives its actual caller residency
and release positivity from the original run; it needs no queue readiness or
reference budget. The detached-release contract permits residual unhashed
slots and keeps its final-reference detachment premise explicit.

DeadHashedReserved records the exact stamped owner of each resident dead
hashed-key owner in an explicit retirement list. It excludes handshake rows:
a dead peer may publish a handshake, and final release unhashes its own row.
This conditional predicate alone can become vacuous after a peer disappears,
so coverage and owner coherence remain separate conjuncts.

The funded release proof counts the actual paid occurrence separately from
base or retirement occurrences. A live peer retains a funded base reference;
a dead hashed-key owner retains a separate retirement occurrence. Either
prevents the payment from deleting a still-hashed key owner. The payment join
recovers the real resident allocation from funding, applies the existing
work_payment_normal on the identical execution, and retains the remaining
DuringWork account, stable RX state and all three index predicates. The
retirement list in its entry predicate already excludes the paid head:
clearing must discharge that owner's hashed rows before its final reservation
is dropped. No reservation is invented from spare reference count.

Actual make-dead transfers newly retired hashed owners to the existing
account's detached stamped base occurrences. The saved first mark pass joins
the exact original list traversal with C1's bulk accounting theorem, retaining
order and multiplicity. The temporary AllHashedReserved predicate handles
both still-live and already-dead owners during that pass. This support covers
the saved mark loop only; the original peerRemoveAll entry, captured-list
connection, cleanup and payment composition remain to be joined. It does not
assert a normally returning run exists or supply its final state as a premise.

Independent reviews found no proof/source mismatch in clear-worker coverage,
funded release, transfer, retention, bulk composition or payment. One ambiguous
headline docstring was corrected to state the exact detachment condition. The
initialized invariant still needs transport through real source cuts. C1's
CurrentSlots compatibility and funded accounts are needed there; its
initialized endpoint bounds do not by themselves establish full
Affiliation.State.Inv or global hashed-owner coherence. No new semantic
finding or mirror-team change request arises.

[AGENT 2026-10-18] Reuse the landed accounting on the same executions and add
only reservation transport for the index relation. Keep counts and ordered
loan occurrences intact, and keep coverage/coherence separate from conditional
retirement membership.

Claims are HashSlotClearWorkerClaims, RetirementReleaseClaims,
RetirementRetentionClaims, RetirementClearWorkerClaims and the three new
Statements declarations. Physical frames are HashSlotClearWorkerFrames and
RetirementClearWorkerFrames. RetirementModel and RetirementBulkModel define
the predicates; Effects modules prove changed-store transport; Source modules
connect the original operations and landed account. No shared lemma is
edited or copied, and no frame is deleted.

All 4,272 prior theorem statements are kept, with no retyping or deletion.
This adds 40 theorems, including three headlines, in 19 modules. H2 moves
from 622/104 to 662/107; the campaign is 4,312 theorems, 437 headlines and
1,245 owned modules. All prior headline names and order remain.

Validation: six scoped builds pass (771, 667, 672, 769, 1,317 and 1,318 jobs).
One split build failed because the new frame module lacked its direct bridge
import and opened an unused unavailable namespace; correcting those imports
closed the build. Twenty-one capped stdin probes produced thirteen clean
passes and eight corrected proof-form/import failures. One failed draft's
axiom print exposed Lean error-recovery sorryAx; that draft was rejected and
the corrected final probe reports only the standard axioms.
The gate passes 2,175 jobs and 1,332 terminal checks with standard axioms only;
it was repeated after the docstring correction and passes unchanged. Fresh
combined-root replay passes with exit zero for this exact tree.
No cap or heartbeat increase, infrastructure rerun or guest run occurred.
The inherited Env.lean String.mk warning is the only build warning.
Reproduce with the three commands above. H1 remains complete at its recorded
boundary; H2–H6 remain in progress, with the landing estimate unchanged.

## H2 releases, selected drains and initialized live-peer credit, 2026-10-18

Four new headlines join key/peer release coverage with owner coherence,
expose queue-selected drain composition through the campaign projection, and
derive base-list membership plus positive reference counts for every nondead
resident at actual initialized normal endpoints.

The shared source certificate for keypairPut retains both release modes,
null selection, absent devices/keys, zero counts, nullable retained owner words
and final dereference failures. A normal retained key keeps its word and slot;
a deleted key has already been unhashed. The existing owner-coherence theorem
has exactly its prior statement and now projects this same source certificate.
Peer release preserves coverage and coherence under positive resident entry,
with empty slots required only at a last reference. Coverage discharges the
conditional detachment obligation there; actual queue/timer refusal paths
remain outside the normal postcondition.

The drain composition uses the existing exact original loop factor. It derives
membership from the actual recorded resolve or placeholder head selection
before invoking a complete flush callback. Send priority, the after-clear upTo
test, missing-record Stop and the 4096-turn exhaustion guard remain unchanged.
The new public contract ranges over Campaign2.State and keeps the two selected
callback obligations explicit. It does not establish callback funding,
termination or global coherence merely from queue membership.

The funding bridge reuses configured identity, public-key/base-list coherence
and the actual funded holder account. It recovers the resident's real epoch
and allocation stamp, then counts a base occurrence separately from all
explicit loans and RX carriers. A separately held same-owner loan gives two
credits even when other reservations alias. The initialized projection uses
the same landed RunnerAccount/HolderEntry endpoint, yielding actual base-list
membership and a positive reference for every nondead resident. No supplied
final invariant, substitute execution or dead-peer positivity claim is added.

Independent reviews found no source/statement mismatch in the release
certificate, legacy replacement, selected drain, funding bridge or initialized
projection. The reviews confirmed that a fixed Ambient value inside the
native drain predicate is harmless only because its public predicate sees the
WireGuard State, not the full Snapshot. Retired-peer reservations and their
transport across actual selected payments remain the next H2 obligation.
The existing funded account does not supply keypair reference counts or
index-word coherence by itself.

[AGENT 2026-10-18] Factor the existing owned keypair-release traversal into one
normal-outcome certificate, then reuse it for owner coherence and slot
coverage. This preserves the old theorem's statement and avoids a parallel
copy of the source case analysis. No shared-layer edit is needed.

New physical frames are SelectedDrainFrames and InitializedFundingFrames.
SelectedDrainModel and InitializedFundingModel define callback/projected
predicates. HashSlotReleaseEffects proves pure transport using existing
physical field frames. KeypairReleaseSource, SelectedDrainSource,
FundedBaseSource and InitializedFundingSource are source support.
HashSlotReleaseClaims, SelectedDrainClaims and InitializedFundingClaims expose
projected contracts. The old OwnerCoherenceKeypairReleaseClaims proof is
refactored, with no statement change. No frame is deleted.

All 4,246 prior theorem statements are kept; none are retyped or deleted.
This adds 26 theorems, including four headlines, in 12 new modules.
H2 moves from 596/100 to 622/104; the campaign is 4,272 theorems, 434 headlines
and 1,226 modules. Previous headline names/order remain.

Validation: three scoped builds pass (1,108, 1,164 and 1,299 jobs).
The combined gate passes 2,156 jobs and 1,329 terminal axiom checks using
only standard axioms. Fresh combined-root replay passes with exit zero. Nine capped
stdin probes produced seven clean passes and two corrected proof-form
failures. No cap/heartbeat increase, infrastructure rerun or guest run
occurred. The sole warning is the inherited Env.lean String.mk deprecation;
new/refactored owned modules are warning-free. Mirror/shared proof code,
gate and lake configuration remain unchanged.

All rows remain current over 783510e8. H1 is complete at its documented
boundary; H2 is in progress, then H3–H6 retain their listed whole-run
obligations. No new finding or mirror-team request arose. The campaign's
own landing estimate remains five to ten focused working days. Main and
remotes are unchanged.

## H2 hashed-slot coverage and initialized bounds, 2026-10-18

Six new headlines connect actual index/session calls to a separate hashed-slot
relation and expose initialized endpoint bounds from the landed runner account.
HashSlotCoverage requires every hashed keypair row to name a resident key whose
embedded owner is resident and has that key in one of its three actual slots.
It asserts neither uniqueness nor reference counts by itself.

Actual lookup preserves coverage together with positive hashed-owner coherence.
A returned keypair hit supplies the same final resident peer/key, an acquired
peer reference above one, a positive key reference, and actual slot membership.
Ordinary misses retain coverage; the entry coherence excludes null/zero-owner
misses. Index removal only removes rows. Actual clearing preserves coverage
and coherence with arbitrary aliases and no static reference budget, empties
the three slots, and derives LastOwnerDetached. That condition is explicitly
conditional on a last peer reference and permits the peer's own handshake
entry; it is not unconditional table emptiness or proof of a later release.

All three actual session rotations and both confirmation results preserve
coverage. Surviving hashed rows were not selected by any immediate put, so
only their unreleased slots need transport. Session publication derives the
new key's self-owner from its surviving handshake row. Existing combined
session invariants provide allocation bounds and rotation freshness; the new
headline preserves that invariant and coverage together on the same normal
call. Refusals and missing-input Stops retain their original meaning.

The actual initialized runner supplies resident peer/key cursor bounds and
slot compatibility at every normal endpoint, with exact original JSON or
indexed Stop. This uses landed HolderEntry.to_aux, allocation and CurrentSlots
facts, not a copied traversal or supplied initial invariant. Normal endpoint
bounds discharge allocation freshness; hashed bounds additionally require
explicit hashed-owner coherence. These endpoint facts are not automatically
facts at an internal session cut. Driver-wide transport of hashed coherence,
coverage and reference funding remains H2's open obligation.

Independent review checked lookup, rotation and session separately from their
authors, and checked clearing and initialized bounds separately. It found no
false theorem or source mismatch. It confirmed that clear-step coverage is
proved after both slot clearing and immediate unhashing, not asserted in the
temporary state between those operations. The existing orphan-row and slot-
alias counterexamples remain records of insufficient arbitrary-state
invariants; this tranche adds no initialized counterexample or new finding.

[AGENT 2026-10-18] Keep hashed-slot coverage separate from numeric uniqueness
and positive owner references, and reuse the landed initialized account for
allocation/slot bounds. Whole-driver closure must compose those facts at the
same actual source cuts rather than infer it from these local contracts.

New physical frame files are HashSlotLookupFrames, HashSlotClearFrames,
HashSlotRotationFrames and InitializedBoundsFrames. HashSlotModel and
InitializedBoundsModel define pure/projected predicates. Files ending Effects
prove relation transport; files ending Source recover actual source cuts.
HashSlotLookupClaims, HashSlotClearClaims, HashSlotRotationClaims,
HashSlotSessionClaims and InitializedBoundsClaims expose projected contracts.
No mirror/shared lemma or gate is changed; no frame is deleted.

All 4,192 prior theorems are retained unchanged in statement, with no retyping
or deletion. This adds 54 theorems, including six headlines, in 18 modules.
H2 moves from 542/94 to 596/100; the campaign is 4,246 theorems, 430 headlines
and 1,214 modules. All previous headline names/order remain.

Validation: four scoped builds pass, ending with the 1,133-job Index terminal
build. The combined gate passes 2,144 jobs and 1,325 terminal axiom checks,
with standard axioms only. Fresh combined-root replay passes with exit zero. Eighteen
capped stdin probes produced ten clean passes, seven corrected proof-form
failures and one corrected warning-bearing pass. No cap or heartbeat limit
was raised, no infrastructure rerun occurred, and no guest was run. Only the
inherited Env.lean String.mk deprecation remains; new files have no warnings.
The boundary audit confirms unchanged mirror/shared code, gate and lake
configuration; the proof root retains only the six existing campaign imports.

H1 remains complete at its documented observation boundary. H2 remains in
progress, followed by H3 general caller/final endpoint coverage, H4 mixed
setters/global ownership, H5 whole-worker decrease/termination, and H6 complete
scheduler coverage. There is no inherited lag over 783510e8 and no new request
to the mirror team. Estimated work to the campaign's own landing remains
five to ten focused working days; no merge to main or push is performed.

## H1 initialized driver coverage and result closure, 2026-10-18

Two projected terminal claims connect every actual syscall and the initialized
runner to the concrete tag journal. Traffic injection, floods, batches, lifecycle,
netlink/socket wrappers, dispatch and the complete syscall tail now compose.
The runner reuses the landed traversal and its actual initializer, retaining
the final WireGuard projection and exactly the original JSON or indexed Stop.
There is no supplied initial invariant, callback-preservation premise, fixture
restriction or successful-termination premise. Normal outcomes include errno
returns. Every surviving normal final tag is one of the five named handshake
states and follows the actual helper/birth effects from the empty initial map.

The dispatcher uses the landed factory. Up and down select the concrete
lifecycle observers rather than treating the old retained-arm classification as
a tag frame. Set, create and delete use their real receipt-bearing callbacks.
Silent dump, routing, descriptor, task and seccomp arms retain their original
guards and results. Traffic callbacks instantiate the concrete scheduler and
deferred workers. The runner erasure uses two existing projections to a common
empty journal and the existing paired source/JSON equations; it copies no runner
body or traversal.

H1's charter clauses now close over normal accepted executions and the
documented completed-call observations. The three Option-valued slots give one
value per slot; the proved source relations retain every role-dependent rotation
and ordered release, including aliases. Clearing empties the three slots in
source order. Expiry retains the published slots and changes the specified
validity/tag fields. Session evaluation is finite for every input mode and
retains refusals and exact Stops; successful completion is proved under explicit
readiness where claimed. Initialized successful completed confirmations are
unique by persistent allocation internalId. The accepted raw store-key
recreation counterexample remains the record of the statement correction.

Independent review found no false H1 headline or source mismatch. It checked
the lifecycle/outer guard order and effects separately from the runner author,
and reviewed the complete charter scope. Two limits remain explicit:
DriverTagMapCoverage is coverage at helper/caller cuts and the normal endpoint,
not a trace of every internal write; completion-only adapters omit internal
receipts when their enclosing callback Stops. Likewise, confirmation uniqueness
covers completed consume observations; a confirmation followed by a Stop inside
that same consume has no shared consumed receipt. Such Stops expose no final
mirror state. These are observation boundaries, not counterexamples to the
proved statements. No universal successful-return or eventual-confirmation
claim is made. A stronger journal of all internal completed cuts before Stop
would be a separate observer extension. The final-tag occurrence corollary
does not identify a unique producing receipt or preserve allocation identity
across raw peer slots; the ordered effect relation remains a separate conjunct.

[AGENT 2026-10-18] Retain this explicit normal-execution/completed-call boundary
for H1's completed result. Do not describe endpoint coverage as an internal
write trace, or completed-consume uniqueness as completeness at every stopped
inner cut. This follows the mirror's existing result semantics and the
independent scope review, without changing any theorem to hide a discrepancy.

New physical frames are DriverTagTrafficFrames, DriverTagEnvironmentFrames,
DriverTagOuterFrames and DriverTagRunnerFrames. DriverTagStateModel and
DriverTagRunnerModel are pure relation/observation models.
DriverTagRunnerClaims and DriverTagInitializedClaims expose projected claims;
the remaining new files compose actual sources. Existing shared layers and the
mirror remain unchanged. The only additional lifecycle factor is the original
short down wrapper, allowing its actual stop receipts to remain visible.
No new mirror-team request arises.

All 4,084 prior theorems are kept; none are retyped or deleted. This adds
108 theorems in 15 modules, including two headlines. H1 is 1,574/75; campaign
totals are 4,192 theorems, 424 headlines and 1,196 modules. All original
headline names and order remain.

Validation: four root scoped builds pass; final Noise.Statements uses 1,237
jobs. The combined gate passes 2,126 jobs and 1,319 terminal axiom checks,
with only the three standard axioms. Fresh combined-root replay passes.
Forty capped stdin draft checks comprise thirteen clean passes and twenty-seven
corrected proof-form failures, including stock-heartbeat failures fixed by
smaller source cuts, aligned erasure tactics and existing runner projections.
No resource limit was increased. Independent final review found one
arbitrary-entry comment omission, corrected before replay without changing
proof terms. No unchanged infrastructure rerun, KILLED job, guest timeout,
guest run or cap increase occurred. The inherited Env:865 deprecation remains;
no owned warning remains. The commit-time whitespace check reported two
extra terminal blank lines in the new outer-wrapper files; the next commit
removes them without changing declarations or proof terms.

H1 is complete at the boundary above; H2–H6 remain current and in progress with
their whole-run scopes in the current table. Continue with H2 reachable
store/slot/owner coherence. The campaign landing estimate remains 5–10 focused
working days, dominated by those remaining invariants and global progress.

## H1 complete scheduler and deferred tag coverage, 2026-10-18

Five further projected claims cover actual data completion, native transmit,
all seven dump calls, the complete scheduler and every deferred-call constructor.
Normal surviving tags trace to the entry state or actual helper/birth receipts.
The exact original projected outcome is paired with each claim. Every worker,
NAPI, Stack, timer, send/clear and guard callback obligation is discharged.
No readiness, residency, successful-run or invariant premise is supplied.
Original negative errno results count as normal outcomes; Stops expose valid
emitted receipts, with the previously stated completion-only helper limitations.

The native receive confirmation proof projects tag equality from the actual
rotation, including aliases. Lookup/repayment projects the landed full-peer
restoration. Receive and transmit suffixes retain tags through actual timer,
queue, counter and staging updates; peer release may delete its location.
Timer callbacks enqueue work rather than invoking handshake owners inline.
Recorded/placeholder dispatch retains all selection, detach, section, step and
termination guards. The actual named/head send and clear dispatches expose their
native flush observers.

Poll and GRO use the existing source/observer compositions with the actual
inner-packet delivery callback. Its Stack transport reuses the previously proved
owned source and erasure, instantiating the three landed Stack preservation
rules with the new tag predicate. The complete scheduler uses landed factories,
including copied consistency probes; those probes add no committed tag receipt.
Dumps specialize the existing seven-case invariant contract, with exact peer
acquisition/release and socket projection, without copying serializer traversal.

[AGENT 2026-10-18] Expose four owned deferred callback hooks: send, clear,
recorded timer dispatch and placeholder timer traversal. The shared old-atom
interface embeds those executions atomically, which would hide real helper
receipts. Exact specialization equations recover its four original factors.
The other crypt/after-transmit/idle/after-advance bodies and the entire scheduler
reuse landed definitions. Quiet atom contracts exclude the effectful hooks;
all are instantiated individually through actual erasure and tag/store frames.
This is new observation composition, not repair or duplication of a shared
holder, reference, serializer or framing layer. Structural counterparts are
explicit: four deferred source bodies, two timer traversals, and three narrow
lookup/trim/splice tag projections; all existing shared declarations stay intact.

Independent review checked the native timer/data/send/receive/keypair paths,
aliased confirmation, saved reads, release/deletion, actual dispatch selection,
product projection and concrete scheduler/deferred wiring. It found no semantic
or source-exactness defect. Three comment overstatements were corrected after replay before commit: origins include entry tags as well as receipts, and
different deferred constructors use different paths through the callback family.
The theorem/proof terms are unchanged by these wording corrections.

New physical files are DriverTagSilentFrames, DriverTagConsumeFrames,
DriverTagTransmitFrames, DriverTagTimerProductFrames, DriverTagPollFrames and
DriverTagDumpFrames. DriverTagProductClaims and the five Statements wrappers
are projected claims. The thirteen remaining new files contain source/observer composition. All
claims use the WireGuard projection; frames remain separate.
All 3,883 prior theorems are kept, none retyped or deleted. This adds 201 in
20 modules including five headlines. H1 is 1,466/73; campaign totals are
4,084 theorems, 422 headlines and 1,181 modules.

Validation: Noise.Statements passes 1,220 jobs; combined gate passes 2,111 jobs
and 1,317 terminal axiom checks with only the three standard axioms. Fresh root
replay passes. Root integration used twelve scoped builds: eleven passes
and one corrected file-split error (a stray comment fragment). Forty-two capped
stdin draft checks comprise twenty-one clean passes, two passes with corrected
unused-parameter/simp warnings, and nineteen corrected proof-form failures.
Stock-heartbeat failures were fixed by grouped read/write cuts and guarded
source selection, without raising limits. No unchanged infrastructure retry,
KILLED job, guest timeout, guest run or cap increase occurred. The sole inherited
Env:865 deprecation remains; no owned warning remains. All heavy jobs use capped
with its unchanged memory cap, 32 Lean threads and 16 guest slots.

All six rows remain current over 783510e8 and in progress. H1 next needs traffic,
lifecycle, and enclosing syscall/runner tag composition. H2–H6 retain their
whole-run scopes in the current table. The landing estimate remains 5–10 focused
working days; no mirror-team request arises.

## H1 actual configuration and removal tag coverage, 2026-10-18

Five projected claims now connect actual peer removal, bulk removal, device
destruction, peer configuration and mixed device configuration to their real
helper/birth receipts and exact original outcomes. All callback obligations are
discharged. Private-key expiry is observed explicitly, births retain their exact
allocation transition, and both configuration removal routes execute the actual
receipt-bearing drains. Field updates, cache resets, port changes and allowed-IP
operations retain surviving tags without a supplied residency or readiness
premise. Unsupported endpoint families take the original no-write path.

Normal returned tags trace to entry tags or the actual journal; every emitted receipt has
an original-call witness, also before an outer Stop. Expiry publishes only after
the complete expiry helper returns; a later Stop inside that helper emits no
receipt for an earlier inner clear. Negative errno is a normal outcome and keeps
its preceding receipts. Completion-only worker
adapters still publish their bundle only when that worker returns. This tranche
does not claim completeness for transient writes inside an unfinished worker,
allocation identity continuity of the raw peer store, or whole-driver ownership.
The previously accepted raw-ID counterexample remains unchanged.

[AGENT 2026-10-18] Reuse the seven landed configuration callback factors and
four removal/destruction factors. Add one narrowly factored after-dead body to
expose both real flushes, preserving guards, accounting, release and errors.
For future scheduler atoms, the product adapter executes an old observation with
a private journal and discards that journal only under an actual-call erasure
and tag frame. Effectful callbacks use explicit tag observers instead.

Two independent reviews found no incorrect removal/configuration/endpoint theorem, hidden readiness
premise or source mismatch. It checked both nested drains, the two-pass saved
peer list, the actual destruction suffix and unrestricted endpoint/port paths.
The destruction suffix has no helper writer; its absence theorem is reused,
not a replacement for observing the earlier removal. Structural overlap remains:
the seven configuration frame compositions traverse five original function
families plus a read and grouped write, with counterparts in owned pending
frames. The paired peer read/update and keepalive cuts also parallel owned
pending support. The configuration review also checked all concrete callback obligations and the
paired keepalive read/write proof. No shared holder, material, serialization or
source layer is copied or changed.

Claims are the five new Statements wrappers using DriverTagClaims. New physical
files are DriverTagConfigurationFrames, DriverTagPeerConfigurationFrames,
DriverTagRemovalFrames and DriverTagProductFrames. DriverTagConfigurationSource,
DriverTagRemovalSource and DriverTagProductSource hold concrete observers and
composition. All 3,815 earlier theorems are kept, with none retyped or deleted.
The seven modules add 68 theorems including five headlines: H1 is 1,265/68,
and campaign totals are 3,883 theorems, 417 headlines and 1,161 modules.

Validation: Noise.Statements passes 1,200 jobs. The combined gate passes 2,091
jobs and 1,312 terminal checks with only the three standard axioms. Fresh root
replay passes. Root integration used seven scoped builds: five passes and
two corrected failures (one stock-heartbeat endpoint composition and one product
projection/syntax error). Grouping the endpoint write fixed the heartbeat
failure without raising limits. The contributing drafts used sixteen capped
stdin probes: eight clean passes and eight corrected failures. This includes two
root leaf probes before the unrestricted endpoint generalization, four removal
probes, and ten configuration probes including the standard-axiom inspection.
No unchanged infrastructure retry, KILLED job, guest timeout, memory-cap increase
or guest run occurred. The mirror's existing Env:865 deprecation remains with its
owner; there is no owned warning. All heavy jobs retain capped's memory cap,
32 Lean threads and 16 guest slots. Mirror/shared boundaries remain unchanged.

All six rows remain current over 783510e8 and in progress. H1 next needs actual
scheduler/deferred, poll and surrounding syscall/runner composition. H2 needs
reachable store/slot/owner coherence; H3 general callers and final endpoints;
H4 general mixed setters and ownership; H5 whole-worker/global progress; H6
complete caller/scheduler and session-relative counts. The campaign landing
estimate remains 5–10 focused working days. No new mirror-team request arises.

## H1 actual birth, work-drain and stop/down tag coverage, 2026-10-18

Five new projected statements connect actual peer creation, the complete bounded
work drain, timer stop, device stop and device down to their original outcomes.
Their observers retain ordered helper/birth receipts. On normal return the
receipts cover every surviving final tag; on Stop the claim is validity of the
receipts actually emitted, with no final-state assertion. Every callback and
physical frame is discharged. The source still uses the saved peer list, the
4096-turn bound, send-before-clear selection, recorded/placeholder branches,
selected-clear early return and original queue/section failures. Timer stop may
run work for other peers. No readiness, coherence or success premise is added.

[AGENT 2026-10-18] Extend the existing tag receipt language with an explicit
peer-creation receipt and preserve the old helper coverage as an exact embedding.
The birth effect records the real allocation counter and pointwise stamps plus
ZEROED initialization, including arbitrary-state cursor overwrite. Raw tag-gap
retention is deliberately not an allocation-identity invariant. The initialized
confirmation uniqueness theorem and its accepted raw-key counterexample remain
unchanged.

The helper adapter runs the existing reception observer once from an empty
local journal, then appends its actual suffix to the incoming mixed journal.
It does not substitute a filtered prior journal for the old coverage invariant.
Initiation, its worker and the receive-step completion adapter publish their
returned receipt bundles only after the enclosing callback returns normally.
The clear worker instead captures handshakeClear before key/reference release.
A later section-stop failure retains already published receipts.

Independent review points and dispositions:

- Endpoint tag coverage alone cannot establish occurrence completeness: a
  transition followed by deletion or a cancelling cycle can fit inside an empty
  gap. The actual drain/stop sources therefore expose the nested callbacks;
  removal and destruction will do the same. No broad silent frame is used for
  those paths. H1 remains open pending their whole-driver composition.
- Validity on Stop does not mean every previously completed helper is retained.
  The completion-only sender/receive-step limitation is explicit above and in
  source documentation. No stopped-write coverage is claimed.
- Per-receipt validity supplies an existential native witness. Actual execution
  and order come from the concrete captures and exact source equations. Each
  new headline includes original-outcome agreement alongside inspection facts.
- Birth coverage permits occupied-slot replacement and does not imply lifetime
  continuity or freshness. Its exact counter transition is separate from the
  initialized allocation-stamp theorem.
- The source inventory identifies handshakeZero, four creator/consumer stores,
  and default-Peer insertion as tag writers. Zeroing occurs through clearing or
  session installation; initialization does not add an unclassified zeroing
  helper. Seven helper families plus birth cover these writer families. Private
  key expiry, removal/destruction, scheduler and full-run composition remain.

The two independent reviews found no false theorem, source-order mismatch or
hidden readiness premise. The cited queued-removal corpus shapes were inspected
only; no guest run or new runtime counterexample is claimed.

Claims are DriverTagClaims and five Statements wrappers; DriverTagModel contains
the projected data model. Physical files are DriverTagFrames, DriverTagLeafFrames,
DriverTagAllowedFrames, DriverTagControlFrames and DriverTagFlushFrames. Adapter,
Caller, Control, ControlComplete, Flush, FlushCaller and DriverTag Source files
contain exact sources and compositions. Allowed-IP frames project the landed
list/node contracts and existing owned insertion factors, preparing configuration
closure without duplicating a trie algorithm. No shared lemma or mirror changes.
All 3,684 previous theorems are kept; none is retyped or deleted. This adds 131
in 14 modules, including five headlines: H1 is 1,197/63; campaign totals are
3,815 theorems, 412 headlines and 1,154 modules. Original headline names/order stay.

Validation: Noise.Statements passes 1,193 jobs; combined gate passes 2,084 jobs
and 1,307 terminal checks with standard axioms only. Fresh combined-root replay
passes. Heavy commands retain capped's memory limit, 32 Lean threads and
16 guest slots. The four contributing draft tranches used 32 capped stdin
probes: ten clean passes, one pass with a corrected linter warning, and 21
corrected failures, including standard-heartbeat failures resolved by smaller
source cuts. Root scoped integration used thirteen builds: eight passes and
five corrected failures (one missing split import, two projection/field proof
failures, one claim-proof syntax error and one allowed-IP projection failure).
An earlier identifier-inspection stdin probe also failed on guessed names.
There were no unchanged infrastructure retries, KILLED jobs, timeouts or cap
increases. The mirror's existing Env:865 deprecation is unchanged; no owned
warning remains.

All six results remain in progress. H1 now needs configuration, removal and the
scheduler/syscall/runner tag composition. H2–H6 retain the scopes in the current
table. The landing estimate remains 5–10 focused working days. No new request to
the mirror team is needed.

## H1 initialized allocation-stamp confirmation uniqueness, 2026-10-18

The original initialized runner now yields an actual successful-confirmation
internalId list with no duplicates. This has no supplied invariant, callback,
accepted-run or successful-termination premise. It includes device recreation,
both placeholder modes, and completed consume receipts before a later outer
Stop. The accepted raw store-key recreation counterexample remains unchanged.
A confirmation whose own enclosing consume stops before publishing its receipt
is outside this journal; no returned-state invariant on Stop is asserted.

The new pending invariant is transported through complete configuration,
all original encrypt/decrypt/transmit iterations, every timer callback and
recorded/placeholder dispatch, scheduler/deferred runs, traffic wrappers,
full/stepped dump, lifecycle notifications, every syscall arm and its actual
return-to-user continuations. The actual fixture supplies the initial invariant.
The landed literal RunnerInvariant composition then proves chronological
confirmation-label distinctness, and the previously checked ordered extractor
identifies those labels with actual allocation internalIds.

This closes the allocation-lifetime confirmation obligation. H1 remains in
progress: the invariant contains configured identity, current slots and pending
allocation history, not handshake-tag ownership. The final coverage review
identified the remaining whole-driver tag composition through stop/down,
private-key expiry, removal and their enclosing syscall paths. Existing normal
sender/receiver/clear-worker tag receipts and the seven native owner helpers
remain proved. H2–H6 retain their previously stated whole-run gaps.

[AGENT 2026-10-18] Add one predicate-parametric dump composition in the owned
Config result, using the landed whole serialization-walk frame, reference
replacement and socket-tail factors. Its mutable-leaf obligations are concrete
peer acquisition, release and socket-mask stability. Existing interfaces are
unchanged. Three named local OwnerControlCalls wrapper variants preserve the
new pending invariant through original socket/netlink/rtnetlink sources.

Review disposition: the generic dump composition has structural counterparts
to five DumpSockets families: done, replacement, finish, tail and callback.
This overlap is real; genericity does not erase it. The new property cannot be
projected from the shared holder frame, which omits pending slots. The addition
is a new predicate-parametric source contract using existing factors, not an
inherited index-frame repair or a copied holder/material/serializer layer.
The earlier index-repair exception therefore supplies no approval claim here;
existing shared declarations remain untouched. This rationale and the five
counterparts disposition the review point explicitly. Independent semantic
reviews found no source mismatch, hidden success/readiness premise or failure
in initialization/history composition. The separate tag-coverage gap is retained.

Claims are ConfirmationUniqueClaims and its Statements wrapper; PendingRunnerSource
supplies actual initialization. New physical files are PendingConfigurationFrames,
PendingAllowedInsertionFrames, PendingPeerConfigurationFrames,
PendingDeviceConfigurationFrames, PendingCryptFrames, PendingTransmitFrames,
PendingTimerFrames, PendingSchedulerFrames, PendingTrafficFrames,
PendingEnvironmentFrames, PendingDumpFrames, PendingOuterFrames and
PendingSyscallFrames, plus Config/DumpInvariantFrames. Corresponding Source files
hold actual compositions; PendingSchedulerCompleteSource supplies concrete
worker/timer obligations. No frame is deleted and no baseline theorem is retyped:
3,496 existing theorems are kept and 188 added in 29 new modules, including one
headline. H1 is 1,066/58, H4 is 1,006/116; total 3,684 theorems, 407 headlines,
1,140 modules. All 258 original headline names/order survive.

Validation: Noise.Statements passes 1,179 jobs. The full combined gate passes
2,070 jobs / 1,302 terminal checks with standard axioms only. Fresh combined-root
replay passes. Every heavy command uses capped with the unchanged memory
cap, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. No guest runs occur.
Draft elaboration/source-association/import/namespace failures were corrected
before new checks. One earlier configuration probe needed its single unchanged
infrastructure retry after a missing dependency artifact became available;
that retry exposed proof errors subsequently corrected. Integration corrected
two file-split errors (a stray closing comment and a dropped abbreviation line)
before rebuilding, and changed two proposition-valued definitions to theorems
to fix warnings. All three dump probes used an explicit 800,000-heartbeat
setting; integration removed it and the modules pass at normal project limits.
The unchanged Env:865 String.mk warning remains with the mirror owner; no owned
warning remains. No KILLED job, guest timeout or memory-cap increase occurred.

No new mirror-team request arises. The campaign landing estimate remains
5–10 focused working days, with uncertainty concentrated in whole-driver tag,
index/owner coherence and global scheduler progress.

## H1 pending invariant through callers and polling, 2026-10-18

The allocation-stamp statement now reaches the end of each actual consume,
including normal drops, instead of stopping at its inner confirmation cut.
The initialized completed-transition headline obtains the resident internalId
from that same actual receipt. The second new headline equates the successful
ordered extractor with the actual journal's confirmation labels, preserving
order and multiplicity. Neither assumes that the successful IDs are distinct.
The accepted raw-store-ID counterexample remains unchanged.

PendingSession combines configured identity, current-slot compatibility and
the allocation-stamped pending-ticket invariant. The actual initial fixture
establishes it with an empty confirmation journal. Session installation and
the complete normal response sender, reception and receive step preserve it;
their actual focused observers add no confirmation labels, including on Stop.
The complete consume observer records its optional entry stamp only after
that consume returns normally. A true inner confirmation followed by a Stop
inside the enclosing consume still has no completed receipt and is outside
this journal's labels. Stopped-prefix safety concerns committed labels only;
no final state invariant on Stop is asserted.

The actual poll, GRO and three NAPI callers now preserve this invariant and
history safety with no replacement callback premise. Poll's seed contains
only lifetime events, so its bridge carries all earlier confirmation labels
explicitly and promotes only the newly appended local suffix. Original
inner-packet delivery is discharged through actual wgXmit, owned staged-send
and release effects, and campaign 1's generic StackSource composition.
Malformed arbitrary replay-counter bitmap shape is allowed by the local
counter frame; initialized provenance remains an independent source fact.

Creation keeps the persistent counter and begins with empty pending slots.
Completed destruction/default native deletion has no device; monotone
allocation frontier suffices for prior confirmed stamps. Original open/up,
stop/down, optional and bulk peer removal, send/clear flushes, timer stop and
actual named/head send/clear dispatch now preserve the supplied invariant.
The original bounded drain retains its selection order and early clear-work
return. The actual peer read and pending-flag write stay in one source cut;
an arbitrary replacement peer is not assumed to preserve the pending slot.
Default native deletion does not yet cover product-world notifier callbacks.
Scheduler, all timer callbacks, general configuration and full initialized
runner composition remain open. No initialized global Nodup claim is made.

[AGENT 2026-10-18] Retain the minimal configured/slot/pending invariant and
use three named configured-only variants for initiation consumption,
response consumption and cookie consumption. Their stronger campaign-1
contracts additionally require session history not needed here. Reuse the
landed lookup/update/release lemmas; do not copy their layer. Two bounded
pending trim/splice variants accompany the existing transmit factors.
The existing owned socket view now carries optional (tag,next) cells; old
tag, queue and timer interfaces still project their previous observations.
A separate shared key snapshot supplies allocation stamps and the frontier.
Owned Index flush/removal source proofs are generalized once over a predicate;
all old table contracts remain instances, with no source-layer duplication.

Claims are in PendingTicketConsumeClaims and ConfirmationTicketClaims;
ConfirmationOrderLabels supplies the exact ordered-list bridge. Physical
frames are PendingInvariantFrames, PendingSocketFrames, PendingConsumeCoreFrames,
PendingTicketConsumeFrames, PendingTicketHandshakeFrames, PendingTicketWorkerFrames,
PendingTicketDeviceFrames, PendingTicketFlushFrames, PendingTicketAllowedIpFrames,
PendingTicketRemovalFrames, PendingTicketControlFrames, PendingReceptionFrames,
PendingPollFrames and PendingStackFrames. Source/observer composition is in
PendingSessionSource, PendingTicketConsumeSource, PendingConsumeHistorySource,
PendingObserverSource, PendingReceptionSource, PendingControlSource,
PendingMaintenanceSource, PendingDispatchSource, PendingPollSource,
PendingPollCompleteSource and PendingStackSource. The two new owned Index
source files are PeerRemovalSource and BulkRemovalSource; FlushSource is
generalized in place. No shared proof or mirror file changed. No frame was
deleted; all old headlines remain.

This checkpoint adds 250 theorems, two headlines and 29 modules: H1 is
890/57, H2 542/94, and the campaign is 3,496 theorems, 406 headlines and
1,111 modules. Independent reviews found no semantic defect in the stronger
socket projection, complete consume transport, prior-label poll composition
or lifecycle/removal joins. A misplaced capture docstring was corrected.
The broader initialized status of H1 and the remaining H2–H6 scopes stays
explicit in the register; the landing estimate remains 5–10 focused days.

Validation: the assembled Noise.Statements build passes 1,140 jobs. The
first full extension gate passed 2,040 build jobs / 1,301 terminal checks;
after adding original send/clear dispatch and correcting the capture comment,
the final gate passes 2,041 jobs / 1,301 terminal checks, standard axioms only.
Fresh combined-root replay passes. The unchanged mirror String.mk
warning remains with its owner; there are no owned warnings or new axioms.
Draft failures involving missing imports, explicit projection/Hoare typing,
macro scope, source-cut comments and stock heartbeat elaboration were fixed;
limits were unchanged. One consume-history probe encountered a temporarily
missing socket artifact during rebuilding; its sole unchanged infrastructure
retry passed after the artifact was available. Two root dependent builds
accidentally repeated a failed dependency unchanged (control-frame namespace
resolution and a split Stack docstring); these were process errors, not
infrastructure retries or passes. Subsequent builds were run after the
specific corrections, and final validation passes. No KILLED job, guest
timeout, memory-cap change or guest run occurred.

No new mirror-team request arises from this tranche.

## H1 sender/receiver coverage and initialized allocation receipts, 2026-10-18

Normal initiation, initiation-worker, reception and receive-step claims now
connect entry tags to the final tags through actual valid helper receipts.
The receipt relation permits deletion at release sites; it does not invent
an unchanged peer where the original code removes one. Actual rate/load/MAC
classification remains in the conclusions. Response final tags were already
closed. Existing erasure preserves all original outcomes, including Stops.
This closes normal handshake sender/receiver caller coverage, not every
driver edge: device stop, configuration and lifecycle composition remain.
The whole-session finite evaluator remains exact for every logical outcome;
successful return still requires its named readiness or refusal domain.

CounterConsume derives a resident key allocation stamp from the original
counter-to-consume handoff for every completed initialized consume event.
No key-residency or accepted-trace premise is supplied. ConfirmationOrder
extracts every such event in absolute journal order, carrying its occurrence,
skb identity, packet stamp, original nested confirmation cut and internalId.
The false-return cases remain in the observations; the successful list selects
the actual true returns. Soundness and completeness match the same original
receipt and deterministic cut. A later outer Stop preserves completed events;
a true inner confirmation followed by a Stop inside that consume has no
completed consume receipt and is outside this list's scope.

PendingTicketCallClaims connects actual sessions and confirmations to the
existing pending-ticket automaton. The optional local label also handles
malformed arbitrary states with a missing key: they carry no allocation
ticket. Initialized occurrence completeness proves that this case loses no
completed true confirmation in an initialized history. ConfirmationTicketClaims
records the actual stamped transition. These are cut and transition contracts;
they do not yet establish the initialized history invariant or Nodup.

The existing owned Index staging proofs now carry table preservation,
surviving peer tag/next cells and exact global keypairCounter in one source
composition. All old table interfaces remain. Independent C1 ordinary
keypair transitions at the same counter supply key-stamp retention; arbitrary
setKeypair is never treated as identity preservation. This closes keepalive,
staged sending and queued-initiation pending retention without copying a
shared layer. PendingTicketRetentionFrames covers creation and releases;
PendingTicketClearFrames covers actual ordered clearing and its whole worker.
PendingTicketTimerFrames projects the owned H6 exact arm/delete effects;
its whole hooks require no initial peer-residency premise. The old missing-tag
timer proof now delegates to its extracted normal-run impossibility fact.

Claims are in InitiationCoverageClaims, ReceptionCoverageClaims,
ReceiveStepCoverageClaims, PendingTicketCallClaims, PendingTicketOptionalClaims,
CounterConsumeClaims, ConfirmationTicketClaims and ConfirmationOrderClaims.
Their physical frames are in the corresponding CoverageFrames files,
ReceptionTagFrames, CounterConsumeFrames, PendingTicketCallFrames,
PendingTicketEndpointFrames, PendingTicketRetentionFrames,
PendingTicketStagingFrames, PendingTicketClearFrames and PendingTicketTimerFrames.
TagCoverageModel and ConfirmationOrderModel contain relations/projected data;
the Source files contain original-call factors, extraction and composition.
Index/StagedObservation and StagedFrames hold the stronger owned frame;
StagedSource composes it. No existing shared declaration changed or was copied.

This checkpoint adds 229 theorems, six headlines and 28 modules: H1 is
649/55, H2 533/94; the campaign is 3,246 theorems, 404 headlines and
1,082 modules. All prior statements remain, and no frame was deleted.
Independent reviews found no semantic defect in strengthened staging,
receiver coverage, optional labels or clear/timer transport. The ordered
extractor additionally received an independent matching/order review.
The review's wording correction distinguishes tag effects from separately
proved receipt validity.

Validation: scoped sender/receiver build passes 1,011 jobs. The first
combined extension gate passed 2,005 jobs / 1,297 terminal checks and fresh
root replay. The expanded checkpoint gate passes 2,012 jobs / 1,299 terminal checks;
fresh combined-root replay also passes.
The unchanged mirror String.mk deprecation remains with its owning lane.
Development errors were corrected: field-projection carry, missing explicit
normalization, one duplicated integration declaration, and redundant tactic
tails in four owned proof sites after stronger imports. Timer and initiation
draft heartbeat failures were resolved with explicit action types, without
raising limits. One failed gate was accidentally repeated unchanged because
a text replacement matched nothing; that repeat was a process error, not an
infrastructure rerun or a pass. The subsequent edit asserts its match.
No KILLED job, guest timeout or memory-cap change occurred; no guest ran.

No mirror-team request arises. Reusing exact helper effects and the landed
source observers is sufficient; proof-history restructuring in the mirror
would not preserve its operational altitude and is not requested.

## H1 response completion and allocation-stamp foundation, 2026-10-18

The normal original response sender now links entry tags, actual creation
and session receipts, and final tags. Its headline retains receipt shape,
roles, validity and local effects. Concrete timer contracts and the owned
socket view discharge every intervening frame; no abstract frame premise
remains. Existing erasure still preserves every original Stop.

ResponseCallerFinalClaims contains the projected claim.
ResponseSuffixTagFrames and ResponseCallerFinalFrames contain the physical
timer and observer frames. UncachedSocketTagFrames and CookieReplyTagFrames
cover both uncached reply families, endpoint decoding, cookie creation,
validation and the complete cookie reply send. These reuse the landed cookie
projection and owned tunnel-send observation; they do not copy a cache layer.

PendingTicketClaims reuses campaign 1's Lifetimes.Store. Its pure invariant
tracks bounded, unique pending allocation stamps and a distinct confirmation
history disjoint from pending stamps. Fresh allocation advances the global
frontier; confirmation removes its pending stamp; removal and recreation may
only retain or remove existing stamps. Its prefix theorem is conditional on
the transition relation, not yet an initialized driver theorem.
PendingTicketFrames connects the actual initial state and allocation update.
The existing slot bound prevents a fresh numeric store insertion from
reviving a dangling next-slot reference.

ConsumeConfirmationModel holds projected observations and their effects;
ConsumeConfirmationSource connects endpoint setting, the actual confirmation
call and its original suffix to a completed consume receipt.
ConsumeConfirmationClaims connects initialized committed receive events to
those observations, and identifies the internalId and exact next-to-current
effect whenever the occurrence is stamped. CounterStampFrames proves that
every normal original counter check has the same resident stamp before and
after, and projects endpoint preservation from the landed keypair snapshot.
The journal's counter-to-consume residency handoff and ordered all-actor
pending history remain open; an inner confirmation before a stopped consume
is not silently counted as a committed consume event.

The extension adds 44 theorems, one headline and eleven modules: H1 now has
453 theorems and 49 headlines; the campaign has 3,017 theorems, 398 headlines
and 1,054 modules. The full gate passes 1,984 build jobs and 1,293 terminal
checks. Fresh combined-root replay passes. The sole compiler warning is
the unchanged mirror String.mk deprecation. Development elaboration failures
were corrected, including one unsupported tactic and one projection/case
split; no infrastructure rerun, KILLED job, timeout or resource-limit change
occurred. No mirror or existing shared-layer file changed.

No mirror-team request or mirror change is needed for this tranche.
Source-selected cut equations for the receive counter/confirmation handoff
belong in the proof tree. Restructuring the mirror around proof history
would not preserve its operational altitude and is not requested.

## Main carry and allocation-identity resumption, 2026-10-18

[USER 2026-10-18] Resume H1 with successful confirmation uniqueness over the
global keypair allocation identity, carried as internalId, while preserving
the raw store-ID counterexample as the explanation for the corrected scope.
Continue the existing charter order. Campaign 3 reads this campaign's files
without modifying them.

Main 783510e8 adds the campaign-3 charter and documentation. Its campaign-1
GRO proof changes were already present here at 8ba82097. The documentation
index conflict was resolved by retaining both campaigns' entries; no Lean
source, mirror definition, target or gate changed in this merge. The prior
1,973-job gate, 1,292 terminal checks and fresh root replay therefore apply
to exactly the same proof source. Every campaign-2 register row is current
over 783510e8. No build rerun is needed for this documentation-only carry.

## H1 initialized recreation finding, 2026-10-18

The proposed whole-run raw-KeypairId confirmation-distinctness statement
fails across device recreation. The original initialized Runner accepts two
copies of d2_respond_then_data separated by successful deletion/creation.
The actual committed promotion receipts have (device, slot, allocation stamp)
(3, 0, 1) and (4, 0, 2). Both move next to current once for their own
allocation. This is a statement artefact, not a mirror/kernel finding;
the charter's per-allocation uniqueness remains open.

[The finding and reproduction](2026-10-18-proof-campaign-2-confirmation-incarnations.md)
record the exact accepted recipe, source explanation, independent review
and evidence boundary. ReplayConfirmationIncarnations is a fail-noisy
runtime module, not a theorem or a finite kernel execution certificate.
It uses the existing observer and separately checks original-runner output
agreement. Placeholder mode is explicit; no Linux replay was performed.
The independent standalone reproduction and the final full proof gate passed.
Fresh combined-root replay passes for the theorem tree. The runtime module is
checked separately by the standalone command and adds no gate build job.
Eight exploratory stdin
probes had three passes and five failures, including three unsuccessful
bounded closed-kernel attempts. No infrastructure rerun or resource-limit
change occurred.

The campaign stops at this finding. The existing fixed native-history
theorems are unchanged. All closed receive-step and socket support is
included in this checkpoint. The runtime module adds no theorem or headline:
the owned tree now has 1,043 modules, 2,973 theorems and 397 headlines.
No new mirror-team request arises; the next H1 lifetime statement needs
allocation identity rather than a device-local store address.

## H1 actual receive step and owned socket tags, 2026-10-18

ReceiveStepCallerSource follows the original entry-ring poll. An empty poll
returns false; a consumed packet is dequeued before the actual classified
reception and the returned device's queue counter is decremented only after
success. The projected receipt identifies the initial snapshot, selected
message/source, actual dispatch and valid local helper receipts. Discarding
the observation preserves the original Bool, state and every Stop. These
claims do not assert whole-worker termination, final tags, or continuity
between reception helper cuts.

ReceiveStepCallerClaims contains the projected claims; ReceiveStepCallerFrames
contains the three native-to-projection update equations. Independent review
checked no-device, empty and consumed paths, including the returned-device
update and Stop propagation.

[AGENT 2026-10-18] Close the cached-send tag dependency by strengthening the
campaign-owned H6 SendWork view. It now retains the complete optional tag map
and the selected peer's tag. Existing get/set, cache, routing, send4/send6
and send-buffer compositions supply the fact; their old weaker projections
are retained. SocketTagFrames projects the stronger send-buffer result to
H1. InitiationView is unchanged. No shared lemma, mirror function or frame
was copied or deleted. This settles the cached send-buffer dependency;
cookie replies without a cached peer, receiver keepalive/reference effects
and whole response suffix composition remain separate.

Twelve added theorems, one headline and four modules: H1 409 declarations/48
headlines; campaign 2,973 theorems, 397 headlines and 1,042 modules. H6's
502 declarations and 65 headlines are unchanged. The combined 1,973-job
gate passes all 1,292 terminal axiom checks. The new receive-step target and
all affected H6 targets build; the socket projection builds without warnings.
The development combined 869-job build failed solely on an unfinished
socket projection; its corrected target and the full gate pass. Root
development checks corrected two setter/type failures and three projection
failures; warning-bearing passes were corrected. Receive prototype: six
stdin calls, four corrected failures and two clean passes. Independent
semantic reviews found no defect. No infrastructure rerun or cap failure.

## H1 complete receive dispatch and actual clear dispatch, 2026-10-18

The whole original receiveHandshakePacket now has a checked normal dispatch
classification from its actual load/MAC computation. Cookie input, MAC drop,
cookie-reply attempt, initiation and response paths are distinct. Receipts
are nonempty exactly on consumer dispatch, including consumer refusal.
Initiation yields its consumer then the actual response creation/session
order; response yields its consumer and, on a returned peer, session.
Every captured helper and load/MAC receipt retains a native execution
witness over its projected endpoints. No acceptance or readiness premise is
assumed. Discarding observation gives every original result and Stop.

Independent review identified two presentation gaps in the initial draft:
the allowed-history grammar admitted an unconditional empty history, and
the final claim discarded its gate/helper validity witnesses. The landed
claim closes both. The enum names cookieReplyAttempt: a normal allocation
refusal may send nothing. Wrong-type dispatch cannot return normally, but
an unknown message type may still normally MAC-drop. Classified receipts
return only on normal completion. Separate persistent-journal source
support validates completed receipts before Stop; neither interface covers
writes inside a stopped helper, links successive receipt states, nor
preserves the whole receiver's final tag map.

ReceptionCallerSource holds the actual observer, erasure, receipt validity
and shared source continuations. ReceptionDispatchSource holds the exact
selection grammar and actual load/MAC observer. ReceptionCallerClaims holds
the projected classification/erasure claims. Ten superseded, unlanded
weak-grammar proof declarations were omitted from integration; no existing
frame or theorem was deleted.

ClearDispatchSource reuses owned named/head queue selection and the existing
section contract to carry the zero-key worker's exact final tag effect
through Env.runOneClearWorker. Its projected claim derives the actual
selected peer, initial queue membership, residency and positive refcount.
Duplicate queue occurrences remain allowed; this is one normal dispatch,
not scheduling fairness, queue consistency or reachable completion.
ClearDispatchClaims holds the Product claim. No physical frame was added.

Thirty-nine added theorems and two headlines: H1 397 declarations/47
headlines; campaign 2,961 theorems, 396 headlines and 1,038 modules.
Validation: 709-job scoped build and full 1,969-job gate pass, with 1,291
standard-axiom terminals. Fresh H1 replay passes. Independent reviews
and their capped stdin checks pass; both identified contract/wording issues
are addressed. Receipt prototype: 13 stdin calls (10 corrected failures,
3 passes); strengthening: 7 calls (5 corrected failures, 2 passes); final
versions have no warnings. Dispatch prototype: 2 corrected failures then a
clean pass. No unchanged-source infrastructure rerun, new warning, mirror
change or shared edit.

## H1 whole zero-key worker tags, 2026-10-18

Normal queuedExpiredZeroKeyMaterial preserves every other optional peer
tag. Its caller is absent exactly when the caller's entry reference count
was one, and has a zero tag otherwise. Actual completion supplies initial
residency and positive refcount. No clock, slot, owner-word or queue readiness
premise is added. Original missing/NULL inputs, insufficient alias credits,
invalid counts, queued packets and pending timers retain their Stops.

ClearWorkerFrames derives tag transport from owned ClearRun/clearPut_peers
and adds one named local variant of Keypairs.WGFrames.peerPut_spec for final
reference deletion. ClearWorkerSource composes the actual handshakeClear,
ordered keypairsClear and peerPut; ClearWorkerClaims holds the projection
and Statements adds one headline. Clearing preserves the peer's refcount,
so the deletion test refers to the original entry. This is final tag
coverage for the worker itself, not dispatcher provenance, successful
reachable-state completion, stopped prefixes or the complete final Device.

Five added theorems: H1 358 declarations/45 headlines; campaign 2,922
theorems, 394 headlines and 1,033 modules. Validation: 699-job scoped build,
full 1,964-job gate with 1,289 standard-axiom terminals, and independent
source/axiom review pass; fresh H1 replay passes. One corrected stdin
failure preceded two passes. No infrastructure rerun, new warning, shared
edit, mirror change or deleted frame.

## H1 outgoing callers and finite session evaluation, 2026-10-18

The original initiation sender and handshakeSendWorker now classify the
actual initial rate guard as rate-limited, creator refusal, or created
message. Each reached creator runs once and supplies its actual return,
projected before/after receipt, local TagReceiptEffect and entry tag-map
linkage. Both observers erase to the complete original calls on every
outcome. A refused creator may have made other writes, and a created message
need not be delivered. Worker peerPut may remove the peer after the receipt;
final tags and stopped partial journals are not asserted.

InitiationCallerSource reuses the existing H6 traversal source/suffix and
owned clock/timestamp frames. Its local afterGuard tail is shared by the
prelude and guard proof. InitiationCallerClaims holds the projected normal
and exact-erasure claims; Statements adds two headlines. No new physical
frame is required.

SessionEvaluationSource reduces the actual keypair allocation to bypass or
one original allocPlaceholder/allocRecord encounter and proves equality of
the complete original beginSession with the resulting evaluator. Its fixed
native suffix has no arbitrary callback premise. SessionEvaluationClaims
and one headline expose exact projected outcomes for all input states and
allocation modes, retaining every Stop.

The transitive source audit checks why this is finite evaluation beyond
merely a total Lean function type: deriveKeys uses a two-output KDF and
BLAKE2s finite block/ten-round ranges; hidden consumers use finite scans;
rotation invokes at most two puts; reference, index and store operations
are finite branches/list/tree operations. This path reaches no curve
inversion, worker dispatch, environment callback or second while fixpoint.
The evaluator removes its only nonstructural loop. This establishes logical
outcome evaluation, not universal successful return, a host runtime bound,
or initialized-driver reachability.

Independent reviews found no correctness defect; receipt-cut and refusal
wording now carry their limitations explicitly. Session prototype: two
corrected tactic failures, then a clean capped stdin pass; its independent
stdin replay also passes with standard axioms. No infrastructure rerun.
Counts: 24 added theorems, H1 353 declarations/44 headlines; campaign
2,917 theorems, 393 headlines and 1,030 modules. The 696-job scoped build
passes; the full 1,961-job gate passes with 1,288 standard-axiom terminal
declarations, and fresh H1 replay passes. The independent wording finding
was fixed: encounter helpers may still perform finite scans. There is no
formal step-count relation or compiled-runtime guarantee. No new warning,
shared edit, mirror change or deleted frame.

## H1 peer-creation lifetime boundary, 2026-10-18

The actual peerCreate now has an unconditional normal-return tag-map
contract: numeric refusal leaves every tag unchanged; success sets exactly
the returned location to zero. Other peer locations retain their optional
tags. Cursor overwrite is included, so this is initialization of a location,
not an additional IK protocol edge or an allocation-freshness claim.

[AGENT 2026-10-18] Strengthen the already owned PeerCreateAt invariant with
the newborn zero tag and carry it through its existing cache, handshake
initialization, precompute and timestamp proof. This reuses the complete
source proof instead of duplicating it. The physical update obligations stay
in Index/OwnerCoherencePeerCreateFrames; Source carries the actual control
flow and Claims retains its former H2 interface. Noise/PeerCreationClaims
contains the new projected claim; Statements adds one headline. No shared
layer or mirror changed, and no frame was deleted.

Two added theorems: H1 329 support/claim declarations and 41 headlines;
campaign 2,893 theorems, 390 headlines, 1,026 modules. Validation: 851-job
H1/H2 scoped build and full 1,957-job gate pass, with 1,285 standard-axiom
terminals. Fresh H1 and H2 replays pass. Independent review found no defect;
handshakeInit itself preserves tags, so the zero fact comes from the actual
newborn insertion rather than an arbitrary handshakeInit reset. No new warnings,
infrastructure failure or rerun. Driver-history closure remains open.

## H1 response receipt tag provenance, 2026-10-18

Normal whole response calls now link the creator's entry tag map to the
actual caller entry, and the session's entry tag map to the creator's exit.
The initial clock/timestamp update and intervening MAC update preserve all
optional tags. The existing observer executes every original suffix action;
after the session cut the linkage predicate observes only the recorded
history, so no socket or timer frame is assumed.

Combined with actual receipt order and existing local effects, two receipts
derive CONSUMED_INITIATION at caller entry and CREATED_RESPONSE at the actual
session entry, even when session returns false. Full snapshots need not be
equal across these cuts: timestamp and MAC fields change. This does not
claim final tag preservation, whole-call totality or linkage for receipts
retained on a subsequently stopped call.

ResponseMacFrames holds the explicitly named local variant of
Keypairs.WGFrames.addMacToPacket_spec and two projections of existing clock
and peer-update support. Native chain/capture composition extends
ResponseCallerSource; pure receipt-chain/role predicates and projected claims
extend ResponseCallerClaims. Two already owned private elimination helpers
are reused rather than duplicated. Statements adds one headline. No shared
lemma or mirror changes; no frames are deleted. Fourteen added theorems:
H1 313 to 327, 39 to 40 headlines; campaign 2,891 theorems, 389 headlines
and 1,025 modules.

Validation: 635-job scoped build, full 1,956-job gate with 1,284 standard-axiom
terminal declarations, and fresh H1 replay all pass. Independent source
review found no issue and confirmed the normal-completion qualification.
No new warnings, infrastructure failure or rerun. The separate socket/cache
support request remains the final-map dependency; no mirror change is needed.

## H1 caller coverage inventory, 2026-10-18

A separate source audit found no stale saved-Peer write restoring a tag after
an intervening handshake operation. That inspection is not a kernel-checked
global frame. Direct tag assignments are the four create/consume commits and
handshakeZero; peerCreate additionally installs a zero-tag record, and peer
or device removal makes optional tags absent. The finite seven-operation
language does not yet classify those lifetime changes.

Remaining caller families are outgoing initiation and its worker, the full
handshake receive path and worker, clear work followed by reference release,
lifecycle flushes/removal, and mixed configuration/creation/expiry. The next
bounded step is actual receiveHandshakePacket receipt order using the landed
receptionWith/afterMacWith source factors. It can record all normal helper
calls without assuming final-map preservation.

## H1 total session refusals, 2026-10-18

Two total-return contracts complement the successful-installation result.
For a resident peer whose tag is neither accepted response state,
beginSession returns false for arbitrary Ambient input, preserving the device
and allocation counter. The source equality preserves the entire native WG
state and records both true role-rejection branches; the public claim retains
only the device/counter observations.

For an accepted response tag, an armed, well-formed 40-byte allocation record
whose outcome byte is zero produces false, consumes exactly that record and
preserves device/counter. The remaining record list is arbitrary. The claim
does not require peer liveness, a non-null owner word, hashed entry, slot
credits, or a derivation-clock record. The source equality additionally
preserves the full native WG state. Ambient decision steps may grow.
The record must be the immediate stream head; leading passive records and
other allocation modes remain outside this contract.

SessionRefusalSource has three exact native outcome supports;
SessionRefusalClaims has two projected Returns claims; Statements adds two
headlines. These are totality claims for the named false-return domains,
not exhaustive session totality or initialized-driver coverage. There are no
new frame variants, shared edits, mirror changes or deleted declarations.
Counts: seven added theorems; H1 306 to 313, 37 to 39 headlines; campaign
2,877 theorems, 388 headlines and 1,024 owned modules.

Validation: 634-job scoped build and the full 1,955-job gate pass, with
1,283 standard-axiom terminal declarations. Fresh H1 replay passes. Independent review rechecked the draft in capped stdin, found no
correctness defect, and confirmed the projection, Ambient and record-domain
limits above. Two earlier proof probes failed on Boolean/propositional guard
normalization; corrected proofs pass without warnings. No infrastructure
failure or rerun, and no mirror-team request.

## H1 whole response-caller receipts, 2026-10-18

The observer now follows original sendHandshakeResponse through its complete
normal path. It records the actual createResponse call, then beginSession
exactly when creation returns a message. Normal completion has one creation
receipt with result none, or creation followed by session with their actual
returned message and Boolean. Every receipt is backed by a helper run at its
actual incoming WG/Ambient state and satisfies the existing TagReceiptEffect.
No callback is replayed to manufacture its witness.

The public observer returns existing TagReceipt records with Campaign2
snapshot endpoints. Discard erasure preserves every original outcome,
successful state and Stop. Native persistent-journal support also establishes
validity of receipts retained before a Stop. It records completed helpers:
a stopped beginSession may already have written its tag without emitting a
session receipt. The claim does not cover those internal writes, prove
whole-call totality, connect snapshots across intervening helpers, or preserve
the final tag map. Those broader H1 obligations remain explicit.

ResponseCallerSource contains native observer, order/validity and projection
support; ResponseCallerClaims contains the projected claims. Statements adds
one combined headline. There are no new WG state frames; journal composition
is source-observer support. No conditional final-tag theorem is added and no
shared socket/cache layer is copied. Counts: 23 added theorems; H1 283 to 306
theorems and 36 to 37 headlines; campaign 2,870 theorems, 386 headlines and
1,022 owned modules.

Validation: 632-job scoped build and full 1,953-job gate pass, including
1,281 terminal declarations with only standard axioms. A supplemental audit
of all 40 new public declarations from this and the preceding H1 step also
passes. Its first parser rejected a wrapped axiom line; parsing the same
output with multiline support resolves that reporting failure without a Lean
rerun. Fresh H1 replay passes. Independent review found one wording
issue (normal creator completion includes refusal), corrected in the source,
and no semantic finding. There are no new proof warnings or infrastructure
failures; no mirror change is requested. The socket-tag support request
continues to identify the final-map dependency.

## H1 initial slot credits, 2026-10-18

[AGENT 2026-10-18] Express session release readiness using credits in the
original three slots and count those credits through the actual rotation.

Previously the total session theorem required SessionReady, a release budget
over the already allocated intermediate device. The new theorem derives that
budget from initial ClearReady for all three caller slots and the landed C1
CurrentSlots.SlotInv. It executes the original beginSession using the supplied
successful allocation and clock records, returns true with the same run's
ordered SessionEffect, and preserves enough per-occurrence credits for the
selected peer's final slots. The pure accounting identity says released
occurrences plus retained slots equal the original slots plus one new key.

Old slots may alias each other; their multiplicity is counted. The slot bound
excludes an old slot naming the fresh allocation ID. Final credits mean
resident keys, non-null peer words and sufficient reference counts for this
peer's slots. They do not establish final owner coherence, final SlotInv,
other peers' or packets' funding, or initialized-driver preservation.
Accepted role, live peer, non-null handshake word, hashed handshake and the
successful supplied records remain explicit initial conditions.

InitialSlotCredits contains seven pure relation/accounting lemmas;
InitialSlotClaims contains the projected total-return claim. Statements adds
one headline wrapper. There are no new frames, native state parameters in
the claim, shared edits, mirror changes or type-given deletions. Counts:
H1 274 to 283 theorems and 35 to 36 headlines; campaign 2,838 to 2,847
theorems, 384 to 385 headlines and 1,018 to 1,020 modules.

Validation: 630-job scoped build and complete 1,951-job proof gate pass,
with 1,280 terminal declarations using only the standard axioms. Fresh H1
replay passes. Independent source review found no semantic defect and
confirmed the alias, caller-only funding and reachability limits above.
Exploratory stdin drafts had unused simp arguments; the checked files have
no warnings. The inherited mirror deprecation remains reported. No
infrastructure failure or rerun occurred. No mirror change is requested;
the separate socket-tag proof-support inventory remains open.

## Campaign-1 GRO carry, 2026-10-18

[USER 2026-10-18] Incorporate campaign 1's validated 8ba82097 carry directly
on the campaign branch and treat its later identical main landing as already
incorporated. Continue whole-run claims in charter order, beginning with H1.

The incoming proof changes use actual successive GRO selections. All shared
proof files remain byte-identical to that commit; the gate and executable
mirror remain byte-identical to main 77c9b555. The sole merge conflict was the
register introduction. No campaign-owned proof changed, so before and after
counts are identical: 2,838 theorems, 384 headlines and 1,018 owned modules;
zero retyped, zero deleted, all retained. The per-result table above records
the remaining scope, which a green combined gate does not close.

Validation: the full capped proof-gate passes all four stages, with 1,949
build jobs and 1,279 terminal declarations restricted to propext,
Classical.choice and Quot.sound. The inherited Env.lean:865 String.mk
deprecation is reported and left to its mirror owner; no proof warning was
introduced. Fresh combined-root kernel replay passes. No guest, mirror or
shared-lemma edit was needed, and no infrastructure retry occurred.

The H1 socket inventory requests stronger shared observations for three
composite socket contracts and four cache/transmit leaf families. Those
families have not been copied locally. Session-credit and actual caller
receipt work proceed independently.

## Main landing and H2 bulk removal, 2026-10-18

[USER 2026-10-18] Incorporate main 77c9b555 and use campaign 1's landed
proof layers and gate, preserving the campaign-owned claim/frame boundary.
[AGENT 2026-10-18] Project the newly landed contracts for the five existing
temporary adapters and the missing H2 bulk-removal frame; do not reproduce
the broader shared traversal layers.

All 916 incoming shared proof files and scripts/proof-gate are byte-identical
to main. Nine obsolete inherited Keypairs/Frames files absent from main are
removed as part of selecting the landed tree, not counted as new type-given
deletions. Every landed root import remains, together with the six H1–H6 roots.
The main-owned GRO correction is the only incoming mirror change. No owned
GRO classifier or continuation needed rewriting: the observers execute actual
napiGroReceive/napiGroFlushAll and retain their actual suffix outcomes.

Five existing proof bodies now use landed contracts: Index/AipRemovalFrames
uses Framing.hoare_liftAip; Roaming/RateLimitFrames projects the three
Framing/WGCookie contracts; Progress/BatchDrainFrames projects
Framing/EnvLeaves.deliverSent_sameKernel to the exact optional Device.
Their statements and premises are unchanged. These are proof reuse, not
type-given deletion or new totality claims.

H2 now also proves original peerRemoveAll preserves View.TablesSafe on normal
return. BulkRemovalFrames projects AllowedIps.free_storeView to the exact
index table/allocation cursor; BulkRemovalClaims composes the actual free,
saved post-free peer list, complete dead-marking loop and complete cleanup
loop. The sole entry requirement is table safety. Missing peers, malformed
tries, queue/clock failures and other Stops remain actual computation outcomes.
This claims neither completion, empty stores, owner residency nor initialized
whole-driver coherence. It closes the narrow bulk-removal dependency in the
older shared-frame request without copying rootRemovePeerLists/free support.

Carry accounting from 76cbd196: all 2,818 owned theorems and 379 headlines
are retained, no claims are retyped, no owned theorem is deleted, and five
bodies reuse shared proofs. H2 adds one native frame, one projected claim and
one terminal wrapper in two new modules: 2,821 theorems, 380 headlines and
1,008 owned modules afterward. Claims remain in BulkRemovalClaims and
Statements; the native preservation fact is in BulkRemovalFrames.
All H1–H6 statuses and remaining scope are in the current table above.

Validation:

- Full capped proof-gate: FAIL, one build finding, with failures in
  Logged/PrefixGro, Logged/RxPoll and WG/Queues/GroState after removal of
  groTakenAtOnce. Failed elaborations also emit declaration-uses-sorry and
  linter diagnostics; no successful result is credited to those modules.
  The token/import/default-target checks pass. The full terminal axiom stage
  is skipped after the build failure. Campaign 1 owns this carry.
- All 1,006 pre-extension owned modules: scoped build PASS, 1,082 jobs.
  The new H2 terminal closure: PASS, 459 jobs. Env:865's existing String.mk
  deprecation remains inherited and unsuppressed.
- Current owned closure: 5,314 public logical declarations in 1,088 proof
  modules, including 3,676 public theorem roots, use only propext,
  Classical.choice and Quot.sound. The scratch scanner initially read a
  comment as a declaration; using the gate's comment scanner fixes that
  audit-tool error. No missing or nonstandard axiom remains.
- Fresh replay: all six terminal closures PASS. An unscoped leanchecker --help invocation failed
  at the unchanged 32 GiB cap (exit 137). Its CLI ignores that flag and
  selected the whole project; it also printed a problem in SendSocketView
  before termination. This is a failed run, not proof evidence. One scoped
  replacement attempt checked the six terminal closures with --fresh, including
  SendSocketView through TimerDiscipline. All six return exit 0; no cap increase
  or second infrastructure retry.
- Original 258 headline names/order and all static tree checks pass.
  Independent merge, shared-projection and H2 composition reviews have no
  unresolved findings. Three direct-file adapter probes and the combined
  H2 probe check after correcting explicit bridge arguments and projection
  normalization. No cap increase or guest run. Incoming shared files also
  retain six existing blank-at-EOF diff-check warnings; campaign-owned changes
  pass diff --check, and shared-file identity is preserved.

Reproduce the scoped checks with the standard bundle/capped wrapper, 32 Lean
threads and 16 QEMU slots: lake build each owned module (or the six terminal
roots for their closures), print axioms, and lake env leanchecker --fresh
Leanux.Proofs.WG.<result>.Statements. The full gate remains
scripts/proof-gate; it is reported as failing, not replaced by these checks.

The landed PublicationHistory/PublicationChecks path still reaches the three
broken GRO layers, so it does not yet supply H3's persistent queued provenance.
H4's ClearEndpoint and represented insertion support are available independently;
the initialized bulk-removal emptiness theorem still reaches the GRO lag.
No mirror change is requested. The ranked useful support change is campaign
1's GRO carry (proof-only, altitude-preserving); no mirror restructuring is
needed for this H2 increment.

## H2 continuation: confirmation preserves the index invariant

The original receivedWithKeypair now preserves numeric-index uniqueness,
embedded-owner uniqueness and the hashed-keypair allocation bound through
both false exits, ordered slot writes and immediate old-previous release.
The claim keeps an optional device and arbitrary Ambient inputs; it adds no
residency, distinct-slot, reference-budget or successful-confirmation premise.
Failures remain outside its normal-return conclusion. This is one missing
confirmation edge toward whole-driver propagation, not owner-word coherence,
reachability or complete H2 coverage.

Architecture: Index/ConfirmationClaims uses the campaign projection directly
and composes existing get/branch/peer-write/key-release contracts. Existing
frames stay in their separate files; no shared-layer variant is added.
Index/Statements appends one documented headline without changing the prior
52. H2 now has 53 headlines and 335 theorems; the campaign has 259 headlines
and 1,985 theorems. No existing statement is reshaped and no new finding occurs.

The first capped probe passes at the default limit. The scoped Index.Statements
build passes 257 jobs; its only warning is inherited Env:865 String.mk.
Axioms: 995 logical roots in 193 modules, including 644 public theorem roots,
standard only. Fresh kernel replay passes. Static checks and original-name
order pass; independent review finds no issue. No limit/cap increase, failed
probe or infrastructure rerun. The full-gate failure in inherited
CounterWindow/ReplayWindow remains as recorded; it is not rerun unchanged.
Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 threads and 16 QEMU slots.

No mirror change is requested for this step: existing narrowed operations and
proof contracts suffice. The next bounded obligations are lookup preservation
of an explicit hashed-owner coherence predicate and data-ingress table safety.

## H2 continuation: local hashed-owner coherence

A separate pure predicate now relates every hashed owner to a resident,
positively referenced peer. Handshake owners point to their containing peer;
keypair owners also name a resident, positively referenced keypair. It does
not require unique rows, a live isDead flag, an upper reference bound or
distinct IDs. It is a local entry invariant, not a reachable-state theorem.

Native lookup preserves that invariant on every normal return. Absent or
disallowed rows leave the device unchanged; NULL/zero-reference empty causes
contradict the supplied invariant. A successful lookup uses the actual
peer-reference increment followed by same-word owner storeback, handling aliases
through pointwise lookups without asserting TreeMap representation equality.

Allocation preserves the joint table-safety and coherence predicates. The
hashed-owner allocation bound prevents overwriting a hashed keypair; existing
unhashed objects may be overwritten and the new peer word may be arbitrary or
NULL. The new object is not yet published. Refusal and absent-device behavior
are retained under normal-return semantics, without completion or lifetime claims.

Removal and its actual keypair specialization preserve coherence and are total
for a present device. Insertion preserves it on normal completion when the
newly published owner is explicitly coherent. Handshake replacement is total
with an explicitly coherent destination keypair; its exact Boolean/table effect
allows existing destination rows, so this theorem does not assert owner
uniqueness. These publication premises are obligations for callers, not inferred
reachability facts. All claims use the native projection.

Architecture: OwnerCoherenceModel holds the three predicates; OwnerCoherenceFrames
and OwnerCoherenceAllocationFrames hold preservation facts; TableEffects holds
the three pure table transformations. Source/Claims files connect them to the
actual operations; six literal terminal wrappers are appended in Statements.
The existing own-result liftSkb_tables helper is made public without changing
its body for the forthcoming ingress proof; no theorem is added by that change.
Its eleven affected modules are all within Index and covered by the check.
No existing shared lemma or mirror function is edited.

This tranche adds 21 theorems: lookup seven, allocation three, table primitives
eleven. H2 has 59 headlines and 356 checked theorems; campaign totals are
265 headlines and 2,006 theorems. Existing claims are not reshaped. Global
reachability, complete driver-entry propagation and release ownership remain
open. No new mirror request is needed; the narrowed types and actual source
contracts suffice for these local obligations.

Development: lookup probe 1 fails three diagnostics with two unused-simp
warnings; changed probe 2 passes. Allocation probes 1 and 2 fail three and
five proof/import/projection diagnostics; changed probe 3 passes. Primitive
probes 1 and 2 each fail one proof-form diagnostic; probe 3 passes. The first
terminal packaging build fails four syntax errors because extraction stopped
at a record-field assignment; corrected extraction fixes them. All final
new proofs use the default limit, without warning suppression or cap changes.
Independent review of all three packages finds no correctness/domain issue
and identifies the need for literal terminal wrappers, which are supplied.

The promoted helper builds in 137 jobs; lookup integration passes 261 jobs.
The final combined Index.Statements build passes 265 jobs, with only inherited
Env:865 String.mk. Axiom inspection checks 1,020 logical roots in 201 modules,
including 666 public theorem roots, using only standard axioms. Fresh replay,
static checks, original 258-name order and mirror/shared boundaries pass.
No infrastructure rerun or unchanged failed-source rerun occurs. The inherited
full-gate failure remains recorded and is not rerun unchanged.

Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: data-ingress table preservation

The actual consumeData now preserves numeric-index uniqueness, embedded-owner
uniqueness and the hashed-keypair allocation bound on every normal return.
The only entry premise is TablesSafe; optional device, arbitrary Ambient inputs,
aliases, malformed objects and queue states retain their actual stopped outcomes.
Lookup, NULL/keypair acquisition, dead-peer cleanup, skb allocation, device/peer
enqueue, EPIPE publication and unsuccessful-enqueue cleanup all remain in the
source order. The short-circuit enqueue condition is the actual WG.orM.

Architecture: Index/RxQueueFrames contains two receive-queue preservation
contracts, named as local variants of WGMore.enqueuePerDeviceAndPeerRx_spec
and enqueuePerPeerRx_pure_spec. They reuse the guarded skb-store adapter and
existing reference/release contracts. Index/ReceiveDataClaims contains the projected source claim, composed
through proof-local factors whose equality to consumeData is reflexive.
Index/Statements appends one literal headline. The publication frame covers
the actual empty WG callback in consumeData, not arbitrary interrupt callbacks.
Full packetReceive/wgReceive, decrypt/poll workers and environment closure remain
open. This does not establish owner coherence or reachability.

The split removes the need for separate skb allocation/update/free frames:
their SkbM types and the existing guarded adapter supply table preservation.
This tranche uses two substantive queue families from the old ingress inventory,
not the broader worker layer. No shared lemma or mirror operation is edited.
No existing claim is reshaped; four new theorems bring H2 to 60 headlines and
360 theorems, and campaign totals to 266 headlines and 2,010 theorems in 598
owned modules. No mirror change is requested.

Development: probes 1–3 fail five, 101 and two diagnostics respectively
(composition, malformed pair-case tactic, then matcher branches). Probe 4
reaches the default heartbeat limit. Probe 5 has ambiguous orM/factor errors,
two default-limit failures and one warning; probe 6 has two default-limit
failures. Probe 7 has two unspecified-intermediate-predicate errors and two
unused-simp warnings. Changed probe 8 passes cleanly after explicit local source
factoring. An earlier package-generation search fails before Lean because the
reused skb helper had been promoted from private. No limit/cap increase, warning
suppression, infrastructure retry or unchanged failed-source rerun occurs.

Final scoped Index.Statements build passes 267 jobs; only inherited Env:865
String.mk warns. Axiom audit checks 1,024 logical roots in 203 modules, including
670 public theorem roots, standard only. Its first fresh replay passes; after
renaming the two frames as shared-lemma variants, the 267-job rebuild also
passes. Final combined replay is reported below. Static
checks, original 258-name order and mirror/shared boundaries pass. Independent
review finds no correctness/domain issue and confirms the callback restriction.
The inherited full-gate failure remains recorded, without an unchanged rerun.
Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under capped
with 32 Lean threads and 16 QEMU slots.

## H2 continuation: coherence needs release ownership

The proposed unrestricted preservation of OwnerCoherentSafe by peerPut is
false. A checked native witness starts with peer 0 and keypair 0 each at
reference count 1, keypair.peer = some 0, one hashed keypair row at index 7,
and empty queues/timers. Every actual WG/Ambient realization of that device
returns normally from peerPut (some 0): it removes the handshake owner if
present, erases peer 0 and retains the keypair row/object. The initial device
is coherent under the local predicate; the final device is not.

[AGENT 2026-10-17] Classify this as a statement-domain artefact: the predicate
omits reference ownership and release/unhash ordering. The witness does not
establish reachability, an accepted runner trace or a mirror/kernel defect.
No existing theorem is weakened or retired, and no mirror repair is requested.

A second checked theorem characterizes the missing obligation exactly for
the pure last-release device effect. Under initial hashed-owner coherence
and p.refcount = 1, final coherence holds iff every retained hashed owner
does not name the released peer. Other handshake owners already satisfy this
under coherence; retained keypair owners supply the substantive obligation.
This pure equivalence needs no resident-peer premise. Applying it to the
actual release still requires the resident peer and actual normal outcome;
the theorem supplies neither readiness nor reachability.

Architecture: Index/OwnerCoherenceReleaseFindings holds the native witness;
OwnerCoherenceReleaseFrames holds the pure preservation equivalence.
Statements appends two literal documented headlines. Four new theorems bring
H2 to 62 headlines/364 theorems and the campaign to 268 headlines/2,014 theorems
in 600 owned modules. The completed retrofit counts remain unchanged.

Finding probe 1 fails three record-layout syntax diagnostics; changed probe 2
passes. The equivalence's probe 3 fails four lookup/case goals and four
unused-simp warnings; changed probe 4 passes cleanly. No limit/cap increase,
warning suppression or infrastructure rerun occurs. Independent review finds
no correctness/domain issue and confirms the pure/operational distinction.

The final combined Index.Statements build passes 269 jobs; only inherited
Env:865 String.mk warns. Axiom audit checks 1,028 logical roots in 205 modules,
including 674 public theorem roots, standard only. Fresh kernel replay passes.
Static checks, original-name order and mirror/shared boundaries pass.
The inherited full-gate failure remains recorded and is not rerun unchanged.
Reproduce using the same scoped Index.Statements build and fresh replay
commands above, under capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: removal and conditional release coherence

Original removeByPeer and outer peerRemove now preserve table safety on
every normal return, with only TablesSafe at entry. The removal frame keeps
the exact optional (indexTable,nextKeypairId) pair. It uses the actual
allowedipsList snapshot, ordered listDel operations, every malformed-node
branch and the original pubkey-removal branch before marking the current
peer dead. Outer removal retains NULL handling, key clearing, actual worker
flushes, crypt-work refusals and final peer release through the existing
after-dead contract. No NodePairs, residency, readiness or owner-coherence
premise is added; no completion or owner-coherence conclusion is claimed.

The split supplies preservation for slotSet/subtree through their AipM types
and a guarded liftAip adapter. Only two mixed-WG removal families remain
necessary here. Index/AipRemovalFrames has three local variants of campaign
1's hoare_liftAip, removeByPeer_spec and peerMakeDead_spec, following its
native lift shape. Index/PeerRemovalClaims holds the two projected claims.
The broader rootRemovePeerLists/free and peerRemoveAll layer remains pending;
this package does not copy it or establish H4's general ownership transport.

The actual peerPut also has a normal-return owner-coherence contract using
the checked release obligation. It requires the actual resident positive
peer and explicitly requires every retained hashed owner to be detached on
last release. Nonfinal decrement preserves coherence without detachment:
the actual resident peer retains positive count and its embedded word.
Queue/timer refusals remain actual stopped outcomes; no readiness premise
is supplied. Index/OwnerCoherenceDecrementFrames holds the pure frame and
OwnerCoherenceReleaseClaims the projected source contract. This derives no
reachability or global reference-ownership invariant.

Three literal documented headlines are appended. Seven removal declarations
and three conditional-release declarations bring H2 to 65 headlines/374
theorems, and campaign totals to 271 headlines/2,024 theorems in 604 modules.
No existing claim is reshaped, shared lemma or mirror code edited, or mirror
change requested. Independent reviews of both packages find no issues.

Removal probe 1 fails record syntax, a projection mismatch and broad
automation at the default heartbeat limit. Probe 2 fails remaining record
syntax/liftM leaf mismatches and has one binder-name warning. Changed probe 3
passes the adapter/removal frame; probe 4 passes all five support/claim
declarations cleanly. Conditional-release probe 1 fails a nested-run rewrite
and reports one deprecation warning; probe 2 fails an Except.map reduction;
changed probe 3 passes cleanly. All final new proofs use default limits,
without cap/limit increases, suppression or infrastructure retries.

Final scoped Index.Statements build passes 287 jobs, with only inherited
Env:865 String.mk warning. Axioms: 1,156 logical roots in 223 modules, including
763 public theorem roots, standard only. Fresh kernel replay passes. Static
checks retain all 258 original names/order; mirror/shared boundaries pass. The inherited full-gate failure remains recorded and
is not rerun unchanged. Reproduce with the scoped Index.Statements build and
fresh replay above, under capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: keypair release preserves owner coherence

Original keypairPut preserves local hashed-owner coherence on every normal
return, with that invariant as its sole entry predicate. The key argument,
immediate-unhash flag, optional device and Ambient inputs are arbitrary.
Last release unhashes all rows for the key before erasing it; retained hashed
keys keep their peer word and positive count. Peers are unchanged, so no
peer-release detachment obligation is needed.

The source proof retains NULL input, absent device, missing key, zero count,
immediate-unhash dereference and deferred final-NULL refusal. A deferred
nonfinal key with a NULL word may return normally; the proof uses the existing
retained-key contract rather than imposing the non-NULL premise of the
stronger total exact-effect helper. No reference upper bound, readiness,
freshness or object-residency premise is added to the projected theorem.

Architecture: Index/OwnerCoherenceKeypairReleaseFrames holds pure preservation
of the actual resident/live key effect. OwnerCoherenceKeypairReleaseClaims
derives the actual normal-run cases and applies it; Statements appends one
literal documented headline. These three new theorems bring H2 to 66
headlines/377 theorems, and campaign totals to 272 headlines/2,027 theorems
in 606 modules. No existing claim is reshaped or shared/mirror code edited.
This does not establish global ownership or reachability. No mirror request
is needed.

Probe 1 elaborates with two unused-simp warnings; changed probe 2 fixes them
and passes cleanly at default limits. The warnings are fixed before
integration, without limit/cap increases, suppression or infrastructure retry.
Independent review finds no correctness/domain issue, including the retained
NULL-word case and the distinction from peer release.

The scoped Index.Statements build passes 289 jobs, with only inherited
Env:865 String.mk warning. Audit checks 1,159 logical roots in 225 modules,
including 766 public theorem roots, standard only. Fresh kernel replay passes.
Static checks retain all 258 original terminal names/order; mirror/shared
boundaries pass. The inherited full-gate failure remains recorded without an
unchanged rerun. Reproduce with the scoped Index.Statements build and fresh
replay commands above, under capped with 32 threads and 16 QEMU slots.

## H2 continuation: session-wide hashed-owner coherence

Every normal beginSession return now preserves coherence of all hashed
owners. Entry requires the actual resident caller, hashed-keypair owner IDs
below the allocation cursor, the existing SessionRotationFresh condition,
and local hashed-owner coherence. No table uniqueness, whole-store freshness,
self peer-word, positive-caller, reference budget, readiness or successful-result
premise is added.

The false return retains the device. On success, the actual SessionEffect
supplies a surviving handshake row. Rotation's exact handshake-membership
equivalence places that row in the entry table; coherence derives the caller's
self peer-word. Coherence of the surviving row after rotation supplies the
resident positive peer for the new key's publication. The allocation bound
prevents overwriting a hashed key; unhashed allocation-ID objects remain
allowed. Rotation freshness excludes only releases of the new key ID.
All other slot aliases and repeated releases retain their actual semantics.

Architecture: Index/OwnerCoherenceSessionFrames holds resident-peer write,
prepared-device and RotationRun preservation; OwnerCoherenceSessionEffects
composes the exact successful/false device effects; OwnerCoherenceSessionClaims
connects them to the native operation through the projection. Statements
appends one literal headline. Six new theorems bring H2 to 67 headlines/383
theorems and campaign totals to 273 headlines/2,033 theorems in 609 modules.
No existing claim is reshaped or mirror/shared layer edited. The static
freshness/bound obligations remain unproved reachability conditions, and
whole-driver H2 is still open. No mirror change is requested.

Probe 1 fails four case-rewrite goals without warnings. Changed probe 2
passes all five support/claim declarations cleanly at default limits.
Independent review finds no correctness/domain issue, including derivation
of the self-word and positive-peer facts from the actual publication row.
No limit/cap increase, warning suppression or infrastructure retry occurs.

Scoped Index.Statements build passes 292 jobs, with only inherited Env:865
String.mk warning. Audit checks 1,165 logical roots in 228 modules, including
772 public theorem roots, standard only. Its final replay is included in the
combined checkpoint below; original-name/order and boundary checks pass.
The inherited full-gate failure remains recorded, without an unchanged rerun.
Reproduce with the scoped Index.Statements build and fresh replay commands
above, under capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: confirmation and clearing preserve owner coherence

Original receivedWithKeypair and keypairsClear each preserve local coherence
for all hashed owners on every normal return. Coherence is the only entry
predicate; the optional device, caller IDs, slot aliases and Ambient inputs
remain arbitrary. The actual first peer read supplies the source effect's
residency, while each successful put supplies its resident/live/word facts.
Missing objects and refused releases remain Stops.

Confirmation's false branch retains the device; its true branch uses the
checked ordered rotation. Clearing follows each evolving resident peer and
its actual put, including repeated or aliased slot IDs. Neither claim promises
completion, positive references for every slot, or global reachability.

Architecture: Index/OwnerCoherenceClearFrames proves pure ClearRun
preservation using the peer-metadata write and key-release frames.
OwnerCoherenceKeypairCallerClaims applies actual source effects through the
projection. Two literal terminal headlines are appended. Five new theorems
bring H2 to 69 headlines/388 theorems. Existing claims remain unchanged.
No shared/mirror edit or mirror request is needed.

Probe 1 fails dependent ClearPut elimination; changed probe 2 fails an
incorrectly explicit start-device argument; probe 3 passes cleanly at default
limits. Independent review finds no issue, including the derivation of
residency from actual execution and both confirmation branches.
Final combined validation is recorded below.

## H4 continuation: mixed fwmark and peer-setting readback

The actual setter/getter sequence now has a mixed-attribute readback theorem:
set fwmark together with one peer's preshared key and keepalive interval,
then run wgGetDevice. The result contains the model's exact JSON and completed
socket state. A malformed second peer returns normal -EINVAL after retaining
the earlier fwmark, generation, endpoint-source/cache and scalar writes.
The proof records every non-peer Device field, the selected peer's actual
cleared/configured state and all other peer bindings.

The domain is explicit: creating namespace, singleton peerList, actual
hashtable hit and resident positive peer with room for its lookup reference,
and a stopped device. The getter additionally requires no Allowed IPs for
that peer, sufficient space, an idle empty socket and actual device selection.
The claim adds no reset-record readiness: a genuine reset Stop prevents the
getter, and the existential reset timestamp is obtained from the successful
source prefix. It asserts no post-error state. The mark is an arbitrary Nat
in the mirror; current dumping uses direct JSON conversion, so this is not
a theorem about netlink byte serialization or u32 input validation.

Architecture: Config/MixedAttributeModel defines the request, updated
device, cleared/scalar peer and exact effect predicate. MixedAttributeFrames
separates socket/selector preservation across the actual endpoint-source clear.
MixedAttributeSource proves the native setter effects; MixedAttributeClaims
composes the actual projected set/get. Statements appends one literal headline.
Four new theorems bring H4 to 80 headlines/586 theorems. Together with the H2
continuations, the campaign has 276 headlines and 2,042 theorems in 615 modules.
No existing claim is reshaped or shared/mirror code edited. General mixed
requests, ownership, queued-cleanup completion and pagination remain open.
No mirror change is requested.

Probes 1–2 fail source factoring/normalization, with five unused-simp warnings
in probe 2; changed probe 3 passes the frame and source. Probe 4 fails record
syntax and a reserved local name; probe 5 fails projection/congruence and
nested-precondition elaboration; probe 6 passes all three new proof declarations
cleanly. Every warning is fixed. Both H2 and H4 packages use default new-proof
limits; no cap/limit increase, suppression or infrastructure retry occurs.
Independent review finds no issue and confirms actual prefix failures,
partial-mutation ordering and the JSON-only observation domain.

Combined Index.Statements and Config.Statements build passes 414 jobs, with
only inherited Env:865 String.mk warning. Axiom inspection checks 1,731 logical
roots in 350 modules, including 1,192 public theorem roots, standard only.
Both fresh kernel replays pass. Static checks retain all 258 original
terminal names/order; mirror/shared boundaries pass. The full
gate still fails in inherited CounterWindow/ReplayWindow and is not rerun
unchanged. Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.Index.Statements Leanux.Proofs.WG.Config.Statements, followed
by scripts/in-bundle lake env leanchecker --fresh for each module, under capped
with 32 Lean threads and 16 QEMU slots.

## H6 continuation: first actual outer timer turn

The actual runTimers now has an exact first-turn connection to the checked
timerDispatchUnit_variant. Its projected entry predicate requires a present
device, an initial non-passive record naming a non-clear timer worker, and
the actual TimerWheel.nextDue selection. No callback-success, readiness,
record-sufficiency or logical-expiry premise is added. The original initial
queue reset and captured record budget are retained; the remaining original
turns, early breaks, step checks, delivery and final queue rejection follow
the unit unchanged. Worker/unit mismatches, callback failures and suffix
failures therefore remain exact outcomes from the same actual Product entry.

Architecture: TimerDiscipline/OuterFirstTurnSource contains the operational
factors and native equality proofs; OuterFirstTurnModel contains the projected
selection predicate; OuterFirstTurnClaims contains the projected agreement.
Statements appends its literal wrapper. No frame lemma, shared-layer copy,
state reconstruction or mirror edit is needed. Four theorems bring H6 to
51 headlines and 442 theorems, and the campaign to 277 headlines and 2,046
theorems in 618 modules. No existing statement is reshaped. This establishes
neither successful dispatch nor an entire retry episode, and does not move
the caller's requireNothingDue check into runTimers.

Development: seven changed probes fail with error/warning counts 1/2, 5/1,
7/6, 2/0, 5/0, 2/1 and 3/0 (source-factor congruence, monadic normalization,
branch rewrites and type/destructuring syntax). Probe 8 passes without
diagnostics. All proofs use default limits and the unchanged memory cap;
there is no unchanged retry or infrastructure failure. Independent review
finds no issue. No mirror change is requested.

The integrated scoped build passes 312 jobs with only the inherited Env:865
String.mk warning. Axiom inspection checks 1,375 logical roots in 270 modules,
including 780 public theorem roots, with standard axioms only. Fresh replay
passes. Static checks, original 258-name order and mirror/shared boundaries
pass. The inherited full-gate failure remains unchanged and is not rerun.
Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.TimerDiscipline.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 Lean threads and 16 QEMU slots.

## H6 continuation: first retransmission receipt

A normal actual runTimers return now supplies the first selected retransmission
unit's intermediate observations. The receipt records the original remaining
budget, the actual selected-prefix snapshot, the immediate post-unit snapshot,
and the exact outcome of the remaining original continuation. Its retry count
is nextAttempts of the entry count and its retransmit timer is detached at
that intermediate point. Later turns can change those fields again; no claim
is made about their values at the whole call's final state.

The entry premises are actual first record/wheel selection and the existing
retry observation. Prefix, callback and suffix success follow from the
normal whole-call return; no readiness, empty-queue, attempt-bound or successful
callback premise is inserted. The existing observed_erase theorem retains
every original error, independently of these entry premises. The receipt
inspects its suffix on the actual post-unit product, preserving all fixture
inputs rather than reconstructing a state from its projection.

OuterFirstReceiptSource contains the small receipt path and native decomposition;
OuterFirstReceiptClaims contains the projected effect; Statements adds the
literal wrapper. The three new theorems add no frame layer, changed statement
or mirror request. This supplies an intermediate transition for later induction,
but does not establish adjacency to a send worker or the inspection conditions
needed for a complete retry pair.

Development: probe 1 fails eight parser errors from a reserved local name;
changed probe 2 passes without diagnostics. The integrated build passes 314
jobs with only the inherited Env:865 warning. All 1,380 logical roots in 272
modules, including 783 public theorem roots, use standard axioms. Independent
review finds no issue. Fresh replay passes; no cap/limit increase or
infrastructure rerun occurred. Reproduction uses the same TimerDiscipline.Statements
build and fresh replay commands as the preceding first-turn increment.

## H2 continuation: data-ingress owner coherence

The actual consumeData now preserves hashed-owner coherence on every normal
return, with coherence alone at entry. Lookup supplies a newly held positive
peer reference and the selected hashed key's original positive reference;
keypairGet then supplies its extra reference. Dead-peer and failed-enqueue
cleanup release those acquired references, so the problematic final-peer
detachment case cannot occur. EPIPE publication temporarily acquires another
peer reference and restores it. Missing lookup, all aliases and arbitrary
Ambient inputs retain their original domains; missing objects, overflow,
queue membership and recorded-work refusals remain Stops. This establishes
local preservation, not completion or initialized whole-driver reachability.

OwnerReferenceModel retains the index table, keypair store and pointwise peer
presence/owner-word/reference count. OwnerReferenceFrames contains its pure
coherence transport and key-acquisition preservation. RxQueueOwnerFrames
contains the guarded Skb adapter and stronger variants of the same two queue
families already covered by RxQueueFrames. It asserts no arbitrary callback
preservation: publication uses the actual pure callback. The lookup-held
and final caller claims are projected in OwnerCoherenceLookupHeldClaims and
OwnerCoherenceReceiveClaims; Statements appends the literal headline. No
broader shared-layer inventory is copied, and no existing shared lemma or
mirror operation is edited. The ten new theorems bring H2 to 70 headlines
and 398 theorems; together with the H6 receipt, the campaign has 279 headlines
and 2,059 theorems in 625 modules. No statement is reshaped or new mirror
change requested.

Development: support/caller author probes 1–4 fail with 2, 1, 1 and 5 errors;
5 passes, 6 passes with one unused-simp warning, and corrected 7 passes clean.
Probe 8 fails three diagnostics from continuation indentation; its later caller
portion is not accepted. Root's changed caller probe 1 exposes one remaining
positive-count obligation, and changed probe 2 closes it without diagnostics.
The separate lookup-held helper has one failed probe (two normalization/kind
errors and three unused-simp warnings), followed by a clean changed probe.
All use default limits and the unchanged memory cap; there is no infrastructure
or unchanged-source rerun. Independent review of support and the final caller
finds no issue.

The support build passes 183 jobs without warnings; final Index.Statements
passes 299 jobs with only inherited Env:865 String.mk. Axioms: 1,181 logical
roots in 235 modules, including 786 public theorem roots, standard only.
Fresh Index replay passes. Static checks, original terminal-name order and
mirror/shared boundaries pass; the unchanged inherited full-gate failure is
not rerun. Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Index.Statements
and scripts/in-bundle lake env leanchecker --fresh on that module, under
capped with 32 Lean threads and 16 QEMU slots.

## H2 continuation: handshake clearing and expiry preserve coherence

Both actual handshakeClear and expireCurrentPeerKeypairs now preserve local
hashed-owner coherence on every normal return. Coherence is the sole entry
premise: optional device, missing or NULL peer words, zero counts on unhashed
objects, arbitrary clocks and repeated next/current identities retain the
original partial domain. The exact native Config contracts carry ordered
handshake removal/zeroing, last-sent time reset and both validity writes.
The pure missing-key identity in invalidateDevice is not a claim that native
expiry succeeds when a selected key is absent.

Architecture: OwnerCoherenceExpiryFrames holds three pure preservation facts;
OwnerCoherenceExpiryClaims holds two projected claims; Statements appends two
literal headlines. No broader owner-reference projection is weakened to hide
validity writes, and no shared lemma or mirror operation is edited. Seven
theorems bring H2 to 72 headlines/405 theorems and the campaign to 281
headlines/2,066 theorems in 627 owned modules. Whole-driver reachability and
final queued-worker release ownership remain open. No new mirror request.

The sole capped source probe passes with no diagnostics at the default limits.
Independent review finds no issue. Index.Statements builds 301 jobs, with only
inherited Env:865 String.mk. Axioms: 1,188 logical roots in 237 modules,
including 793 public theorem roots, standard only. Fresh kernel replay passes.
Static checks, original terminal-name order and mirror/shared boundaries pass.
No limit/cap increase or infrastructure rerun occurs; the unchanged inherited
full-gate failure is not rerun. Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.Index.Statements and scripts/in-bundle lake env leanchecker
--fresh on that module, under capped with 32 Lean threads and 16 QEMU slots.

## H1 continuation: the response edge starts at whole-call entry

An actual consumeResponse returning a peer now derives that peer's entry
CREATED_INITIATION tag and final CONSUMED_RESPONSE tag. Previously the H3
observer established the former only after lookup. The new pure lookup-update
frame proves that acquisition and owner-word storeback preserve the referenced
peer's tag, including owner/peer aliases. Actual prefix execution and existing
observer erasure connect that fact to the whole call. No residency, coherence,
authentication or record-readiness premise is added.

ResponseEdgeFrames, ResponseEdgeSource and ResponseEdgeClaims separate the
pure frame, native bridge and projected claim; Statements adds a literal wrapper.
Four theorems bring H1 to 23 headlines/189 theorems. Failed-call rollback,
whole-driver edge ownership and allocation-lifetime confirmation remain open.

## H2 continuation: response and cookie consumers retain owner coherence

Actual consumeResponse and cookieMessageConsume now preserve local hashed-owner
coherence on every normal exit. A general indexLookup_peer_held contract derives
the retained peer reference from the actual returned lookup for any owner mask.
OwnerCoherenceHeldFrames contains the internal native held-reference predicate,
metadata-preserving peer writes and non-final cleanup; the two public caller
claims remain projected. Response composition reuses the existing exact H3
observer; cookie composition factors the actual original consumer.

Rejected paths, optional devices, arbitrary records and all aliases remain in
the original partial domain. Crypto/clock errors remain Stops. No entry reference
budget or cleanup readiness is assumed; successful lookup supplies count greater
than one, which discharges final-release detachment internally. Seven theorems
bring H2 to 74 headlines/412 theorems. Whole-driver reachable ownership remains
open; publication and genuinely final release retain their separate obligations.

## H4 continuation: ordered mixed peer attributes and their readback

One actual setPeerCmd now combines PSK, one valid Allowed-IP, an optional malformed
second entry and keepalive, followed by actual getPeerDump. Normal allocation
refusal retains the PSK and sequence increment; later malformed input retains
the PSK and inserted address; only complete success reaches keepalive. Cleanup
restores the original positive peer reference count. Exact readback includes
the result code, peer fields, JSON address masking, cursor reset and consumed room.

Premises are explicit: matching resident peer lookup, positive bounded reference
count, stopped device, empty selected root, legal prefix width, and, for readback,
empty target list and finite dump cursor/sequence/capacity conditions. There is
no allocation-record readiness, allocation-ID freshness or singleton-device
premise. Cursor aliases retain their actual overwrite effect, without asserting
global trie consistency. Stops are retained and no totality or wire-format claim
is made. MixedPeerModel/Frames/Source/Claims separate exact transforms, their
readback facts, native execution and projected composition. Four theorems bring
H4 to 81 headlines/590 theorems.

### Validation of the H1/H2/H4 continuation

All independent reviews find no correctness/domain issue. New proofs use stock
limits, with no suppressions or cap increase. H1 probes 1 and 2 fail three and
one proof-form errors (three unused-simp warnings in the first); probe 3 checks
with one unused-simp warning; probe 4 is clean. H2 held-support probes 1 and 2
fail three and two errors with twelve cascade warnings each; probe 3 is clean.
Response probes 4 and 5 fail three and four parser/cascade errors; probe 6 is
clean. Root's general lookup probe passes first time. Cookie probes 1 and 2 fail
three import/layout and two native-postcondition inference diagnostics; probe 3
is clean.

H4 probes 1–5 fail respectively: one source-reduction goal/one warning; two
diagnostic sites with nine bind-reduction goals/seventeen warnings; eight final
device goals/two warnings; record-layout parsing at two sites and a cascade;
missing Bridge import and its intro cascade. Probes 6 and 7 check the full
package and narrowed split imports cleanly. One early preview of probe 2 was
premature; its completed diagnostic output was subsequently read in full.

Integration first fails one unqualified Json.arr in the H4 terminal wrapper;
the corrected Index/Config build passes 429 jobs. Adding H1 first fails two
diagnostics from copying the scratch import/namespace shell into Statements;
extracting only its documented theorem fixes that packaging error. Final combined
Noise/Index/Config build passes 446 jobs, with only inherited Env:865 String.mk.
Support builds pass 114, 67 and 136 jobs. Axioms: 1,840 logical roots in 382
modules, including 1,286 public theorem roots, standard only. All three fresh
kernel replays pass. Static checks, original 258-name order and mirror/shared
boundaries pass. There is no infrastructure retry or unchanged failed-source
rerun. The inherited full-gate failure remains recorded and is not rerun.

Reproduce with scripts/in-bundle lake build on Leanux.Proofs.WG.{Noise,Index,Config}.Statements,
then scripts/in-bundle lake env leanchecker --fresh on each target, under capped
with 32 Lean threads and 16 QEMU slots. No mirror change is requested for this tranche.

## H2 continuation: initiation consumption and handshake publication

Actual consumeInitiation now preserves hashed-owner coherence on every normal
return from the sole projected coherence premise. The actual public-key lookup
derives its retained peer reference; misses and zero counts return normally,
while missing peers, overflow and hidden-input failures retain their Stops.
Post-lookup rejection releases only the acquired reference. Successful metadata
writes preserve owner words and counts. No public-key-table coherence, entry
reference budget or readiness premise is added.

OwnerCoherencePubkeyFrames holds the native acquisition fact;
OwnerCoherenceInitiationClaims composes the actual source through the existing
exact initiation observer and its erasure. Its literal Statements wrapper adds
the third theorem. The result remains local coherence, not reachability or
failed-call state preservation.

Actual createInitiation and createResponse also preserve coherence under an
explicit coherent-publisher premise: for a present Device, the caller's peer
is resident, positively referenced and has its own handshake owner word, even
when that owner is not yet hashed. Hashed-table coherence alone does not imply
this premise. OwnerCoherenceCreatorModel defines it, CreatorFrames proves
metadata/publication preservation, and CreatorClaims connects both actual
creators. Two literal wrappers bring this package to six theorems. No readiness,
success, cursor-bound, hash-membership or uniqueness premise is introduced.

Together these packages bring H2 to 77 headlines and 421 theorems. Global
driver propagation and caller discharge of publication/lifetime obligations
remain open. Neither package changes a shared layer or the mirror.

## H3 continuation: invalid MAC1 preserves the Device

The whole actual non-cookie receiveHandshakePacket call preserves the complete
optional Device, and thus every remote endpoint, on normal return when the
entry Device's actual MAC1 comparison fails. The predicate uses the source's
saturating message slices and has no packet-shape or type-1/type-2 premise.
Missing Device and earlier clock failures retain their stopped behavior;
Ambient and load-history changes are not claimed to roll back.

InvalidMac1Frames covers the actual load/decay prefix; InvalidMac1Source covers
both load outcomes of the actual receive body; InvalidMac1Claims is projected,
and Statements adds its literal wrapper. Four theorems bring H3 to 14 headlines
and 161 theorems. Later authentication failures, queued data callbacks and
whole-driver endpoint provenance remain open.

### Validation of the H2/H3 continuation

Independent reviews of all three packages find no correctness/domain issue.
The initiation package's probe 1 passes support only; probes 2–5 fail,
respectively, four parser/cascade diagnostics; five proof-construction errors
and two unused-simp warnings; one bind-normalization error and one warning;
two eliminated-successor-name errors. Changed probe 6 is clean. Creator probe
1 fails a projected/native Device rewrite; probe 2 is clean. Invalid-MAC1
probe 1 fails the final projected endpoint equation with one unused-simp warning;
probe 2 is clean. All final proofs use default limits without suppression.

The H3 support build passes 115 jobs; combined integration passes 348 jobs,
and the final Index/Roaming build passes 351 jobs. Only inherited Env:865
String.mk is reported. Axioms: 1,412 logical roots in 287 modules, including
918 public theorem roots, standard only and no missing roots. Both fresh kernel
replays pass. Static checks, original 258-name order and mirror/shared boundaries
pass. Current totals are 2,094 theorems, 646 owned modules and 289 headlines.
One static-check invocation mistakenly sent its Python body to the shell and
failed to parse; the corrected Python invocation passes all static checks.
No infrastructure retry, cap increase or unchanged failed-source rerun occurs.
The inherited full-gate failure remains recorded and is not rerun unchanged.

Reproduce with scripts/in-bundle lake build on
Leanux.Proofs.WG.{Index,Roaming}.Statements and scripts/in-bundle lake env
leanchecker --fresh on each target, under capped with 32 Lean threads and
16 QEMU slots. No new mirror request arises.

## H1 continuation: actual session derivation-clock provenance

The original beginSession now has a full Product observation connecting its
actual derivation clock read to the successful ordered preparation, rotation
and handshake-index publication. The entry projection is arbitrary; normal
return itself supplies the resident Device and peer. No successful allocation,
intermediate clock run, readiness or final-key-residency premise is added.

A successful receipt records the actual admission/allocation prefix, role and
chaining key, and the complete before/after clock projections. Its birthdate
is the same value used by SessionBirthEffect through RotationRun and final
index replacement. Aliased puts remain admitted and can erase the allocated
key. Normal false returns have no derivation receipt and preserve Device and
keypair counter, while retaining the prefix's actual record consumption.
The claim does not assert whole-snapshot rollback or receipts on stopped calls.
Existing observed_erase retains every original error without a new copy.

SessionClockModel holds the input, receipt and effect predicates;
SessionClockSource holds two exact source factors, prefix/derivation effects,
the native whole-run decomposition and actual Product observation path;
SessionClockClaims holds the projected claim. Statements adds a documented
literal wrapper. No standalone frame is added: the clock's Ambient type and
the existing native lift rule provide WG preservation locally. Seven theorems
bring H1 to 24 headlines and 196 theorems; campaign totals are 2,101 theorems,
649 modules and 290 headlines. Whole-driver edge ownership, wider totality and
allocation-lifetime confirmation remain open.

Independent review finds no correctness/domain issue. Development probes 1–5
fail, respectively: factor congruence and two record-layout sites with cascade;
match reduction and one unused-simp warning; bind normalization, derived-record
layout, rewritten-prefix equality and eliminated before-state names; Product/native
lift reassociation; missing receipt-constructor type annotation. Probe 6 passes
cleanly at default limits. Failed elaboration's generated recovery terms are
diagnostics, not accepted proof evidence.

The integrated Noise.Statements build passes 113 jobs without warnings.
Axioms: 477 logical roots in 89 modules, including 290 public theorem roots,
standard only with no missing roots. Fresh kernel replay passes; static checks,
original 258-name order and mirror/shared boundaries pass. No infrastructure
retry, dependency build during replay, cap increase or unchanged failed-source
rerun occurs. The inherited full-gate failure is unchanged.

Reproduce with scripts/in-bundle lake build Leanux.Proofs.WG.Noise.Statements
and scripts/in-bundle lake env leanchecker --fresh on that target, under
capped with 32 Lean threads and 16 QEMU slots. No mirror change is requested.

## H2 continuation: actual peer initialization supplies publication coherence

Actual peerCreate preserves local hashed-owner coherence on every normal return
and every successful result names a resident peer with refcount one and its
own handshake owner word. A separate projected corollary establishes exactly
the handshake creators' publisher premise. Numeric allocation/limit errors
preserve the original Device; all stopped paths retain their actual behavior.

The proof admits nextPeer collisions. It tracks the unchanged index/keypair
stores and all other peer lookups through initialization, without asserting
coherence while the replacement's handshake word is temporarily NULL. The
actual handshakeInit self-word write restores coherence. This is positivity
and owner-word coherence, not accounting for reference ownership, public-key
table uniqueness or global reachability.

OwnerCoherencePeerCreateModel holds the pure footprint; Frames holds the
internal native initialization predicate and three supporting facts; Source
proves the actual creation effect; Claims contains the two projected contracts.
Statements adds one literal headline. Seven theorems bring H2 to 78 headlines
and 428 theorems. No new mirror change or shared-layer copy is needed.

An independent removal inventory confirms that dead-marking can preserve the
existing ownerReferences projection, but it cannot discharge final release's
detachment obligation from coherence alone. Coherence does not require every
hashed keypair naming a peer to occupy one of that peer's three slots. The
existing checked peerPut counterexample already exposes this invariant gap.
General removal needs slot coverage and retained-reference accounting, or an
explicit detachment premise at release. The later whole-removal finding
below turns this inventory into a checked actual-call counterexample.

## H2 continuation: whole quiet removal exposes the lifecycle obligation

The earlier last-peerPut witness now extends to the complete original peerRemove.
Its explicit Device contains one positively referenced peer, an empty three-slot
key set, empty work/trie/packet state and a positively referenced hashed keypair
whose peer word names that peer. The entry satisfies HashedOwnersCoherent.
The theorem derives an actual normal removal and its exact final Device for
every native state and Ambient realizing that Device. The keypair row remains
hashed after the peer disappears, so final owner coherence is false.

This is a checked statement-domain finding: local coherence does not connect
hashed keypairs to peer slots or establish retained-reference accounting.
The witness does not violate the separate numeric-index uniqueness predicate,
establish reachability from initialization, or demonstrate a mirror/kernel bug.
A keypair peer word alone must not be treated as a proved held-peer reference.
No mirror-team change is requested. The next positive architecture transports
an entry detachment condition through quiet removal; a second architecture
would allow live slots under explicit coverage and prove their actual unhashing.
Neither treats post-call coherence as an assumption.

OwnerCoherenceRemovalFindingModel holds seven pure witness definitions;
OwnerCoherenceRemovalFindings holds the projected whole-call claim.
Statements adds its literal documented wrapper. There are no new native frame
files or shared variants. Two theorems bring H2 to 430 theorems and 79 headlines.

Seven changed scratch probes were used. Probes 1–6 fail respectively on concrete
source recursion; source/cleanup recursion and membership decidability;
concrete specialization recursion; repeated singleton-map normalization;
ring/NAPI guard simplification; and the initialized empty-ring fact.
Probes 1 and 2 also emitted an unused-simp warning. Probe 7 accepts both
theorems with one unused-simp warning; removing that unused argument is checked
by the installed 331-job build. No limits were raised or unchanged job retried.
Independent review finds no semantic or domain issue.

## H2 continuation: quiet removal under entry detachment

The positive counterpart of the whole-removal finding is now checked.
A resident, positively referenced peer with three empty key slots, an empty
allowed-IP list and empty send/clear work queues can be removed while preserving
hashed-owner coherence on every normal return. The device peer count is positive.
At a last reference, the entry condition requires every retained owner other
than that peer's own handshake entry to stop naming the peer. A nonlast release
needs no additional detachment. This is an explicit local lifecycle obligation,
not a theorem that reachable driver states establish it.

The proof applies the actual whole-call quiet-removal contract. It transports
coherence and detachment through unlisting, dead-marking, ordered slot/timer
cleanup and the peer-count decrement, then applies the existing exact last-
or retained-reference release law. Crypt/NAPI/packet/timer refusals remain
possible; no hidden-record or completion readiness is introduced. The earlier
counterexample violates this entry condition and remains unchanged.

OwnerCoherenceQuietRemovalModel holds LastOwnerDetached;
OwnerCoherenceQuietRemovalFrames holds four small pure transports;
OwnerCoherenceQuietRemovalClaims contains the projected claim, and Statements
its documented wrapper. No shared variant or mirror change is needed.
Six new theorems bring H2 to 436 theorems and 80 headlines; campaign totals
are 2,137 theorems, 670 modules and 297 headlines. The later live-slot theorem separately discharges entry coverage through actual
ordered unhashing; this empty-slot theorem alone does not establish it.

Six changed scratch probes were used. Probe 1 fails with one record-normalization
goal and two default-heartbeat diagnostics in final composition. Splitting a
named pure release frame and abstracting cleanup output yields probe 2's clean
pass. Probe 3 fails at outcome let-bindings, and probe 4 at a redundant dsimp.
Probe 5 passes after that removal; probe 6 checks the split package with narrowed
imports without diagnostics. No limit increase, suppression or infrastructure
rerun occurred. Source review checks the entry/final distinction and retained
refusal cases without finding an issue.

The installed Index build passes 334 jobs, with only inherited Env:865 String.mk.
The axiom audit passes 1,285 logical roots in 270 modules, including 847 public
theorems, using only the three standard axioms. Fresh Index kernel replay passes without diagnostics after dependency
artifact writers stopped. Static checks, original headline order and the
source census pass. Existing C1 layers and the executable mirror are unchanged.
The inherited full gate remains failed and is not rerun. Reproduce with the
Index.Statements scoped build and fresh leanchecker command under capped,
scripts/in-bundle, 32 Lean threads and 16 QEMU slots.

## H4 continuation: mixed port refusal and actual readback

The actual mixed setter now has a contract for a changed nonzero listen port
that collides while the device is running in its creating namespace. Supported
flags include REPLACE_PEERS; private-key and peer-attribute suffixes remain
arbitrary. On a normal return the code is -EADDRINUSE. The earlier generation
increment, fwmark write and both endpoint-source/cache clearing passes persist.
All other device fields, including port, sockets, identity and index/keypair
stores, retain their original values. Listed peers have the actual final reset
value; unlisted bindings are unchanged. Replacement and later attributes do
not execute. Duplicate or missing listed peers are not excluded: missing-peer
or hidden-reset failures remain actual Stops, with no post-Stop claim.

A second claim composes the actual following wgGetDevice. Its bounded domain
adds a singleton resident peer, no allowed IPs, enough dump room and an idle,
empty socket 7. The device may remain running; there is no peer-reference bound
or reset readiness premise. The getter returns exact mirror JSON with the new
mark and original port, identity and serialized peer fields, empties its socket
at the incremented generation, and retains the setter's real source/cache
effects. This is not a byte-level netlink encoding theorem.

PortRefusalModel holds the request and committed-prefix Device.
PortRefusalFrames contains two substantive native frames for the clearing loops
and refused bind; PortRefusalSource connects the whole original setter;
PortRefusalClaims contains the two projected contracts. Statements adds two
documented wrappers. Seven theorems bring H4 to 597 theorems and 83 headlines.
The proofs use existing campaign-owned effects without changing shared lemmas.
No mirror change is requested.

Eight changed scratch probes were used. Probe 1 fails on projection elaboration,
Boolean equality, name shadowing and a missing frame import. Probe 2 fails on
two source-factor equalities. Probe 3 accepts the source with two unused-simp
warnings, removed in the next draft. Probes 4–6 fail on getter record layout,
projection congruence and dependent equality elaboration respectively.
Probe 7 checks both claims without diagnostics; probe 8 checks the exact split
bodies and both wrappers without warnings, with seven standard-axiom outputs.
Independent review finds no issue. No readiness premise, suppression, limit
increase or infrastructure rerun was introduced.

## Validation of the quiet-removal finding and mixed port refusal

The installed combined Index/Config build passes 449 jobs, with only the
unchanged Env:865 String.mk deprecation. The new proofs are warning-free.
The combined axiom audit covers 1,833 logical roots in 385 modules, including
1,252 public theorems: only propext, Classical.choice and Quot.sound.
Fresh kernel replays of both terminal modules pass without diagnostics,
after dependency artifact writers stopped.
Static token/import/root/default-target checks, all 258 original headline
names/order, source census and diff formatting pass. The executable mirror
and existing C1 shared layers remain unchanged. The owned tree now contains
2,131 theorems in 667 modules and 296 headlines. The inherited full-gate failure
is unchanged and is not rerun; no whole charter result is declared complete.

Reproduce the scoped build and each fresh replay using Index.Statements and
Config.Statements under scripts/in-bundle, capped, LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. Scratch diagnostics are reconstructible and not committed.
The separate H3 reply/socket overlap is inventoried in the shared-frame
follow-up; neither of its two architectures has been implemented.

## H2 continuation: actual slot clearing discharges coverage

Whole peerRemove now preserves owner coherence with live or aliased key slots.
At a last peer reference, every hashed owner naming that peer must be either
its own handshake entry or a keypair in one of its three original slots.
The public condition concerns the entry Device. The actual successful clearing
prefix supplies the ClearRun certificate; it is not a caller premise.
Each immediate key put unhashes its owner even when the key retains references,
and ordered clearing removes every covered owner. No slot distinctness, static
reference budget or ClearReady premise is imposed. Missing keys and insufficient
references on repeated aliases remain actual Stops.

The theorem keeps positive peer reference/count, a resident peer, an empty
allowed-IP list and empty send/clear work queues. It follows actual unlisting,
dead-marking, key clearing, timer cleanup, the crypt/NAPI guard, count decrement
and final release. Queue/timer refusals are eliminated only from the supplied
normal whole-call run. This establishes a local conditional preservation law,
not global reachable-state coherence or removal totality.

OwnerCoherenceSlotRemovalModel holds LastOwnerCovered; Frames contains six
pure transports; Source connects the actual post-dead removal; Claims lifts
the whole call through the campaign projection. Statements adds its documented
wrapper. Nine theorems bring H2 to 445 theorems and 81 headlines. No shared
variant or mirror edit is introduced.

Six changed probes were used. Probe 1 fails with two errors and three unused-simp
warnings; probe 2 checks the three initial pure transports without diagnostics.
Probe 3 fails with five diagnostics from parsing/cascades and an unreduced crypt
refusal; probe 4 fails on an unreduced observed Except-map contradiction.
Probes 5 and 6 check the complete and reordered split packages without
diagnostics. No limit increase or unchanged retry occurred. Independent review
finds no issue in the entry coverage, actual clearing certificate or refusals.

## H3 continuation: admitted response rejection preserves endpoints

The actual whole response-kind receiver now preserves every remote endpoint
when its same-entry receipts show MAC admission and no response-consumer cut.
The entry is otherwise arbitrary. Two read-only inspections observe the actual
MAC/load prefix and response prefix from the same complete Product state;
their erasure executes the original receiver once and retains every original
normal result and Stop. Normal whole-call execution supplies both successful
prefix receipts. MAC admission excludes the cookie-reply path, so a missing
response cut identifies actual consumer rejection and the remaining suffix
performs no endpoint write.

A stronger supporting frame preserves every optional full Endpoint observation
through consumeResponse, for every normal result. Actual index lookup derives
the extra reference needed by rejection cleanup. Arbitrary owner words, owner/
peer aliases, NULL clears and zero-reference misses retain their source behavior.
No coherence, residency, self-owner, reference-budget, source-family or hidden
input readiness premise is added. The peer map itself may change; an owner-word
clear is compatible with endpoint preservation. Broader caller and callback
authentication coverage remains open.

ResponseRejectionModel contains the admission and observation predicates;
Frames contains four native frames and two private pure map helpers, including
the native held-reference predicate. Source defines the two inspections and
their all-errors erasure; Claims contains the projected whole-call result.
Statements adds one documented wrapper. Nine theorems bring H3 to 179 theorems
and 16 headlines. Existing campaign-owned exact effects suffice; the pending
six-family cookie-reply/socket layer is not copied.

Seven changed probes were used. Probes 1–4 fail on projection normalization,
source bind reduction, eliminated-variable names or source/projection bookkeeping;
probes 2 and 3 also emit one warning each. Probe 5 fails on a nonexistent Option
lemma and emits two warnings. Its axiom output includes sorryAx from failed
elaboration recovery: that run is failed and supplies no accepted proof.
Probes 6 and 7 pass the complete and split-body checks without warnings,
printing only standard axioms for all seven public roots. Independent review
finds no issue. No suppression, limit increase or infrastructure retry occurred.

## H4 continuation: private-key update and actual getter

The actual private-key-only setter/getter composition now reads back its effective
identity and exact peer expiry effect. The source comparison distinguishes the
supplied key from the stored private key; clamping may affect the final value.
The initial identity is established, the generated public key has no peer-table
collision, and the getter domain is one resident peer without allowed IPs,
enough room for the effective installed identity, and an idle empty socket.
Running state, staged packets, keypair aliases and counts remain arbitrary.

An established old identity disables the staged-send branch even when the new
key removes the identity. Actual precomputation, handshake unhash/zero, expiry
clock and current/next invalidation produce the exact final Device. The expiry
time is derived from the actual ObservedKeyPeerRun, not a supplied historical
relation; the public conclusion exposes an existential effect, not a clock
receipt. Missing clocks, NULL handshake words and missing keypairs remain Stops.
On a normal set/get sequence the setter returns zero, JSON contains the effective
clamped identity and original serialized peer fields, and the getter empties
socket 7 at the incremented generation. A null key omits identity fields through
the actual JSON convention. No byte-level encoding claim is made.

KeyReadbackModel contains two pure effects; Frames has three substantive native
socket/selector frames and one pure Device-field frame. Source derives the exact
whole-setter effect; Claims composes the actual getter; Statements adds its
documented wrapper. Socket and fixture preservation are proved from execution,
not inferred from Device equality. Seven theorems bring H4 to 604 theorems and
84 headlines. No shared lemma or mirror code is changed.

Six changed probes were used. Probe 1 fails on bind grouping and action
metavariables. Probe 2 accepts the frames with one unused-simp warning, removed
in the next draft. Probe 3 fails on dependent inversion/projection and emits
three unused-simp warnings; probe 4 fails on projection elaboration and two
unnormalized pure-frame branches. The complete diagnostic output was inspected;
a truncated preview was not treated as complete evidence. Probes 5 and 6 pass
the whole and split-body checks without diagnostics and with seven standard-axiom
outputs. Independent review finds no issue. No limit increase, suppression or
infrastructure rerun occurred.

## Validation of slot removal, response rejection and key readback

The installed Config build passes 277 jobs. Its axiom audit covers 1,028 logical
roots in 213 modules, including 698 public theorems; fresh Config replay passes
without diagnostics. The installed Index/Roaming build passes 386 jobs and
their combined axiom audit covers 1,512 roots in 322 modules, including 983 public
theorems, all standard only. Both fresh terminal kernel replays pass without diagnostics, after
dependency artifact writers stopped.
Only the unchanged Env:865 String.mk warning remains in builds; all added proofs
are warning-free. Static token/import/root/default checks, all 258 original
headline names/order, source census and diff formatting pass. The mirror and
existing C1 shared layers remain unchanged.

The campaign now has 2,162 theorems in 682 owned modules and 300 headlines.
No whole H1–H6 charter result is declared complete; the inherited full-gate
failure remains failed and is not rerun unchanged. The preceding quiet-removal
package also received independent source review with no findings. Reproduce
the scoped builds and fresh replays on Config.Statements, Index.Statements and
Roaming.Statements under capped, scripts/in-bundle, LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. No new mirror-team request arises from these increments.

## H2 continuation: arbitrary allowed-IP removal and zero-key work

The whole peerRemove coherence contract now permits arbitrary allowed-IP lists
and trie representations. The entry resident/positive peer, positive numPeers,
empty send/clear work queues and LastOwnerCovered obligations remain. A pointwise
peer observation hides only allowedipsList; index/keypair stores, embedded owner
words, references, slots and cleanup queues remain visible. Actual listDel and
removeByPeer preserve this observation even when lists contain duplicates or
nodes have malformed shape. Missing nodes, invalid bit accesses and all later
cleanup refusals remain actual Stops; no NodePairs, readiness or reference
budget premise is introduced.

OwnerCoherenceAipRemovalModel holds the two observations. Frames contains two
pure transports and the named local listDel_spec/removeByPeer_spec variants;
Source contains the peerMakeDead_spec variant. These are three bounded variants
of C1 WGBase contracts, not a copied shared layer. Claims composes the actual
whole removal and Statements adds a wrapper. Seven theorems remove the prior
empty-allowed-IP restriction; broader root/free/remove-all overlap stays pending.

The actual queuedExpiredZeroKeyMaterial worker also preserves coherence under
resident/positive peer and LastOwnerCovered, with no numPeers, queue/list
emptiness or readiness premise. Handshake zeroing retains coverage, the actual
ClearRun derives detachment, and the final peerPut uses that derived fact.
OwnerCoherenceZeroWorkerFrames holds one pure coverage transport; Claims and
Statements contain the projected whole-worker claim and wrapper. These three
theorems do not establish scheduler selection or global reachability. Dropping
coverage still leaves the existing off-slot lifecycle obligation; no new
worker-specific counterexample is claimed.

AIP development probes 1–4 fail with 16, 7, 2 and 1 diagnostics respectively;
probe 3 also has one corrected unused-simp warning. Probes 5–6 check the complete
and narrowed packages without diagnostics. Both zero-worker probes pass without
diagnostics at default limits. Independent AIP review and root zero-worker
source review find no issue. No limit increase, suppression or infrastructure
rerun occurs. H2 now has 455 theorems and 83 headlines.

## H3 continuation: admitted initiation rejection preserves endpoints

The whole initiation-kind receiver now has the corresponding rejection contract:
same-entry Product receipts show actual MAC admission and no initiation-consumer
cut, and every remote endpoint is preserved on normal whole-call return. The
source observer executes the original receiver once after its two inspections;
erasure retains every original error and normal result. Normal execution derives
both successful prefix receipts. Admission excludes cookie-reply paths, and the
no-cut suffix is pure.

The supporting full optional Endpoint-map frame follows all of consumeInitiation,
including decrypt, timestamp/replay/flood rejection and successful handshake
writes. Public-key lookup supplies the retained reference used by rejection
cleanup. No owner coherence, self-word, residency, alias, reference-budget,
source-family or clock/decrypt readiness premise is added. Ambient logging and
handshake metadata may change; endpoint preservation does not assert a complete
peer-map frame.

InitiationRejectionModel holds admission and observation predicates; Frames holds
three native contracts and one private map helper. Source contains both inspection
definitions and all-errors erasure; Claims and Statements contain the projected
whole-call claim and wrapper. Existing owned response endpoint/cleanup support
is reused; no pending cookie-reply/socket layer is copied. Seven theorems bring
H3 to 186 theorems and 17 headlines.

Probe 1 checks the consumer frames. Probe 2 fails two linked rename/map diagnostics;
probes 3–4 check the whole claim, wrapper and six public axiom roots without
warnings. The first installed split build fails because the model header opens
an unavailable Noise namespace, causing three diagnostics; removing that
unneeded open resolves the package error. No proof body, limit or premise
changes. The corrected build passes. Independent review finds no correctness
or domain issue.

## H4 continuation: repeated callbacks and separate DONE transport

Five support contracts connect a resumed allowed-IP dump that splits again,
its actual fixed-size callback, final DATA without room for DONE, the subsequent
DONE-only dump, and the receive that triggers it. Resumed capacity is the actual
44-byte overhead plus 28 bytes per IPv4 item; DONE consumes its actual 20 bytes.
The failing next item must be readable because the source reads it before the
serialization refusal. The cursor is set to the next un-emitted node; repeated
IDs may revisit the same first occurrence, so no progress theorem is claimed.

Completion spill retains DATA and the callback-running flag. DONE-only retains
the actual nonpositive errno, accepts any optional Device with a NULL peer
cursor, and runs no WireGuard callback. The receive contract derives its actual
pop and queued DONE. PaginationCallbackSource and PaginationDoneSource contain
all five facts; there is no new model, frame file or headline. General bounded
pagination still requires a capacity partition, cursor freshness, callback/
receive induction and JSON coalescing. H4 now has 609 theorems and 84 headlines.

Probe 1 fails three parser/elaboration diagnostics. Probe 2 exits zero with one
unused-simp warning and is not accepted. Probe 3 fails one exposed Except.map
normalization goal. Probes 4–7 check the whole and split packages without
diagnostics and print standard axioms for all five facts. Independent review
finds no correctness issue and catches the overstrong cursor-progress docstring;
the installed text now describes the exact cursor assignment. No limit increase,
unchanged retry or infrastructure failure occurs.

## Validation of removal, initiation rejection and pagination support

The initial AIP/pagination build passes 369 jobs. After the corrected initiation
module header, the combined build passes 418 jobs; zero-worker installation
passes 347 jobs. The only build warning is inherited Env:865 String.mk.
The combined axiom audit covers 1,640 logical roots in 356 proof modules,
including 1,064 public theorems, with standard axioms only. All four fresh kernel
replays pass without diagnostics after dependency artifact writers stop.
Static checks and all 258 original terminal names/order pass. Mirror and
existing shared-layer boundaries are unchanged.

This checkpoint adds 22 theorems and 12 modules to 9dcb9646: 2,184 theorems,
694 owned modules and 303 headlines. No whole H1–H6 result is declared complete;
the inherited full-gate failure remains failed and is not rerun unchanged.
Reproduce builds and fresh replays on Index.Statements, Roaming.Statements,
Config.PaginationCallbackSource and Config.PaginationDoneSource under
Leanux.Proofs.WG, using capped, scripts/in-bundle, 32 threads and 16 QEMU slots.
No new mirror-team request arises.

## H6 continuation: every actual timer-loop turn

The observer now covers one complete original runTimers call from an arbitrary
Product entry and jPass. It resets queuedThisCall once, uses the actual record
budget, records every executed loop turn including a terminating turn, and
executes the original timerOuterFinish. Each turn retains its iteration,
incoming control, entry/exit Product snapshots, result and same-entry selected
unit inspection. The unit choice reads the actual next non-passive record and
rescans the current wheel on that turn. Successful execution derives worker/
timer agreement; it is not a callback-readiness premise.

Selected timer receipts connect the actual prefix snapshot and immediate
callback exit. Retransmit selection preserves identity and changes attempts to
nextAttempts with no remaining logical expiry at that immediate exit. Yield
receipts thread the exact observed snapshots and control through the finite
range; done receipts retain the terminating turn and exclude the unused tail.
Absent-device calls have their actual reset and false result. Errors from
selection, callback, loop or finish remain errors under whole-call erasure;
there is no partial receipt history on failure.

OuterEpisodeModel contains eleven data/model declarations; Source contains four
observer definitions, five public source theorems and one private selection
factor. Claims holds the projected episode theorem and Statements its literal
wrapper. Eight added theorems bring H6 to 453 theorems and 53 headlines. No frame
file, shared-layer copy or type-deletion is needed. The complete Product
observations retain the existing fixture projection; executable states are never
reconstructed from snapshots.

[AGENT 2026-10-17] Use a source-specific finite-loop observer over actual
timerOuterTurn rather than copying C1's absent Logged/TimerPass closure.
Its erasure keeps the real worker interleavings, reset and finish. The episode
certificate does not separately characterize finish's queue checks, prove fuel
adequacy, assert no remaining due timer, or establish a retry-19/session-once
bound. The supplied-unit sequence remains a separate theorem awaiting a
history invariant connecting its pairs to the actual episode.

Ten changed development probes were used. Probes 1–9 fail with errors/warnings
7/5, 3/0, 7/7, 11/1, 7/2, 1/0, 2/3, 1/0 and 1/0 respectively, on run/lift
normalization, annotations, eliminated locals, Boolean branches and bind form.
Probe 10 checks the complete package with zero diagnostics and only standard
axioms on all seven public roots. Default proof limits/caps are unchanged;
no suppression, unchanged retry or infrastructure failure occurs.

Installed split build passes 317 jobs, with only inherited Env:865 String.mk.
Axiom inspection checks 1,402 logical roots in 275 modules, including 790 public
theorems, standard only. Fresh terminal kernel replay passes
without diagnostics after all artifact writers stop.
Independent source review finds no correctness issue and confirms the limits
above. Static checks, original terminal names/order and mirror/shared boundaries
remain unchanged. The campaign now has 2,192 theorems in 697 owned modules and
304 headlines, versus 2,184/694/303 at ba6f537a. All H1–H6 remain in progress;
the inherited full-gate failure is not rerun or reclassified. Reproduce build
and fresh replay on Leanux.Proofs.WG.TimerDiscipline.Statements under capped,
scripts/in-bundle, 32 Lean threads and 16 QEMU slots. No new mirror request.

## H2 continuation: the actual clear-work dispatcher

The original Env.runOneClearWorker now preserves owner coherence with a lifecycle
obligation confined to the peer it actually selects. The pure entry selector
matches passive-record stripping, the optional recorded unit, its worker-specific
unitPeers lookup, queue membership and the head fallback. A successful source
selection proves agreement and actual queue membership. Missing devices,
empty queues, unknown or unqueued identities, malformed inputs, section failures
and worker-body Stops remain possible.

ClearWorkerOwnerEntry requires local coherence and, only for that selector's
result, a resident positively referenced peer with LastOwnerCovered. It requires
neither queue-wide coverage nor completion readiness. The actual dequeue
preserves those fields; the real section wrapper then composes the checked
zero-key worker. Duplicated queues and arbitrary records are retained.

OwnerCoherenceClearWorkerModel has three pure definitions; Frames has the
dequeue and section contracts; Source has the selector, exact source factor,
private peek equation and selected-peer theorem; Claims and Statements have the
projected whole-call claim and wrapper. Seven theorems bring H2 to 462 theorems
and 84 headlines. No shared variant or mirror change is added.

Probes 1–6 fail with 6, 7, 3, 3, 3 and 2 errors. The first also reports two
failed-elaboration sorry warnings; the sixth has two unused-simp warnings.
These are failed drafts, not accepted trust evidence. A bounded continuation
corrects two reduced equality witnesses and removes the unused arguments;
probes 7–8 check the complete and split packages without diagnostics. No limit,
cap, premise or source-semantics change occurs. Root source review finds no issue.

## H4 continuation: finite receive composition and complete page coalescing

PaginationPlanModel defines canonical first/resumed capacities and positive-sized
tail partitioning, with two flatten proofs. PaginationFinalSource connects the
actual final callback without a DONE-room premise and the fitting inline-DONE
transport. PaginationReceiveSource connects pop/refill, ordinary DATA drain
steps and a finite original receive-loop induction. Its bound counts each
ordinary DATA receive plus the finishing receive, including a separate DONE.
The one-step contracts are internal composition hypotheses: the eventual public
getter must discharge them from its canonical plan. The empty allowed-IP case
still needs its real single peer DATA envelope.

PaginationCoalesceModel defines recursive continuation DATA messages and DONE;
Claims proves the actual adjacent continuation merge and finite-page result.
The merge keeps the untouched later tail, including later Stops. Coalescing
preserves every IP occurrence in order, even for empty or repeated pages.
Only the first-page endpoint-none domain is imposed; no global ID uniqueness is
needed for this JSON theorem. Actual cursor progress still needs boundary
freshness, and production of those pages by the getter remains a separate task.

Nine added theorems and seven definitions bring H4 to 618 theorems, with
84 headlines unchanged. No arbitrary-pagination headline is claimed.
The source tranche uses seven changed probes: probes 1–5 fail on termination
reduction, parser/record syntax, nil witnesses, arithmetic or array normalization;
probes 2 and 4/5 additionally expose warnings or default simplifier recursion
limits. Probes 6–7 check the complete and narrowed packages without diagnostics.
No limit is raised; finite rewrites replace the recursive simplification.
Coalescing probe 1 checks adjacent merging; probe 2 exits zero with one unused
simp warning and is not accepted; probe 3 removes it and checks both standard
axiom roots. Independent reviews find no correctness issue and retain the
first-page capacity and cursor-freshness boundaries explicitly.

## H5 continuation: actual timer-completion guards

A true normal return of the original Env.runTimers establishes exactly its
final tests: Device present, empty send/clear work lists, encryptQueue.empty,
and empty txWorkQueue. The predicate uses the ring's own empty operation;
it says nothing about all physical slots, pendingWork, wheel exhaustion,
fairness or the adequacy of the loop budget. A false return carries no guard
conclusion. No callback or readiness premise is assumed.

TimerCompletionModel holds the projected predicate. Source proves the unchanged
finish guard, Claims connects the original complete call, and Statements adds
the wrapper. Three theorems bring H5 to 296 theorems and 44 headlines.
Probe 1 fails one source-bind factoring goal; probe 2 fails two optional-step/
Boolean normalization goals and emits two warnings. Probes 3–4 check the whole
and split package without diagnostics, standard axioms only. Root source review
and independent source reviews find no issue.

## Validation of clear dispatch, pagination support and timer completion

Builds pass 318 jobs for pagination/Progress, 91 for coalescing, and 489 for
Index/H6. The latter exposes the existing owned timerOuterTurn_selected_run
source theorem publicly, unchanged, so the next actual-history bridge can reuse
it without copying its proof. This changes visibility, not the theorem count.
The only warning remains inherited Env:865 String.mk.

The combined audit covers 2,567 logical roots in 532 proof modules, including
1,626 public theorem roots, with standard axioms only. All five fresh kernel replays
pass without diagnostics after dependency artifact writers stop.
Static checks, original terminal order and mirror/shared boundaries pass.
This adds 19 theorems and 12 modules to 7118b842: 2,211 theorems in 709 owned
modules, 306 headlines. All H1–H6 remain in progress; the inherited full gate
remains failed and is not rerun unchanged. Reproduce builds/fresh replays on
Index.Statements, Progress.Statements, TimerDiscipline.Statements,
Config.PaginationReceiveSource and Config.PaginationCoalesceClaims under
Leanux.Proofs.WG, through capped and scripts/in-bundle with 32 threads and
16 QEMU slots. No new mirror request or infrastructure retry.

## H4 continuation: actual finite IPv4 pagination

The original getter now returns every allowed-IP occurrence in order for a
singleton resident peer with an arbitrary finite readable IPv4 list, subject to
the actual 4096-envelope limit. Its entry domain includes no endpoint, an idle
empty socket, header room and cursor freshness at canonical chunk boundaries.
Freshness excludes a boundary ID from the entire emitted prefix; repeated IDs
away from those boundaries remain allowed. No callback-success, receive-success,
peer-reference or global ownership premise is assumed.

The source composition executes the actual first callback, repeated callbacks,
first-occurrence cursor search, DATA receives, final inline or separate DONE,
and coalescing. The exact envelope count includes the queued predecessor DATA
and any separate DONE, allowing completion on receive 4096. Empty lists emit
the real fixed peer DATA. The result preserves the whole Device and gives the
exact final socket; arbitrary Ambient inputs retain their original behavior.
This closes single-peer IPv4 pagination, not multi-peer/IPv6/endpoint pagination,
global ownership or general setter/getter composition.

Architecture: PaginationBoundaryModel and PaginationCountModel hold the pure
boundary/capacity/count/socket definitions. PaginationCanonicalSource,
CompletionSource, StartSource, FirstSource, ChainSource and SingleSource connect
the actual operations. PaginationManyClaims and PaginationClaims expose the
projected getter; Statements adds original_finite_ipv4_pagination. The public
getterDrain_range_source is an exact source factor, avoiding expansion of the
concrete 4096 range without raising proof limits. Twenty theorems in ten modules
bring H4 to 638 theorems and 85 headlines. No shared variant or mirror edit.

Development ledger: canonical/completion probes 1–6 fail on membership tactics,
record or constructor inference, recursive count context, errno/array
normalization, and default recursive simplification; probe 2 also warns.
Probes 7–8 check the complete and exact split packages. Start transport passes
its first probe. First-page probes 1–2 fail four and one diagnostics, then
probe 3 passes. Many-page probes 1–5 fail on count/branch arithmetic, concrete
range kernel recursion, rewrite orientation, and native/projected conversion;
probe 1 also warns. Probes 6–8 pass after an exact symbolic range factor.
Single-page probes 1–2 fail three syntax/cascade errors and one redundant
tactic; probe 3 passes. Final all-list composition and axiom probes both pass.
No limit/cap increase, warning suppression or infrastructure retry occurs.
Independent reviews of the support, first page and final whole composition
find no correctness or scope issue.

## H6 continuation: retry blocks from actual episode history

An adjacent-pair contract now connects two actual consecutive outer-loop runs:
an empty-send-queue retransmit selected by the current records and wheel,
followed by the actual nonempty send-worker turn. The intermediate concrete
state is shared by both runs; projected history is never used to reconstruct
an executable state. The successful actual dispatch and worker derive their
certificate without a supplied callback-success or entry-readiness premise.

For a nonempty contiguous same-peer block of those pairs, the normal original
episode now yields initial/final peer residency, preserved internalId/refcount,
exact attempt growth by the number of pairs, pending=false and an empty send
queue. Attempts are at most MAX_TIMER_HANDSHAKES + 1 (19) at the last send exit.
Later turns and final delivery are outside that bound. The theorem does not
assert that arbitrary episode histories are paired, exclude intervening resets
outside the block, prove fuel adequacy, or establish once-per-session arming.
All errors remain those of the exact observedRunTimersEpisode erasure.

OuterAdjacentModel holds the conditional certificate; Frames contains the
substantive requireStepComplete same-concrete-state contract; Source extracts
adjacent concrete runs; Claims connects the whole episode. ActualRetryBlockModel
holds receipt pairing and the final effect; Claims takes only snapshot continuity
from OuterTimerChain and execution certificates from the actual run. Statements
adds the two literal headlines. Thirteen theorems in six modules bring H6 to
466 theorems and 55 headlines. No shared layer is copied or edited.

Adjacent-pair probes 1–5 fail with 3, 2, 15, 3 and 3 diagnostics on lift/match,
reserved identifier, projection and layout issues; probes 6–7 pass the complete
and split packages, standard axioms only. Block-count probe 1 fails one reserved
name, probe 2 two membership/nil-length goals, and probes 3–4 pass the candidate
and exact split/terminal/axiom checks. No proof-limit/cap increase, warning
suppression or infrastructure retry. Independent reviews of both packages find
no correctness or scope issue.

## Validation of finite pagination and actual retry blocks

Scoped builds pass 102 jobs for canonical completion, 355 for first-page and
adjacent support, 107 for many-page composition, and 510 for both complete
terminal closures. The only warning is inherited Env:865 String.mk.
The combined axiom audit covers 2,185 logical roots in 446 proof modules,
including 1,353 public theorem roots, using only standard axioms.
Both final fresh kernel replays pass without diagnostics after dependency
artifact writers stop. Static checks, the original 258 terminal names/order,
and mirror/shared-layer boundaries pass.

Relative to c22ebdca this adds 33 theorems, 16 modules and three headlines:
2,244 theorems in 725 campaign-owned modules, 309 headlines. Every owned module
is in the scoped checked closure; all H1–H6 remain in progress. The full gate
still fails in inherited CounterWindow.Refinement and ReplayWindow.Counterexamples;
it is neither rerun unchanged nor reclassified. Reproduce builds and fresh
replays on Leanux.Proofs.WG.Config.Statements and
Leanux.Proofs.WG.TimerDiscipline.Statements through capped and scripts/in-bundle,
with 32 Lean threads and 16 QEMU slots. No new mirror-team request.

## H1 continuation: whole-response tag ownership

The actual consumeResponse now preserves every optional peer tag on every
normal refusal. Success changes only the returned peer and derives its entry
CREATED_INITIATION tag. The captured entry is arbitrary: no coherence,
residency, readiness, reference-budget or alias premise is added. Stops retain
their original domain. This is tag preservation, not Device rollback: lookup
may still clear an owner word on a normal miss.

ResponseTagModel holds the pure tag map. Frames contains two private map facts
and two local variants of WGBase.indexLookup_spec and peerPut_spec; actual
lookup supplies the retained reference for cleanup. Source composes the real
consumer, Claims conjoins the existing successful entry edge, and Statements
adds a literal headline. Seven theorems bring H1 to 203 and 25 headlines.
The successful-transcript alternative was rejected because a none receipt
does not retain rejection effects. No shared definition or lemma is edited.

Probe 1 fails one dependent-postcondition goal and warns on one unused simp
argument; probes 2–3 check the corrected and split packages without diagnostics.
Root source review finds no correctness/domain issue. No new premise or limit
increase is used.

## H4 continuation: paginated readback after actual setters

Mixed fwmark/peer-scalar and private-key-only set/get now compose with the
finite IPv4 getter. Each proof derives the actual post-set list, node map,
selector and socket inputs from the same normal setter run. The mixed request
retains mark/scalar writes on a later malformed-peer EINVAL and its actual
cache-reset timestamp. The private-key request retains effective/clamped or
null-key serialization, actual expiry time and ordered aliased key effects;
capacity, boundary freshness and receive count use the post-install identity.

Existing setter premises remain explicit. No callback-success, hidden-clock,
reset-readiness or reference premise is added. These are normal-return
compositions, not total setters. Singleton/no-endpoint/readable-IPv4/capacity/
boundary-freshness/socket/4096-envelope conditions remain. Global ownership,
free transport and unrestricted mixed/multi-peer/IPv6 behavior stay open.

PaginationCapacityFrames holds two substantive pure transport lemmas for
prefix-size equality, not facts supplied by narrowed types. MixedPaginationClaims
and KeyPaginationClaims contain the projected compositions; Statements adds
two literal wrappers. Six theorems are added. Mixed probe 1 fails three
proof-form goals; probes 2–4 pass the corrected/axiom/narrow-import checks.
Both private-key probes pass. Independent source review finds no issue.

MultiPeerCoalesceModel/Source/Claims add two further support theorems: the
actual coalescer preserves an arbitrary finite list within one DATA envelope,
adding an empty allowed_ips field only where absent. This is not a proof that
the getter produces that envelope. Its exact step retains the continuation
errors. Root probes 1–8 fail with 1, 1, 1, 1, 4, 1, 1 and 1 diagnostics
on type inference and higher-order source conversion; probe 1 also has seven
unused-simp warnings. Probe 9 exits zero with one warning and is not accepted;
probe 10 and the exact split-package check pass without warnings, standard
axioms only. No proof limit is raised. H4 now has 646 theorems and 87 headlines.

## H6 continuation: local partial-exchange arming

A checked local fixture runs the original give-up callback with a running/live
CREATED_INITIATION peer, attempts 19, empty key slots/store and allocation
counter zero. It returns normally, leaves those session observations intact,
arms zero-key at ZERO_KEY_MATERIAL_TICKS and performs one wheel enqueue.
The public total contract fixes the complete WG projection and only disables
recorded timer arming in Ambient; all other Ambient fields, including hidden
inputs, remain arbitrary. The source gives the exact four appended decisions.

This is a local arm-without-session-creation example, not a reachable runner
history or a counterexample to a precisely scoped reachable-session invariant.
[AGENT 2026-10-17] Keep session-hook calls, guarded logical arms and physical
enqueues distinct when stating the remaining count theorem. The smaller next
architecture labels existing actual response-caller receipts by their allocation
serial and derives the all-mode arm effect. A second architecture counts
derived versus give-up events across a named-caller history, but needs additional
counter frames and still does not supply whole-runner reachability.

PartialExchangeArmModel contains the pure fixture/view, Source the native
execution, Claims the projected contract, and Statements its wrapper. Three
theorems bring H6 to 469 and 56 headlines. Root source review finds no issue.
Probes 1–2 fail three and one diagnostics, the second with four warnings;
3–4 pass. Attempted unrelated-WG generalization fails default recursion/field
goals in probes 5–6, with recovery sorry diagnostics not accepted and two
warnings in probe 6. The final claim does not make that generalization:
probes 7–8 check the complete WG projection and exact package cleanly.
No cap/proof-limit increase or suppression.

## Validation of tag ownership, setter readback and local arming

Scoped builds pass 296, 364 and 333 jobs. The only warning is inherited
Env:865 String.mk. The combined audit checks 2,330 logical roots in 487 proof
modules, including 1,458 public theorem roots, using only standard axioms.
All four fresh kernel replays pass after artifact writers stop. Static checks,
original terminal order, mirror identity and shared-layer boundaries pass.

Against 1fe20f41 this adds 18 theorems, 13 modules and four headlines:
2,262 theorems in all 738 owned modules, 313 headlines. No existing statement
is reshaped or deleted. All H1–H6 remain in progress and the inherited full gate
remains failed, without an unchanged rerun. Reproduce the scoped builds and
fresh replays on Noise.Statements, Config.Statements, TimerDiscipline.Statements
and Config.MultiPeerCoalesceClaims under Leanux.Proofs.WG, through capped and
scripts/in-bundle with 32 Lean threads and 16 QEMU slots. No infrastructure
retry or new mirror-team request.

## H1 continuation: whole-initiation tag ownership

The original consumeInitiation now preserves every optional peer tag on all
normal refusals and changes only its returned peer on success. There is no
required old tag: the source permits a restarted exchange. Both ordered clock
reads, rejection cleanup, arbitrary aliases and all original Stops remain.
No readiness, coherence, residency or reference-budget premise is added.

InitiationTagFrames supplies two narrow local pubkeyLookup/setPeer variants;
actual acquisition derives the retained reference. Source composes the existing
erased consumer and Claims projects the result. Statements adds the literal
headline. The owned ResponseTagFrames.tagMap_write helper is exposed unchanged
and reused, avoiding a duplicate pure proof; no shared file is edited.
Five added theorems in three modules bring H1 to 208 and 26 headlines.
All three capped default-limit probes pass without diagnostics, and the
installed build passes 144 jobs without warnings. Root review finds no issue.

## H6 continuation: actual session-arm events

Both full response callers now retain their original complete observations and
attach an all-mode SessionArmEvent to each reached session cut. Its serial is
the actual pre-session allocation counter plus one, preserved across the hook.
The source derives the resident live peer. A running device has the exact
peerTimerArmEffect; a false running guard preserves the entire WG projection
while still permitting Ambient caller-read/decision effects and original Stops.
Across the hook the physical enqueue counter stays equal or increases by one.

Existing ResponseSessionFacts supplies hook presence exactly when beginSession
returns true and the actual SessionEffect. Its premise is discharged internally
from each original prefix, not assumed by either headline. Incoming response
only needs its message-kind equality; both whole-call preconditions are True.
The claim is at the actual hook cut, not final caller state. It does not imply
survival of an aliased keypair, unique serials across an arbitrary mixed history,
or one physical enqueue per successful session.

SessionArmEventModel holds the event predicate. Frames proves the substantive
counter consequence of the exact arm effect. Source factors the two existing
prefixes by their original decision site and connects the actual hook; Claims
and the two literal terminal wrappers retain the original observations.
Nine added theorems and two definitions in four modules bring H6 to 478 and
58 headlines. No observer, source behavior or shared layer is changed.
Probes 1–3 fail five, three and two mechanical bind/layout/type goals;
probes 4–5 pass the complete and exact split/axiom packages without warnings.
Independent review finds no correctness or domain issue. No proof-limit,
cap or premise increase occurs.

## Validation of initiation tags and session-arm events

The helper build passes 67 jobs, initiation 144 and session events 330;
only the latter reports inherited Env:865 String.mk. The audit covers
1,572 logical roots in 323 proof modules, including 914 public theorem roots,
with standard axioms only. Both final fresh kernel replays pass after
dependency artifact writers stop. Static checks, original terminal order,
mirror identity and shared-layer boundaries pass.

Relative to 2f3e9b7f this adds 14 theorems, seven modules and three headlines:
2,291 theorems in all 753 campaign-owned modules, 316 headlines. All H1–H6
remain in progress; the inherited full gate remains failed and is not rerun
unchanged. Reproduce the scoped builds and fresh replays on
Leanux.Proofs.WG.Noise.Statements and Leanux.Proofs.WG.TimerDiscipline.Statements
through capped and scripts/in-bundle with 32 Lean threads and 16 QEMU slots.
No new mirror-team request, infrastructure retry or warning suppression.

## H3 continuation: rate-limit refusal preserves peers and endpoints

The whole original non-cookie receiver now has an actual strict-prefix
observation of load selection and cookie validation. Normal whole-call return
derives successful execution of that prefix. If its actual verdict is
ratelimited, the final optional peer map and every remote destination equal
their entry values. No load, MAC, clock, allocation, address-family or peer
residency premise is added.

Cookie-secret rotation, rate-limit state, load history and Ambient effects
remain active; whole Device equality is not claimed. The noCookie verdict
alone does not imply rejection, because the unloaded path admits it.
The bad-MAC2 reply path and queued callback provenance remain open. Exact
observer erasure retains all original failures, without claiming a returned
receipt or final state on a stopped call.

RateLimitModel holds the projected observation. RateLimitSource factors the
actual prefix and unchanged suffix and proves observer erasure. RateLimitFrames
contains three narrow local variants of C1 Framing/WGCookie's makeCookie,
ratelimiterAllow and cookieValidatePacket frames, plus actual-prefix peer-map
composition and the refusal suffix frame. Claims and the literal Statements
wrapper complete nine theorems, bringing H3 to 15 headlines and 170 theorems.
No reply/socket layer is copied.

## H5 continuation: recorded batch completion guards hold at return

Every normal original afterBatch call entered with recorded inputs has a
present Device satisfying its five queue-empty tests, zero handshake queue
counter (handshakeQueueLen) and no scheduled NAPI peer. An exact source factor retains the bounded
schedule/peek/send-worker loop, all guard failures and all delivery failures.
The final delivery operation preserves the Device, so the guard facts hold
at actual return without a separate loop-success or readiness premise.

These are precisely the source tests. PtrRing.empty observes its head slot;
it does not establish that every physical slot is free, nor a ring-count
invariant on malformed metadata. No global drain adequacy, fairness,
pendingWork, suspension, record-exhaustion or recordless-path claim is made.
The recordless early branch remains explicitly outside this theorem.

BatchDrainModel holds the exact loop/suffix actions and projected predicate;
BatchDrainFrames has one Device-only local variant of C1
Framing.deliverSent_sameKernel from Framing/EnvLeaves. BatchDrainSource proves
the original recorded factor and suffix guarantee; BatchDrainClaims and its
literal wrapper connect the whole original call. Five theorems bring H5 to
43 headlines and 293 theorems. No broader scheduler frame layer is copied.

### Validation of peer creation, rate-limit rejection and batch completion

Independent full-source reviews of all three packages find no correctness or
scope issue. Peer creation probes 1, 3, 4, 5 and 6 fail with respectively one,
four, four, two and one errors; probes 1, 4 and 5 also have one unused-simp
warning each. Probe 2 checks support and probe 7 checks the full package cleanly.
Probe 8 fails five diagnostics after import narrowing drops Campaign2.Bridge;
the explicit import correction is validated by the integrated 319-job build.

Rate-limit probes 1–3 fail respectively: peer-map projection normalization
and one unused-simp warning; a reserved binder, opaque predicate rewrite and
downstream no-goals diagnostic; an eliminated Unit variable. Probes 4–6 pass
the full candidate, reordered split bodies and standalone pure model cleanly.
The integrated Roaming.Statements build passes 120 jobs without warnings.

Batch-drain probes 1–5 fail respectively: factor/getter/do-layout issues and
three warnings; factor/getter conversion and an unavailable tactic; lift/Stop/bind
normalization and four warnings; final factor/getter conversion and one warning;
two getter pure-reduction obligations. Probe 6 is clean. The first packaging
driver fails because its wrapper already contains only the theorem. The
subsequent 266-job build checks the previous target and is not new-result
validation. Before repairing the driver, every dirty worktree is preserved,
including nonignored untracked files, under
refs/snapshots/campaign2-package-recovery-20261017T074600755913Z; branch tips
and working indexes remain unchanged. The corrected insertion and integrated
Progress.Statements build pass 270 jobs.

The Index and Progress builds report only inherited Env:865 String.mk.
Axiom checks use standard axioms only: Index 1,244 logical roots/255 modules
(824 public theorem roots); Roaming 444/90 (226); Progress 1,147/206 (702).
All three fresh kernel replays pass. Static checks, original 258-name order,
mirror/shared boundaries and the complete owned census pass.
Current totals are 2,122 theorems, 661 modules and 293 headlines. Final proofs
use default limits; no cap increase, infrastructure retry or unchanged failed
source rerun occurs. The inherited full-gate failure remains recorded.

Reproduce with scripts/in-bundle lake build on
Leanux.Proofs.WG.{Index,Roaming,Progress}.Statements, and scripts/in-bundle
lake env leanchecker --fresh on each target, under capped with 32 Lean threads
and 16 QEMU slots. No new mirror-team request arises.

## Remaining general Allowed-IP ownership dependency

Campaign 1 already has native AllowedIps/InsertionRouting contracts for original
insertion success and normal allocation refusal, using represented Patricia trees,
RoutingInvariant, NodesBelow and ResidentLists. That layer is absent here.
A second architecture based on direct node/list preservation would duplicate
the same layer, so it is inventoried rather than copied.

The eventual H4 setAllowedip bridge can reuse insert_routing_outcome,
insert_routing_success and insert_routing_refusal after their landing, retaining
target residency, address/prefix bounds and represented-input premises.
OwnersBelow bounds labels; it does not imply that every labeled peer is resident.
A stronger resident-owner claim therefore needs its own explicit invariant.
This is a proof dependency, not a mirror discrepancy or change request.

## Remaining coherent-ring progress dependency

A positive H5 activation/drain theorem now has a precise proof-layer dependency:
campaign 1's Queues/PtrRing, RingGeometry and RingSteps, available on its branch
but absent here. Their ringOf/Bounds representation relates physical cursors
and stale slots to logical live contents, and consume_preserves supplies the
tail step for arbitrary batch values. Recreating that layer here would cross
the shared-layer boundary, so no copy is made.

The proposed own wrapper would induct on the live list using those pure facts
and existing cookie source continuations. Arbitrary recorded inputs retain
actual Stops; valid stop/reschedule records give drain/yield corollaries,
without clock/allocation records for empty-table cookie misses. Logical count
zero/items empty can then be proved; the retired physical reset-to-empty
claim remains false even for coherent rings. Initial queue-length equality
is needed only to conclude handshakeQueueLen = 0. The alternative direct physical-state
induction would duplicate the same absent ring layer; it was inventoried,
not implemented. This is a proof dependency, not a mirror request or a new H5 result.

## Remaining outer timer-episode dependency

The selected-unit H6 retry sequence does not yet give a retry bound for an
entire runTimers call. The OuterEpisode observer now records every actual turn.
The actual scheduler can interleave clear, crypt and send work with timers,
finish several callbacks at the same wheel step before running send work,
rescan a changed wheel, and reset queuedThisCall only once. A supplied sequence
of timer/send pairs, each beginning with an empty send queue, therefore needs
a separate invariant identifying those pairs inside the actual event sequence.
Normal runTimers completion also does not imply that no timer remains due:
the requireNothingDue check belongs to the enclosing idle/advance path.

[AGENT 2026-10-17] Start with an exact connection to the first actual iteration,
retaining the original remaining loop and final checks. This avoids assuming
callback success and supplies a bounded basis for a later event-sequence proof.
The alternative is campaign 1's Logged/TimerPass observer, whose erasure theorem
already follows the actual timer/clear/send/crypt scheduler. Its Capture and
PrefixLoops dependencies are absent here; copying that layer is outside the
allowed few local variants. Its current receipts also need selected-wheel
information before they can connect to the retry certificates. The source-specific observer now has a checked complete turn chain, but neither
architecture establishes the complete scheduler retry bound.

The enclosing requireNothingDue also reads fixture.hiddenAhead, outside the
campaign Product projection. Comparisons from the same actual product entry
retain that input; equality of projected snapshots alone does not determine
its error classification. No execution state is reconstructed from a projection.
This is a proof obligation, not a mirror finding or change request.

## Historical checkpoint before the split

Historical checkpoint: branch `proofs/campaign-2`, worktree `.worktrees/proofs-campaign-2`,
Lean v4.35.0, mirror **`de62c9d`**. The proofs are **lagging main's
representation batch `cb2348e`**. No merge or push during this resumption.
**None of H1–H6 is complete.** The historical H5 backlog finding is complete;
the other H5 clauses and corrected-main carry remain open.

| Result | Headlines | Established scope | Remaining charter core |
| --- | ---: | --- | --- |
| H1 Noise | 22 | State/slot edges, clearing/rotation, session effects and recorded total success, total initiation creation, consecutive confirmation | Remaining whole-call edges/totality, clock provenance, allocation-lifetime confirmation |
| H2 Index | 52 | Exact index operations, all normal lookup outcomes, caller table safety, session coherence/allocation sequence | Reachable hashed uniqueness and owner/peer residency through all driver entries |
| H3 Roaming | 13 | Authenticated handshake cuts, decrypt/first-poll join, complete poll setter-attempt audit | Queue/callback authentication invariant, broader caller coverage, final endpoint |
| H4 Configuration | 79 | Leaves/flags, effective bounded readback, removal/replacement phase effects, root insertion/transfer, actual two-chunk getter and scalar set/get composition | Global ownership, queued cleanup/completion, mixed attributes, general getter pagination |
| H5 Progress | 127 | 1056 | Closed proofs current: exact runner/activation/scheduler observations and completion guards; initialized committed receipts; finite curve, allocation and pipe helpers. Actual routing, sockets, whole handshake calls, inner delivery, poll/GRO and all NAPI callers now preserve supplied-record suffixes with concrete dependencies. Every normal receive/encrypt/decrypt/transmit activation strictly consumes supplied records, as do selected send and clear dispatches. The transmit claim includes actual cryptAhead and complete disposal/payments; nonempty receive needs no empty-start premise. These measures do not assert normal return, adequate fuel, useful service or termination. Global termination waits for the confirmed environment fixes; scheduler measures and initialized useful-work composition continue. |
| H6 Timers | 50 | Seven local arm sites, recorded delays, caller hook compositions, retry bound, pending/absent-zero-key give-up, total recorded retransmit hook, initiation send, retry timer dispatch and named send worker | Complete caller coverage, scheduler episodes, session-relative counting |

**258 headlines**; latest increment: total original named send-worker dispatch
through initiation, rearm and retained reference release.
Scoped builds, axioms and fresh replay pass; independent review found no issue.
The full proof gate remains **failed in inherited campaign-1 files**.

[USER 2026-10-15] Resume before the split: factor claims over a WireGuard-only
view, separate frames, then continue. Delete frames made trivial or unstatable
by the future types; retype substantive claims. No shared-layer edits, merge or
push. This supersedes the pause at `aeece72`; the earlier index-fix merge
authority was already exercised at `de62c9d`.

[USER 2026-10-15] Shared layers remain campaign 1's. Only a few necessary named
local variants may be added; report larger overlaps before copying them.
The [six-family outer-removal request](2026-10-15-campaign-2-shared-frame-request.md)
and [follow-up inventory](2026-10-15-campaign-2-shared-frame-followup.md) remain
pending. The latter covers six H1 reinstallation families (three checked,
three unimplemented), nine additional H2 ingress families, and H4's dependence
on three already-pending removal families. These carries are deferred, not
split into batches to bypass the rule.

[USER 2026-10-14] Write mirror-team requests here and notify the user.
The [three requests](2026-10-14-campaign-2-mirror-requests.md) were notified;
the latest increments add none.

[AGENT 2026-10-15] Use a WG data projection plus separate ambient context,
with execution contracts universal over concrete realizations. Distinguish
normal-return effects, total original return and total inspection. Compose
observations through actual successors; never splice independent existential
runs. Errors have no final state. Public statements name neither `World`
nor `Kernel`.

## Claims, frames and the split boundary

Factoring checkpoint `69f988a` preserved all 153 then-existing headlines.
Paths below are relative to `Leanux/Proofs/WG/`; suffix `.lean` is implicit.
Each result's `Statements` contains public projected claims.
`Campaign2/View` is data-only; `Campaign2/Bridge` defines projection and
universal execution contracts.

| Result directory | Substantive files | Separate structural frame files |
| --- | --- | --- |
| `Noise` | `Model`, `Slots`, state/consume edges; clear, rotation, session and confirmation-sequence `Model/Effects/Source` families; `Execution`, `AccessSource`, `RestartModel`; `SessionReadyModel/Source/Claims`, `InitiationReadyModel/Source/Claims` | `KernelFrames`, `PeerFrames`, `SlotFrames`, `ClearFrames`, `RotationFrames`, `SessionFrames`, `SessionReadyFrames`, `InitiationReadyFrames`, standalone `RestartFrames` |
| `Index` | View/table/owner/allocation/release models; lookup provenance and empty-result source; lifecycle/caller operation sources; session coherence/allocation/sequence effects and sources | `IndexFieldFrames`, `OwnerFieldFrames`, `StoreFieldFrames`, `LifecycleFrames`, `NewlinkFrames`, `SendFrames`, `DispatchFrames`, `ResponseFrames`, `ConsumeFrames`, `StagedFrames`, `ReceiveFrames`, `ClearFrames`, `TimerFrames`, `FlushFrames`, `SessionCoherenceFrames`, `SessionAllocationFrames` |
| `Roaming` | Endpoint/authentication claims; publication, poll endpoint/attempt, response, initiation and handshake-audit model/source/claim families | `Frames`, `PublicationFrames`, `PollEndpointFrames` |
| `Config` | `ClaimView`, models/effects/source claims, observation bridge; allowed-IP removal/insertion/transfer, collision, removal flags, remove-all/replacement, multipart/suffix readback families; `SocketReadbackModel/Claims` and five substantive `SocketReadback*Source` files; `ScalarSocketReadbackClaims/Source` compose original set/get | `ConcreteFrames`, `OperationFrames`, `ReadbackFrames`, `AllowedListFrames`, `AllowedRootFrames`, `AllowedRemovalFrames`, `AllowedPairsFrames`, `QuietFrames`, `LiveRemovalFrames`, `KeyFieldFrames`, `CollisionFrames`, `AllowedInsertFrames`, `RemoveAllFrames` |
| `Progress` | Model/view/source/observation claims; control/scheduler sources; cut, flush-queue, pow, drain and poll-bound model/source/effect/claim families; `RunnerBoundaryModel/Claims`, `IndexProgressModel/Claims` and `JitterProgressModel/Claims` are projected; their `Source` files, `RunnerBoundaryAuditSource` and `BacklogSource` connect original operations; `CookieActivationModel/Source/Loop/Claims`, `CookieSchedulerSource` and `CookieScheduleModel/Source/Claims` | `StackFrames`, `CutFrames`, `FlushQueueFrames`, `CookieActivationFrames`, `CookieScheduleFrames` |
| `TimerDiscipline` | Model/view/send-view/observation claims; recorded, send/retry/rearm/sequence/boundary, pending-give-up, session, data and traversal model/source/effect/claim families; `AbsentGiveUpModel/Claims` and substantive `AbsentGiveUpSource`; `RetransmitReadyModel/Source/Claims`, `SendReadyModel/Source/Claims`, `RetryReadyModel/Source`, `FireReadyModel/Source/Claims`, `WorkerReadyModel/Source/Claims` | `SourceFrames`, `RecordedFrames`, `RecordedJitterFrames`, `SectionFrames`, `SelectionFrames`, `RetryFrames`, `JitterFrames`, `InitiationFrames`, `InitiationPreservationFrames`, `SendCutFrames`, `SendPeerFrames`, `SendSocketFrames`, `SendBufferFrame`, `SendWorkerFrame`, `SendDispatchFrames`, `RetryDispatchFrames`, `RetryRearmFrames`, `WorkStateFrames`, `ResponseSessionFrames`, `SendReadyFrames`, `FireReadyFrames` |

`Index/HandshakeFrames` and `OwnerFrames` are import-only reexports.
`Noise/Basic` reexports access contracts; `Roaming/Basic` reexports endpoint
source. Standalone `Noise/RestartFrames` is outside the headline import closure.
`Progress/ControlLaws` is generic control, not a structural frame layer.

Delete only preservation made trivial by the split. Compound effects that
also establish outputs—generation/deadness, ordered release, cleared-peer
accumulation, dump/UDP payloads—remain substantive. In particular, H4's
arbitrary-kernel-predicate dump/UDP helpers retain output obligations, and H6's
reference decrement belongs in `SendWorkerSource`, separate from preservation.
Source factors are proved equal to original operations; they are not substitutes
for the mirror.

## H1 — Noise session state machine

Checked state edges allow initiation creation/consumption to restart from any
prior state: the machine is not a single linear handshake. Optional next/current/
previous slots do not bound the entire retained key store to three. Initiator
rotation with an existing next key demotes next and puts old current; without
next it demotes current. Responder installation goes to next.

Exact clear/rotation/confirmation effects retain ordered writes, releases,
unhashing and erasure. Normal effects derive evidence from the actual call;
total contracts additionally use static `ClearReady`, counting repeated
releases. Aliases are allowed. An old next/current alias with one reference can
leave a slot naming an erased key; this is an arbitrary-state invariant boundary,
not an accepted-run finding.

Complete normal `beginSession` effects cover allocation, KDF fields,
role/remote index, handshake zeroing, rotation and hashed replacement.
False returns preserve device and allocation cursor, though records may be
consumed. Total success now follows from accepted/live handshake state,
non-null stored peer word, hashed handshake entry, static `SessionReady`, and
an armed successful 40-byte allocation record followed by an 8-byte birthdate
record. Readiness is calculated after the allocator's actual insertion, so it
accounts for overwriting an aliased key's reference count with one. The same
successful original run yields the existing ordered `SessionEffect`; no
execution witness is assumed. Allocation-ID aliases remain allowed, including
ones that erase the new key during rotation. Neither self-owner equality nor
referenced-peer residency is assumed: this mirror's dereference checks only
the non-null word. These facts do not establish final key coherence or
reachability. Birthdate remains existential; exact decoded-clock and final
record-suffix claims, other input outcomes and broader call totality were open
at this checkpoint. The later original_begin_session_clock proves actual
birthdate provenance through rotation/publication without readiness; it does
not assert receipts on stopped calls or general totality.

The full original `createInitiation` now succeeds under resident-peer/identity,
non-null stored-word and pure crypto guards, with a 32-byte ephemeral record,
16-byte timestamp and any finite collision prefix followed by a fresh index draw.
Collision tests apply after removing this handshake owner's old rows. The result
fixes the returned message, all ordered peer/index writes and exact unused record
suffix; a separate frame preserves the timer-record mode on that same run.
No prior handshake-state, liveness, reference-count, table-uniqueness, self-owner
or referenced-peer-residency premise is required. Crypto guards are named value
predicates; no successful execution is assumed. This does not assert a fixed
message length for arbitrary identity fields, send/rearm behavior or reachability.

For consecutive actual `receivedWithKeypair` calls, the first ID matching
initial next is the sole true result, with the exact confirmation effect;
no match leaves the device unchanged. Duplicates are allowed. Total completion
adds the previous-key release budget only if a match occurs. This is not
confirmation once per allocation lifetime.

[AGENT 2026-10-15] A begin/confirm-only sequence cannot model repeated
installation after successful begin zeroes the handshake tag. A genuine mixed
history needs actual consume/create operations. Three checked restart variants
preserve the relevant cursor/next predicate; release/consumer/creator transport
would complete six shared families and awaits the reported scope decision.
Later whole-call tag maps and finite mixed tag histories cover all seven
native tag owners. The later nine-operation fresh-confirmation history now
also proves the initial-next-below-cursor result for the tracked peer, including
actual create/consume calls. The owned-source audit removes the general
failed-consumer release obstacle. Broader driver/recreation/reset histories,
reachable slot/key coherence and lifetime closure remain separate.

## H2 — Session index uniqueness

[AGENT 2026-10-15] “Live” means simultaneously hashed receiving-index owners
within one device. Unhashed retained objects do not reserve their stale number:
C unhashes before release (`noise.c:131–139`, `peerlookup.c:192–197`) and
insertion tests hashed entries (`peerlookup.c:119–163`). Remote indices occupy
a separate peer-supplied namespace. Numeric uniqueness, owner uniqueness and
owner/peer-word residency are distinct obligations.

Lookup stops at the first equal index even if its kind is disallowed.
Every normal successful lookup derives that permitted row, its resident owner
and referenced peer, positive bounded reference acquisition, and the exact
ordered acquisition/store effect. Every normal empty result has exactly one
cause: absent/disallowed first row; resident owner with NULL word; or resident
referenced peer with zero references. The first leaves the device unchanged;
the others retain the exact NULL store, including same-value insertion.
Missing owners, dangling peers and overflow are errors, not empty results.
No table uniqueness, owner=peer identity or deadness premise is smuggled in.

Removal, keypair-specialized removal (`indexRemove (.keypair id)`), replacement,
insertion and release have exact contracts. Replacement preserves numeric
uniqueness; owner uniqueness additionally needs a fresh destination owner.
Insertion removes the previous owner row before installing a fresh number.
Recorded collision/retry/exhaustion contracts retain their contiguous-record
premises; the two-call corpus-draw instance is not general runner coverage.
H5 now also proves exact insertion outcomes and budget adequacy for arbitrary
finite supplied records, including passive and malformed records.

`TablesSafe` combines numeric/owner uniqueness and the hashed-owner allocation
bound. Normal preservation covers lifecycle, send/consume/receive iterations,
clear/timer/drain and post-death removal paths. Session publication coherence
additionally requires a self handshake peer word and exclusion of the allocated
ID from actual rotation releases. True return then leaves a resident one-reference
key in the selected slot, uniquely published at the old handshake index.

Original consecutive `beginSession` calls preserve an initially bounded key
store and derive fresh consecutive allocation IDs for true returns. Cursor
advance equals their count; caller residency comes from actual normal reads.
Rotation aliases may still erase the new key. There is no retained-key lifetime
or completion claim.

The historical pre-split inventory estimated six outer-removal and nine
ingress families, plus a larger decrypt/NAPI layer. That is not the current
blocker count: after the split, owned single-peer removal and consumeData table
contracts are checked. packetReceive/wgReceive retain four deferred header/CPU
families; peerRemoveAll, decrypt/NAPI and environment closure remain broader
dependencies, detailed in the shared-frame follow-up. Most shared contracts
omit the observation rather than being false. Full reference lifetimes,
broader record layouts and whole-runner witnesses remain supporting extensions,
not separate primitive H2 targets.

## H3 — Endpoint roaming

[AGENT 2026-10-14] Roaming concerns remote family/address/port/IPv6 scope.
Local source caches legitimately change; endpoint equality ignores flowinfo
(`n1_flowinfo_only.json`). Authentication needs actual consume/AEAD evidence,
not MAC admission or a CRYPTED label alone. The outer source is not an AEAD
input; roaming precedes later inner-packet checks and does not imply delivery.

Decrypt publication retains actual plaintext/key provenance before callbacks.
The first-poll join uses the same execution and matching packet identity,
plus the actual true counter-check result. It does not establish a general
queue invariant, replay-window correctness or packet-peer/key-owner equality.

Both original handshake callers have exact pre-setter cuts. Response facts
derive MAC admission, owner/reference lookup, DH checks, derived AEAD key/AAD,
empty plaintext and consumer commit. Initiation facts derive both AEAD results,
public-key lookup/acquisition, precomputed DH, timestamp `memcmp`, wrapped signed
flood comparison and commit. Separate inspections retain these certificates
through setter or later failure; their original outcome is exact. A cut records
an attempted setter, not completed mutation or an error's final state.

The whole original poll now audits every attempted iteration at its designated
`consumeDataDone` setter site. Records retain actual entry/prefix/continuation
outcomes, including failures; subsequent iterations use actual successors.
Each reached cut derives a resident packet with packet.peer equal to the selected peer ID, CRYPTED status, true counter
result and supported source endpoint. Source equality, audit head equations and
recursion establish retention beyond mere final-outcome equality.
Arbitrary callback writes are outside this site's classification. Persistent
AEAD provenance through queues/callbacks, other callers and final endpoint
preservation remain open.

## H4 — Configuration semantics

[AGENT 2026-10-15] Linux 6.12.110 has no per-allowed-IP removal flag:
UAPI `wireguard.h:188–194`, `netlink.c:329–355`, and
[W1/W2 §2.1](2026-10-06-w1-w2-netlink.md). The obligations use peer REMOVE_ME/
REPLACE_ALLOWEDIPS and device REPLACE_PEERS. This is a statement/version
correction, not a mirror omission.

[AGENT 2026-10-14] Readback means effective clamped/masked/allocated values,
not raw input. Set is nontransactional. Leaves cover validation, no-ops,
removal precedence, identity/cookie keys, peer scalars and expiry. Bounded public
scalar readback uses one resident stopped-device peer, bounded positive reference,
matching selector/key, no allowed IPs, sufficient room and idle socket 7.
168 bytes suffice for the peer fixed part; the outer getter also needs envelope room.

Port contracts distinguish unchanged/nonzero/zero allocation and failure.
Recorded draws remain premises; an occupied first candidate is an outside-domain
stop, not proved retry. Source/cache clearing can precede bind failure; equal
outer requests still increment generation. Fwmark preserves remote destinations.
Private-key effects retain clamping, precomputation, expiry and staged sending;
aggregate timestamps remain existential.
[AGENT 2026-10-15] Collision composition starts after optional self-peer removal:
its flush may change survivors under the old identity. Normal collision effects
use actual acquisition, caller put, removal and installation over that baseline.

Allowed-IP removal has witness-based total contracts and normal converses under
initial peer residency and `NodePairs` (two child slots per resident node).
This is representation shape, not topology, ownership or acyclicity.
Live-key removal retains aliases/multiplicity and reference-count effects.
Full REMOVE_ME derives acquisition, removal and caller release under positive
counts, shape and empty send/clear queues; final erasure occurs exactly when
the original peer reference count was one. Later peer attributes are bypassed,
while invalid flags/protocol are rejected first. The singleton device wrapper
retains selection and generation. Normal REPLACE_ALLOWEDIPS derives its witness,
empties the selected peer's allowed-IP list and balances the lookup reference;
these converses do not promise queued-work completion.

Original remove-all frees allowed IPs, captures the actual post-free peer list,
marks all selected peers dead, then cleans up that same list. Shape and listed
residency at the post-free cut yield first-pass residency/deadness even with
duplicates. Flag-only REPLACE_PEERS composes selection/generation and guarantees
a cut on normal selected-device return. Cleanup stays opaque. Initial-to-post-free
transport uses three already-pending shared families; no renamed copies were added.

Empty-root insertion preserves exact allocation failure/success and sequence
effects; paired actual dumps serialize the masked prefix or omit allowed IPs
after -ENOMEM. Exact root-leaf transfer permits duplicate lists/same-peer
reassignment, retains ordered owner/filter/append writes, and totally reads back
donor/destination with explicit room/cursor premises. These are peer-serialization
claims, not global ownership or full socket getters. One named
`hiddenAlloc_sameKernel_node_spec_variant` avoids importing the inherited
counter failure; the shared original is unchanged.

Two actual peer-getter calls now cover `a :: b :: tail` with only `a ≠ b`,
resident width-32 nodes and no endpoint. First room 168 emits a and splits at b.
The actual returned context feeds room at least `44 + 28 * (1 + tail.length)`,
emitting the whole suffix, clearing allowed-IP cursor/sequence and consuming exact
room. Later repeated IDs are allowed. Original coalescing uses actual fragments;
device remains unchanged. Header, flags, DONE and capacities are supplied.
The complete original socket getter additionally covers one resident peer with
no endpoint and a finite IPv4 list split into a nonempty fitting prefix and a
remaining suffix. Capacity inequalities force two actual chunks of capacity
3776 and leave room for DONE. The continuation ID is absent from the first
prefix; other duplicates remain allowed. Original start creates the first DATA;
the first receive invokes the resumed callback and queues DATA plus DONE; the
second receive and original drain/coalescer return the entire ordered list,
checking repeated device metadata. The device is unchanged, and the socket ends
idle/empty with cleared cursors, zero dump errno and current generation.
The original scalar setter now composes with that two-chunk getter on the same
actual successor. For a stopped device and a positive bounded lookup reference,
the result reads the new preshared key/keepalive interval and unchanged full
IPv4 list. A malformed second peer returns `EINVAL` without undoing the first
update, and the same readback succeeds. Device generation increases once;
the final socket is empty/idle at that generation. Existing selector/socket
frames suffice; no new structural frame was added. Multi-peer/general
pagination, concurrent updates, other setter compositions and reachability are
not established. Global ownership, mixed attributes, final queued cleanup and
total collision completion remain open.

## H5 — Termination and progress

The historical constructed backlog witness refuted no-pending-at-completion
over de62c9d. The current runner and the boundary audit both reject that trace
at the batch-completion guard, as the checked carry report records. The old
acceptance and backlog statements were corrected explicitly during the retrofit;
no accepted final backlog boundary is claimed over b700659. This was a
constructed fixture, not a parsed or captured Linux run.

Every accepted original trace now supplies exactly one ordered projected boundary
per operation, with consecutive indices and identical output JSON. Each boundary
has absent/empty hidden records, no suspended activation and no pending NET_RX
signal, after original ambient stripping and guards. This covers file/network
operations and negative syscall returns. Exact source/audit erasure includes
prefill, descriptor/result bookkeeping, output formatting and final placement/
steering checks, including errors. Boundary lists are returned only on successful
whole-trace completion; later errors discard them. There is no pending-work,
worker-queue or scheduled-NAPI emptiness conclusion. Total inspection never
implies successful dispatch or drain.

Source-connected scheduler claims retain actual dispatch/resumption, caller
busy/idle/error and NAPI branches. Cut budgets are derived before ambient
stripping and include the final empty/non-cut observation; allocation rejection
keeps the original error. Send/clear flush removes one queue occurrence,
allows duplicates and retains final reference release/deletion.

The exact 4096-turn drain audit includes original outcomes. Below 4096 queued
items, actual selection/flush effects bound turns begun by count+one and exclude
only its own exhaustion. Worker/selector errors remain possible. Normal full
drain under resident-device/count premises empties both queues; requested-clear
may leave other work. Exactly 4096 removals leave no extra empty-observation
turn: a boundary, not an accepted finding.

Finite modular-power adequacy uses fuel `e + 1` and a checked fixed-point
equation. Original exponent zero returns 1 even modulo 1; unrestricted equality
with stock `Nat.powMod` would be a statement artefact. Poll audit under requested
budget at most MAX_QUEUED_PACKETS+1 excludes its finish-time exhaustion on normal
prefix return: each continued iteration increments count despite arbitrary
callbacks. Queue-test stop can mean an uncrypted head. Unsupported repoll remains.
Neither local result proves callback/internal work termination. General whole-worker
record decrease, detached-activation progress and global progress remain open.

For arbitrary finite supplied records and a resident device, original index
insertion now agrees with a terminating record resolver after unhashing this
owner's old rows. Each collision consumes a strictly shorter suffix, so the
original record-derived budget suffices. Outcomes are exactly an original
hidden-input error or the first fresh index with the exact inserted device
table and unused suffix. The second bucket walk cannot find a stolen index.
Passive records are skipped without payload validation, as in the original
read; wrong-site, malformed and missing input retain their original errors.
No table uniqueness or owner residency is assumed. Recordless placeholder/
domain-filter execution and global scheduler progress remain outside this claim.

Both original timer jitter sites now have the analogous total contract for any
finite supplied record list. Each successful draw consumes a strict suffix,
including skipped passive records; rejected draws recurse on that suffix.
The original length-plus-one budget therefore reaches either the first accepted
jitter below `HZ / 3` or the exact original missing/malformed/wrong-site error.
Success preserves the entire projected state except the unused record suffix.
No device-residency premise is needed. Recordless execution, distribution,
arming and scheduler progress are separate claims.


The historical cookie-activation contracts assumed that list/count occupancy
alone described the physical ring. That domain was insufficient. The split
retrofit retires five false count/totality supports and checks concrete
malformed-ring counterexamples in CookieActivationBoundFindings and
CookieItemsFindings. Those witnesses are arbitrary-state refutations, not
initialized accepted executions.

The current original_cookie_activation_outcome gives exact agreement with
cookieHybridRun under the original cookie-only/empty-index premises. It
retains receive, record and occupancy-exhaustion errors; it does not prove
successful drain, strict record decrease or count adequacy on arbitrary ring
metadata. Cookie classification remains an entry premise, not ingress
validation.

The current original_cookie_scheduled_resumption_progress selects the control
branch from pure resolver success, then retains the actual probe, detached
bounded rerun and all their errors. Resolver success is not an execution
success witness and does not imply a drain or a strict suffix. The two
CookieActivationFrames projection equations remain frames; the other files
express operational outcomes.

The current original_cookie_schedule_outcome retains its explicit record
shape and count premises but concludes agreement with the bounded first turn
and actual remainder, including the scheduler's budget guard. It does not
promise successful completion, empty physical queues or the historical
list-based final projection. Positive represented-ring adequacy and initialized
queue/pending-work consistency require the inventoried shared support.

## H6 — Timer discipline

Local contracts cover all seven concrete arm sites, actual clock-plus-delay
wrapping and jitter below 83. H6's finite draw certificates require contiguous
draws; H5 additionally proves arbitrary supplied-record jitter outcomes and
budget adequacy. General arm-record mode can permit placeholders.
There is no distribution claim. The applicable running/live/interval guards qualify each arm;
a final timer value alone does not prove an arm event.

The supplied caller/jitter/arm domain now gives exact Product agreement with
the retransmit hook's actual continuation (original_retransmit_hook_ready).
It retains caller and jitter reads, running/live guards, and timer-clock or
wheel-record refusals. Normal enabled arming has the documented wrapped delay
and full WG wheel/registration effect; an inactive guard follows the actual
skipped path. The supplied domain does not guarantee completion.

The supplied creation/send-tail domain gives exact Product agreement through
actual initiation, send and rearm (original_send_initiation_ready). Existing
creation, cookie, interval, endpoint and allocation conditions remain explicit.
The caller ignores the no-endpoint address-family return, but subsequent arm
refusals remain Stops. No unconditional completion, packet delivery or whole
retry-history claim follows.

The supplied ready domain does prove successful execution of the actual
selected retransmit wheel unit (original_fire_retry_ready). Due/horizon,
identity, records, reference and queue conditions remain explicit. Its full
Product effect includes wheel detachment, pass-step reset, pending-work
filtering and queuedThisCall preservation. This is timerDispatchUnit_variant,
not outer selection or completion of runTimers; the later first-turn and
whole-episode contracts address those original control paths separately.

The named-worker domain gives exact Product agreement through selection,
dequeue, creation, arm, release and section stop (original_send_worker_ready).
Dequeue erases one selected occurrence and derives pending from residual
queue membership: a duplicate may leave it true (original_send_dispatch_path).
Arm, release and section failures stay visible. The theorem does not promise
unconditional worker completion, packet transmission or queue exhaustion.

From a resident device and initially empty send queue, normal selected
timer/send pairs derive same-peer selection, entry attempts at most 18,
enqueue/reference acquisition, detach, increment and worker release.
Consecutive successful same-peer pairs from zero number at most 19. This
excludes 20 such pairs, not a twentieth callback. The immediate original
callback after 19 has exact all-outcome give-up behavior; normal return
preserves identity/count and empty queue. Later episode observers also derive
actual adjacent-pair certificates and qualifying contiguous-block counts;
they do not prove every arbitrary history decomposes into those blocks.

Above the limit with zero-key already pending, give-up is total: retain its
expiry, delete send-keepalive expiry and wheel entry, purge staged packets, add their length to dropped,
and append exact true-give-up/false-zero-key-absent decisions. Hidden records,
clocks, attempts and device queues stay unchanged. No running/live/record-mode
premise is needed.

With zero-key absent, the supplied-record domain gives exact Product agreement
with the actual post-give-up arm continuation (original_giveup_absent_zero_key).
Timer-clock and wheel-record refusals remain possible. A normal enabled arm
retains the original zero-key delay and complete WG timer effects. These
conditions establish neither scheduler selection nor a session history.

Both response callers observe actual session results; the session-derived hook
is reached exactly on true. Traversal compositions cover outgoing initiation,
outgoing response, common initiation/response receive tails, data completion and
data receipt in their stated contexts. Data completion traverses once per
encrypted item/list before its per-packet send loop (`Data.lean:181–194`,
C `send.c:242–260`), not per packet/transmission. Successful nonkeepalive sends
control data-sent; nonzero received length controls data-received. Guarded
recorded wheel effects are established at actual hook cuts. Current observer
erasures preserve original failures; cut facts do not promise final expiry or
delivery. Common response traversal does not require session success.

Zero-key firing queues clearing; it does not immediately erase keys. Give-up
can arm it without session creation, as shown by the local checked finding and
separate initialized runner replay in their stated scopes. Actual session
events tie their hook to beginSession success and the allocation serial, with
zero or one physical enqueue under the guard. Whole timer episodes, actual
adjacent retry certificates and qualifying contiguous same-peer block counts
are now checked. Universal history decomposition and cross-call session-relative
counts remain open. The give-up finding rejects attributing every zero-key arm
to session creation; it does not settle every interpretation of at-most-one
arm per completed session. No mirror discrepancy is established.

## Findings and mirror requests

The [request document](2026-10-14-campaign-2-mirror-requests.md) ranks all three
changes as altitude-preserving. No mirror/kernel edit or upstream report occurred.

| Finding | Evidence and limit | Status |
| --- | --- | --- |
| H5 batch backlog | Kernel-checked accepted constructed fixture and backlog, with symbolic proof locating it at the actual final runner boundary; not parsed/captured Linux | Historical over de62c9d. Main `9db558b` adds completion guard; actual runner/audit refusal carry checks over b700659 |
| H5 nested refill | Evaluated initialized prefix/source review; operation 4 reaches worker occupancy-budget invariant; later suffix incomplete | Neither accepted complete trace nor kernel-proved prefix; callback-aware bound requested |
| H4 dump cancellation | Accepted getter, kernel-checked internal room 3720 versus source-derived C 3724 | Restore pre-nest snapshot; no demonstrated compared-output mismatch. Dead-cursor extension only inspected |

Alias examples, statement qualifications and the 4096 boundary are not
accepted-run findings. H1/H2/H3/H6 have no ranked mirror-change request.

## Validation and trust limitations

The historical pre-split six-target checkpoint passed **482 jobs**. All **258 headlines** and eight new
worker-ready supports use only the three standard axioms; token/import/root/default/
projected-name checks pass. Independent read-only review found no issues. Fresh
TimerDiscipline replay passed. New tracked/untracked whitespace checks passed
before the final build. Author Source/Statements builds passed 170/264 jobs.

Retained-put/handshake-worker prototype: three capped stdin compilations, two
passes and one corrected Boolean-guard failure. Dispatcher prototype: seven
compilations, two passes and five corrected failures, including wrong draft
section constants corrected to the original named sites. One failed draft's
diagnostics and compressed copy were truncated by an insufficient tool-output
budget and lost. That unchanged source was not rerun for diagnostics; subsequent
outputs were fully captured. Both packaging builds passed, with stock limits,
unchanged memory cap and no infrastructure or unchanged-source diagnostic rerun.

The preceding timer-dispatch checkpoint `403fa0d` passed 479 build jobs, all
257 headlines and 12 supports on standard axioms, fresh TimerDiscipline replay
and independent review. Its callback/scaffold/specialization and corrected
packaging failures are counted in that commit.

The preceding initiation-send checkpoint `b90f9bb` passed 473 build jobs, all
256 headlines and 11 supports on standard axioms, fresh TimerDiscipline replay
and independent review. Its prototype and packaging counts are in that commit.

The preceding cookie-schedule checkpoint `8055612` passed 469 build jobs, all
255 headlines, 15 new and four existing supports on standard axioms, fresh
Progress replay and independent review. Its seven prototype calls had three
passes and four corrected failures; all three packaging builds passed.

The preceding initiation checkpoint `5ee787c` passed 465 build jobs, all 254
headlines and 29 new supports on standard axioms, fresh Noise replay and review.
Its source uses an 800000-heartbeat budget unchanged throughout the retained
continuation; earliest prototype budget provenance is unconfirmed, as recorded
in that commit. Memory cap was unchanged.

The preceding H5/H6 checkpoint `daa1b10` passed 461 build jobs, all 253 headlines
and 41 supports on standard axioms, both fresh replays and independent reviews.
Its compiler counts and corrected drafts are in that commit. The diagnostic
rerun violation below remains explicitly recorded; it was not infrastructure.
The earlier socket-getter review found a headline attribution error, corrected:
the callback returns DATA; the enclosing socket dump appends DONE and finalizes.
Earlier closed increments also passed
affected scoped builds, axiom checks and fresh replay; counts, corrected draft
failures and review dispositions are in their commits. Reviews did not rerun
reported validation. All review findings were fixed, including unconditional
source correspondence, explicit supplied dump envelopes and cursor-reset scope.
Standalone H1 restart support separately passed 116 jobs, seven declarations
and fresh replay; it adds no headline.

The pre-split full gate at **`69f988a` failed** in inherited
`WG/CounterWindow/Refinement.lean` and `WG/ReplayWindow/Counterexamples.lean`
(counter operands/index-owner carries). Campaign 1 owns repair. The later split-gate failure and its
diagnostics are recorded in the current checkpoint and retrofit report.
Scoped passes are not a full-gate pass; existing shared lemmas were not edited.

**Two infrastructure failures, one rerun each:** `84355d1` import overlapped
rebuild and missed ReceiveFrames.olean; `9019ca8` repeated that orchestration
mistake while Config Statements rebuilt, missing its object. Each sole rerun
after confirmed build completion passed. Build and dependent import/axiom
checks are now sequential, including docstring changes.

The absent-zero-key increment also repeated a successful Lean axiom invocation
after its output parser failed. A second invocation failed on an unsupported
printing option; the third repeated the first input and passed. This was
redundant checking, not an infrastructure retry. [AGENT 2026-10-15] Root now
owns central axiom-output checks; parser repairs reuse captured output instead
of repeating successful Lean invocations.

**Separate cookie-loop diagnostic rerun violation:** after a failed scoped
`CookieActivationLoop` build, the author reran unchanged source through
`lake env lean -Dpp.structureInstances=false -Dpp.proofs=false` to read goals
truncated from the first output. Both exited 1; this was not infrastructure and
was not an allowed retry. Source corrections to monad/case reduction and loop
composition then passed. Diagnostic output must be retained and read from the
original invocation; changing printing options does not authorize a rerun.

**Separate process violation at `314d13e`:** an unconditional dependent build
repeated an unchanged failed REPLACE_PEERS source draft. This was not
infrastructure or a permitted retry. Launch control was corrected; neither
failure was accepted. There have been no cap hits/increases, guests or guest
timeouts. Ordinary corrected elaboration failures remain failures, documented
in commits. Earlier deterministic-limit accounting is in those commits; the
initiation investigation has the budget-history uncertainty stated above.

One bounded trial kernel-checked original curve25519 through the finite power
bridge (about 0.334 s). A separate single full QueueRefill reduction trial failed
at stock simplifier-step exhaustion with exit 1; its recovery printed sorryAx.
No theorem was obtained/committed, no retry or limit increase occurred.
The small bridge proves neither full-prefix throughput nor trace acceptance.

A separate sessionless H6 episode prototype evaluated the initial send and one
retry, but its full kernel-reduction proof failed with an application type
mismatch; recovery reported `sorryAx`. No theorem or mirror finding was accepted,
and the full attempt was not repeated or given larger limits. Seven stdin
trials comprised two successful stage evaluations, three elaboration failures,
one corrected missing-record failure and that failed full proof. This leaves
the twenty-initiation scheduler episode and mixed-history arm count open.

Stock `repeatM` has `implemented_by repeatM.erased`; stock `Nat.powMod`
has an external implementation annotation. Proofs use logical definitions,
checked equations and induction, not executable overrides as oracles.
No project axiom or forbidden trusted declaration was added.

The H5 runner increment used 16 implementation builds, with nine corrected
failed drafts (source/prefill normalization, case-rewritten equalities, range
normalization, explicit witnesses and initial-state reduction). A sub-agent
usage-limit interruption left the tree preserved at snapshot `ab0c13c`; root
completed the bridge and projected claims. No build was active at takeover; no
infrastructure retry, limit increase or new structural frame was needed.

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
# Standalone support, not imported by the headline modules:
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Noise.RestartFrames
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Noise.RestartFrames
# Full gate: expected inherited failure, not reported as a scoped pass:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
```

The gate already supplies the headline discovery/axiom-check procedure; no
additional audit infrastructure was introduced. After the split lands by paste,
retype claims and delete structural frames that the new types make unnecessary.


## H1 continuation: whole-creator tag ownership

The actual createInitiation and createResponse now preserve every optional peer
tag on normal refusal, and on success change only the requested peer's tag.
Response success derives the entry CONSUMED_INITIATION tag from its actual
first peer read and guarded branch. No residency, readiness, reference budget,
coherent owner word or alias restriction is supplied. Missing-device, missing-peer,
NULL-word, hidden-input and index failures keep their actual stopped behavior;
the claims are normal-return contracts, not totality or full-state rollback.

CreationTagFrames holds one named local peer-write variant.
CreationTagSource composes the actual operations and the existing typed index
adapter; CreationTagClaims projects both results, and Statements adds two
literal headlines. Seven theorems and three modules are added, with no data
definition or shared-layer edit. Together with the two whole-consumer tag
contracts, this supplies all four create/consume tag maps. Session/clear
composition and allocation-lifetime confirmation remain separate work.

Probe 1 fails eleven proof/inference diagnostics and seventeen unused-simp
warnings; changed probe 2 passes. The narrowed split-body check and isolated
Frames check also pass without warnings at default limits. Root and independent
source review find no issue. No mirror change is requested.

## H4 continuation: fitting multi-peer getter

The original wgGetDevice now returns the exact ordered JSON for any finite
fitting peer list whose listed peers are resident and have empty allowed-IP
lists. Repeated identifiers and public keys remain repeated visits; endpoint
fields are unrestricted and use the mirror's actual serialization.
The explicit bound is devicePrefixSpace + 168 * length + 20 <= NLMSG_GOODSIZE.
It covers DATA and DONE in one envelope. An empty list uses the actual
cancelled nest and becomes peers=[] through the original coalescer.

MultiPeerDumpModel records the fixed attributes and exact callback result.
MultiPeerDumpSource proves the original finite dump loop and callback,
including cancellation. MultiPeerGetterModel defines the expected JSON;
MultiPeerGetterSource proves the actual queued DATA/DONE drain;
MultiPeerGetterClaims composes the original start, receive and coalescer.
Statements appends one literal projected headline. These eight theorems,
five definitions and five modules reuse the previously checked two-theorem
multi-peer coalescer. Whole Device equality and final socket state are exact.
The selector, idle/empty socket, residency, empty-IP and capacity premises
remain explicit; no callback-success, liveness or reference premise is added.
Multi-peer pagination, nonempty peer IP lists and global owner/list coherence
remain open. This result concerns mirror JSON rather than wire encoding.

Producer probes 1--10 have outcomes PASS, FAIL(1), FAIL(4), FAIL(5),
FAIL(2), FAIL(2), FAIL(2), FAIL(5), exit-zero-with-warning, PASS.
Intermediate failures concern source-loop normalization, record syntax,
arithmetic and default recursion/simplification/heartbeat limits; no limit was
raised. Probes 4 and 8 each have four warnings; probe 9 has five unused-simp
warnings and is not accepted. Getter probes 1--3 fail four, one and one
diagnostics; probe 1 also emits two warnings, including failed-elaboration
recovery from a broken JSON definition. No written or recovered placeholder
is accepted. Corrected probe 4 checks all three getter roots with only standard
axioms and no warnings. Independent review verifies the actual loop,
cancellation, duplicate handling, capacity, socket and whole-getter composition.

The producer build passes 76 jobs without warnings; the combined Noise/Config
build passes 383 jobs with only the inherited Env:865 String.mk warning.
The scoped axiom audit checks 1,467 logical roots in 319 modules, including
972 public theorem roots, using only the three standard axioms.
Fresh replays of both terminal modules pass. Static checks, all 258 original
terminal names/order, diff formatting and mirror/shared-layer boundaries pass.
The census rises from 2,276/745/316 to 2,291/753/319
(theorems/modules/headlines). No infrastructure retry, cap increase, guest
run, merge to main or push occurs. The inherited full-gate failure is unchanged
and is not rerun or presented as passing.

Reproduce with capped scripts/in-bundle lake build on
Leanux.Proofs.WG.Noise.Statements and Leanux.Proofs.WG.Config.Statements,
then capped scripts/in-bundle lake env leanchecker --fresh on each module,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H1 continuation: session, clearing and expiry tag maps

The original beginSession now preserves every optional peer tag on a normal
false return. A true return changes only the selected peer to ZEROED and
derives its actual entry CREATED_RESPONSE or CONSUMED_RESPONSE tag.
The original handshakeClear and whole expireCurrentPeerKeypairs each zero
only the selected peer on normal return. Residency comes from the actual first
read, not a supplied precondition. Missing/NULL owners, hidden clocks, missing
keys and aliased releases keep their actual stopped paths.

SessionTagFrames contains two pure preservation facts: ordered rotation keeps
peer tags through every slot write/release, and validity-only key updates keep
tags. SessionTagSource reuses the exact SessionEffect and configuration expiry
effects; SessionTagClaims contains the three projected contracts. Three literal
headlines bring this package to eleven theorems and three modules, with no
data definition or shared variant. The seven creation, consumption, session,
clear and expiry operations now have whole optional tag-map contracts.
This is not a mixed-history, full-driver or allocation-lifetime theorem.

The full eleven-theorem candidate and narrowed standalone Frames probe each
pass on the first check, with no diagnostics and default limits. Root and
independent review find no issue. The installed Noise closure passes 161 jobs
without warnings. No mirror change is requested.

## H6 continuation: outgoing session-counter origin

The actual outgoing response prefix preserves keypairCounter through the
sender clock/write, response creation and MAC publication. A reached session
cut therefore starts at the original whole-call counter. The projected claim
retains the existing complete outgoing observer and SessionArmEvent. When
that event is an allocation, its serial is entry counter plus one at the
actual hook cut. False session returns and normal creation refusal keep their
existing observations. Exact erasure keeps all stopped executions; no stopped
post-state, final-call counter delta, final key residency or cross-call
uniqueness is asserted.

SessionOriginFrames has two narrow named variants of C1's
WGTransitions.createResponse_spec and addMacToPacket_spec, using only their
counter/frontier observation. SessionOriginSource links the actual prefix;
SessionOriginClaims projects the whole-call observation; Statements has one
literal headline. Five theorems and three modules are added, with no data
definition. The eight-site complete outgoing preservation layer and larger
incoming layer remain inventoried in the shared-frame follow-up, not copied.

Probes 1 and 2 fail two inference and one consumed-binder diagnostics,
respectively. Changed probes 3--5 pass, including narrowed imports and all five
standard-only axiom roots. None emits warnings or raises limits.
Independent review finds the two shared variants were not named after their
C1 counterparts; both names and docstrings are corrected before this commit.
The initial 333-job build and fresh replay pass; the renamed source is rebuilt
and replayed again. This is changed-source validation, not an infrastructure
retry. The reviewer finds no semantic or domain issue.

## H4 continuation: scalar update followed by fitting multi-peer readback

The original scalar request followed by the original getter is now total on
the existing stopped-device/selected-peer reference domain and the finite
fitting getter domain. The response contains every listed occurrence in order,
with arbitrary endpoints; each occurrence of the selected peer reflects the
PSK and keepalive update. The selected peer may be absent from the dump list:
the exact Device still changes but that peer is absent from JSON. A malformed
second request retains the successful first mutation and returns -EINVAL.
No callback-success or post-set invariant premise is supplied.

MultiPeerScalarModel defines the updated peer view.
MultiPeerScalarEffects computes the actual ordered peer-map writes and derives
all getter inputs. MultiPeerScalarClaims composes the two original calls
through their actual intermediate native state and Ambient; Statements adds
one literal headline. Three theorems, one definition and three modules are
added. The existing scalar setter premises remain explicit; arbitrary-list
fwmark composition and multi-peer pagination are separate obligations.

Probe 1 fails two default-heartbeat diagnostics; probe 2 fails record syntax
and a selected-peer goal; probe 3 tries an unnecessary structural TreeMap
equality; probe 4 fails two default-heartbeat diagnostics and the downstream
missing helper. Preserving the actual repeated inserts and reducing explicitly
closes probes 5 and 6, the latter with all three standard-only roots.
No probe warning or limit increase occurs. Independent review finds two form
issues: the substantive helper belonged in Effects rather than Frames, and
the terminal prose did not explicitly distinguish an unlisted target.
Both are fixed without changing any proposition or adding a membership premise.
No mathematical/source-linkage finding remains.

The combined pre-form-correction build passes 534 jobs; the corrected Config
closure passes 308 jobs. Their only warning is the unchanged Env:865 String.mk
deprecation. Final axiom inspection checks 2,387 logical roots in 511 modules,
including 1,507 public theorem roots, using only standard axioms.
Fresh Noise replay passes; final Config and TimerDiscipline replays pass after
all artifact writers stop. Static trust/import checks, all 258 original
terminal names/order, diff formatting and mirror/shared boundaries pass.
The census rises from 2,291/753/319 to 2,310/762/324
(theorems/modules/headlines). All three independent reviews are dispositioned.
No infrastructure retry, cap increase, guest run, merge to main or push occurs.
The inherited full gate remains FAILED and is not rerun unchanged.

Reproduce with capped scripts/in-bundle lake build on the Noise, Config and
TimerDiscipline Statements modules, then capped scripts/in-bundle lake env
leanchecker --fresh on each, with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

A documentation-update guard matched the full H6 label too broadly and
stopped before writing the register. Dirty worktrees, including untracked
files, were snapshotted to recovery refs before correcting that guard. Branch
tips and working indexes stayed unchanged; no Lean validation was rerun for
this documentation-only correction.


## H1 continuation: finite mixed native tag histories

TagSequenceModel describes seven actual native operation kinds, their complete
original results, projected before/after receipts and a linked edge relation.
TagSequenceSource dispatches only to those original operations, reads the
actual snapshots and proves exact computation erasure, including concrete
WireGuard/Ambient state and the first Stop. TagSequenceClaims derives the
linked history from those same runs. Statements adds one literal headline.
No frame file is needed. The package adds five theorems, five ordinary
definitions, three inductives and one structure in three modules.

Every normal finite execution has exactly the supplied operation order and
linked all-peer tag effects. Initiation creation/consumption retain their
arbitrary-tag restart behavior; the response/session old-tag guards remain
derived. Normal refusals stutter the tag map, not necessarily other state.
No residency, readiness, coherence or reference premise is supplied.
A later Stop returns no partial history. This does not establish driver
scheduling, initialized reachability, slot coherence or allocation-lifetime
confirmation, and does not discharge the separate RestartFrames scope issue.

Probes 1 and 2 fail four and six bind/consumed-variable diagnostics, with no
warnings. Changed probes 3--5 pass the full package, narrowed split imports,
five standard-only axiom roots and standalone Model. Root and independent
review find no issue. The Noise closure builds in 164 jobs without warnings.
No mirror change is requested.

## H4 continuation: arbitrary-list mixed fwmark/scalar readback

The actual fwmark request now composes with its scalar suffix and the original
fitting getter for arbitrary finite peer lists. The real captured list drives
all source/cache clears, including repeated visits. The selected peer can be
unlisted; its scalar update still occurs, and its existing source/cache fields
then survive. Every listed occurrence is serialized with the actual endpoint
attributes and the selected scalar change where applicable.

This is Ensures, not total return: missing listed peers in the native setter
and unavailable reset records retain their Stops. The public getter composition
requires listed residency, empty allowed-IP lists, fitting capacity and idle
socket/selector state, with the existing creating-network, stopped-device and
selected-reference premises. A malformed second peer returns -EINVAL only
when the earlier reset prefix normally completes; the earlier mark, generation,
clears and scalar writes remain reflected in the result.

MultiMixedModel defines the pointwise clear store and final effect.
MultiMixedEffects derives resident/dump field effects; MultiMixedFrames
separately preserves fields outside peers relative to the updated base.
MultiMixedSource factors the actual whole setter; MultiMixedClaims joins
the actual setter and getter; Statements appends one literal headline.
Six theorems, two definitions and five modules are added. The final Device
relation is exact outside peers, with pointwise peer contents and existential
final reset times. It is not a per-visit reset transcript or a fixed TreeMap
representation. JSON and socket state are exact. Global ownership and
cross-peer pagination remain open.

Probe 1 fails five congruence/source-record/inference diagnostics and emits
one unused-simp warning. Changed probes 2 and 3 pass source/residency and pure
effects. Probe 4 fails two serialization/projection composition diagnostics;
changed probes 5 and 6 pass the whole set/get and narrowed split package,
including all six standard-only roots, without warnings. No limit is raised.
Independent review finds no defect and confirms the normal-return and
pointwise-effect qualifications above. The installed closure builds 313 jobs,
with only the inherited Env warning.

## H6 continuation: initialized give-up cleanup witness

The [initialized give-up report](2026-10-17-proof-campaign-2-initialized-giveup.md)
records an accepted 23-operation generated history through the actual runner,
using the existing boundary observer and its exact erasure. Nineteen retries
produce twenty initiations; callback twenty gives up and enqueues zero-key
cleanup at stamp 21. Every boundary has zero keypair counter, empty key store
and empty slots, and every per-operation log lacks keypair allocation/session
decisions. Original and audited complete JSON agree.

Source inspection of the C's partial-exchange cleanup agrees with a statement
artefact, not a mirror defect. This is recorded-arm runtime evidence with
generated inputs, not Linux capture, all-mode evidence or a kernel-proved closed
trace. It receives zero theorem/headline credit. The standalone module has
ten private executable definitions plus main; the generator and report carry
the reproducible inputs/conclusion, with no committed logs. The larger
session-relative history theorem remains open.

The scratch run passes first time with --root .; independent review finds no
semantic issue and requests a precise keypair-allocation label, which is fixed.
The installed command also passes without warnings. The standalone module
builds 71 jobs with the inherited Env warning. No failed runtime run or
infrastructure retry occurs.

Final combined audit checks 1,528 logical roots in 337 modules, including
1,007 public theorem roots and the standalone runtime entry, all standard-only.
Fresh replay passes on Noise.Statements, Config.Statements and the standalone
runtime module. Static checks, all 258 original terminal names/order,
diff formatting and mirror/shared boundaries pass. The census rises from
2,310/762/324 to 2,321/771/326 (theorems/modules/headlines).
No cap increase, guest run, main merge or push occurs. The inherited full gate
remains FAILED and is not rerun unchanged.

Reproduce the scoped builds and fresh replays on those three modules under
capped scripts/in-bundle with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
The runtime reproduction command is in its linked report.


## H2 continuation: owner coherence through actual handshake queueing

Both modes of original sendQueuedHandshakeInitiation now preserve
HashedOwnersCoherent on every normal return, with OwnerCoherentSafe as the
sole projected entry invariant. Actual false-mode attempt reset and true-mode
unchanged prefix remain distinct. The existing observers supply the actual
clock and queue-inspection result; their exact erasures identify the same
original run. Repeated peer writes are compared pointwise. Successful
acquisition supplies the reference restored on an already-pending refusal;
no residency, publisher, readiness, queue-state or reference-budget premise
is added. This is neither worker completion nor global reference ownership,
and it asserts no state after a Stop.

OwnerCoherenceQueuedFrames contains the one pure preservation fact for
queuedDeviceAfterInspection. OwnerCoherenceQueuedClaims contains the projected
whole-call theorem; Statements adds its literal wrapper. Three theorems, two
modules, no new definitions or shared variants: H2 reaches 465 theorems and
85 headlines. The obsolete queuedDevice approximation is not used.

Probe 1 fails five proof-form diagnostics and probe 2 fails two; neither emits
warnings. Changed probes 3–5 pass: complete candidate, exact split package
with all three standard-only axiom roots, and standalone narrowed Frames.
The scoped build passes 356 jobs with only inherited Env:865 String.mk.
Independent review finds no issue. No limit change or infrastructure rerun.

## H3 continuation: the original cookie-message branch

Every normal type-3 receiveHandshakePacket call preserves all remote endpoints.
The actual cookie path runs lookup, optional decryption and cookie-field update,
then releases its held reference. Existing generic lookup contracts supply
that reference even for arbitrary aliases and owner words; the new write
preserves both the endpoint and reference. No coherence, residency, clock,
decryption-success, packet-length or reference-budget premise is introduced.
The native frame preserves the full optional Endpoint map; the projected
headline promises remote family/address/port/IPv6 scope. It retains actual
Stops and does not claim totality or post-error rollback.

CookieEndpointFrames holds the native preservation theorem;
CookieEndpointSource is the exact original type-3 source factor, including
errors; CookieEndpointClaims and Statements connect the lifted whole call
through the campaign projection. Four theorems in three modules bring H3 to
190 theorems and 18 headlines. No definition or shared variant is added.
The deferred cookie-reply/socket layer is not needed for this branch.

Probe 1 fails 11 elaboration errors and six warnings; probe 2 fails four
errors without warnings. Recovery placeholders in those failed drafts are not
accepted. Changed probes 3–4 pass the complete candidate and exact split
package with four standard-only axiom roots, without warnings. The scoped
build passes 145 jobs without warnings. Independent review finds no issue;
its scope is this receiver branch, not queue provenance or full H3.

## H5 continuation: recorded idle-wait wheel completion

Every normal recorded idleTimers return stores its actual end-of-wait read
and satisfies TimerWheel.nextDue = none at that read. Device absence is
allowed. The source suffix keeps pass bound and end read separate; this caller
supplies equal values. The actual guard excludes its due branch because all
of that branch's worker/lookahead outcomes stop. The following Ambient-only
clock read cannot change WireGuard state, and the final write changes only
jiffiesLast. No frame lemma is added for that type-given fact.

NoTimerDue means exactly the wheel's nextDue test over resident IDs in
device.peerList and their wheel entries. It does not establish peer-list/store
or wheel/expiry coherence, absence of timers on unlisted residents, successful
execution for arbitrary records, global work emptiness or recordless behavior.
The differing pass bound in afterAdvance is not silently equated with its
end read.

TimerWaitModel holds the predicate; TimerWaitSource contains the actual suffix,
its guard/suffix contracts and exact recorded idle source equation;
TimerWaitClaims and Statements contain the projected claim and wrapper.
Five theorems and two definitions in three modules bring H5 to 301 theorems
and 45 headlines. No shared variant or mirror change is needed.

Development probes 1–6 fail respectively 3, 2, 1, 1, 1 and 1 proof-form
errors; only probe 1 emits warnings (five). Probe 7 passes the guard.
Probe 8 fails four suffix/source proof-form errors; probe 9 fails one and
emits one unused-simp warning. Changed probe 10 passes the complete package;
probe 11 passes the exact split and all five axiom roots, standard only.
All final proofs use default limits, without suppression or cap changes.
The scoped build passes 278 jobs with only inherited Env:865 String.mk.
Independent review finds no issue and confirms the nextDue scope above.

The three-result continuation adds 12 theorems, eight modules and three
headlines: 2,333 theorems in 779 owned modules, 329 headlines. The combined
axiom audit checks 2,041 logical roots in 425 modules, including 1,321 public
theorem roots, standard only and without diagnostics. All three fresh kernel
replays pass. Static trust/import checks, all 258
original terminal names/order, and mirror/shared-layer boundaries pass.
No infrastructure rerun occurs. All H1–H6 remain in progress; the inherited
CounterWindow/ReplayWindow full-gate failure is unchanged and is not rerun.

Reproduce the scoped build and fresh replay for
Leanux.Proofs.WG.Index.Statements, Leanux.Proofs.WG.Roaming.Statements and
Leanux.Proofs.WG.Progress.Statements with scripts/in-bundle under capped,
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. Existing ranked mirror requests
are unchanged; no mirror-team change is requested for these local contracts.


## H4 continuation: endpoint-aware finite IPv4 pagination

The whole original getter now handles arbitrary endpoint fields on its existing
finite single-peer IPv4-list domain. The first capacity includes the actual
endpoint cost, (Q - D - (peerFixedSpace p + 4)) / 28. The progress premise is
D + max 168 (peerFixedSpace p + 32) ≤ Q: it specializes to the previous D+168
bound without an endpoint, while making room for the first IPv4 item with
either endpoint family. First-boundary freshness and DATA/DONE counts use
this capacity. Resumed pages keep the original 44-byte overhead and 28-byte
IPv4 items; their induction and transport remain unchanged.

The claim derives every actual first callback and resumed receive; it does
not assume successful execution. Empty, fitting and arbitrarily many pages
within the calculated 4096-receive bound produce the exact suffixJson,
preserve the whole initial Device and finish the actual selected socket.
Singleton/listed/resident, readable IPv4 nodes, canonical boundary freshness,
capacity and idle/empty selector inputs remain explicit. Repeated IDs away
from cursor boundaries are allowed. This does not prove weighted IPv4/IPv6
packing, multi-peer pagination, ownership or reachability.

Endpoint output means the mirror's original peerFixedAttrs serialization.
AF_INET becomes JSON family 4; any other present family becomes family 6.
Addresses are truncated to the serialized 4/16-byte width, and IPv4 omits
IPv6 flowinfo/scope; source-cache fields are also absent. For an unsupported
family the mirror charges no endpoint attribute space while still producing
its IPv6-shaped JSON. The theorem follows those definitions for arbitrary
states; it does not assert raw-field retention or that such a state is
reachable from initialization. Independent review identified the terminal
docstring's raw-retention wording as a P3 overclaim. The wording was corrected
before the build; the formula and proof did not change. No other finding.

EndpointPaginationModel holds four data definitions, a capacity bound and
exact no-endpoint compatibility. EndpointPaginationFirstSource supplies
the actual endpoint-aware first prefix and fitting/splitting callbacks;
EndpointPaginationCoalesceClaims holds the two finite coalescing laws.
EndpointPaginationTransportSource and Source supply thin start/complete
adapters and compose the existing ipv4ResumeDrain_returns. Claims and
Statements supply the projected whole getter and literal wrapper.
Thirteen theorems in six modules bring H4 to 676 theorems and 91 headlines.
No old signature, existing induction, shared layer or mirror definition changes;
no new frame family is copied.

Probe 1 fails seven parse/arithmetic diagnostics; probe 2 fails one default
recursion-depth check. Abstracting the common continuation head resolves it
without raising limits. Changed probes 3–4 pass the first/whole transport.
Probe 5 fails two no-endpoint constant reductions; changed probes 6–7 pass the
whole claim and exact narrowed split with all thirteen standard-only roots.
No probe emits a warning. The scoped build passes 319 jobs with only inherited
Env:865 String.mk. The closure audit checks 1,127 logical roots in 255 modules,
including 770 public theorem roots, standard only and without diagnostics.
Fresh kernel replay passes. Static checks, original 258-name order and
mirror/shared boundaries pass. No infrastructure rerun or cap/limit increase.

Current totals: 2,346 theorems, 785 owned modules, 330 headlines. All H1–H6
remain in progress. The inherited CounterWindow/ReplayWindow gate failure
remains unchanged. Reproduce the scoped build and fresh replay of
Leanux.Proofs.WG.Config.Statements with scripts/in-bundle under capped,
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. Existing ranked mirror requests
are unchanged; this extension needs no mirror-team change.


## H2 continuation: new-handshake and zero-key callback coherence

Original expiredNewHandshake and expiredZeroKeyMaterial now preserve the
local hashed-owner invariant on normal return, with OwnerCoherentSafe as
their sole projected entry condition. The former composes actual endpoint
source/cache clearing and both-mode handshake queueing. The latter derives
the held reference from successful actual peerGet; its compensating put
therefore cannot be the last release. Actual queue membership and
peekQueuedUnit remain separate inputs to the original branch. The alternate
path records and enqueues clear work. Neither branch assumes the later
worker's release coverage or completion.

Optional Device, arbitrary Ambient, aliases and unpublished owner words
remain allowed. Missing state, zero/overflow reference checks and clock/record
failures retain their original Stops. This is local normal-return coherence,
not queue consistency, reachable global ownership or failed-call rollback.

OwnerCoherenceCallbackFrames holds the endpoint-source preservation variant.
OwnerCoherenceCallbackSource holds the acquisition-effect variant, deriving
residency and count greater than one. Both names cite the corresponding
C1 WGBase helper; proofs reuse owned exact source contracts. CallbackClaims
and Statements supply the two projected claims and literal wrappers.
Six theorems in three modules bring H2 to 471 theorems and 87 headlines.
No new definitions or shared-layer edit.

Probe 1 fails three proof-form diagnostics without warnings; changed probe 2
passes the complete candidate, probe 3 the exact split and six standard-only
axiom roots, and probe 4 standalone narrow support. Independent review finds
no semantic issue. Its two P3 findings are corrected separately: acquisition
is an effect, so it moves from Frames to Source; terminal wording now says
endpoint-source/cache clearing, since the remote endpoint is preserved.
No formula or premise changed. The final source organization is built and
replayed below.

## H4 continuation: endpoint-aware setter/readback composition

The actual mixed fwmark/scalar and private-key requests now compose with the
endpoint-aware finite IPv4 getter. The old no-endpoint claims remain unchanged.
Both new claims derive every getter input from the same actual normal setter
successor and its remaining Ambient inputs; no callback/receive-success
premise is supplied. Explicit readbackFrame contracts transport socket and
selector state, rather than inferring them from Device effects.

The mixed request retains its singleton, creatingNet, lookup/resident,
live/reference-bound and stopped-device domain. It changes the actual
endpoint source/cache fields; only their serialized remote endpoint fields
agree with the pre-clear value. A later malformed peer returns -EINVAL after
the earlier mark and scalar writes, while reset-record Stops remain Stops.
The key request retains its established/changed/no-collision domain and
derives its actual expiry timestamp and ordered key effects. Capacity and
boundary calculations use the effective installed identity, including
clamping and null-key serialization, not the initial identity.

EndpointPaginationCapacityFrames transports freshness and DATA/DONE count
from equal serialized prefix sizes. MixedEndpointPaginationClaims and
KeyEndpointPaginationClaims hold the two projected compositions; Statements
adds two literal wrappers. Five theorems in three modules, no definitions,
bring H4 to 681 theorems and 93 headlines. The endpoint getter and resumed
induction are reused unchanged. Single-peer IPv4 list, fresh cursor boundaries,
capacity, bounded receive count and idle/empty socket premises stay explicit;
global ownership and multi-peer/mixed-family pagination remain open.

Both development probes pass without warnings: full three-theorem composition,
then exact split package with the two wrappers and five standard-only axiom
roots. Independent review finds no issue, confirming same-run linkage,
effective key capacity and serializer rather than raw-endpoint equality.

Combined validation: the Index/Config scoped build passes 523 jobs, then the
terminal wording correction rebuilds Index in 360 jobs. Only inherited
Env:865 String.mk appears. The combined axiom audit checks 2,004 logical roots
in 459 modules, including 1,382 public theorem roots, standard only and without
diagnostics. Fresh kernel replay passes for both changed roots.
Static trust/import checks, all 258 original headline names/order and
mirror/shared boundaries pass. No default limit/cap change, suppression,
infrastructure rerun or unchanged failed-source rerun occurs.

Current totals: 2,357 theorems in all 791 owned modules, 334 headlines.
All H1–H6 remain in progress; the inherited CounterWindow/ReplayWindow gate
failure is unchanged. Reproduce the scoped build and fresh replay of
Leanux.Proofs.WG.Index.Statements and Leanux.Proofs.WG.Config.Statements with
scripts/in-bundle under capped, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
Existing ranked mirror requests are unchanged; these steps request no mirror
change. The two named native helper variants are listed in the shared-frame
followup for eventual unification.


## H2 continuation: both retransmission callback branches

The whole original expiredRetransmitHandshake preserves OwnerCoherentSafe
on every normal return under that sole entry invariant. Retry increments the
attempt count, clears endpoint source/cache fields and queues the handshake
through existing contracts. Give-up deletes the keepalive timer, purges staged
data, and conditionally arms zero-key cleanup through the exact all-mode arm
effect. Owner words and counts survive all of these writes pointwise, with
aliases allowed.

No residency, readiness, running/alive, pending-timer, consistent-wheel,
reference-budget or successful-arm premise is added. The caller clock still
precedes the arm guard; a down/dead guard is not treated as a guaranteed
successful no-op. Missing state, clock/cache/reference/queue and wheel failures
remain actual Stops. This does not establish callback totality, outer timer
selection or the remaining keepalive callbacks.

OwnerCoherenceRetransmitFrames contains the pure arm-effect transport and
three named C1-family variants: WGBase.delTimer_spec and
WGTransitions.purgeStagedPackets_spec/modPeerTimer_spec. The proofs reuse
owned delTimer_exact and GuardedArmingClaims.modPeerTimer_effect; no hidden,
armTimer or wheel-placement implementation layer is copied. Claims and
Statements contain the projected whole-call theorem and literal wrapper.
Six theorems in two modules, no definitions: H2 reaches 477 theorems and
88 headlines.

Development probe 1 fails six proof-form errors and three unused-simp warnings;
probe 2 fails one false-branch normalization error without warnings. Changed
probes 3–5 pass the combined candidate, exact split with six standard-only
axiom roots, and standalone narrow Frames. The scoped build passes 364 jobs
with only inherited Env:865 String.mk. The closure axiom audit checks 1,362
logical roots in 300 modules, including 910 public theorem roots, standard
only and without diagnostics. Fresh kernel replay passes. Independent source
review finds no issue in the whole callback, all arm modes or variant scope.

Current totals are 2,363 theorems in all 793 owned modules, 335 headlines.
Static trust/import checks, original 258-name order and mirror/shared
boundaries pass. No limit/cap change, suppression or infrastructure rerun.
All H1–H6 remain in progress; the inherited full-gate failure is unchanged.
Reproduce build and fresh replay of Leanux.Proofs.WG.Index.Statements under
capped with scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
No new mirror request; the three bounded variants are listed in the existing
shared-frame followup.


## H5 continuation: the actual post-advance wait bounds

The original afterAdvance now has an operational receipt for its actual
lastAdvance pair and non-consuming end peek. Dropping the receipt gives the
complete original operation, including both recordless branches and every
Stop. The recorded normal-return claim has only hidden.isSome as its entry
condition. It derives a present receipt, the final stored end read, and the
original no-due-wheel guard at the pass selected by wrapped timeAfter.

The pass is the end read when timeAfter selects it and otherwise the stored
pre-advance bound. The final clock always stores the end read. No linear time
order, preceding advance execution, record freshness, callback success, device
presence, queue emptiness or totality is assumed or concluded. The source
provenance theorem exposes the real fixture read without extending the
campaign projection or reconstructing a World from it. Peek and consuming
read agree in value on normal return; record identity is not asserted.

AdvanceWaitModel holds the receipt and pure pass function; Source holds the
exact prefix/suffix decorator, erasure and native provenance; Claims and the
literal Statements wrapper use Product. No Frames file is needed: the pure
prefix reads do not mutate state and the existing timer-wait suffix contract
supplies the effect. Six theorems in three modules bring H5 to 307 theorems
and 46 headlines. No shared variant or mirror change.

Draft probes 1–6 fail ordinary congruence, discard, typed-throw, identifier and
state-normalization obligations. Their rejected axiom queries are not accepted
proofs. Changed probe 7 closes the full candidate; probe 8 checks the exact
split and all six standard-only roots at default limits, without warnings.
Independent review finds two documentation errors, both corrected before the
build: a prefix-run typo and wording that failed to distinguish stored end
from checked pass. The formulas do not change.

## H4 continuation: exact mixed-width dump scans

Four new data definitions represent actual per-node space, serialized JSON,
the mapped JSON array and summed space. Six source theorems prove the exact
readNode/getAllowedips result, complete and first-failing weighted scans,
their original sequence/cursor wrappers, and the actual first dump callback's
split. IPv4-width nodes cost 28 bytes and every other stored width costs 40;
the JSON family branch and masking still use the original node fields.
This arbitrary-width source contract is not a valid-IPv6 or topology claim.

Readability is required only for nodes actually read. Duplicate identifiers
and an empty emitted prefix are allowed. A failed node put restores its
incoming skb; the enclosing allowed-IP nest must itself have fit. The
first-callback fact derives the actual fixed peer attributes, endpoint cost,
sequence, next cursor and DATA split. It adds no successful-call premise.
Complete mixed-family getter progress, weighted partitioning, cursor freshness,
transport and coalescing are still to compose; there is no new headline.

MixedDumpModel is data; LeafSource, ScanSource and CallbackSource are source
contracts. No new frame or shared variant is introduced. H4 now has 687
theorems and 93 headlines. The four modules are explicitly scoped roots/support
until the full getter composition imports them.

Development probes 1, 3 and 5 fail ordinary endian/room, Device-field and list
head reductions. Probe 1 also has two unused-simp warnings; probe 4 elaborates
but reports three deprecated lemma warnings. All are fixed. Changed probes
2, 6, 7 and 8 pass leaf/full/narrow packages; probe 9 passes the exact split
with six standard-only axiom reports and no warnings. The final author command
is capped scripts/in-bundle lake env lean --stdin, with LEAN_NUM_THREADS=32
and LEANUX_QEMU_SLOTS=16, no limit overrides; reported exit 0 in 0.93 seconds.
Independent source review finds no issue. The reviewer verifies the source
and logs; root validation below independently builds and replays the package.

Combined scoped build passes 334 jobs, with only inherited Env:865 String.mk.
The closure axiom audit checks 1,424 logical roots in 270 modules, including
866 public theorem roots; all are standard-only, with no diagnostics.
Fresh kernel replay passes for both changed roots.
Static trust/import checks, all original 258 headline names/order and
mirror/shared-layer boundaries pass. No infrastructure rerun, cap/limit
increase or warning suppression occurs.

Current totals are 2,375 theorems in 800 owned modules and 336 headlines.
All H1–H6 remain in progress. The inherited CounterWindow/ReplayWindow full
gate fails as previously recorded; it is not rerun unchanged.
Reproduce the scoped build and fresh replay for
Leanux.Proofs.WG.Progress.Statements and
Leanux.Proofs.WG.Config.MixedDumpCallbackSource under capped with
scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.
Existing ranked mirror requests are unchanged; neither package requests a
mirror-team change.


## H2 continuation: a persistent-callback invariant counterexample

The proposed sole-OwnerCoherentSafe preservation claim for the whole
expiredSendPersistentKeepalive callback is false on arbitrary native states.
A checked coherent entry has caller peer 0's current-key slot name keypair 1,
whose peer word names peer 1. Actual staged sending acquires peer 1; dead-peer
data creation then releases caller 0's last reference. The callback returns
normally with a separately hashed keypair still naming the erased peer 0.
The explicit real birthdate record keeps the selected key valid.

The [finding](2026-10-17-proof-campaign-2-persistent-owner.md) gives the concrete
state, actual path and C correspondence. This is a missing slot/caller ownership
relation in a local arbitrary-state invariant. No accepted initialized trace,
mirror divergence or kernel defect is established. The separate send-keepalive
callback subsequently reads the erased caller and Stops on this witness, so
that callback is not refuted by the same normal-return argument. No premise
was silently added to force a positive theorem.

The model holds seven witness definitions and entry coherence; Source proves
the actual complete callback's total return; Claims and Statements refute
preservation over the projection. Four theorems in three modules bring H2 to
481 theorems and 89 headlines, with no frame/shared variant. Both broader
architectures were audited: direct native preservation needs six shared
send-path families, while existing owned fallback contracts cover absent or
invalid keys only. This larger overlap is inventoried rather than copied.

Ten changed-source probes were needed. Probes 1–9 fail respectively on map
lookups (4 errors/2 warnings), optional/total lookup mismatch (4/6), clock
metadata (1/2), passive-section reduction (1/2), signed expiry (1/2), errno
constants (1/1), Index adapter reduction (1/1), Ambient modification (1/2),
and execution witnesses/Except.map (2/2). All warnings are corrected.
Probe 10 passes with all four standard-only roots, no warnings or proof-limit
increase. The final split module organization is independently built below.
Independent source review finds no issue.

## H4 continuation: weighted plans, resumed callbacks and generic coalescing

WeightedPaginationModel greedily consumes exact 28/40-byte costs, proves
prefix decomposition/fit/first-failure maximality, and defines finite resumed
pages whose recursive remainder is strictly shorter. With at least 40 bytes
of node room, every resumed page is nonempty and fits. The first page may
be empty once. Concatenation preserves order and multiplicity; arbitrary
stored widths and duplicate IDs remain allowed. Boundary freshness is defined
against the whole previously emitted prefix and is a later composition
premise, not a property asserted of every plan.

WeightedPaginationSource derives the original resumed callback from its
actual cursor selection, fixed prefix and complete/split scans. Header room
implies at least 124 bytes for nodes. Resident nodes and cursor freshness
discharge every read and choice; no successful callback is supplied.
Claims presents its exact return and preserved Device over the projection.
Five data definitions and eight theorems occupy three modules. Four probes:
1 fails two local-let goals and one unused-simp warning; 2 passes the pure
model; 3 fails two 40+4 room normalizations; 4 passes all eight standard-only
roots without warnings. Independent review finds no issue.

GenericPaginationModel and Claims supply five pure JSON-list constructors
and two actual coalescer equalities. Any adjacent continuation can be merged
before the unchanged remainder, including later errors; every finite page
sequence coalesces to its concatenated entries. Empty/repeated pages and
arbitrary JSON and endpoints are allowed. This is a coalescer contract,
not a claim that a getter produced the pages. The first capped default-limit
probe passes with both standard-only roots and no warnings. Independent
review finds no issue. No existing IPv4 signature is changed.

These ten H4 declarations bring it to 697 theorems and 93 headlines. The
weighted actual first complete/empty branches, full callback/socket sequence,
DONE spill count and final getter composition remain open. The exact receive
count must include a separate DONE when the final DATA has less than 20 bytes
left, including a genuinely empty input. The implementation will reuse the
generic receive-sequence theorem; no resumed IPv4 transport induction or
shared layer is copied.

Combined scoped build passes 400 jobs, with only inherited Env:865 String.mk.
The axiom audit checks 1,533 logical roots in 336 modules, including 1,010
public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes for all three changed roots.
Static trust/import checks, all 258 original headline names/order and mirror/
shared boundaries pass. No cap/limit changes, suppression or infrastructure
reruns. Current totals: 2,389 theorems in 808 modules and 337 headlines.

All H1–H6 remain in progress. The inherited full gate remains FAILED in
CounterWindow/ReplayWindow and is not rerun unchanged. Reproduce the scoped
build and fresh replay of Leanux.Proofs.WG.Index.Statements,
Leanux.Proofs.WG.Config.WeightedPaginationClaims and
Leanux.Proofs.WG.Config.GenericPaginationClaims under capped/scripts/in-bundle
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. No new mirror-team request.


## H5 continuation: actual advance syscall and runner linkage

The complete original wg_advance syscall now has an erased operational
receipt. Every normal return gives result zero and the bounds written by that
same actual advance, with j1 - j0 = ticks.toUInt64. The descriptor, entry guard,
fdput, return work and afterAdvance remain in their original order with every
Stop. If the actual wait returns a recorded receipt, its bounds equal this
advance's bounds; the final clock stores jEnd and NoTimerDue holds at the
distinct wrapped pass. No entry-mode preservation through arbitrary task work
or successful execution is assumed.

AdvanceOperationSource contains three action definitions, actual advance
effects and exact syscall erasure. Claims uses Product. RunnerAdvanceSource
connects the same execution through the real runnerEntry and skipAmbient to
the existing boundary guards. The runner source is imported by Statements,
so its proof is included in that closure. FS fixture preservation is local
reasoning from liftFS writeback, without a named cross-subsystem frame.
Six theorems in three modules bring H5 to 313 theorems and 47 headlines.

Changed probes 1–4 fail ordinary source factoring with error/warning counts
3/2, 5/7, 1/2 and 1/2. Probe 5 closes the three source facts. Probes 6–9 fail
8/1, 2/3, 5/0 and 1/0, from reserved/constructor-like names, discard/tuple
normalization and names eliminated by case substitution. Probe 10 checks the
exact split and six standard-only roots, no warnings. All outputs were
inspected; no rejected recovery declaration counts as proof. Independent
review finds no issue. Root corrects the entry definition's comment, which had
described the broader prefix rather than entry resets and the guard.

## H4 continuation: original first callback and dump start

WeightedStartModel distinguishes empty input from an empty first emitted
prefix of nonempty input. Source derives the original first callback's full
DATA, room, sequence and cursor for empty, complete and split cases. All
inputs need the header bound; only nonempty input needs its allowed-IP nest
to fit, and the first node need not fit. The actual netlinkDumpStart follows
through existing transport contracts to the exact socket. Completion retains
the real inline-DONE versus separate-DONE choice, including empty input.

Claims provides the two projected total-return contracts. The two data
definitions and five theorems occupy three modules; H4 now has 702 theorems
and 93 headlines. The first draft fails seven syntax/shape errors and four
recovery/unused-variable warnings; its recovery axiom output is rejected.
Changed probe 2 passes the exact package and five standard-only roots without
warnings. Independent source review finds no issue. Full receive sequence,
exact envelope count, coalescing and whole weighted getter composition remain
open; no shared variant or copied receive induction is introduced.

H5's scoped build passes 284 jobs, including its source-link import update;
H4's source build passes 120 jobs. Only the inherited Env:865 String.mk
warning appears in the H5 build. The combined audit checks 1,468 logical roots
in 284 modules, including 893 public theorem roots, standard-only and without
diagnostics. Fresh kernel replay passes both changed roots. Static trust/import
checks, all 258 original headline names/order and mirror/shared boundaries
pass. No cap/limit change, warning suppression or infrastructure rerun.

## Completion audit and documentation corrections

H1 already covers all seven tag-changing whole operations and their actual
finite mixed histories. Option-valued slots supply per-slot capacity; they do
not imply distinct slots or a three-key store bound. The current header and
register are narrowed accordingly. Confirmation across reinstallation remains
open; consecutive confirmation is not once-per-allocation-lifetime uniqueness.
Unconditional whole-call totality is not an extra requirement. No Noise
theorem changes in this documentation correction; its comment-only rebuild
passes 164 jobs without warnings.

The H5 audit found two stale present-tense claims: the old cookie paragraphs
still promised arbitrary-ring drain/suffix decrease, and mirror request 1 still
called its corrected-refusal carry pending. Both are corrected in place.
The historical claims/evidence retain their pins; current cookie contracts
preserve bounded outcomes/errors, and the actual backlog trace and audit now
have checked rejection equations. This is a documentation repair, not a new
mirror request or a change to the already checked statements.

[AGENT 2026-10-17] Describe operational refusal with the actual named Stop
constructor rather than treating every refusal as outsideDomain: trailing
records/suspension use hidden and pending NET_RX uses invariant. These are
fail-closed outcomes, not accepted-backlog counterexamples.

Finite recursion/ranges bound the explicit outer iterations provided their
bodies terminate, but a total logical
denotation does not itself prove executable termination of loop-backed helpers.
At this checkpoint the modular-power helper had a checked finite-evaluation
bridge, while arbitrary exact-count allocation remained beyond the single
successful keypair-allocation case. The later exact finite allocation tranche
closes that iteration gap. Further H5 work includes derived-fuel adequacy with callback refill and an
initialized queue/pending-work consistency invariant strong enough to lift
the exact local completion guards to all accepted operations. Fairness,
erasing physical stale ring slots, disarming future timers and unconditional
recordless success are separate stronger questions.

Two architectures remain inventoried: represented-ring/resource composition
using C1 Queues, RingGeometry and RingSteps plus actual record histories; or an
initialized runner invariant using C1 RxRing/RxEnv/JointSyscalls/JointRunner.
Neither is copied locally. Arbitrary malformed-ring counterexamples do not
establish initialized accepted executions. The existing callback-refill mirror
request remains separate from any attempt to increase a budget constant.

Current totals: 2,400 theorems in 814 owned modules and 338 headlines.
All H1–H6 remain in progress; the inherited full gate remains FAILED.
Reproduce the changed closures with scoped build and fresh replay of
Leanux.Proofs.WG.Progress.Statements and
Leanux.Proofs.WG.Config.WeightedStartClaims under capped/scripts/in-bundle,
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H1 continuation: direct reinstallation and the confirmation domain

The broad local wording, confirmation succeeds at most once for a resident
key, is false when arbitrary direct installation-helper calls are admitted.
The checked witness starts with one positively referenced responder key at ID
0, internal serial 17, and one peer with next = 0 and other slots empty.
The original sequence receivedWithKeypair 0 0; addNewKeypair 0 0;
receivedWithKeypair 0 0 returns true twice. The entire resident key, global
keypairCounter and device allocation cursor are unchanged. The final previous
and current slots both contain 0; next is empty. Every Ambient is permitted.

This is a statement-domain finding, not an initialized accepted trace or a
mirror/kernel discrepancy. The arbitrary entry does not establish an
allocation history; the direct helper does not allocate. Consequently the
fresh beginSession installation language and once-per-allocation-lifetime
claim remain open, with their larger transport inventory unchanged. The
existing adjacent-call no-repeat theorem remains valid. No premise is added
to it and no mirror-team repair is requested.

ConfirmationReinstallModel gives the concrete data and entry shape; Source
runs the three actual calls through the existing exact rotation factors;
Claims and the terminal expose the observation over the campaign projection.
Four theorems in three modules bring H1 to 235 theorems and 33 headlines.
No frame or shared variant is added. Independent review corrects “allocation”
to “positively referenced responder key” in the entry description, since
residency and a positive refcount alone do not establish allocation provenance.
No formula/domain issue remains.

Changed probes 1–3 fail on private-write reduction, existential witnesses and
the final peer witness; probe 1 also has four unused-simp warnings. Probes
4–5 pass, the last checking the exact split and four standard-only roots.
The installed scoped build passes 167 jobs without warnings.

## H5 continuation: the actual send-worker completion guard

Normal runSendWorkers return now guarantees absent Device or an empty final
sendWorkQueue, for both record modes and arbitrary entry state. The exact
source factor retains initial Device absence, requireNoCryptWork, queuedThisCall
reset, captured budget, every worker/scheduler call and every Stop. A completed
turn has observed an empty send queue and then run actual deliverSent, whose
existing named Device frame transports that fact to return. Finite-loop
induction follows the actual early-return branch; exhaustion reaches the real
budgetExhausted and cannot be accepted as completion in either mode.

SendCompletionModel contains the projected predicate; Source contains the
concrete loop factor and reasoning; Claims and Statements use Product.Ensures.
This adds five theorems in three modules, bringing H5 to 318 theorems and
48 headlines. It does not prove successful completion, fuel adequacy,
pendingWork/ring consistency, whole-operation emptiness or fairness. No
additional shared frame is copied. Independent source review finds no issue.

Changed probes 1–3 fail respectively with 6/10, 3/0 and 2/0 error/warning
counts, on option matching, lifted reads, eliminated names and budget-error
reduction. Probes 4–5 pass; the exact final split checks five standard-only
roots without warnings. Installed build passes 287 jobs, with only the
inherited Env:865 String.mk warning.

The combined axiom audit checks 1,537 logical roots in 295 modules, including
936 public theorem roots, using standard axioms only and no diagnostics.
Fresh kernel replay passes both changed terminal roots.
Static trust/import checks, all 258 original terminal names/order and mirror/
shared-layer boundaries pass. No proof-limit/cap change, suppression or
infrastructure rerun occurs. Totals are 2,409 theorems in 820 owned modules
and 340 headlines. All H1–H6 remain in progress; the inherited full gate
remains FAILED and is not rerun unchanged.

Reproduce with scoped build and fresh replay of
Leanux.Proofs.WG.Noise.Statements and Leanux.Proofs.WG.Progress.Statements
under capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H5 continuation: final idle waits at syscall and runner return

The original wgSet, wgInject, wgXmit and wgBatch syscall tails now have exact
final-wait observers. The prefix retains actual network entry resets/guard,
dispatch, tail calls, task work, and the correct send/afterXmit worker
continuation. Erasing the receipt yields the original syscall with the same
numeric result and every Stop. A receipt exists exactly when the actual idle
wait entered recorded mode; its value is the clock stored by that wait.
A present receipt proves NoTimerDue at the final syscall state. Recorded mode
at syscall entry is not assumed to survive arbitrary preceding work.

The actual runner operation executes that same observer at runnerEntry,
then its real skipAmbient and completion guards. Ambient stripping preserves
the clock/wheel fact by the lift's writeback type, without a new frame lemma.
Negative syscall returns remain included. wgUp is excluded because routing
work follows its wait. Nothing here establishes queue/ring/pendingWork
consistency, successful execution, future-timer absence or recordless no-due
behavior.

IdleOperationModel names the four accepted syscall forms; Source contains
the exact factors/erasures and read-only observer definitions; Claims contains
the three projected receipt facts; RunnerIdleOperationSource contains the
actual runner link and is imported by Statements. Eight theorems in four
modules bring H5 to 326 theorems and 49 headlines. Independent review finds
three overbroad comments on unrestricted helper definitions/theorems; they
are qualified by HasFinalIdleWait. Exact erasure and the terminal already
have that restriction, so no formula changes.

Six changed-source probes: 1 fails three read-normalization/witness errors
and four unused-simp warnings; 2 passes the first five facts; 3 fails one
projected-mode reduction and one unused-simp warning; 4 fails two uses of
Syscall where the runner needs Operation; 5 passes all eight facts; 6 passes
the reordered exact split and all standard-only roots, without diagnostics.
Recovery declarations from failed probes are not accepted trust evidence.
The installed scoped build passes 291 jobs, with only inherited Env:865
String.mk. The axiom audit checks 1,207 logical roots in 227 modules,
including 738 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes the changed terminal root. The subsequent
comment-only clarification rebuild also passes 291 jobs.
Static trust/import checks, all 258 original terminal names/order and the
mirror/shared-layer boundaries pass. No cap/limit increase, suppression or
infrastructure rerun occurs.

Current totals: 2,417 theorems in 824 owned modules and 341 headlines.
All six results remain in progress; the inherited full gate remains FAILED
and is not rerun unchanged. Reproduce with scoped build, axiom inspection
and fresh replay of Leanux.Proofs.WG.Progress.Statements under
capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: complete finite mixed-width getter

The original wgGetDevice now returns the exact single-peer JSON for a finite
readable allowed-IP list of arbitrary stored widths, under an exact receive
count of at most 4096. Greedy pages use the actual 28/40-byte costs. The count
includes each DATA envelope and an extra DONE envelope precisely when the
final DATA leaves less than 20 bytes. Empty input and a nonempty input with
an empty first fitting prefix retain their distinct raw attribute shapes.
Coalescing preserves every original occurrence in order.

Static premises are one listed resident peer, its exact list and node
residency, first-header and conditional nest room, resumed cursor freshness
against all earlier emissions, an idle empty socket7 and interface selection.
No actual callback/receive success, readiness or global ownership invariant is
assumed. IDs may repeat away from resumed boundaries; endpoints remain
arbitrary. Non-32-bit stored nodes use the original family-6 mask/hex branch,
without claiming those arbitrary widths are valid IPv6 configurations.

The source derives an internal indexed receive receipt from actual first and
resumed callbacks, including exact socket state at every receive. That receipt
is not a public premise. The existing getterReceive_sequence supplies the
only getter-loop induction; no IPv4 drain layer or shared frame is copied.
The final total-return theorem preserves the entire Device and gives the
exact completed, empty socket. The source count is also the number of receives
constructed by that receipt.

WeightedGetterModel holds count/message/freshness definitions and the pure
resumed-prefix equation. WeightedReceiveSource, WeightedTailSource and
WeightedGetterSource hold actual transport, coalescing and whole-call
composition; WeightedGetterClaims and Statements expose the projection.
Five definitions and ten theorems in five modules bring H4 to 712 theorems
and 94 headlines. No new frame is needed. Root independent review of all
files, planner and existing receive contracts finds no issue.

Nine changed-source probes: 1 fails constructor/layout syntax with recovery
warnings; 2 fails an array conversion name; 3 fails transitivity, array
rewrite, positivity and termination arithmetic, plus a deprecated rewrite;
4 fails array normalization and a deprecated integer rewrite; 5–6 fail
nil-array/freshness layout; 7 fails record-update normalization. Failed
recovery/sorry or misleading empty-axiom reports are rejected. Probe 8
passes all ten mathematical roots; 9 passes the corrected literal terminal
namespace. Both final passes have only standard axioms and no warnings.

Root installation also catches a namespace guard mismatch before wiring the
headline. The intervening cached old-root build is not evidence for the new
package. After correcting the installation, the new scoped closure passes
337 jobs, with only inherited Env:865 String.mk. Axiom inspection checks
1,181 logical roots in 273 modules, including 803 public theorem roots,
standard-only and without diagnostics.
Fresh kernel replay passes the changed Config terminal root.
Static trust/import checks, all 258 original terminal names/order and
mirror/shared boundaries pass. No cap/limit changes, suppression or
infrastructure reruns.

Current totals: 2,427 theorems in 829 owned modules and 342 headlines.
Multi-peer pagination, broader mixed setters, ownership and queued cleanup
remain open; no whole charter result is completed. The inherited full gate
remains FAILED and is not rerun unchanged. Reproduce the build, axiom
inspection and fresh replay of Leanux.Proofs.WG.Config.Statements under
capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H2 continuation: successful session publication with an aliased old slot

The [session-alias finding](2026-10-17-proof-campaign-2-session-alias.md)
checks an entry satisfying table safety, hashed-owner coherence and the key
store bound. Its old previous slot names the absent next allocation ID.
The original beginSession allocates that key, releases it during responder
rotation, then publishes its index row and returns true. Its immediate
original lookup stops at the missing owner object. Numeric table safety
survives, but owner coherence does not. Actual allocation/birthdate records
and the derived release readiness retain arbitrary other native/Ambient
fields; no successful intermediate execution is supplied.

This tests a local invariant, not initialized reachability. The checked C
ordering agrees, but no reachable C-state argument is made. No mirror
repair is requested. The alternative positive handoff architecture needs
the existing SessionRotationFresh premise; adding it would name an unresolved
caller obligation, not derive it from the three tested invariants.
The actual-effect witness instead settles their insufficiency without
copying a shared family. Primitive uniqueness, exact lookup and collision
clauses were already checked; broader initialized driver coherence remains
open.

SessionAliasModel gives eight witness/input definitions and the entry
invariants. Source derives the real rotation effect, total session return and
exact lookup Stop; Claims and Statements expose both executions over the
projection. Six theorems in three modules, including one private effect fact,
bring H2 to 487 theorems and 90 headlines. Independent source/domain review
finds no issue.

Probe 1 fails three role/cursor/count reductions with one unused-simp warning;
2 passes the session witness; 3 fails one final throw/string normalization;
4 passes the full finding; 5 passes the exact split and all six standard-only
roots; 6 checks Model alone with its narrower imports. Final probes have no
warnings. No frame or shared variant is added.

## H3 continuation: whole data admission preserves endpoints

The original consumeData now preserves the full optional endpoint map and
every remote destination on normal return, from arbitrary initial state.
Actual lookup and key acquisition derive the references needed by cleanup.
The no-key, dead-peer, successful enqueue, full peer queue and full device
ring arms remain, including EPIPE's real pure-callback publication. Endpoint
presence is retained as well as its full value. Missing owners, NULL words,
overflow, malformed queues and hidden-input failures keep their actual Stops.

This is before decryption and NAPI; it does not establish queued packet
authentication provenance or frame arbitrary later callbacks. Two named
local frame variants match C1 WGMore.enqueuePerDeviceAndPeerRx_spec and
enqueuePerPeerRx_pure_spec. Their SkbM reasoning follows the component
writeback locally. A private pure peer-map fact completes Frames; Source
proves the whole original operation; Claims and Statements use the campaign
projection. Six theorems in three modules bring H3 to 196 theorems and
19 headlines, without new definitions or changed old claims.

Independent review finds no issue and confirms reference effects are derived,
including actual owner-word dereference during EPIPE publication. Probe 1
fails seven record/witness/component-type errors; 2 fails five projection/
metavariable errors and two unused-simp warnings; 3 passes both queue frames;
4 fails one local-predicate unfolding; 5 passes the whole contract; 6 passes
the exact split and all six standard-only roots without warnings.

The broader architectures remain distinct: completing authenticated setter
receipts still needs substantive preservation through send/session/release
suffixes; persistent decrypt/NAPI authentication needs packet occurrence and
queue/lifetime history beyond current optional-endpoint frames. Both overlap
larger C1 layers and are not copied locally. Arbitrary initial CRYPTED packets
or arbitrary callbacks do not establish authentication.

Combined scoped build passes 433 jobs, with only inherited Env:865 String.mk.
The audit checks 1,668 logical roots in 369 modules, including 1,096 public
theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes both changed terminal roots.
Static trust/import checks, all 258 original terminal names/order and mirror/
shared boundaries pass. No proof-limit/cap change, suppression or infrastructure
rerun occurs. Totals: 2,439 theorems in 835 owned modules and 344 headlines.
All H1–H6 remain in progress; the inherited full gate remains FAILED.
Reproduce the scoped build, axiom inspection and fresh replay of
Leanux.Proofs.WG.Index.Statements and Leanux.Proofs.WG.Roaming.Statements
under capped/scripts/in-bundle, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H6 report audit correction

Independent audit found stale base-report prose that promised total success
for four supplied-record contracts now expressed as Product agreement:
retransmit-hook, initiation-send, named send-worker and absent-zero-key
give-up. Those paragraphs now retain the actual clock/wheel/release/section
refusals. The worker paragraph also now derives pending from residual queue
membership rather than claiming every dequeue clears it.

The selected retry-unit theorem remains a successful-outcome theorem under
its stated domain; its report now names that unit instead of outer fireTimer
selection, and includes wheel/pass-step effects. Pending-zero-key give-up
likewise remains total on its own stated domain. Current episode/block
coverage and the narrower meaning of the initialized give-up finding replace
stale gaps. No H6 theorem changed and no new H6 proof credit is taken.

The same audit corrects a stale backlog-table carry status and labels old
validation counts as historical. These are report repairs. Remaining H6 work
includes broader caller-local all-mode hook effects and the inventoried
cross-call lifetime/counter transport. Firing fairness and universal arbitrary
history decomposition are separate stronger questions. No new mirror request.


## H2 continuation: actual session-to-lookup handoff

The original beginSession followed, on true, by the original indexLookup now
returns the newly allocated keypair owner and its peer on every normal return.
Final table safety and hashed-owner coherence are measured after that same
lookup. False session returns skip lookup and preserve the Device exactly;
Ambient rollback is not claimed. Publication is tied to the entry's actual
handshake row.

SessionRotationFresh remains an explicit caller/lifecycle premise alongside
resident peer, table safety, owner coherence and the handshake row. The
session-alias finding proves those other local invariants cannot supply it.
No hidden-record readiness, successful intermediate execution, key-store bound
beyond table safety or reference ceiling is added; overflow and all actual
source Stops remain. This is a local handoff, not an initialized-history
freshness theorem.

SessionLookupSource contains the actual sequencing definition, published-row
lookup fact and composition. SessionLookupClaims and Statements expose the
projection. Four theorems in two modules bring H2 to 491 theorems and 91
headlines. No new frame or shared variant is needed. Independent review finds
no issue and checks every normal-none cause and the post-lookup invariant.

Probe 1 fails ten proof/reduction/field/name errors and seven warnings, including
deprecated/unused simplification; changed probe 2 checks both source facts;
probe 3 checks the exact split and all four roots with standard axioms only
and no warnings.

## H4 continuation: weighted mixed and private-key get-after-set

Both existing mixed fwmark/scalar and established private-key setters now
compose with the whole finite mixed-width getter. Every getter input is
derived from the same actual setter successor. Equal serialized device/peer
prefix sizes preserve the weighted boundaries, freshness and exact receive
count, including empty input, an empty first emitted prefix and separate DONE.
Private-key capacities use the effective installed identity, including clamping
and null-key behavior.

The mixed request retains source/cache clearing and earlier writes before a
malformed later peer returns -EINVAL. The key request retains actual expiry
time and ordered final Device effects. Both claims retain the existing setter
domains and the singleton resident/listed-node, capacity, boundary-freshness,
4096-receive and idle socket/selection getter domain. Endpoints and stored
node widths remain arbitrary; the original serializer supplies mask/JSON
behavior without asserting arbitrary widths are valid IPv6 configurations.
No callback-success or reset-record readiness premise is introduced.

WeightedPaginationCapacityFrames holds the one pure preservation fact;
MixedWeightedPaginationClaims, KeyWeightedPaginationClaims and Statements
hold projected claims. Five theorems, zero definitions and three modules bring
H4 to 717 theorems and 96 headlines. Existing IPv4 signatures are unchanged.
The first default-limit capped probe passes all five roots with standard
axioms and no warnings. Independent review finds no issue.

Combined validation: the scoped build passes 561 jobs with only inherited
Env:865 String.mk. Axiom inspection checks 2,158 logical roots in 497 modules,
including 1,485 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes both changed terminal roots. Static trust/import
checks, all 258 original terminal names/order, and mirror/shared-layer
boundaries pass. No raised limits/caps, suppression or infrastructure rerun.

This package adds nine theorems, five modules and three headlines:
2,439/835/344 before, 2,448/840/347 after. H1, H3, H5 and H6 counts are unchanged;
every result remains in progress with its remaining scope in the top table.
The inherited full gate remains FAILED and is not rerun unchanged. No new
mirror request arises. Reproduce the scoped build, axiom inspection and fresh
kernel replay of Leanux.Proofs.WG.Index.Statements and
Leanux.Proofs.WG.Config.Statements under capped/scripts/in-bundle with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H6 continuation: all-mode authenticated receive traversal

Both original handshake receiver observers now retain their authentication and
recorded-hook facts and add exact immediate persistent-keepalive effects in
either record mode. Normal hook execution derives the resident Device/peer
from its actual read. Nonzero interval, running Device and live peer select
the complete existing peerTimerArmEffect with interval times HZ; otherwise
the WG projection is unchanged. Ambient log rollback is not asserted.

Missing Device/peer and clock/wheel refusals remain actual Stops. In the
nonzero-interval arm, the original clock read precedes the running/dead guard.
The existing capture records the same hook's entry and successor and executes
the real hook once; the clock probe is inspected separately. Disabled paths
do not treat the probe as a required actual read. Existing exact full-receiver
erasures preserve every error, including later sender/session/release failures.
A successful observer receipt concerns its immediate hook boundary, not final
expiry, delivery or a receipt returned after a later Stop.

ReceiveTraversalAllModeModel contains one projected effect predicate;
ReceiveTraversalAllModeSource contains three source/capture facts;
ReceiveTraversalAllModeClaims and Statements contain two projected caller
claims and two literal headlines. Seven theorems in three modules bring H6
to 490 theorems and 61 headlines. No new observer, frame file, shared variant,
readiness premise or change to an old signature is needed. Independent review
checks actual residency, both modes, disabled guards, authentication receipts
and same-run capture, finding no issue.

Changed probe 1 fails three proof-form errors (two unreduced error branches
and a variable removed by substitution), without warnings. Probe 2 checks the
combined proof; probe 3 checks the exact split and seven standard-only roots,
without warnings. Scoped build passes 336 jobs, inherited Env:865 String.mk
only. Axiom inspection checks 1,452 roots in 294 modules, including 826 public
theorem roots, standard-only and without diagnostics. Fresh replay passes
TimerDiscipline.Statements. Static trust/import, original 258-name/order and
mirror/shared boundaries pass. No proof-limit/cap change or infrastructure rerun.

Totals move from 2,448/840/347 to 2,455 theorems/843 modules/349 headlines.
The other five counts are unchanged. Outgoing/data caller all-mode compositions,
cross-call allocation transport and session-relative counts remain open.
Reproduce the scoped build, axiom inspection and fresh kernel replay of
Leanux.Proofs.WG.TimerDiscipline.Statements under capped/scripts/in-bundle
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H2 coverage audit

Independent audit finds the core named-operation clauses checked: numeric
uniqueness is preserved by index insertion, removal, replacement and actual
handshake/session creation; lookup has exact owner/empty/error outcomes;
recorded collisions retry as the source does. The principal terminal contracts
are original_index_insert, original_index_remove, original_index_replace,
original_begin_session_indices, original_index_lookup_success,
original_index_lookup_none, original_index_insert_recorded,
original_index_insert_exhausted and original_session_lookup_handoff.

Here live means simultaneously published receiving-index owners within one
Device. Retained unhashed objects do not reserve their former number, and
peer-supplied remote indices are a separate namespace. Numeric uniqueness,
embedded-owner uniqueness, owner residency and slot/reference lifetimes are
distinct. The session-alias finding is not a duplicate-index or wrong-return
counterexample: numeric safety survives and lookup Stops. Its positive
counterpart explicitly retains SessionRotationFresh.

These local contracts do not establish equivalence to whole initialized driver
histories. The audit distinguishes that broader lifecycle/Runner closure from
the named-operation H2 claim; additional isolated owner-coherence leaves would
not by themselves establish the former. One optional
consolidation would compose existing owned contracts into a finite native
index history from an empty table. The full-driver architecture instead needs
the deferred header/CPU, outer removal, decrypt/NAPI and environment layers;
those are inventoried, not copied.

The aggregate gate is still FAILED, not a scoped pass: inherited
CounterWindow.Refinement references flattened World.steps/World.k and old
monadic runs; ReplayWindow.Counterexamples references Runner.initialKernel,
World.k and old peer-word types. The recorded 62 errors, 22 warnings and
metavariable panic occur before the axiom stage. Campaign 1 owns these repairs.
No whole-result gate completion or initialized-driver theorem is claimed.


## H6 continuation: outgoing and data traversal callers

Outgoing initiation and response, createDataDone and raw consumeDataDone now
retain their existing observations and add exact all-mode immediate traversal
effects. Existing source erasures preserve the original operation, return
values, early exits and every Stop. No new observer or readiness premise is
introduced. Initiation's hook remains conditional on message creation;
response's remains conditional on actual session success. Common received
response traversal, proved in the preceding tranche, does not require that
success.

createDataDone traverses once before its item loop, including an empty list;
the theorem does not count one traversal per packet. Raw consumeDataDone
records its real endpoint/confirmation/keep-fresh prelude, traversal, receipt
gating and original validation/routing suffix. It supplies no upstream
authentication or inner-packet acceptance proof. All effects are measured at
the same actual hook boundary; later sends, release, error or timer changes
are retained, not turned into final-expiry or delivery guarantees.

OutgoingTraversalAllModeClaims and DataTraversalAllModeClaims hold four
projected caller claims; Statements adds four literal erasure/consequence
wrappers. Eight theorems in two modules, no definitions, frames or shared
variants. Root source inspection finds five direct timersTraversal call sites:
two in Handshake and one each in Receive, Data and RxData. The common received
handshake site is exposed by two observer branches, yielding six checked
all-mode caller statements. This local coverage is not global history or
decrypt/NAPI authentication closure.

Probe 1 fails fifteen parser/cascade errors caused by a reserved local name.
Probes 2 and 3 exit zero but each emits one unused-simp warning; both are
rejected as validation. The author corrects an initially mistaken clean-output
status after inspecting the saved logs. Changed probe 4 removes the unused
argument and checks the exact split and all eight standard-only roots without
diagnostics. No warning suppression, limit/cap increase or infrastructure rerun.

The installed scoped build passes 338 jobs, inherited Env:865 String.mk only.
Axiom inspection checks 1,460 logical roots in 296 modules, including 834 public
theorem roots, standard-only and without diagnostics. Independent review finds
no issue. Fresh kernel replay passes TimerDiscipline.Statements; static trust/
import, original 258-name/order and mirror/shared boundaries pass.

H6 now has 498 theorems and 65 headlines. Totals move from 2,455/843/349 to
2,463 theorems/845 modules/353 headlines; the other five counts are unchanged.
Cross-call allocation transport, session-relative counting and broader
history/authentication composition remain open. The inherited full gate
remains FAILED, not rerun unchanged. No mirror request arises. Reproduce the
scoped build, axiom inspection and fresh replay of
Leanux.Proofs.WG.TimerDiscipline.Statements under capped/scripts/in-bundle
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## Coverage audit: H1 and H5

H1's seven whole-call tag maps and finite actual histories cover the native IK
edge clauses. Each slot's Option type gives one value per slot, not pairwise
distinct slots or a three-object store bound. Ordered rotation/clear/expiry
contracts retain aliases and the initiator-with-next arm. The remaining core
confirmation obligation is across fresh installations: consecutive-confirmation
contracts exclude intervening installation, and direct helper reinstallation
is not an initialized accepted-run witness.

The historical six-family transport inventory is no longer the minimum after
newer owned acquisition/cleanup contracts. Actual acquisition supplies a
retained reference for rejected consumption; exact peerPut decrement prevents
deletion of that held peer. The next bounded architecture composes owned
consume/create source shapes and cursor effects, then a finite native history
under an explicit initial next-ID-below-cursor premise. C1's lifetime projection
omits slots and the Device cursor; extending it and all callers is a distinct
larger architecture. This audit takes no fresh-history proof credit.

H5's outer finite recursion is separate from finite execution of its loop-backed
helpers. At this audit the modular-power bridge was checked and general exact-count
allocation remained beyond the single-site successful case; the later exact
finite allocation tranche closes that iteration gap. Total logical denotation
alone is insufficient. Record-budget adequacy is a further separate obligation.
Existing dispatch/turn/resumption contracts connect the recorded choice to the
real activation, including detached-state rerun and all failures. Fairness and
unconditional successful resumption are stronger than relative progress.

Another substantive H5 gap is initialized accepted-operation pending-unit consistency.
RunnerBoundaryClean checks only consumed records, no suspended activation and
netRxRaised=false. afterBatch's recorded guard explicitly omits pendingWork and
relies on an unproved pending-to-queue relation. Later syscall worker/timer tails
also prevent transporting an earlier drain cut directly to the final boundary.

One architecture establishes the initialized relation through queue production,
section-start clearing, physical ring transitions, NAPI, retirement, syscall
tails and Runner.executeTrace. It overlaps C1 Queues/RingGeometry, RingSteps,
RingJournal, RxScheduleHistory, RxEnvBatchHistory, JointSyscalls and JointRunner;
those layers are not copied, and their erasures alone do not supply the relation.
The alternative investigates a current initialized accepted trace with an actual
pending boundary. A rejected prefix or manufactured successor cannot settle
this. Placeholder/recordless bookkeeping must be distinguished from supplied
record execution.

The old accepted backlog is now a proved refusal on the current mirror.
QueueRefill is an initialized executable prefix rejection; arbitrary cookie
ring witnesses refute their stated local domains. None supplies a current
kernel-proved accepted pending-unit trace. Investigation remains open and may
find no witness. Independent audits found no theorem defect in the inspected
coverage. Stale terminal-lag wording in backlog, removal and timer notes is
corrected; no proof counts change and the inherited aggregate gate remains FAILED.


## H1 continuation: exact fresh-installation transport support

Original consumeInitiation and createResponse now preserve the exact pair of
optional allocation cursor and optional tracked-peer next slot on every normal
return. The nested option distinguishes an absent peer from a resident peer
with no next key. Native source transports require no initial bound. Projected
claims carry the named FreshNextBound from a captured entry; they do not derive
it from residency or assert successful creation, fresh allocation or reachability.

Actual lookup supplies the extra reference used by rejected consumption.
The existing exact retained-put contract then proves cleanup cannot delete
that held peer. Ordinary refusal, missing/NULL inputs, overflow and all original
Stops remain. Response creation uses the actual index adapter; no general
deletion-capable release layer is copied.

FreshInstallModel contains the data view and projected bound. After the later
acquisition-contract relocation, FreshInstallFrames contains two native predicates
and five preservation facts; FreshInstallSource contains the acquisition effect
and two whole-operation transports; FreshInstallClaims contains two projected
contracts. Four named variants correspond to shared modifyPeer, pubkeyLookup,
consumeInitiation and createResponse contracts. Owned lookup/retained-release,
crypto, index-adapter and observer-erasure support supplies their substantive
dependencies. Ten theorems and four definitions in four modules; no new H1
headline or fresh-history claim. Independent review finds no issue.

Probe 1 checks five frame roots; 2 fails one implicit transformer inference
without warnings; 3 checks all ten declarations; 4 checks the exact split
proof bodies/import union and ten standard-only roots; 5 checks Model alone.
The last changes before installation are docstrings only. All final checks
are warning-free at unchanged defaults. H1 now has 245 checked theorems and
33 headlines. The finite fresh-installation history remains the next step.

## H5 continuation: accepted placeholder pending identity

The [placeholder finding](2026-10-17-proof-campaign-2-placeholder-pending.md)
checks actual initialized runner acceptance with placeholders=true and no
supplied records. Its final audited boundary retains the receive-worker
pending identity while satisfying the specified queue-empty/count/NAPI tests,
with no suspension or raised NET_RX. The theorem extracts the same actual
audit/cut and uses its exact erasure to the original runner.

This is a mode-specific bookkeeping finding, not evidence of an unexecuted
unit, general physical-ring coherence or supplied-record progress failure.
The actual hidden-input implementation clears pending identities on section
start only in its supplied-record branch; the placeholder branch returns first.
The constructed supplied-record completion control runtime-accepts with no
pending identity. No kernel acceptance theorem is claimed for that control.

PlaceholderBoundaryModel has the two concrete traces and Boolean audit predicate;
Source kernel-checks the predicate; Claims and Statements extract the actual
acceptance and cut. Three theorems, three definitions and three modules add one
headline. H5 now has 329 checked theorems and 50 headlines. Independent review
confirms the mode, same-run extraction and exact test scope.

Seven compiler invocations: 1 fails an invalid diagnostic field; 2 executes a
rejected candidate with an eight-byte UDP steer; 3 runtime-accepts the corrected
four-byte placeholder trace; 4 runtime-accepts the supplied-record control;
5 kernel-checks the Boolean; 6 fails a wrapper matcher rewrite (recovery axioms
rejected); 7 closes all three roots but emits an unused-simp warning, so is not
accepted as clean validation. Removing that argument is checked by the root
installed build. Three distinct trace inputs are tested; no infrastructure
rerun or changed proof limit/cap occurs.

The first combined installed build closes all support but fails the new literal
headline on an unqualified Runner.executeTrace, with two diagnostics. Qualifying
it fixes the packaging error. The corrected build passes 314 jobs, inherited
Env:865 String.mk only. Axiom inspection checks 1,300 roots in 250 modules,
including 779 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes both changed roots. Static trust/import,
original 258-name/order and mirror/shared boundaries pass.

Totals move from 2,463/845/353 to 2,476 theorems/852 modules/354 headlines.
Other result counts are unchanged. The inherited aggregate gate remains FAILED;
no unchanged full-gate rerun or new mirror request. Reproduce the scoped build,
axiom inspection and fresh replay of Leanux.Proofs.WG.Noise.FreshInstallClaims
and Leanux.Proofs.WG.Progress.Statements under capped/scripts/in-bundle with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: actual endpoint setter and weighted readback

The original setPeerCmd endpoint request now has exact normal-return effects
for a found, positively referenced peer on a stopped device, with the explicit
acquisition ceiling. Existing-peer UPDATE_ONLY is covered. Invalid length/family
encodings are ignored; valid IPv4/IPv6 attributes follow the actual defaults and
field conversion. Endpoint comparison omits IPv6 flowinfo, so equality retains
the stored value. A change writes the endpoint, retains the cache slot and
optionally updates its reset timestamp. Acquisition and release stores balance.
No reset-record availability or successful-return premise is supplied.

The whole wgSetDevice composition increments the generation and retains these
writes before a later malformed peer returns -EINVAL. The following actual
weighted getter runs from that same successor. Its capacities, freshness and
exact DATA/DONE bound use the effective post-set endpoint, which may change
family and serialized size. Singleton/readable-node/header-room/idle-empty-socket
premises remain explicit. Exact JSON, final socket and ordered Device effects
are proved, including arbitrary stored allowed-IP widths under the serializer's
existing semantics. This is not a general mixed-request or running-peer theorem.

EndpointSetModel contains ten pure definitions; EndpointSetSource,
EndpointAttributeSource and EndpointRequestSource connect the real operations
and their one local endpoint-attribute factor. EndpointSetEffects proves the
exact resulting fields and serialization, including preservation conjuncts;
it is a substantive effect claim rather than a standalone frame-only layer.
EndpointSetClaims and the two new Statements declarations use the campaign
projection. Existing separate readback/capacity frames are reused. Six new
modules, eleven definitions and sixteen theorems including one private proof;
no shared variants or shared-layer duplication. Independent review finds no issue.

Development uses eleven changed-source probes. Probes 1–10 fail with respectively
2/0, 10/3, 30/2, 6/5, 2/0, 2/0, 7/1, 7/1, 7/0 and 7/1 errors/warnings.
These cover comparison/StateT normalization, attribute/acquisition lookup,
UPDATE_ONLY and device binds, and finally getter field/capacity transport.
The initial ten-probe tranche ends with source contracts closed and getter
composition unresolved; a separate narrowly bounded getter tranche repairs
that proof without changing its premises. Its first probe (11 overall) passes
all fifteen public theorem roots with standard axioms and no diagnostics.
Recovery sorry axioms from failed probes are rejected. No infrastructure rerun,
warning suppression, proof-limit or memory-cap change occurs.

The installed scoped build passes 346 jobs; only inherited Env:865 String.mk
warns. Axiom inspection checks 1,212 roots in 282 modules, including 823 public
theorem roots, standard-only and without diagnostics. Fresh Config.Statements
kernel replay passes. Static trust/import, original 258-name/order and
mirror/shared boundaries pass.

H4 moves from 717/96 to 733 theorems/98 headlines. Campaign totals move from
2,476/852/354 to 2,492 theorems/858 modules/356 headlines; other result counts
are unchanged. Global allowed-IP ownership, initial-to-post-free replace-peers
transport, queued cleanup, general mixed requests and multi-peer pagination
remain open. The inherited full gate remains FAILED and is not rerun unchanged.
No mirror-team request arises. Reproduce the scoped build, axiom inspection
and fresh replay of Leanux.Proofs.WG.Config.Statements under
capped/scripts/in-bundle with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H1 continuation: distinct confirmations across actual installations

A finite language now dispatches the original consumeInitiation, createResponse,
beginSession and receivedWithKeypair calls for one tracked peer. Observations
record the actual consecutive entry/exit projections and full return values.
Unconditional erasure preserves the original computation, concrete states and
first Stop; a stopped execution does not manufacture a successful receipt list.

Under the sole initial FreshNextBound, successful confirmation numeric IDs are
pairwise distinct throughout any normally completed sequence. Actual session
success advances the allocation cursor and sets next to the old cursor or none;
confirmation clears next; the setup calls preserve the cursor/next view.
The induction records prior successful IDs below the cursor and absent from next.
No readiness, reference ceiling, successful-prefix, owner coherence or distinct
slot premise is added. Arbitrary aliases and their release failures remain.

The earlier unrestricted direct-helper reinstallation counterexample remains
valid. This positive theorem excludes that helper, peer recreation and device
reset; it does not claim initialized-driver closure, full handshake-call coverage,
key residency or allocation-lifetime identity beyond this numeric-ID language.
The initial bound is explicit rather than inferred from a reachable-state claim.

FreshHistoryModel holds the operation/receipt data and pure predicates.
FreshHistoryEffects holds five substantive transition/invariant facts;
FreshHistorySource holds the three original-call effect/erasure facts;
FreshHistoryClaims holds two projected contracts. Statements adds one headline.
Independent review identifies the original Frames filename as inaccurate for
changing-state effects; renaming it to Effects and updating its import resolves
that finding without changing a proposition or proof. Semantic review finds no
remaining issue. Four modules and eleven theorems, no shared variants.

Seven development probes: 1 fails four proof errors and two unused-simp warnings;
2 checks the pure support; 3 and 4 each fail two reduction/matcher errors without
warnings; 5 checks the complete candidate; 6 checks the exact split/import
closure and all eleven standard-only roots; 7 checks the narrow Model alone.
Successful probes are diagnostic-free. No limit/cap change or infrastructure rerun.

Both initial and renamed installed builds pass 175 jobs without diagnostics.
Axiom inspection checks 704 roots in 148 modules, including 421 public theorem
roots, standard-only and without diagnostics. Fresh Noise.Statements replay,
static trust/import, original 258-name/order and mirror/shared boundaries pass.
H1 moves from 245/33 to 256 theorems/34 headlines; totals move from
2,492/858/356 to 2,503 theorems/862 modules/357 headlines. Other result counts
are unchanged. The inherited aggregate gate remains FAILED, not rerun unchanged.
Reproduce with the scoped build, axiom inspection and fresh kernel replay of
Leanux.Proofs.WG.Noise.Statements under capped/scripts/in-bundle, using
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 architecture audit: pagination between peers

The existing fitting multi-peer getter and weighted singleton getter cannot
simply be composed. A cross-peer callback retains the last completed peer as its
cursor, acquires the next retained cursor before releasing the old one, and may
omit device metadata on resumed pages. Its Device changes through those reference
stores. A dead held cursor ends the original callback normally with later peers
omitted. The current singleton receive theorem fixes one Device and full metadata;
these are interface restrictions to generalize openly in the owned layer.

Canonical full pagination needs boundary-cursor freshness against earlier peer
occurrences, local allowed-IP cursor freshness, live held peers and the actual
acquisition bounds. Repeated held cursors can temporarily require two extra
references above baseline. Full list/key uniqueness must not be imposed merely
for convenience: completed peers with equal public keys remain separate in the
coalescer; the continuation identifies its own occurrence. Ordered map writes
remain explicit until structural Device equality is actually proved.

[AGENT 2026-10-17] Develop an exact fixed-peer cursor-handoff package first, then
generalize owned receive/coalescing transport. This provides actual multi-peer
pagination without simultaneously adding the nested weighted-IP planner.
The alternative nested planner needs the same cursor/ref transitions plus
lexicographic progress and split-fragment coalescing. Both architectures reuse
the existing peer-loop body and weighted scan leaves; no C1 layer is copied.
This audit adds no theorem credit or accepted-run counterexample. The genuine
remove-all/global-ownership shared dependencies remain separate.


## H6 validation follow-up: give-up execution reduction

The bounded attempt to turn the initialized give-up runtime witness into a
closed execution theorem fails after six development probes; it adds no proof
credit. Actual runtime checks remain true, but decide +kernel cannot reduce
the first wgSet call's proposition. This is neither a semantic counterexample
nor a kernel rejection. The [finding note](2026-10-17-proof-campaign-2-initialized-giveup.md#attempt-to-obtain-a-closed-execution-theorem)
records every failed probe, the rejected recovery axioms and both continuation
architectures: a proved finite-computation bridge or actual per-operation source
composition. Defaults/caps remain unchanged; no infrastructure rerun occurs.
H6 remains at 498 theorems/65 headlines and runtime-only initialized give-up
evidence. No mirror-team request follows from this reduction obstruction.


## H5 audit correction: logical totality and executable loops

Independent review finds the blanket termination justification in two earlier
coverage summaries and the register incorrect; those passages are corrected
in place. The toolchain's Init/While implementation gives repeatM a logical
denotation with a private partial implementation and an implemented_by erased
loop, and Lean.Loop.forIn delegates to it. Function totality alone therefore
does not establish a finite number of executable iterations.

Progress.PowSource supplies a checked fixed-point unfolding and finite-evaluation
bridge for the original modular-power loop. Noise.SessionReadySource supplies
the allocation-loop equation and the exact single successful kzallocKeypair
record case. It does not establish the general exact-n allocation loop over
arbitrary returns, errors and records. This is a proof-coverage/reporting
finding, not an observed nonterminating trace or mirror defect. Stock executable
overrides remain reported and are not used as proof oracles. The following
exact finite allocation tranche subsequently closes this specific iteration gap.

A minimal candidate at this audit was equality of the original allocation loop to a structurally
recursive evaluator with at most n encounters, retaining early false returns and
the first Stop. The actual encounter helpers must then be connected explicitly;
arbitrary callbacks cannot be declared terminating merely from their types.
The scope is WireGuard execution. Generic runner boundary theorems condition on
acceptance; they do not establish termination for all subsystem operations.
For example, the separate FS pipe path has its own loop-backed rounding helper.
Whole-operation fuel adequacy and initialized pending-work consistency remain
separate. No theorem count changes or full-gate rerun accompany this correction.


## H1 continuation: all named handshake lifecycle operations

The existing fresh-confirmation language now includes createInitiation,
consumeResponse, handshakeClear, expireCurrentPeerKeypairs and keypairsClear.
Together with the four previously checked operations, these cover all handshake
create/consume calls, session installation, confirmation, handshake clearing,
expiry and slot clearing for the tracked peer. The existing headline and all
eleven prior theorem signatures are unchanged; the operation/return inductives
and the history claim's coverage are extended.

The sole initial FreshNextBound still suffices. Both additional handshake calls
preserve the exact optional next/cursor view; response lookup derives its held
reference for every normal rejection cleanup. Handshake clearing and expiry
preserve next, while actual keypair clearing supplies the new clearNext effect
without rewinding allocation. Aliased releases and all original Stops remain.
No readiness, coherence, reference ceiling, static release budget or successful
prefix is introduced. This still excludes direct helper reinstallation, peer
recreation and device reset, and makes no global driver/lifetime claim.

FreshLifecycleFrames holds the owner-word/view preservation and ClearRun cursor
fact. FreshLifecycleSource holds the actual lookup acquisition and five whole-call
contracts. Three named shared-family variants correspond to index lookup,
initiation creation and response consumption; they compose existing owned source,
crypto, lookup and retained-release facts. No new shared lookup/crypto/release
layer is copied. FreshHistoryEffects owns the changing clearNext invariant case;
Model/Source/Claims retain the single existing observer/sequence architecture.

Independent review finds one placement issue: lookup derives an acquired reference,
so its mixed effect belongs in Source. The same correction is made for three
older owned acquisition contracts: the response-tag lookup moves to
ResponseTagSource, initiation-tag pubkey lookup to InitiationTagSource, and
fresh-transport pubkey lookup to FreshInstallSource. Their propositions and proof
bodies are unchanged; pure owner/view facts stay in Frames and are made public
where cross-file use requires it. This is a factoring correction, not a new
theorem or an edit to C1's shared layer. Review finds no semantic or domain issue.

Eight new support theorems in two new modules strengthen the existing headline.
Probe 1 fails one cursor definitional-equality application without warnings;
2 checks lookup plus both handshake transports; 3 checks all nine operations;
4 checks the split bodies and nineteen roots standard-only without diagnostics.
The final scratch edits are comments only. No proof-limit/cap changes or
infrastructure reruns occur.

A root packaging script copies the support files but fails while locating the
terminal comment. Incorrect unconditional shell sequencing then launches a build
before the required recovery snapshot; that process error is not treated as a
completed checkpoint. The build passes 177 jobs, but the dirty tracked/untracked
source state is subsequently preserved at recovery ref
refs/snapshots/campaign2-lifecycle-package-recovery-20261017T110512583822Z before
further edits. Corrected scripts validate all edits before writing and fail
closed before dependent commands. The literal comment is fixed and reviewed
acquisition relocations applied. The final Noise build passes 177 jobs without
diagnostics. No source is reset or discarded.

## H5 continuation: exact finite allocation loop

AllocationIterationSource identifies the original fixed-bound while loop with
a structurally recursive evaluator using at most n-k encounter invocations.
Early false returns retain the actual successor state and counter; an error
retains the exact Stop without manufacturing a successor. The generic theorem
does not infer executable termination of an arbitrary callback from its type.

AllocationProgressSource connects every actual hiddenAlloc branch to that
evaluator: exact counts including zero, lax/unrecorded success, below-cut
refusal and unarmed bypass. The record/placeholder choice is captured once at
entry as in the source. The evaluator calls the actual private native helpers;
paired source equations expose their original finite list/byte operations,
record handling and steering failures. No record shape, readiness, success
or state-preservation premise is supplied.

AllocationProgressClaims and the new literal original_allocation_finite headline
state exact projected agreement, including all errors. There are three support
modules, six theorems and three definitions; no frame file or copied C1 Allocation
layer. This closes the general exact-count allocation iteration gap identified
by the preceding audit, rather than using logical totality as a termination
argument. Scheduler fuel adequacy, initialized pending-unit consistency and
all-subsystem runner termination remain separate.

Ten changed-source probes: 1 checks the generic loop; 2 fails an unexpanded
source let; 3 fails five count-case/variable obligations; 4 fails source equality
and warns on an unused simp argument; 5–6 fail generated-matcher equality;
7 fails an alternate forIn spelling; 8 isolates the two Option continuation
matchers. The initial eight-probe tranche stops there. A narrowly bounded
matcher-correction tranche uses bind congruence and Option cases: 9 closes the
source bridge, and 10 checks the exact split package and six standard-only roots
without diagnostics. Failed recovery environments are rejected. No infrastructure
rerun, warning suppression, proof-limit or cap increase occurs. Independent
review finds no issue.

The combined Progress/standalone FreshInstallClaims build passes 318 jobs,
inherited Env:865 String.mk only. The H1/H5 axiom audit checks 1,612 logical roots
in 316 modules, including 985 public theorem roots, standard-only and without
diagnostics. All three fresh kernel replays pass (Noise.Statements,
Noise.FreshInstallClaims and Progress.Statements). Static trust/import, original
258-name/order and mirror/shared boundaries pass.

H1 moves from 256/34 to 264 theorems/34 headlines; H5 from 329/50 to 335/51.
Totals move from 2,503/862/357 to 2,517 theorems/867 modules/358 headlines.
The other results' counts are unchanged. The inherited aggregate gate remains
FAILED and is not rerun unchanged. Reproduce the builds, axiom inspection and
fresh replay of the three named roots under Leanux.Proofs.WG using
capped/scripts/in-bundle with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 attempted cursor tranche: native serializer still open

The ten-probe cursor tranche does not close its requested native milestone.
Only two pure greedy-prefix facts check: decomposition/capacity/first-refusal
and progress when the first peer fits. They are not installed or counted as
native H4 coverage. The first missing source fact is exact arbitrary-room
empty-IP serialization; callback cursor handoff and finite multi-peer transport
are not implemented.

Probe 1 fails six import/type/tactic obligations. Probes 2–3 fail respectively
four and six reduction/default-limit obligations. Probe 4 fails two obligations
around an unavailable progress tactic. Probe 5 fails three obligations beginning
with the symbolic first-put Bool.rec; 6 fails two. Probe 7's small/large helper
split fails three obligations and has two unused-simp warnings. Probe 8 fails
four default reduction obligations. Probe 9 fails an unavailable experimental
vcgen dependency and warns. Probe 10 passes only the pure model, standard-only.
All native recovery axioms and warned/failed drafts are rejected.

Direct path reduction and compositional branch contracts both reach default
simp/heartbeat limits. One separate root diagnostic changes the experimental
tactic to the earlier mvcgen spelling; it fails the same 200,000-heartbeat limit,
also reporting deprecated syntax, an unused simp argument and a downstream
unknown helper/recovery constant. That diagnostic stops after one probe.
No warning suppression, cap/limit increase, infrastructure outcome or rerun
occurs. These are proof-development failures, not semantic counterexamples or
mirror-team requests. A smaller exact source factor with one-put-at-a-time
contracts is the next architecture to assess; no stronger capacity/readiness
premise is introduced to force the original claim through.


## H4 continuation: exact fit or cancellation at arbitrary room

[AGENT 2026-10-17] Factor the fixed put chain and endpoint tail before
reasoning about capacity. Exact equality to the original getPeerDumpTailSource
holds for every context and room, including its resumed allowed-IP path and
all original errors. The proof unfolds only the local source factors and
literal lists; actual puts, branch effects and run semantics remain opaque.

The projected total getter claim assumes a resident peer, a fresh allowed-IP
cursor and an empty stored allowed-IP list. It has no capacity, liveness,
reference, endpoint-validity, record-readiness or supplied-success premise.
At exact sufficient capacity it returns the original attributes, subtracts
peerFixedSpace and resets only nextAllowedip/allowedipsSeq; otherwise it returns
the original skb/context and cancellation. Device and existing messages remain
unchanged. Fixed cost is 136 plus 20 for AF_INET or 32 for AF_INET6.
Other present endpoint families retain the mirror's original serializer and
zero endpoint-space accounting; this is not a reachable-endpoint or Linux
correspondence claim.

FactoredTailModel holds two result definitions. FactoredTailSource holds three
operational factors and their equality to the original. FactoredTailReturns
holds the put-chain induction and the endpoint/original-tail total contracts.
FactoredTailClaims holds the projected native getter claim, wrapped literally
as original_peer_dump_fixed_room in Statements. These are mixed return/effect
contracts; no preservation-only frame or shared-layer variant is added.
No cursor planner, callback reference handoff, multi-peer pagination or socket
transport is claimed by this step.

Nine changed-source probes: 1 fails the final syntax equality, fixed by
reflexivity in passing probe 2; 3 fails five endpoint witness-shape obligations
and warns once; 4 fails two unspecified witness obligations; 5 fails three
Boolean family normalizations and warns twice; 6 fails five composition/result
obligations and warns twice; 7 leaves two; 8 leaves the whole-contract
simplification mismatch. Probe 9 extracts the actual run and normalizes its
result locally, checking all five package roots standard-only without warnings.
The seven failed drafts and their recovery environments are rejected. This
successful architecture does not reclassify the earlier failed cursor or
mvcgen probes. No timeout, cap/limit increase or infrastructure rerun occurs.

The installed Config.Statements build passes 350 jobs, with only inherited
Env:865 String.mk. Axiom inspection checks 1,223 roots in 286 modules, including
829 public theorem roots, standard-only and without diagnostics. Fresh kernel
replay passes. Static token/import/root/default checks, the original 258-name
order and mirror/shared boundaries pass. The inherited aggregate gate remains
FAILED and is not rerun unchanged.

Independent source/domain review finds no issue.

Six new theorems including the headline bring H4 to 739/99 and campaign totals
to 2,523 theorems, 871 owned modules and 359 headlines. Other result counts
are unchanged. The next native obligation is ordered multi-peer cursor
handoff, including acquisition before the previous cursor reference is put;
the fit/cancel result now supplies its exact per-peer capacity behavior.

Reproduce with capped -- scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, axiom inspection of its proof closure,
and capped -- scripts/in-bundle lake env leanchecker --fresh
Leanux.Proofs.WG.Config.Statements, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. No mirror change is requested.

## H5/H6 continuation: exact finite power and curve evaluation

[AGENT 2026-10-17] Connect a successful finite square-and-multiply evaluation
to the original private modular-power loop by induction on evaluation fuel.
This improves the earlier exponent-sized adequacy bridge: a successful
256-step evaluation suffices for these concrete curve inputs without fuel
proportional to their large exponent. Exhaustion gives no conclusion and no
fallback value is used.

Progress/PowEvaluationSource holds the two exact evaluation contracts.
Progress/CurveEvaluationSource factors the original finite ladder immediately
before inversion and connects successful inversion evaluation to the original
X25519 output. The ladder equality is definitional source factoring, not a
cryptographic-specification claim. Progress/Statements adds the literal
original_pow_mod_of_evaluation headline. No frame is added.

TimerDiscipline/InitializedGiveUpCurveSource checks four original curve-output
facts for the tracked initialized give-up recipe: configured secret/basepoint,
secret/remote, ephemeral/basepoint and ephemeral/remote. The latter three
retain both raw and actual caller-clamped inputs. The recipe reuses the same
ephemeral value across initiations; different messages do not mean twenty
different curve inputs. Candidate arithmetic values were obtained at runtime,
but every installed equality is proved by kernel-checked finite evaluation.
There is no runner acceptance or timer-history theorem in this package;
the first initialized operation remains a separate open obligation.

Development: root probe 1 checks both power contracts; probe 2 fails the
ladder equality under rfl, and probe 3 fails two unavailable Id names and
its split. The continuation's probes 1--3 check the source factor, inversion
and configured output. Before probe 4, a recipe-extraction preparation
mistakenly selected a later repeated draw directive and failed before Lean;
using the actual generator's first three directives corrects it. Probe 4
checks candidate outputs. Probe 5 fails three default recursion-depth
obligations while identifying raw and clamped inputs. Probe 6 instead checks
their actual finite inversions independently; all eight support roots pass
standard-only without warnings. Failed recovery environments are rejected.
No warning suppression, limit/cap increase, timeout or infrastructure rerun
occurs.

The combined Progress.Statements/TimerDiscipline.Statements build passes
485 jobs, with only inherited Env:865 String.mk. Axiom inspection checks
2,130 roots in 421 modules, including 1,251 public theorem roots, standard-only
and without diagnostics. Both fresh kernel replays pass. Static checks,
original 258-name order and mirror/shared boundaries pass. The inherited
aggregate gate remains FAILED and is not rerun unchanged.

Independent source/domain/trust review finds no issue in the original loop,
ladder factor, finite inversion or concrete caller inputs.

Nine new theorems, including the one headline, bring H5 to 340/52 and H6
to 502/65; totals are 2,532 theorems, 874 owned modules and 360 headlines.
H1 264/34, H2 491/91, H3 196/19 and H4 739/99 are unchanged. All six
charter results remain in progress. The current summary's previous stale
358-headline count is corrected; the preceding H4 checkpoint had 359.

Reproduce with capped/scripts/in-bundle lake build on the two named
Statements roots, standard-axiom inspection of their proof closure, and
lake env leanchecker --fresh on each, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16. No mirror-team request arises from this proof
reduction work.

## H6 follow-up: first initialized operation remains open

The eight-probe first-operation tranche adds no theorem. It keeps all 23
operations, all supplied record batches and future lookahead from the generated
recipe, calls actual runnerInitial with placeholders disabled, then actual
runnerOperation for its first wgSet. The checked predicate would require return
zero, consumed records, no suspended activation and no pending NET_RX; errors
map to false. No state is reconstructed from a projection.

Probes 1--2 fail respectively a request layout error plus two default recursion
limits, then two recursion limits. Probe 3 isolates the curve-rule smoke failure
at the 32-element basepoint map. Probe 4 uses a kernel-proved literal basepoint
equality: curve reduction passes, but the whole operation still hits the default
recursion limit. Probe 5 locates eager expansion of the actual 4,096-slot initial
ring. Probe 6 checks a generic exact initial-ring empty rule, keeping init opaque
to cbv; the operation instead becomes stuck at the original FIB boot insertAlias.
Probe 7 proves its no-leaf logged insertNode equality by reflexivity and passes
that point, but the whole operation again hits the default recursion limit.

Probe 8 enables diagnostic tracing and is deliberately interrupted when it
continues producing no useful diagnosis. Only its verified own Lean PID is
sent SIGTERM. Exit 143 and capped's KILLED/signal banner are a failure, never
a passing or infrastructure-rerun result. No deeper failure location is inferred
from this interrupted probe. All eight outcomes remain failed; recovery axioms
are rejected. There are no warnings, cap/limit increases or infrastructure
reruns. The separately committed curve package retains its own successful
validation and does not receive whole-operation credit.

[AGENT 2026-10-17] Stop this reduction architecture at the bounded tranche.
The next alternatives are exact composition through an independently checked
actual initialization cut, or native setter/record contracts from that state;
do not copy a FIB or shared layer, alter the recipe, or increase limits to force
reduction. The full initialized give-up execution remains runtime-only.
H1--H6 statuses and the 2,532/874/360 census are unchanged. No mirror request
is warranted by a tactic reduction failure.

## H3 continuation: native NAPI owner and first-packet authentication

[AGENT 2026-10-17] Compose the original decryptStep with Env.napiSoftirq
and Env.napiIrqExit, observing the first pre-put poll prefix on its actual
state. Exact unconditional erasure retains both softirq calls, publication,
fixture scheduling choice, all polls, section records, peer release and every
original failure. The observer neither reconstructs state from its projection
nor substitutes a successful callback.

Actual publication derives a resident scheduled owner from the index owner
word. NAPI's own multiple-peer refusal then derives its selected owner,
without an owner-equals-packet-peer assumption. The queue-read contract covers
peeked and physically malformed queues on normal returns. If the observed
first poll reaches an endpoint setter and that owner's actual queue head
at publication is the published packet, packet identity follows; the earlier
authenticated decryption then supplies the AEAD plaintext, accepted counter
and immediate source endpoint. Entry precondition is True. The owner-head
condition is explicit in the conclusion's implication, not silently assumed
for all queue histories.

This is first setter-cut provenance. It does not establish every queued
packet's authentication, later poll iterations, final endpoint preservation
or initialized reachability. Skipped polling, including recordless pre-put
polling, remains possible. No stronger H3 result is inferred.

NapiPublicationModel contains projected cut/fact definitions. Source contains
the original NAPI factors, full observer and five exact source/erasure facts.
Frames contains the one genuine composite Product-to-WG preservation fact;
the Product computation's type alone does not give it. SelectionSource holds
four queue/poll provenance contracts, including PrevQueue_peek_head moved
from the draft frame file because it is a return-value fact. OwnerSource
holds five scheduling/selection contracts. Claims holds the projected
composition; Statements adds its literal original_native_napi_publication_authentication
headline. No shared-layer variant or mirror change is added.

The first twelve-probe tranche closes eight support theorems. Failed probes
1--11 have error/warning counts respectively 3/1, 3/0, 6/3, 1/4, 1/0,
4/4, 3/0, 2/1, 4/10, 4/3 and 1/0; failures cover source/erasure
normalization, getters and queue facts, including default heartbeat failure
in probe 9. Probe 12 passes without warnings. A separately bounded
continuation adds the actual owner linkage and final claim. Probes 13--18
fail with counts 12/0, 1/0, 4/0, 1/0, 3/0 and 8/2; these include
default recursion-depth errors, dependent elimination, singleton/result
normalization and reserved identifiers. Probe 19 closes the full claim;
20 checks all seventeen roots; 21 checks the reordered split bodies.
Those three pass without warnings and with standard axioms. Every failed
recovery environment is rejected. No limit/cap increase, warning suppression
or infrastructure rerun occurs.

Installed Roaming.Statements builds in 259 jobs with only inherited
Env:865 String.mk. Axiom inspection checks 1,098 roots in 225 modules,
including 643 public theorem roots, standard-only and without diagnostics.
Fresh kernel replay passes. Independent source/domain/trust review finds
no issue. Static checks, original 258-name order and mirror/shared boundaries
pass. The inherited aggregate gate remains FAILED and is not rerun unchanged.

Seventeen new theorems in six modules bring H3 to 213 theorems/20 headlines.
Campaign totals are 2,549 theorems, 880 owned modules and 361 headlines.
H1 264/34, H2 491/91, H4 739/99, H5 340/52 and H6 502/65 are unchanged;
all six charter results remain in progress. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Roaming.Statements, standard-axiom inspection of
its closure and lake env leanchecker --fresh on the same root, with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: native cursor body and ordered reference handoff

The original dump operation now factors unconditionally into its unchanged
header and an exact peer-body computation. The peer body combines the actual
empty/dead-cursor guard, ordered finite peer loop, original cancellation
branches and original cursor-reference finalizer. The body normal-return
contract gives the exact completed prefix, serialized attributes, context,
skb/messages and Device effect. Its cursor acquisition precedes the old
cursor read/release, including when both cursor IDs coincide.

Entry premises are a resident Device, resident selected suffix peers with empty
allowed-IP lists, a fresh allowed-IP cursor and a resident old cursor when
present. There is no capacity, sequence-consistency, liveness, distinct-list,
cursor-membership, reference-budget, record-readiness or execution-witness
premise. Arbitrary raw room is retained, including incomplete outputs whose
saturating ret arithmetic is zero. Successful last-reference release may
erase a peer/unhash its handshake and increment txDropped; original zero,
overflow, queued-work and timer refusals remain outside normal completion.
The body theorem is not totality or a whole-callback contract.

CursorCallbackModel contains seven pure transforms; CursorCallbackSource
contains four exact operational factors and two original equalities.
CursorLoopSource proves the native greedy loop and cursor provenance.
CursorHandoffSource proves successful release and ordered reference effects.
CursorBodySource composes the guard, loop and finalizer. These are mixed
return/effect contracts, not preservation-only frames. Statements imports
the eleven support theorems but adds no headline. Header continuation and
the projected whole callback remain open at this checkpoint.

Twelve changed-source probes: 1--2 fail with error/warning counts 4/5 and 2/2,
including default isDefEq timeout with an invalid draft definition. Probe 3
checks both source equalities but has one unused-simp warning. Probes 4--11
fail with counts 2/3, 1/0, 6/2, 9/0, 4/6, 3/0, 17/0 and 3/2.
They cover run/bind normalization, lookup witnesses, conditional syntax and
the header's default whnf limit. Dependent unknown-helper and self-axiom
recovery output is rejected, including the unaccepted header's misleading
empty-axiom print. Probe 12 checks only the eleven support roots, standard-only
without warnings. It does not reclassify the failed whole-callback draft.

Installation exposes a further module-boundary proof-form error in
CursorBodySource's selected-list join. Three scoped builds fail one error
each: the original general simp, a restricted simp, then explicit bind/list
normalization. An explicit case split on ctx.nextPeer closes it in build 4.
Only this proof changes; original statement and factors stay unchanged.
All failed outcomes remain failures. No limit/cap increase, warning suppression
or infrastructure rerun occurs.

The final Config.Statements build passes 355 jobs, with only inherited
Env:865 String.mk. Axiom inspection checks 1,245 roots in 291 modules,
including 840 public theorem roots, standard-only and without diagnostics.
Fresh replay, static checks, original 258-name order and mirror/shared
boundaries pass. Independent source/domain/trust review finds no issue.
The inherited aggregate gate remains FAILED and is not rerun unchanged.

Eleven new theorems in five modules bring H4 to 750/99; totals are 2,560
theorems, 885 owned modules and 361 headlines. Other counts and all six
in-progress statuses are unchanged. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Config.Statements, standard-axiom inspection of
its closure and lake env leanchecker --fresh on the same root, with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: whole normal callback through the actual header

[AGENT 2026-10-17] Factor the original header into AmbientM before composing
its continuation. Its type supplies unchanged WireGuard state; no extra
preservation frame is needed. A second exact factor exposes one put at a
time, so normal-return reasoning retains each original refusal without
unfolding the entire remaining continuation.

The projected wgGetDeviceDump claim now gives the complete normal callback:
actual first/resumed device attributes, consistency flags, exact successful
header room, ordered peer-prefix serialization/cancellation, prior messages,
cursor context and acquire-before-release Device effects. It retains the
body's explicit resident selected empty-IP suffix, fresh allowed-IP cursor
and resident old cursor. No capacity, live flag, distinctness, membership,
reference budget, sequence consistency, readiness or successful-execution
premise is added. Exact source equalities preserve every original failure.
This is a normal callback contract, not totality or multi-call pagination
progress; arbitrary raw room can still give zero saturating ret when unfinished.

HeaderCutModel holds the successful header skb transform. HeaderCutSource
and HeaderPutSource hold the two original Ambient factors and their exact
equalities plus one-put/branch continuation contracts. HeaderResultSource
holds native Ambient normal output; HeaderLiftSource composes its actual
lift with an arbitrary WG continuation. CursorCallbackClaims contains the
projected whole-call claim, and Statements adds the literal
original_cursor_callback_normal. No native state is reconstructed from a
projection and no shared-layer variant is added.

The bounded header worker's eight full invocations all fail, with respective
error/warning counts 1/2, 1/1, 1/1, 1/0, 3/0, 6/0, 1/0 and 1/1.
Source lift/conditional normalization fails first; direct full-prefix reasoning
then reaches the default whnf limit. Factoring puts closes normal header
output, but an unavailable tactic, bind association, type annotations and
finally the successful Except bind prevent whole-package acceptance. Five
prefix roots are individually accepted in the final failed environment;
that is not counted as a passing invocation. Recovery roots are rejected.

A separate root integration probe removes the unused simp argument and uses
an explicit reflexive Except.ok-bind equality. It closes all eight roots,
including the projected callback and literal headline, on its first run
without warnings or nonstandard axioms. Renaming the native prefix-result
file to HeaderResultSource changes only its classification/import path.
No limit/cap increase, warning suppression or infrastructure rerun occurs.
A documentation guard later expects a period where the register uses a semicolon
and aborts before writing any file. The dirty tree, including new modules, is
preserved under refs/snapshots/campaign2-header-doc-guard-20261017T115038940935Z
before correcting that assertion; branch and index remain unchanged.

Installed Config.Statements builds in 361 jobs with only inherited
Env:865 String.mk. Axiom inspection checks 1,258 roots in 297 modules,
including 848 public theorem roots, standard-only and without diagnostics.
Fresh replay, static checks, original 258-name order and mirror/shared
boundaries pass. Independent source/domain/trust review finds no issue.
The inherited aggregate gate remains FAILED and is not rerun unchanged.

Eight new theorems in six modules bring H4 to 758/100; totals are 2,568
theorems, 891 owned modules and 362 headlines. H1 264/34, H2 491/91,
H3 213/20, H5 340/52 and H6 502/65 are unchanged. All six charter results
remain in progress. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, standard-axiom inspection of its closure
and lake env leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H5/H6 scope audit and dependency-note corrections

Independent read-only audit finds no correctness defect in the inspected
current contracts. For H5, the two finite loop-helper bridges do not by
themselves compose whole-worker finite execution or adequate derived fuel.
Runner completion checks consumed records, no suspension and no raised NET_RX;
the literal queue tests and placeholder pending-marker witness establish
neither supplied-record pending-unit consistency nor its negation. Actual
dispatch/resume source correspondence still needs composition through accepted
runner histories. Fairness is stronger than the charter and is removed from
the register's remaining obligations. The new bounded activation-exit task
addresses actual loop control, not those broader gaps.

The mirror-request note now distinguishes the earlier repeatM.impl reduction
obstruction from the available finite power/curve bridge; QueueRefill's
initialized-prefix equation remains unproved. No runtime finding is promoted
to a theorem, and actual hidden/invariant Stops are not relabelled unsupported.

For H6, the shared-overlap note's eight-site list is corrected to its historical
scope: two origin variants now check locally. Source inspection of C1 at
0268b1fc finds unconditional native snapshot contracts that observe the serial,
including sendBufferToPeer_sameSnapshot. Their lifetime invariant is not a
premise. This branch still has the older shared copies; availability is the
outgoing dependency. Incoming staged/keepalive OrdinaryAction contracts permit
allocation and do not yet supply exact serial preservation. The note records
both the smaller outgoing composition after shared support arrives and the
remaining incoming strengthening. No stopped successor is invented: the
monad returns no final WG state on error. No new mirror request is made.


## H5 continuation: actual bounded activation exits

The original Activation.run now has an exact inspection receipt retaining
occupancy-read, iteration and section-stop errors in their original order.
The last attempted iteration is an actual native call at its actual state;
no snapshot reconstruction or stopped successor is used. Captured occupancy
bounds attempted iteration calls by occupancy plus one. Continuing calls
advance the activation counter; yielding appends exactly the incremented
activation; exhaustion has the original invariant Stop and makes no extra call.

ActivationExitModel contains the projected result and accounting predicate.
ActivationExitSource contains actual-state factorization, erasure and native
last-iteration/section-stop provenance. ActivationExitClaims and the literal
original_activation_exit headline state the projected contract. Its ended
and error branches carry no additional projected phase predicate: their
native provenance is separately checked by activationExitRun_source_facts.
This distinction was clarified after independent review, which found no
correctness defect. No new frame or shared variant is needed.

This is a bounded outer-control result, not callback termination, derived-fuel
adequacy, a complete iteration journal or global progress. Those charter gaps
remain. No existing statement is weakened and no new mirror request arises.

The nine bounded development invocations have outcomes FAIL, FAIL, FAIL,
FAIL, PASS, FAIL, PASS, PASS, PASS. Their failed error counts are 2, 8, 2,
2 and 2; the third invocation also has one unused-simp warning. Bind
normalization and occupancy witness rewriting caused the failures; recovery
axiom roots were rejected. The final exact split package checks all nine
theorems with standard axioms and no warnings. No limit or cap was raised,
and there was no infrastructure rerun.

Installed Progress.Statements builds in 301 jobs; rebuilding after the
documentation clarification also passes. Only inherited Env:865 String.mk
warns. Axiom inspection checks 1,248 roots in 237 modules, including 759
public theorem roots, standard-only and without diagnostics. Fresh kernel
replay, static checks, original 258-name order and mirror/shared boundaries
pass. The inherited aggregate gate remains FAILED and is not rerun unchanged.

Nine new theorems in three modules bring H5 from 340/52 to 349/53.
Campaign totals move from 2,568/891/362 to 2,577 theorems, 894 owned modules
and 363 headlines. H1 264/34, H2 491/91, H3 213/20, H4 758/100 and H6
502/65 are unchanged; all six charter results remain in progress.
Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Progress.Statements, standard-axiom inspection of its
closure and lake env leanchecker --fresh on that root, with
LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: exact coalescing across a complete-peer page boundary

Three support theorems now prove the actual coalescer's output for two
DATA pages of complete peer records, device fields on the first page only,
then successful DONE. Arbitrary endpoints, repeated IDs/keys and empty pages
are retained. Complete peers stay distinct occurrences; absent allowed_ips
is normalized exactly as before. This is not yet the native two-page getter:
its producer must establish the cursor, second-header shape and receive path.

TwoPageCoalesceSource contains inner-loop/source support;
TwoPageCoalesceClaims contains the exact coalescer equality. Statements
imports it without adding a headline. No frame or shared variant is added.

Nine root development invocations give FAIL, FAIL, FAIL, PASS, FAIL, FAIL,
FAIL, PASS, PASS. The failures have respectively 2, 1, 1, 1, 1 and 1 errors:
a syntax error, unresolved last-element reduction, an unavailable induction
name, and source-function congruence. Invocation six also has two unused-simp
warnings. The final narrowed-import package checks all three roots without
warnings or nonstandard axioms. The first installed build fails because the
new import was appended after the namespace end; placing it at the file start
fixes that error. No limit/cap increase or infrastructure rerun occurs.

The corrected Config.Statements build passes 363 jobs, with inherited
Env:865 String.mk only. Axiom inspection checks 1,261 roots in 299 modules,
including 851 public theorem roots, standard-only without diagnostics.
Fresh replay, static checks, original-name order and mirror/shared boundaries
pass. Independent review finds no defect and confirms the producer-header
obligation above. The inherited aggregate gate remains FAILED.

H4 moves from 758/100 to 761/100; campaign totals move from 2,577/894/363
to 2,580 theorems, 896 modules and 363 headlines. H1 264/34, H2 491/91,
H3 213/20, H5 349/53 and H6 502/65 are unchanged. All results remain in
progress; no mirror request arises. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Config.Statements, closure axiom inspection and
lake env leanchecker --fresh on that root, using 32 threads and 16 QEMU slots.


## H4 continuation: actual two-page complete-peer getter

[AGENT 2026-10-17] Track the actual held-cursor Device between callbacks.
The final Device retains its ordered acquisition/release tree writes; every
peer lookup and every non-peer field are restored separately. Raw TreeMap
representation equality is not established or needed for the readback claim.

The native callback package establishes both complete executions from data
premises: a nonempty maximal fitting front, resident peers with empty allowed-IP
lists, a positive bounded cursor reference, no earlier occurrence of the
resume cursor, a live boundary cursor and a fitting tail. Duplicate other
visits, later occurrences of the cursor and arbitrary endpoints remain.
Initial cancellation and a dead resumed cursor are outside this total domain;
prior exact source and normal-return contracts retain those branches.

TwoPageCallbackModel holds the pure prefix/cursor model; TwoPageCursorFrames
holds four substantive preservation facts; TwoPageCallbackSource derives the
two actual callbacks and their native source contracts. DeviceTransitionSource
generalizes six owned transport contracts to distinct entry/exit Devices.
TwoPageDrainSource composes the actual receives, both inline and separate DONE,
and the original one-plus-4095 receive budget. These source interfaces take
callback/receive contracts as premises; TwoPageGetterClaims now discharges
every one from the stated data conditions. The literal
original_two_page_empty_ips_getter returns exact multiPeerJson, the actual
ordered Device updates and socketReadbackFinal. The coalescer consumes the
produced pages, and the unchanged drain uses two receives with inline DONE
or three with a separate DONE. This covers exactly two complete-peer pages,
not arbitrary page counts or mixed peer/allowed-IP pagination.

The callback worker's twelve development invocations are FAIL, FAIL, FAIL,
FAIL, FAIL, PASS, FAIL, PASS, FAIL, FAIL, PASS, PASS. Failed error counts are
3, 5, 1, 2, 4, 2, 3 and 3. Invocations two through five have respectively
6, 2, 2 and 4 warnings. Failures concern a missing raw-map extensionality
route, reference/lookup reductions, an array simp loop at the default depth,
redundant proof steps, witness/lift shapes, cursor guards, an over-general
induction hypothesis and record layout. All are corrected in the accepted
17-theorem split package, with standard axioms and no diagnostics.

Root's four transport probes give PASS, FAIL, PASS, PASS. The sole failure is
one record-layout parse error. Seven drain probes give FAIL, PASS, FAIL,
FAIL, FAIL, PASS, PASS. The first has a looping-array simp warning and a
default-depth error. The next three failures are kernel-depth errors when
composing the concrete receive range; their recovery self-axiom roots are
rejected. A symbolic remaining-budget factor avoids reducing that range and
then specializes to the unchanged 4095. The final five-theorem package has
only standard axioms and no diagnostics. No proof limit/cap increase,
warning suppression or infrastructure rerun occurs.

The initial installed callback/drain support build passes 135 jobs. Independent
reviews find no correctness, source, domain or factoring issue in the seventeen
callback facts, six transport variants and five drain facts.

The H1 scope header and register also correct two stale notes: actual
nine-operation confirmation history is already checked with its initial
next/cursor bound. Broader initialized-driver/lifetime propagation remains
separate. The documentation-only Noise.Statements build passes 177 jobs.

The final getter's four development probes give FAIL, FAIL, PASS, PASS.
The first has four record-layout/congruArg recovery errors; the second has
two room/cast normalization errors and one unused simp warning. The frozen
claim and literal headline then check without warnings and with standard
axioms. Independent final review finds no mathematical or source issue;
its wording correction is applied: the getter coalesces DATA pages into JSON,
rather than returning pages. Its domain is nonempty, and all actual source
contracts are discharged without execution/readiness premises.

The installed Config.Statements build passes 369 jobs, with only inherited
Env:865 String.mk. Combined Config/Noise axiom inspection checks 1,741 roots
in 402 modules, including 1,155 public theorem roots, standard-only and
without diagnostics. Fresh replays of both terminal modules pass. Static
checks, original 258-name order and mirror/shared boundaries pass. The
inherited aggregate gate remains FAILED and is not rerun unchanged.

Thirty new theorems in six modules bring H4 from 761/100 to 791/101.
Campaign totals move from 2,580/896/363 to 2,610 theorems, 902 owned modules
and 364 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6
502/65 are unchanged; all six charter results remain in progress. Independent
scope audits confirm the currently documented H1/H2 named-operation coverage
and its explicit confirmation/publication qualifications; they do not promote
those results past the inherited failed aggregate gate. No mirror or shared
layer changes, no new mirror request, no main integration or push.
Reproduce with capped/scripts/in-bundle lake build on
Leanux.Proofs.WG.Config.Statements and Leanux.Proofs.WG.Noise.Statements,
closure axiom inspection and lake env leanchecker --fresh on each root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: finite peer-page plan and actual middle callbacks

The arbitrary-page support now checks the actual fixed-peer byte-cost plan,
its maximal fitting prefixes, progressing resumed pages, occurrence-preserving
flattening, boundary freshness and DATA-plus-DONE-spill budget. The first
nonempty peer must fit; an empty first prefix would retain a null cursor and
repeat the first callback. Only the last peer of each nonfinal page becomes
a cursor. Its freshness excludes all earlier occurrences; interior duplicates,
later cursor occurrences, duplicate public keys and endpoints remain allowed.

MiddlePageModel records the held reference over the actual accumulated
Device. MiddlePageEffects establishes acquisition and ordered handoff:
acquire the distinct new cursor before releasing the old one. All non-peer
fields and pointwise peer records return to baseline on final release.
It neither reconstructs the Device nor equates raw TreeMap representations.
MiddlePageSource derives the actual nonfinal and final resumed callbacks
from baseline residency, empty-IP lists, boundary lifetime/reference data,
freshness and actual page room. No successful execution premise is supplied.

PeerPagePlanModel/Claims hold the pure plan; PeerPageCoalesceSource/Claims
prove that arbitrary finite complete-peer pages coalesce in occurrence order.
The prefix-merge equation retains an arbitrary message tail, including its
possible errors. PageTransitionSource proves that receiving the queued page
executes the next nonfinal callback first and retains its exact Device.
These are support for the whole getter, which remains to be composed; no
new headline or arbitrary-page getter claim is added here.

Independent review found no remaining semantic issue. Its factoring finding
moved the two changed-reference invariants from Frames to Effects. A proposed
four-byte empty-nest correction was withdrawn after checking the actual
assignment order: the mirror saves nestStart after charging the nest.
A temporary pure-formula edit was reverted before acceptance. The original
formula is retained with a pointer to the existing DumpCancellation finding;
no new mirror request arises. Empty DATA has no peer nest, a distinct message
shape that the final getter composition must retain.

Development outcomes: pure plan FAIL (two proof-form errors), PASS, PASS,
PASS; middle callbacks FAIL, FAIL, PASS, FAIL, PASS, PASS. The middle failures
were optional/dependent map lookup normalization, a let alias, an unavailable
tactic and record layout; two unused-simp warnings were corrected.
Root coalescer probes FAIL, PASS, FAIL, PASS (a source-step rewrite and list
append normalization); nonfinal receive transport FAIL then PASS (record
layout). Every accepted package uses default limits, standard axioms and no
warnings. Failed recovery proofs were rejected; no cap increase, warning
suppression or infrastructure rerun occurred.

Initial support build passes 112 jobs. The complete installed build and the
two changed-tree review builds each pass 377 jobs, with only inherited
Env:865 String.mk. Final scoped axiom inspection checks 1,316 roots in 313
modules, including 896 public theorem roots, standard-only without
diagnostics. Fresh Config.Statements kernel replay passes. Static checks,
the original 258-name order, and mirror/shared boundaries pass. The full
aggregate gate remains FAILED in the inherited modules and is not rerun
unchanged.

Fifteen new theorems in eight modules bring H4 from 791/101 to 806/101.
Campaign totals move from 2,610/902/364 to 2,625 theorems, 910 modules and
364 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65
remain unchanged; all six results remain in progress. No mirror/shared edit,
main integration or push. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H4 continuation: whole finite empty-IP peer getter

The original getter now handles the complete canonical finite peer-page
sequence, including empty input, a completing first page, any number of
resumed pages and a final separate DONE when its actual room requires one.
The literal original_finite_empty_ips_getter returns multiPeerJson in original
occurrence order, the completed socket and the actual ordered Device writes.
CursorHeld at none additionally gives every baseline peer lookup and all
non-peer fields; it does not claim structural TreeMap equality.

The domain is listed resident peers with empty allowed-IP lists, a fitting
first header and first peer, all-prior freshness and live/positive/bounded
reference data only at computed nonfinal boundaries, selected Device,
idle empty socket and computed DATA-plus-DONE-spill budget at most 4096.
Interior/final duplicates, later occurrences of earlier cursors, duplicate
public keys and arbitrary endpoints remain. The exact static count supplies
a sufficient original receive budget; no instrumented minimal-call count
is claimed. No callback, receive-success or general readiness premise is
supplied. Mixed peer/allowed-IP pagination remains open.

PeerPageStartModel/Source derive actual first DATA and idle start, using exact
summed costs rather than the prior conservative whole-page bound.
PeerPageTailModel/Source induct over the actual greedy suffix, deriving
maximality, freshness, cursor lifetime, ordered handoffs and receives.
PageDrainSource composes symbolic remaining budgets and specializes to the
unchanged 4096 loop. PeerGetterModel/PeerGetterPlanClaims hold pure final
messages/Device and count/coalescer facts; PeerGetterSource derives the
native drain and PeerGetterClaims projects the whole actual getter.
Reference effects stay in the previously checked MiddlePageEffects file;
no shared-layer copy or new frame is needed.

First/start development has seven invocations: FAIL (five errors and one
unused-simp warning), FAIL (one local-alias arithmetic goal), PASS, FAIL
(two record-layout/cascade errors), PASS, PASS, PASS. The accepted split has
four standard-only theorem roots and no diagnostics.
The tail has nine invocations: PASS, FAIL, FAIL, FAIL, FAIL, FAIL, PASS,
PASS, PASS. Failed error counts are eight, three, two, seven and one;
three failed probes also have an unused-termination warning. Failures concern
count/list normalization, dependent-input termination bookkeeping and a
default-depth/default-heartbeat simplification attempt. The ensuing failed
commitConst/recovery outputs are rejected. The final exact split has two
standard-only roots and no diagnostics; no limit was raised.
Pure getter helpers have four invocations: FAIL (four type/list-normalization
errors), then three PASS, the final split/model checks without diagnostics.

Root's drain probes are FAIL, FAIL, PASS with one unused-simp warning, then
PASS without diagnostics. The first two fail with eight and three errors,
including a default-depth array simp loop and missing source names/imports.
Directional rewriting resolves the array normalization without increasing
limits. Root's final glue probes are FAIL (two over-unfolded socket goals and
two unused-simp warnings), PASS with two deprecation warnings, then PASS for
the exact source, projected claim and literal headline without diagnostics.
Every accepted root uses only the three standard axioms. No cap increase,
warning suppression or infrastructure rerun occurs.

Scoped support builds pass 109, 138 and 158 jobs. Config.Statements passes
386 jobs with only inherited Env:865 String.mk. Axiom inspection checks
1,341 roots in 322 modules, including 912 public theorem roots, standard-only
without diagnostics. Fresh Config.Statements replay passes. Independent
reviews of the source layers and final literal theorem find no remaining
issue. Static checks, the original 258-name order and mirror/shared boundaries
pass. The inherited aggregate proof gate remains FAILED and is not rerun
unchanged.

Sixteen new theorems in nine modules bring H4 from 806/101 to 822/102.
Campaign totals move from 2,625/910/364 to 2,641 theorems, 919 modules and
365 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65
are unchanged; all six charter results remain in progress. No mirror or
shared-layer edit, new mirror request, main integration or push. Reproduce
with capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: scalar and mixed setters through finite peer pages

The original selected-peer scalar setter now composes with the full finite
empty-IP peer getter. Its total projected contract retains stopped-device,
selected-key/residency and positive/bounded selected-reference premises,
including partial-error writes before a malformed second peer request.
Pagination conditions name the concrete scalar successor. Every listed
occurrence reflects its effective fields; an unlisted selected target changes
the Device alone. Exact JSON, completed socket, ordered final Device and
CursorHeld at none are returned.

The mixed fwmark/scalar composition derives its page inputs from the same
actual setter successor. Its normal-return contract preserves missing reset
record Stops and retained writes before later EINVAL; it supplies no reset
readiness or successful callback premise. The actual intermediate postSet
satisfies MultiMixedEffect. Getter cursor writes then produce the exact final
Device; the raw setter effect is not falsely transferred to that final map.
All existing duplicate, endpoint, computed-boundary lifetime/freshness and
4096-envelope qualifications remain.

PeerScalarGetterClaims and PeerMixedGetterClaims hold projected claims;
Statements appends their two literal headlines. PeerPageCapacityFrames has
three pure page/count/lifetime preservation facts. PeerMixedGetterFrames
holds the mixed setter's pure residency/reference/liveness/cost preservation.
Review classified that last file as Frames instead of the initially proposed
Effects; only its filename/import changed. No new native observer or shared
variant is introduced.

Review also identified eight older owned native contracts in frame files.
Their statements, proofs and existing options are unchanged: ReadbackFrames
retains its two data declarations, five contracts move to ReadbackSource,
and three contracts with their two data definitions move from
ScalarGetterFrames to ScalarGetterSource. Direct imports follow those source
files. This is a classification correction, not a theorem deletion or a new
state-split retyping. The obsolete scalar frame module is removed solely
because its contents moved, not because compilation failed.

Scalar development: FAIL (one binder-order proof-form error), PASS, then
PASS for the exact claim/literal package with two standard-only axiom roots
and no diagnostics. Mixed development: FAIL (two well-founded/count proof
errors and one unused-simp warning), PASS for the four support facts,
NOT ACCEPTED despite exit zero for three deprecation warnings, then PASS
for the six-fact exact package without diagnostics. All new proofs use
default limits. No cap increase, warning suppression or infrastructure retry.
Independent review finds no mathematical or domain issues. Its scalar
wording clarification and both source/frame classification findings are fixed;
the reviewer verifies the eight moved theorem tails are byte-identical.

The scalar/classification scoped build passes 388 jobs; the installed mixed
build passes 391 jobs. Both have only inherited Env:865 String.mk.
The final scoped axiom audit checks 1,349 roots in 327 modules, including
920 public theorem roots, standard-only without diagnostics. Fresh
Config.Statements kernel replay passes. Static checks, all 258 original
headline names/order and the mirror/shared boundaries pass. The inherited
aggregate gate remains FAILED and is not rerun unchanged.

Eight new theorems and two headlines bring H4 from 822/102 to 830/104.
The source split and four new claim/frame modules bring the campaign from
2,641/919/365 to 2,649 theorems, 924 modules and 367 headlines.
H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65 are unchanged;
all six charter results remain in progress. No mirror/shared edit, new
mirror-team request, main integration or push. Reproduce with
capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: private-key rotation through finite peer pages

The original changed private-key request now composes with the complete
finite empty-IP peer getter on the established-identity, no-collision path.
The normal-return claim uses the effective clamped or null key identity,
with exact header capacity and page plan for that successor. It permits a
running Device; established identity disables the staged-send branch.
All existing listed-residency, empty-IP, first-fit, computed-boundary
freshness/lifetime, selected-Device, idle-socket and 4096-envelope conditions
remain explicit. No callback success or hidden-record readiness is assumed.

The same actual setter execution supplies both its socket/selector frame
and an ordered ObservedKeyPeerRun false on an existential intermediate
Device. The induction keeps repeated IDs and each evolving resident's own
existential expiry parameter. It does not impose a common clock. These are
ordered effect witnesses, not an exposed clock transcript; the normal-return
claim gives neither setter totality nor a failed-prefix receipt.
Getter cursor writes start from this actual intermediate Device, retaining
the key/index/handshake effects. Exact JSON, completed socket, final ordered
Device and CursorHeld at none follow. No raw peer-map rollback is asserted.

PeerKeyGetterModel supplies the readback/lifetime projection and a total
lookup view that uses actual residents on the original peer list.
Its off-list fallback makes no residency assertion. PeerKeyGetterFrames
contains three pure preservation facts; PeerKeyGetterClaims holds the
projected composition and Statements its literal headline. Existing
PeerPageCapacityFrames is reused. No new shared variant or native observer.

Development: probe 1 FAIL with six errors (an unnecessary Peer equality
decision, three missing PeerId binder types and two declaration cascades);
probe 2 FAIL with seven errors (TreeMap comparison normalization, five
congrArg expected-type inferences and a definitional list equality) and four
warnings (one deprecated name and three unused simp arguments). Probe 3
PASS without diagnostics; probe 4 checks the exact split and literal with
five standard-only axiom roots; probe 5 checks the narrow Model import
without diagnostics. All proofs use default limits, with no cap increase,
warning suppression or infrastructure retry.

The installed scoped build passes 394 jobs, with only inherited
Env:865 String.mk. The final axiom audit checks 1,356 roots in 330 modules,
including 925 public theorem roots, standard-only without diagnostics.
Fresh Config.Statements kernel replay passes. Independent review has no
findings; static checks, original-name order and mirror/shared boundaries
pass. The inherited aggregate gate remains FAILED and is not rerun unchanged.

Five new theorems in three modules bring H4 from 830/104 to 835/105.
Campaign totals move from 2,649/924/367 to 2,654 theorems, 927 modules and
368 headlines. H1 264/34, H2 491/91, H3 213/20, H5 349/53 and H6 502/65
are unchanged; all six charter results remain in progress. General mixed
peer/allowed-IP pagination, global ownership and queued cleanup remain open.
No mirror/shared edit, new mirror-team request, main integration or push.
Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H3 continuation: complete ingress endpoint preservation

The original wgReceive call now preserves every optional endpoint and remote
destination on normal return for arbitrary messages, sources, optional Device,
queues and Ambient inputs. The proof follows the actual header-validation,
handshake-enqueue/CPU-selection and data-admission branches. It assumes no
readiness, authentication, successful prefix or reference premise. Source
Stops remain Stops; this is neither totality nor a post-error state claim.
Handshake work is queued here, so later worker/NAPI execution is separate.

ReceiveIngressSource composes the actual packetReceive with the existing
consumeData endpoint contract. ReceiveIngressClaims projects the whole
wgReceive result; Statements adds original_receive_ingress_endpoints.
ReceiveIngressFrames contains exactly three named local endpoint variants
of C1's prepareSkbHeader (including its internal length check),
cpumaskNextOnline and ipTunnelGetDsfield contracts. Their native originals
are reused directly; no shared file or broad frame layer is copied.
The [shared follow-up](2026-10-15-campaign-2-shared-frame-followup.md)
records counterpart paths for eventual unification.

The remaining historical-authentication gap has two audited architectures.
Persistent endpoint provenance should reuse C1 PublicationHistory,
PublicationFrontier and PublicationChecks.actual_poll. These distinguish
packet occurrences and their earlier successful publication/consume events.
Queues/PollAuthorization is for the later routing/Stack join, not a required
premise for endpoint mutation before routing.
A bounded fresh-admission/decrypt/NAPI alternative could instead start with
empty coherent queues, but still needs queue geometry and occurrence transport.
Current first-cut authentication requires the publication owner's actual queue
head to be the published packet; CRYPTED status, counter acceptance and numeric
ID equality do not establish prior AEAD for arbitrary earlier queue contents.
Neither architecture is replaced by this ingress preservation result, and no
parallel queue/history layer is added.

Development has three probes: FAIL with one CPU-update projection reduction
error and no warnings; PASS after explicit optional-state cases; PASS for the
exact split package, all six roots standard-only with no diagnostics.
Independent review finds no mathematical/source/domain issue. Its one wording
finding is fixed: the literal headline explicitly qualifies normal return.
No cap/limit increase, warning suppression or infrastructure rerun occurs.

The installed scoped build passes 262 jobs without warnings. Axiom inspection
checks 1,104 roots in 228 modules, including 649 public theorem roots,
standard-only without diagnostics. Fresh Roaming.Statements kernel replay
passes. Static checks, all 258 original headline names/order and mirror/shared
boundaries pass. The aggregate gate remains FAILED in inherited modules and
is not rerun unchanged.

Six new theorems in three modules bring H3 from 213/20 to 219/21.
Campaign totals move from 2,654/927/368 to 2,660 theorems, 930 modules and
369 headlines. H1 264/34, H2 491/91, H4 835/105, H5 349/53 and H6 502/65
are unchanged; all six charter results remain in progress. No mirror change,
new mirror-team request, main integration or push. Reproduce with
capped/scripts/in-bundle lake build Leanux.Proofs.WG.Roaming.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: mixed-page serialization, cursor and coalescer support

The actual fresh/resumed getPeerDump now has an exact result at arbitrary
remaining room. MixedPeerSerializerModel holds three pure result functions;
MixedPeerSerializerSource proves six native contracts by composing existing
fixed/endpoint puts and weighted scans. Fixed-prefix or endpoint cancellation
restores the original skb and context. Allowed-IP nest cancellation restores
the skb but retains sequence initialization. Empty lists, zero-emitted splits,
the first nonfitting node and full completion keep their exact attributes,
room and cursor. Resumption uses the original 40-byte public-key prefix.
Resident/readable data, the actual selected suffix and zero/current sequence
are explicit; arbitrary endpoint families and stored widths retain original
serialization, without topology, owner or valid-address assumptions.

CursorReacquireEffects proves the pure held-reference invariant after
acquiring and releasing the same cursor. CursorReadySource proves the total
original finalizer for NULL, equal or distinct cursors and completion, using
conditional acquisition data and retained-release data from the actual
post-acquisition Device. It preserves ordered map writes. A third fact proves
the original overflow Stop when a cursor with baseline count 2^31-2 is
reacquired while already held. The first acquisition's +1 bound holds, but
reacquisition needs +2 below 2^31. This is a local arbitrary-state source
refusal, not an initialized whole-dump trace, kernel defect or new mirror
request. No existing distinct-cursor claim is weakened.

MixedPeerCoalesceModel supplies one raw boundary-data record.
MixedPeerCoalesceSource has three exact equations for the original coalescer:
merge a first continuation into the preceding split peer, append arbitrary
following records, and merge the adjacent DATA pages before an unchanged
arbitrary message tail. The second device header may be absent or identical
to the first. No global key uniqueness is assumed, and later tail errors
remain. Fixed attributes exclude an existing allowed_ips key; continuation
syntax contains only public_key and allowed_ips. This is coalescer behavior,
not a supplied successful producer premise.

Independent review finds no issue in the cursor or serializer packages.
Root's coalescer review identified an interface gap in the initial empty-only
second-header equation; the final rule also accepts the repeated header
required while the first peer remains split. The revised source equation
and preserved tail were checked. No shared lemma or mirror changes.

Cursor development: FAIL (two unspecified Ambient witness errors), FAIL
(one remaining pure equality), PASS for the two support facts, FAIL (wrong
Stop constructor and its cascade), PASS for all three, then PASS for the
exact split. Failed recovery axioms are rejected; accepted checks have only
the standard axioms and no warnings.
Serializer probes: PASS; FAIL (18 errors/7 warnings); FAIL (14/1); FAIL
(unknown arithmetic lemma); FAIL (dependent-ite rewrite); FAIL (4/1);
FAIL (4/3); PASS; FAIL (three resumed-layout diagnostics); FAIL (changed
indentation still leaves those three diagnostics); FAIL (one false branch);
PASS; PASS exact split with six standard-only roots; PASS narrow Model.
Failures concern proof normalization/form and deprecated/unused tactics;
no limit was increased.
Coalescer probes: FAIL (6 errors/3 warnings, including default simplifier
maxSteps); FAIL (1/2); FAIL (1/1); FAIL (2/0); PASS; PASS initial split;
PASS generalized header. Named page expressions and an explicit typed map
equality resolve the normalization failures. Failed recovery is rejected.
A scratch diagnostic-count utility also failed on an invalid regex and was
replaced by direct counting; it changed no proof. No warning suppression,
cap increase, infrastructure retry or unchanged failed rerun occurs.

Support builds pass 128 and 98 jobs. The complete Config.Statements build
passes 400 jobs with only inherited Env:865 String.mk. Axiom inspection
checks 1,372 roots in 336 modules, including 937 public theorem roots,
standard-only without diagnostics. Fresh Config.Statements kernel replay
passes. Static checks, the 258 original headline names/order and mirror/shared
boundaries pass. The inherited aggregate gate remains FAILED and is not
rerun unchanged.

Twelve new support theorems in six modules bring H4 from 835/105 to 847/105.
Campaign totals move from 2,660/930/369 to 2,672 theorems, 936 modules and
369 headlines. H1 264/34, H2 491/91, H3 219/21, H5 349/53 and H6 502/65
are unchanged; all six results remain in progress. A full mixed getter still
needs the finite two-level page plan, its native callback correspondence,
and complete drain/coalescer composition. The chosen plan tracks remaining
peer and node occurrences plus the actual fresh/resumed context; it does
not assume callback success. No main integration or push. Reproduce with
capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.

## H4 continuation: finite mixed-page plan and native peer scan

MixedPageScanModel follows complete, split and cancelled peer results while
retaining the literal native loop tuple and exact unconsumed peer/node
occurrences. MixedPageScanClaims proves four progress facts. The measure
assigns two units to each peer occurrence, one to each node occurrence and
one to fresh mode; this covers a completed peer's reset to fresh mode and a
first split which emits no node but enters continuation mode. No artificial
fuel or successful callback premise is used.

MixedPageBoundaryModel/Claims supply static room/head-fit readiness and its
preservation. MixedPagePlanModel/Claims define the finite plan and prove its
last scan completes, all preceding scans are nonfinal, and its length is at
most the initial occurrence measure plus one. This is a bound on planned
peer scans, not on receives or DONE spill. Empty input has a completed pure
scan; the real header and empty-device guard remain separate obligations.
The first fresh peer need not emit a node, but a resumed nonempty peer must
emit its first node. The proof retains repeated device headers when no peer
has completed and the 24-byte header after a cursor is established.

MixedPageScanInput states the actual row-selection relation and proves the
complete-result context reset. MixedPageScanSource relates the plan's inner
scan to the original forIn/deviceDumpPeersStep on the actual state and Ambient.
The first row is either the full allowed-IP list or the actual dropWhile
suffix with its supplied cursor at the head; later rows are full. Residency,
node reads and zero/current sequence are explicit. The proof transports the
actual middle state, logged events and reset sequence through completion,
and preserves the exact early split/cancellation tuple. Repeated peer and
node IDs are allowed. This native inner-loop result does not yet establish
outer cursor selection, header/guard/finalizer behavior or a complete getter.
No new frame file is needed in this tranche; pure definitions and claims are
separate from the native Input/Source contracts.

Independent review finds no mathematical/source/domain defect. One wording
finding is corrected: pure completion is no longer described as an actual
callback guarantee. The comments were corrected after replay; theorem
statements and proofs are unchanged. Boundary freshness, acquire-before-put
readiness (including coincident cursors), and final DATA/DONE receive counts
remain explicit follow-on obligations.

Plan development has eleven changed probes: FAIL (7 errors), FAIL (4 errors,
1 warning), PASS serializer progress, PASS inner scan, FAIL (1 error,
2 warnings), FAIL (5 errors), PASS recursion/readiness, FAIL (1 error,
2 deprecated-name warnings), PASS outer candidate, PASS exact split and
standard-only axioms, PASS standalone boundary model. Errors concern binder,
normalization, dependent cases and count-bound proof form. One malformed
orchestration call launched no compiler and was corrected.
Native scan development: FAIL (10 errors, 2 warnings), FAIL (2 errors,
1 warning), FAIL (one mapped-loop normalization error), FAIL (one remaining
mapped-loop normalization error after a changed proof), PASS both roots,
PASS exact split. An explicit List.forIn_map normalization closes the
actual tail run. Failed recovery axioms are rejected. Two read-only source
lookups used nonexistent filenames; corrected searches locate the real
files. No cap/limit increase, warning suppression or infrastructure rerun.

The inner support builds pass 95 and 103 jobs. Config.Statements builds
408 jobs with only inherited Env:865 String.mk. The axiom inspection passes
1,399 roots in 344 modules, including 952 public theorem roots, with only
the standard axioms and no diagnostics. Fresh Config.Statements replay
passes. Static checks, all 258 original headline names/order and the
mirror/shared boundaries pass. The inherited aggregate gate remains FAILED
and is not rerun unchanged.

Fifteen new support theorems in eight modules bring H4 from 847/105 to
862/105. Campaign totals move from 2,672/936/369 to 2,687 theorems,
944 modules and 369 headlines. H1 264/34, H2 491/91, H3 219/21,
H5 349/53 and H6 502/65 are unchanged; all six charter results remain
in progress. No mirror change, new mirror-team request, main integration
or push. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H4 continuation: original mixed callbacks and computed cursor boundaries

MixedCallbackFrames preserves the input held-peer cursor through every
serializer branch. MixedCallbackSource supplies three total native contracts:
the mixed loop plus finalizer, the whole fresh-buffer callback through the
false guard, and its empty-list/dead-cursor guard. The proofs thread the actual
state and Ambient, including the final dumpPeerIter=false event, arbitrary
generation flags and acquire-before-release writes. The true guard retains
the mirror's post-nest room and peers=None; an empty selected loop under the
false guard instead emits some []. Initial-peer allowed-IP continuations
repeat the device header until a peer cursor exists.

CursorStepEffects derives the held-reference invariant and actual finalizer
readiness from baseline counts for NULL, equal and distinct cursors. Its
extra increment bound applies only when reacquiring the already-held cursor.
MixedPageReferenceFrames proves four pure congruences: reference-only peer
changes preserve serialization, the scan, readiness and the entire plan;
Device sequence and header size are the explicit inputs where used. These
are preservation facts in their own file, not implicit equality of actual
stores or an assertion that reference operations succeed.

MixedPageSelectionModel/Claims retain genuine peer/node occurrence suffixes,
derive membership in the original residency/readability domain and transport
that structure through every planned page. MixedPlanFresh checks only the
computed nonfinal boundaries, against the entire original consumed peer
prefix and the current peer's consumed node prefix across pages. This yields
the original cursorSelected and dropWhile choices without global uniqueness.
Cancellation and zero-node splits retain their true suffixes. Five definitions,
seven public facts and one private first-match helper form this package.

Independent reviews find no issue in these three packages. Their scope is
local native callbacks plus pure reference/selection support. Whole mixed
getter completion still needs the actual finite drain and canonical emitted
content/coalescer composition; none is assumed as a successful-run premise.

Callback probes: FAIL (7 errors, 1 warning), PASS three core facts, FAIL
(one new guard proof error, rejected recovery axiom), PASS all four,
PASS exact split. Reference congruence probes: FAIL (one conditional
normalization error), FAIL (one remaining definitional equality), PASS two
facts, FAIL (two well-founded proof-form errors), FAIL (one generated-name
error), PASS all four. CursorStepEffects passes its first changed probe.
Selection probes: FAIL (one match projection), FAIL (five proof-form errors
and one cascading termination warning), FAIL (one missing explicit list
argument), PASS complete candidate, PASS exact split and all eight standard
axiom roots, PASS narrow Model. Accepted probes have no diagnostics.
No cap/limit increase, warning suppression or infrastructure rerun occurs.

Support build passes 160 jobs. Config.Statements passes 414 jobs with only
inherited Env:865 String.mk. Axiom inspection passes 1,421 roots in 350
modules, including 969 public theorem roots, standard-only without diagnostics;
the private helper is separately checked in its exact package. Fresh
Config.Statements replay passes. Static/original-name checks and mirror/shared
boundaries pass. The inherited aggregate gate remains FAILED and is not
rerun unchanged. Main remains b3f56807; campaign 1's subsequent f7153a13
account-conservation work was inspected read-only and is not merged.

Eighteen new support theorems in six modules bring H4 from 862/105 to
880/105. Campaign totals move from 2,687/944/369 to 2,705 theorems,
950 modules and 369 headlines. H1 264/34, H2 491/91, H3 219/21,
H5 349/53 and H6 502/65 are unchanged; all six remain in progress.
No mirror change, new mirror-team request, main integration or push.
Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H4 continuation: baseline callback, finite budget and exact page content

MixedHeldCallbackSource now derives the actual fresh-buffer callback from a
baseline Device and its real CursorHeld successor. It transfers resident
records with only the held reference adjustment, original node/sequence/list
data and header attributes, then applies the exact native callback and
ordered finalizer. Static selection, false guard, header capacity and
conditional acquisition/release bounds remain explicit. Its second fact
identifies the planned room with the real header after the peer-nest put.

MixedPageTransportModel defines planned DATA/callback values, DATA-plus-DONE
messages and the sufficient receive budget. MixedPageBoundsClaims proves
room bounds, positive nonfinal return expressions, nonempty finite plans,
final cursor/sequence reset and count at most occurrence measure plus two.
An initial empty scan needs reset at entry; nonempty completion derives it.
The count is page length plus one exactly when the last DATA lacks DONE
room. These pure formulas require separate native correspondence.
MixedPageMetadataEffects retains hasWg, empty message buffers and the
zero/current sequence invariant through scans and plans. Three unchanged
bundled facts were moved from a proposed Frames file after review: sequence
initialization/reset is changed-field invariant closure, not untouched-state
framing. The obsolete eight build artifacts were removed.

MixedPageDeviceModel/Claims record the exact ordered native handoff fold and
static lifetime data only for computed nonfinal cursors. Liveness is retained
for the next callback guard; reference positivity/overflow bounds alone do
not supply it. The conditional second increment appears only on same-cursor
reacquisition. One fact decomposes this condition along the finite plan.

MixedPageContentModel/Source normalize the actual serialized fixed fields
and prove exact completed and split node content, including a zero-node
fragment. The scan-content theorem feeds its retained suffix virtually to
the original inner coalescer and recovers the exact original row/node
occurrences. Cancellation emits nothing and preserves the relevant phase.
Missing allowed_ips is normalized by the coalescer, not attributed to the
serializer. Arbitrary stored widths, endpoints and repeated public keys
remain. This virtual suffix is not an asserted extra native page; full
cross-page accumulator/coalescer composition remains separate.

Independent review finds no mathematical defect. Both form findings are
fixed before final validation: the metadata classification above and wording
that had described planned room under an oversized header as native room.
The original header may Stop there; capacity remains an explicit premise.

Held-callback probes: FAIL (seven projection/elaboration/numeric proof-form
errors), then PASS both roots. Device-plan probes: PASS candidate, PASS
narrow exact split. Content probes: FAIL (13 errors), FAIL (5 errors and
6 warnings), PASS three facts, FAIL (1 error/1 warning), PASS four facts,
PASS exact split. Bounds probes: FAIL (7 errors/1 warning), FAIL
(15 errors/1 warning), PASS initial four bundled facts, FAIL (5 errors after
separation/additions), PASS full fifteen, PASS exact split/axioms, PASS
standalone Model. Accepted probes have no diagnostics. Failed recovery
axioms are rejected. No cap/limit increases, warning suppression or
infrastructure reruns. A read-only source search named a missing file; the
existing transport APIs were located without changing source.

Support builds pass for each package. Final Config.Statements builds 422
jobs after the form corrections, with only inherited Env:865 String.mk.
Axiom inspection passes 1,451 roots in 358 modules, including 991 public
theorem roots, standard-only without diagnostics. Fresh Config.Statements
replay passes. Static checks, original headline order and mirror/shared
boundaries pass. The inherited aggregate gate remains FAILED, not rerun.

Twenty-two new theorems in eight modules bring H4 from 880/105 to 902/105.
Campaign totals move from 2,705/950/369 to 2,727 theorems, 958 modules
and 369 headlines. H1 264/34, H2 491/91, H3 219/21, H5 349/53 and
H6 502/65 are unchanged; all six remain in progress. No mirror change,
new mirror-team request, main integration or push. Reproduce with
capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: complete finite mixed peer/allowed-IP getter

The original wgGetDevice now has a total projected contract for arbitrary
finite peer and allowed-IP occurrences. It derives start, every callback,
ordered acquire-before-release handoff, every receive and original outer
coalescer. No callback, receive or successful-execution premise is supplied.
The output is exact canonical JSON, the reset socket and the ordered native
Device fold. CursorHeld with no held cursor separately restores all baseline
peer lookups and non-peer fields; raw TreeMap equality is not asserted.

The domain is explicit: listed residents and readable nodes, initial and
continuation capacity/readiness, first-header space, all-prior freshness only
at computed nonfinal cursor boundaries, and live/positive/bounded references
only for those cursors. Same-cursor reacquisition needs the second increment.
The socket starts idle and empty, and the sufficient DATA/DONE receive count
is at most 4096. Empty devices, first-page completion, zero-node fragments,
same-cursor pages and final DONE spill are covered. Stored widths, endpoints,
other duplicate occurrences and duplicate public keys remain arbitrary.
This closes mixed getter pagination, not general setter or global ownership
semantics.

MixedFirstModel/Source supply first start/callback shapes and two source facts.
MixedPageDrainSource derives the finite tail; MixedGetterDrainSource connects
the actual first call and remaining drain with two facts. The six
MixedCoalesceContext/Step/Scan/Plan, CoalesceMessage and MixedPlanCoalesce
modules supply four definitions and thirteen source facts for the original
coalescer. Its standalone ACK shortcut, mixed ACK error, flags, compressed-JSON
header comparison, continuation errors, continued scanning after DONE and
final error ordering are retained. MixedGetterModel defines the exact JSON;
MixedGetterClaims holds the projected total contract. Statements adds one
literal headline. These are models, source correspondences and a claim;
no new frame file or shared-layer variant is needed.

Independent reviews of the first/tail, coalescer and final composition find
no issue. The first-call identifier initially collided with an existing
weighted-getter definition in the full Config build; that build FAILED.
Only the new identifier was renamed to mixedPeersFirstCall. Existing
definitions and proofs were unchanged.

Development ledgers: first-call probes fail with 7, 2, 1, 1, 1, 1 and 2
errors, then the two roots and exact split pass. The sixth was a diagnostic
probe exposing differing hidden decision terms; the fix uses equality
rewriting rather than simp. Tail-drain probes fail with 10 and 2 errors,
then the candidate and axiom check pass. Whole-drain probes fail with
3 errors; the next has two unused-simp warnings and is not accepted;
corrected candidate and axiom check pass. Coalescer probes in order:
FAIL 5 errors/7 warnings, PASS, FAIL 4/10, FAIL 4/1, PASS, FAIL 4/6,
FAIL 1/0, PASS, FAIL 1/0, FAIL 1/0, FAIL 4/1, FAIL 2/1,
zero errors/one warning (not accepted), PASS exact split and all thirteen
axiom roots. The final projected getter's first probe passes. Accepted
probes have no diagnostics. No cap/limit increase, warning suppression,
infrastructure rerun or unchanged failed-source rerun occurs.

The corrected Config.Statements build passes 434 jobs with only inherited
Env:865 String.mk. Closure inspection passes 1,480 logical roots in 370
modules, including 1,011 public theorem roots, using only standard axioms.
Fresh kernel replay, static checks, all 258 original headline names/order
and mirror/shared boundaries pass. The aggregate gate remains FAILED in
the inherited CounterWindow/ReplayWindow files and is not rerun unchanged.
Campaign 1's subsequent runtime-fixture repair was inspected read-only;
main remains b3f56807 and no campaign-1 branch is merged.

Twenty new theorems, nine definitions and twelve modules bring H4 from
902/105 to 922/106. Campaign totals move from 2,727/958/369 to
2,747 theorems, 970 modules and 370 headlines. H1 264/34, H2 491/91,
H3 219/21, H5 349/53 and H6 502/65 are unchanged; all six remain in
progress. The register overview's stale aggregate counts are corrected.
No mirror change, mirror-team request, main integration or push. Reproduce
with capped/scripts/in-bundle lake build Leanux.Proofs.WG.Config.Statements,
closure axiom inspection and lake env leanchecker --fresh on that root,
with LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16.


## H4 continuation: scalar set followed by the full mixed getter

The actual existing-peer PSK/keepalive setter now composes with the complete
finite mixed peer/allowed-IP getter. This removes the earlier empty-IP
restriction. All original peer/node occurrences retain their order and
serialized width/endpoint behavior. The first peer's writes remain when a
later malformed peer returns -EINVAL; an unlisted target changes Device
without adding a dump occurrence. The getter uses the exact post-set Device
and Ambient, then records its own ordered cursor handoffs.

ScalarMixedGetterEffects derives resident configured peer reads, unchanged
node/list/selector fields and retained allowed-IP lists from the pure ordered
setter effect. ScalarMixedGetterClaims holds the projected total composition;
Statements adds its literal headline. Its stopped-device, target lookup,
positive/bounded reference domain remains explicit. Getter readiness,
capacity, computed boundary freshness/lifetime and sufficient receive budget
are static conditions on scalarRequestDevice and scalarPeerView. No callback,
receive or successful execution is assumed. No new frame or shared variant
is introduced.

Independent review finds no issue. All three probes pass without diagnostics:
candidate, exact split plus three standard-only axiom roots, and standalone
Effects. Support build passes 201 jobs; final Config.Statements build passes
436 jobs with only inherited Env:865 String.mk. Closure axiom inspection
passes 1,483 roots in 372 modules, including 1,014 public theorem roots,
standard only. Fresh replay, static/original-name checks and mirror/shared
boundaries pass. No failed probe, cap/limit increase, warning suppression or
infrastructure rerun occurs. The inherited aggregate gate remains FAILED,
not rerun unchanged.

Three new theorems in two modules bring H4 from 922/106 to 925/107.
Campaign totals are 2,750 theorems, 972 modules and 371 headlines.
H1 264/34, H2 491/91, H3 219/21, H5 349/53 and H6 502/65 are unchanged;
all six remain in progress. No mirror change or new mirror-team request,
main integration or push. Reproduce with capped/scripts/in-bundle lake
build Leanux.Proofs.WG.Config.Statements, closure axiom inspection and
lake env leanchecker --fresh on that root, with LEAN_NUM_THREADS=32
and LEANUX_QEMU_SLOTS=16.


## H4 continuation: endpoint, fwmark and key set with full mixed readback

Three actual configuration paths now compose with the complete finite mixed
getter. Endpoint configuration retains ignored encodings, equality-preserved
endpoint fields, UPDATE_ONLY behavior for an existing peer and earlier writes
before a later malformed peer returns -EINVAL. Static pagination uses the
pure reset-none successor; the getter runs on the actual optional-reset
Device and preserves its cache effects through ordered cursor handoffs.

Mixed fwmark/scalar configuration retains all ordered source/cache clears,
including repeated visits, and the selected PSK/keepalive update. Later
-EINVAL retains those earlier effects. The explicit scalarRequestDevice
successor supplies static page conditions; MultiMixedEffect describes the
actual intermediate Device, which remains the base of the final cursor fold.
Unlisted selected peers remain updated without adding JSON occurrences.

Established-identity private-key installation uses the effective clamped/null
identity and actual ordered peer-expiry effects. Its ObservedKeyPeerRun and
per-visit witnesses describe the actual intermediate Device. Getter-visible
peer data, node stores and page inputs survive; no empty allowed-IP list is
required. Changed/no-collision conditions remain explicit. All three claims
are normal-return guarantees: they derive getter completion at the actual
setter successor, while retaining original reset/expiry-record Stops.
They do not assert setter totality or global initialized ownership.

MixedGetterInputFrames supplies three reusable pure congruences for readiness,
the entire finite page plan, and rows/JSON/boundary/reference conditions.
They use exact observed attributes/costs, sequence, header and resident views;
no raw-map equality or reconstructed execution state is assumed. KeyMixedGetterClaims
contains its projected claim. EndpointGetterFrames has three reset-choice/
other-lookup preservation facts, and EndpointMixedGetterClaims its projected
composition. FwmarkMixedGetterFrames holds one source/cache-reset projection
frame, and FwmarkMixedGetterClaims the corresponding composition. Three literal
headlines are appended to Statements. No shared layer is copied or modified.

Independent reviews of the generic frames and all three packages find no
issue. Key/generic probes: FAIL 3 errors/1 warning, FAIL 2/0, PASS,
PASS narrow imports/three axioms, FAIL 2/0, FAIL 1/0, PASS claim, PASS
exact split/five axioms. Endpoint frame probes both PASS; composition probes
FAIL 4 errors (omitted scratch import), FAIL 9 (masked-record projection
elaboration and a remaining equality), FAIL 1 (redundant tactic), PASS,
PASS exact split/two axiom roots. The missing-import recovery axioms are
rejected. One read-only search preceded creation of an agent scratch path.
Fwmark probes: FAIL 1 error/4 unused-simp warnings, PASS frame,
FAIL three default-heartbeat diagnostics from broad record normalization,
FAIL two proof-form errors, PASS complete candidate, PASS exact split/three
axioms, PASS standalone Frames. Reusing the existing outer-field equation
removes the heartbeat failure; no limit is increased. All accepted probes
have no diagnostics. No cap change, warning suppression or infrastructure rerun.

Support builds pass. Final Config.Statements passes 442 jobs with only
inherited Env:865 String.mk. Closure inspection passes 1,496 roots in 378
modules, including 1,027 public theorem roots, standard-only. Fresh kernel
replay, static checks, all original 258 headline names/order and mirror/shared
boundaries pass. The aggregate gate remains FAILED in the inherited files
and is not rerun unchanged. Campaign 1's 7365f387 worker-closure report was
inspected read-only; its whole initialized conservation remains open.

Thirteen new theorems, six modules and three headlines bring H4 from
925/107 to 938/110. Campaign totals are 2,763 theorems, 978 modules and
374 headlines. H1 264/34, H2 491/91, H3 219/21, H5 349/53 and H6 502/65
are unchanged; all six remain in progress. No mirror change, mirror-team
request, main integration or push. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Config.Statements, closure axiom inspection and
lake env leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.


## H4 continuation: full mixed readback after port configuration

The original mixed request's changed nonzero-port refusal now composes with
the complete mixed getter. Its -EADDRINUSE return retains old incomingPort,
sock4 and sock6; earlier fwmark/generation and both source-clearing loops
remain effective. Later supported replacement, private-key and peer attributes
are bypassed. PortMixedGetterFrames preserves exact getter-visible peer data
through ClearedPeerStore, including absent and unlisted entries.
PortMixedGetterClaims gives the projected normal-return composition.

NonzeroPortMixedGetterClaims separately covers every nonzero port-only
request outcome under creatingNet=true: same-port generation-only success,
changed stopped-device update with old sockets, changed running successful
bind, and changed running collision refusal. PortOutcomeModel normalizes the
existing outcome; PortOutcomeFrames preserves its unrelated fields and
PortOutcomeSource derives the actual same/changed effect from the original
setDevice_port_nonzero contract. It retains exact same-port Device equality
and otherwise the actual ClearedPeerStore. No effect is reconstructed as an
execution state. PortReadbackFrames supplies four preservation-only native
contracts for socket replacement, nonzero initialization, setPort and the
selected whole request. These preserve portBound, netlink socket and fixture
selection, including absent-device and namespace-refusal paths where applicable.

Both new compositions derive the full getter from the same actual setter
successor and Ambient. Static listed residency/readability, readiness, header,
computed freshness/lifetime and receive-count premises remain explicit.
The final raw Device is the ordered cursor fold over that actual successor;
socket reset and pointwise CursorHeld restoration are stated separately.
Normal-return scope retains missing-peer/reset-record Stops. Zero-port draw
semantics are not claimed by these results. Two literal headlines are added.

Independent review finds one inherited form issue, fixed before final checks:
socketInit_nonzero_collision_frame also proves the concrete refusal return.
Its declaration/body move unchanged from PortRefusalFrames into PortRefusalSource,
where its sole caller resides; the clearing-loop preservation fact remains in
Frames. This is a relocation, not a deletion or a new theorem. Reviews of the
normalized outcome, four native frames and both compositions find no other issue.

Refusal probes: FAIL one error/three unused-simp warnings from requesting
whole-peer equality; corrected projection proof PASS; exact split/three roots
PASS. Outcome probes: FAIL five import/layout/namespace errors, FAIL one
overbroad equality rewrite, FAIL two rewrite errors/two deprecated-name warnings,
then PASS two standard-only roots. Precise conditional reduction fixes the
normalization without rewriting unchanged record fields. Native-frame probes:
FAIL 4 errors/1 warning, FAIL 2 errors, FAIL 4 errors/3 warnings, PASS first
three, FAIL 1 error/4 warnings, FAIL 1 error/4 warnings, PASS all four,
PASS exact four-root check. Nonzero composition: FAIL six projection
elaboration errors, PASS corrected candidate, PASS exact installed imports/
literal wrapper/two roots. All accepted probes have no diagnostics; recovery
axioms are rejected. No limit/cap increase, warning suppression or infrastructure
rerun occurs.

Support builds pass 228, 93 and 90 jobs. Final Config.Statements build passes
449 jobs, including all relocation dependents, with only inherited Env:865
String.mk. Closure inspection passes 1,508 roots in 385 modules, including
1,038 public theorem roots, standard-only. Fresh replay, static checks,
original 258-name order and mirror/shared boundaries pass. The aggregate
gate remains FAILED in inherited files and is not rerun unchanged.

Eleven new theorems, one definition, seven modules and two headlines bring
H4 from 938/110 to 949/112. Campaign totals are 2,774 theorems, 985 modules
and 376 headlines. H1 264/34, H2 491/91, H3 219/21, H5 349/53 and H6 502/65
are unchanged; all six remain in progress. No mirror change, mirror-team
request, main integration or push. Reproduce with capped/scripts/in-bundle
lake build Leanux.Proofs.WG.Config.Statements, closure axiom inspection and
lake env leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.


## H4 continuation: actual zero-port configuration and full mixed readback

The zero-port-only setter now composes with the complete mixed getter.
The chosen-port witness comes from the same normal native execution. An
unchanged zero port retains the Device apart from generation; a changed port
on a stopped Device clears captured peer sources, sets incomingPort to zero
and retains UDP sockets; a changed running Device clears sources and binds
both sockets to the selected in-range port. The unused choice is normalized
to zero on the first two branches. This is not a new draw-record transcript.

ZeroPortOutcomeModel gives the scalar outcome and choice domain,
ZeroPortOutcomeSource normalizes the existing actual source contract,
and ZeroPortOutcomeFrames contains its pure preservation fact.
ZeroPortMixedGetterClaims and its literal Statements headline use
Campaign2.Ensures. Static pagination premises use requestGeneration d:
port and socket fields do not affect header capacity or peer/node inputs.
JSON includes the actual selected port. The final Device is the getter's
ordered cursor fold over the actual post-set Device, retaining its original
source-clearing effects, socket reset and CursorHeld restoration.

CreatingNet, resident/readable listed data, computed page readiness and
freshness, cursor lifetime counts, header capacity, idle/empty socket and
the sufficient 4096-receive budget remain explicit. No successful random
draw, free candidate, reset or callback is a premise. Missing records,
random-port collisions and reset Stops remain Stops; this normal-return
claim does not prove total setter execution. Duplicate occurrences outside
the computed boundary constraints and arbitrary endpoints/widths remain.

[AGENT 2026-10-17] Factor the existing owned selected port-request prefix
into setDevice_port_configurationFrame_of_setPort so zero and nonzero
readback frames share that prefix. The original nonzero statement is
unchanged; its body applies the generic fact. Its first three supporting
frames are byte-identical. ZeroPortReadbackFrames adds three preservation-only
facts for zero initialization, setPort and the whole request. Independent
reviews of both the refactor/native frames and the complete composition
find no issue; no shared-layer edit or type-based deletion occurs.

Native frame probes: FAIL one conditional-normalization error, PASS two
zero leaves, PASS the refactor and all three zero frames, PASS five roots.
Outcome/getter probes: FAIL one record-update layout parser error; PASS
two roots, PASS three roots, PASS exact split/literal four-root package.
One generation command read a scratch file already cleaned after its
commit; it wrote nothing and was corrected to read the installed source.
Accepted probes have no diagnostics and standard axioms only. Rejected
elaboration output is not proof evidence. There is no limit/cap increase,
warning suppression, killed build, timeout or infrastructure rerun.

The support build passes 91 jobs. Final Config.Statements build passes
454 jobs with only the inherited Env:865 String.mk warning. Closure axiom
inspection passes 1,518 roots in 390 modules, including 1,046 public theorem
roots, with only the three standard axioms. Fresh replay, token/import checks,
the original 258 headline names/order and mirror/shared boundaries pass.
The inherited aggregate gate remains FAILED and is not rerun unchanged.

Eight new theorems, two definitions, five modules and one headline move
H4 from 949/112 to 957/113. Campaign totals are 2,782 theorems, 990 modules
and 377 headlines. H1 264/34, H2 491/91, H3 219/21, H5 349/53 and H6 502/65
are unchanged; all six remain in progress. No mirror-team request, main
integration or push. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.


## H4 continuation: empty allowed-IP replacement and complete readback

The actual REPLACE_ALLOWEDIPS request with no new addresses now composes
with the complete mixed getter. The normal setter run supplies RemovalEffect;
it is not a premise. Every original peer occurrence is retained, and every
removed node ID is filtered from every peer list, including aliases. The target
list is empty. The target's acquired reference is restored, generation increments,
and the allowed-IP sequence increments exactly when the captured list is nonempty.
The final Device is the getter's ordered cursor fold over the actual removal
successor; its roots and node records are never reconstructed for execution.

[AGENT 2026-10-17] Use the existing stopped-device, live/bounded-reference,
lookup/residency and NodePairs domain, plus a local survivor condition:
every dumped node outside the removed IDs has a non-null owner word.
This condition neither identifies that owner with the dumping peer nor
asserts global trie/list ownership. A collapsed unowned parent can otherwise
still be named by another malformed peer list, so original readability alone
does not transport through removal. That obstruction is source analysis,
not a new checked counterexample or a mirror finding. Unrelated aliases may
still Stop; no total setter claim is made.

ReplacementSurvivorModel/Frames preserve actual node presence, owner word,
width, bits and CIDR across the ordered removal. MixedNodeViewModel/Frames
transport exact costs, JSON, greedy prefixes, scan tuples and full page plans
using only width/bits/CIDR. ReplacementReadbackModel supplies static getter
inputs; ReplacementReadbackFrames separates pure commutation/outer facts and
ReplacementReadbackEffects derives exact filtered peer lookups and sequence.
AllowedRemovalReadbackFrames, ReplacementPeerReadbackFrames and
ReplacementRequestReadbackFrames preserve socket/fixture fields through the
actual native path. ReplacementMixedGetterClaims and its literal Statements
headline use Campaign2.Ensures over the projection.

Actual readable successor nodes discharge every getter access; fallback values
are used only outside that footprint. Arbitrary stored widths, endpoints,
duplicate target occurrences and other aliases remain subject only to the
stated survivor and computed pagination domains. Header room, boundary freshness,
cursor reference counts, idle/empty socket and sufficient 4096-receive budget
remain explicit. Independent reviews of every support package and the exact
final composition/terminal find no issue.

Development checks: node-view FAIL two conjunction goals, then PASS eight
standard-only roots. Survivor probes FAIL four errors/two warnings, FAIL one
error/three warnings, PASS full candidate, PASS seven split axiom roots and
PASS narrowed model. Native frames FAIL two errors, then three clean passes
covering all five roots. Input/effect probes FAIL three diagnostics, FAIL three
type/rewrite errors, then PASS four roots. Getter probes FAIL two missing-import
diagnostics; two subsequent kernel-accepted candidates each had one linter
warning and were corrected; final candidate PASS with no diagnostics.
All failed/recovery output remains rejected. No limit/cap increase, warning
suppression or infrastructure rerun occurs.

Support builds pass 124, 59 and 118 jobs; final Config.Statements build passes
472 jobs, with only inherited Env:865 String.mk. The closure audit checks
1,594 logical roots in 408 modules, including 1,084 public theorem roots,
all standard-only. Fresh kernel replay, static token/import checks, original
258 headline names/order and mirror/shared boundaries pass. The aggregate
gate remains FAILED in inherited files and is not rerun unchanged.

Twenty-six new theorems, four definitions, eleven modules and one headline
move H4 from 957/113 to 983/114. Campaign totals are 2,808 theorems,
1,001 modules and 378 headlines. H1 264/34, H2 491/91, H3 219/21, H5 349/53
and H6 502/65 are unchanged; all six remain in progress. General nonempty
insertion/replacement and REPLACE_PEERS final erasure still cross the
documented shared ownership/free boundary. No new mirror-team request,
main integration or push. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.


## Remaining-scope audit after the replacement checkpoint

A read-only audit at main b3f56807 and campaign 1's 4e71927e distinguishes
literal obligations from stronger initialized-driver claims. H2's named
index operations, ownership lookup and collision retry core are checked;
initialized driver/lifetime propagation is separate. General H4 nonempty
insertion and final replace-peers erasure still require the represented-trie,
ownership and free layers already inventoried.

For H5, outer activation exit accounting does not supply finite execution
and hidden-record suffix decrease for every inner worker, or a relation
between pending identities and physical queued work. Composing C1 represented
rings/resources and instead deriving an initialized runner invariant both reach
the deferred queue/callback/history families. The accepted placeholder witness
only proves retained bookkeeping; it is not evidence of supplied-record work
left unexecuted. No new progress headline is claimed from this audit.

For H6, the local arm-site delays, traversal receipts and qualifying retry
blocks already have actual-call contracts. Whole-call allocation labels and
arbitrary interleavings need the documented serial transport: direct expansion
duplicates socket/cache families; C1 SameSnapshot can reduce the outgoing case
to four facts once that support reaches this branch. Incoming staged sending
still admits allocation. This audit supplies no additional arm-count proof.

The current H3 follow-up is corrected: PollAuthorization governs routing/Stack
entry after endpoint mutation and is not itself a prerequisite of the narrow
endpoint-authentication join. Persistent publication history or a bounded
fresh-queue/decrypt/NAPI alternative still requires packet occurrence and queue
geometry transport. The bad-MAC2/no-cookie reply-preservation suffix remains
the separately inventoried six-operation socket/cache path. No shared layer
is copied. An old H1 status sentence is also brought current with the already
checked nine-operation fresh-confirmation history; no theorem changes follow
from either documentation correction.


## H1 continuation: arbitrary-peer interleavings of the native lifecycle

The nine-operation fresh-confirmation history now permits a different actor
on every call. For one tracked peer, successful confirmation numeric IDs remain
pairwise distinct under its sole initial next-slot-below-allocation-cursor bound.
Foreign session installation advances the shared cursor while retaining tracked
next, including an absent tracked peer. Foreign rotation and clearing retain
that peer's slot record even when aliased releases erase a shared key.

InterleavedFreshModel adds actor-labelled receipts and a pure monotone-cursor
step beside the original local relation. InterleavedFreshFrames isolates the
two foreign-peer preservation facts; InterleavedFreshEffects carries actual
session effects and the seen-ID invariant. InterleavedFreshSource executes the
existing native calls and proves exact observation erasure; Claims derives
every linked projected boundary from that same execution. The new literal
headline combines unconditional Campaign2.AgreesOn with the normal-return
Campaign2.Ensures history/distinctness claim. No successful prefix, release
readiness, key residency or global owner invariant is assumed.

This is fixed-peer numeric distinctness. Different peers can initially share a
next ID; their confirmations are not folded into one global uniqueness claim.
Consumer messages still select their peer internally. Direct helper
reinstallation, peer recreation/reset, final key residency and initialized
driver history remain outside this finite language. The original first Stop
propagates without returning an invented partial receipt history. Existing
models, signatures and shared layers are unchanged; no new shared variant is
needed. Independent design and final frozen-package reviews find no issue.
One draft relation docstring is corrected to distinguish linked pure boundaries
from their separately proved execution provenance.

Four source checks: PASS pure support; one kernel-accepted but rejected warned
candidate with deprecated if_neg; PASS after ite_eq_right correction and the
full chain/terminal; PASS the exact split and all ten axiom roots. No other
diagnostics, proof-limit/cap change, warning suppression or infrastructure rerun.
Final Noise.Statements build passes 182 jobs without warnings. Closure
inspection passes 731 logical roots in 155 modules, including 440 public theorem
roots, standard-only. Fresh kernel replay, original 258-name order, static
token/import checks and mirror/shared boundaries pass. The inherited aggregate
gate remains FAILED and is not rerun unchanged.

Ten added theorems, eight data/source declarations, five modules and one
headline move H1 from 264/34 to 274/35; no theorem is retyped or deleted in
this tranche. Campaign totals are 2,818 theorems, 1,006 modules and 379 headlines.
H2 491/91, H3 219/21, H4 983/114, H5 349/53 and H6 502/65 are unchanged;
all six remain in progress. No mirror-team request, main integration or push.
Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Noise.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, with LEAN_NUM_THREADS=32 and
LEANUX_QEMU_SLOTS=16.

## H4 continuation: initial-state replace-peers observations

The flag-only REPLACE_PEERS observation now takes its routing representation,
node-shape and listed-residency assumptions from the initial Device. Actual
device selection increments deviceUpdateGen before free; landed
AllowedIps.free_endpoint relates the real post-free Device to that incremented
initial state. Its surviving-node relation transports NodePairs, its exact peer
lookups transport listed residency, and its unchanged peerList identifies the
list used by both original removal passes.

Every normal full request return therefore exposes the actual post-free cut
and a first-pass snapshot with every originally listed peer resident and dead.
Duplicate identities are permitted. The theorem also retains the actual
DeadPassEffect and exact allowed-IP clearing relation. The observer executes
the whole cleanup pass before returning; all errors and original final
execution remain connected by the existing unconditional erasure theorem.

This closes the earlier post-free-assumption gap. It does not prove that the
request completes, that final peer/node stores are empty, a general mixed
attribute request, or a later getter composition. The routing premise does
not itself assert resident owners; listed residency is stated separately.
No existing statement is weakened and no mirror discrepancy is inferred.

Architecture: ReplacementInitialEffects transports invariants over changed
stores; ReplacementInitialSource connects actual free and generation-prefix
runs; ReplacementInitialClaims and the new Statements terminal use the campaign
projection. No shared layer or mirror is edited. Five theorems in three new
modules bring H4 to 988 theorems and 115 headlines, and the campaign to 2,826
theorems, 381 headlines and 1,011 owned modules. Existing names/order remain.

Validation: the final scoped Config.Statements build passes 552 jobs.
The first split build failed because two older local getDev subproofs had
redundant rfl steps after importing the landed simplification support; those
proof-form steps were removed with unchanged statements. The closure axiom
audit passes 2,710 logical declarations in 488 proof modules, including
1,970 public theorem roots, with the three standard axioms only. Fresh kernel
replay passes. Static checks and original headline names/order pass.
Independent review's sole placement finding was fixed by moving the pure
changed-store transport from Frames to Effects; no correctness/scope issue
remains. The earlier stdin candidates had proof-form and parser failures
(including rejected recovery diagnostics); the final five-fact candidate
passed without diagnostics. No cap increase, infrastructure rerun or guest
run for this tranche; inherited Env:865 deprecation remains. The full gate's
three inherited GRO failures are unchanged and are not rerun here.

Reproduce with capped -- scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, the closure axiom audit, and capped --
scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Config.Statements,
using 32 Lean threads and 16 QEMU slots. The ranked helpful support is C1's
remaining GRO carry for final initialized cleanup (proof-only,
altitude-preserving). No mirror-team change is requested.

## H4 continuation: represented insertion followed by peer readback

[AGENT 2026-10-18] Derive the serializer's readable successor from initial
routing coherence and the actual setter outcome, using landed C1 insertion
contracts. Keep the value lookup data-only: its default node is proved unused
on the serialized list, and no original failure is replaced.

RoutingReadbackModel composes the original setAllowedip and getPeerDump.
For arbitrary represented IPv4/IPv6 trees, a resident destination and the
address-shape premise, every normal composition return has the exact actual
setter effect and weighted fresh-peer serialization of its actual successor.
The dump context starts without an allowed-IP cursor and with sequence zero;
its room, endpoint and finite old peer list are unrestricted.

Invalid attributes preserve Device. Normal ENOMEM retains the sequence
increment and possible consumed node ID, with pointwise unchanged peers and
nodes. Successful insertion derives the normalized all-peer ownership transfer:
remove the selected binding ID from old lists and append it once to the target.
The actual resulting list order and node widths determine serialized content,
room, cancellation and splitting. Representation and readability are derived
after the setter; neither is supplied as a final-state premise.

This is a local setter/single-peer serializer composition. It does not claim
completion on arbitrary hidden inputs, complete socket pagination, an arbitrary
outer mixed setDevice request, or initialized reachability. Original Stops
remain possible and are not assigned a successor. C1's RoutingInvariant does
not by itself establish residency for every owner; only the destination's
initial residency is required here.

RoutingReadbackEffects contains pure representation/readability and normalized
list effects; RoutingReadbackSource connects the original setter; projected
claims live in RoutingReadbackClaims and Statements. No new frame is needed.
Six theorems in four modules bring H4 to 994/116 and the campaign to 2,832
theorems, 1,015 modules and 382 headlines. Other result counts are unchanged.

Validation: scoped Config.Statements build passes 579 jobs with the inherited
Env String.mk deprecation only. The closure audit covers 3,098 public logical
declarations, including 2,250 theorem roots in 515 proof modules; all use only
the standard axioms. Fresh replay passes; independent review closed
without findings.
One exploratory stdin proof failed on an uninferred existential witness;
the explicit witness closes it. Later probes and the split build pass without
owned warnings. The full gate remains failed in the inherited GRO modules.
Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Config.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, using 32 Lean threads and 16 QEMU slots.

## H2 continuation: a preserved session/index invariant

[AGENT 2026-10-18] Compose campaign 1's landed affiliation preservation with
the existing campaign-owned table and owner-coherence contracts on the same
original session run. Derive rotation freshness and allocation bounds from the
combined initial invariant rather than supplying them at each call boundary.

SessionInvariantModel combines full Affiliation.State.Inv, numeric-index
uniqueness, embedded-owner uniqueness and HashedOwnersCoherent. Affiliation
bounds slot identities below nextKeypairId, including aliases and old absent
keys. Hashed-owner residency plus its resident-key bound gives the required
hashed-key allocation bound. The actual first peer read supplies caller
residency. The call preserves all four facts together on every normal return.
A direct finite mapM beginSession composition derives the next call's invariant
from its actual predecessor without intermediate freshness assumptions.

These are local input invariants, not initialized-driver claims. Missing
unhashed targets and NULL-compatible references remain possible; identity
bounds do not imply refcount ceilings or full reference accounting. Original
false results and Stops remain, and no completion or stopped-prefix invariant
is asserted. The existing SessionAlias witness violates the slot bound rather
than refuting this stronger combined premise.

Two architectures were inspected. CurrentSlots.Inv from RunnerAccount.normal
or HolderAuxiliary.session_normal can supply the rotation slot bound, but its
import closure reaches the inherited GRO failures. More importantly, those
initialized APIs do not supply full affiliation, hashed-owner coherence or
index uniqueness. The narrow landed Keypairs.Affiliation.beginSession_affiliation
contract compiles independently and gives the preserved local invariant used
here. Repairing the GRO imports alone will not close the initialized H2 gap;
the additional invariant transport remains substantive work. No shared layer
is copied or edited, and no mirror change is requested.

SessionInvariantEffects contains the two pure bridges. The original-call and
finite-composition claims are in SessionInvariantClaims, with two literal
Statements headlines; no frame file is added. Six theorems in three modules
bring H2 to 500/94 and the campaign to 2,838 theorems, 1,018 modules and
384 headlines. Other result counts are unchanged.

Validation: the scoped Index.Statements build passes 510 jobs with only the
inherited Env String.mk warning. Its audit checks 3,402 public logical roots,
including 2,463 theorem roots in 446 proof modules, using only the standard
axioms. Independent review closes without findings. Fresh replay passes.
Exploratory stdin drafts exposed proof-form and unused-simp diagnostics, then
mapM-unfolding and substituted-binder errors; the split build passes cleanly
after correction. No infrastructure rerun occurs. The inherited aggregate
GRO gate failure remains. Reproduce with capped/scripts/in-bundle lake build
Leanux.Proofs.WG.Index.Statements, closure axiom inspection and lake env
leanchecker --fresh on that root, using 32 Lean threads and 16 QEMU slots.
