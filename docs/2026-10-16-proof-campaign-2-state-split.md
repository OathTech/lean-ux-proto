# Campaign 2: state-split retrofit

The retrofit starts from `04b2f7c` and incorporates main `b700659`. The
mirror is unchanged. The branch retains its proof tree, nondefault
`LeanuxProofs` target and `scripts/proof-gate`; main removed those pending
campaign 1's landing. No new result is attempted before this retrofit.

[USER 2026-10-16] Carry campaign 2 to the split worlds, retaining its
projection boundary. Remove frames only when the new types provide the
preservation fact. Follow campaign 1's native contracts and adapters where
the layers coincide; keep remaining local variants separate from claims.

## Baseline and accounting

The baseline census strips nested comments and strings and includes private
and attributed theorem declarations. Campaign 2 owns 427 Lean files,
1,831 theorems and 258 headline theorems at `04b2f7c`.

| Result | Baseline files | Baseline theorems | Headlines | Checked now | Retrofit status |
| --- | ---: | ---: | ---: | ---: | --- |
| Common projection | 2 | 0 | 0 | 0 | Actual native WG/Ambient and full Product observations carried; no reconstructed execution states. |
| H1 Noise | 35 | 171 | 22 | 180 | The full terminal closure is current; five restart-support lemmas remain pending. Six type-given frames are deleted. Wider caller/lifetime/reachability and clock-provenance charter claims remain open. |
| H2 Index | 68 | 318 | 52 | 212 | Table, lookup, collision records, allocation, owner invariants and lifecycle support carried; seven type-given frames deleted. Exact peer-release outcomes replace stale totality, with checked counterexamples. Terminal closure and whole-driver coherence remain pending. |
| H3 Roaming | 35 | 119 | 13 | 137 | Endpoint/publication, polling, attempt facts, crypto, lookup and response-caller factors/facts carried with full Product certificates; two type-given frames deleted. Initiation transcript facts are carried with full Product certificates; broader authentication/caller closure remains pending. |
| H4 Configuration | 130 | 554 | 79 | 368 | Scalar, identity, port, dump, allowed-IP and structural support carried; three type-given frames deleted. Quiet timer cleanup and queued-send observations are corrected; queued-send and removal totality have checked stale-statement counterexamples. Remaining readback/effects and terminal closure remain pending. |
| H5 Progress | 59 | 265 | 42 | 177 | Pure/control, cut, jitter, index, poll bounds, dispatch, scheduler turns, stack/probe frames, queue flush contracts, drain selection and Product observation bridge carried; one type-given index frame deleted. The old backlog fixture now has a checked exact runner rejection. Receive-ring activation models, general runner boundaries, drain bounds are carried; terminal closure remains pending. |
| H6 Timer discipline | 98 | 404 | 50 | 156 | Base/guard/jitter, arming/wheel, recorded clock and initiation-send arming contracts carried; three type-given frames deleted. Exact wheel corrections are explicit; queue/pending and retained-worker frames are carried; broader timer episodes and terminal closure remain pending. |

Retyped, deleted and retained counts will be reported per validated tranche.
H1 now has a checked split terminal closure; H2–H6 remain lagging.
All six results retain their previous charter gaps.
The last scoped validation at `04b2f7c` does not validate the split mirror.

## Migration boundaries

The design's sections 2–4 and 12–15 distinguish native `WG.M` executions
from product-level orchestration. The native observation projects `WGWorld`
and `Ambient` directly; product observations additionally retain the actual
fixture data when a claim needs it. No missing state is reconstructed with
defaults. Errors retain their actual stop and no invented final state.

Campaign 1's report at `5b0cbad` supplies the reference shapes: generic
StateT contracts, explicit nested native runs, generic component adapters,
and separate product observations. The campaign 2 result closure has no
direct imports of the old shared layers; those files remain campaign 1's
responsibility and are not edited here.

Deletion candidates include ambient-only preservation of the obsolete
Kernel and index-component preservation of peers. Return-value, totality,
exact-error and within-component facts remain substantive. Each deletion
will name the actual type and excluded state, separately from unused
support that becomes redundant.

The incoming mirror also contains behavior and representation changes since
`de62c9d`: queued-release guards, the receive ring, the batch pending-work
check, the FIB and timer wheel, and remaining-send-queue pending state. Those
are source carries, not type-given deletions. In particular, the former
`Env.fireTimer` interface is gone and the old local due-peer factor no longer
describes dispatch; their timer episode claims
need a bridge to the actual wheel dispatcher. The historical accepted
backlog finding stays attributed to its old mirror commit.

## Validation

At the merge checkpoint no split proof build had passed. Retained gate:
`scripts/in-bundle scripts/proof-gate`. During the carry, build scoped modules,
print axioms for their logical declarations and replay the resulting closure
with `scripts/in-bundle lake env leanchecker --fresh MODULE`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. On the
shared host, all heavy commands run through `capped`, with the existing cap,
32 Lean threads and `LEANUX_QEMU_SLOTS=16`.

## Native projection and initial pure closure

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.Execution`, `Noise.AccessSource` | 5 | 4 | 0 | 1 | 2 | 7 |
| Initial pure/configuration/control closure | 13 | 0 | 0 | 13 | 0 | 13 |
| Total validated theorem surface | 18 | 4 | 0 | 14 | 2 | 20 |

At `adba365` the tree has 428 campaign-owned files and 1,833 theorems. The 258
headline names are unchanged and none has yet been validated against the
split mirror. Of the baseline, 1,813 theorems still await retrofit validation.
These are support carries, not new charter results.

`Campaign2.View` projects actual WG and Ambient state. Its routing and wheel
fields follow the current owners; obsolete representation fields disappear.
`ProductView` retains the eight original fixture observations separately.
`Bridge` runs native actions on both actual input states and product actions
on the entire actual product. Inspection retains the actual entry state;
no missing component is supplied with defaults. The richer product view is
necessary because old exact outcome equalities implicitly framed fixture
fields, even when a predicate never selected those fields explicitly.

`Noise.Execution` supplies native composition over arbitrary
`StateT σ AmbientM`, and preserves the original product composition laws
under `Noise.Product`, generalized to `StateT σ (Except Stop)`. The two
native laws are companions of those product laws. The native getter/setter
contracts preserve their residence and postcondition obligations.
Independent review found the first draft had lost the arbitrary-product
composition scope; the separate product laws fix that finding, and the
complete re-review found no further substantive issue.

The pure closure covers configuration pair shape; generic iteration;
record-driven index and jitter search; cut suffix/progress; and poll-budget
effects. Their theorem meanings are unchanged. Two warnings were fixed:
one unused simplification argument and a match-equation name used only by
the termination proof. The latter is now anonymous and retrieved from the
termination context. No warning suppression was introduced.

The final combined scoped build passes 54 jobs without warnings. All 133
named logical roots in its 23 proof modules have only the three permitted
axioms. Fresh replay passes for all twelve roots covering this closure;
the static token/import/root/default-target checks and scoped whitespace pass.
The mirror equals `b700659` and shared layers equal their pre-merge copies.
The full proof gate remains unvalidated on the split tree; the old
inherited failure is not a current full-tree check.

Development accounting: the worker made five builds (three conversion
failures, one pass with a warning, then a clean pass). The root's first pure
build passed with two warnings; seven subsequent combined builds included
four failed warning-fix drafts, one pass, a pass with the product-law warning,
and the final clean pass after correcting it. Failed drafts included Lean
recovery placeholders; none was accepted as validation or retained as an
admitted source proof. No unchanged failed source was rerun; no cap or proof
limit changed. Every compiler output was captured before display.

Reproduce the support build with `scripts/in-bundle lake build` on these
module suffixes under `Leanux.Proofs.WG`:

- `Campaign2.Bridge`, `Noise.AccessSource`;
- `Config.Model`, `Config.AllowedInsertModel`, `Config.AllowedPairsModel`,
  `Config.ClaimView`;
- `Progress.ControlLaws`, `Progress.PowModel`, `Progress.IndexProgressModel`,
  `Progress.CutModel`, `Progress.JitterProgressModel`,
  `Progress.PollBoundModel`, `Progress.PollBoundEffects`.

Replay those roots with `scripts/in-bundle lake env leanchecker --fresh MODULE`
(`PollBoundEffects` includes `PollBoundModel`). Use `capped` on this host.

## Total native contracts and the index table

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.Returns`, `Index.Table` | 5 | 5 | 0 | 0 | 2 | 7 |
| `Index.TableModel` | 7 | 0 | 0 | 7 | 0 | 7 |
| This tranche | 12 | 5 | 0 | 7 | 2 | 14 |
| Cumulative checked support | 30 | 9 | 0 | 21 | 4 | 34 |

At `b1d899d` the tree has 428 campaign-owned files and 1,835 theorems. The remaining
baseline theorem count awaiting validation is 1,801. All 258 headline names
remain present and all six terminal closures remain lagging.

`Config.Returns` distinguishes native total execution over arbitrary Ambient
inputs from arbitrary product execution. Its original product laws are
generalized over the actual state type in `Config.Product`; the native
versions are companions. The outer-state predicate cannot constrain hidden
records: a record-sensitive total claim still needs both states observed.

`Index.Table`'s removal, hashed-membership and handshake-replacement contracts
now call the real `liftIndex` adapter around each narrowed operation. Their
resident-device premise, exact Device effects and Boolean results remain;
no uniqueness, validity, owner-residency or successful-execution premise was
added. Duplicate and malformed tables remain in scope. The pure table
uniqueness/owner algebra contributes seven unchanged theorems.

The scoped build passes 30 jobs without warnings. All 35 named logical roots
in the seven-module closure have only standard axioms; independent complete
review found no substantive issue. Fresh replay of `Index.Table` passes.
Static token/import/root/default-target and whitespace checks pass; mirror
and shared-layer boundaries are unchanged.

Development: two capped stdin calls for the total-contract prototype (one
failed, then a warning-free pass after correction), and two packaging builds
(one failed normalization proof, then a warning-free pass). No unchanged
failed source rerun, infrastructure retry, cap or proof-limit change.

Reproduce with `scripts/in-bundle lake build Leanux.Proofs.WG.Index.Table`
and `scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Index.Table`,
through `capped` on this host. This is scoped support validation, not a
terminal or full-tree gate pass.

## Component frames and pure lifecycle relations

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.KernelFrames` and three index peer frames | 13 | 7 | 6 | 0 | 3 | 10 |
| Pure index owner/allocation/lifecycle/lookup/sequence closure | 13 | 0 | 0 | 13 | 0 | 13 |
| Pure release/rotation/confirmation/session-readiness closure | 29 | 0 | 0 | 29 | 0 | 29 |
| This tranche | 55 | 7 | 6 | 42 | 3 | 52 |
| Cumulative processed baseline and checked support | 85 | 16 | 6 | 63 | 7 | 86 |

At `43bb1d8` the tree has 429 campaign-owned files and 1,832 theorems. Of the baseline,
1,746 theorems still await validation. All 258 headline names remain, and no
terminal closure has passed on the split mirror. Retained-pending declarations
are excluded from the checked-kept count.

`Noise.KernelFrames` is replaced by `Noise.CryptoFrames`: its seven crypto
helpers still have type `WG.M`, which permits WireGuard mutation, so their
preservation obligations remain substantive. Each now quantifies arbitrary
`WGWorld` predicates and all actual Ambient executions. Its three other
leaves (`hidden_kernel_spec`, `hiddenClock64_kernel_spec`, and
`keypairAllocation_kernel_spec`) disappear because their underlying actions
have type `AmbientM`. Their lifted execution cannot access the outer state.

The three `Noise.PeerFrames` index-operation peer frames disappear because
`indexRemove`, `indexInsert` and `indexReplaceHandshake` have type
`IndexM = StateT (List IndexEntry) AmbientM`: peers are absent from their
state. The real guarded `liftIndex` only writes the table back. These are
type-based deletions, not reactions to compile errors. The bucket's own-table
preservation, keypair creation and derivation peer frames remain substantive
and pending in `PeerFrames`; none is counted as validated.

`Noise.ComponentFrames` holds three local variants matching campaign 1's
`hoare_liftAmbient`, `liftIndex_run` and `hoare_liftIndex`. The native run
equation retains the missing-device error and actual table-only writeback;
the Hoare rule requires stability under that writeback. These few generic
adapters replace the deleted operation-specific leaves. They can be replaced
by campaign 1's retyped layer when it reaches this branch. Twelve direct
imports and 59 crypto-symbol references were renamed mechanically; this
does not validate their still-unported consumers. Deleted-leaf uses remain
in those pending consumers rather than gaining compatibility aliases.

The two pure closures carry 42 further original theorems unchanged in
meaning: owner words, allocation, lifecycle and lookup-none/sequence models;
release effects, slot rotation, confirmation sequences and session readiness.
Two deprecated `if_pos` uses were changed to `ite_eq_left` and an unused
`if_neg` simplification argument was removed. No warning suppression or
strengthened premise was introduced.

Validation: component/crypto build 27 jobs, pure index build 26 jobs and
final pure Noise build 45 jobs, all warning-free. Axiom checks cover 22 roots
in four component/crypto modules, 49 roots in nine pure index modules and
107 roots in 22 pure Noise modules; only the standard three axioms occur.
All six fresh replay roots pass; independent complete review found no
semantic defect and confirmed the consumer lag described above. Static
token/import/root/default-target checks pass; mirror and shared files remain
unchanged. These are scoped support checks, not a full proof-gate pass.

Development: six capped changed-source component/crypto stdin probes (four
failures, one warning-bearing pass and a clean pass), then one clean packaging
build. One probe hit the default heartbeat limit while inferring an unspecified
lifted action; explicitly supplying the actual branch resolved it without a
limit increase. The pure index build passed first time. The pure Noise build
passed with four warnings, then passed cleanly after the two source edits
above. No unchanged failure rerun, infrastructure retry or cap increase.

Reproduce the scoped builds with `scripts/in-bundle lake build` and these
module suffixes under `Leanux.Proofs.WG`:

- `Noise.ComponentFrames`, `Noise.CryptoFrames`;
- `Index.LifecycleModel`, `Index.LookupNoneModel`, `Index.SessionSequenceEffects`;
- `Noise.ConfirmationSequenceEffects`, `Noise.SessionReadyFrames`.

Fresh-replay those roots with `scripts/in-bundle lake env leanchecker --fresh`
(`CryptoFrames` includes `ComponentFrames`). Use `capped` on this host.

## Native lookup/collision scans and slot frames

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Index.LookupSource` | 6 | 4 | 0 | 2 | 0 | 6 |
| `Index.Collision` | 5 | 4 | 0 | 1 | 0 | 5 |
| `Noise.SlotFrames` | 3 | 3 | 0 | 0 | 0 | 3 |
| `TimerDiscipline.ResponseSessionFrames/Effects` | 2 | 0 | 0 | 2 | 0 | 2 |
| This tranche | 16 | 11 | 0 | 5 | 0 | 16 |
| Cumulative processed baseline and checked support | 101 | 27 | 6 | 68 | 7 | 102 |

At `1e067bd` the tree remains 429 campaign-owned files and 1,832 theorems; 1,730 original
theorems still await validation. The 258 terminal names and all six lagging
terminal closures are unchanged.

`Index.LookupSource` retains the exact original operation decomposition,
including the owner-word store after a failed reference get. Its total scan
still selects the first equal numeric index, including stopping at an excluded
kind, for arbitrary entries, initial scan state and Ambient. The substantive
state equality now names `WGWorld`; other subsystems are inaccessible through
the operation type. Its branch trace helper now acts on Ambient directly.

`Index.Collision` uses native `IndexM` for its scan. Its total return law keeps
the full table equality; this is within the component and is not supplied by
the type. The original Device contract calls the real guarded `liftIndex`,
retains the original resident-device premise and returns the exact any-match
result with the exact original Device. Its unnecessary operational `Lookup`
import is replaced by `Table`.

`Noise.SlotFrames` retains all three original partial-correctness obligations:
arbitrary peer-predicate preservation under suitable Device updates and
keypair release, and handshake-tag preservation through key rotation.
The proof still covers null references, missing stores, null peer words,
zero reference counts and slot aliases. No validity, nonaliasing or successful
execution premise is added. Direct native composition replaces deprecated
tactic use; proof-local helpers add no named theorem or shared layer.

Two unchanged H6 relations establish that slot writes preserve a peer's dead
flag and that a successful pure session effect has a live resident peer.
They do not validate timer execution. The next H6 source carry must account
for `ambient.armRecords`, conditional clock/enqueue records and wheel placement,
expiry plus wheel deletion, and the actual wheel dispatcher. Old expiry-only
models cannot become current merely by compiling.

Scoped builds pass without warnings: lookup 31 jobs, collision 31, slot frames
28, pure H6 38. Axioms pass for respectively 46, 42, 23 and 78 named logical
roots in their dependency closures, with only the standard three. All four
fresh replay roots pass. Independent source review found no contract weakening
in lookup, collision or slot frames. Static gate checks, scoped whitespace
and mirror/shared boundaries pass. No terminal
or full-tree gate pass is claimed.

Development: lookup used three changed-source stdin probes (two failed, one
clean pass); collision used two (one failed, one clean pass); slot frames used
eight (six failed, one pass with an unused-argument warning, one clean pass).
The slot draft's underspecified bind hit the default heartbeat limit; explicit
composition fixed it without raising the limit. Each packaging build and the
pure H6 build passed first time. No unchanged failure rerun, infrastructure
retry or cap increase.

Reproduce with `scripts/in-bundle lake build` on the four roots
`Leanux.Proofs.WG.Index.LookupSource`, `Leanux.Proofs.WG.Index.Collision`,
`Leanux.Proofs.WG.Noise.SlotFrames` and
`Leanux.Proofs.WG.TimerDiscipline.ResponseSessionEffects`; replay each with
`scripts/in-bundle lake env leanchecker --fresh MODULE`. Use `capped` here.

## Branch results, exact insertion and slot operations

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Four selected `Config.OperationFrames` contracts | 4 | 2 | 2 | 0 | 0 | 2 |
| `Index.Insert` | 7 | 7 | 0 | 0 | 0 | 7 |
| `Noise.Slots` | 9 | 9 | 0 | 0 | 0 | 9 |
| This tranche | 20 | 18 | 2 | 0 | 0 | 18 |
| Cumulative processed baseline and checked support | 121 | 45 | 8 | 68 | 7 | 120 |

At `b7481f0` the tree has 430 campaign-owned files and 1,830 theorems. Of the baseline,
1,710 theorems still await validation. The terminal closures remain lagging;
all 258 headline names remain present.

`Config.BranchSource` separates the two result-bearing branch contracts from
preservation frames. The native contracts keep the exact Boolean result,
arbitrary outer-state predicate, all Ambient inputs and the distinction
between partial and total correctness. They do not claim a specialization
to the flat product monad. No arbitrary callback domain is narrowed: these
contracts concern a fixed Ambient primitive. Six consumer references were
renamed; their enclosing proofs remain pending.

Two further `OperationFrames` leaves are deleted: `recordQueued_kernel` and
`hidden_portBound`. The actual `AmbientM.recordQueued` and `AmbientM.hidden`
actions have no access to the preserved state; `portBound` belongs to
`WGWorld`. Their wrappers only lift Ambient actions. Neither deleted contract
contained a return-value or totality promise. Three substantive endpoint
frames and six uses of the deleted leaves remain pending, not validated-kept.

`Index.Insert` now factors the actual `IndexM` computation. Its seven original
theorems retain unhashing before the record budget and draws, both collision
scans, and insertion at an index absent from the table after unhashing. The
within-component postcondition records the exact table; the final Device
contract uses the real guarded lift and keeps the original resident-device
premise. Arbitrary draws, malformed/duplicate tables and missing-record stops
remain in scope. These are normal-return laws, not new totality claims.

`Noise.Slots` carries nine exact original contracts: peer access/update,
clear-one and ordered clear factor, cleared slots/peer, handshake zeroing,
confirmation and all rotation arms. The new proofs keep arbitrary slot aliases
and original resident-peer/key premises. Keypair release failure remains a
possible stopped execution under the existing partial contracts. The actual
double check and next/current/previous writes are retained.

Scoped builds are warning-free: branch source 29 jobs, insertion 33 and slot
operations 29. Axioms pass for 22, 60 and 33 named roots in the corresponding
closures; only the three permitted axioms occur. All three fresh replay roots
pass, and independent review found no contract weakening in all three source
changes or the type-based deletions. Static gate checks, scoped whitespace
and mirror/shared boundaries pass. No terminal/full-tree pass is
claimed.

Development: the branch prototype passed on its first capped stdin run;
insertion used three changed-source probes (failure, a pass with one unused
simp argument, then a clean pass); slot operations used four (seven-contract
and eight-contract passes, a failed full draft, then all nine clean).
The failed slot draft had a captured-versus-current peer-field annotation and
unused simplification arguments; the final proof corrects both. All three
packaging builds passed first time. No unchanged failure rerun, infrastructure
retry, cap increase or proof-limit increase.

Reproduce by building and fresh-replaying the roots
`Leanux.Proofs.WG.Config.BranchSource`, `Leanux.Proofs.WG.Index.Insert` and
`Leanux.Proofs.WG.Noise.Slots` with the same capped bundle commands above.

## Remaining peer frames, owner words and Ambient-only deletions

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Remaining `Noise.PeerFrames` | 3 | 3 | 0 | 0 | 0 | 3 |
| Five `Index.PeerWords` contracts moved to `PeerWordSource` | 5 | 5 | 0 | 0 | 0 | 5 |
| Expiry contract moved from `Noise.StateEdges` to `ExpirySource` | 1 | 1 | 0 | 0 | 0 | 1 |
| Ambient-only preservation leaves | 13 | 0 | 13 | 0 | 0 | 0 |
| This tranche | 22 | 9 | 13 | 0 | 0 | 9 |
| Cumulative processed baseline and checked support | 143 | 54 | 21 | 68 | 7 | 129 |

The tree has 431 campaign-owned files and 1,817 theorems. The baseline's
remaining unvalidated count is 1,688; all 258 headline names and six lagging
terminal closures remain. Moving a declaration does not count as adding one.

All three remaining `Noise.PeerFrames` contracts are carried. The renamed
`bucketHas_index_spec` proves preservation of its own table, a substantive
fact despite the narrower `IndexM` type. Creation and derivation keep arbitrary
peer-map predicates under normal completion, without allocation, clock,
residency or nonaliasing assumptions. They follow actual counter writes,
allocation, key derivation and keypair updates.

`Index.PeerWordSource` factors five original total contracts from the still
lagging `PeerWords`: owner-word read and write, NULL and zero-reference
lookup finishes, and live peer-reference acquisition. Absent owner objects
remain distinct from present NULL words; the failed get still stores NULL
in the original owner. Live acquisition retains the original positive and
bounded-reference premises and the exact Device effect. The other five
`PeerWords` declarations remain pending, not validated.

`Noise.ExpirySource` carries the full original expiry slot/tag contract with
unchanged premises. Its proof includes the real peer-word dereference, guarded
index removal, handshake zeroing, clock/reset and both key invalidations.
It promises unchanged slots and zero handshake state only on normal completion.
The other three `StateEdges` contracts remain pending.

The following thirteen leaves are removed because their actual capabilities
exclude the preserved state; none promised a result value or totality:

| File | Deleted declaration | Actual capability |
| --- | --- | --- |
| `Config.AllowedInsertFrames` | `hiddenAlloc_sameKernel_node_spec_variant` | `AmbientM.hiddenAlloc` |
| `Roaming.Frames` | `hiddenJiffies_kernel_spec` | `AmbientM.hiddenJiffies` |
| `Roaming.PublicationFrames` | `refcountInc_kernel_frame` | Ambient-only polymorphic refcount |
| `Index.ConsumeFrames` | `refcountIncNotZero_kernel_variant` | Ambient-only polymorphic refcount |
| `Index.SendFrames` | `refcountDecAndTest_kernel_variant` | Ambient-only polymorphic refcount |
| `Index.NewlinkFrames` | `skipCutExactly_spec_kernel_variant` | `AmbientM.skipCutExactly` |
| `Index.StagedFrames` | `peekQueuedUnit_kernel_variant`, `queueDeviceWork_kernel_variant`, `keypairAllocation_kernel_spec_keepalive_variant` | Ambient queue operations and allocation |
| `Index.ReceiveFrames` | `keypairAllocation_kernel_spec_reply_variant` | `AmbientM.hiddenAlloc` |
| `TimerDiscipline.SendCutFrames` | `keypairAllocation_kernel_spec_sendBuffer_variant`, `skipCut_spec_kernel_variant` | Ambient allocation and cut |
| `TimerDiscipline.SelectionFrames` | `peekUnit_spec_kernel_variant` | `AmbientM.peekUnit` |

The three refcount functions are polymorphic in `Monad` and `MonadLiftT
AmbientM`; their canonical native lift preserves the outer state. This is
the type-and-adapter reason for deletion, not a claim that their declarations
literally return `AmbientM`. The other ten cores do return `AmbientM`.
The empty `AllowedInsertFrames` file is deleted and its sole direct import
replaced by `Noise.ComponentFrames`. Nine mixed files retain all substantive
neighbors. Twenty-six deleted-name uses remain in twenty unported files;
no replacement leaf aliases hide that lag.

Scoped builds pass without warnings: peer frames 36 jobs, owner-word source
33, expiry source 37. Axiom checks cover respectively 71, 56 and 72 named
logical roots with only the permitted three axioms. Fresh kernel replay passes
for all three roots; independent reviews found no substantive issues. Static
proof-tree checks and whitespace checks pass; mirror and shared layers remain
unchanged. The deletion audit
checks the exact thirteen-name set and absence of imports of the removed file;
lagging mixed files are not claimed to build. No full-tree or terminal pass.

Development: peer-frame and expiry prototypes each passed first time.
The owner-word prototype used five changed-source calls: one clean
three-contract prefix, three failed extensions, then five contracts clean.
One failed extension's diagnostics were truncated by the tool output cap and
not fully retained; later calls and the final packaging build saved complete
output before preview. It was not rerun unchanged for diagnostics. All three
packaging builds passed first time. No infrastructure retry or limit increase.

Reproduce scoped builds and fresh replay for
`Leanux.Proofs.WG.Noise.PeerFrames`, `Leanux.Proofs.WG.Index.PeerWordSource`
and `Leanux.Proofs.WG.Noise.ExpirySource` using the capped bundle commands above.

## Endpoint, lookup, creation and source contracts

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Roaming.EndpointSource`, remaining `Roaming.Frames` | 3 | 3 | 0 | 0 | 0 | 3 |
| `Noise.InitiationSource`, `Noise.ResponseSource` from `StateEdges` | 2 | 2 | 0 | 0 | 0 | 2 |
| `Index.LookupPrefixSource`, `Index.Lookup` | 5 | 4 | 0 | 1 | 0 | 5 |
| Remaining `Config.OperationFrames` | 3 | 3 | 0 | 0 | 0 | 3 |
| Three configuration source factors and `Index.ReceiveOperations` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Progress.ControlSource`, `Index.LifecycleFrames` | 4 | 4 | 0 | 0 | 0 | 4 |
| Four pure index roots, `SessionAllocationEffects`, `Progress.PowSource` | 22 | 0 | 0 | 22 | 0 | 22 |
| This tranche | 43 | 20 | 0 | 23 | 0 | 43 |
| Cumulative validated surface | 186 | 74 | 21 | 91 | 7 | 172 |

The tree now has 434 campaign-owned files and 1,817 theorems. Of the
baseline, 1,645 still await retrofit validation. All 258 headline names
remain unvalidated against the split mirror; the six terminal closures
remain lagging. This tranche adds no new charter result or type-based deletion.

The endpoint source contracts preserve exact source-family results and the
valid-family premise on endpoint equality. The cache-reset frame is a
within-WireGuard fact and follows the actual Ambient/WG flags and recorded
clock path. `Config.OperationFrames` likewise retains exact Device modulo
peers, port/socket/running observations, and `WGWorld.portBound`; these are
substantive frames in their own file.

Initiation and response tag claims move from `StateEdges` into separate
source files. They retain their original old-tag premise, all normal failure
outcomes, and response's success admission condition. The proofs include
the actual chain/ephemeral writes, crypto results, owner dereference and
guarded insertion. They add no identity, allocation, randomness, residency
or success premises. `beginSession_tag` alone remains in the unported
`StateEdges` body.

The lookup prefix retains total selection over arbitrary Ambient inputs
and tables, including first numeric matches with an excluded kind. Full
lookup retains its normal-return owner-origin and unchanged-table claims.
The proof covers missing owner objects, NULL/dead/live words and overflow
stops without adding a consistency premise. The five exact finishing/caller
contracts still in `PeerWords` remain pending.

`Config.DeviceSource`, `DumpSource`, `PeerSource` and
`Index.ReceiveOperations` require only explicit `WG.M` annotations.
Their four unconditional definitional source equations retain early returns,
stopped executions and branch order. These claims remain separate from frames.
`Progress.ControlSource` generalizes its state parameter with the lift
instances required by the actual worker, retaining the original product
instance and arbitrary callbacks. It proves one iteration's control flow,
not whole-loop termination. `Index.LifecycleFrames` keeps the substantive
Device-preservation fact while retirement changes timer and dispatch data.

The unchanged pure index roots are `ReleaseBounds`, `PeerReleaseEffects`,
`SessionCoherenceEffects`, `SessionAllocationFrames` and
`SessionAllocationEffects`. Their release/rotation/session relations are
premises; they do not establish native execution or ownership invariants.
The five `Progress.PowSource` claims additionally connect the actual private
mirror loop to a finite evaluation with zero remaining exponent. They make
no modular-arithmetic correctness or wall-clock claim.

Scoped builds pass without warnings: pure index roots 45 jobs; endpoint
roots 31; initiation 37; lookup prefix/full lookup 32/34; configuration
frames 36; source factors with pure allocation/power roots 47; response 38;
control/retirement 31. The corresponding axiom checks cover 111, 30, 72,
50/56, 45, 115, 74 and 27 named logical roots, all using only the permitted
three axioms. All nineteen fresh kernel replay roots pass.
Independent reviews found no substantive issue. Static proof-tree and
whitespace checks pass; mirror and shared proof layers remain unchanged.
No full-tree or terminal pass is claimed.

Development: endpoint work used eight changed-source probes (five failures,
two warning-bearing passes, then a clean pass). Initiation used three (one
failure, two clean); response passed its first. Lookup used eight (five
ordinary failures, one warning-bearing pass, two clean prefixes/final
versions). Configuration frames used two (one failure, one clean).
Control/retirement passed its prototype with two unused simp arguments,
removed before the clean package build. All package builds passed first
time. No infrastructure rerun or limit increase occurred.

One broader source build failed: the four source factors needed native
annotations, while `Progress.CookieActivationModel` still applies list
operations to the new pointer ring. That failed module also emitted unused
simp and elaborator-generated incomplete-proof warnings; it is not trusted
or counted here. Its exact queue/snapshot semantics and warnings remain
pending together. The four changed factors passed a combined stdin check
and their subsequent scoped build; the other two pure roots had already
built cleanly. Complete diagnostics were captured before preview for these
runs. This representation carry is not justified as a frame deletion.

Reproduce by building and fresh-replaying the roots named in this section
with the capped bundle commands above. `Lookup` imports its prefix;
`OperationFrames` includes the endpoint roots. The explicit per-root checks
recorded here also validated their earlier packaged closures.

## Exact lookup finishes, session admission and configuration insertion

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Remaining `Index.PeerWords` | 5 | 5 | 0 | 0 | 0 | 5 |
| `Noise.SessionEdgeSource` from `StateEdges` | 1 | 1 | 0 | 0 | 0 | 1 |
| `Config.AllowedInsertSource` | 3 | 3 | 0 | 0 | 0 | 3 |
| `Index.LifecycleSource`, `Progress.CutFrames` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Index.DrawRecordSource` from `DrawRecords` | 5 | 5 | 0 | 0 | 0 | 5 |
| `Roaming.EndpointClaims` | 3 | 3 | 0 | 0 | 0 | 3 |
| This tranche | 23 | 23 | 0 | 0 | 0 | 23 |
| Cumulative validated surface | 209 | 97 | 21 | 91 | 7 | 195 |

The tree has 436 campaign-owned files and 1,817 theorems, with 1,622
baseline theorems awaiting validation. The 258 headline names and all six
terminal closures remain lagging. No new charter result or deletion is
counted in this tranche. Claims stay in source/claim files; `CutFrames`
keeps the substantive within-Ambient record frame separate.

All ten owner-word/lookup-finish contracts are now native. The last five
retain totality for every Ambient input under their original first-match,
kind, resident-word, positive-reference and strict-bound premises. The live
path acquires the peer before writing the owner word into the resulting
Device; handshake-owner aliasing therefore keeps the increment. NULL and
zero-reference paths preserve the landed NULL storeback. No uniqueness or
owner-coherence premise was introduced.

`StateEdges` is now an import-only aggregate of its four original contracts.
The last session tag theorem retains its partial scope: normal false keeps
the old tag; true zeroes it and requires one of the two original admission
states. The proof follows short-circuit admission, allocation, derivation,
zeroing, rotation, dereference and guarded replacement. Dead, NULL and
unhashed replacement paths remain stops. This does not close the broader H1
reachability and lifetime obligations.

The three empty-root insertion claims use the actual guarded AIP adapter
and native WG actions. Allocation may fail or overwrite an occupied next-node
identifier, exactly as before; no freshness or list-disjointness premise is
added. Peer-list, parent and root writes retain their order. The configuration
sequence increment remains visible even when allocation returns `-ENOMEM`.
The three endpoint claims retain exact destination behavior, including the
endpoint-equal early return, valid-family premise, source extraction and
cache reset; missing state or records remain partial-correctness stops.

Lifecycle initialization projects `Runner.initialWG`'s actual core into the
existing snapshot, leaving its other WG observations and Ambient arbitrary.
The old filesystem/task parameters disappear because that initializer no
longer accepts them and they never affected the projected core. Destruction
uses the real ring-empty guard and clears only the handshake counter before
removing the device; it does not replace physical ring slots or cursors with
a fabricated empty ring. Setup remains total, while destruction's absent-device
conclusion remains conditional on normal completion. `CutFrames` retains the
total Ambient operation's exact record/decision preservation.

[AGENT 2026-10-17] Record-sensitive component contracts reuse the existing
generic `Config.Product.Returns` on actual native runs, instead of adding
another contract layer. This exposes real Ambient inputs/outputs and the
returned native state together. The five draw-record contracts preserve
exact suffixes, totality and table/Device effects. The bucket walk remains
unguarded `IndexM`; only the public wrappers use the actual device guard.
Whole-Ambient equality is retained where originally promised, and excluded
outer state follows the native capability. The remaining five insertion
record/loop contracts stay named in unported `DrawRecords`.

Scoped builds: owner words 38 jobs; state edges 42; allowed insertion 34;
lifecycle plus cut 81; draw prefix 34; endpoint claims 35. Proof modules
are warning-free. Axiom checks cover respectively 82, 77, 36, 100, 69 and
41 named logical roots, with only the three permitted axioms. All seven
fresh kernel replay roots and final static/whitespace checks pass.
Independent source reviews found no substantive issue. Mirror and shared
layers remain unchanged; no full-tree or terminal pass is claimed.

Development: owner words used two changed-source probes (one failure, one
clean); session admission four (two failures, two clean); allowed insertion
thirteen (eleven failures, one warning-bearing pass, one clean); draw prefix
three (two warning-bearing passes, one clean); endpoint claims passed first
time. Every package build passed on its first attempt. No limit increased.
The first lifecycle probe failed because the imported Runner artifact had
not been refreshed. After its required dependency build (64 jobs), the same
probe passed on its single rerun. That dependency-ordering mistake is
recorded here; there were no killed runs or guest timeouts. Complete compiler
output was retained before preview.

Inherited warning: `Leanux/Env.lean:865` uses deprecated `String.mk`. It was
reported by the Runner build and replayed by the lifecycle build. The mirror
is outside this campaign's edit boundary; the warning is unsuppressed and
pending its owner's repair. It is not a proof-module warning or an axiom
finding.

Reproduce scoped builds and fresh replay for `Index.PeerWords`,
`Noise.StateEdges`, `Config.AllowedInsertSource`, `Index.LifecycleSource`,
`Progress.CutFrames`, `Index.DrawRecordSource` and `Roaming.EndpointClaims`,
each under `Leanux.Proofs.WG`, using the capped bundle commands above.

## Record loops, placement and the timer statement artefact

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.AllowedPlacementSource`, `AllowedTransferOperations` | 2 | 2 | 0 | 0 | 0 | 2 |
| Remaining `Index.DrawRecords` | 5 | 5 | 0 | 0 | 0 | 5 |
| `Index.DrawExhaustion`, `CorpusDraws`, `LookupMiss` | 10 | 8 | 0 | 2 | 0 | 10 |
| `Progress.CookieControlModel` from `CookieActivationModel` | 12 | 0 | 0 | 12 | 0 | 12 |
| `TimerDiscipline.ArmingBaseSource`, `ArmingWheelFindings` | 2 | 2 | 0 | 0 | 2 | 4 |
| This tranche | 31 | 17 | 0 | 14 | 2 | 33 |
| Cumulative validated surface | 240 | 114 | 21 | 105 | 9 | 228 |

The tree has 439 campaign-owned files and 1,819 theorems. Of the baseline,
1,591 remain pending. All 258 terminal names remain in their original
`Statements.lean` files and await whole-result validation; this tranche
does not claim a terminal or full-tree pass. No frame is deleted here.

The allowed-IP placement result retains its totality, width/resident-node
premises and exact Device result through actual `liftAip`. Its dependency
is narrowed to the models it uses. The transfer source equation remains
unconditional and definitional with explicit `WG.M` annotations, including
all allocation/error arms. It retains the placement import needed by
unported consumers.

All ten draw-record contracts now carry. The remaining five preserve the
contiguous collision prefix, two fresh scans, original turn bound, exact
table update and arbitrary unused suffix. Raw steps/loops remain unguarded
`IndexM`; public insertion retains the actual guard and full Device effect.
The exhaustion contracts prove the original missing-input error, not budget
exhaustion, with one more turn than colliding records. The corpus pair keeps
distinct owners/values and its empty-table premise. Lookup misses preserve
the complete Device and stop selection at the first numeric match even
when its kind is excluded.

`CookieControlModel` factors twelve unchanged pure record/control/log
theorems and their definitions. One unused simp argument is removed. Exact
error strings, padding checks, suffix/decrease facts, yield counts and log
composition remain unchanged. The two representation-dependent snapshot
theorems stay in `CookieActivationModel`, pending their pointer-ring carry;
the checked pure facts do not establish native activation correspondence.

H6 supplies a checked counterexample to the old timer-deletion exact-peer
postcondition, documented in the
[timer carry finding](2026-10-17-proof-campaign-2-timer-carry.md). A resident
peer has a pending timer and a wheel entry consistent under
`peerWheelProblem`. Actual deletion clears both fields, contradicting the
legacy conclusion that retained the wheel entry. This is a statement
artefact after adding wheel state. The witness makes no global reachability
claim, and no mirror repair is requested. Seven affected exact-peer
contracts remain intact and pending in `ArmingSource`.

`ArmingBaseSource` carries the unchanged semantic guard claim and generalizes
the original result-map rule over arbitrary flat state/error computations.
A separate native map companion retains arbitrary Ambient execution.
The two added declarations are that companion and the concrete counterexample;
they are retrofit support/finding artefacts, not new charter results.

Scoped builds pass without warnings: allowed placement/source 34 jobs,
cookie control 8, draw records 35, arming base/finding 29, index
exhaustion/corpus/miss 46. Axiom checks cover 34, 23, 75, 16 and 136 named
logical roots respectively, using only the three permitted axioms. Fresh
kernel replay passes for all eight roots below. The retained gate's token
and import checks and the whitespace check pass.
Independent reviews found no theorem-correctness issue. The timer review
clarified the witness's local consistency versus global reachability, as
recorded above. Mirror and shared proof layers remain unchanged.

Development: placement/source used four changed-source probes (three
failures, one clean); cookie extraction passed first time; draw tail seven
(four failures, a clean two-claim prefix, one warning-bearing full pass,
then clean); arming base/finding three (one failure, one warning-bearing
pass, then clean); index frontier two (one failure, then clean). Package
builds passed first time, with full compiler output captured before preview.
No infrastructure rerun or limit increase occurred in this tranche.
The cookie axiom-output parser initially rejected a line-wrapped list of
the standard three axioms because of whitespace handling. The scratch parser
was corrected to strip each comma-separated name and checked the complete
saved output successfully, without rerunning Lean. The retained project gate
already handles this layout and was unchanged.

Reproduce by building and fresh-replaying `Config.AllowedTransferOperations`,
`Progress.CookieControlModel`, `Index.DrawRecords`,
`TimerDiscipline.ArmingBaseSource`, `TimerDiscipline.ArmingWheelFindings`,
`Index.DrawExhaustion`, `Index.CorpusDraws` and `Index.LookupMiss`, each under
`Leanux.Proofs.WG`, with the capped bundle commands above.

## Projected index claims, inversion and native cut contracts

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Index.TableClaims` scoped support | 0 | 0 | 0 | 0 | 10 | 10 |
| `Index.Allocation`, `LookupProvenanceSource`, `LookupNoneSource` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Config.Validation`, `DumpCancellation` | 5 | 4 | 0 | 1 | 0 | 5 |
| `Progress.CutSource`, `CutClaims` | 7 | 7 | 0 | 0 | 0 | 7 |
| `TimerDiscipline.ArmingWheelSource` | 0 | 0 | 0 | 0 | 2 | 2 |
| `TimerDiscipline.JitterBoundSource`, `JitterFrames` | 1 | 1 | 0 | 0 | 1 | 2 |
| This tranche | 19 | 18 | 0 | 1 | 13 | 32 |
| Cumulative validated surface | 259 | 132 | 21 | 106 | 22 | 260 |

The tree has 442 campaign-owned files and 1,832 theorem declarations;
1,572 baseline declarations still await validation. The checked closure has
110 proof modules: H1 49 theorems, H2 132, H3 6, H4 23, H5 40 and H6 10.
All six results remain lagging and their remaining charter obligations stand.
The 258 headline declarations remain in their original `Statements.lean`
files. No full terminal closure or full proof-gate pass is claimed.

`TableClaims` provides ten scoped proofs over the campaign projection for
existing H2 table, lookup and recorded-insertion claims. The public ten
wrappers stay in `Statements.lean`, preserving the gate's literal declaration
audit. Their isolated wrapper forms check, but the enclosing module remains
unvalidated. These ten support declarations are additions in the census;
the ten public wrappers are not double-counted as validated baseline claims.
Index-only operations use the actual guarded `liftIndex`; lookup remains
native `WG.M`. No device, owner word or record state is reconstructed.

Allocation preserves the original normal-return scope and exact device and
counter updates. Lookup inversion derives owner-word identity, peer residency,
positive reference count and the strict increment bound from successful runs;
none becomes a premise. Empty-result inversion retains the exclusive three
causes, first-numeric-match behavior and exact owner-word clearing. Missing
objects and overflow remain actual stopped outcomes; alias cases remain.

Configuration validation keeps its invalid-shape/sufficient-room premises,
exact error/JSON/room effects and native state preservation. The concrete dump
witness retains the same fixture observations through actual WG/Ambient runs;
its 3,720-byte result and cancellation arithmetic are unchanged. Removed
FS/task fixture data is outside that callback's type, not an assumed frame.

The five cut-source contracts now run over actual `AmbientM`; two claims
observe their real lift through the campaign projection. They retain the
pre-strip budget, exact consumed suffix, failure location/message and the
accepted-prefix condition for total return. The numerical outcome proof
includes allocation failure and does not claim every supplied stream succeeds.

Claim files added here are `Index/TableClaims`, `TimerDiscipline/ArmingWheelSource`
and `TimerDiscipline/JitterBoundSource`; `Progress/CutClaims` is carried in place.
The existing `JitterFrames` now proves arbitrary native WG predicate preservation
separately. Jitter is still `WG.M`, so that frame is substantive; no theorem
is deleted here. Together, the bound and frame reconstruct the old combined
claim. Five consumers remain pending: timer `ObservationClaims`, `SourceFrames`,
`InitiationPreservationFrames`, `WorkStateFrames`, and index `SendFrames`.

The two wheel contracts state the current exact selected-peer update for
deleting a timer and completing a handshake. They retain the original resident
peer and partial-correctness scope while explicitly clearing the selected wheel
entry. They are counted as current-semantics companions, not retypings of the
seven legacy exact-peer statements. The earlier counterexample remains valid.

Scoped builds pass: table claims 50 jobs, allocation 41, lookup provenance 40,
lookup absence 42, validation 29, dump cancellation 65, cut source 13, cut
claims 14, wheel effects 32 and jitter split 28. The dump build repeats the
already recorded inherited `Env.lean:865` deprecation; proof modules have no
warnings. Closure axiom checks cover 180, 83, 50, 87, 25, 17 and 92 named
logical roots in their respective groups, with only the three permitted axioms.
Fresh kernel replay passes for all ten roots. The retained gate's token/import
checks and the whitespace check pass.
Independent reviews found no correctness issue. Mirror/shared layers and the
gate/root are unchanged.

Development: table support and isolated wrappers passed clean; a wrapper
extraction boundary was corrected before its first check. Allocation, cut
source, cut claims and lookup absence passed their first prototypes. Lookup
provenance had three failed coarse root drafts, then one failed agent draft,
a clean first-claim draft and a clean three-claim draft. Validation had two
failures then a clean draft. Dump cancellation had two fixture-notation parse
failures then a clean draft. Wheel effects had one corrected annotation failure;
jitter had three corrected proof failures. All packaged builds passed first
time. Three exploratory keypair-release drafts failed and remain outside this
checkpoint. No infrastructure rerun, cap increase or guest run occurred.
Complete compiler output was captured before display.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Index.TableClaims`, `Index.Allocation`, `Index.LookupProvenanceSource`,
`Index.LookupNoneSource`, `Config.Validation`, `Config.DumpCancellation`,
`Progress.CutSource`, `Progress.CutClaims`, `TimerDiscipline.ArmingWheelSource`
and `TimerDiscipline.JitterFrames`, each under `Leanux.Proofs.WG`.

## Native serialization, release and within-WireGuard frames

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.PeerDump`, `DumpReturns`, `Identity` | 8 | 8 | 0 | 0 | 0 | 8 |
| `Config.AllowedLists`, `AllowedListView`, `AllowedListFrames`, `AllowedTransferModel` | 12 | 5 | 0 | 7 | 0 | 12 |
| `Index.Release`, `IndexFieldFrames`, `IndexOperationFrames` | 9 | 9 | 0 | 0 | 0 | 9 |
| `TimerDiscipline.JitterBoundClaims` | 2 | 2 | 0 | 0 | 0 | 2 |
| This tranche | 31 | 24 | 0 | 7 | 0 | 31 |
| Cumulative validated surface | 290 | 156 | 21 | 113 | 22 | 291 |

The tree has 444 campaign-owned files and 1,832 theorem declarations;
1,541 baseline declarations still await validation. The checked closure now
has 121 proof modules: H1 49 theorems, H2 141, H3 6, H4 43, H5 40 and H6 12.
All six full result closures and all 258 terminal declarations remain lagging.
No new charter result or type-given deletion is claimed in this tranche.

H4 carries the partial and total peer-dump contracts separately. The exact
room/JSON/cursor result retains the original empty allowed-IP list, fresh
cursor and 168-byte room premises, with arbitrary endpoint families and
Ambient inputs. Totality excludes the actual error paths before reusing the
partial effect. Identity updates retain the null-secret/public-key behavior,
clamping and selected-peer precomputation; no empty-peer-list premise replaces
the original pure pending-work check.

Allowed-list deletion remains an exact ordered fold over arbitrary supplied
peer records; it does not assume unique entries or current residency for that
helper. Public deletion snapshots the original peer map once. The per-peer
view retains its explicit original-store snapshot hypothesis, including repeated
identities. The unused Fwmark import is removed. Three pure Device frames and
the transfer model consequence are unchanged; this does not yet carry the
executable transfer path.

H2's keypair release keeps totality with only the original resident keypair,
positive count and non-NULL peer word premises. It retains optional first
unhash, decrement, second unhash on last release, and erase, with the actual
ordered Ambient trace. Referenced-peer residency is not added. The five
`IndexFieldFrames` and three extracted `IndexOperationFrames` preserve numeric
uniqueness inside WGWorld and remain substantive frames. The latter are removed
from `HandshakeClaims`; its five other contracts remain unchanged and pending.

H6's two bound claims are extracted into `JitterBoundClaims` from
`ObservationClaims` and `SourceFrames`, which retain fourteen and two pending
contracts respectively. The public Core bound is unchanged. The source bound
states the stronger full WG observation, universally quantified over its initial
projection without new readiness, device or record assumptions. Whole-snapshot
record contracts and arbitrary product-callback observations still require their
Product carry. The removed `Env.fireTimer` path additionally needs the actual
wheel dispatcher relation; it cannot be restored by monad retyping alone.

New claim file: `TimerDiscipline/JitterBoundClaims`. New frame file:
`Index/IndexOperationFrames`; `IndexFieldFrames` and `AllowedListFrames` remain
frames. No public headline name moves out of a `Statements.lean` file.

Scoped builds pass without warnings: peer dumps 44 jobs, total dumps 45,
identity 30, keypair release 42, index field frames 53, index operation frames
54, projected jitter bounds 32, allowed-list source 46, list frames 47 and
list view/transfer model 50. Axiom inspection covers 172, 174 and 207 named
logical roots in the three groups, with only the three permitted axioms.
Fresh kernel replay passes for all eight roots. The retained gate's token/import
checks and the whitespace check pass.
Independent reviews found no correctness issue; mirror/shared layers remain
unchanged. No full terminal or full proof-gate pass is claimed.

Development: peer-dump drafts had one warning-bearing pass, two failures and
a clean pass; total dumps had six failures then a clean pass. Identity had one
failed draft then a clean pass. Keypair release had one agent failure then a
clean pass, following the three root failures recorded in the prior tranche.
Index field frames and projected jitter bounds passed first time. The three
index-operation frames passed their first draft; a separate extension into
pending release/caller frames failed and is excluded from this checkpoint.
Allowed-list source had one failure then a clean pass; its view had a pass with
unused/deprecated simp warnings, then a clean pass. All package builds passed
first time. No infrastructure rerun, cap change or guest run occurred; complete
output was captured before preview.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Config.PeerDump`, `Config.DumpReturns`, `Config.Identity`,
`Config.AllowedTransferModel`, `Index.Release`, `Index.IndexFieldFrames`,
`Index.IndexOperationFrames` and `TimerDiscipline.JitterBoundClaims`, each under
`Leanux.Proofs.WG`.


## Exact recorded jitter, configuration leaves and release-domain finding

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.DeviceDumpSource`, `AllowedReadbackLeaves` | 3 | 3 | 0 | 0 | 0 | 3 |
| `TimerDiscipline.JitterRecordsSource` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Index.PeerReleaseFindings` | 0 | 0 | 0 | 0 | 2 | 2 |
| This tranche | 9 | 9 | 0 | 0 | 2 | 11 |
| Cumulative validated surface | 299 | 165 | 21 | 113 | 24 | 302 |

The tree has 446 campaign-owned files and 1,834 theorem declarations;
1,532 baseline declarations still await validation. The checked closure now
has 125 proof modules: H1 49 theorems, H2 143, H3 6, H4 46, H5 40 and H6 18.
All six full result closures and all 258 terminal declarations remain lagging.
There is no new charter result or type-given deletion in this tranche.

H6's six recorded-jitter contracts retain both supported sites, the ordered
rejected/accepted byte predicates, arbitrary suffix and original turn-budget
condition. Their exact nested native runs preserve all WG state and all
Ambient fields except the consumed hidden prefix. The original source factor
uses the actual record budget. Product fixture observations remain separate
pending obligations.

H4's device-dump source equality changes only its two action annotations to
`WG.M`; branch order, saved device, cursor updates, cancellations and failures
are unchanged. `AllowedReadbackLeaves` extracts two original total contracts
from `AllowedReadbackSource`: inserted-node readback and its serialized
allowed-IP attribute. Their arbitrary address, CIDR and parent inputs and
original space premise remain. The other three source contracts are
byte-for-byte unchanged and pending; the entire source module is not validated.

The [peer-release finding](2026-10-17-proof-campaign-2-peer-release.md) adds
two exact stopped runs refuting the old unconditional total contract. Queued
work and a locally consistent pending timer are separately permitted by the
old resident-peer/positive-count premises. These witnesses neither establish
reachability nor expose a stopped poststate. The legacy contract remains
pending, and no mirror repair is requested.

Claim files: `Config/DeviceDumpSource`, `Config/AllowedReadbackLeaves`,
`TimerDiscipline/JitterRecordsSource`, and the counterexample file
`Index/PeerReleaseFindings`. There are no new frame files. The proof root
now imports both this finding and the earlier `ArmingWheelFindings`, so they
remain in its build closure. This corrects the earlier omission of the timer
finding from the root; the gate script and all public headline declarations
are unchanged.

Scoped builds pass without warnings: peer-release findings 43 jobs, device
dump factor 46, jitter records 37 and readback leaves 48. Axiom inspection
covers 144, 63 and 91 named logical roots in the three groups, with only the
three permitted axioms. Fresh kernel replay passes for all four roots.
The retained gate's token/import checks and the whitespace check pass.
Independent reviews found no correctness issue. Mirror and shared layers are
unchanged; no full terminal or full proof-gate pass is claimed.

Development: the queued-release probe passed; its timer extension had one
string-interpolation type failure, then both passed. The device-dump prototype
passed first time. Jitter had one failed draft on budget-lift normalization
and deprecated conditional rewrites, then a clean draft; the warnings were
fixed. Readback had one failed room-bookkeeping draft, then a clean draft.
All packaged builds passed first time. No infrastructure rerun, cap change
or guest run occurred. Complete compiler output was captured before preview.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Index.PeerReleaseFindings`, `Config.DeviceDumpSource`,
`TimerDiscipline.JitterRecordsSource` and `Config.AllowedReadbackLeaves`,
each under `Leanux.Proofs.WG`.


## Owner frames, ordered clear and record-budgeted jitter

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Index.OwnerFieldFrames`, `OwnerIndexFrames` | 8 | 7 | 0 | 1 | 0 | 8 |
| `Noise.ClearSource` | 11 | 11 | 0 | 0 | 0 | 11 |
| `Config.AllowedRemovalSource` | 2 | 2 | 0 | 0 | 0 | 2 |
| `TimerDiscipline.JitterExhaustionSource` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Progress.JitterProgressSource`, `JitterProgressClaims` | 6 | 6 | 0 | 0 | 0 | 6 |
| This tranche | 31 | 30 | 0 | 1 | 0 | 31 |
| Cumulative validated surface | 330 | 195 | 21 | 114 | 24 | 333 |

The tree has 447 campaign-owned files and 1,834 theorem declarations;
1,501 baseline declarations still await validation. The checked closure has
132 proof modules: H1 60 theorems, H2 151, H3 6, H4 48, H5 46 and H6 22.
All six full result closures and all 258 terminal declarations remain lagging.
Two H5 public jitter wrappers are carried and check in isolation; that is not
a pass of their enclosing `Statements` module and they are not counted again.

The owner predicates retain their resident-device, uniqueness, allocation-bound
and designated-fresh-owner hypotheses. They do not imply keypair-store
residency, peer-word coherence or slot safety. The five field frames preserve
these predicates through actual native setters, handshake zeroing and key
derivation. Two guarded index-adapter contracts and their unchanged pure bound
are extracted to `OwnerIndexFrames`; the keypair-release and rotation callers
in `OwnerUpdateClaims` remain unchanged and pending. All seven operational
frames are substantive within WG, so none is deleted.

H1's ordered-clear contracts retain both partial effects and total original
returns under the original occurrence-count readiness condition. Normal
keypair release derives residency, a positive reference and a non-NULL peer
word from its actual guards. Total clear rereads, clears and releases next,
previous and current in order, threading both native states. Repeated slot
identities remain allowed; no owner-peer residency or record premise is added.

H4 carries two exact source equalities for allowed-IP removal by changing only
three helper annotations to `WG.M`. The actual empty-list branch, safe-loop
order, node frees, invariant failures and final iteration record remain.

H6's four exhaustion contracts retain empty streams and contiguous rejected
byte streams at both sites. The real record-derived budget includes the next
read, which raises the exact missing-input error rather than an invented
budget failure. H5's four source contracts additionally cover arbitrary
supplied records, including passive prefixes and malformed input. Their two
projected claims use the actual `liftWG` through `Product.Observes`, retaining
the original fixture observations as well as exact WG/Ambient state. Success
has a bounded jitter and a strictly shorter suffix; recordless execution and
scheduler progress remain outside the claims.

Claim files: `Noise/ClearSource`, `Config/AllowedRemovalSource`,
`TimerDiscipline/JitterExhaustionSource`, `Progress/JitterProgressSource`
and `Progress/JitterProgressClaims`. Frame files: `Index/OwnerFieldFrames`
and the new `Index/OwnerIndexFrames`. No public headline moves out of its
`Statements` file. The gate, mirror and campaign-1 layers are unchanged.

Scoped capped builds pass without warnings: owner frames 55 jobs, combined
jitter/removal source 63, and ordered clear 49. Closure axiom inspection covers
282 and 139 logical roots in the two groups, using only the permitted axioms;
the two isolated public jitter wrappers also use only those axioms. Fresh
kernel replay passes for all five roots. Static gate token/import checks and
whitespace pass. Independent reviews found no correctness issue. No full
result or full proof-gate pass is claimed.

Development: both owner probes passed first time. Ordered clear had one failed
draft on an omitted direct import and elaboration details, then a clean draft.
Jitter exhaustion had one failed match-normalization rewrite, then a clean
draft; arbitrary-record source, projected claims, isolated wrappers and removal
source passed first time. All packaged builds passed first time. Separately,
three pending readback-composition drafts failed: an existential Ambient
witness, remaining room/sequence normalizations with unused simp warnings,
then simplifier/heartbeat exhaustion. They are excluded from this checkpoint;
the next approach composes checked leaves through the actual guarded node read.
No infrastructure rerun, cap/proof-limit change or guest run occurred. Complete
compiler output was captured before preview.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Index.OwnerIndexFrames`, `Noise.ClearSource`,
`Config.AllowedRemovalSource`, `TimerDiscipline.JitterExhaustionSource`
and `Progress.JitterProgressClaims`, each under `Leanux.Proofs.WG`.


## Projected clear, root transfer, rotation and exact jitter outcomes

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `TimerDiscipline.JitterOutcomeSource`, `JitterOutcomeClaims` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Noise.ClearClaims` | 0 | 0 | 0 | 0 | 2 | 2 |
| `Noise.RotationSource` | 10 | 10 | 0 | 0 | 0 | 10 |
| `Config.AllowedTransferSource` | 3 | 3 | 0 | 0 | 0 | 3 |
| This tranche | 17 | 17 | 0 | 0 | 2 | 19 |
| Cumulative validated surface | 347 | 212 | 21 | 114 | 26 | 352 |

The tree has 450 campaign-owned files and 1,836 theorem declarations;
1,484 baseline declarations still await validation. The checked closure has
137 proof modules: H1 72 theorems, H2 151, H3 6, H4 51, H5 46 and H6 26.
All six full result closures and all 258 terminal declarations remain lagging.
Four public wrappers in this tranche check in isolation, not as complete
`Statements` modules, and are not counted again.

H1's new `ClearClaims` contains projected support for the two existing ordered
clear headlines. Resident-only partial correctness and static occurrence-count
totality remain separate, with exact final cleared slots and ordered releases.
The public names remain literal declarations in `Statements`. These posts
observe Device and the release relation, not exact fixture-snapshot equality,
so native projection preserves their stated scope.

The ten rotation contracts carry both exact source identities and eight native
execution contracts. They retain arbitrary Ambient inputs, actual branch-record
prefixes and ordered peer writes/releases. Repeated identities, including an
alias of the new key, remain allowed. Matching confirmation promotes next and
releases old previous; unmatched next returns false without a Device write.
The static old-previous budget is required only in the matching case. No final
key-store coherence or reachable-lifetime claim is added.

H4's three original total root-transfer contracts use the actual guarded Aip
adapters. They update the node owner, delete its old list membership through
the original peer-map snapshot, then append once to the target peer's list.
All original width, root, node and target-peer premises remain; no owner,
freshness or alias restriction is added. The pure transfer model import is
now explicit after an earlier dependency narrowing.

H6 extracts the two source wrappers from `SourceClaims` and two projected
outcome claims from `ObservationClaims`. The native source equalities retain
arbitrary WG/Ambient states and exact record suffixes/errors. The projected
claims run the actual `liftWG` under `Product.Observes`, retaining all eight
original fixture observations. Their two public wrappers stay in `Statements`.
The remaining 24 source and 12 projected aggregate contracts remain pending.

Claim files: `Noise/ClearClaims`, `Noise/RotationSource`,
`Config/AllowedTransferSource`, `TimerDiscipline/JitterOutcomeSource` and
`TimerDiscipline/JitterOutcomeClaims`. No frame is added or deleted in this
tranche; no shared layer or mirror file changes.

Scoped capped builds pass without warnings: jitter outcome claims 42 jobs,
projected clear 53, root transfer 53 and rotation 53. Axiom inspection covers
210, 113 and 169 logical roots in their respective groups, using only the
three permitted axioms. The four isolated public wrappers also use only those
axioms. Fresh kernel replay passes for all four roots; static gate token/import
and whitespace checks pass. Independent reviews found no correctness issue.
No full terminal or full proof-gate pass is claimed.

Development: jitter outcome, clear support and isolated wrapper probes passed
first time. Transfer's first draft closed its first contract; the second added
two tails but failed on width-guard simplification and had unused simp warnings;
the third closed all three without warnings. Rotation had three failed drafts
(branch-record threading, record-field layout, then redundant tactics) before
its clean fourth draft. All packaged builds passed first time. A separate
consume-edge draft failed on simplifier steps and deprecated tactic warnings;
it remains outside this checkpoint, with no changed source retained. No
infrastructure rerun, cap/proof-limit change or guest run occurred. Complete
compiler output was captured before preview.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Noise.ClearClaims`, `Noise.RotationSource`,
`Config.AllowedTransferSource` and `TimerDiscipline.JitterOutcomeClaims`,
each under `Leanux.Proofs.WG`.


## Consume tags, product publication and consecutive confirmation

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.ConsumeEdges`, `ConfirmationSequenceSource` | 7 | 7 | 0 | 0 | 0 | 7 |
| `Roaming.PublicationSource`, `PublicationFrames` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Progress.IndexProgressSource` | 6 | 6 | 0 | 0 | 0 | 6 |
| This tranche | 17 | 17 | 0 | 0 | 0 | 17 |
| Cumulative validated surface | 364 | 229 | 21 | 114 | 26 | 369 |

The tree still has 450 campaign-owned files and 1,836 theorem declarations;
1,467 baseline declarations await validation. The checked closure has 142 proof
modules: H1 79 theorems, H2 151, H3 10, H4 51, H5 52 and H6 26. All six
whole-result closures and all 258 terminal declarations remain lagging.

H1's two successful-consumption tag contracts retain unconditional entry and
normal-return scope. They derive final residency and tag from the actual final
peer read/write; prefix computations need no invented frame, successful-return
or cryptographic premise. Initiation's successful tail takes the actual false
failed-release branch. The generic prefix law retains arbitrary product
computations through `StateT σ (Except Stop)`, rather than silently narrowing
that original domain to native WG.

Consecutive confirmation retains the actual finite `mapM`, its intermediate
WG/Ambient states and its first-match behavior. Normal completion needs only
caller residency. Totality uses exactly the original conditional old-previous
release budget when an input matches the initial next slot. Repeated identifiers
and aliases remain; no interleaved installation, lifetime or reachable-state
claim is added.

H3's publication data and source factors use the full product projection.
The `softirq` and `irqExit` callbacks remain arbitrary `Leanux.M` actions;
all source equalities preserve the actual empty-queue path, both callback
positions, held-owner reference release and exact errors. The packet owner
comes from the embedded keypair word. The snapshot-read frame generalizes
over arbitrary state and observation, retaining its full-state predicate domain.
Its returned observation and preservation are substantive, so it is not
deleted. Authentication, enqueue and complete projected caller claims remain
pending; the three source equations do not establish them alone.

H5's index-input source equations retain every supplied record list, passive
prefix stripping, malformed-input errors, collision behavior, both original
bucket scans and the record-derived turn bound. Helpers run on actual
`AmbientM` or `IndexM` state; the whole insertion uses the actual guarded
`liftIndex`. Its original resident-device premise remains and success retains
the exact new Device/table and record suffix. Errors retain their exact Stop
without a poststate. Projected caller claims remain pending in this tranche.

Claim files: `Noise/ConsumeEdges`, `Noise/ConfirmationSequenceSource`,
`Roaming/PublicationSource` and `Progress/IndexProgressSource`.
`Roaming/PublicationFrames` remains a separate frame file; its data shape is
in `PublicationModel`. No headline, shared layer, mirror file or gate changes.

Scoped capped builds pass without warnings: consume edges 43 jobs, publication
39, consecutive confirmation 56 and index progress 38. Axiom inspection covers
240 and 93 logical roots in the two groups, using only the three permitted
axioms. Fresh kernel replay passes for all five roots. Static gate token/import
and whitespace checks pass. Independent reviews found no correctness issue.
No full terminal or full proof-gate pass is claimed.

Development: after the root consume draft recorded in the preceding tranche,
three changed agent drafts had a continuation-shape failure, a record-field
parse failure, then a clean pass. Publication first passed with unused simp
warnings, then passed clean after removing them. Its generic read-frame draft
had a triple-elaboration failure for a raw lambda, then passed with the same
read expressed through the state monad. Confirmation had one nested-pair
bookkeeping failure, then a clean pass. Index progress had two failed drafts
(tuple/branch normalization with unused simp arguments, then an induction
substitution), followed by a clean pass. All package builds passed first time.
No infrastructure rerun, cap/proof-limit change or guest run occurred. Complete
compiler output was captured before preview.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Noise.ConsumeEdges`, `Noise.ConfirmationSequenceSource`,
`Roaming.PublicationSource`, `Roaming.PublicationFrames` and
`Progress.IndexProgressSource`, each under `Leanux.Proofs.WG`.

## Projected rotation, index progress and session dependencies

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.RotationClaims`, `ConfirmationSequenceClaims` | 0 | 0 | 0 | 0 | 6 | 6 |
| `Progress.IndexProgressClaims` | 2 | 2 | 0 | 0 | 0 | 2 |
| `Roaming.Authentication` | 1 | 1 | 0 | 0 | 0 | 1 |
| `Noise.SessionFrames`, `Index.SessionOperations` | 5 | 4 | 0 | 1 | 0 | 5 |
| This tranche | 8 | 7 | 0 | 1 | 6 | 14 |
| Cumulative validated surface | 372 | 236 | 21 | 115 | 32 | 383 |

The tree has 453 campaign-owned files and 1,842 theorem declarations;
1,459 baseline declarations await validation. The checked closure has 149 proof
modules: H1 89 theorems, H2 152, H3 11, H4 51, H5 54 and H6 26. All six
whole-result closures and all 258 terminal declarations remain lagging.

H1's six new helpers carry existing projected rotation and consecutive-confirmation
headlines. Their public declarations remain in `Statements`; the helpers are
counted as additions, and the isolated public wrappers are not counted again.
Original Device/relation observations, arbitrary WG/Ambient inputs, aliases,
normal-return scope and exact conditional release budgets remain unchanged.
No original exact fixture-snapshot equation is discarded.

H5's two index-progress claims use actual `liftIndex` through the native
projection. They preserve arbitrary supplied records, exact resolver errors,
the post-unhash table, fresh-index test and strict suffix decrease. The successful
postcondition existentially names the actual final snapshot without asserting
a fixture frame. No owner-residency or uniqueness premise is added.

H3's native decryption-provenance contract retains its original resident-keypair
premise and normal-return scope. It identifies the returned peer, source,
keypair, decoded nonce and AEAD plaintext using the actual receiving key.
It adds no key-validity or cryptographic-success hypothesis and claims neither
totality nor authentication of the source address.

The three native session counter frames remain substantive: `keypairCounter`
belongs to WG state, which these operations can access. Their pure peer-word
companion is retained. The new `Index.SessionOperations` extracts the two
session tail definitions and exact `beginSession` source factor from
`SessionOwners`; its other four owner-invariant bodies are unchanged and pending.
The source factor retains the actual derivation, allocation, zeroing, rotation,
owner-word dereference, guarded index replacement and error order.

Claims: `Noise/RotationClaims`, `Noise/ConfirmationSequenceClaims`,
`Progress/IndexProgressClaims`, `Roaming/Authentication` and
`Index/SessionOperations`. Frames: `Noise/SessionFrames`.
No shared layer, mirror file, gate or public audit name changes.

Scoped capped builds pass without warnings: rotation/confirmation 61 jobs,
index claims 41, authentication 55 and session dependencies 55. Axiom inspection
covers 261, 90 and 176 logical roots in the three groups, using only the three
permitted axioms. The six isolated Noise wrappers and two index-progress
wrappers also check with standard axioms. Fresh kernel replay passes for all
six roots; static gate token/import and whitespace checks pass. Independent
reviews found no correctness issue. No whole-result or full proof-gate pass
is claimed.

Development: rotation/confirmation, authentication and index-claim prototypes
passed first time; a second index prototype also checked its public wrappers.
Session dependencies had two failed drafts (native adapter weakest-precondition
shape and deprecated tactics; then equality/type inference and unused simp
arguments), followed by a clean third draft. All package builds passed. Two
session EOF formatting issues were fixed before a final successful rebuild;
an index-claims EOF issue was fixed without changing its proof. No infrastructure
rerun, cap/proof-limit change or guest run occurred. Complete compiler output
was captured before preview.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Noise.RotationClaims`, `Noise.ConfirmationSequenceClaims`,
`Progress.IndexProgressClaims`, `Roaming.Authentication`,
`Noise.SessionFrames` and `Index.SessionOperations`, each under
`Leanux.Proofs.WG`.

## Configuration composition, owner invariants and publication leaves

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.AllowedReadbackSource`, `AllowedTransferRequestSource` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Config.AllowedRootRemoval` | 5 | 3 | 0 | 2 | 0 | 5 |
| `Index.OwnerUpdateClaims` | 2 | 2 | 0 | 0 | 0 | 2 |
| `Roaming.PublicationLeafClaims`, `PublicationReadFrames` | 5 | 5 | 0 | 0 | 0 | 5 |
| This tranche | 16 | 14 | 0 | 2 | 0 | 16 |
| Cumulative validated surface | 388 | 250 | 21 | 117 | 32 | 399 |

The tree has 455 campaign-owned files and 1,842 theorem declarations;
1,443 baseline declarations await validation. The checked closure has 155 proof
modules: H1 89 theorems, H2 154, H3 16, H4 60, H5 54 and H6 26. All six
whole-result closures and all 258 terminal declarations remain lagging.

H4's three remaining inserted-node readback contracts compose the actual guarded
Aip node read with checked serialization and exact source prefixes. Their original
singleton list, stored node, sequence, fresh-cursor and room premises remain.
Addresses and CIDRs remain arbitrary; only the original public getter requires
peer residency. Total completion retains exact serialized attributes, cursor
reset and room subtraction. Root transfer now also covers the actual configuration
request, including the preceding sequence increment. Singleton root removal
retains ordered list deletion, both root families and exact final Device.
The node-tail contract still needs no initial node/root residency: its first
operation inserts the supplied node. The two pure lookup effects are unchanged.

H2's release and rotation contracts preserve owner uniqueness, allocation bounds
and designated-key freshness on every original normal-return path. In particular,
a null peer word remains permitted when deferred release of a nonfinal reference
does not unhash. No key/peer residency, positivity, nonnull-word or distinctness
premise is added to these partial contracts. Actual Stops remain outside their
normal-return conclusions.

H3 extracts five existing contracts from `PublicationClaims`; its other six
contracts remain pending. Native key presence is connected through the actual
`liftWG` to projected product authentication. Packet replacement retains the
guarded Skb adapter. The suffix keeps arbitrary `Leanux.M` callbacks and their
original order; it concludes only the Boolean result. The exact packet-read
helper belongs in `PublicationReadFrames`: it still returns the packet and
preserves the entire actual product, including unobserved components. Its entry
type is inferred from the actual lifted computation; that technical source/frame
helper is not presented as a projected public claim or a type-given deletion.

Claims: `Config/AllowedReadbackSource`, `AllowedTransferRequestSource`,
`AllowedRootRemoval`, `Index/OwnerUpdateClaims` and
`Roaming/PublicationLeafClaims`. Frames: `Roaming/PublicationReadFrames`.
No shared layer, mirror file, public audit name or gate changes.

Scoped capped builds pass without warnings: readback 49 jobs, transfer request
54, root removal 50, owner invariants 67 and publication leaves 62. Axiom
inspection covers 94, 114, 106, 221 and 137 logical roots respectively, using
only the permitted axioms. Fresh kernel replay passes for all six roots.
Static token/import and whitespace checks pass. Independent reviews found no
correctness issue. No full terminal or proof-gate pass is claimed.

Development: revisited readback had three failed drafts (bind/sequence
normalization, nonzero-sequence rewriting, then a reserved identifier and unused
simp arguments) before its clean fourth draft; the earlier three failed drafts
remain recorded separately. Transfer request had three failed drafts on inferred
state and existential-conjunction shape, including one unused simp argument,
then a clean fourth draft. Both root-removal probes passed, first the leaf and
then the complete five-contract module. Owner invariants passed their first
probe. Publication's first probe failed on substitution/record eta and unused
simp arguments, then its five-contract draft passed. A later bulk enqueue draft
failed to normalize product lifts and emitted extensive warnings; its tool output
was truncated without a retained complete log, a recording failure. That route
was stopped. Two subsequent compositional enqueue drafts also failed on predicate
annotations and syntax; their complete logs were saved. Those enqueue attempts
are excluded from this checkpoint. All packaged builds passed first time; a
readback blank-line cleanup changed no proof. No infrastructure rerun, cap or
proof-limit increase, or guest run occurred.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on `Config.AllowedReadbackSource`, `Config.AllowedTransferRequestSource`,
`Config.AllowedRootRemoval`, `Index.OwnerUpdateClaims`,
`Roaming.PublicationLeafClaims` and `Roaming.PublicationReadFrames`, each
under `Leanux.Proofs.WG`.

## Session and publication composition, configuration requests

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.SessionSource` | 14 | 13 | 0 | 1 | 0 | 14 |
| `Index.SessionOwners`, `HandshakeClaims` | 9 | 9 | 0 | 0 | 0 | 9 |
| `Index.OwnerCreation`, `SessionAllocationSource` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Roaming.PublicationClaims` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Config.Port`, `Flags`, `SocketPorts` | 9 | 9 | 0 | 0 | 0 | 9 |
| `Config.AllowedRoundTripSource` | 2 | 2 | 0 | 0 | 0 | 2 |
| This tranche | 44 | 43 | 0 | 1 | 0 | 44 |
| Cumulative validated surface | 432 | 293 | 21 | 118 | 32 | 443 |

The tree has 455 campaign-owned files and 1,842 theorem declarations;
1,399 baseline declarations await validation. The checked closure has 165 proof
modules: H1 103 theorems, H2 167, H3 22, H4 71, H5 54 and H6 26.
All six whole-result closures and all 258 terminal declarations remain lagging.
These are carries of existing contracts; no remaining charter core is declared
complete.

H1's session source retains the exact allocation overwrite/counter increment,
role and remote-index assignment, existential birthdate, zeroing, ordered
rotation/releases and index replacement. Normal success derives the original
live-peer, nonnull-word and hashed-entry conditions; they are not new premises.
Aliases remain allowed, and no final key residency is asserted. False returns
preserve Device and allocation counter. The KDF contract remains total for
arbitrary native-state predicates and Ambient inputs; its pure output equation
is unchanged. The source imports the checked operation factor directly.

H2 carries owner invariants through all original session paths, and numeric-index
uniqueness through release, rotation, session creation, initiation and response.
Missing objects, null words, allocation or crypto failures and stopped paths
retain partial scope. In particular, null-word deferred release of a nonfinal
reference remains covered. Owner creation asserts owner uniqueness and numeric
bounds without store residency. The allocation-effect contract retains exactly
its resident-peer and store-bound premises, deriving entry absence and the
original false/no-increment versus true/one-increment outcomes.

H3's remaining six publication contracts now compose the actual guarded WG/Skb
operations with product execution. All original product snapshots retain their
eight fixture observations. The prefix starts at the actual entry state; enqueue
retains its queue-membership and reference-count guards, including stopped
zero/overflow cases. Arbitrary callbacks retain their original positions, and
the final suffix still executes. No constraint is imposed on callback-modified
final state. The prior exact product-read frame stays in its separate frame file.

H4 carries the down-device port contract and all six flag/early-return contracts
with their original return codes and domains. Native WG equality replaces the
old Kernel equality; unrelated subsystems are excluded by the action type.
Removal's exact source equation still orders removal before release and attribute
cleanup. Socket reinitialization and nonzero initialization remain total with
their original residency, net and port-bound premises, preserving exact socket
and incoming-port writes. The allowed-IP set/get composition runs the actual
getter after either numeric setter outcome; exceptions still stop the bind.
Its room, cursor, sequence, empty-root and width premises are unchanged.

Claims/source files are the ten modules in the table. This tranche adds or
deletes no frame file; local helper inductions stay inside their existing proofs.
No shared layer, mirror file, public audit name or gate changes.

Scoped capped builds pass without warnings: session source 57 jobs, session
owners 69, handshake indices 69, owner creation/allocation 73, publication 64,
port 43, flags 45, sockets 44 and allowed-IP round trip 50. The last also rebuilt
the earlier readback module after its whitespace-only cleanup. Axiom inspection
covers 201, 229, 246, 144, 53, 63, 96 and 281 named logical roots across the
groups, using only the permitted axioms. Fresh kernel replay passes for all ten roots. Static gate token/import and
whitespace checks pass.
Independent reviews found no correctness issue. No whole-result or full
proof-gate pass is claimed.

Development: session source had two failed normalization drafts, including one
unused simp argument, then a clean third draft. Session owners had one failed
continuation-normalization draft, then a clean second draft. Both handshake
prototypes passed, as did the first owner/allocation and allowed-IP round-trip
prototypes. Port had two failed branch-log normalization drafts (the first also
had an unused simp argument), then a clean third. Flags had two failed
case-layout/key-substitution drafts, a pass with one unused simp argument, then
a clean fourth. Socket drafts 1–4 failed on elaboration/parser/equality details;
draft 5 passed clean. Publication continued the recorded compositional route:
draft 6 failed on native reference-count composition, draft 7 closed enqueue,
draft 8 also closed publication but left product-lift reductions, draft 9 closed
packet/selection with two prefix reductions pending, and draft 10 closed all six
without warnings. All package builds passed first time. Complete outputs were
saved before preview. No infrastructure rerun, cap/proof-limit increase or guest
run occurred; obsolete heartbeat settings were removed from publication and
socket modules after they checked at the default.

Reproduce scoped builds and fresh replay using the capped bundle commands above
on the ten modules in this table under `Leanux.Proofs.WG`.

## Recorded session totals, poll-attempt audit and configuration readback

| Tranche | Before | Retyped/generalized | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.SessionReadySource`, `SessionReadyReadFrames`, `SessionReadyClaims` | 19 | 19 | 0 | 0 | 0 | 19 |
| `Index.SessionSequenceSource` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Roaming.PollEndpointSource` | 10 | 10 | 0 | 0 | 0 | 10 |
| `Roaming.PollAttemptSource`, `PollAttemptAuditSource` | 7 | 7 | 0 | 0 | 0 | 7 |
| `Config.AllowedStructural`, `AllowedLeaf` | 14 | 14 | 0 | 0 | 0 | 14 |
| `Config.PeerScalars`, `RoundTrip` | 7 | 6 | 0 | 1 | 0 | 7 |
| This tranche | 61 | 60 | 0 | 1 | 0 | 61 |
| Cumulative validated surface | 493 | 353 | 21 | 119 | 32 | 504 |

The tree has 456 campaign-owned files and 1,842 theorem declarations;
1,338 baseline declarations await validation. The checked closure has 177 proof
modules: H1 122 theorems, H2 171, H3 39, H4 92, H5 54 and H6 26.
All six whole-result closures and all 258 terminal declarations remain lagging.
No new charter result or type-given deletion is claimed.

H1's recorded totality retains the original allocation/clock widths, success
record, armed allocation, resident/live peer, nonnull word, hashed entry and
alias-sensitive release budget. Allocation readiness is computed after the
actual overwrite. Arbitrary outer predicates and loop callbacks keep their
generic StateT domain, including the former product instances. The projected
ready claim gets success and its exact ordered effect from the same run.
The existing full-product peer-read preservation helper moves to
`SessionReadyReadFrames`; it retains arbitrary product predicates and the actual
`liftWG`, rather than presenting full-product preservation as a projected claim.

H2's four sequential-allocation contracts thread actual native state and Ambient
through consecutive original calls. Missing-peer exclusion follows from a
normal entry run. Entry store bounds, fresh allocation IDs, ordered results,
distinctness and cursor increments retain their original domains. Exact erasure
keeps every original error; no handshake installation is inserted between calls.

H3 carries the ten endpoint-prefix source contracts and seven attempt-audit
source/erasure contracts. Their models retain Product snapshots and all eight
fixture observations. Arbitrary stack and softirq callbacks remain product
actions. Every attempted iteration records its prefix and, if reached, its actual
successor suffix, including errors. Budget guards, cleanup, GRO, stopping and
later callbacks remain in the exact source equations. Two named campaign-1 lift
law variants stay proof-local; no shared layer is copied or edited. The audit's
operational import now names the checked source module directly; the pending
endpoint facts are not deleted.

H4's structural and leaf removal contracts retain actual guarded Aip lifts,
slot-bit/size conditions and reads over successive Devices. No parent/child
non-alias premise is introduced; the branching tail still inserts its supplied
node before any residency requirement. Scalar configuration retains the ordered
lookup, PSK update, interval update and release writes. Normal-return contracts
keep overflow Stops outside their conclusions without adding a bound. The
retained-reference premise still excludes final-release guards. The set/get
composition uses the actual intermediate state and preserves the exact peer,
serialized fields, room subtraction and cursor reset. Its pure lookup equation
is unchanged.

Claims/source files are the modules in the table, with models in
`PollEndpointModel` and `PollAttemptModel`. Frames are isolated in
`Noise/SessionReadyReadFrames`. Public audit names remain literal and in order
in the six Statements files. Mirror, shared layers and gate remain unchanged.

Scoped capped builds pass without warnings: recorded session source 66 jobs,
structural removal 51, endpoint source 67, scalar leaves 48, scalar round trip 51,
attempt audit 70, ready/sequence 76 and leaf removal 52. Axiom inspection covers
248, 120, 174, 88, 97, 193, 288 and 129 logical roots in those groups; only the
three permitted axioms occur. Fresh kernel replay passes for all ten roots.
Static gate token/import checks, public-name comparison and whitespace checks
pass. Independent reviews found no correctness issue. No whole-result or full
proof-gate pass is claimed.

Development: session-ready drafts 1–6 failed on layout, inference and native
lift/bind normalization; draft 7 closed the module and draft 8 checked the
separated read frame. Structural removal had two failed native-normalization
drafts, including unused simp arguments, then a clean third. Endpoint source
had three failed lift-normalization drafts, a fourth with one unused simp
argument, then a clean fifth. Scalar leaves first failed on normalized overflow
arithmetic, then closed their first two contracts; extending the draft failed on
poststate normalization and a deterministic heartbeat timeout. The fourth draft
removed the timeout but retained poststate mismatches; the fifth closed with one
unused simp argument, removed in the package. No limit was raised. Attempt audit
had one failed polymorphic-branch annotation draft with an unused simp argument,
then a clean second. Leaf removal had one failed adapter-map composition, then
a clean compositional draft. Round-trip and ready/sequence prototypes passed
first time. All packaged builds passed first time; full compiler outputs were
saved before preview. No infrastructure rerun, cap increase or guest run occurred.

Reproduce using the capped scoped build and fresh-replay commands above on
`Config.AllowedStructural`, `Config.AllowedLeaf`, `Config.PeerScalars`,
`Config.RoundTrip`, `Noise.SessionReadySource`, `Noise.SessionReadyReadFrames`,
`Noise.SessionReadyClaims`, `Index.SessionSequenceSource`,
`Roaming.PollEndpointSource` and `Roaming.PollAttemptAuditSource`, each under
`Leanux.Proofs.WG`.

## Total scalar readback, paired transfer and remaining native frames

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.ScalarReturns`, `RoundTripReturns` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Config.AllowedTransferReadbackSource` | 1 | 1 | 0 | 0 | 0 | 1 |
| `Config.AllowedRootFrames`, `AllowedRemovalModel` | 3 | 0 | 0 | 3 | 0 | 3 |
| `Roaming.PollEndpointFrames` | 3 | 3 | 0 | 0 | 0 | 3 |
| `Index.NewlinkFrames` | 3 | 3 | 0 | 0 | 0 | 3 |
| This tranche | 16 | 13 | 0 | 3 | 0 | 16 |
| Cumulative validated surface | 509 | 366 | 21 | 122 | 32 | 520 |

The tree still has 456 campaign-owned files and 1,842 theorem declarations;
1,322 baseline declarations await validation. The checked closure has 184 proof
modules: H1 122 theorems, H2 174, H3 42, H4 102, H5 54 and H6 26.
All six complete results and all 258 terminal declarations remain lagging.

H4's total scalar contracts keep the original reference-count upper bound and
retained-reference domain. Each constructs normal completion for the actual
entry state and arbitrary Ambient, then obtains the exact postcondition from
that same run. The total set/get composition retains its exact dump, cursor and
peer postconditions. Paired allowed-IP transfer/readback threads the setter and
both getters through their actual successors, including the first getter's
returned buffer and cursor. Original peer inequality, node/list/root/width,
sequence and space premises are unchanged. Three pure Device-transform facts
remain byte-identical and are now checked; they alone claim no native execution.

H3 retains queue-peek preservation as a substantive within-WireGuard fact:
`PrevQueue.peek` still has type `WG.M`, which can write packet storage.
The local variant is renamed from its obsolete Kernel spelling to
`PrevQueue_peek_spec_wg_variant`. Full Product observation equality is retained
by the read helper. The existing packet-read provenance/preservation contract
moves from `PollEndpointClaims` to `PollEndpointFrames`, using the actual WG
lift and exact product getter. Those claims and `PollAttemptClaims` receive
only the corresponding move/reference updates and remain unvalidated.

H2's three new-device frames retain all absent-device and partial/error paths.
`TablesSafeKernel` becomes `TablesSafeWG`, with the same Device table safety
predicate under native optional-device quantification. Cookie and hash-key
initialization preserve that predicate through unrelated field writes;
ratelimiter initialization preserves it on every normal branch. Pending
consumers still using the old predicate name are explicitly deferred; no alias
or shared-layer edit is introduced.

Claims: `Config/ScalarReturns`, `RoundTripReturns`,
`AllowedTransferReadbackSource` and pure `AllowedRemovalModel`.
Frames: `Config/AllowedRootFrames`, `Roaming/PollEndpointFrames` and
`Index/NewlinkFrames`. No theorem is deleted or added in this tranche.

Scoped capped builds pass without warnings: scalar totals 49 jobs, transfer and
pure support 64, total round trip 53, poll frames 40 and new-device frames 36.
Axiom inspection covers 161, 130 and 150 logical roots across those groups,
with only the permitted axioms. Fresh kernel replay passes for all seven roots.
Static token/import, public-name and whitespace checks pass; independent reviews
found no correctness issue. Mirror and shared layers are unchanged. No full
terminal or gate pass is claimed.

Development: scalar totals had one failed existential-witness draft, then a
clean second. Transfer/readback first had one redundant tactic after the goal
was already solved, then a clean second draft. Poll frames first left a predicate
transport goal, then closed on the second draft. New-device frames first omitted
the mirror import after removing an unnecessary pending proof import, then
closed with that import restored. Total round trip passed its first prototype.
All packaged builds passed first time. Full compiler output was saved before
preview; no infrastructure rerun, limit increase or guest run occurred.

Reproduce scoped build and fresh replay on the seven modules in the table
under `Leanux.Proofs.WG`, using the capped bundle commands above.

## Complete poll observations, removal traversal and recorded port initialization

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.AllowedCollapse`, `AllowedRemoval` | 14 | 14 | 0 | 0 | 0 | 14 |
| `Config.AllowedRemovalFrames` | 19 | 0 | 0 | 19 | 0 | 19 |
| `Config.RandomPort` | 6 | 4 | 0 | 2 | 0 | 6 |
| `Roaming.PollEndpointClaims` | 7 | 5 | 0 | 2 | 0 | 7 |
| `Roaming.PollAttemptFactsSource`, `PollAttemptClaims` | 5 | 5 | 0 | 0 | 0 | 5 |
| `Progress.PollStepSource`, `PollLoopSource`, `PollBoundSource/Claims` | 13 | 13 | 0 | 0 | 0 | 13 |
| `Progress.Scheduler` | 3 | 0 | 0 | 3 | 0 | 3 |
| This tranche | 67 | 41 | 0 | 26 | 0 | 67 |
| Cumulative validated surface | 576 | 407 | 21 | 148 | 32 | 587 |

The tree has 457 campaign-owned files and 1,842 theorem declarations;
1,255 baseline declarations await validation. The checked closure has 196 proof
modules: H1 122 theorems, H2 174, H3 54, H4 141, H5 70 and H6 26.
All six complete results and all 258 terminal declarations remain lagging.
H1, H2 and H6 gain no newly checked theorem in this tranche.

H4's collapse and whole-removal contracts preserve the original successive-map
readiness relations. Sibling selection precedes leaf deletion; the parent is
reread afterward. Reparenting, slot writes and final parent deletion retain
their order and alias cases. Whole removal traverses the original peer-list
snapshot, reading each node after that iteration's list deletion from the
evolving Device. Empty lists avoid the sequence increment; nonempty lists
increment once and retain the final iteration marker. No disjointness, shape
or residency premise is added. The nineteen unchanged pure frames remain
substantive within-Device and Peer facts, including queue, metadata and field
preservation; new world types do not provide them. They assert no execution
coverage without the source contracts.

Random-port initialization retains all hidden-input modes, malformed-record
Stops, port collisions and supplied-record tails. The generic outer-state
predicate domain is retained by the byte-shape and recorded-draw contracts.
Partial initialization still asserts only normal outcomes; recorded totality
still requires the original creating-network, own-socket and bound-port
conditions. Both pure arithmetic bounds remain unchanged.

H3's prefix and full-poll claims retain packet lookup, peer identity, crypted
state, successful counter outcome, source family/address and endpoint-at-cut
facts. Arbitrary callbacks remain product actions. The publication join still
requires the same packet ID; rejected and zero-budget paths gain no success
claim. Per-attempt audit facts include failed prefixes and failed suffixes.
Exact `beforeSetter` equality and all outcome snapshots retain the eight fixture
observations. The existing concrete step/loop/audit support moves into
`PollAttemptFactsSource`; the claims file exposes the projected observation
contract. No prefix or callback execution is omitted.

H5's poll-step and loop contracts preserve the original count, budget and drained
alternatives with arbitrary product callbacks and their failures. Under the
original bounded-budget premise, the audit certifies the actual loop boundary;
normal completion retains the exact result/count bound. Inspection's unchanged
entry is distinct from an operation's successful final state. `PollBoundModel`
uses Product snapshots for exact outcomes. Its existing two pure budget lemmas
were rebuilt and replayed after that model change, without being counted again.
The concrete audit-facts helper moves to `PollBoundSource`; only its projected
inspection contract remains in `PollBoundClaims`. Scheduler's three exact
product probe contracts are unchanged: success and hidden mismatch report on
the original entry, and every other Stop propagates. Its pure result mapper
generalizes over the state type.

Claims/source files are the modules in the table. Frames remain in
`Config/AllowedRemovalFrames`; no new frame file or type-given deletion occurs.
The new `Roaming/PollAttemptFactsSource` separates concrete execution support
from projected claims. Mirror, shared layers, gate and public audit names remain
unchanged.

Scoped capped builds pass without warnings: collapse 53 jobs, removal 54, pure
removal frames 56, random port 45, endpoint claims 69, attempt facts/claims 74,
poll step 69, poll loop with its updated model 71, poll source 72, poll claims 73
and scheduler 39. Moving the concrete poll helper afterward rebuilt its source
and claims cleanly in a 73-job build. Axiom inspection covers 270, 208, 232, 24,
153, 63 and 178 logical roots across the groups, with only the three permitted
axioms. Fresh replay passes for all seven final roots and their closures.
The poll closure was replayed again after the helper move; this was validation
of changed source. Static token/import, public-name and whitespace checks pass.
Independent reviews found no correctness issue. No full-result or gate pass is
claimed.

Development: collapse had three failed drafts (constructor binding/source
normalization with a deterministic heartbeat timeout; then a no-progress tactic;
then the wrong congruence domain and an unused simp argument), followed by a clean
fourth. Removal's first draft closed with two unused simp arguments, removed in
the clean second. The nineteen unchanged frames passed their first probe.
Random-port drafts 1–4 failed on native bind/tactic normalization, overly broad
simplification with a deterministic heartbeat timeout, hidden-path discriminators
and steering/padding case equations, then residual Except error reductions; the
fifth passed clean. No limit was increased.

Endpoint-prefix draft 1 failed on local type/record normalization; draft 2 closed
the core. Wrapper drafts 3–4 fixed parser/substitution details and unused simp
arguments; draft 5 closed all seven. Attempt facts passed their first combined
probe and packaged split. Poll-step draft 1 failed on old WP/lift normalization
and deprecated tactic syntax; draft 2 closed with one unused simp argument,
removed in the clean package at default limits. Poll-loop and projected audit
claims passed first time. Poll source drafts 1–4 failed on let normalization,
branch-lift reduction and record layout; draft 5 passed. Scheduler's unchanged
proofs passed first time. All packaged builds passed first time; full compiler
outputs were saved before preview. No infrastructure rerun, cap increase or
guest run occurred.

Reproduce scoped build and fresh replay on `Config.AllowedRemoval`,
`Config.AllowedRemovalFrames`, `Config.RandomPort`,
`Roaming.PollEndpointClaims`, `Roaming.PollAttemptClaims`,
`Progress.PollBoundClaims` and `Progress.Scheduler`, under `Leanux.Proofs.WG`.
These roots include the other modules in the table.

[AGENT 2026-10-17] For the remaining H6 carry, develop separately named exact
wheel-effect support rather than a compatibility projection that erases wheel
fields. The seven old exact-Peer statements remain pending with their finding;
they are not type-given deletions. Actual same-expiry shortcuts and wheel
validation failures must remain in the carried domains.

## Native link, recorded-port and partial-application contracts

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Index.LinkSource` | 5 | 5 | 0 | 0 | 0 | 5 |
| `Config.RecordedPort`, separated `RecordedPortFrames` | 4 | 4 | 0 | 0 | 0 | 4 |
| `Config.DeviceScalars` | 4 | 4 | 0 | 0 | 0 | 4 |
| Pure removal, pair-shape and owner-clear effects | 18 | 0 | 0 | 18 | 0 | 18 |
| `TimerDiscipline.WheelPlacementSource` | 0 | 0 | 0 | 0 | 1 | 1 |
| This tranche | 31 | 13 | 0 | 18 | 1 | 32 |
| Cumulative processed baseline and checked support | 607 | 420 | 21 | 166 | 33 | 619 |

The tree contains 459 campaign-owned files and 1,843 theorems; the checked
closure contains 205 proof modules. Of the original 1,831 theorems, 1,224
await carry validation. Checked counts are H1 122, H2 179, H3 54, H4 167,
H5 70 and H6 27. All 258 terminal names and their order remain; all six
whole-result closures and the full proof gate remain lagging.

The five native link contracts retain optional-device vacuity, numeric
index uniqueness, owner uniqueness and hashed-keypair allocation bounds.
Newlink errors remain stopped executions; normal allocation failure is
covered. Creation keeps the existing-device branch and removes the device
after a normal negative initialization result. Deletion uses the original
default callbacks instantiated at `WG.M`, not arbitrary callbacks, and
keeps both the absent-device return and successful destructor absence.

The recorded-port contracts keep arbitrary actual WG and Ambient states.
Socket replacement preserves the exact pending hidden-record value.
The supplied four-byte draw consumes precisely its first record and leaves
the arbitrary suffix. Total zero-port initialization retains the original
network and both socket/external-port freshness premises. A collision still
has the exact original outside-domain message and last-decision site.
The hidden-stream frame moved to `RecordedPortFrames`; it remains
substantive because `socketReinit : WG.M Unit` can access Ambient.

The four configuration contracts preserve the first matching interface
selection, arbitrary fixture lists, and the original live/bounded/down-peer
premises. The malformed second peer returns `-EINVAL` after the first
peer's scalar writes and one device-generation increment. The readback
still observes those writes with the original empty-list, fresh-cursor
and room premises; these remain total contracts, not success-only claims.

The eighteen pure contracts are unchanged. They express removal-list
effects, node-pair shape and owner clearing over the same carried
`NodeRemoval`, `RemovalRun` and `RemovalEffect` relations.
`AllowedPairsFrames` remains a frame file; its node-pair preservation
inside Device is not provided by the subsystem type.

The new wheel support describes the complete actual WG state after
normally returning placement. A kept slot changes the selected expiry
and retains wheel metadata and the enqueue counter. An enqueue changes
the expiry and selected wheel entry with the next stamp, incrementing the
counter once. Every other WG field is exact. No wheel-consistency,
record-readiness or arithmetic-admission premise was added; operational
record and invariant failures remain Stops. This is added support, not
a retyping or deletion of any of the seven stale exact-peer timer claims.
Those claims and the existing statement-artefact counterexample are unchanged.

Scoped builds pass: LinkSource 82 jobs, RecordedPort 47, DeviceScalars 54,
the pure closure 59 then 61, and WheelPlacementSource 32. LinkSource's
dependency replay includes the previously recorded mirror `Env:865`
`String.mk` deprecation; no campaign proof warning remains and the mirror
was not edited. Axiom audits cover 331 logical roots in the combined
link/configuration closure and 35 in the wheel closure, with only the three
standard axioms. Fresh replay passes for LinkSource, RecordedPort,
DeviceScalars, AllowedOwnerClear, AllowedPairsEffects and
WheelPlacementSource. Independent reviews found no remaining issue.
The token/import/public-name/whitespace checks and mirror/shared-layer
boundaries pass.

Development: LinkSource took two changed probes (first native sleeping
effect/lift normalization and one unused simp argument, then clean).
RecordedPort passed its first combined probe and separated package build.
DeviceScalars took four probes: two normalization failures, a deterministic
kernel timeout, then compositional success. The full first output was saved;
its truncated display was followed by inspection of the remainder. Wheel
placement took four changed probes for record syntax, source joinpoint
factoring and local normalization, then a clean pass. The unchanged pure
modules and all package builds passed first time. No infrastructure rerun,
cap/proof-limit change or guest run occurred.

Reproduce with `scripts/in-bundle lake build` on the six fresh-replay roots
above under `Leanux.Proofs.WG`; inspect logical roots with `#print axioms`
and replay each with `scripts/in-bundle lake env leanchecker --fresh MODULE`.
Use `capped`, 32 Lean threads and 16 QEMU slots on this host.

## Table invariants, identity, expiry and recorded initiation inputs

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Index.TablePreservationSource`, `SessionCoherenceSource`, `TablePeerFrames` | 8 | 8 | 0 | 0 | 0 | 8 |
| `Config.EndpointSources`, `PrivateKey`, `Precomputation` | 6 | 5 | 0 | 1 | 0 | 6 |
| `Config.AllowedReplacement` | 7 | 5 | 0 | 2 | 0 | 7 |
| `Config.ExpiryEffects`, `ExpiryReadSource`, `ExpiryClock` | 11 | 9 | 0 | 2 | 0 | 11 |
| `Noise.InitiationReadyInputFrames`, `InitiationReadyInputSource` | 2 | 2 | 0 | 0 | 0 | 2 |
| This tranche | 34 | 29 | 0 | 5 | 0 | 34 |
| Cumulative processed baseline and checked support | 641 | 449 | 21 | 171 | 33 | 653 |

The census is 464 campaign-owned files, 1,843 theorems and 218 checked proof
modules. Of the baseline, 1,190 theorems still await validation.
Checked support is H1 124, H2 187, H3 54, H4 191, H5 70 and H6 27.
All 258 terminal names/order remain, and all six terminal closures and the
full proof gate remain lagging.

The table source contracts combine numeric-index and owner/allocation
invariants from the same actual native execution. Their optional-device
domain remains unchanged; guarded `liftIndex` preserves missing-device
Stops. Session coherence retains its resident, self-word and rotation-fresh
premises, with installation conditional on a true result. The three table
frames remain substantive within WG: peer writes, MAC generation and the
table/allocation cursor preserve exactly the original invariants.
The existing declarations moved from `SendSource`, `ResponseSource`
and `SendFrames`; all their other bodies remain unchanged and pending.
The unchanged `TimerDiscipline.SendView` supplies the existing cursor,
without a duplicate observation definition.

Identity/precomputation keep arbitrary peers and devices, both identity and
null-result arms, and the exact ordered repeated map writes. The unchanged
private-key request increments the generation once without a new pending
work or empty-peer-list premise. Endpoint clearing keeps both record modes,
its exact device/other-peer frame and the actual reset timestamp.
Root allowed-IP replacement retains every singleton/node/root/refcount/down
and selector premise: acquisition, list/root removal and retained release
occur in order, after the outer generation increment.

Expiry retains its resident-only partial domain. A NULL handshake peer word
or missing keypair still Stops; no readiness assumption was introduced.
Index removal precedes handshake zeroing, the actual clock read/reset,
and the ordered next/current invalidations, including aliased keypairs.
The original prefix declarations and `zeroedHandshake` definition moved
to `ExpiryReadSource`, allowing the existing head and clock proofs to share
the same source contract. `expiryAfterClock_exact` still needs no residency
premise because its input device construction installs the peer. The
clock-extraction theorem names the actual intermediate WG and Ambient
states from the same run.

The two initiation input contracts preserve the exact supplied site,
16/32-byte width, resident device and arbitrary record suffix.
`InitiationReadyInputFrames.hidden_run` keeps exact full-product execution
through the actual Ambient lift, including every subsystem and fixture
field. The total input contract runs native WG over arbitrary Ambient.
The other 23 initiation-source theorem bodies remain pending and unchanged;
these are moved original contracts, not added companions.

Scoped builds pass: table source 83 jobs, session coherence 87, table frames
40 (including the unchanged SendView), endpoint source 49, private key 56,
precomputation 57, root replacement 61, expiry effects 60, factored expiry
clock 62, and initiation input 30. No compiler warning remains.
Axiom audits cover 383 logical roots in the first combined source closure,
270 in the expiry/replacement/frame closure and 23 in the initiation-input
closure; every root uses only the three standard axioms. Fresh replay passes
for SessionCoherenceSource, EndpointSources, Precomputation, ExpiryClock,
AllowedReplacement, TablePeerFrames and InitiationReadyInputSource.
Independent reviews found no remaining issue. Static token/import/name
checks, whitespace and mirror/shared-layer boundaries pass.

Development: table source/session coherence/private key passed first probe;
table frames passed the second after a missing type annotation/import.
Endpoint clearing passed the fourth after Boolean/record-lift normalization
and unused-simp fixes. Precomputation first passed with an unused simp
argument; removing the wrong occurrence failed, and the corrected third
probe passed. Root replacement passed the second after two closed mask
equalities and a warning fix. Expiry effects passed the second after native
lift typing, bind/conditional factoring and a substitution fix; the
factored clock candidate passed first time. Initiation input passed the
second after redundant simp arguments were removed. Full compiler outputs
were saved before preview; truncated previews were inspected further.
All package builds passed first time. No infrastructure rerun, cap or proof
limit increase, or guest run occurred.

The separate `modPeerTimer_sendQueue` draft remains unclosed and uncounted.
Seven changed agent probes and one changed root probe failed: the initial
recursive split also reached a deterministic heartbeat limit; the final
attempts leave two source-suffix equality obligations. No new premise,
tracked placeholder or semantic discrepancy was accepted. Its scratch
candidate remains available for further work; this is a failed proof
attempt, not a scoped validation pass.

Reproduce with `scripts/in-bundle lake build` on the seven fresh-replay
roots above under `Leanux.Proofs.WG`, audit logical declarations with
`#print axioms`, and replay each using
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Quiet key installation and initiation crypto

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.KeyPeerLoop`, `KeyInstall` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Config.KeyFieldFrames` | 2 | 0 | 0 | 2 | 0 | 2 |
| `Noise.InitiationReadyCryptoModel`, `InitiationReadyCryptoFrames` | 7 | 5 | 0 | 2 | 0 | 7 |
| This tranche | 15 | 11 | 0 | 4 | 0 | 15 |
| Cumulative processed baseline and checked support | 656 | 460 | 21 | 175 | 33 | 668 |

The census is 466 campaign-owned files, 1,843 theorems and 224 checked proof
modules. Of the original baseline, 1,175 theorems await validation.
Checked support is H1 131, H2 187, H3 54, H4 199, H5 70 and H6 27.
All 258 terminal names/order remain; all six terminal closures and the full
proof gate remain lagging. No new charter result is claimed.

Quiet key installation retains the original partial domain and snapshotted
peer list. Identity installation and cookie precomputation precede each
peer's precomputation and key expiry. Repeated peer IDs and keypair aliases
remain allowed; absent peers and dangling state still Stop. The quiet
premise excludes only the staged-send case. The source factor retains its
unconditional equation, including staged sends outside that premise.
The two pure field frames still describe preservation within Device and
remain separate in `KeyFieldFrames`.

The five crypto contracts retain totality, their original nonzero/DH/public
premises, arbitrary byte lengths and hidden streams. Their arbitrary
predicate relates the actual WG, FS, Task and Seccomp worlds and hidden
records through the actual product lift: all 43 old Kernel fields remain
represented by their new subsystem owners. No default reconstruction or
fixture restriction was introduced. Decision-trace changes are permitted,
as before. These substantive frames moved to
`InitiationReadyCryptoFrames`; the two unchanged KDF identities moved to
`InitiationReadyCryptoModel`. The other sixteen initiation-source theorem
bodies remain unchanged and pending.

Scoped builds pass: KeyPeerLoop 63 jobs, crypto 32, KeyInstall/KeyFieldFrames
65, then warning-free KeyFieldFrames 62. The latter's first build reported
one unused simp argument; it was removed without changing the statement.
Axiom audits cover 192 logical roots in 42 proof modules, using only the
three standard axioms. Fresh replay passes for KeyPeerLoop,
InitiationReadyCryptoFrames, KeyInstall and KeyFieldFrames. Independent
review found no remaining issue. Token/import/name checks, whitespace and
mirror/shared-layer boundaries pass.

Development: KeyPeerLoop passed its first changed probe. Crypto took six
changed probes for native normalization and nested result witnesses,
including removal of one unused simp argument. KeyInstall took seven:
the first five failed at branch markers, substituted variables and the
actual nested StateT continuation; the sixth closed with one unused simp
argument and the seventh was warning-free. Full outputs were saved before
preview; truncated diagnostic previews were followed by inspection of the
remaining diagnostics. One further changed root timer-queue draft failed
at the same two source-equality obligations and remains uncounted. No
infrastructure rerun, cap/proof-limit increase or guest run occurred.

[AGENT 2026-10-17] The pending timer correction will describe the actual
entry/exit WG and Ambient state, including wheel entries and enqueue
counters. It will distinguish records-off placement, recorded same-expiry
metadata updates and recorded changed-expiry placement. A kept wheel slot
retains its old bucket and stamp; enqueue bounds apply only to enqueues.
This preserves the mirror's actual cases without a readiness premise.
The seven stale exact-peer contracts remain pending until their corrected
counterparts close; these are statement-artefact corrections, not type-only
retypes or type-given deletions.

Reproduce with `scripts/in-bundle lake build` on the four fresh-replay roots
above under `Leanux.Proofs.WG`, audit logical declarations with
`#print axioms`, and replay using
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Configuration claims, general removal and initiation continuations

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.AllowedGeneralReplacement`, `Fwmark`, `PeerDead` | 9 | 7 | 0 | 2 | 0 | 9 |
| `Config.LeafSourceClaims` | 12 | 12 | 0 | 0 | 0 | 12 |
| `Noise.InitiationReadyFinishSource`, `InitiationReadyWriteSource`, `InitiationReadyClockSource`, `InitiationReadyContinuationSource` | 10 | 10 | 0 | 0 | 0 | 10 |
| `TimerDiscipline.ArmingOffSource` | 0 | 0 | 0 | 0 | 1 | 1 |
| This tranche | 31 | 29 | 0 | 2 | 1 | 32 |
| Cumulative processed baseline and checked support | 687 | 489 | 21 | 177 | 34 | 700 |

The census is 472 campaign-owned files, 1,844 theorems and 233 checked proof
modules. Of the baseline, 1,144 theorems await validation. Checked support
is H1 141, H2 187, H3 54, H4 220, H5 70 and H6 28. All 258 terminal names
and their order remain; all six whole-result closures and the full gate
remain lagging. The retrofit continues before new charter results.

General allowed-IP replacement retains the general `RemovalEffect` domain,
including empty lists and non-root structural removal. Lookup acquires the
reference before removal; the tail releases once. Device selection and
generation increment retain their original order, and the inner selector
remains independent. Peer death retains its original general-removal
totality domain and Device effects. Its proof-local source factor now
includes the landed `pubkeyRemoveHashed` decision and device read before
hash removal, matching the actual mirror. No new table/residency premise
was added. Its pure effect theorem is unchanged.

The fwmark contract remains partial, with only the original creating-net
and device-selection premises. Its source reduction and loop preserve all
Device fields outside peers, while writing the mark and incrementing the
generation. Missing or repeated peer-list entries and reset-record Stops
remain in its original domain.

Twelve source claims moved to `LeafSourceClaims`: six partial contracts,
four total contracts and two exact source equations. The ten state
predicates now explicitly use the campaign projection. It retains every
original observation: Device, the selected peer, port/socket/running
fields and fixture-interface selection. These claims contain no arbitrary
product callback or full-product equality that could be lost by narrowing.
The remaining source-claim suffix is unchanged. No terminal Statements
module is counted as validated by this extraction.

The ten initiation contracts preserve the original resident/non-NULL word,
crypto-success, clock-width and collision/fresh-draw premises. The stored
handshake peer word need not equal the selected peer or point to a resident
peer. Each call receives the actual returned WG and Ambient states from
the preceding call. Ordered peer writes, index insertion, message bytes
and unused hidden-record suffixes are exact. The two write contracts still
allow an absent record stream. Local exact native crypto reductions leave
the separately checked product-predicate contracts unchanged. Six theorem
bodies remain pending in the original initiation source.

The new unrecorded-arm support describes every normally successful run
with records disabled and a resident peer. Its caller option is arbitrary,
as the source ignores it in that mode. It retains the exact kept/enqueued
wheel metadata and enqueue counter through `wheelPlacementState`.
It adds no consistency/readiness premise and is not counted as a retyping
of one of the seven legacy arming contracts.

Scoped builds pass: general replacement 69 jobs, fwmark/unrecorded arm 60,
initiation finish 36, writes/clock 41, continuations 43, projected leaf
claims 62 and peer death 65. No warning remains. Axiom audits cover 393
logical roots in 71 proof modules, using only the three standard axioms.
Fresh replay passes for AllowedGeneralReplacement, Fwmark, LeafSourceClaims,
InitiationReadyClockSource, ArmingOffSource, InitiationReadyContinuationSource
and PeerDead. Independent reviews found no remaining issue. Static checks,
whitespace and mirror/shared-layer boundaries pass.

Development: general replacement, unrecorded arm and continuation contracts
passed their first probes. Initiation finish passed the third after native
result normalization and record-update layout fixes; writes/clock passed
the second after exposing the exact clock site. Native and then projected
leaf claims both passed. Peer death passed the second after an explicit
import restored its existing `withPeer` dependency. Fwmark took eight
changed probes: the first six failed at nested run/lift/state/map
normalization, the seventh closed the goal before a redundant tactic, and
the eighth was clean. Full outputs were saved before preview; truncated
fwmark previews were followed by diagnostic-list and tail inspection.

The recorded-arm draft remains unclosed and uncounted. After the first
unrecorded-arm pass, three recorded drafts failed at the hidden-read bind;
four later same-expiry drafts reached that bind but still failed at
read-equation normalization. These failures establish no semantic
counterexample. No infrastructure retry, cap/proof-limit increase or guest
run occurred.

Reproduce with `scripts/in-bundle lake build` on the seven replay roots
above under `Leanux.Proofs.WG`, inspect logical declarations with
`#print axioms`, and replay using
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Initiation completion, projected identity and queued-handshake finding

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.ClearedSources`, `FwmarkEffects` | 12 | 11 | 0 | 1 | 0 | 12 |
| `Noise.InitiationReadySource` | 6 | 6 | 0 | 0 | 0 | 6 |
| `Config.QueuedReferenceSource` | 1 | 1 | 0 | 0 | 0 | 1 |
| `Config.IdentitySourceClaims` | 12 | 9 | 0 | 3 | 0 | 12 |
| `TimerDiscipline.ArmingSameExpirySource`, `Config.QueuedHandshakeFindings` | 0 | 0 | 0 | 0 | 2 | 2 |
| This tranche | 31 | 27 | 0 | 4 | 2 | 33 |
| Cumulative processed baseline and checked support | 718 | 516 | 21 | 181 | 36 | 733 |

The census is 476 campaign-owned files, 1,846 theorems and 240 checked proof
modules. Of the baseline, 1,113 theorems await validation. Checked support
is H1 147, H2 187, H3 54, H4 246, H5 70 and H6 29. All 258 terminal names
and their order remain. Each of H1–H6 remains in retrofit; no whole-result
closure or full-gate pass is claimed.

The seven clearing contracts and four operational fwmark effects retain
arbitrary peer lists and accumulated visits, including duplicate and absent
entries. Record-consuming resets keep their original stopped outcomes.
The pure double-clear equation is unchanged. The six remaining initiation
contracts now use native WG execution throughout, retaining the resident,
identity, non-NULL word, crypto, clock-width and collision/fresh-draw
premises. The pure effect equation observes WG and Ambient. Its separate
three mode frames and projected/public wrappers remain pending.

Twelve existing claims moved from `SourceClaims` to
`IdentitySourceClaims`: four total and four partial projected contracts,
one native source equation, and three unchanged dump-cancellation aliases.
They retain device selection, ordered key updates, clock existence and
the actual snapshotted peer list. The remaining source-claim declarations
are unchanged. These extracted aliases do not validate the terminal module.

The retained-reference partial contract moved to `QueuedReferenceSource`.
Zero and overflow reference counts still stop; successful execution itself
implies positivity and the exact increment. The other five queued-send
declarations remain unchanged and pending. A checked
[queued-handshake counterexample](2026-10-17-proof-campaign-2-queued-handshake.md)
shows that the old pending-peer prediction is stale after `1f0fbeb):
the actual queue becomes `[0, 0]` and the reference count becomes 3.
This is a statement artefact predating the state split, without a reachability
or kernel-bug claim.

The new recorded same-expiry arm support observes the exact current WG
effect: the jiffies value and a nonzero unit/address registration can change,
while peer and wheel state stay unchanged. Its normal-execution premise
implies the recorded signed gap is 0 or 1. It imposes no wheel-consistency
premise, since the source returns before that check. It complements the
unrecorded-arm support; neither is counted as one of the seven stale
legacy arming contracts.

Scoped builds pass: clearing 57 jobs, fwmark effects 58, initiation 44,
reference/same-expiry 70, queued finding 49 and identity claims 108.
The identity build reports the inherited mirror `Env.lean:865`
`String.mk` deprecation; campaign code has no warning and the mirror is
unchanged. Axiom inspection covers 342 logical roots in 66 proof modules,
with only the three standard axioms. Fresh replay passes for
FwmarkEffects, InitiationReadySource, ArmingSameExpirySource,
QueuedReferenceSource, QueuedHandshakeFindings and IdentitySourceClaims.
Independent reviews, static checks, whitespace and mirror/shared boundaries pass.

Development: clearing passed its second changed probe after invariant/bind
normalization; fwmark effects passed its second after replacing a deprecated
simplification lemma. Initiation, retained-reference and identity claims
passed first probes. The queued witness passed its second after record
syntax and result normalization fixes. Same-expiry probes five through seven
failed at state rewrites or record syntax; eight passed without warnings.
No failed outcome is counted as validation.

Two further scratch batches remain uncounted. Five changed-expiry probes
failed at a reserved identifier, source joins, simplifier steps and then a
nested continuation selected by generic splitting. Six mode-frame probes
failed at stale helpers, tactic-framework mismatches and explicit native
reductions; one reached the unchanged heartbeat limit. The independent
bucket-mode induction elaborates but is not yet packaged. Ambient remains
accessible to these operations, so mode preservation is substantive and
cannot be deleted on type grounds. These failures establish no counterexample.
No infrastructure retry, cap/proof-limit increase or guest run occurred.

Reproduce with `scripts/in-bundle lake build` on the six fresh-replay roots
above under `Leanux.Proofs.WG`, inspect logical declarations with
`#print axioms`, and replay using
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Port semantics, handshake inspection and crypto frames

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.EmptyKeypairs`, `RunningPort`, `DevicePorts` | 8 | 8 | 0 | 0 | 0 | 8 |
| `Roaming.HandshakeAuditSource` | 3 | 3 | 0 | 0 | 3 | 6 |
| Roaming response/initiation crypto effects and frames | 12 | 8 | 0 | 4 | 0 | 12 |
| `TimerDiscipline.ArmingChangedExpirySource` | 0 | 0 | 0 | 0 | 1 | 1 |
| This tranche | 23 | 19 | 0 | 4 | 4 | 27 |
| Cumulative processed baseline and checked support | 741 | 535 | 21 | 185 | 40 | 760 |

The census is 481 campaign-owned files, 1,850 theorems and 255 checked proof
modules. Of the baseline, 1,090 theorems await validation. Checked support
is H1 147, H2 187, H3 72, H4 254, H5 70 and H6 30. All six result closures
and the full gate remain lagging; all 258 terminal names remain in order.
The unchanged RestartModel, ResponseModel and InitiationModel definitions
also build; they add no theorem count.

Empty-keypair cleanup retains arbitrary pure slot selectors and peer updates,
the resident/empty premises and all three ordered writes. Port cleanup keeps
arbitrary peer lists, accumulated visits and current/initial Device relations.
Nonzero socket contracts include the original no-network and occupied-port
outcomes. Device configuration still increments the generation before calling
setPort, retains the same-port shortcut and preserves the full bound-port
function during lookup. Reset-record and absent-peer Stops remain within the
partial contracts; no list readiness is added.

Handshake inspection keeps its original three arbitrary-product contracts in
`Roaming.Product`. Their prefix and suffix receive actual full product
states, and exact outcomes retain the eight original fixture observations.
Three native companions receive actual WG and Ambient successor states.
Inspection preserves entry state and reports prefix errors exactly; successful
prefix facts survive suffix failure. `HandshakeAuditFacts` is parameterized
by snapshot type without changing its three clauses.

Crypto statements are separated into pure `ResponseCryptoEffects` and
`InitiationCryptoEffects`, and preservation contracts in the corresponding
`CryptoFrames` files. Their old Source files are import facades. All eight
operational contracts keep total correctness and arbitrary predicates over
WG, FS, Task and Seccomp owners through the actual product lift. Both DH
outcomes, failed/successful decrypts and zero/nonzero precomputation remain
covered with no new trace, byte-width or crypto-success assumption. One
unused simplification argument was removed from an unchanged pure KDF claim.

The changed-expiry arm support follows the actual record, unit, clock,
previous-clock, overdue-bucket and pass-step guards. Successful execution
implies the signed caller gap is 0 or 1 and the exact complete WG state:
jiffies and optional unit registration, the recorded base clock, then
`wheelPlacementState` including kept/enqueued metadata and counter effects.
It adds no consistency/readiness premise. This completes the three supporting
arm cases; the seven legacy arming contracts still await correction.

Scoped builds pass: empty-keypair/pure models 71 jobs, audit model 9,
running-port/audit 65, response effects 31, response crypto 34,
initiation effects 33, initiation crypto 36, changed-expiry 35 and device
ports 61. No campaign warning remains. Axiom inspection covers 359 logical
roots in 68 proof modules, using only the three standard axioms.
Independent review found no remaining issue; static checks, whitespace and
mirror/shared-layer boundaries pass.

Development: empty-keypair cleanup passed its second probe after replacing a
private-name reference with its actual get/set composition. Both product and
native audit probes passed first time. RunningPort passed the third changed
probe after conditional/update and logged Boolean normalization; DevicePorts
passed the fourth after signature, native continuation and branch-focus fixes.
Response frames passed the second after list-take/postcondition normalization;
initiation frames passed the second after preserving the exact private
zero-key comparison during rewriting. The first response-effects build
reported an unused simp argument; the corrected build is warning-free.

Changed-expiry probes six through ten failed at native read normalization,
branch focus and finally a redundant tactic after the goal closed. Removing
that tactic passed the root probe and package build. All failed probes remain
failures, not validation. Full outputs were saved before preview; truncated
port previews were followed by the remaining diagnostics. No infrastructure
retry, cap/proof-limit increase or guest run occurred.

Fresh replay passes for EmptyKeypairs, DevicePorts, HandshakeAuditSource,
ResponseCryptoSource, InitiationCryptoSource and ArmingChangedExpirySource.
Reproduce with `scripts/in-bundle lake build` on those modules under
`Leanux.Proofs.WG`, inspect logical declarations with `#print axioms`,
and replay with `scripts/in-bundle lake env leanchecker --fresh MODULE`.
On this host use `capped`, 32 Lean threads and 16 QEMU slots.

## Initiation mode, zero ports and timer queue frames

| Tranche | Before | Retyped | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.InitiationReadyFrames`, `InitiationReadyClaims` | 4 | 4 | 0 | 0 | 3 | 7 |
| `Config.ZeroPortDrawFrames`, `ZeroPort` | 5 | 5 | 0 | 0 | 0 | 5 |
| `TimerDiscipline.TimerQueueFrames` | 2 | 2 | 0 | 0 | 0 | 2 |
| `Config.AllowedRemovalConverseLeaves` | 7 | 7 | 0 | 0 | 1 | 8 |
| This tranche | 18 | 18 | 0 | 0 | 4 | 22 |
| Cumulative processed baseline and checked support | 759 | 553 | 21 | 185 | 44 | 782 |

The census is 485 campaign-owned files, 1,854 theorems and 262 checked proof
modules. Of the baseline, 1,072 theorems await whole-module validation.
Checked support is H1 154, H2 187, H3 72, H4 267, H5 70 and H6 32.
All six terminal closures and the full gate remain lagging; all 258 terminal
names and their order remain intact.

The three initiation mode frames retain arbitrary index tables and Ambient
states. The actual guarded index lift, all hidden-input modes, placeholder
and passive records, and normal returns from rejected paths remain covered.
These frames are substantive because their action types still permit Ambient
updates. Three small private execution supports accompany them; no shared
layer is copied. The projected total creation claim retains its exact
message, ordered Device writes, hidden suffix and all original static/draw
premises. Mode now projects from Ambient. The existing
`original_create_initiation_ready` declaration remains in Statements, with
only its two mode projections changed. Its isolated body and axiom check pass;
it is excluded from the checked-module census until the whole terminal module
can be validated.

The zero-port draw/range frame moves to `ZeroPortDrawFrames`, with the
original arbitrary former-Kernel predicate preserved across all actual
subsystem owners. Four native port contracts remain in `ZeroPort`.
They retain the current/initial Device relation, socket/port updates, captured
peer list and initial-peer effects. Colliding draws and bad records still
stop; no new success or record assumption is introduced.

The two queue frames move intact in scope to `TimerQueueFrames`.
Residency is derived from successful guard execution, rather than assumed.
All timer modes and caller options are covered using the three current arm
effects; recorded execution without a caller still stops. Give-up follows
the actual expiry/wheel deletion, staged-packet accounting, pending check and
guarded zero-key arm. Its helper moves from `RetryBaseSource` into
`RetryGiveUpSource` with the same body and native type. Remaining retry
contracts are unchanged, including those pending on the stale queue prediction.

Seven removal-converse leaves moved from their aggregate. Six operational
contracts retain arbitrary slots, node IDs and partial-success domains
through the actual guarded AIP adapter. Only slotSet retains its original
NodePairs premise; child bounds and node residence follow from execution.
The original returns-to-ensures law generalizes over arbitrary product
StateT state; a separate native companion quantifies every Ambient
realization. Fifteen original aggregate declarations remain unchanged and
pending.

Scoped builds pass: zero ports/initiation 84 jobs and queue/removal leaves 78.
Axiom inspection covers 435 logical roots in 83 proof modules using only
the three standard axioms, including every dependency of the private mode
supports. The isolated initiation headline uses only those axioms as well.
Independent reviews, static checks, whitespace and mirror/shared boundaries
pass. No campaign warning remains.

Development: mode-frame probes seven through eleven had four reduction/
tactic failures then a clean prefix; twelve through seventeen had five
source-composition, binder or simplification failures, including one unchanged
heartbeat limit, then a warning-free combined proof. Zero ports passed the
second changed probe after binder/generated-block fixes. The guarded timer
queue and give-up extension each passed their first probes. Packaging the
helper initially left an orphaned documentation comment and failed; relocating
the comment fixed the build. Removal leaves passed the second probe after
using the equalities already established by case inversion. All failures
remain recorded as failures. Full outputs preceded previews; no infrastructure
retry, cap/proof-limit increase or guest run occurred.

Fresh replay passes for ZeroPort, InitiationReadyClaims, TimerQueueFrames and
AllowedRemovalConverseLeaves. Reproduce with `scripts/in-bundle lake build`
on those modules under `Leanux.Proofs.WG`, inspect logical declarations
with `#print axioms`, and use
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Projected port claims, removal branches and explicit timer corrections

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.PortSourceClaims` | 14 | 14 | 0 | 0 | 0 | 0 | 14 |
| `Config.AllowedRemovalConverseBranches` | 7 | 7 | 0 | 0 | 0 | 0 | 7 |
| `TimerDiscipline.ArmingClaims` | 2 | 0 | 2 | 0 | 0 | 0 | 2 |
| This tranche | 23 | 21 | 2 | 0 | 0 | 0 | 23 |
| Cumulative processed baseline and checked support | 782 | 574 | 2 | 21 | 185 | 44 | 805 |

The census is 488 campaign-owned files, 1,854 theorems and 265 checked proof
modules. Of the baseline, 1,049 await whole-module validation. Checked support
is H1 154, H2 187, H3 72, H4 288, H5 70 and H6 34. All six whole-result
closures and the full gate remain lagging. The 258 terminal names and order
remain unchanged.

Fourteen existing source claims now live in `PortSourceClaims`, over the
campaign projection: nine partial, four total and one exact-stop contract.
Every original observation remains: selected fixture interface, Device,
pointwise listed/unlisted peer effects, bound-port functions or single-port
bounds as appropriate, supplied draw records and arbitrary unused tails.
Recorded-return wrappers unpack the actual native run. Collision retains the
exact outside-domain error message and existential source site, rather than
asserting merely that success is impossible. The fourteen corresponding
terminal declarations also check in isolation with standard axioms; only the
collision wrapper's proof body changes to use the projected alias. These
isolated checks do not enter the checked-module census or validate the
complete Config Statements module.

Seven more removal-converse branches moved out of the aggregate. They retain
the original NodePairs, shape, unlink and parent-choice premises. Successive
node residence, sibling and parent reads remain conclusions of the actual
execution, with aliases allowed. Local monadic compositions use the actual
guarded AIP lifts inside WG execution. Eight aggregate contracts remain
unchanged and pending at this checkpoint.

The two `ArmingClaims` statements explicitly correct stale pre-wheel
conclusions; they are not type-only carries. A universally quantified entry
snapshot names the actual starting observation without adding readiness.
Recorded arming preserves its original recorded-mode/resident-peer
normal-return domain and signed clock gap, while describing the exact whole
WG state in same-expiry and changed-expiry cases. Deletion specifies the
entire final native snapshot, clearing both expiry and wheel and preserving
Ambient. Three pure view transformations retain every other WG/snapshot
field. The [legacy deletion counterexample](2026-10-17-proof-campaign-2-timer-carry.md)
remains valid. Five other legacy arming/caller contracts remain unchanged
and pending; downstream uses must adopt the corrected effects. No mirror
or shared-layer change is involved.

The combined scoped build passes 97 jobs without warnings. Axiom inspection
covers 366 logical roots in 69 proof modules with only the three standard
axioms. Independent reviews, static checks, whitespace and mirror/shared
boundaries pass. Port source aliases and projected arming corrections passed
their first probes; removal branches passed their second after three local
compositions were explicitly typed as WG.M. No infrastructure retry,
cap/proof-limit increase or guest run occurred.

Fresh replay passes for PortSourceClaims, AllowedRemovalConverseBranches and
ArmingClaims. Reproduce with `scripts/in-bundle lake build` on those modules
under `Leanux.Proofs.WG`, inspect logical declarations with
`#print axioms`, and replay with
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Complete removal converse and response-consumer scope

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Config.AllowedRemovalConverseSource` (remaining contracts) | 8 | 8 | 0 | 0 | 0 | 0 | 8 |
| `Roaming.ResponseConsumeSource`, `ResponseConsumeProductSource` | 2 | 2 | 0 | 0 | 0 | 2 | 4 |
| This tranche | 10 | 10 | 0 | 0 | 0 | 2 | 12 |
| Cumulative processed baseline and checked support | 792 | 584 | 2 | 21 | 185 | 46 | 817 |

The census is 490 campaign-owned files, 1,856 theorems and 269 checked proof
modules. Of the baseline, 1,039 await whole-module validation. Checked support
is H1 154, H2 187, H3 76, H4 296, H5 70 and H6 34. All six terminal closures
and the full gate remain lagging. All 258 terminal names and their order
remain intact.

The final eight removal-converse contracts now compose the checked leaves
and branches in the aggregate source module. Original NodePairs, shape,
residency and effect premises remain, including arbitrary aliases and duplicate
identifiers. Actual guarded node reads establish intermediate residency.
The peer-death composition follows the current public-key removal and actual
normal execution; it does not substitute the refuted peer-release totality
claim. The full removal-converse source aggregate now builds.

The native response consumer retains its exact erased computation, including
all errors, and its authenticated-cut facts and committed successor snapshot.
The old snapshot also observed eight fixture fields. Two explicitly added
product companions preserve that full scope: the model captures the actual
fixture, executes the native consumer once through the actual WG lift and
records the full product observation. They preserve listeners, NAPI choices,
route state, sender inbox and namespace holder observations; no default or
reconstructed execution state is used. The native and product claims retain
the original identity/state hypotheses, arbitrary failed peer writes and
independent lookup-owner identity. No success/readiness premise is added.
These are claims, not cross-subsystem frame lemmas. The separate
`ResponseConsumeProductModel` contains the fixture-extended certificate and
execution only, with no theorem.

The existing `Noise.InitiationReady.hidden_mode` helper is now public with
its proof unchanged, so timer input frames can reuse it without copying a
layer. This visibility change does not affect theorem counts.

The combined scoped build passes 97 jobs without warnings. Axiom inspection
covers 410 logical roots in 70 proof modules and finds only the three standard
axioms. Independent review, static checks, whitespace and unchanged mirror/
shared-layer boundaries pass. Removal-tail probes: the first failed on local
case equalities/binders and reported two unused simplifications; the second
passed cleanly. Response native probes one and three closed with unused simp
warnings, probe two failed local read/commit normalization, and four passed
cleanly. Product probes one through five failed progressively exposed bind
reductions; six closed substantive goals but had a redundant tactic and two
unused simplifications; the authorized seventh cleanup passed without
warnings. These development failures are not passes. No infrastructure
retry, cap/proof-limit increase or guest run occurred.

Fresh replay passes for AllowedRemovalConverseSource, ResponseConsumeProductSource
and InitiationReadyClaims. Reproduce with `scripts/in-bundle lake build` on
those modules under `Leanux.Proofs.WG`, inspect logical declarations with
`#print axioms`, and replay with
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Noise terminal closure, guarded timers and replacement converse

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.Statements` | 22 | 22 | 0 | 0 | 0 | 0 | 22 |
| `Config.AllowedRemovalConverseClaims`, `ReplacementConverseSource` | 4 | 4 | 0 | 0 | 0 | 0 | 4 |
| `TimerDiscipline.GuardedArmingClaims`, `TimerInputFrames` | 2 | 0 | 2 | 0 | 0 | 2 | 4 |
| This tranche | 28 | 26 | 2 | 0 | 0 | 2 | 30 |
| Cumulative processed baseline and checked support | 820 | 610 | 4 | 21 | 185 | 48 | 847 |

The census is 492 campaign-owned files, 1,858 theorems and 274 checked proof
modules. Of the baseline, 1,011 await whole-module validation. Checked support
is H1 176, H2 187, H3 76, H4 300, H5 70 and H6 38. All 258 terminal names
and their order remain intact. H1's whole Statements module now checks on the
split mirror; H2–H6 terminal closures and the full gate remain lagging.

All 22 Noise headline contracts retain their scope. Twenty-one proof bodies
were already compatible with the carried dependencies; adjacent confirmation
now threads both actual native WG/Ambient executions. Its second call starts
at the first call's exact successor. Partial Stop paths stay partial. The
claims observe only the peer/device/counter fields and explicitly named
Ambient inputs; none loses an old fixture comparison or arbitrary product
callback. All declarations are counted as native retypes, including bodies
unchanged after their supporting aliases were retyped. H1's wider charter
obligations remain open: whole-call/lifetime reachability and exact derivation
clock provenance are not supplied by this retrofit.

The two removal claims use their actual native run with unchanged projected
relations. The two replacement source contracts retain general RemovalEffect,
NodePairs, original reference bounds and stopped-device premises. The outer
request obtains the actual acquired peer Device from its successful lookup
and feeds that same execution into the partial replacement update. It adds
no singleton/alias constraint or independent successful-run witness.

The timer contracts `modPeerTimer_effect` and
`timersSessionDerived_effect` explicitly correct their stale full-peer
conclusions. Their original residency/normal-return domains remain. The
arbitrary entry projection records the real input; separate `TimerInputFrames`
prove WG preservation and mode/result facts of the actual caller-clock read
and guard. The false guard preserves the entire WG state. The true guard
specifies nominal placement or recorded same-expiry/changed-expiry behavior,
including wheel/counter state and the signed clock gap. No timer/readiness
premise is introduced. These are two corrections, with two added support
frames; three legacy arming/caller contracts remain pending. The frame helpers
reuse the unchanged initiation hidden-mode proof rather than copying it.

Scoped build passes 155 jobs without warnings. Axiom inspection covers 665
logical roots in 127 proof modules, including all Noise headlines, using only
the three standard axioms. Independent review finds no scope loss in the
Noise or timer contracts; root review of configuration composition is clear.
Static checks, whitespace and mirror/shared boundaries pass.

Noise's first probe failed after case substitution removed two local names;
the changed second probe passed. Removal claims passed their first probe.
Replacement source probe one failed a redundant tactic and incomplete exact
lookup reduction; probe two passed. Timer probes one through four failed
annotations, substitution and source reductions (three/five warnings in
probes three/four); five closed the guard contract and six added the
session-derived caller, both clean. Full logs preceded previews. No
infrastructure retry, cap/proof-limit increase or guest run occurred.

Fresh replay passes for Noise.Statements, AllowedRemovalConverseClaims,
ReplacementConverseSource and GuardedArmingClaims. Reproduce with
`scripts/in-bundle lake build` on those modules under `Leanux.Proofs.WG`,
inspect logical declarations with `#print axioms`, and replay with
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Initiation lookup scope and remaining arming corrections

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Roaming.InitiationLookupSource`, `InitiationLookupProductSource` | 3 | 3 | 0 | 0 | 0 | 2 | 5 |
| `Config.ReplacementConverseRequestSource` | 1 | 1 | 0 | 0 | 0 | 0 | 1 |
| `TimerDiscipline.ArmingLifecycleClaims` | 3 | 0 | 3 | 0 | 0 | 0 | 3 |
| This tranche | 7 | 4 | 3 | 0 | 0 | 2 | 9 |
| Cumulative processed baseline and checked support | 827 | 614 | 7 | 21 | 185 | 50 | 856 |

The census is 496 campaign-owned files, 1,860 theorems and 281 checked proof
modules; 1,004 baseline declarations await validation. Checked support is
H1 176, H2 187, H3 81, H4 301, H5 70 and H6 41. H1's 22-headline terminal
closure is current over b700659; H2–H6 terminal closures and the full gate
remain lagging. All charter gaps and all 258 terminal names/order remain.

Initiation lookup provenance derives the first matching public-key entry,
resident peer, positive/nonoverflow reference and exact increment from the
actual successful lookup. Its projected entry fixes only the Device used by
the original conclusion, generalizing the old enclosing-Kernel fixation.
No key/peer coherence or readiness premise is added. Native bind/facts
companions carry the actual WG/Ambient successors; the Product bind/facts
retain arbitrary original product continuations and all eight fixture
observations in before/observed/after snapshots. Inspection observes a copy;
the actual lookup starts at the same state. Exact erasure includes every
Stop. The separate Product model holds data/predicates only.

The replacement request preserves its original lookup, reference bounds,
NodePairs, stopped-device and selector premises. Its composition executes the
actual generation increment and acquired-peer update, then relates the
removal and continuation from their real intermediate states. The unchanged
pure `requestGeneration` definition moves into `RequestModel`; both users
import it, avoiding a dependency on the still-pending private-key request
proof. That pending theorem is unchanged.

The last three legacy arming claims now live in `ArmingLifecycleClaims`;
`ArmingSource` is an import facade. Traversal retains its nonzero-interval,
running and alive conditions. Data receipt retains running, pending and dead
branches; pending writes exactly the keepalive flag in the complete WG view.
Active arms use the current complete nominal/recorded wheel effects tied to
the actual entry mode. Handshake completion reuses the previously checked
wheel theorem and specifies the complete Peer, including both expiry and
wheel clear, attempt/flag reset and actual hidden walltime. These are explicit
semantic corrections, not type-only carries. All seven originally identified
arming contracts are now corrected; downstream timer callers still need carry.

Scoped build passes 118 jobs without warnings. Axiom inspection covers 481
logical roots in 89 modules with only the three standard axioms. Independent
initiation-scope review and root reviews of replacement/timer composition
are clear. Static checks, whitespace and unchanged mirror/shared boundaries
pass. Initiation lookup passed changed probe two after handling impossible
successful-none branches and normalizing the actual Product lift. Replacement
request passed probe three after correcting its singleton-loop factor and
avoiding a conflicting simp rewrite (the preceding failed probe also warned).
Timer lifecycle probes one through five failed local source/branch reductions
with error/warning counts 3/4, 4/1, 3/0, 1/0, 1/0; probe six passed cleanly.
Full outputs preceded previews. No infrastructure retry, cap/proof-limit
increase or guest run occurred.

Fresh replay passes for InitiationLookupProductSource,
ReplacementConverseRequestSource and ArmingSource. Reproduce with
`scripts/in-bundle lake build` on those modules under `Leanux.Proofs.WG`,
inspect logical declarations with `#print axioms`, and replay with
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Exact peer-release outcomes and complete response lookup scope

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Noise.InitiationReadyFrames` metadata generalization | 0 | 0 | 0 | 0 | 0 | 4 | 4 |
| `TimerDiscipline.SendReadyFrames`, `RecordedFrames` | 5 | 5 | 0 | 0 | 0 | 0 | 5 |
| `Index.PeerRelease` | 1 | 0 | 1 | 0 | 0 | 0 | 1 |
| `Config.StructuralSourceClaims` | 4 | 4 | 0 | 0 | 0 | 0 | 4 |
| `Roaming.ResponseLookupSource`, `ResponseLookupProductSource` | 7 | 7 | 0 | 0 | 0 | 7 | 14 |
| This tranche | 17 | 16 | 1 | 0 | 0 | 11 | 28 |
| Cumulative processed baseline and checked support | 844 | 630 | 8 | 21 | 185 | 61 | 884 |

The census is 499 campaign-owned files, 1,871 theorems and 288 checked proof
modules; 987 baseline declarations await validation. Checked counts are H1 180,
H2 188, H3 95, H4 305, H5 70 and H6 46. H1's terminal closure is rechecked
after the metadata proof change; H2–H6 terminal closures and the full gate
remain lagging. All 258 original terminal names/order remain. Wider charter
obligations are unchanged.

Four metadata frames generalize the existing initiation-mode proof to any
predicate of armRecords and allocArmed. The four original mode signatures
remain exact specializations. Two private composition helpers generalize in
place; they add no declaration count. Three original allocation-arming frames
become short specializations over actual IndexM/WG.M runs. This avoids copying
the initiation execution layer. The two recorded-input frames preserve the
old arbitrary predicate over all four former-Kernel owners via the actual
Ambient lift, plus mode, and the original projected caller result/device/mode
facts. No new readiness premise or shared-layer edit is involved.

The corrected `peerPut_exact` replaces unconditional total return with a
precise outcome classification under exactly the same residency and positive
reference premises. Final release checks queued transmit/receive buffers
first, then the first pending timer/wheel entry, and reports the corresponding
exact invariant Stop. Otherwise it returns the original released Device.
The proof follows actual decrement, guarded index removal, dropped-packet
accounting, erasure and dispatch-identity retirement. Errors expose no invented
post-state. This is an explicit semantic correction supported by the existing
[counterexamples](2026-10-17-proof-campaign-2-peer-release.md), not a weakened
success claim or a new readiness hypothesis. Two Index headlines and six
configuration/timer source users still require their own outcome/domain carry.

Four existing configuration claims move to `StructuralSourceClaims` over
the campaign projection: partial expiry field effects and total witnessed
removal, replacement and peer-death effects. Original alias, RemovalEffect,
selector, reference and running hypotheses and all node/list/store conclusions
remain. Every success witness is the actual native result and successor states.
Other SourceClaims bodies are unchanged and pending.

The seven response lookup contracts now have native and Product forms. Product
continuations remain arbitrary. Before/observed/after/committed certificates
retain all eight actual fixture observations, using the real native lift and
pure certificate extension. Lookup owner and referenced peer remain independent;
no table coherence or success assumption is added. Failed-consumption peer puts
can still stop. Exact prefix, continuation and erasure equations cover those
errors too. Product models contain only data/predicates and pure extensions;
all operational claims stay in source files.

Build passes 160 jobs without warnings. Axiom inspection covers 723 logical
roots in 131 proof modules, using only the three standard axioms. Independent
reviews of metadata, recorded frames, peer release, structural claims and
response lookup are clear. Static checks, whitespace and mirror/shared
boundaries pass. Metadata/SendReady passed their first scratch probe; recorded
frames passed the second after projection normalization. Peer-release probe one
failed Boolean/projection normalization; two passed. Structural scratch began
with six candidates: an unported dump dependency and redundant singleton-domain
hypothesis warnings remain deferred with those two original bodies unchanged.
The four carried claims passed probe three after correcting projection reduction.
Response probes one/two failed predicate/identifier and nested-run normalization;
three closed native contracts, four failed Product tuple/map reductions and
reported two unused simplifications, five passed all fourteen cleanly. Full
outputs preceded previews; a truncated peer-release preview was followed by
inspection of its remainder. No infrastructure retry, cap/proof-limit increase
or guest run occurred.

Fresh replay passes for Noise.Statements, SendReadyFrames, RecordedFrames,
PeerRelease, StructuralSourceClaims and ResponseLookupProductSource. Reproduce
with `scripts/in-bundle lake build` on those modules under `Leanux.Proofs.WG`,
inspect logical declarations with `#print axioms`, and replay with
`scripts/in-bundle lake env leanchecker --fresh MODULE`. On this host use
`capped`, 32 Lean threads and 16 QEMU slots.

## Dispatch, initiation erasure and downstream wheel corrections

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Config quiet timers and separated drain frame | 8 | 1 | 3 | 0 | 4 | 0 | 8 |
| Progress.Dispatch | 4 | 4 | 0 | 0 | 0 | 0 | 4 |
| TimerDiscipline.RecordedJitterFrames | 1 | 1 | 0 | 0 | 0 | 0 | 1 |
| Initiation exit frames and consumption erasure | 2 | 2 | 0 | 0 | 0 | 2 | 4 |
| TimerDiscipline.RecordedSiteSource | 3 | 0 | 3 | 0 | 0 | 0 | 3 |
| This tranche | 18 | 8 | 6 | 0 | 4 | 2 | 20 |
| Cumulative processed baseline and checked support | 862 | 638 | 14 | 21 | 189 | 63 | 904 |

The census is 502 campaign-owned files, 1,873 theorems and 298 checked proof
modules; 969 baseline declarations await validation. Checked counts are H1 180,
H2 188, H3 99, H4 313, H5 74 and H6 50. H1's 22-headline terminal closure
remains current over b700659; H2–H6 terminal closures and the full gate remain
lagging. All 258 original terminal names/order remain, as do the wider charter
obligations. No new charter result is claimed.

QuietModel now clears both expiry and wheel entry for each selected timer,
retaining list order and repeated identifiers. Three pure QuietFrames lemmas
and the residence lemma retain their meaning; three total QuietTimers
contracts explicitly correct their complete Peer effects. Their original
resident/empty-clear-queue domains remain. The drain-empty frame moves to
QuietDrainFrames and preserves the complete actual product state through
liftWG, including fixture data and arbitrary other owners. Claims and frames
remain separate. Later quiet/live peer-removal totality is a separate pending
audit: the actual removal path includes an additional crypt-queue/NAPI guard.

Progress.Dispatch keeps the actual product scheduler, selected activation,
section-start read and intermediate-state witnesses. Its four contracts
preserve exact false/success behavior and unchanged complete product state
when no work exists. Receive work now observes PtrRing.empty, matching the
actual head slot rather than replacing it with an item-list/count predicate.
The scheduler priority order is unchanged.

The recorded-jitter bound retains its arbitrary predicate over WG, FS, Task
and Seccomp owners, actual Ambient lift, mode and numeric bound. Initiation
exit framing likewise retains arbitrary four-owner predicates; its native
companion describes the real exit, including a peerPut that may stop. Native
and Product consumption erasure use the actual native run and lift, preserve
every Stop and return only the peer identifier. They do not claim the
remaining transcript/fixture facts are carried. Those two original bodies
remain pending, with independent supplied lookup/beforeDh certificates in
scope.

RecordedSiteSource corrects three current timer effects. The projected
caller-entry contract retains the actual clock record, mode, resident peer
and guard premises. The two technical Product source witnesses retain the
complete original initial/final product and the actual caller-read state.
Their complete WG effects distinguish same expiry from changed expiry and
use the actual signed clock gap. No execution state is reconstructed from a
projection and no readiness premise is added.

Scoped builds pass 126 jobs for the first seventeen contracts and 65 jobs
for RecordedSiteSource, without warnings. Axiom inspection covers 515
logical roots in 97 modules, including 278 public theorem roots, and finds
only the three standard axioms. All five fresh replays pass. Independent review
of quiet cleanup and initiation erasure is clear; dispatch and timer-source
reviews are clear too. Static checks, whitespace and mirror/shared boundaries
pass.

Development ledger: quiet timers passed the first scratch probe. Dispatch
passed probe five after fixing polymorphic hidden-action annotations, nested
native/product reduction and match distribution; the first two drafts also
had unused simplification warnings. Recorded jitter passed probe four after
three local reduction failures (error/warning counts 2/0, 2/1 and 2/0).
Initiation erasure made three runs over two changed drafts: the first failed
with redundant steps and thirty unused simplifications; a cleanup edit then
failed its assertion, and an incorrectly batched command reran the unchanged
failing source. That second run was a process failure, not an infrastructure
retry or a pass. The third run followed an inspected successful edit and
passed cleanly. Subsequent edit and probe calls are separate. Recorded-site
probes one through three failed product-bind normalization (2/0, 2/9 and
1/0); four passed cleanly. Full output was saved before previews. No cap or
proof-limit increase, infrastructure retry or guest run occurred.

Reproduce with scripts/in-bundle lake build on Config.QuietTimers,
TimerDiscipline.RecordedJitterFrames, Progress.Dispatch,
Roaming.InitiationConsumeErasureSource and TimerDiscipline.RecordedSiteSource
under Leanux.Proofs.WG; inspect logical declarations with #print axioms and
replay with scripts/in-bundle lake env leanchecker --fresh MODULE. On this
host use capped, 32 Lean threads and 16 QEMU slots.

## Scheduler observations, response caller and removal-domain finding

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Scheduler turns, probe/stack frames and operational wrappers/bridge | 62 | 62 | 0 | 0 | 0 | 0 | 62 |
| TimerDiscipline.RecordedJitterSource | 3 | 1 | 2 | 0 | 0 | 0 | 3 |
| Config.QuietRemovalSource and QuietRemovalFindings | 1 | 0 | 1 | 0 | 0 | 1 | 2 |
| Roaming.ResponseCallSource and Product companions | 5 | 5 | 0 | 0 | 0 | 5 | 10 |
| TimerDiscipline.InitiationArmSource | 5 | 4 | 1 | 0 | 0 | 1 | 6 |
| This tranche | 76 | 72 | 4 | 0 | 0 | 7 | 83 |
| Cumulative processed baseline and checked support | 938 | 710 | 18 | 21 | 189 | 70 | 987 |

The tree has 508 campaign-owned files, 1,880 theorems and 314 checked proof
modules. Of the 1,831 baseline declarations, 893 await validation. Checked
counts are H1 180, H2 188, H3 109, H4 315, H5 136 and H6 59. The status
table above describes each result. H1's 22-headline terminal closure remains
current over b700659; H2–H6 terminal closures and the full proof gate remain
lagging. All 258 original terminal names/order remain. No new charter result
is claimed, and no additional frame is deleted.

The scheduler carry includes nine ScheduleTurn contracts (three probe/filter
preservation facts moved to ScheduleProbeFrames), seven PlaceholderTurn
contracts, six RecordedTurn contracts, the separate StackFrames contract,
six StackResume contracts, twenty-three SchedulerSourceClaims wrappers and
ten ObservationBridge contracts. The full actual Product state remains
quantified. Candidate order/multiplicity, arbitrary callback effects,
selected activation/start-read witnesses, post-NAPI peeks, detachment,
stack guards and exact Stops survive. Receive readiness uses the current
PtrRing.empty head-slot test. View and ObservationBridge use Product
snapshots with all eight original surviving fixture fields; foreignCreator
remains observed through WG routing. Guard/filter inversion uses proved
full-state preservation, not injectivity of a projection. The two historical
backlog wrappers stay unchanged and pending in SourceClaims.

Recorded jitter now specifies the complete current wheel effect under its
original recorded/running/alive/resident domains. It retains actual Product
caller-read and jitter-draw intermediate states and the bound from that same
draw. Initiation arming keeps the exact native factor, skipped and reached
branches, and actual Product execution. Its recorded effect starts at the
real post-prefix state, without assuming successful network transmission.
One private Product factor is added and included in the census; its axioms
are covered transitively. These three downstream effect corrections follow
the existing timer finding and do not drop new wheel state.

The response caller has five native contracts and five Product companions.
The Product load helper accepts an unrestricted Bool-to-product-action
continuation. Complete lookup, consumed and before-setter certificates retain
the actual entry fixture; only pure observations are extended, while the
actual native execution is lifted unchanged. Caller erasure is unconditional,
including non-response messages and all Stops. Response-kind factor and
transcript equalities retain their original kind hypothesis and the complete
endpoint/session/keepalive/statistics/timer/release suffix. The transcript is
the actual prefix outcome driving that suffix, not just an arbitrary observer
with a matching erased result.

The [removal finding](2026-10-17-proof-campaign-2-removal-carry.md) refutes
the old quiet/live totality domain with a resident dead peer, refcount 2,
empty key slots/work queues, positive device peer count, ClearReady and a
scheduled NAPI poll. The actual prefix clears keys/timers, then stops at the
crypt-work guard added in a7a5e1f. The exact message and actual diagnostic
site are retained; no error post-state or reachability is asserted. The
source factor is explicitly corrected in QuietRemovalSource. Four remaining
QuietRemoval contracts and broader LiveRemoval users stay pending. This is
statement lag after a known fail-closed guard, not a new mirror defect or a
request to change the mirror. The proof root now imports both this finding
and the previously checked queued-handshake finding; the latter root-import
omission is corrected without changing its proof.

The combined scoped build passes 148 jobs without warnings. Earlier scoped
packaging builds pass 88, 102, 52, 43 and 54 jobs. Axiom inspection covers
658 logical roots in 114 proof modules, including 362 public theorem roots,
with only the three standard axioms. All four fresh replays pass. Independent
reviews of scheduler, stack/observation scope, response caller, removal witness and timer effects
are clear. Static forbidden-token/import/root/default-target checks pass;
mirror and shared proof layers remain byte-identical to their registered
pins.

Development ledger: ScheduleTurn probes one and two failed local Ambient
read reduction (the first also reported five unused simplifications);
three passed with two warnings, four passed cleanly. PlaceholderTurn passed
with one duplicated simplification warning, then cleanly. RecordedTurn
passed with two warnings, then cleanly. Stack framing failed one local
match reduction, then passed cleanly. SchedulerSourceClaims packaged cleanly
on its first build; ObservationBridge passed its first scratch probe.
RecordedJitterSource failed three local reduction goals, then passed.
ResponseCall used four changed probes: two errors/twenty-three warnings;
native success with eleven warnings; a Product helper failure with three
redundant-step errors; then all ten clean. InitiationArmSource used four
changed probes: reserved identifier errors and two warnings; three Product
lift-join errors; unavailable tactic/residual goal; then all six clean.

The removal witness used ten changed probes. One failed syntax; two and
three hit the unchanged recursion limit; four inspected a larger residual;
five exposed an inaccessible private identifier and the same limit; six
failed a local bind equality; seven hit the same limit; eight reached the
concrete map/guard normalization; nine failed a composed ok-bind reduction
with warnings; ten passed cleanly by composing existing native contracts.
No recursion limit was raised. Truncated previews of four and eight were
followed by reading the complete saved remainder. No failure was a pass or
an infrastructure outcome. The separately attempted initiation transcript
facts made six changed failing probes and closed no additional theorem;
their independent supplied lookup/beforeDh certificate scope remains
pending. All outputs were saved before previews. No infrastructure retry,
unchanged-source rerun, cap/proof-limit increase or guest run occurred in
this tranche; the earlier unchanged rerun remains recorded in its own entry.

Reproduce with scripts/in-bundle lake build on Progress.ObservationBridge,
TimerDiscipline.InitiationArmSource, Config.QuietRemovalFindings and
Roaming.ResponseCallProductSource under Leanux.Proofs.WG. Inspect logical
declarations with #print axioms and replay each root using scripts/in-bundle
lake env leanchecker --fresh MODULE. On this host use capped, 32 Lean
threads and 16 QEMU slots.

## Initiation frames, timer prefixes and projected peer-release claims

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| TimerDiscipline.ArmingPrefixesSource | 7 | 4 | 3 | 0 | 0 | 1 | 8 |
| TimerDiscipline.InitiationFrames | 2 | 2 | 0 | 0 | 0 | 0 | 2 |
| QuietRemovalFrames and QuietRemovalLeaves | 2 | 1 | 0 | 0 | 1 | 0 | 2 |
| Index.PeerReleaseClaims companions | 0 | 0 | 0 | 0 | 0 | 2 | 2 |
| This tranche | 11 | 7 | 3 | 0 | 1 | 3 | 14 |
| Cumulative processed baseline and checked support | 949 | 717 | 21 | 21 | 190 | 73 | 1,001 |

The census is 512 campaign-owned files, 1,883 theorems and 320 checked proof
modules; 882 baseline declarations await validation. Checked counts are H1
180, H2 190, H3 109, H4 317, H5 136 and H6 69. H1's terminal module remains
current; H2–H6 and the full gate remain lagging. All 258 terminal names/order
remain, and no new charter result is claimed.

ArmingPrefixesSource carries two native source factors and two total Product
prefix contracts on their original premises. Three recorded-arm predictions
are explicitly corrected to the complete wheel effect, anchored at the actual
prefix successor where applicable; actual caller/jitter Product states remain.
One private lift-bind variant follows campaign 1's composition shape and is
counted as added support. No frame is deleted.

InitiationFrames retains two substantive within-WG preservation claims.
Their native runs quantify arbitrary Ambient inputs and preserve the original
initiation view through actual branch/crypto/index behavior, including missing
identity, crypto failure and NULL peer-word failure paths. No residency or
successful-index premise is added. Existing generic component/crypto contracts
are reused; no shared-layer copy or edit is made. The arbitrary-world callback
scope of other generic send-frame contracts is not settled by these two
native-operation carries.

The unchanged pure cleanup-residency lemma moves to QuietRemovalFrames.
QuietRemovalLeaves carries the native total counter decrement under the same
positive-count premise. The two broader removal contracts remain pending at
this checkpoint; neither receives an additional crypt/NAPI readiness premise.

PeerReleaseClaims supplies two new checked projected companions for the
original table/peer/drop-accounting/uniqueness and allocation-bound headlines.
Both keep the old resident/live and invariant premises, classify the exact
queue-first/timer-second refusal, and retain every original success conjunct.
PeerReleaseOutcomeModel contains only that pure refusal selector. No
post-error state or whole-driver reference safety is asserted. The two
Statements wrappers now have the corrected outcome signatures and delegate
to these companions; their enclosing module remains lagging. The companions
are counted as added support here, not as two additional validated baseline
headlines. Independent review requested that their old unconditional docstrings
be qualified; both companion and wrapper descriptions now state refusal or
normal-return effects explicitly.

Scoped build passes 138 jobs without warnings. Axiom inspection covers 531
logical roots in 110 proof modules, including 319 public theorem roots, with
only the three standard axioms. Fresh kernel replay passes for all four scoped
roots. Static token/import/root/default-target checks
pass and all terminal names/order are intact. Root reviews of timer/cleanup
carries and independent peer-release/prefix classification review are clear.

Development ledger: ArmingPrefixesSource failed its first changed probe on
a native Bool normalization with one unused simplification warning; the second
passed cleanly. InitiationFrames, the two cleanup leaves and PeerReleaseClaims
each passed their first probe. Broader removal-outcome and initiation transcript
packages remain outside this checked surface and its census. No unchanged-source rerun, infrastructure retry, cap/proof-limit increase or
guest run occurred.

Reproduce with scripts/in-bundle lake build on TimerDiscipline.ArmingPrefixesSource,
TimerDiscipline.InitiationFrames, Config.QuietRemovalLeaves and
Index.PeerReleaseClaims under Leanux.Proofs.WG, followed by #print axioms and
scripts/in-bundle lake env leanchecker --fresh MODULE for each root.
Use capped, 32 Lean threads and 16 QEMU slots on this host.

## Quiet removal outcomes and the loopback send frame

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Config.QuietRemoval | 2 | 0 | 2 | 0 | 0 | 4 | 6 |
| TimerDiscipline.SendCutFrames | 1 | 1 | 0 | 0 | 0 | 1 | 2 |
| This tranche | 3 | 1 | 2 | 0 | 0 | 5 | 8 |
| Cumulative processed baseline and checked support | 952 | 718 | 23 | 21 | 190 | 78 | 1,009 |

The census is 513 campaign-owned files, 1,888 theorems and 323 checked proof
modules; 879 baseline declarations await validation. Checked counts are H1
180, H2 190, H3 109, H4 323, H5 136 and H6 71. H1's terminal closure remains
current; H2–H6 and the full gate remain lagging. No new charter result is
claimed.

Both quiet removal contracts now classify exact projected outcomes on all
their original resident/live/count/empty-slot/empty-work-queue premises.
The actual crypt/NAPI guard can refuse after cleanup; otherwise the exact
final-reference queue/timer guard may refuse or the original successful
Device effect holds. The outer contract retains its original RemovalEffect
premise. Neither gains a readiness assumption or invents a post-error state.
The constant crypt diagnostic site follows the actual three empty-slot
release decisions, rather than an arbitrary reconstructed log.

QuietRemovalOutcomeModel is the pure outcome selector. QuietRemoval contains
the two projected claims and four private exact-execution prefix helpers;
these helpers carry complete native WG/Ambient runs and are not preservation
frames. The two earlier leaves stay in QuietRemovalLeaves/QuietRemovalFrames.
This corrects known statement lag documented by the removal counterexample.

SendCutFrames retains the original arbitrary joint predicate over all four
former Kernel owners and adds a native companion over all WGWorld fields.
The actual raise/clear sequence restores netRxRaised on normal return, so
this is a substantive frame, not a deletion justified by the split type.
The proof keeps absent-device, pending-NAPI and malformed-record failures
partial, with no new readiness premise. Its obsolete FireSelectionSource
dependency is removed; the already-carried InitiationFrames dependency remains
for downstream users. Independent review found no scope or execution mismatch.
No shared layer or mirror source is changed.

Scoped build passes 137 jobs without warnings. Axiom inspection covers 517
logical roots in 109 proof modules, including 307 public theorem roots,
using only the three standard axioms. Fresh kernel replay passes both roots.
Static token/import/root/default-target checks pass; all 258 original terminal
names/order remain intact. Mirror and shared-layer boundary checks are clear.

Development ledger: quiet-removal probe 1 (the two earlier leaves) passed.
Probe 2 failed native full-state equality with an unused simplification;
probe 3 exposed an incorrectly supplied intermediate peer. Probe 4 closed
the four prefix helpers. Probe 5 failed log/run reductions and the unchanged
default heartbeat bound; probe 6 retained a redundant step and that heartbeat
failure. Probe 7 failed cleanup/drain/outer-branch normalization with two
warnings; probe 8 failed only an internal matcher join, without warnings.
Probe 9 closed after-death outcomes by ordinary case analysis of the exact
refusal expression, and probe 10 closed the outer contract. All passing probes
were warning-free. Probes 3, 5 and 7 had bounded previews; complete saved
outputs were inspected before subsequent edits. No private matcher name or
increased proof limit is used. These probes are distinct from the ten
earlier counterexample probes already reported.

SendCutFrames probes 1–3 each failed one definitional join; probe 4 failed
two branch-normalization joins and had one unused simplification warning.
Probe 5 passed cleanly. No unchanged-source rerun, infrastructure retry,
cap increase, dependency rebuild during fresh replay or guest run occurred.

Reproduce with scripts/in-bundle lake build on Config.QuietRemoval and
TimerDiscipline.SendCutFrames under Leanux.Proofs.WG, then inspect logical
declarations using #print axioms and replay each root with scripts/in-bundle
lake env leanchecker --fresh MODULE. Use capped, 32 Lean threads and 16 QEMU
slots on this host.


## Send-state adapters, live-removal source outcomes and response-caller facts

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| TimerDiscipline.SendPeerFrames | 25 | 25 | 0 | 0 | 0 | 2 | 27 |
| Config.LiveRemovalFrames | 4 | 0 | 0 | 0 | 4 | 0 | 4 |
| Config.LiveRemovalSource | 3 | 0 | 3 | 0 | 0 | 0 | 3 |
| Roaming.ResponseCallClaims and Product companions | 3 | 3 | 0 | 0 | 0 | 3 | 6 |
| This tranche | 35 | 28 | 3 | 0 | 4 | 5 | 40 |
| Cumulative processed baseline and checked support | 987 | 746 | 26 | 21 | 194 | 83 | 1,049 |

The census is 514 campaign-owned files, 1,893 theorems and 329 checked proof
modules; 844 baseline declarations await validation. Checked counts are H1
180, H2 190, H3 115, H4 330, H5 136 and H6 98. H1's terminal closure remains
current; H2–H6 and the full gate remain lagging. This tranche carries existing
obligations; it claims no new charter result.

SendPeerFrames retains all five higher-order adapters over arbitrary Product
actions. Two separately named native adapters support the concrete WG actions;
they do not restrict the original callback domain. Cache/access/tunnel frames
keep optional-device/peer domains, normal-return failures and the one total
getPeer contract. Send, table/cursor, initiation, work-queue and pending views
are unchanged. Their equalities use the actual WG/Ambient observations.
The transmit proof respects routing-back rejection and the original
loopback, statistics, socket-read and sent-output sequence. These substantive
preservation claims stay in the frame file; no frame is deleted.
Independent review compared all original statements and current source and
found no scope or behavior mismatch.

LiveRemovalFrames retains four pure cleanup/keypair preservation facts.
LiveRemovalModel still specifies only successful effects; its comments now
make the guard distinction explicit. LiveRemovalSource corrects three false
totality claims. The local post-clear sequence retains its exact original
action and classifies release refusal or its original success effect. The
two complete source contracts additionally witness actual dead-guard,
keypair-clear and timer-stop executions; the outer one also witnesses actual
peerMakeDead after its null guard. Those witnesses determine the crypt-work
diagnostic site from the real Ambient decision log. The original ClearReady,
resident/live/count, empty-work-queue and RemovalEffect premises are retained,
as are successful LiveRemovalEffect conclusions. No readiness premise or
post-error state is invented. Terminal projected wrappers still need to
observe those actual prefixes; an arbitrary existential error site would
not preserve the claim.

ResponseCallClaims carries the three native packet-prefix, caller-prefix and
full-observer facts. The accepted MAC cases come from actual proceeding
branches, and the setter boundary is the actual read after the no-peer
decision. Device equality to committed state permits the intervening log
step without claiming an unchanged whole snapshot. ResponseCallProductClaims
adds three complete Product companions: every one of the eight fixture
observations is captured from the actual entry, preserved by liftWG and
restored into lookup/commit/caller certificates. Full beforeSetter snapshot
equality and lookup outcome equality remain full equalities. The two pure
Product predicates live in ResponseCallProductModel. Independent native and
Product reviews found no issue. Terminal wrappers still need to select the
Product operations/facts when carried.

Scoped builds pass 85 jobs for the send module, 153 for initial combined
packaging, and 158 for the final Product closure, without warnings. Axiom
inspection covers 681 logical roots in 129 proof modules, including 388
public theorem roots, with only the three standard axioms. Fresh kernel replay
passes all three roots. Static token/import/root/default-target checks and all
258 original terminal names/order pass; mirror/shared-layer boundaries are clear.

Development ledger: SendPeerFrames probe 1 failed four local elaboration/source
joins; probe 2 failed four record-layout diagnostics; probe 3 failed one
if/bind join; probe 4 passed cleanly. All four were warning-free.
LiveRemoval probe 1 failed a drain alias join and two unused simplifications;
probe 2 closed the local continuation. Probe 3 failed an extra reflexivity
step, reverse unfolding and bind normalization, with one unused simplification.
Probe 4 elaborated but had four warnings; probe 5 closed after-death source
outcomes cleanly and probe 6 closed all three contracts cleanly.

Response-call native probes 1 and 2 failed eight branch reductions, with
thirteen and eight unused simplification warnings respectively. Probe 3
reduced the source with exact local run equations but retained eight MAC
branch goals; probe 4 reduced those to three execution cases. Probe 5 failed
record layout/dotted notation; probe 6 failed dependent equality elimination;
probe 7 failed a nested product projection. Probe 8 closed the packet fact,
and probe 9 closed all three native facts, both warning-free. Complete outputs
were saved before bounded previews; all diagnostic headings and remaining
goals were inspected before subsequent edits. The Product companions passed
their first probe without warnings.

The separate initiation-consume attempt remains outside this census.
Its additional probes 7–12 failed respectively on normalization, kernel
recursion, auxiliary-extraction recursion, helper simplification/layout,
ambiguous ordering constructors and kernel recursion. In particular, closing
elaboration goals at probes 8 and 12 did not pass kernel checking. No proof
limit was raised. A subsequent mechanical prefix/tail split remains pending.
No unchanged-source rerun, infrastructure retry, cap increase or guest run
occurred in this tranche.

Reproduce with scripts/in-bundle lake build on TimerDiscipline.SendPeerFrames,
Config.LiveRemovalSource and Roaming.ResponseCallProductClaims under
Leanux.Proofs.WG, then #print axioms for logical declarations and
scripts/in-bundle lake env leanchecker --fresh MODULE for each root.
Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Response audits, normal removal effects and IPv4/IPv6 send frames

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Roaming.ResponseAuditClaims | 2 | 2 | 0 | 0 | 0 | 2 | 4 |
| Config.RemoveFlagEffects | 2 | 0 | 0 | 0 | 2 | 0 | 2 |
| Config.CollisionFrames/CollisionRemovalSource/RemoveFlagSource | 6 | 6 | 0 | 0 | 0 | 0 | 6 |
| Index.PeerReleaseTableFrames | 1 | 1 | 0 | 0 | 0 | 0 | 1 |
| TimerDiscipline.SendSocketFrames | 6 | 6 | 0 | 0 | 0 | 1 | 7 |
| This tranche | 17 | 15 | 0 | 0 | 2 | 3 | 20 |
| Cumulative processed baseline and checked support | 1,004 | 761 | 26 | 21 | 196 | 86 | 1,069 |

The census is 517 campaign-owned files, 1,896 theorems and 338 checked proof
modules; 827 baseline declarations await validation. Checked counts are H1
180, H2 191, H3 119, H4 338, H5 136 and H6 105. H1's terminal module remains
current; H2–H6 and the full gate remain lagging. No new charter result is claimed.

ResponseAuditClaims separates the two existing response audits from the
pending initiation audit. It retains their native exact-inspection meanings
and adds the two Product companions using the checked generic Product audit.
The actual prefix outcome is retained even when the suffix fails; inspection
preserves the actual entry and error outcomes have no final state. Full fixture
observations remain in the Product certificate. HandshakeAuditClaims imports
this response closure and retains its pending initiation declarations.

The remove-flag source contracts were partial originally. Their original
premises, lookup acquisition, two ordered releases, return code and successful
effect remain; this is a retype, not another totality correction. The actual
crypt/final-release refusals are eliminated only against a supplied successful
run. CollisionFrames retains the substantive native dead-guard frame, while
the two removal converses and three remove-flag claims remain in their source
files. Two pure residency/count effects are unchanged.

An attempted build of RemoveFlagEffects failed through CollisionModel's
unnecessary KeyInstallEffects import, which reached the known stale
QueuedHandshake proofs. The full output was retained and inspected, including
its queued-state type/source errors and two unused simplifications. Only
CollisionKeyEffect needs that installation layer. CollisionRemovalModel now
holds the two unchanged pure lookup/removal definitions; CollisionModel
imports it and retains the key-installation definition. RemoveFlagModel and
CollisionFrames import the smaller removal model. This is dependency factoring,
not a repaired or copied installation layer. The resulting 96-job scoped
build passed without warnings.

PeerReleaseTableFrames moves the original peerPut table-safety contract out
of the pending send-source composition. Its proof retains arbitrary optional
peers/states and all normal-return paths, deriving positive refcount from the
actual run rather than assuming it. Exact release outcomes then preserve
numeric uniqueness, owner uniqueness and keypair allocation bounds together.
The frame asserts no completion of refused releases.

SendSocketFrames carries all six concrete socket-send frames, preserving
arbitrary endpoints/bytes/DS/exactRx inputs and optional view predicates.
IPv4 source/interface retry, route errors, cache writes, IPv6 source reset
and both transmit branches follow actual source composition. One private
hoare_liftRouting_variant follows campaign 1's Framing/Lift shape: the
actual adapter supplies WG interface facts and writes back routing only.
Its arbitrary WG predicate has the explicit routing-stability premise.
This minimal variant is pending campaign 1's shared retyped layer; no FIB
proof layer is copied. Independent review of statements, source and the
campaign 1 counterpart found no issue. No frame is deleted.

Further scoped packaging passes 143 jobs and the final four-root build passes
184 jobs, both without warnings. Axiom inspection covers 778 logical roots
in 154 proof modules, including 467 public theorem roots, using only the three
standard axioms. All four fresh kernel replays pass. Static token/import/root/
default-target checks pass, all 258 original terminal names/order remain intact,
and mirror/shared-layer boundary checks are clear.

Development ledger: ResponseAuditClaims passed its first probe.
PeerReleaseTableFrames probe 1 failed one unreduced outcome-map contradiction;
probe 2 passed without warnings. RemoveFlag probes 1–6 were: multiline do
syntax failure; clean frame/first-converse closure; stale imported-environment
collision; untyped branch/deprecated-tactic/simplification failure; continuation
indentation failure; clean closure of all six declarations. The stale-import
failure was followed by the source dependency factoring and rebuild described
above, not an unchanged retry. The final files use the default heartbeat bound.

Socket-frame probes 1–2 failed composition; probe 3 also used an unavailable
tactic; probes 4–6 failed cache matcher joins; probe 7 reached route-match and
endpoint-clear joins; probe 8 introduced indentation errors. Probe 9 closed
all six contracts, and probe 10 passed after removing unused match helpers.
All ten were warning-free and only the final two passed. Existing limits were
retained. Complete outputs were saved before previews. No cap increase,
unchanged-source rerun, infrastructure retry or guest run occurred.
Initiation-consume facts remain outside the census and under further factoring.

Reproduce with scripts/in-bundle lake build on Roaming.ResponseAuditClaims,
Config.RemoveFlagSource, Index.PeerReleaseTableFrames and
TimerDiscipline.SendSocketFrames under Leanux.Proofs.WG, then #print axioms
for logical declarations and scripts/in-bundle lake env leanchecker --fresh
MODULE for each root. Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Send preservation, queued inspection and the corrected backlog fixture

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| TimerDiscipline.SendBufferFrame | 5 | 5 | 0 | 0 | 0 | 0 | 5 |
| Index.SendFrames/SendSource | 7 | 7 | 0 | 0 | 0 | 3 | 10 |
| Config.QueuedHandshake | 5 | 1 | 4 | 0 | 0 | 2 | 7 |
| Progress.BatchBacklogAcceptance | 1 | 0 | 1 | 0 | 0 | 2 | 3 |
| This tranche | 18 | 13 | 5 | 0 | 0 | 7 | 25 |
| Cumulative processed baseline and checked support | 1,022 | 774 | 31 | 21 | 196 | 93 | 1,094 |

The census is 519 campaign-owned files, 1,903 theorems and 344 checked proof
modules; 809 baseline declarations await validation. Counts by result are H1
180, H2 201, H3 119, H4 345, H5 139 and H6 110. H1 retains its checked terminal
closure; H2–H6 and the full gate remain lagging. No new charter result is claimed.

SendBufferFrame retains all five original observations and their arbitrary
optional device/peer domains. It follows allocation, IPv4/IPv6 socket sending
and the actual transmit-byte update. Index.SendFrames retains the five
table-safety contracts; three private supports compose the actual clock,
guard and arming effects. Residency comes from a successful actual guard.
Timer wheel changes are projected through the table cursor, not claimed absent.
Index.SendSource carries initiation and send-worker table safety on their
original normal-return domains, including actual expiry, cryptographic,
timer, socket and release operations. There are no new readiness premises.
Independent review of both frame files found no issue. All frames remain
substantive within WGWorld; none is deleted.

[AGENT 2026-10-17] The queued-send correction observes the actual queue-record
inspection and carries that result into the predicted Device. Decorated
suffix/full-call operations have exact erasure equalities, including failure
outcomes, so their claims refer to executions of the actual mirror rather
than a reconstructed state or a different schedule.

QueuedHandshake now carries all five original declarations: the read prefix
is retyped, while the factor and three effects explicitly correct the old
source/prediction. Resident-peer scope remains unchanged. Successful peerGet
supplies the positivity needed for the retained release, rather than a new
precondition. Two new erasure theorems connect the observations to the actual
operation; full-call witnesses preserve the actual clock, intermediate states
and final state. The old pure queuedDevice remains labelled historical for
unported callers. The existing checked counterexample remains valid.
Downstream key-install/staged-send contracts and terminal wrappers are pending.
Independent review found no correctness issue in the queued or backlog carries;
its stale queued-finding status note was fixed in that report before commit.

BatchBacklogModel contains the unchanged trace fixture. BatchBacklogAcceptance
checks accepted=false and the exact actual executeTrace error: operation 1
stops at the WireGuard queueing boundary because pending work would outlive
the guest wait. This is the landed completion guard addressing the historical
finding, not a new mirror defect. The exact error is recovered from a
kernel-checked observable projection, without needing DecidableEq on Json or
Stop. The legacy hand-initialized runTwo/backlog code remains pending in
BatchBacklog: it omits the runner's current FIB boot and is not used to prove
the current rejection. Historical accepted-boundary wrappers are still lagging;
the previous result remains attributed to its old mirror commit.

Scoped builds pass 87 jobs for SendBufferFrame, 97 for Index.SendFrames,
69 for QueuedHandshake, 163 for the combined acceptance closure and 134 for
Index.SendSource. New proof files have no warnings. The acceptance closure
replays an inherited Env.lean:865 String.mk deprecation warning; the mirror
is frozen by the charter, so this warning is reported and neither suppressed
nor repaired in this proof branch. Axiom inspection covers 683 logical roots
in 136 proof modules, including 411 public theorem roots, using only the
three standard axioms. Fresh kernel replay passes on Index.SendSource,
QueuedHandshake and BatchBacklogAcceptance. Static token/import/root/default
checks pass, all 258 original terminal names/order remain intact, and the
mirror/shared-layer boundary checks are clear.

Development ledger: SendBufferFrame probe 1 failed six branch/lift inference
goals and probe 2 passed cleanly. Index.SendFrames and SendSource each passed
their first probe without warnings. Queued probes 1–6 were: return-witness
shape failure; record-layout failure; clean two-leaf closure; redundant
function-extensionality step; incomplete erasure proof; clean leaf/erasure
closure. Probe 7 lacked the explicit projection-bridge import; probe 8
closed the corrected suffix; probe 9 referenced names eliminated by equality
substitution; probe 10 closed all five declarations and both erasures.
The final queued proofs use the default heartbeat limit.

The backlog discovery evaluated the actual runner, then three changed proof
probes were checked: probe 1 failed to synthesize equality decidability for
the whole result, probe 2 failed reflexivity, and probe 3 proved the exact
error via its observable projection. The accepted=false theorem passed in
each proof probe; only probe 3 closed the complete candidate. No evaluation
alone is counted as proof. Complete outputs were saved and inspected.
No unchanged-source rerun, infrastructure retry, limit increase or guest run
occurred in this tranche.

Initiation-consume facts remain outside the census. Additional probes 13–18
failed respectively on a reserved binder, a non-definitional source/bind join,
conditional-bind normalization plus recursion, helper application plus kernel
recursion, the same recursion after explicit continuation factoring, and
kernel recursion after the local precheck equation removed elaboration
recursion. These are failures; closed elaboration is not kernel acceptance.
The next attempt names that precheck equation separately. Limits are unchanged.

Reproduce with scripts/in-bundle lake build on Index.SendSource,
Config.QueuedHandshake and Progress.BatchBacklogAcceptance under
Leanux.Proofs.WG, then #print axioms for logical declarations and
scripts/in-bundle lake env leanchecker --fresh MODULE for each root.
Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Consumer table safety, initiation views and staged fallback

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Index.ConsumeFrames/ResponseFrames/ConsumeSource | 10 | 10 | 0 | 0 | 0 | 0 | 10 |
| TimerDiscipline.InitiationPreservationFrames | 4 | 4 | 0 | 0 | 0 | 0 | 4 |
| Config.StagedSource/StagedFallbackSource | 2 | 1 | 1 | 0 | 0 | 1 | 3 |
| This tranche | 16 | 15 | 1 | 0 | 0 | 1 | 17 |
| Cumulative processed baseline and checked support | 1,038 | 789 | 32 | 21 | 196 | 94 | 1,111 |

The census is 520 campaign-owned files, 1,904 theorems and 350 checked proof
modules; 793 baseline declarations await validation. Counts are H1 180, H2 211,
H3 119, H4 348, H5 139 and H6 114. H1 retains its checked terminal closure;
H2–H6 and the full gate remain lagging. No new charter result is claimed.

ConsumeFrames retains arbitrary optional devices/cursors, complete LookupState
values, kind masks, numeric indices, public keys and Ambient inputs. It follows
the actual owner-word read, possibly-zero acquisition and owner-word store,
including NULL/dead storebacks and owner/peer aliases. The cursor frames only
the table and keypair allocation bound. ConsumeSource composes initiation,
response and cookie consumers on their original table-safety-only partial
domains: every early return, missing-owner case, cryptographic helper, clock
read, peer update and failure-side release remains. Success of a release is
never assumed. ResponseFrames carries the session-derived timer table frame.

InitiationPreservationFrames retains the four original selected-view frames.
Traversal and keepalive deletion use current timer/wheel effects; these writes
leave the specific InitiationView unchanged. The final retransmit hook frames
WorkerView, whose fields exclude timers. Residency comes from the original
some-view premise. Off, recorded same-expiry, changed-expiry, missing-caller and
record failures remain covered, and prefix composition uses the actual send
operation. These are substantive within-WireGuard frames, so none is deleted.

StagedSource's operational factors are retyped without changing their control
flow. Its unused KeyReferences import is narrowed to checked QueuedHandshake.
StagedFallbackSource carries the corrected fallback effect over the projection,
indexed by the actual clock and inspection bit. Its erasure is unconditional
over invalid/keypair arguments, including every error. The original arbitrary
partial keypairPut Device contract and after-put residency remain the only
premises. Packet restoration preserves order before attempt reset and the
actual queued-send observation. StagedFallback retains the historical pure
predictor and two pending downstream callers; no caller is silently removed.

Independent reviews of the six lookup frames, two previously carried send
compositions, three consumer contracts, four timer frames and staged-fallback
candidate found no correctness issues. Scoped builds pass 105 jobs for the
lookup frames, 129 for staged fallback/session timer, 88 for initiation frames
and 138 for consumers, without warnings. Axiom inspection covers 698 logical
roots in 141 proof modules, including 427 public theorem roots, using only the
three standard axioms. All four fresh kernel replays pass: ConsumeSource,
ResponseFrames, StagedFallbackSource and InitiationPreservationFrames.
Static token/import/root/default checks pass, all 258 terminal names/order
remain, and mirror/shared-layer boundaries are clear.

Development ledger: ConsumeFrames probe 1 elaborated with one unused
simplification warning; probe 2 passed after removing it. The first combined
consumer proof attempt failed all three declarations at the existing heartbeat
bound. Explicit source composition then closed cookie in probe 2, response
and cookie in probe 3, and all three in probe 4. Probe 5 removed unused local
supports and a duplicated source expression, and passed cleanly. No bound was
raised. ResponseFrames passed its first scoped build. Initiation-preservation
probes 1–2 failed projection/inference and wheel simplification respectively;
probe 3 passed without warnings.

Staged-fallback probes 1–5 failed on: erasure timeout/missing native annotation
and one warning; control-flow erasure/projection inference and two warnings;
a misplaced local predicate; native put-post annotation and one warning;
and a Unit/PUnit mismatch in the actual orphan loop. Probe 6 passed at the
default heartbeat bound with no warnings. Probe 1's shell wrapper also used
zsh's readonly status variable; the Lean log was preserved and read, and the
wrapper was corrected to use a task-specific variable. Complete outputs were
saved before inspection. No failure was treated as success, and no unchanged
rerun, infrastructure retry, cap increase or guest run occurred.

The initiation-consume transcript facts remain outside the census. Probe 19
failed kernel recursion in the extracted precheck and the original finish
fact. Probe 20 closed the named precheck with targeted bind/run equations but
the original fact still failed kernel recursion. Further continuation factoring
is pending; no proof limit changed.

Reproduce with scripts/in-bundle lake build on Index.ConsumeSource,
Index.ResponseFrames, Config.StagedFallbackSource and
TimerDiscipline.InitiationPreservationFrames under Leanux.Proofs.WG, then
#print axioms and scripts/in-bundle lake env leanchecker --fresh MODULE for
each root. Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Response sending, worker references and keypair references

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Index.ResponseSource | 1 | 1 | 0 | 0 | 0 | 0 | 1 |
| TimerDiscipline.SendWorkerFrame/SendWorkerSource | 4 | 4 | 0 | 0 | 0 | 0 | 4 |
| Config.KeyReferences | 5 | 4 | 0 | 0 | 1 | 0 | 5 |
| This tranche | 10 | 9 | 0 | 0 | 1 | 0 | 10 |
| Cumulative processed baseline and checked support | 1,048 | 798 | 32 | 21 | 197 | 94 | 1,121 |

The census remains 520 campaign-owned files and 1,904 theorems, with 354 checked
proof modules; 783 baseline declarations await validation. Counts are H1 180,
H2 212, H3 119, H4 353, H5 139 and H6 118. H1's terminal closure is current;
H2–H6 and the full gate remain lagging. No new charter result is claimed.

ResponseSource preserves table safety through the actual create/session/send
sequence, including false creation/session branches and both last-send clock
writes. It assumes neither authentication nor successful network transmission.
SendWorkerFrame retains the exact internal-id/attempt-count/reference-count
WorkerView, deriving its finer prefix view from the actual resident peer.
SendWorkerSource composes the actual initiation with release on the same run;
its pre-existing reference-count-greater-than-one premise rules out final
release refusal. Queue, timer and all other peer fields remain arbitrary.

KeyReferences keeps its total/partial distinctions. The present-key get is
partial under residency alone: zero returns none, a successful positive get
increments, and overflow is excluded only by the supplied successful run.
Retained keypairPut remains total with its original resident and greater-than-one
premises, including NULL, nonresident and otherwise arbitrary peer words.
With immediate unreference disabled and a nonfinal decrement, neither index
removal nor peer dereference executes. Null get/put remain total. The pure
round-trip lookup theorem and exact ordered Device writes are unchanged.

Independent reviews of all ten declarations found no issues. The scoped build
passes 169 jobs without warnings. Axiom inspection covers 690 logical roots in
140 proof modules, including 423 public theorem roots, with only standard
axioms. All three fresh replays pass (ResponseSource, SendWorkerSource and
KeyReferences). Static checks, all 258 terminal names/order, and mirror/shared
boundaries pass.

ResponseSource passed its first probe. Worker probe 1 failed a reserved local
identifier and reported a deprecated rewrite; probe 2 fixed both and passed
cleanly. Key-reference probe 1 failed concrete Step equality for the zero/one
tests and reported two unused simplifications; probe 2 derived the Boolean
test equalities and removed unused arguments, then passed. Complete outputs
were retained and inspected. No unchanged rerun, infrastructure retry, limit
increase or guest run occurred.

The independent initiation-facts effort remains outside the count. Probe 21
accepted its four named helpers but the original fact still failed kernel
recursion. Probe 22 exposed an incorrectly inferred entry Ambient at the
post-guard continuation and still failed recursion in its new guard helper;
the next attempt supplies the actual post-guard Ambient explicitly while
retaining the original before-checks snapshot. No scope or proof limit changed.

Reproduce with scripts/in-bundle lake build on Index.ResponseSource,
TimerDiscipline.SendWorkerSource and Config.KeyReferences under Leanux.Proofs.WG,
then #print axioms and scripts/in-bundle lake env leanchecker --fresh MODULE
for each root. Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Retry observations, staged callers and base flush preservation

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| TimerDiscipline.RetryBaseSource | 3 | 1 | 2 | 0 | 0 | 1 | 4 |
| Config.StagedFallback | 2 | 0 | 2 | 0 | 0 | 2 | 4 |
| Progress.FlushBaseFrames and old index-only frame | 5 | 4 | 0 | 1 | 0 | 0 | 4 |
| Progress.FlushQueueEffects | 2 | 0 | 0 | 0 | 2 | 0 | 2 |
| This tranche | 12 | 5 | 4 | 1 | 2 | 3 | 14 |
| Cumulative processed baseline and checked support | 1,060 | 803 | 36 | 22 | 199 | 97 | 1,135 |

The census is 522 campaign-owned files, 1,906 theorems and 359 checked proof
modules; 771 baseline declarations await validation. Counts are H1 180, H2 212,
H3 119, H4 357, H5 145 and H6 122. H1's terminal closure remains current;
H2–H6 and the full gate remain lagging. No new charter result is claimed.

RetryBaseSource retains the total resident-peer read prefix without resetting
attempts. Its factor and exact effect explicitly correct the old queued suffix:
the actual clock and optional inspection bit determine the post-state, with
resident-only partial scope and an unconditional observer-erasure equality,
including errors. Legacy downstream consumers of queuedDevice remain pending.

StagedFallback carries its absent-key and invalid-key callers over projected
observations. The absent-key observer erases unconditionally. The invalid-key
observer performs the actual key read and invalid decision; exact run erasure,
including every error, is stated on the original resident/invalid-key domain.
It asserts no equivalence on valid-key states. Both contracts preserve their
original premises, including the retained-count premise only where previously
present, and the ordered keypair decrement, packet restoration, attempt reset
and actual clock/peek effect. The historical fallbackDevice remains for pending
StagedInvalid/key-peer consumers. No valid-key/nonce proof layer is copied.

FlushBaseFrames separates four carried within-WireGuard frames: peer release,
handshake clearing, keypair clearing and the queued clear worker. They preserve
both original work queues on all original normal-return paths, including final
peer deletion and keypair aliases, with no new readiness premises. The
clear sequence uses the actual ordered ClearRun; failed release/lookup guards
remain actual errors. FlushQueueEffects extracts two unchanged pure queue-count
decrease equalities. The two send-dependent frames remain in FlushQueueFrames.

The deleted indexRemove_flushQueues frame is provided by the narrowed type:
indexRemove is IndexM Unit, with state List IndexEntry over AmbientM. Neither
layer can access Device.sendWorkQueue or clearWorkQueue. The generic liftIndex
adapter retains its real getDev guard and writes back only indexTable; the
handshake-clear caller explicitly discharges queue stability through the
already-checked hoare_liftIndex_variant. The peer-release caller uses its exact
guarded outcome contract. Repository search found no other callers of the
deleted frame. This deletion is justified by the accessible state fields,
not by a failed compile. No shared-layer lemma was edited.

Independent reviews of both corrected caller groups and all four flush frames
found no issues; the flush review also confirmed the deletion and its replaced
caller obligations. Scoped builds pass 78 jobs for retry/staged callers and
103 for the flush closure, without warnings. Axiom inspection covers 526
logical roots in 95 proof modules, including 297 public theorem roots, with
only the three standard axioms. All four fresh kernel replays pass.
Static token/import/root/default checks, all 258 terminal names/order, and
mirror/shared boundaries pass.

Retry probe 1 eliminated the wrong peer variable while unpacking a return
witness; probe 2 named the equality and substituted the returned value, then
passed. Staged-caller probe 1 inferred the entry Ambient at the post-branch
continuation; explicitly reducing the projected Device precondition fixed that
inference, and probe 2 passed. Flush-base frames passed their first probe, and
the unchanged pure count equalities passed their first scoped build. Complete
outputs were saved and inspected. No warning suppression, unchanged rerun,
infrastructure retry, limit increase or guest run occurred.

Initiation transcript facts remain outside the census. Probe 23 closed
elaboration without warnings but failed kernel recursion in the new guard
contract; the original final fact had become a small composition and was no
longer the reported failure site. Probe 24 passed after targeted bind/run
rewrites, with the native finish contract and five private support lemmas
accepted at unchanged limits. Independent review found no native scope or
behavior issue. The whole-consumer and full Product companions remain pending,
so the incomplete original carry remains outside this census.

Reproduce with scripts/in-bundle lake build on Config.StagedFallback,
TimerDiscipline.RetryBaseSource, Progress.FlushBaseFrames and
Progress.FlushQueueEffects under Leanux.Proofs.WG, then #print axioms and
scripts/in-bundle lake env leanchecker --fresh MODULE for each root.
Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Work-state preservation, queue flushes and drain selection

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| TimerDiscipline.WorkStateFrames | 21 | 21 | 0 | 0 | 0 | 4 | 25 |
| Progress.FlushQueueFrames, Source and Claims | 6 | 6 | 0 | 0 | 0 | 0 | 6 |
| Progress.DrainOperations and DrainSelectionSource | 3 | 3 | 0 | 0 | 0 | 0 | 3 |
| Config.StagedLeaves | 3 | 3 | 0 | 0 | 0 | 0 | 3 |
| This tranche | 33 | 33 | 0 | 0 | 0 | 4 | 37 |
| Cumulative processed baseline and checked support | 1,093 | 836 | 36 | 22 | 199 | 101 | 1,172 |

The census is 523 campaign-owned files, 1,910 theorems and 367 checked proof
modules; 738 baseline declarations await validation. Counts are H1 180, H2 212,
H3 119, H4 360, H5 154 and H6 147. H1 remains current at its terminal closure;
H2–H6 and the full gate remain lagging. No new charter result is claimed.

WorkStateFrames retains ten queue/pending contracts, nine work-only projections
and two retained-worker contracts. Both index-insert callers use the actual
getDev-guarded liftIndex. Timer off/same/changed cases use the checked wheel
effects. Work-only projections obtain the actual initial clear queue internally;
no new clear-queue, readiness or success premise is added. Four private support
lemmas handle peer stores, timer arming and the native projection adapter. The
existing arbitrary Product adapter is unchanged.

FlushQueueFrames contains the two send-dependent queue frames;
FlushQueueSource contains the two substantive worker effect contracts; and
FlushQueueClaims contains their projected claims. Normal-return scope includes
final peer release, first-occurrence removal, duplicates and actual section
reads. Count decrease still requires only the original membership premise.
The drain source factor and selection contract preserve the actual send-before-
clear peek order, recorded-mode refusal, placeholder queue order and requested-
clear stop. The resolver uses the first actual matching unit association and
its rejecting membership guard, for arbitrary unit, queue and Ambient inputs.
No deletion is based on compilation failure.

StagedLeaves extracts empty-staged totality, missing-key partial impossibility
and the full Product staged_compose contract. The latter retains arbitrary
Q over the entire actual Product and actual liftWG callback executions. The
fourth staged_invalid contract remains pending, with its historical pure device
prediction explicitly outside the checked closure.

Independent reviews found no issues in the worker-state and drain source
contracts. Independent review also found no issues in all six flush contracts and the
three configuration leaves against their original scopes. The drain review identified an obligation
for the pending audit layer: native DrainOutcome alone omits original fixture
observations. Its exact audit equalities must also retain the full Product view;
the three source contracts here do not depend on those outcome equalities.

Scoped builds pass 103 jobs for WorkStateFrames, 160 for the drain/flush closure
and 74 for StagedLeaves, all warning-free. Axiom inspection covers 787 logical
roots in 149 proof modules, including 473 public theorem roots, with only the
three standard axioms. All four fresh kernel replays pass. Static checks,
all 258 terminal names/order, and mirror/shared boundaries pass.

Work-state probes 1–2 failed updated-peer inference, wheel predicate unfolding
and an unspecified intermediate bind predicate; unused simplifications were
removed. Probe 3 passes. Flush probe 1 failed Option.map normalization and
reported unused simplifications; probe 2 closed the goals but warned about an
unnecessary simpa; probe 3 uses explicit elimination and passes. Drain probe 1
substituted away the wrong device name and reported five unused simplifications;
probe 2 left the local action uninferred; probe 3 split a nested match before
the intended hidden-input test; probe 4 passed with one unused simplification;
probe 5 removes it and passes. Staged-leaf probe 1 failed record-update layout;
probes 2–4 failed successive native/Product run-factor normalizations and
reported unused simplifications; probe 5 had one obsolete trailing tactic;
probe 6 passes. Complete diagnostic outputs were saved and inspected. No
unchanged rerun, infrastructure retry, limit increase or guest run occurred.

Reproduce with scripts/in-bundle lake build on TimerDiscipline.WorkStateFrames,
Progress.FlushQueueClaims, Progress.DrainSelectionSource and Config.StagedLeaves
under Leanux.Proofs.WG, then #print axioms and scripts/in-bundle lake env
leanchecker --fresh MODULE for each root. Use capped, 32 Lean threads and
16 QEMU slots on this host.


## Complete initiation facts, full drain audit and invalid-key caller

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Roaming.InitiationConsumeSource and Product companions | 2 | 2 | 0 | 0 | 0 | 8 | 10 |
| Progress.DrainAuditSource and Product companions | 7 | 4 | 0 | 0 | 3 | 5 | 12 |
| Config.StagedInvalid | 1 | 0 | 1 | 0 | 0 | 2 | 3 |
| This tranche | 10 | 6 | 1 | 0 | 3 | 15 | 25 |
| Cumulative processed baseline and checked support | 1,103 | 842 | 37 | 22 | 202 | 116 | 1,197 |

The census is 527 campaign-owned files, 1,925 theorems and 374 checked proof
modules; 728 baseline declarations await validation. Counts are H1 180, H2 212,
H3 129, H4 363, H5 166 and H6 147. H1's terminal closure remains current;
H2–H6 and the full gate remain lagging. No new charter result is claimed.

The initiation finish and whole-consumer fact contracts are now carried on
their complete original domains. InitiationConsumeProductSource contains the
two original-scope claims and an unconditional actual-consumer erasure;
InitiationConsumeSource contains the two native companions and five private
source-composition lemmas. The Product model preserves independently supplied
lookup/beforeDh snapshots in the finish contract, including arbitrary fixture
fields. Observations actually captured by the consumer retain the actual
entry fixture through liftWG. No state is reconstructed for execution. The
True-entry partial scope, arbitrary messages, all rejection/release paths,
signed wrapping time comparisons, clock-read order and exact peer writes are
unchanged. Fact composition helpers are substantive source proofs, not frames.

DrainAuditSource has one recursive audit over actual WGWorld and Ambient,
with five native companion equalities and the two unchanged private Except
bind lemmas. DrainProductModel retains complete Product outcomes;
DrainProductAuditSource maps successful native states through the exact
liftWG update on the actual entry Product. Its five original-scope equalities
retain every other component and all eight fixture observations. No second
recursive audit or default state is introduced. The range correspondence
preserves every selector/worker error and exact success; the observation
retains the entry state. The pure increment erasure is kept unchanged.

StagedInvalid corrects the old deterministic queued-device prediction using
an actual optional clock/peek observation. The original resident and universal
invalid-current-key premises are unchanged. Empty packets bypass key access;
absent and zero-count keys take their actual fallback; missing and overflowing
key references keep their Stops. Positive acquisition and release preserve
the ordered key-store writes. A private tail contract and a domain-scoped
exact observer erasure support the projected claim, including failures. The
historical invalidStagedDevice definition remains for pending downstream
consumers and does not state the checked current effect.

Independent reviews found no issues in the complete initiation family or the
invalid-key observer and erasure. Root reviewed the native/Product drain audit
against the original exact outcomes. Scoped builds pass 72 jobs for the two
audit families and 75 for StagedInvalid, without warnings. A later 39-job drain
build follows removal of an extra final blank line. Axiom inspection covers
394 logical roots in 69 proof modules, including 165 public theorem roots,
with only the standard axioms. All three fresh kernel replays pass. Static
checks, all 258 terminal names/order, and mirror/shared boundaries pass.

Initiation probe 25 failed leaf/source-factor normalization, 26 failed the
remaining precomputed-key condition and reported an unused simplification,
27 passed with a deprecated rewrite warning, and 28 fixed that warning but
failed one Product lookup-result constructor reduction. Probe 29 passes with
no warnings. This follows the previously recorded probes 1–24; all original
scope is now included rather than crediting only the native finish fragment.
The proof limits remain 800000 heartbeats and recursion depth 2048.
Drain audit probe 1 closed the native goals but reported nine unused
simplifications; probe 2 removed them and added full Product derivations,
then passed. Invalid-key probe 7 failed an eliminated variable name and a
rewritten current-key branch; probe 8 failed the outer Except bind reduction;
probe 9 made that reduction explicit and passed. Complete diagnostics were
saved and inspected. No unchanged rerun, infrastructure retry, limit increase
or guest run occurred in this tranche.

Reproduce with scripts/in-bundle lake build on
Roaming.InitiationConsumeProductSource, Progress.DrainProductAuditSource and
Config.StagedInvalid under Leanux.Proofs.WG, then #print axioms and
scripts/in-bundle lake env leanchecker --fresh MODULE for each root.
Use capped, 32 Lean threads and 16 QEMU slots on this host.


## Drain bounds, initiation caller observations and retry preservation

| Tranche | Before | Retyped | Corrected | Deleted | Kept | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Progress.DrainEffects, DrainProductEffects and DrainClaims | 7 | 6 | 0 | 0 | 1 | 4 | 11 |
| Roaming.InitiationCallSource and Product companions | 4 | 4 | 0 | 0 | 0 | 4 | 8 |
| TimerDiscipline.RetryFrames and RetrySource | 9 | 7 | 0 | 0 | 2 | 0 | 9 |
| Config.KeyPeerEffects | 3 | 0 | 1 | 0 | 2 | 2 | 5 |
| This tranche | 23 | 17 | 1 | 0 | 5 | 10 | 33 |
| Cumulative processed baseline and checked support | 1,126 | 859 | 38 | 22 | 207 | 126 | 1,230 |

The census is 530 campaign-owned files, 1,935 theorems and 383 checked proof
modules; 705 baseline declarations await validation. Counts are H1 180, H2 212,
H3 137, H4 368, H5 177 and H6 156. H1's terminal module remains current;
H2–H6 and the full gate remain lagging. No new charter result is claimed.
The status table previously overstated H1 as carrying every original Noise
obligation: five RestartFrames declarations remain outside its terminal import
closure and outside the checked count. The wording is corrected; no census
number changes because of that correction.

DrainEffects contains four native support contracts. DrainProductEffects and
DrainClaims retain all seven original interfaces over full Product execution
and observations. The pure Product increment-bound contract is unchanged.
Each successful selected worker removes exactly one queue occurrence under
the original membership premise. The strict count < fuel bound leaves room
for the final empty selection; selector/worker failures retain their actual
origin and are not relabeled as the drain's own exhaustion. Observer totality
remains distinct from partial correctness of the actual drain. Claims use
the full Product projection, and the audit remains tied to actual lifted runs.

InitiationCallSource contains four native source/observer companions;
InitiationCallProductSource retains four original-scope equalities with full
nested cut and outcome observations. Packet/full-caller/transcript equalities
retain the original message-kind premise, while erasure remains unconditional.
The actual MAC, cookie, consumer, endpoint setter, response, statistics, timer
and release order is preserved. Arbitrary supplied Product cuts remain valid
suffix inputs. Captured cuts use the actual fixture and actual native/Ambient
states; the Product model itself permits independent snapshot fields.

RetryFrames retains the original id/attempt/retransmit-expiry predicates with
no added readiness, queue, reference or record premise. The queued-send frame
recovers the actual observer run from unconditional erasure and projects its
actual clock/peek effect. The historical queuedDevice lemma is kept but not
used as the source prediction. Zero-key arming projects current off/same/
changed wheel effects while preserving the retransmit expiry. RetrySource
retains the strict give-up test and one increment on the other branch; retry
queueing does not reset attempts. Its source equality is unchanged.

KeyPeerEffects keeps two pure lemmas and corrects the operational caller to
an observed staged-send effect. Actual precomputation and expiry derive the
invalid-key premise internally from the original resident-only domain. Both
sendStaged flags, empty packets, aliasing and ordered key writes remain in
scope. The expiry clock retains its original existential role; the fallback
clock/peek comes from actual execution. A private prefix contract and exact
resident-domain erasure retain all prefix and suffix Stops. Historical
keyPeerDevice remains for pending callers; their old prediction is not claimed.

Independent reviews found no issues in all four tranches. Scoped build passes
210 jobs without warnings. Axiom inspection covers 974 logical roots in 180
proof modules, including 552 public theorem roots, with only standard axioms.
All four fresh kernel replays pass. Static checks, all 258 terminal names/order,
and mirror/shared boundaries pass.

Drain probe 1 failed substituted successor names and a Product reason-match
normalization; probe 2 passed, and probe 3 removed three unnecessary native
claim companions and passed. Initiation caller probe 1 closed goals with one
constructor-name and six unused-simplification warnings; probe 2 fixed them
and passed. Retry probe 1 failed eliminated successor names, 2 failed a
Prop/Bool condition conversion, 3 passed with an unnecessary-simpa warning,
and 4 removed it and passed. Key-peer probe 1 used a reserved local name,
probe 2 passed with seven unused simplifications, and probe 3 removed them
and passed. Complete outputs were saved and inspected. No unchanged rerun,
infrastructure retry, limit increase or guest run occurred in these tranches.

Reproduce with scripts/in-bundle lake build on Progress.DrainClaims,
Roaming.InitiationCallProductSource, TimerDiscipline.RetrySource and
Config.KeyPeerEffects under Leanux.Proofs.WG, then #print axioms and
scripts/in-bundle lake env leanchecker --fresh MODULE for each root.
Use capped, 32 Lean threads and 16 QEMU slots on this host.
