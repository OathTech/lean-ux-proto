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

| Result | Files | Before theorems | Before headlines | Retrofit status |
| --- | ---: | ---: | ---: | --- |
| Common projection | 2 | 0 | 0 | Native and product observations carried |
| H1 Noise | 35 | 171 | 22 | Native access, crypto/slot/peer frames, slot/clear/zero operations and all four state-edge contracts carried; six type-given frames deleted; full caller/reachability closure pending |
| H2 Index | 68 | 318 | 52 | Table/scans/insertion, full lookup/miss and success/empty-result inversion, exact allocation, ten projected table claims, all ten record contracts, exact draw exhaustion/corpus pair, five lifecycle contracts and 55 pure theorems checked; native receive factor and retirement frame carried; seven Ambient frames deleted; whole terminal closure/callers pending |
| H3 Roaming | 35 | 119 | 13 | Six native endpoint/destination contracts carried; two Ambient frames deleted; authentication callers and product callbacks pending |
| H4 Configuration | 130 | 554 | 79 | Total-return/branch laws, four exact source factors, three endpoint-clearing frames, three empty-root insertion contracts, total first placement, validation, concrete dump cancellation and one pure theorem checked; three Ambient frames deleted; remaining effects/readback carry pending |
| H5 Progress | 59 | 265 | 42 | Twenty-nine pure/control or pure-source theorems, three generalized worker control contracts and one Ambient record frame and seven exact cut-source/projected contracts checked; two pointer-ring snapshot contracts and remaining operational carry pending |
| H6 Timer discipline | 98 | 404 | 50 | Two pure session-liveness relations, map/guard base, two current wheel effects, separated jitter bound/frame and a checked stale-statement counterexample; three Ambient frames deleted; seven exact-peer arming claims and wider timer/worker semantics pending |

Retyped, deleted and retained counts will be reported per validated tranche.
All six results remain lagging, with their previous charter gaps unchanged.
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
