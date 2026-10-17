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
| H1 Noise | 35 | 171 | 22 | Native access, crypto/slot frames and nine exact slot/clear/zero contracts carried; six type-given frames deleted; pure effect relations checked; terminal closure pending |
| H2 Index | 68 | 318 | 52 | Table, lookup/collision scans, insertion exactness and 36 pure theorems checked; full lookup/caller closure pending |
| H3 Roaming | 35 | 119 | 13 | Pure observation models build; native calls and product callbacks pending |
| H4 Configuration | 130 | 554 | 79 | Total-return/branch laws and one pure theorem checked; two Ambient frames deleted; operational carry pending |
| H5 Progress | 59 | 265 | 42 | Twelve pure/control theorems checked; operational carry pending |
| H6 Timer discipline | 98 | 404 | 50 | Two pure session-liveness relations checked; timer wheel and worker semantics pending |

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

The tree now has 430 campaign-owned files and 1,830 theorems. Of the baseline,
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
