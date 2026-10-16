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
| H1 Noise | 35 | 171 | 22 | Native execution/getter/setter carried; terminal closure pending |
| H2 Index | 68 | 318 | 52 | Pending native index-table and WG contracts |
| H3 Roaming | 35 | 119 | 13 | Pure observation models build; native calls and product callbacks pending |
| H4 Configuration | 130 | 554 | 79 | One pure theorem checked; operational carry pending |
| H5 Progress | 59 | 265 | 42 | Twelve pure/control theorems checked; operational carry pending |
| H6 Timer discipline | 98 | 404 | 50 | Pure views build; timer wheel and worker semantics pending |

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

The tree now has 428 campaign-owned files and 1,833 theorems. The 258
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
