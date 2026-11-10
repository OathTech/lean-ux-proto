# C2 work package 1: callbacks and call sites

Read first: `PLAN.md` here, `AGENTS.md`, `binary/C2Cut.lean`,
`binary/C2CutInterfaces.lean`, `binary/CallbackCmp8Rule.lean`.

## Files

You own `binary/CallbackCmp8.lean` and new files named `CallbackCmp8*.lean` (the
neutral half, which the C1 branch will take unchanged: nothing there imports a `C2*`
or `StatementC1*` module), and `binary/C2Callbacks.lean` and new files named
`C2Callbacks*.lean`. Import new files from those two roots; do not edit
`binary/lakefile.toml`. Frozen for you: `CallbackCmp8Image.lean`,
`CallbackCmp8Rule.lean`, the three `C2Cut*.lean` files, the statement files, and every
landed file (`RegionExecution.lean` in particular: it is shared with C1).

## What to prove

Each as `theorem name : Proposition`, with no hypothesis other than interface
propositions of this package.

Neutral half (`CallbackCmp8*`), in `Binary.Callback.Cmp8`:

| Proposition | Content |
| --- | --- |
| `PcRule` | the landed PC callback with its interior confined to the callbacks' text |
| `Cmp8Rule` | `__sanitizer_cov_trace_cmp8` from its five instructions and the landed `write_comp_data` proof |
| `ConstCmp8Rule` | the same for `__sanitizer_cov_trace_const_cmp8` (tag 7) |

C2 half (`C2Callbacks*`), in `Binary.C2`:

| Proposition | Content |
| --- | --- |
| `StubsAgree` | the range's reading of the image gives `Callback.Cmp8.Agreement` |
| `BtsSupported` | `CpsMono` for Kraken's `bts` |
| `RegionsLaidOut` | every run of consecutive instructions of the range is `LaidOut` |
| `PcSite`, `Cmp8Site`, `ConstCmp8Site` | the call-site rule (`CallSite`) for the three callees |

The call-site theorems may take the three rules, `StubsAgree` and nothing else as
hypotheses, or be closed; say which in your report.

## Where to start

- Rules. `CallbackWrappers.lean` proves the 4-byte and 1-byte entries by five
  `callback_step`s into `wrapper_body`, which rests on `CallbackCmp.cmp_run`. The 8-byte
  entries have the same five instructions. `wrapper_body` and `wrapper_plan` are
  stated by `KcovKind`, which has `.cmp8` and no constant 8-byte kind: for tag 7 go to
  `cmp_run` directly with `Callback.cmpPlan` on the entry's register state
  (`recordPlan tag` is that plan; `recordPlan_cmp8` already identifies tag 6 with
  `KcovPlan .cmp8`). The code runs under a partial fetch that is `ServiceImage.fetch`
  or `Cmp8.fetch`; `Callback.guarded_agreement` and `guarded_history` carry it to any
  agreeing `fetch`.
- The interior. `leafGuard` only keeps the callbacks out of the lookup image. `Text`
  needs: every guarded step fetched its instruction from the partial fetch, so its
  program counter is in that fetch's domain. That is one generic induction over
  `guardedStep`; with it `PcRule` follows from the landed `pc_run`.
- `BtsSupported`: the tactic block of `RegionExecution.operation_mono` on
  `Operation.interp` for `.bts` (a load, five `undefined`s, a store). Then a layout
  tactic that tries `Binary.regular_mono` and falls back to your lemma;
  `LaidOut` for the whole range and `CommonBitsSegments.layout_take`, plus a `drop`
  companion, give `RegionsLaidOut`. Do not add `.bts` to `RegionOperation`.
- Call sites. `Instrumentation.call_return` composes the `call` with a service run;
  `Kcov.callback` turns a contract into `KcovState` kept and `EqualOutside
  KcovBufferBytes`. Two differences from the landed use: (a) `Context` gives the
  separations only in a recording mode (`layout.mode = 2 ∨ layout.mode = 3`), where
  `Kcov.state_ready` and `state_preserved` take them unconditionally: split on the
  mode and use `Kcov.inactive_plan` in the other case; (b) for tag 7 there is no
  `KcovKind`, so the lemmas of `KcovInvariant.lean` that are stated by kind
  (`plan_normal_form`, `bufferPlan_preserves`, `writes_inside`, `ready`,
  `effect_preserves_buffer`) need a tag-7 counterpart: the stores differ from tag 6's
  in one value, at an address that is not the count word.
- `Quiet` after a call: the interior is in `Text`, and no exit is (`rfl` on the three
  exit addresses against `ServiceImage.fetch` and `Cmp8.fetch` was checked while the
  cut was made); the return state is at `pc + 5`, which the rule takes as not an exit.

Trial material (unreviewed, lemma sources only): `binary-trials/t3/RxMemory.lean` on
branch `task/binary-trials` for frame lemmas over `Footprint`. T3 assumed the callbacks;
this package is exactly the part it skipped.

## Dependencies

None on other packages. WP2 uses your propositions as hypotheses and does not wait.

## Estimate, risk, acceptance

- 7 to 12 worker-hours: rules 2 to 3, `bts` and layout 1 to 2, call sites 4 to 7.
- Main risk: the call-site rule for tag 7 (item (b)); it is the named main uncertainty
  of the statement packet's estimate. If generalising `KcovInvariant` by tag looks
  like more than three hours, stop and report with the lemma list. Second: `CallSite`
  as stated may ask for something the callback does not give. If so that is a finding
  against the cut: report it, do not weaken the proposition.
- Acceptance: `lake -d binary build` and `scripts/binary-proof-gate` pass; `#print
  axioms` on the nine theorems shows the standard three; no file outside your
  prefixes changed; raises of `maxHeartbeats`/`maxRecDepth`, if any, scoped to one
  declaration with the reason beside it and listed in your report.
