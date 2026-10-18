# Campaign 1: carry over the GRO correction

The carry targets mirror `77c9b555`, following the campaign landing at
`aacaed43`. It changes the proof tree and its documentation only. All seven register
rows are current over this pin after the complete proof gate, fresh kernel
replay and executable witness checks.

## Corrected contracts

The mirror now classifies GRO packets through its network and TCP layers.
A refused merge of two packets in the same flow completes the held packet
before processing the newcomer. The proof-side logged and tagged copies follow
these branches exactly, including early normal delivery, unsupported coalescing,
and the unsupported second held flow. Erasure still permits arbitrary incoming
GRO states, histories and callbacks; it does not assume a singleton held list.
Callback failures retain their exact stopped prefixes.

The old static normal-before-held partition is false under this source.
[AGENT 2026-10-18] The replacement `selectedEntries` follows the source's
successive selection decisions.
Its permutation theorem and the per-poll selected-entry prefix and completion
theorems are proved for that definition. The supporting ready/pending invariants
carry a continuation equation for arbitrary future entries; a derived bound on
the initialized poll's held list is local to these order proofs. Unsupported
branches retain a bookkeeping suffix, without asserting that those callbacks
run. These definition changes are substantive even where a theorem's written
header is unchanged.

The two conditional helper statements `held_then_normal` and
`original_gro_held_then_normal` use the corrected classifier and require that the
newcomer bypass the held packet. Without that condition, a refused same-flow
merge gives the opposite order. `ReplayGro.lean` checks this distinction using
the original receive/receive/flush actions and a callback that accepts only
held-before-newcomer order; applying that callback in the former reversed order
fails. This additional check is a direct helper input, not another accepted
initialized runner trace or a Linux capture.

The existing accepted distinct-flow `r4-gro-reorder` episode remains the R4
counterexample to chronological post-GRO order. The carry preserves the
initialized lifetime, authorization, ingress disposition and carrier contracts;
it does not turn reviewed completeness of observer wiring into a theorem.
Existing limitations in the result register continue to apply.

## Counts and review

Twenty-two proof files change; the complete tree still has 916 proof files.
Named theorems increase from 12,302 to 12,310: thirteen supporting theorems are added and five obsolete
static-partition helpers are removed. The removed helpers are
`GroPending.normal_ready`, `GroPending.held_ready`, `groNormalOne_ready`,
`GroReady.rxList_normal` and `GroReady.held_not_normal`, all in `SelectedGro`.
The count includes private and attributed declarations and counts declarations
in different namespaces separately. The seven `Statements.lean` surfaces keep
all 860 names: 858 theorems and two definitions, including all 326 R4 terminals.
Two existing theorem headers change as described above; the selector and its
invariants also change meaning.

Independent source review found stale explanations of callback order in two
register locations and wording that made the required box resource wrapper sound
optional. Both findings are corrected and verified. Review covered the final
source changes, arbitrary-state erasure, same-flow completion, callback failures
and initialized domains; it found no further source or contract issue.

## Validation

On the shared box, reproduce from this checkout using the project bundle and
required resource wrapper:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-counterexamples
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

The unit suite passes: 131 tests, one skip because no selected real kernel build
is supplied to its identity test. The complete build passes all 973 jobs.
The proof gate passes all 895 declarations across nine direct root modules, with only `propext`,
`Classical.choice` and `Quot.sound`; its token, import and target checks pass.
Fresh kernel replay of `Leanux.Proofs` exits successfully with no output.
All twelve executable recipes pass, including the strengthened GRO helper
check and the W7 full-ring witness. No differential guest run is claimed for this
proof-only change.

Development builds and scoped checks had ordinary source/tactic failures,
including a deterministic heartbeat failure in the generic carrier-preservation
search; those attempts are failures, not validation. Two worker preflights
initially lacked the `RxPollOrder` or
`RoutingHandshakeFrames` dependency artifact, before launching Lean; each had
one infrastructure retry after its dependency was available. No carry build or
check was killed, and no resource limit was raised. The existing mirror-side
`String.mk` deprecation at
`Leanux/Env.lean:865` remains outside this proof-only carry.

[USER 2026-10-18] This work carries the landed campaign over the GRO correction;
further campaign work waits for campaign 3's charter.
