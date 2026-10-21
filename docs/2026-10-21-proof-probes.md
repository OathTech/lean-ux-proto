# Bounded probes after campaign 3

Branch `proofs/probes`, based on main `c63423ef` (campaign 3 landed at
`3361fb77`; executable mirror remains `218d3ffd`). Scope: the three probes
queued by the 2026-10-20 fresh-eyes review. No mirror, harness or evaluator
source was changed. No Lean resource limit was introduced or raised.

| Probe | Result |
| --- | --- |
| [Lifetime fault exclusion](2026-10-21-lifetime-fault-probe.md) | Initialized goal stated for a named parser-admitted fixture class; **open**. One checked local countermodel refutes deriving fault exclusion from R2's allocation invariant alone. Stronger closure cost and next milestone are reported. |
| [One-event removal](2026-10-21-observer-removal-probe.md) | Removing the peer getter's read breaks its unchanged coverage equation. Exact erasure and safety of the retained history survive. Temporary excerpts only; no production mutation. |
| [Independent inputs and UP interference](2026-10-21-independent-input-probe.md) | All 16 fixed traces / 115 operations agreed; none filtered, unsupported or retried. Audit distinguishes the second BH-enable from the insufficient first-unlock scenario; initialized UP race reachability remains unproved. |

The first probe contributes one negative local theorem, not a new initialized
security guarantee. Lookup-history safety, no invalid access attempts, exact
reference accounting and eventual reclamation remain separate claims.

## Validation

The focused proof build passes without warnings (117 jobs), and its headline
uses only `propext`, `Classical.choice`, `Quot.sound`. Fresh kernel replay of
`Leanux.Proofs.WG.LifetimeSafety.FaultProbe` exits 0 with no output. The observer
experiment passes its unchanged baseline and surviving claims and obtains the
expected red result on the deleted event's coverage equation.

All **144 unit cases** have passed across the scoped runs. The first run had
142 passes, one failure because `leanux-fixed-width-tests` had not yet been
built in this new worktree, and one skipped kernel-identity case because the
default kernel directory was absent. Building that executable and selecting
the approved kernel allowed the two affected cases to pass; the other cases
were not redundantly rerun. The native model build passes (130 jobs).

The **full proof gate passes**: 6,681 build jobs, 2,455 terminal declarations
over 20 root modules; only the three permitted axioms, no compiler warnings,
no forbidden-token or import/default-target violations. The proof source did
not change after `3f100450`; subsequent commits change reports and recipes.
The **counterexample speedbump fails: 14/15 pass**. The sole failure is the
unchanged inherited C2 `h5-namespace-pin` recipe,
`Progress/NamespacePinPending.lean:36` (`#eval reproduce`):
`namespace-pin alias: concrete input no longer parses`. The current parser
rejects its literal reserved fixture descriptor; the recipe still expects
acceptance. This is the already registered H5 replay lag, not a new fault
found by these probes. It remains unfixed here; no C2 source was edited.
The other fourteen published recipes pass, including both R2 cursor witnesses
and the R5 lifetime witnesses. The failed speedbump is not reported as green.

An exploratory `leanchecker --help` invocation was terminated
by its own PID after it started checking instead of printing usage (exit 143,
not a pass); the subsequent correctly scoped fresh replay above passed.

## Reproduction

From a clone with the declared toolchain and approved oracle prepared as in
[the repository build instructions](../AGENTS.md#build-test-and-check):

```sh
lake build leanux-model leanux-fixed-width-tests
python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
scripts/proof-gate
scripts/proof-counterexamples
lake env leanchecker --fresh Leanux.Proofs.WG.LifetimeSafety.FaultProbe
python3 docs/probe-observer-removal.py
python3 docs/probe-input-sample.py --emit
python3 docs/probe-input-sample.py --run
```

Set `LEANUX_KERNEL_DIR` to the approved build if it is not at the harness's
default project artifact path. On the shared box, run each build/check through
`capped -- scripts/in-bundle`. Large output, binaries and temporary copies are
reconstructible worktree artifacts, not committed evidence bundles.

