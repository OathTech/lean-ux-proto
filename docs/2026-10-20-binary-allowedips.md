# Allowed-IPs binary refinement: experimental closing record

Status: intentionally partial experiment on `task/binary-allowedips`. Neither
charter checkpoint A nor B completed. **Zero newly completed functions; no
insertion or subsystem adequacy claim.** The proved components and executable
tests remain in the standalone binary package. The original target is in the
[charter](2026-10-20-charter-binary-allowedips.md); its review is in
[the charter review](2026-10-20-review-binary-allowedips-charter.md).

## Experimental close and landing preparation

[USER 2026-10-20] Stop manual whole-function insertion and land the tested
components as an early experiment with their measured limitations. After
landing, redirect the track to realization R1 of the typed heap view, on a
new branch from main. R1 has not begun on this branch.

The coordinator's design note is commit **`de18ce37` on
`task/design-heap-view`**, path `docs/2026-10-20-design-heap-view-overlay.md`;
it is not included in this landing. Read the fixed revision with:

```sh
git show de18ce37:docs/2026-10-20-design-heap-view-overlay.md
```

R1 presents Kraken memory through an executable typed view, with load/store
correspondence and framing proved once, leaving the instruction semantics
unchanged. Its proposed calibration is a lookup re-proof followed by the
empty-root tail. This is a direction to test, not a result already achieved.

## Calibration and persistent cost

Work started at 2026-10-20 01:25:17 UTC, preparation included. At the four-hour
point, 05:25:17 UTC, there were **zero newly completed functions**. The count
remained zero at the final manual checkpoint recorded at 09:55 UTC, about eight
and a half elapsed hours after starting. That elapsed interval includes testing
and coordination; the later pause and landing preparation are excluded.

| Measurement | Reachable record / tree | Added / deleted Lean lines | Files | Excluding three generated modules | New completed functions |
| --- | --- | --- | --- | --- | --- |
| Four-hour measurement | Recorded by `2b049c9b`, measuring its parent tree | 9,845 / 31 | 110 | 8,290 additions in 107 files | 0 |
| Final manual checkpoint | `bf730baa` | 18,529 / 31 | 221 | 16,974 additions in 218 files | 0 |

Reproduce with `git diff --numstat eba3c2b6..2b049c9b^ -- 'binary/*.lean'`
and `git diff --numstat eba3c2b6..bf730baa -- 'binary/*.lean'`. Exclude
`AllowedipsMutationImage`, `AllowedipsMutationLayout` and
`AllowedipsMutationCodeLayout` for the last size column. The record commit
`2b049c9b` itself also includes 430 later support lines: its tree has 10,275
additions across 115 files. It must not be substituted for the four-hour tree.
These sizes include executable reconstruction, tests and support lemmas as
well as proofs. Review repairs after `bf730baa` are not counted as manual
calibration work. There is no measured time per completed new function.

Testing found a mirror defect before universal composition and exercised
structural split, failure, rollback and reuse cases on a retained heap. The
empty-root physical tail composes in 83 lines, showing useful execution reuse.
The continuing expense was allocation identity extension, fresh-node byte
decoding, mutation frames and structural invariants. Elaboration shape also
mattered: an overly expanded decoder was reduced from a 70-second failed
attempt to about a second by exposing its conditional without changing its
accepted states. These observations motivate the heap-view experiment; they
do not establish viable whole-WireGuard proof cost.

## Retained component theorems

Names below are in `Binary.Pair.Allowedips` unless stated otherwise. Every
insertion result begins at a named internal cut with explicit local resources.
None establishes all paths from insertion entry to ABI return.

| Result | Theorem / module | Scope and remaining composition |
| --- | --- | --- |
| Extended lookup reconstruction | `lookup_checked` in `PairAllowedipsLookupAdequacy` | Lifts the existing complete lookup to roots, exact counter, parents, ownership lists and heap validity. Reuse of an existing function, not new function coverage. |
| Shared common-prefix helper | `common_checked` in `AllowedipsCommonChecked` | Both insertion call sites, both families, using the tested caller assertion and existing helper theorem. |
| Placement loop | `Placement.loop_checked` in `AllowedipsPlacementChecked` | Complete loop from its executable header assertion, preserving reconstruction and heap validity. Entry-to-header establishment remains open. |
| Exact-prefix reassignment | `Exact.assignment_from_relation` in `AllowedipsExactTotal` | Actual stores/list updates restore reconstruction, heap validity and byte frame, including same-owner movement and previously internal nodes. |
| Empty-root tail | `Root.initialization_checked` in `AllowedipsRootChecked` | Post-allocation boundary through initialization, allocation-name extension and root publication; restores reconstruction and heap validity. |
| Nonempty initialization | `NodeInit.initialization_core_checked` in `AllowedipsNodeCore` | Fresh node core from the tested initialization boundary, with a byte frame and pending old-state resources. |
| Continuous child attachment | `ChildFinish.initialization_child_checked` in `AllowedipsChildChecked` | `add+0x156` to `add+0x549`, including initialization, two coverage calls, selection and publication; restores reconstruction and heap validity from tested resources and explicit branch cases. |
| Returns | `Return.{add_checked,wrapper_checked}` in `AllowedipsReturnChecked`; `Return.finish_checked` in `AllowedipsReturnFrame` | Separate epilogues through RET, and final callback/frame preservation; not joined to every insertion path. |
| Counter instruction | `increment_region` in `AllowedipsCounterRegion` | The actual u64 increment and write frame, including wraparound. |

The exact target `Exact.assignment` calls the mirror primitives; the empty-root
endpoint `Model.emptyInstalled` is a local formula copied from the source
proof. The current segment theorems do not link either target to an accepted
complete execution of `Leanux.WG.add`. That is part of the missing composition.
`AllowedipsInsertionSurface` is a partial-proof replay root, not an adequacy
theorem for insertion.

## Rule Zero: sequence-counter defect and correction

Linux stores the allowed-IPs sequence as a u64, while the original mirror used
an unbounded Nat. The dump compares the saved sequence, making wrap observable.
The constructed-state reproducer executes both insertion wrappers and the
invalid-prefix path, including real coverage/comparison services, to the ABI
return. It needs no allocator substitution on that path.

| Initial sequence | Cases | Binary result / sequence | Mirror before correction | Mirror after correction |
| --- | --- | --- | --- | --- |
| 1 | IPv4 CIDR 33; IPv6 CIDR 129 | -EINVAL / 2 | -EINVAL / 2 | -EINVAL / 2 |
| 2^64 - 1 | Same | -EINVAL / 0 | -EINVAL / 2^64 | -EINVAL / 0 |

Both undefined-value seeds (zero and all ones) give those results: eight cases,
124 interpreted instructions for IPv4 and 127 for IPv6. The mirror lane fixed
the counter on main `1f766662`, using UInt64 with wrapping increments and dump
comparisons. The same binary expectation now passes; no non-wrapping Pre,
modulo target or weakened reconstruction was introduced. These are concrete
entry witnesses, not a general reachability theorem.

## Trust surface and reproducibility

The image remains the read-only **s5** ELF with SHA-256
`06513d05fc37506b6cea546e8f11b9fe328e482265341ca41c242157bfa5e88e`.
Kraken is pinned at **`43df9468febc173e6cf9363d87e8ad34e76d7434`**, upstream
`8af78062037bc237b341d20252aafd1797c1bcb7` plus nine committed patches. Patch
nine adds register BT, with operand-width modulo indexing, CF set to the
selected bit, unchanged registers, and OF/SF/ZF/AF/PF undefined. ZF is deliberately
nondeterministic to cover the vendor difference described in the
[README](../binary/README.md). Both image sites overwrite flags before reading
ZF. Unsupported forms fail closed. The patch, lock, clean private checkout and
`TrustBase.krakenCommit` agree. This is a retained **trust-surface change**, not
an ISA-fidelity theorem. No kernel image change accompanies it.

`AllowedipsMutationDecoderAgreement` names the additional literal insertion
image premises. Theorems retain their explicit decoder, callback and local
resource hypotheses. The paired runner supplies generic allocator/free
transitions; it does not prove those services. The environment remains an
unrealistic serialized projection. No project axiom, native-decision axiom,
proof escape or increased resource limit is introduced by this increment.

A clone can bootstrap the locked dependency with network access, then build
and gate the proofs from committed image terms. The execution drivers,
image/layout regeneration checks and captures require the exact s5 artifact,
which is box-local and has no repository recipe promising that exact ELF hash.
The README states this limitation and the `LEANUX_BINARY_KERNEL_DIR` override.

The generated suite uses constructed entry memory and supplied allocator/free
returns. Its retained sequences contain 66 insertion/lookup pairs and 24
isolated root cases, with 28 root, 20 exact, ten child-publication and ten
child-resource assertions, among others. The earlier recorded three-way check
compares eight calls under two seeds with 170 coverage entries, 64 comparisons
and 117 decisions; it also constructs entry memory. A separate first-entry
capture uses actual kernel bytes with a captured allocator transition under a
checked frame. These three kinds of evidence are distinct; none supplies a
missing universal contract.

## Landing review and remaining obligations

The independent landing review is commit `00d96ec8` on
`task/review-binary-allowedips`, path
`docs/2026-10-20-review-binary-allowedips-landing.md`.

| Finding | Disposition |
| --- | --- |
| B1 | `binary/` imports no `Leanux.Proofs` modules. Required definitions and two map lemmas were copied with origin comments into `AllowedipsSourceModel`; local execution equations live in `AllowedipsSourceRun`. The endpoint formula is unchanged apart from namespace. The proof gate's `check_imports` step passes. |
| S1 | ZF is undefined in patch nine; focused tests check both results for both incoming values at all three widths. Native comparison reads CF only. The patch, lock and printed trust surface are updated. |
| S2 | Reachable calibration records are used, with the earlier measured tree distinguished from the later support additions. |
| S3 | The heap-view note is cited by commit `de18ce37`, not by an assumed file in this tree. |
| S4 | Exact-s5-artifact dependence and the absence of an exact-hash rebuild recipe are explicit. |
| S5 | Timestamped checkpoints are removed from the tracked report; this closing record retains the conclusions, costs and reproduction commands. |
| N9 | The new register row is part of the Markdown table. |

The whole-function work remains open: entry establishment, allocator contracts,
covering/intermediate insertion, failure/rollback, and function/sequence
composition. The joint decoder premises do not yet have a common-fetch
satisfiability witness (review N4); the literal images are checked against the
same pinned ELF, but that is a test, not the proposed witness theorem.

Earlier M1 obligations also remain open as detailed in the
[landing assessment](2026-10-19-binary-landing-assessment.md): NULL-owner and
wrong-kind/KCOV-mode-3 theorem witnesses (F1), original transports' callback
hypotheses (F2), initial representation/separation assumptions (F6), entry
realism (F7), and subsystem-wide cost/coverage (F9). Index insertion still
uses the broader permission premise through its random provider. No realistic
interrupt, RCU, concurrent-caller, whole-operation or whole-trace contextual
refinement follows from this landing.

## Validation and reproduction

Review corrections are being validated on the requested rebase onto
`ac55c7d5`; the closing handoff records the exact source commit and counts here.
The mirror itself is not edited. The opt-in insertion coverage profile and
allocator-site arming are the only runtime harness changes in this experiment.

From the worktree root, with system Python and pyelftools installed:

```sh
capped python3 -B binary/run.py --bootstrap-only
capped scripts/binary-proof-gate
capped lake build leanux-fixed-width-tests
capped lake build
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
capped python3 -B binary/allowedips_seq_wrap.py
capped python3 -B binary/allowedips_mutation.py
```

The package [README](../binary/README.md#allowed-ips-mutation-scaling) gives the
recorded/capture recipes and the nine-root export command. The external gate
must run outside Nono from `binary/`:

```sh
capped lake check --from-export ../.tmp/binary-allowedips-landing.ndjson
```

Require successful export generation from the claimed code revision. Exports
and logs are disposable, not committed artifacts. No earlier export acceptance
covers the review corrections. Independent external acceptance remains pending;
no merge to main or push is made by this branch preparation.
