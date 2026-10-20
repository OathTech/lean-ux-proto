# Independent review: landing the allowed-IPs binary scaling experiment

Reviewed: branch `task/binary-allowedips` at `8940fe12` (27 commits over
main `eba3c2b6`; 241 files, +23,393 lines), against main `ac55c7d5`, on a
detached copy. Inputs read: the charter, its review, the scaling report
(closing entry in full, checkpoints sampled), `binary/README.md`, the
register row, patch nine, the lock, `binary/TrustBase.lean` diff,
`binary/surface.py` diff, the printed trust surface for the new headlines, and
the design note at `de18ce37`.

## Verdict

**Land with named changes.** The experiment is honestly reported: zero
completed functions, both checkpoints open, segment-level theorems stated as
such, and the trust-surface change of patch nine pinned consistently. One
finding blocks: the branch makes `binary/` import the proof tree, which turns
main's proof gate red. Fix that (or obtain the user's decision to change the
rule) and address the should-fix items, then land.

## Checks run

All on the detached copy, through `capped`.

| Check | Where | Result |
| --- | --- | --- |
| `python3 -B binary/run.py --bootstrap-only` | `8940fe12` | PASS, no network: cloned from the main checkout's staged `.deps/kraken`, applied nine patches, HEAD `907830a1` as locked |
| `scripts/in-bundle scripts/binary-proof-gate` | `8940fe12` | PASS: 1,160 jobs, axioms standard, trust-surface diff PASS, escape scan clean, no warnings |
| same gate | local merge preview of `8940fe12` into `ac55c7d5` (clean merge) | PASS |
| `lake env leanchecker --fresh AllowedipsInsertionSurface` | merge preview | PASS (exit 0, 3 min 35 s) |
| `binary/allowedips_seq_wrap.py` | `8940fe12` | PASS 8/8; entry 2^64-1 gives binary and mirror sequence 0 |
| `binary/allowedips_mutation.py` | `8940fe12` | PASS: 66 insertions/66 lookups, 24 isolated root cases, segment counts as reported |
| `lake build` + the five-module unit tier | merge preview | PASS, 144 tests, 1 skip (after building the test executables, which the default target omits) |
| proof gate step 4 (`check_imports`) in isolation | `8940fe12` vs main | **FAIL on the branch (3 findings), PASS on main** |
| `git diff eba3c2b6 8940fe12 -- Leanux` | | empty: the mirror and the proof tree are untouched |

Not run: the user-run `lake check --from-export` (not mine to run), the
QEMU-backed recorded comparison and capture replay, the full differential
check (the branch cannot reach it; see N1).

## Findings

### Blocking

**B1. The branch makes the binary package import the proof tree; main's proof
gate then fails.** `binary/AllowedipsAllocationTarget.lean`,
`binary/AllowedipsExactTarget.lean` and `binary/AllowedipsPlacementSourceStep.lean`
import `Leanux.Proofs.WG.AllowedIps.{MutationMirror,ExactMutation,ArithmeticMirror}`,
and the printed binary surface contains the proof-tree definition
`Leanux.Proofs.WG.AllowedIps.emptyInstalled`. `scripts/proof-gate` step 4
scans every `.lean` file outside `Leanux/Proofs/` (it skips only build and
cache directories, not `binary/`) and fails on any such import; AGENTS.md
names this as part of the proof tree's gate. Running that step alone gives
three FAIL lines on the branch and none on main. Main's last integration
reported the proof gate green, so landing would break it. Consequences beyond
the red gate: the binary build now pulls 43 proof-tree modules, so
`binary/README.md`'s statement that the binary gate does not build
`LeanuxProofs` is no longer accurate. Proof-tree refactors, which land often,
can also break the binary package without either gate noticing (the proof
gate does not build `binary/`). Fix: move the few definitions and lemmas the
binary needs into `binary/`, restated over the mirror, or put the rule change
to the user (allow `binary/` as a declared consumer, update the gate's scan
and the README, and accept the coupling). Either way the decision is recorded.
It is not something the merge should decide on its own.

### Should fix before landing

**S1. Patch nine follows Intel's BT flag rule; AMD documents ZF as undefined.**
The semantics keep ZF and make OF/SF/AF/PF undefined, citing the Intel SDM.
AMD's manual lists ZF as undefined for BT. Earlier Intel references did too,
and QEMU's 2011 discussion of the same divergence (Launchpad bug 904308)
records it. This box is an AMD Zen 4; the native test passing here shows
that this part preserves ZF in that case, not that the architecture does.
At both image sites (`AllowedipsMutationImage` regions `r31d` and `r577`) BT
is followed by `setb`, `lea`, `movzbl`/`mov` and then an `or` that rewrites the flags, so
ZF is dead there. Making ZF undefined as well should cost no proof and makes
the trust surface vendor-neutral. If it is kept, the README should state the
vendor choice and why. Otherwise the patch checks out. Register offsets
reduced modulo the width are right for 16/32/64 bits; the AT&T operand order is
right (base = destination); 8-bit, memory, immediate and LOCK forms fail
closed. The undefined flags are nondeterministic `undefined` choices, which
`Effects.All` quantifies over. The lock, the patch's `From` hash,
`TrustBase.krakenCommit`, the README and the bootstrapped checkout all agree
on `907830a1`. Note that the lock's `commit` field changes as well as the
patch list, because it is the patched tip, not an upstream commit; upstream
is still `8af78062`. Without the patch the proofs would not be false. They
could not be stated: the image text would not parse.

**S2. The scaling report cites two pre-rebase commits that will disappear.**
The closing table gives `7b8b257c` and `e683be60`. Neither is reachable from
any branch, so garbage collection will remove them. Cite the post-rebase
commits (`2b049c9b` for the four-hour record, `bf730baa` for the final one),
or say that the figures were recomputed on them.

**S3. README and report point at a design note that exists only on
`task/design-heap-view`.** Once that branch is removed, the pointer dangles.
Either land the note with this change or cite it by commit (`de18ce37`) and
say it is not on main.

**S4. Executable reproducibility from a clone is narrower than the README
suggests.** A clone can bootstrap the pinned Kraken (with network) and build
and gate every proof, since the image terms are committed. Every executed
test (the mutation runner, the sequence-wrap witness, generator `--check`,
the recorded comparison, the capture) needs the s5 ELF with an exact SHA-256.
No recipe here rebuilds it, and it is no longer the mirror's oracle (main
uses e2). The README should say plainly that the tested segments can be
replayed only with the s5 artifact. If that artifact matters, say how to
regenerate it or that it is box-local. This dates from milestone 1, but this
increment adds the most tests that depend on it.

**S5. The report reads as a run narrative.** It has about 1,000 lines of
timestamped checkpoints, including lists of development slips (wrong paths,
a wrong working directory, guessed file names). AGENTS.md excludes run
narratives from landed records, and the charter asks for conclusions and
reproduction commands. The closing entry already carries the conclusions,
costs and validation. Either condense the checkpoint sections to the cost
evidence the redirection rests on (what was proved when, what cost
persisted, the counter finding) or get the user's explicit acceptance of
landing the long form as the record of cost.

### Notes

**N1. Segregation from the mirror work holds, except for B1.** The mirror
is untouched. `harness/linux.py` adds a fifth opt-in coverage profile,
`allowedips-insert`, that resolves four ELF symbols. It fails closed if a
symbol is missing, duplicated, not text, or comes from the wrong source
file. `evaluator/check.py` adds the profile to the parser's choices and,
only when `--binary-coverage --binary-profile allowedips-insert` are both
given, arms the three allowed-IPs allocator sites unsteered. The default
profile is `index`, and the parser already rejects a non-default profile
without `--binary-coverage`. No gate command passes these flags, so the
differential check, its guards and the identity check cannot see the change.
No unit test covers the new profile; it is exercised only by the README's
recorded-comparison recipe, which I did not run.

**N2. The claims match the theorems.** Every new headline is a segment
statement. An executable boundary check or a hand-written effect summary
(list splice, saved-register reload, record initialization; not an
interpreter replay) succeeds at a named PC, and then every Kraken execution
reaches a later named PC with the summarized registers, a write frame and,
where stated, reconstruction and heap validity. No headline starts at a
function entry and ends at its return. `Placement.loop_checked` starts at
`add+247` from a checked header, which matches the report's statement that
entry-to-loop establishment is open. The four-hour and final counts of zero
completed functions are stated consistently in the charter header, the
report, the register and the README. I found no precondition narrowed to
close a case. The sequence counter's correspondence stayed exact, and the
witness's binary expectation is unchanged.

**N3. Two segment targets restate the mirror rather than call it.**
`Exact.assignment` (in `binary/`) and `emptyInstalled` (in the proof tree)
are reassemblies of mirror primitives. By inspection, `assignment` matches
`add`'s exact branch line for line (`setNode`, `listDel`, `listAddTail`).
No theorem links either one to `Leanux.WG.add`; that link is part of the
missing composition. A reader should not take "relates to the mirror" as
"runs `add`".

**N4. The new decoder premise has no satisfiability witness.**
`AllowedipsMutationDecoderAgreement` is conjoined with the existing
`AllowedipsDecoderAgreement`. If two literal images disagreed at one PC, the
theorems would hold vacuously. The risk is low, because the images are
separate functions generated from one ELF. Proving a single witness `fetch`
(for example, the union of the literal fetches, with disjointness checked
by `decide`) is cheap and worth doing when composition resumes.

**N5. The counter finding is recorded accurately.** The report and charter
give the discovery state (Nat against u64), the reproducer, the assignment of
the fix to the mirror lane, the fix on main at `1f766662` (an ancestor of
main) and the unchanged witness, which now passes. The mirror's commit
message credits the binary track's instrument, and I re-ran the witness.

**N6. Main has mirror changes since the branch base.** `Leanux/Runner.lean`
and `Leanux/Syscalls.lean` changed (the namespace-pin fix), as well as docs
and the proof tree, and `binary/ProbeSupport.lean` imports `Leanux.Runner`.
The branch's own gate run does not cover the merged tree. My merge preview
(the gate, a fresh replay of the insertion closure and the unit tier) passes.
The merge commit should still record a gate run on the actual merge result.

**N7. Size and carrying cost.** The binary build is 1,160 jobs and the
expected surface is 4,713 lines. The register lists 71 printed headlines; a
reader could take that number as a measure of results, but most are segment
lemmas. The coupling cost to main is real and not owned by any gate: mirror
or proof-tree changes can break `binary/` silently between binary claim
points. Recording this as the register's existing "lagging" notion, applied to
the binary package, would make the cost explicit.

**N8. Hygiene.** The increment adds no resource-limit raises (the one
`maxHeartbeats` in the diff is pre-existing Kraken context in the patch) and
no linter suppressions. The gate log has no warnings and the forbidden-token
scan is clean.

**N9. Formatting.** In `docs/proofs.md` the new register row comes after a
blank line, so Markdown renders it as a stray paragraph rather than a table
row.

**N10. The redirection is supported by the evidence given.** The report
puts the persistent cost in allocation identity, byte decoding, mutation
frames and structural invariants, and stops short of a rate estimate. The
typed-heap-view note says it targets the memory representation and leaves
Kraken's instruction semantics alone. That is a reasonable next experiment.
It is not a result of this branch, and the report says so.

Independent reviewer: Claude Opus 5.5, 2026-10-20.
