# The Ascent / Kraken-WP probe: closing report

Status: experiment closed. [USER 2026-11-10] The documentation of the
experiment lands (this report, the charter, the bridge design, the review);
none of its code does. The code stays on the local branch
`task/ascent-probe`, unmerged and unpushed, in case the direction is
revisited. Its stage 2 package must in any case not be pushed or merged
while Ascent carries no licence: three of our rules there follow its
demo's proofs closely.
[Charter](2026-11-09-charter-ascent-probe.md),
[bridge design](2026-11-09-ascent-image-bridge.md),
[independent review of stage 1](2026-11-10-review-ascent-probe-stage1.md).
Paths under `binary-ascent/` below are on that branch. Times are agent
wall-clock times read from the box clock; they are not labour baselines for
a person.

## Verdict

**Usable with named engine gaps, and no authoring saving shown.** The
fork's weakest-precondition layer works on our image with no new trusted
assumption, and porting to it was cheap. On the one unproved, heap-mutating
segment tried both ways, both methods closed in about six minutes with
similar proof size and check time. The segment did not discriminate: the
difficulty the allowed-IPs work ran into (allocation identity, structural
invariants, reconstruction after mutation) is not in a 22-instruction
physical segment, and the layer under test does not address it. Lifting
with `ascend` works on a call-free fragment but did not reduce proof effort
and cannot yet handle our code's shape (calls, fragments that exit by a
jump).

## Results by stage

| Stage | Result |
| --- | --- |
| 0a | Our nine Kraken patches carried onto the fork's `vcgen` head (tree `2cd5038f`), instruction hunks unchanged except two condition codes the fork already has. Two `sorry` declarations of the fork's examples remain in its library, unreferenced. |
| 0b | The mirror builds on `nightly-2026-11-07` unchanged. |
| 0c | Ascent and its demo build; a bridge from `Eventually (step1 Host.exe)` to `Eventually (instructionStep fetch)` exists without a new premise. |
| 1 | The client's 141-module closure ported by 23 added lines in 13 modules (two toolchain causes, no proof change). `ChildInput.segment'` proved through the WP layer at the original's type (same term), standard axioms, none of sixteen old execution lemmas in its closure. Four new specs proved from the interpreter. |
| 2 | The ten call-free instructions lift through three layers; `ChildInput.segment''` checks at the original's type. Local branch only (licence). |
| 3 | `Target.Statement` (`binary-ascent/stage3/Target.lean`) proved by both arms, standard axioms, rebuilt together by the coordinator (529 jobs). |

## Stage 3: one unproved segment, two methods

`add.isra.0`, `Add.entry + 0x338` to `+0x38c` or `+0x6c0`: 22 instructions,
four stores into three trie nodes, three loads performed after the first
two stores, one conditional exit. The statement was frozen at `f9b05376`
after 3,600 executed instances, five rejected wrong postconditions and
three rejected overlapping states. Both arms started at 01:25:51 UTC.

| Measure | Direct (`c66e1cfb`) | WP (`5be715da`) |
| --- | --- | --- |
| First checked theorem about the segment | 2 min 18 s | 6 min 08 s |
| Target closed | 5 min 53 s | 6 min 31 s |
| Unsuccessful check cycles | 9 | 6, plus one warning-only |
| of which instruction execution | 0 | 0 |
| of which memory frame, alias, mapping | 0 | 0 |
| of which arithmetic, registers, exits, other | 8 (and one parse error) | 6 |
| Proof code lines / declarations | 255 / 14 | 187 / 26 |
| Warm check of the arm's file | 1.4 s | 1.1 s |
| Setup taken off the clock | 32 lines, under 1 min | 412 lines (six specs, checks, host), about 4 min, 8 failed checks |

Reading it:

- The frame and mapping conditions, expected to be the hard part, closed
  first time in both arms from the closure's existing memory rules.
- Both arms' failures were normal-form friction (literal spellings, operand
  order, register forms, the `test`/`je` condition). The WP layer removed
  the interpreter unfolding but not that friction.
- The WP arm did not use `kfinish`; it discharged 19 conditions with about
  25 ground facts and `simp`. Stage 1's ten-fold check slowdown came from
  `kfinish` and does not appear here. So stage 3 says nothing about the
  fork's automation on memory conditions.
- The WP arm's `test_zero` lemma unfolds `CondCode.interp` through a
  `show`. The brief's list of forbidden names did not include it; it is
  recorded as a boundary case, not a breach [AGENT, coordinator].
- The direct arm case-split the two bits to literals, and its shift
  arithmetic rested on lemmas the closure already had for the same
  instruction idiom. With the setup counted, the WP route cost more in
  total on this segment.
- One pair, concurrent, same model: author noise is of the same order as
  the differences. No ordering can be claimed.

## What the experiment does and does not show

Shown:

- The fork's layer is sound against Kraken's own judgement and can be
  bridged to our image step with no new premise; our closure survives the
  fork and the nightly almost untouched.
- Instruction specs are cheap to add (ten proved here, minutes each).
- Per-instruction execution is not where proof attempts fail, in either
  method, on these segments.

Not shown, in either direction:

- Any saving in authoring or discovery time from the WP layer.
- Anything about allocation identity, reconstruction of the trie after a
  mutation, entry realism or concurrency. No verdict here bears on them.
- Scaling: whole-function hosts, loops with invariants, the fork's frame
  and call rules, `kfinish` on memory conditions.

Named gaps in the external tooling:

- The fork has no rule for a call to code outside the host; ours requires
  the call instruction to occur once per host, and the same `trace_pc` call
  occurs 28 times in `Add`.
- `grind` (inside `kfinish`) loops on two of our conversion lemmas, and one
  of the fork's own examples failed 6 of 20 identical runs for the
  reviewer.
- `ascend` has no call rule, handles only whole functions that leave by
  `ret`, covers 34% of `Add`'s instructions with the rules at hand, and
  failed on straight-line programs of 280 instructions.
- Reproducibility rests on a personal fork's working branch and a nightly;
  the bootstrap script's network path is untested.

## Dispositions of the stage 1 review

| Finding | Disposition |
| --- | --- |
| S1 stage 1 exercised only straight-line stepping | Accepted. Stage 3 was the response; it too left the fork's memory and call rules unexercised, as stated above. |
| S2 the hand arithmetic is relocated, not removed | Accepted; confirmed again by both stage 3 arms. The stage 1 commit's line contrast overstated the change. |
| S3 the line and time comparison is not like for like | Accepted. The 152 and 216 line figures of the stage 1 commit message are withdrawn; stage 3's table is the like-for-like comparison. |
| S4 the fork's automation is flaky | Accepted as a finding against the tooling; our own modules passed every run. Not investigated further. |
| S5 the statement comparison cannot be re-run from the branch | Answered by the reviewer's independent rebuild and comparison (N1). No script is committed; if the port is kept, one is owed. |
| S6 reproducibility | Raised with the user. |
| S7 Ascent has no licence | Raised with the user, who keeps the code on a local branch; stage 2 is not to be pushed or merged until a licence exists. |
| S8 the external-call rule cannot serve repeated call sites | Accepted; listed above as an engine gap. |

## Replication

Everything below was run on 2026-11-10 from a fresh clone of the branch,
except the stage 2 steps, which were run only in the experiment's own
worktree. The inputs are fixed by hash:

| Input | Identity |
| --- | --- |
| Experiment branch | `task/ascent-probe`, local to the devbox holding this repository; stage 1 at `ea176fff`, frozen stage 3 statement in `09fcaa45` (scoped as `f9b05376` on `task/ascent-probe-s3`), arms `c66e1cfb` and `5be715da`, stage 2 `af17daaf` |
| Lean | `leanprover/lean4:nightly-2026-11-07` (`binary-ascent/lean-toolchain`); the landed packages stay on v4.35.0 |
| Kraken | `https://github.com/sgraf812/kraken` at `add7e55be84fe4850c12649ae8ef6cb9ca2d4b6d` (branch `vcgen`) plus the nine patches of `binary-ascent/kraken-patches/`; resulting tree `2cd5038f4cf6cf484f729aff7225dc25386d40fe` |
| Ascent (stage 2 only) | `https://github.com/sgraf812/ascent`, branch `fork/tracer`, `e3b326e86b5476949a90823113683db5b3c27fab`; no licence |
| Image | the committed decoded terms of the s5 image in `binary-ascent/closure/` (copies of `binary/`, hashes in `closure/SOURCE.txt`); the ELF is not needed |

Stages 0, 1 and 3, from a clone with the branch checked out (network needed
once, for the fork):

```sh
git checkout task/ascent-probe
binary-ascent/bootstrap-kraken.sh      # clones the fork, applies the nine patches, checks the tree hash
cd binary-ascent
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
CAPPED_MEM_MAX=24G cap lake build      # closure, bridge, specs, stage 1 sibling, stage 3 target, tests and both arms
lake env lean -Dbackward.grind.normalizer=false CheckSibling.lean
```

`scripts/in-bundle` cannot select a nightly; these commands call `lake`
directly, with the nightly installed by an ordinary elan. On the devbox of
the run the nightly was kept in an isolated elan home and selected with
`ELAN_HOME`, so that the shared one stayed untouched.

Expected, and what the fresh-clone run gave: the bootstrap reports tree
`2cd5038f...`; the build completes 529 jobs with exit 0 (125 s wall with
Kraken and the mirror built from nothing, largest process 1.9 GB), its only
warnings in the fork's own modules; every `#print axioms` line is within
`propext`, `Classical.choice`, `Quot.sound`, including
`Binary.Stage3.Direct.target` and `Binary.Stage3.WP.target`;
`TargetTest` (the 3,600 executed instances and the rejected variants) is
part of the build and fails it on a wrong expectation; `CheckSibling.lean`
exits 0, reports the sibling's type as the same term as the client's and
none of the sixteen forbidden constants in its closure.

What a replication does not re-run: the arms' elapsed times (they are a
record of two agent runs, in the arms' commit messages and this report),
the scoping worker's test grid beyond what `TargetTest` encodes, and the
reviewer's v4.35.0 comparison (no script is committed).

To repeat stage 3 as an experiment and not as a build: start two workers
from `f9b05376` in separate worktrees, hand each
`binary-ascent/stage3/BRIEF.md` unchanged with its arm named, and compare
their records; the charter's stage 3 section has the rules.

Stage 2 (`binary-ascent/ascend/`), after the steps above, from the
repository root:

```sh
git clone -b fork/tracer https://github.com/sgraf812/ascent .tmp/ascent    # e3b326e
ln -s kraken-vcgen .tmp/kraken-ascent-demo
# in .tmp/ascent/demo: lakefile.toml gains a [[require]] of binaryAscent at
# ../../../binary-ascent, and Demo/Kraken.lean a first line `import KrakenMatchers`
cd binary-ascent/ascend && lake build
lake env lean -Dbackward.grind.normalizer=false CheckSibling2.lean
```

Expected: 633 jobs, exit 0; the check exits 0 with the standard axioms for
`ChildInput.segment''`.

Known fragility: the fork's branch may be rebased or deleted upstream (the
patches then need the base commit from another copy); one of the fork's own
AArch64 examples failed nondeterministically for the reviewer when the
whole fork was built, though not in the builds above, which do not need it;
a nightly toolchain is not kept available indefinitely.
