# Independent review: the Ascent / Kraken-WP probe, stage 1

Reviewed: branch `task/ascent-probe` at `ea176fff` (four commits over main
`d45c9ddb`: `c31854f0` charter, `26305975` stage 0a, `2b36dc15` stage 0c,
`c00294bb` stage 1a, `ea176fff` stage 1), in a separate worktree
(`.worktrees/ascent-probe-review`, branch `task/ascent-probe-review`) with
its own patched Kraken checkout, rebuilt from the fork clone and the
committed patches. Inputs read: the charter, the image-bridge design,
`binary-ascent/README.md`, `binary-ascent/kraken-patches/README.md`, all of
`binary-ascent/wp/`, `CheckSibling.lean`, `CheckClient.lean`,
`closure/KrakenMatchers.lean`, the old proofs of the client in `closure/`,
the four commit messages, and the differences between the landed Kraken pin
(`8af7806` plus `binary/kraken-patches`) and the fork (`add7e55` plus
`binary-ascent/kraken-patches`).

## Verdict

**The theorem can be believed. The cost conclusion cannot be built on yet.**

`ChildInput.segment'` is a kernel-checked theorem at the type of
`ChildInput.segment`, with the standard axioms, and the statement is the
landed one as far as I could test it: I rebuilt the landed closure on
v4.35.0 against the landed pin and compared it with the experiment's build
declaration by declaration (finding N1). Nothing I found makes the result
false or the commits dishonest; the commit messages name most of the
limits themselves.

What stage 1 does not show is the thing the charter asks. Ten straight-line
instructions, one conditional exit and one call to code outside the host
went through the fork's layer. Framing, the callee's contract, call setup
and the reconstruction of `Frame` stayed in the closure's own lemmas, the
address and width arithmetic is still supplied by hand, the proof is about
ten times slower to check, and the external-call rule written here cannot
serve a host with two call sites to one callee, which is every function of
the image (S1 to S4). Read against the charter's verdict forms this is
"usable with named engine gaps" at best, on a narrow client; the stage 1
commit states no verdict, and it should before stage 2 is decided.

Two matters need the user rather than a fix: the reproducibility of the
external pin (S6) and Ascent's missing licence (S7).

## Checks run

All in the review worktree or a second detached one, heavy jobs through
`capped`, the nightly from `ELAN_HOME=/tmp/ascent-assess-182411/elan`,
v4.35.0 from the installed toolchain (read only).

| Check | Result |
| --- | --- |
| Clone of the local fork clone at `add7e55`, `git am binary-ascent/kraken-patches/*.patch`, `git rev-parse 'HEAD^{tree}'` | `2cd5038f4cf6cf484f729aff7225dc25386d40fe`, as recorded; `bootstrap-kraken.sh` then accepts the checkout. Its network clone path was not exercised |
| `capped -m 24G -- lake build` in `binary-ascent/`, from nothing | PASS: 489 jobs, exit 0, 2 min 9 s wall, largest process 1.9 GB. No warning from `closure/` or `wp/`; 50 from Kraken modules (S6) |
| `lake env lean CheckClient.lean` | type printed; axioms `propext`, `Classical.choice`, `Quot.sound` |
| `lake env lean -Dbackward.grind.normalizer=false CheckSibling.lean` | exit 0; both type checks pass; 10,467 constants in the sibling's dependency closure; none of the 16 forbidden; axioms standard |
| `CheckSibling.lean` with the root changed to the old `ChildInput.segment` | check 3 fails and names `child_step`, `child_guard`, `child_move`, `region_eventually`, `call_instruction` and five monotonicity lemmas: the check is not vacuous |
| `capped -m 16G -- lake env leanchecker --fresh WP.Client.Segment` | exit 0, 91 s: the kernel replay of the sibling and everything under it passes |
| `python3 binary-ascent/import-closure.py --check` and `--diff` | originals match `SOURCE.txt`; 13 modules, +23 −0, as the README says |
| Landed closure rebuilt: `lake +leanprover/lean4:v4.35.0 build AllowedipsPlacementSaved` in `binary/` of a detached worktree, Kraken = `8af7806` plus `binary/kraken-patches` | PASS, 220 jobs |
| Types of the closure's declarations and values of its definitions, pretty-printed in both builds and compared (N1) | 2,365 types equal; 1,007 definition values equal up to one bound-variable name in 4 |
| `pp.explicit` and `pp.universes` print of `ChildInput.segment`, `ChildInput.follow`, `ChildInput`, `Frame`, `AllowedipsTracePcContract`, `AllowedipsServiceReturns`, `instructionStep` in both builds | byte-identical (40,675 bytes each) |
| All 313 `parse("…")` strings of the closure's image modules through the pin's parser (v4.35.0) and the fork's (nightly), `repr` compared | identical |
| Scan of the 7,070 closure and `wp/` constants for a reference to an `instDecidableForall` instance | none, as the README says |
| Full `lake build` of the patched fork (the 188-job default target) | **FAIL on the first run**: 187 of 188, `Kraken.AArch64.Examples.Examples` (S4) |
| `python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm` in the patched fork | 51/51 |
| Old and rebased patch series compared hunk by hunk | differences are those the patches' README lists (N3) |
| Timings, a profile, a prefix series and one ablation of `follow_wp` | S2, S3 |

Not run: the 2,945-declaration comparison the README cites (no script for it
is committed; mine is a separate implementation with a different count, see
S5); the network clone in `bootstrap-kraken.sh`; anything of stage 0c
(Ascent's build, its demo, its timings); `lake check`; the proof gate and
the differential check (the branch touches neither the mirror nor the proof
tree: `git diff --stat d45c9ddb ea176fff -- Leanux binary scripts AGENTS.md
lakefile.toml` is empty).

## Findings

### Should fix or settle before the result is built on

**S1. Stage 1 exercises a small part of what the charter asks about, and
states no verdict.** The charter's question is whether the fork's layer
(specs, `vcgen`, function specs, call and frame rules) removes the
per-instruction and bookkeeping cost. What went through the fork is the
straight-line part only:

- `follow_wp` (`wp/WP/Client/Segment.lean:42`) has the hypotheses of the old
  `child_step` (`closure/AllowedipsPlacementChild.lean:13`), word for word:
  the two reads after the store are already given over `parentMemory s`. The
  fork never has to reason about a load after a store at a possibly
  aliasing address. Its memory rules are untested.
- `ChildInput.follow'` (`Segment.lean:121`) repeats the first 25 lines of the
  old `ChildInput.follow`: every separation and frame fact comes from
  `frame.memory.loadInt`, `frame.after_parent`, `query_frame`, as before.
- The callback is not a call in the fork's sense. `call_image` runs one
  instruction and stops at the callee's entry; the callee's contract is
  applied by the closure's `Frame.region_callback`, on the image side. The
  fork's `FunDecls`, call rule and frame rule are not used.
- By count: the sibling's dependency closure still holds 530 constants of
  the closure where the old proof's holds 585 (my scan, same traversal as
  `CheckSibling.lean`). The execution-typed closure theorems it still uses
  are `instruction_mono`, `history_project`, `CommonBitsCoverage.callback`,
  `CommonBitsCoverage.region_callback` and `Frame.region_callback`.

The stage 1 commit message says the last three points in its closing
sentence, so nothing is hidden. But the charter's "usable" form requires
frame facts handled by shared rules, which did not happen, and the commit
gives no verdict in the charter's terms. On this evidence the verdict is
"usable with named engine gaps" for straight-line fragments, and
"unmeasured" for calls, frames, loops and whole functions. Say so in the
stage report, and do not open stage 2 on the reading that stage 1 closed
cleanly.

**S2. The hand arithmetic is still there and is load-bearing; the six-line
figure understates it.** The body of `follow_wp` is five `have` lines and
`vcgen [follow] with kfinish [parentMemory]`. The five facts are the old
proof's hand lemmas in a new place: `byte_count32` is the old `shiftMask`,
`byte_low32` and `byte_zext64` the old `extend8` instances, `child_addr` the
old `childAddr`, and `sar_bit` / `bit_zero` the old `shift_mod` step. Each
is instantiated by hand at the exact term the verification condition will
contain. I removed one (`child_addr`) from a copy with trivial posts:
`kfinish` fails after 8.9 s with ``finish has failed after reaching the
thresholds (gen := 8) and (ringSteps := 100000)`` and nothing that names the
missing fact. So:

- the address and width arithmetic the 21 October diagnosis names is not
  removed, it is moved into `wp/WP/Adapters.lean` (43 lines) and two client
  lemmas (12 lines), and the author must know the form the condition takes;
- the failure mode when a fact is missing is slow and uninformative;
- the proof was written with the finished old proof beside it, so the cost
  of finding those five facts is not in the measurement. The charter lists
  "unsuccessful check cycles" as a measure; the commit does not report it.

"Six lines against about fifty" compares a tactic call with a `simp` set. A
like-for-like count is `follow_wp` with its inputs (5 + 1 lines, plus 55
lines of adapters) against `child_step`'s body of about forty lines.

**S3. The line and time comparison is not like for like, and supports no
extrapolation.** The commit gives 216 lines against 152 and about 5 s
against 0.6 s.

- 216 is `WP/Client/Host.lean` (50) plus `WP/Client/Segment.lean` (166).
  152 is `AllowedipsPlacementFollow.lean` (84) plus
  `AllowedipsPlacementSaved.lean` (68). The 152 includes the three
  `SavedInput` lemmas, which are not the client, and leaves out
  `child_step` (`AllowedipsPlacementChild.lean`, 65 lines), `child_guard`,
  `child_move`, `Frame.call` and the four layout theorems, all of which the
  sibling replaces. Neither figure includes the 715 generic lines of `wp/`
  (bridge 511, specs 153, adapters 43, root 8), which is a fair omission
  only if they are reused.
- Time, three warm runs each of `lake env lean` on one file, about 0.5 s of
  which is imports: `Segment.lean` 5.1 to 5.7 s; `AllowedipsPlacementChild`
  0.80 to 0.82 s; `AllowedipsPlacementFollow` 0.54 to 0.61 s;
  `AllowedipsPlacementSaved` 0.54 s. Less imports that is about 4.8 s
  against about 0.5 s for the three old files together. The "ten times"
  figure holds; it is not an overstatement of the slowdown.
- Where the time goes (`-Dprofiler=true`): 2.75 s in `grind`, of which
  0.78 s e-matching and 0.58 s the ring solver.
- It is not a per-instruction cost. I ran `vcgen … with kfinish` on prefixes
  of the fragment with posts `True`, same hypotheses: 2 instructions 0.62 s,
  4 0.84 s, 6 0.87 s, 7 1.66 s, 8 1.62 s, 10 1.68 s (wall, with imports).
  The seventh instruction (the scaled-index load) costs 0.8 s by itself;
  the real posts add a further 3.5 s over the trivial ones. Cost follows
  the conditions `grind` has to close, and the `sar` count split doubles
  them.

Nothing here predicts the cost of a 500-instruction function. The fork's
own bench in the design note (section 7) grows eightfold for a fourfold
input. Record the comparison with the same things on both sides, and call
scale unmeasured.

**S4. The fork's automation is not deterministic on this toolchain, and its
default build does not pass reliably.** Stage 0a reports that the patched
fork builds (188 jobs). My full `lake build` of the same tree failed:
`Kraken/AArch64/Examples/Examples.lean:57:2: grind has failed after reaching
the threshold (gen := 8)` (`swap_correct`, the fork's own example, untouched
by our patches). Repeating: `lake build Kraken.AArch64.Examples.Examples`
failed once more and then passed; of twenty direct `lake env lean` runs of
the file, six failed with that error (3 of 12, then 3 of 8). Same source,
same toolchain, same options.

The sibling itself passed 20 of 20 direct runs, and the module is outside
what `binary-ascent` builds, so the result is not in doubt. The relevance
is to cost: `kfinish` is `grind`, and a finisher that fails one run in four
or so on a three-instruction example is a risk for a tree of hundreds of such
proofs under a gate. It also means the command in
`kraken-patches/README.md` (`lake build`, "default targets: 188 jobs") can
fail for a reader through no fault of theirs. Record the flake, and report
it to the fork's author with the rest of the gaps.

**S5. The "same statement" claim holds as far as I could test it, but the
experiment's own evidence for it cannot be re-run, and two parts of it rest
on reading.** The README says 2,945 public declaration types were compared
between a v4.35.0 build and this one. No script, command or output for that
is in the branch. I built an independent comparison (N1) and it agrees, with
a different count (2,365 after dropping compiler-generated names), so I
believe the claim; but a conclusion without the command that reproduces it
is what the standing rules ask us not to keep. Commit the comparison as a
script beside `import-closure.py`, or cut the number.

What no textual comparison covers, and what the README's caveat should
name beside the `Directives.interp` default:

- Kraken's definitions under the same names differ between the pin and the
  fork. In `Kraken/X64/Semantics.lean`: `Operation.push` stores before it
  commits `rsp` (the pin commits first); `CondCode` has six more
  constructors in another order; `Reg64s.get64` / `set64` are typed
  `BitVec 64` where the pin wrote `Width.W64.type`; eleven AVX operations
  are added; `Directives.interp` has the extra continuation. The parser's
  `cmov` case is rewritten. I read each: `push` gives the same final state
  and the same effects (the store touches only `dmem`), the two condition
  codes our patches added have the fork's meaning, and the parser gives the
  same terms on all 313 strings of the image. That is an argument and a
  test, not a theorem. `kraken-patches/README.md` mentions the `push`
  reorder only in passing, under patch 5.
- The core library between v4.35.0 and the nightly (the definitions of
  `BitVec`, `Int64`, `List` operations the statement uses) was not compared
  by the experiment or by me.

The charter already calls the pin a trust-surface change. The stage record
should list these differences as its content.

**S6. Reproducibility from a clone rests on two things outside the
project's control; the README's warning count is stale.**

- The base is commit `add7e55` of a personal fork's working branch
  (`sgraf812/kraken`, `vcgen`), 383 commits beyond the landed pin. If that
  branch is rebased or the fork removed, `bootstrap-kraken.sh` cannot make
  the checkout and nothing in `binary-ascent/` builds. The script's clone
  path has not been run by anyone (stage 1a says so); I ran the rest of it
  from a local clone and the tree hash matches.
- The toolchain is a nightly. Whether `nightly-2026-11-07` stays
  downloadable is not something this project decides.
- `binary-ascent/README.md` says Kraken's modules print five warnings. That
  was true of the closure's imports at stage 1a. With `wp/` the build
  compiles the fork's `WP`, `Blocks`, `Specs`, `StateCfg` and `Registers`
  modules: 50 warnings (deprecated `if_pos` / `dif_pos` names, unused
  variables and `simp` arguments), all in the fork's own code at its base
  commit, none in our patches' lines.
- The root `.lake` hazard (the package builds the mirror with the nightly
  into the checkout's root `.lake`) is documented in the README and is
  real: nothing but the warning prevents a v4.35.0 build in the same
  worktree from mixing with it.

For an experiment on a branch this is acceptable and mostly disclosed.
Before any of it is proposed for `main`, the pin needs a source the
project can rely on (the user's call: a mirror, a bundle, or waiting for
the layer to reach upstream Kraken), and the README needs the true count.

**S7. Ascent carries no licence; raise it before stage 2 produces anything
to keep.** Kraken and the fork are MIT (`LICENSE`, copyright AeneasVerif),
so the rebased patches are in the same position as the landed
`binary/kraken-patches`. The Ascent clone (`sgraf812/ascent` at `e3b326e`)
has no `LICENSE` file and no licence statement in its README or lakefile.
Building it locally is within what the user approved. Committing code
copied or adapted from it, or patches against it, into this GPL-2.0-only
repository is not something the project can do on its own reading; nothing
of the kind is in `ea176fff` (no file under `binary-ascent/` mentions
`ascend`), but stage 2 is exactly where it would appear. This is the
user's decision, and probably a question to Ascent's author.

**S8. The external-call rule cannot serve a host with two call sites to one
callee.** `call_external_image` (`wp/WP/Bridge/CallExternal.lean:75`)
requires `onlyAt`: the call instruction occurs once in the host. The
reason is given in the file: `Program.wp` quantifies over every embedding
of the instruction, so the pushed return address is only known to be the
end of some embedding. `call L_ffffffff810f31f0` occurs 28 times in
`AllowedipsMutationImage.Add` alone. A whole-function host, which is where
the layer's labels, loops and invariants would start to pay, cannot use
this rule; each call site would need its own host, or the rule a different
formulation. The commit names the restriction; its consequence for the
next client belongs in the list of engine gaps, near the top.

### Notes

**N1. The landed statement and the ported one agree, by an independent
comparison.** In a second detached worktree I built
`binary/AllowedipsPlacementSaved` and its imports on v4.35.0 against
`8af7806` plus `binary/kraken-patches` (220 jobs), and in each build ran one
Lean file that walks the modules outside Kraken, the mirror and core and
prints, for every constant that is not compiler-internal, its kind, name
and pretty-printed type (`pp.fullNames`), and for definitions the value.
After dropping generated names (`eq_N`, `match_N`, `congr_eq_N` and the
like, whose number and form differ between the toolchains), 2,365
declarations are common to both builds, none is in one only, and all 2,365
types are textually equal. Of 1,007 definition values, 1,003 are equal and
4 (`AllowedipsImage.cutPoints`, `Image.cutPoints`, `ServiceImage.decoded`,
`ServiceImage.listing`) differ in one bound-variable name (`y` against
`x`). The values include every image region, `Add.fetch` and
`Image.linkedLabels`. With `pp.explicit` and `pp.universes` the client, its
`follow`, `ChildInput`, `Frame`, the PC contract and `instructionStep` print
byte-identically. The limits are those of S5.

**N2. `CheckSibling.lean` checks what it says, within stated limits.**

- Check 1 compares `ConstantInfo.type` and the universe parameters
  structurally. Since both siblings are declared `type_of% @original`, it
  can only fail if that elaboration misbehaves; it is a guard, not
  evidence, and it compares with the ported constant, not the landed one
  (N1 covers that).
- Check 2 traverses types and values, including theorem proofs, and its
  self-test confirms it reaches `child_step` through the old proof. The
  forbidden list is hand-written; check 3 is what makes an omission from it
  harmless.
- Check 3 flags a closure theorem only if its proof term names one of
  thirteen interpreter functions directly. It skips definitions and every
  module of Kraken. On the old proof it flags ten theorems, so it has
  teeth. `Binary.instruction_mono`, the one exemption, is as described: it
  unfolds `instructionStep` and applies `all_mono`, and looks at no
  instruction. My own scan by type (theorems whose statement mentions the
  step or `Eventually`) finds no execution lemma the check misses.
- The file is run by hand; `lake build` does not run it. For an experiment
  that is proportionate.

The sibling depends on more than the original, not less: 10,467 constants
against 8,040, of which 1,569 are Kraken's against 558. All are
kernel-checked, so this is exposure to the fork's churn, not to unproved
claims.

**N3. The rebased patches keep the instruction meanings of the landed
series.** Comparing added and removed lines patch by patch: 2, 4, 8 and 9
are line-identical; 1 and 6 drop the `js` and `jg` hunks, which the fork
has with `s.sf` and `!s.zf && (s.sf == s.of)`, the landed definitions; 1, 6
and 7 add naturality lemmas and case splits in `Kraken/X64/WP/Step.lean`; 5
threads the new `system` field through projection lemmas; 3 is weaker, as
its README says. The eight in-patch test modules compiled in my full build
of the fork (only the AArch64 example failed) and the native suite passed
51/51. The two `sorry` declarations of `Kraken/X64/Examples/Examples.lean`
are compiled by the fork's default target and by nothing `binary-ascent`
builds: no module in the 489-job build contains the token.

**N4. The four specs are consequences of the interpreter, and say no more
than it.** All are proved by unfolding `Directive.interp` down to
`Operation.interp` and print the standard axioms. `sar_reg32_cl_interp` is
an equivalence, so its spec loses nothing. The two `movzx` specs and
`and_reg32_imm` are implications with a mapped-ness precondition, in the
fork's style; they are sound and narrower than the instruction (`movzx`
only at 64-bit address size, base plus displacement or base plus index at
scale 1, into a 32-bit register). A wrong spec could not have been proved;
an over-narrow one fails to apply, which is a cost and not a risk.

**N5. The bridge adds no assumption.** `Agrees` runs one way (each
positive-size host instruction is the image's instruction at that address
with the same size and meaning), `eventually_of_step1` carries a host
execution to the image, and the gaps are byte-array directives with a
declared size whose step is `False`. The host of the client starts at the
callee's address, 2.8 MB below the segment, so that the callee's label
resolves to its real address; the six `Host` side conditions come from one
`decide +kernel` (kernel evaluation, no added axiom; `binary/` uses the
same in 32 files). Label agreement is needed and proved for the two labels
the fragment names. I found nothing checked by `native_decide`, no
`sorry`, no `unsafe`, `implemented_by` or `extern`, and no resource raise
anywhere in `wp/`.

**N6. Standing rules.** The branch changes nothing under `Leanux/`,
`binary/` or `scripts/`, and nothing in `binary-ascent/` imports the proof
tree. The decision entry in `docs/decisions.md` separates the user's
approval from the coordinator's choices and paraphrases; I found no quoted
user text in the documents or commit messages. The box path of the nightly
appears in the charter and the design note as a fact about the run, not as
a requirement; the README tells a reader on another machine to use elan.
The stage 0c scratch package is not preserved, as the design note says;
stage 1's `wp/` supersedes it. The design note's sentence that check time
is not a concern at this scale was written for a four-instruction fragment
under two seconds and should be corrected by stage 1's figure.

## What I did not verify

- The clone from GitHub in `bootstrap-kraken.sh`, and that `add7e55` is
  still the head of `vcgen` there.
- Any stage 0c figure (Ascent's build, its demo's axioms, its timings, the
  fork bench).
- The README's own 2,945-declaration comparison and its count of eight
  statements that mention `Directives.interp`.
- The equivalence of core library definitions between v4.35.0 and the
  nightly.
- Whether the AArch64 failure of S4 also occurs at the fork's unpatched
  head (our patches do not touch that file or its imports' AArch64 side,
  but I did not build the base).
- The fork's soundness theorems beyond what the kernel replay and the axiom
  print establish for the constants the sibling uses.
- Anything of stage 2, which the worker was writing during this review.

## Housekeeping

The second worktree (`.worktrees/ascent-probe-review-v435`) and the build
outputs of the review (`.lake` directories, the two Kraken checkouts under
`.worktrees/ascent-probe-review/.tmp/`) were removed after the run. The
review's small Lean and Python scripts were scratch and are not kept; each
is described above closely enough to rewrite.
