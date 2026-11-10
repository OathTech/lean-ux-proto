# Independent review: landing result C2, the receive replay window

Reviewed: branch `task/binary-c2` at `42d63cb2` (44 commits over `c4b66700`;
the whole branch is main `4fbcc1eb..42d63cb2`: 54 commits, 51 files, +9,139
lines), in my own worktree `.worktrees/review-c2-landing` on `task/review-c2-landing`.
Inputs read: the closing report and the final statement on the branch, the
2026-11-10 decisions, the statement packet's review and its follow-up,
`binary/README.md`, the register rows, the AGENTS.md and gate diffs, the
tenth Kraken patch in full, `C2Statement`, `C2Image`, `C2Cut`,
`C2CutInterfaces`, `C2CutAssembly`, `C2Headline`, the bridge, the witness
part of `C2Sequences`, the generator, and the saved s5 image's disassembly.
Judgements are mine [AGENT, reviewer].

## Verdict

**Land with named changes.** The result is what it says it is. The closed
theorems have the types of the statement the owner was shown, byte for byte;
I rebuilt every C2 module, the two touched invariants, the four proof-tree
modules and the bridge from source on a Kraken I reconstructed from upstream
plus the ten patches, and the closure is accepted on the three standard
axioms, by the build and again by the replay checker run as a diagnostic. I found no way in which the proofs mean less than their
types. The limits are stated honestly where a reader meets them first
(`binary/README.md`, the closing report).

What does not hold up is part of the gating around the result, not the
result:

- **The headline theorem is in no gate as a statement** (S1). The bridge
  gate passes when `headline` is restated as one clause and the transported
  clause as `True`. I ran that.
- **The four-module limit is enforced on spelling only** (S2). Three
  spellings of an import that Lean accepts pass step 4 of the proof gate in
  any file, a file of the binary package included; the fix the integrator
  proposes covers one of the three.
- **The branch holds no record of the owner's signature** on the final
  statement, which its documents call signed (S3).

The named changes, all small: S1, S2 and S3 before or with the merge; S4 to
S8 at the owner's choice; the owner's kernel replay outside the sandbox, on
a tree built from the merged source (N2 says why that qualifier matters).

## Checks run

All in my worktree. Heavy jobs through `capped` at 16G or less, except
where N4 says otherwise.

| Check | What I did | Result |
| --- | --- | --- |
| Kraken pin from upstream plus ten patches | `binary/run.py --bootstrap-only` in a worktree with no `.deps` (clones the main checkout's staged upstream, applies the ten patches) | HEAD `96d484872c2c438a4d02f47e6390507f587a095c`, equal to the lock and `TrustBase.krakenCommit`; `verify_pin` accepts |
| Binary package build | Copied `.lake` and `binary/.lake` from the reviewed worktree, deleted the outputs of every `C2*` and `CallbackCmp8*` module, of `MemoryInvariant`, `SystemInvariant` and of the four `CounterWindow` modules, then `lake -d binary build`. Kraken itself was built fresh (no copied output) | 1137 jobs, exit 0, no warning. Compiled here: the 13 Kraken modules the package imports, the 18 C2 and callback modules, `MemoryInvariant`, `SystemInvariant`. Taken from the copy (replayed, not recompiled): the rest of the landed package |
| Bridge build | `lake -d binary build C2Bridge` | 130 jobs; the four `CounterWindow` modules and `C2Bridge` compiled here; five theorems on `propext`, `Classical.choice`, `Quot.sound` |
| Binary gate | `scripts/binary-proof-gate` | PASS: pin, 1137 jobs, 74 terminal statements on the standard three, surface diff PASS, no forbidden token |
| Bridge gate | `scripts/c2-bridge-gate` | PASS: five theorems on the standard three; lag report `b32bb164`, `1b7a3b70`, `218d3ffd`, no mirror file differs |
| Bridge gate, my mutant | `headline : ExitsCleanly`, `no_counter_accepted_twice : True` | **PASS** (finding S1) |
| Proof gate, step 4 alone | `check_imports` at the head; then with a scratch file in `binary/` importing three proof-tree modules in three spellings (Lean compiled it) | 0 findings at the head; **0 findings with the scratch file** (finding S2) |
| Transitive imports of the bridge | a scratch `#eval` over `allImportedModuleNames` of `C2Bridge` | 2500 modules; of the proof tree exactly `CounterWindow.Model`, `.Refinement`, `.MirrorCalls`, `.Bounds` |
| Signed text against the file | every declaration in section 1 of the final statement searched verbatim in `binary/C2Statement.lean` at `8200bf7e` and at the head | 22 of 22 present in both; the only change to the file since is `14f53df5` (N5) |
| Image terms against the ELF | `binary/generate_c2.py --check` on `.artifacts/kernel-net-choice-s5`; and my own `objdump -d` of the range read beside `C2Image.lean` | "matches the pinned ELF", 70 instructions, 324 bytes, 13 call sites; the listing agrees line for line |
| Image terms, my mutant | `and $0x3f,%r15d` changed to `and $0x3e,%r15d` in `C2Image.lean`, then `lake -d binary build C2Headline`; reverted | build fails at `C2RangeRegions.lean:75`: the proofs do depend on the term |
| Printed surface counts | `binary/packets/c2/surface` | 120 assumed, 111 claimed, 9 other, as reported |
| Patch ten's own tests | `lake build Kraken.X64.BtsTests Kraken.X64.BtTests` in the reconstructed Kraken (S5) | built: every `#guard` holds |
| Cut tests | `binary/packets/c2/proof/check` | exit 0: 2,925 cases; 512 runs, 41,760 calls, 18,544 loop iterations, every cut predicate held. Equal to the report |
| Statement tests | `binary/packets/c2/check` | exit 0. Every count equals the report's and the final statement's table: 972 runs, 564 accepted, 0 failures; the eleven wrong variants fail 16, 8, 56, 160, 216, 112, 112, 108, 108, 112, 108 of 216; six sequences, 465 visits, 2, 8, 145, 143, 113, 3 accepted, with the sequence variants caught on 6, 6, 0 and 2 of 6; search 775 and 921 layouts, broken on 0 and replay accepted on 0 under the revised `Context`; capacity loop 28,568 states, 9,442 meeting the revised `Context`, broken on 0, replay accepted on 0 |
| Kernel replay, diagnostic | `lake env leanexport C2Headline C2Bridge`, then `lake check --from-export … --inadvisably-no-sandbox` | export exit 0, 17,824,663 lines, 1,095,410,711 bytes, the report's figures exactly; "Lean default kernel accepts the solution", axioms `propext`, `Quot.sound`, `Classical.choice`. Not trustworthy by its own banner (sandbox disabled). This is my second export; N2 says what the first one was. Export deleted |
| Mirror and proof tree untouched | `git diff 4fbcc1eb 42d63cb2 -- Leanux` | empty |

Not run: the whole proof gate (the tree it builds is unchanged from main and
only its step 4 changed, which I ran alone); the mirror build and the unit
tier (no mirror file changed); `test_bts.S` in Kraken's assembly runner and
`bts_host.c`; the two one-off mutants of the patch; anything in a guest; the
replay outside the sandbox, which is the owner's. I did not read AMD's
manual. Intel's flag rule for BTS (CF the old bit, ZF unaffected, OF, SF, AF
and PF undefined) I checked against a public rendering of the SDM page
(felixcloutier.com/x86/bts), not the SDM itself.

## What I conclude about the proofs, and how

The three packages took 15 to 42 minutes each and the integrator did not
re-derive them. Neither did I, and it is not needed for the claim. The five
closed theorems take no hypothesis, and their axioms are the standard three.
So every intermediate device (the pivot `validate`, `Carried`, the cut
predicates, the 25 interface propositions, the window representation) is
inside a kernel-checked term. If one of them were trivially true or had an
unsatisfiable hypothesis, the theorem that uses it would still have to
produce `Refines` or `ExitsCleanly` at the stated type from nothing, and
could not. What can be wrong while everything checks is therefore only the
statement, the reading of the image, and the semantic base. I spent the
time there. (The speed is less strange than the report leaves it: the
briefs point the provers at trial T3 on `task/binary-trials`, which had
per-region executions, the index arithmetic and the loop induction for the
same instructions up to the `bts`, and the cut predicates had been executed
against Kraken at every cut before a prover started. I did not check how
much of T3 was reused.)

- **The statement.** Read with every definition it mentions.
  `Eventually` is Kraken's inductive (least fixed point), `historyStep`
  appends each actual successor, `Effects.All` is false on a fault, an
  unimplemented instruction and a missing decode, and quantifies over every
  undefined value: `ExitsCleanly` and `Refines` are total-correctness
  claims. `Refines` concludes the exit, the first-exit property, the
  acceptance byte equal to the mirror's result, the window bytes
  representing the mirror's new state, and `Kept`; none of these is
  weakened by a definition. `accepted` is `pc = donePC ∧ %bpl = 0`, which is
  what the image tests after the range (`test %bpl,%bpl; jne` at
  `…d3ff`/`…d402`), and both rejection exits fall into the drop path
  (`…d80d`, `…d9c3`, then `wg_noise_keypair_put`). `exitPC` and the
  constants agree with `receive.c` (`REJECT_AFTER_MESSAGES` =
  `0xffffffffffffe03e`, window `0x1fc0`, 128 words, counter at `kp+0x88`,
  bitmap at `kp+0x90`).
- **The witness.** `Witness.reading` proves a decoder exists that meets
  `Reading` (the range's terms, else the landed service image; the two
  decode disjoint addresses, by `decide +kernel`). The entry state is
  concrete: coverage in PC-recording mode with a 64-word buffer, preempt
  count `0x100`, a zero window, packet counter 5. The second visit enters
  at the first visit's exit state with the program counter put back, at
  preempt count `+0x200`. That is a state the kernel is never in; it is a
  fair witness that `Visits` is satisfiable and that accept-then-refuse
  happens, and no more than that. `C2CutAssembly` says so; the closing
  report's "a concrete state" is shorter than the fact.
- **`decide +kernel`.** Seven uses, each a closed decidable fact evaluated
  by the kernel (two label values, a side condition of the range's layout lemma, disjointness of
  the two images, placement of the witness regions, the pivot on the two
  witness inputs). None adds an axiom; `Lean.ofReduceBool` appears nowhere.
- **Rendering or object.** The search's `contextHolds` is a rendering of
  `Context`; the reviewer of the packet asked that it be re-read (F2). It
  no longer carries weight: the theorems quantify over `Context` itself.
  The witness's Boolean `wellPlaced` is connected to `Context` by proved
  lemmas, since `witness_start` has the type `WitnessStart`.
- **The instruction terms.** The proofs reach the 70 instructions only
  through `RangeDecoderAgreement` on `Range.fetch`, whose text the
  generator compares with the ELF bytes row by row, with every branch
  encoding against its target, and with the alternatives table. The
  neutral copy of the two callback entries is not a second assumption:
  `stubs_agree` derives agreement with it from agreement with the range's
  terms.
- **The join failure** (`06276248`). It was a name clash and nothing else.
  The diff is two lines in `C2Callbacks.lean` (the declaration and its one
  use); package 2 does not import package 1's module, so each package's
  lemma kept its own meaning, and Lean would have refused a second
  declaration of either name. The cut files (`C2Cut`, `C2CutInterfaces`,
  `C2CutAssembly`) have no commit after `c4b66700`, where the packages
  started; the three merges add only package files
  and, in package 2's, the list of roots.

## Findings

### Should fix before or with the landing

**S1. The bridge's headline is checked for axioms and not for what it
states.** `scripts/c2-bridge-gate` prints the axioms of five names and
compares the set of `theorem` names with its list. It never looks at a
type. The binary gate pins `exits_cleanly`, `refines` and `replay_witness`
by `#check` in `TrustSurface.expected.txt` (lines 1589 to 1591) and pins
the definition `HeadlineRefinement`; nothing pins
`Binary.C2.Bridge.headline : HeadlineRefinement` or
`no_counter_accepted_twice : NoCounterAcceptedTwice`. Mutant, run in my
worktree and reverted:

```lean
theorem no_counter_accepted_twice : True := trivial
theorem headline : ExitsCleanly := exits_cleanly
```

Result: `c2 bridge gate: PASS`, exit 0, with `no_counter_accepted_twice: no
axioms` printed. The kernel replay does not pin it either: `lake check
--from-export` reports acceptance and axioms, not statements (N2). So the
track's headline, the one theorem the rule change exists for, could be
weakened by an honest refactor and every gate would stay green. Fix, a few
lines: the bridge gate runs `#check @Binary.C2.Bridge.headline` and
`#check @Binary.C2.Bridge.no_counter_accepted_twice` in its scratch file
and compares the two printed lines with the expected text
(`Binary.C2.Bridge.headline : Binary.C2.HeadlineRefinement`,
`… : Binary.C2.NoCounterAcceptedTwice`); AGENTS.md's sentence about the
gate gains "and their statements". Severity: medium. This is the
packet reviewer's M3 point ("unless a named gate builds the bridge and
checks its axioms, the track's headline is in no gate") met in the letter.

**S2. "Nothing else of the tree" is enforced on the spelling of one
line.** Step 4 of `scripts/proof-gate` matches `^import\s+Leanux\.Proofs…`
per line, without stripping comments. The integrator reports that `public
import` passes. So do three spellings that need no module system. A scratch
file `binary/ReviewScratch.lean`:

```lean
import C2Headline
 import Leanux.Proofs.WG.CounterWindow.Bounds
import C2Cut import Leanux.Proofs.WG.CounterWindow.Model
/- x -/ import Leanux.Proofs.WG.CounterWindow.Refinement
#check @Leanux.Proofs.WG.CounterWindow.accepted_nodup
```

Lean 4.35 compiles it (the `#check` prints the theorem) and
`check_imports` reports 0 findings. The fix proposed in the closing report
(item 6) catches the indented line and misses the other two. The bridge
gate is stricter about the bridge's own import lines (it fails on any line
it cannot read), but it accepts any module of the binary package, and a
package module can carry such a line, so the bridge can reach any part of
the proof tree through the package with both gates green. The weakness in
step 4 is older than this branch and the branch's pattern matches exactly
the lines the old one did (I compared them); what is new is that a
standing exemption now leans on it. At the head the condition does hold:
the bridge's transitive imports from the proof tree are exactly the four
(table above). Fix, either of:
- in step 4, search the comment-stripped text (the gate already has
  `strip_comments`) for `\bimport\s+(?:all\s+)?Leanux\.Proofs` anywhere,
  not per line from column 0;
- in the bridge gate, ask Lean: a scratch `#eval` listing
  `allImportedModuleNames` under `Leanux.Proofs` after `import C2Bridge`,
  required to equal the four. This checks the fact and not a spelling, and
  costs one second.

Severity: medium for the rule change (it is one of the four conditions),
low for the result.

**S3. No record on the branch that the final statement was signed.** The
2026-11-10 decision has the final text with its diff go back to the owner
before any proof is accepted. The final statement was committed at 19:59
(`b890c947`: "the signature is the owner's"); the proof cut at 20:24
(`c499a310`) already speaks of "the signed C2 statement", and the closing
report, `docs/proofs.md` and `C2Cut.lean` call it signed. `docs/decisions.md`
is not touched by the branch and no commit carries a [USER] entry for the
signature. I cannot tell from the repository whether the owner signed in
those 25 minutes or the word ran ahead. The text is the one shown, so the
remedy is a record, not rework: before the merge the owner confirms the
signature, and it is entered in `docs/decisions.md` with [USER] and the
date, beside the entry for the rule change if it is accepted. If it was not
signed, the documents' "signed" is a misattribution and should be corrected
in the same commit. Severity: medium, procedural.

### At the owner's choice

**S4. The register rows leave the limits out.** `binary/README.md` states
them fully. The two rows added to `docs/proofs.md` do not: neither says
single-CPU instrumented build with no lock, the bridge's row says "no
packet counter accepted twice by the s5 receive range" without the premise
that the window bytes are unchanged between a complete list of visits, and
neither names the gap to "a replayed packet is dropped". The paragraph
above them links the closing report, which has all of it. A register row
is read alone; one clause each would do. Both rows also say "signed
statement" (S3) and "Pending: the independent landing review"; the second
becomes a link to this document. Severity: low.

**S5. Patch ten's tests are run by nothing.** `Kraken.X64.BtsTests` is in
Kraken's library by glob, but the binary package imports no test module, so
neither `lake -d binary build` nor either gate compiles it (my build log
has no line for it, nor for patch nine's `BtTests`). I built both by hand:
they pass. The final statement's reproduction section gives a command for
the assembly test only. One line in `binary/README.md` (`lake build
Kraken.X64.BtsTests` in `.deps/kraken`) would make the claim "tested"
repeatable. Severity: low; the same holds for patch nine on main.

**S6. The image terms are pinned by the generator only.**
`TrustSurface.expected.txt` prints `RangeDecoderAgreement` and `Context`,
which mention `Binary.C2.Range.fetch` and `Range.entry`, but not those
definitions, nor `Layouts.ReplayFields` and the layout constants. The
check that `C2Image.lean` is the image (`generate_c2.py --check`) needs the
saved ELF and pyelftools and is in no gate. An edit to an instruction term
would most likely break a proof (the one I tried did), but that is a
property of these proofs and not a check. The
earlier results treat their image terms the same way, so this is the
track's standing position and not a regression; the cheap repair is to add
the six `Range` definitions to `DEFINITIONS` in `binary/surface.py` (about
100 printed lines of reading, assumed kind). Severity: low.

**S7. A change in the proof tree can break the bridge with the proof gate
green.** The proof gate does not build `C2Bridge`. A refactor of the four
modules (a renamed lemma, a changed hypothesis of `mirror_step`) passes it
and is found at the next binary claim point. The AGENTS.md text and the
register speak only of the other direction (the mirror moving under the
modules). The bridge gate prints the commit at which the four modules last
changed and compares it with nothing. Since the gate rebuilds the four
modules from source, a pass always means the result holds over the tree as
it stands; what is missing is only the trigger. One sentence in AGENTS.md
would do: a change to any of the four modules is a claim point for the
bridge gate. In the same vein, `scripts/binary-proof-gate` neither builds
nor mentions the bridge, and the build block of `binary/README.md` stops at
the binary gate, so a claim point run from that block leaves the headline
unbuilt; the block should carry the bridge gate's line. Severity: low.

**S8. Working papers would land under `binary/packets/c2/proof/`.**
`PLAN.md`, `WP1.md` to `WP3.md`, `BRIDGE.md` and `C1-ADAPTER.md` are the
briefs and the proposal as written before the work; the first lines of two
of them say they are superseded by the closing report, and `BRIDGE.md`
still describes `C2Bridge.lean.proposed` and `binary/bridge/check`, which
no longer exist. The project keeps plans in `docs/` and lands no run
narratives. I would drop the six files from the landing, or move the two
that the C1 branch still needs. The tests beside them (`C2CutTest`,
`C2CutTrace`, `check`) are worth keeping. Severity: low.

### Notes

**N1. The rule and gate change otherwise does what it says.** The AGENTS.md
text describes the bridge gate accurately (build of the non-default target,
axioms, token scan over `binary/bridge/`, the four-module limit on the
bridge's own lines, no second Lean file, not a default target). The
exemption in step 4 is one exact path and four exact names; the same four
imports in another file fail it (4 findings) and a fifth in the bridge fails
it (1 finding); I ran both. The
branch's pattern matches the same lines as main's. `C2Bridge` is not a
default target, the mirror's lake file is untouched, and the binary
package itself imports nothing of the proof tree. The lag check is a
consistency check on the register row and works as described: it fails if
the row says Current while a mirror file differs from the commit the row
names. `1b7a3b70` (the mirror's last change) is an ancestor of `218d3ffd`
(the commit the row names) and no mirror file differs between `218d3ffd`
and the head.

**N2. The replay accepts whatever was built, and says nothing about
statements.** My first export was taken after I had reverted the S1 mutant
in the source but before I rebuilt the bridge. `leanexport` read the stale
output, and the replay accepted it: 17,824,655 lines against the report's
17,824,663. I noticed only because the count differed, rebuilt, and
exported again; the second export has the report's size to the byte and was
accepted too. Two things follow for the owner's run outside the sandbox:
build `C2Bridge` from the merged source immediately before the export, and
do not read "the kernel accepts the solution" as a check of the headline's
text (S1 is what supplies that). The diagnostic also needs `git` on `PATH`
inside `scripts/in-bundle`, as the report says.

**N3. The closing report overstates one assumption.** Its table of what is
assumed lists the four `CounterWindow` modules "as validated by the proof
gate". They are not assumed: the bridge build compiles them from source and
the headline's axiom list and the export cover them. `NoCounterAcceptedTwice`
is stated in machine terms only; the pure window model is proof, not
surface. Harmless, and it errs on the safe side.

**N4. Capping.** `scripts/in-bundle` resets `PATH`, so both binary gates
print "capped is not installed; building uncapped" whenever they run under
it, and are capped only if the caller wraps the whole command, as AGENTS.md
writes it. The closing report's validation table gives the two gate
commands without the wrapper. My first run of the two gates made the same
mistake and ran uncapped (the builds were small); my
later runs were wrapped. Worth one line in `binary/README.md`, whose
reproduction block does wrap them.

**N5. The statement file after the signature.** `14f53df5` removes
`AcceptedWithinWindow` and `AdvanceAccepted` and edits the header comment
of Part 4. The final statement lists both as in the file and not signed, so
the removal changes nothing signed. `AdvanceAccepted` was the packet's
exclusion of "refuses everything"; the witness and `Refines` now do that
work. The docstring of `HeadlineRefinement` still names `AdvanceAccepted`
as the rejected alternative, a reference to a declaration that no longer
exists; the integrator left it because the docstring is signed text. I
agree with leaving it unless the owner says otherwise.

**N6. The patch.** Against the decision clause by clause: the constructor
takes an address and a register, so no register destination; `w ≠ .W64` and
an offset of 64 or more are `unimplemented` before any access; the quadword
is read with `Mem.loadInt` directly, so an unmapped one is `unimplemented`
and not an MMIO effect; CF is the old bit of the word read; the word is
stored back with the bit set on every path; five `undefined` binders for
PF, AF, ZF, SF, OF. Undefined ZF contains Intel's "unaffected", so a
universally quantified claim is sound under either vendor's text. The
below-64 restriction is met in the image by `and $0x3f,%r15d` two
instructions earlier; where it is not met the step is declined, and a
declined step makes `Effects.All` false, so it cannot help a proof. The two landed files gain one proof case each
(`MemoryInvariant.operation`, `SystemInvariant.operation`); the diff
touches no statement, and both rebuilt here. The patch file's author date
is a fixed noon timestamp, which is what makes the reconstructed commit
hash reproducible.

**N7. Standing rules.** `git diff 4fbcc1eb 42d63cb2 -- Leanux` is empty:
the mirror and the proof tree's files are untouched. The branch is a
fast-forward of main, which is unchanged at `4fbcc1eb`. I found no user
text quoted in the added documents or in the 54 commit messages (a search
for quotation and attribution patterns, and what I read). The rule
and gate changes are marked as proposals for the owner in their commit
subjects; the integrator's own decisions (the rename, the removal of the
two unsigned statements) are recorded with [AGENT] in their commits. No
file added carries a resource raise, a `set_option`, a `sorry` or a linter
suppression (the binary gate's scan and my own grep).

## Verified, taken from the report, not checked

- Verified by rebuilding or rerunning here: everything in the table of
  checks.
- Taken from the report: the whole proof gate's pass with the changed rule;
  the mirror build and unit tier; the four one-off mutants of the bridge
  gate; the comparison of the 25 interface theorems' types in a scratch
  file (the `example` lines in `C2Headline.lean` do the same and compiled
  here); the host-processor run and the native assembly comparison of
  `bts`; the vendor manuals as recorded in the decision.
- Not checked by anyone: `Context` against a captured kernel state; the
  decoder against the bytes (objdump's text and Kraken's parser are
  trusted); the replay outside the sandbox.

## To the owner

Land it, with S1 to S3 done first. S1 and S2 are a few lines each in two
scripts and one sentence in AGENTS.md, and they are what make the four
conditions of the 2026-11-10 decision true of the gates and not only of
today's tree. S3 is yours alone. The result itself I would sign as it
stands: a closed, kernel-checked refinement of the mirror's
`counterValidate` by 70 instructions of the pinned image, under the stated
premises, in a single-CPU instrumented build, ending at `setb %bpl`.
