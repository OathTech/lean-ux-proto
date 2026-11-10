# C2, the receive replay window: closing report

Branch `task/binary-c2`. Status: the headline is closed on the branch; it is
not on `main`. The independent landing review
(`docs/2026-11-10-review-c2-landing.md`, `bf36a236` on
`task/review-c2-landing`) says land with named changes; section 9 disposes
of each finding. What stands between the branch and a landed result is the
owner's: his signature on the final statement, his signoff on a change to a
standing rule (section 6), and the kernel replay run outside the sandbox
(section 5).

## 1. What is proved

The statement is `binary/C2Statement.lean`, as put to the owner in the
[final statement](2026-11-10-c2-final-statement.md). The owner has not yet
signed it: he left the choices to the coordinator's recommendation and is to
see the final text before any proof is accepted; his signature is given at
the landing. Its headline, verbatim:

```lean
def HeadlineRefinement : Prop :=
  ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness
```

and the theorems that close it, verbatim, with no hypothesis:

```lean
-- binary/C2Headline.lean (the binary package; no import of the proof tree)
theorem exits_cleanly : ExitsCleanly :=
  exits_cleanly_of_parts range_simulates_closed representation.mapped
theorem refines : Refines :=
  refines_of_parts range_simulates_closed representation
theorem replay_witness : ReplayWitness :=
  replay_witness_of_parts (strong_refines range_simulates_closed representation)
    representation witness_start

-- binary/bridge/C2Bridge.lean (the bridge library)
theorem no_counter_accepted_twice : NoCounterAcceptedTwice :=
  no_counter_accepted_twice_of_parts refines representation
theorem headline : HeadlineRefinement :=
  ⟨exits_cleanly, refines, no_counter_accepted_twice, replay_witness⟩
```

In words, of the 70 instructions `[0xffffffff8139d2a6, 0xffffffff8139d3ea)`
of the pinned s5 image (`counter_validate` as inlined in
`wg_packet_rx_poll`), under Kraken's semantics:

- `Refines`: when the 1032 window bytes represent a replay state and the
  mirror's `counterValidate` on a world holding it returns a result, the
  machine reaches, as its first exit, the exit the three tests name, with the
  acceptance byte equal to the mirror's result and the window bytes
  representing the mirror's new state.
- `ExitsCleanly`: from every entry state the code reaches an exit without
  faulting, and `Kept` holds at the first one.
- `NoCounterAcceptedTwice`: over executions of the range on one keypair
  address between which the window bytes are unchanged, no packet counter is
  accepted twice. This is the landed `CounterWindow.accepted_nodup` carried to
  the machine code through `Refines` and `CounterWindow.mirror_step`.
- `ReplayWitness`: the premises are met. The entry state is concrete
  (coverage in PC-recording mode, a zero window, packet counter 5); the
  second visit enters at the first visit's exit state with the program
  counter put back at the entry. That second entry is not a state the kernel
  is ever in: the witness shows that `Visits` is satisfiable and that
  accept-then-refuse happens, and no more.

Also proved, in no headline: `Binary.C2.Bridge.replay_refused : ReplayRefused`.

Closure counts:

| | Count |
| --- | ---: |
| Interface propositions of the cut, each closed by a theorem of exactly that type | 25 (3 callback rules, 6 of package 1, 5 of package 2, 11 of package 3) |
| Clauses of the headline closed | 4 of 4 |
| Theorems whose axioms were printed (25 interface theorems, 4 that use `decide +kernel`, `representation`, `execution_closed`, 3 clauses; and the bridge's 5) | 34 + 5, none beyond `propext`, `Classical.choice`, `Quot.sound` |
| `sorry`, new axiom, `native_decide`, `unsafe`, `implemented_by`, `extern`, `set_option`, resource raise, linter suppression in the added files | 0 |
| Uses of `decide +kernel` in the added files | 7; none adds an axiom (`Lean.ofReduceBool` appears nowhere) |

## 2. What is assumed

The printed surface (`binary/TrustSurface.expected.txt`) gained 234 lines:
120 of what is assumed, 111 of what is claimed, 3 theorem lines.

| Premise | Where | What it asks the reader to accept |
| --- | --- | --- |
| `Reading fetch` | `C2Statement` | The decoder returns the committed terms of the range's 70 instructions and the two 8-byte callback entries (`RangeDecoderAgreement`) and the landed callback terms (`ServiceDecoderAgreement`). Tested against the ELF, not proved |
| `Context layout preempt s kp skb nonce` | `C2Statement` | The entry state: `%r13` the keypair, `%rbx` the packet, the counter at `skb+0x28`, the window and three stack slots mapped, the stack aligned, the coverage state ready, and five separations (stack, window, preempt count, coverage metadata and buffer). Argued from the disassembly |
| `Visits`, `WindowRetained`, `FirstExit` | `C2Statement` | For the third clause only: each visit starts in a `Context` and ends at its first exit, and the window bytes are the same from one visit's exit to the next visit's entry |
| Kraken's x86-64 semantics at `96d48487`, ten patches | `binary/kraken-patches`, `TrustBase.lean` | Patch ten gives `bts` with a 64-bit register offset on a memory quadword, unlocked: defined when the offset is below 64 and the quadword mapped; CF takes the old bit, the bit is set, the five other status flags are undefined. Tested against one processor, not proved faithful |
| The mirror's `counterValidate` (`Leanux.WG.RxData`), by path | the mirror at `218d3ffd` | `Refines` says no more than the mirror says |

The four `CounterWindow` modules of the proof tree are not assumed: the
bridge build compiles them from source, and the headline's axioms and the
replay export cover them. The pure window model is proof, not surface.

The image terms (`binary/C2Image.lean`) are the reading of the image. They
are compared with the saved ELF by `binary/generate_c2.py --check`, a
by-hand check beside the landed generators' in `binary/README.md`; the gate
prints no image terms, for this result as for the landed ones.

## 3. What is not claimed

In the words of the final statement (its section 5):

- A single-CPU, coverage-instrumented build, with no lock. The spinlock has
  size zero, `spin_lock_bh` is one add to the preempt count and the `bts`
  has no LOCK prefix. Nothing carries to an SMP build. The model is
  sequential: no interrupt between instructions.
- The entry context is argued from the disassembly, not derived. No captured
  kernel state has been checked against `Context`.
- The window is unchanged between visits: a premise about the rest of the
  kernel (keypair lifetime, completeness of the list of visits, absence of
  other writers).
- The gap between the range and "a replayed packet is dropped". The range
  ends at `setb %bpl`. The unlock, the branch, the drop path, that this is
  the keypair and counter the packet was decrypted under, and that every
  delivery passes through the range are in no statement.
- Decoder agreement is tested, not proved; Kraken's semantics, the tenth
  patch included, is the base.
- `Refines` is conditional on the mirror's run succeeding, and a defect
  shared by the mirror and the code passes it.

## 4. The proof's shape and size

One pivot, `validate : Window → BitVec 64 → Outcome` (`C2Cut.lean`), the
range at machine width. Package 2 proves the machine computes it, segment by
segment, from package 1's call-site rules; package 3 proves the mirror
computes it, the representation lemmas, the first-exit facts and the
witness. `C2CutAssembly` joins them; `C2Headline` and the bridge apply the
joins.

The invariant carried from +14 on, across each of the thirteen calls and at
the head of each loop iteration (`Carried`): coverage readiness at the
raised preempt count, the window bytes holding the window in progress, the
three stack slots mapped, memory equal to the entry's outside the footprint
and the coverage buffer, and `%rsp`, `%rbx`, `%r12`, `%r13` the entry's. The
cut predicates and the pivot are also executed (`binary/packets/c2/proof/check`):
evidence that they hold on those runs, beside the proof.

The 8-byte comparison callback is stated once, in `CallbackCmp8Image` and
`CallbackCmp8Rule`, and proved in `CallbackCmp8`, none of which imports a C2
module. The C1 branch takes those files unchanged and proves on its side
that its own image terms give `Cmp8.Cmp8Agreement`; the note written for it
is in history at `c4b66700:binary/packets/c2/proof/C1-ADAPTER.md`.

| Part | Files | Lines | Elapsed agent time |
| --- | --- | ---: | ---: |
| Statement and image terms | `C2Statement`, `C2Image` | 336 | (earlier phases) |
| Cut: pivot, interfaces, assembly, shared callback statement | `C2Cut`, `C2CutInterfaces`, `C2CutAssembly`, `CallbackCmp8Image`, `CallbackCmp8Rule` | 983 | (earlier phase) |
| Package 1: callback rules, layout, `bts` support, call sites | `CallbackCmp8`, `C2Callbacks` | 869 | about 15 minutes |
| Package 2: the five segments | `C2Range` and six `C2Range*` modules | 1,407 | about 21 minutes |
| Package 3: representation, mirror link, sequences, witness | `C2Sequences` | 1,317 | about 42 minutes |
| Integration: closed theorems, bridge, gate | `C2Headline`, `bridge/C2Bridge.lean`, `scripts/c2-bridge-gate` | 80, 141, 202 | about 50 minutes, and about 90 on the review's findings |

No file carries a resource raise. Each package module compiles in one to
three seconds. The plan estimated 20 to 33 worker-hours for the three
packages; they took about 78 agent-minutes. The integration pass checked
types, axioms and builds, and did not re-derive the mathematics. The
landing review's answer: the closed theorems take no hypothesis, so every
intermediate device is inside a kernel-checked term, and what can be wrong
while everything checks is only the statement, the reading of the image and
the semantic base, which it read.

## 5. Validation

`scripts/in-bundle` resets `PATH`, so the two binary gates cannot find
`capped` themselves: they are capped only when the whole command is wrapped,
as written here. The first three rows and step 4 were rerun, wrapped, after
the changes of section 9; the other rows are from the integration pass, and
no file they read has changed since except header comments in four package
modules (which the build of the first row recompiled).

| Check | Command | Result |
| --- | --- | --- |
| Binary package build | `capped -m 24G -- scripts/in-bundle lake -d binary build` | 1137 jobs, no warning |
| Binary gate | `capped -m 24G -- scripts/in-bundle "$(command -v python3)" scripts/binary-proof-gate` | PASS: pin `96d48487`, 74 terminal statements on the standard axioms (71 before, 3 new), surface diff PASS, no forbidden token |
| Bridge gate | `capped -m 24G -- scripts/in-bundle "$(command -v python3)" scripts/c2-bridge-gate` | PASS: 130 jobs, 5 theorems on the standard three axioms, the statements of `headline` and `no_counter_accepted_twice` equal to the expected text; printed lag report: four modules at `b32bb164`, mirror at `1b7a3b70`, register names `218d3ffd` |
| Bridge gate, the reviewer's two restatements as one-off mutants (run once, reverted) | `no_counter_accepted_twice : True`; `headline : ExitsCleanly` | both rejected on the statement diff |
| Proof gate, step 4 alone | `check_imports` of `scripts/proof-gate` | main's gate on this tree: 4 findings (the bridge's four imports). This branch's gate on this tree: 0. This branch's gate on main's tree: 0. A fifth proof-tree import in the bridge: 1. The same four imports in another file: 4 |
| Whole proof gate, with the changed rule | `capped -m 24G -- scripts/in-bundle scripts/proof-gate` | PASS: 6681 jobs, 2455 terminal statements over 20 root modules on the standard three axioms; about 30 minutes. Not rerun: `scripts/proof-gate` is as it was for that run |
| Types of the packages' theorems | a scratch file comparing each constant's type with its proposition, syntactically | 25 closed and 5 conditional theorems have exactly the stated types |
| Statement tests | `binary/packets/c2/check` | exit 0, about 24 minutes. Every count equals the final statement's table (its section 4): 972 runs, 564 accepted, 0 failures; the eleven wrong variants fail 16, 8, 56, 160, 216, 112, 112, 108, 108, 112, 108 of 216 runs; six sequences, 465 visits, 2, 8, 145, 143, 113, 3 accepted; search 775 and 921 layouts, broken on 0 under the revised `Context`; capacity loop 28,568 states, 9,442 meeting the revised `Context`, broken on 0, replay accepted on 0 |
| Cut tests | `binary/packets/c2/proof/check` | exit 0, about 4 minutes: the pivot agrees with the mirror on 2,925 cases; 512 runs, 41,760 calls, 18,544 loop iterations, every cut predicate held |
| Image terms against the ELF, by hand | `scripts/in-bundle "$(command -v python3)" -B binary/generate_c2.py --check` | "C2Image.lean matches the pinned ELF": 70 instructions, 324 bytes, 13 call sites |
| The Kraken patches' own tests, by hand | the command in `binary/README.md` (eleven test modules) | 24 jobs, every `#guard` holds |
| Kraken bootstrap from nothing | `binary/test_bootstrap.py` (a scratch root with no checkout) | 10 patches applied, identity equals the lock (`96d48487`), 1 test OK |
| Mirror build | `capped -m 24G -- scripts/in-bundle lake build` | 66 jobs, completed |
| Unit tier | the `unittest` line of AGENTS.md | 149 tests, OK (1 skipped) |
| Kernel replay export | `lake env leanexport C2Headline C2Bridge` | exit 0; 17,824,663 lines, 1,095,410,711 bytes |
| Kernel replay, diagnostic inside the sandbox | `lake check --from-export=… --inadvisably-no-sandbox` | exit 0 in about 3 minutes: "Lean default kernel accepts the solution", axioms `propext`, `Quot.sound`, `Classical.choice`. Not trustworthy by its own banner (sandbox disabled); it needed `/usr/bin` appended to `PATH` for `git` |

The gate proper is the same replay run by the owner outside the sandbox.
Two cautions from the landing review. The export reads whatever was last
built, and the replay accepted a stale output in the reviewer's first try:
build `C2Bridge` from the merged source immediately before exporting. And
"the kernel accepts the solution" says nothing about what the headline
states: the bridge gate's statement comparison is what checks that. From the
worktree root:

```sh
capped -- scripts/in-bundle lake -d binary build C2Bridge      # from the merged source, immediately before the export
cd binary
capped -- ../scripts/in-bundle lake env leanexport C2Headline C2Bridge > ../.tmp/c2-check.ndjson   # exit 0 required
capped -- ../scripts/in-bundle lake check --from-export ../.tmp/c2-check.ndjson
```

## 6. The rule change the bridge needs

The bridge is the one file outside `Leanux/Proofs/` that imports the proof
tree. That needs a change to a standing rule, decided in principle on
2026-11-10 on four conditions and put to the owner here as two diffs against
`main`. Neither is in force until the owner signs off.

`AGENTS.md`:

```diff
 `implemented_by` or `extern` anywhere in the tree outside comments and
-string literals, and fails if anything outside the tree imports it, if the
-root misses a result's `Statements`, or if `LeanuxProofs` is a default lake
-target. Beside it, a speedbump: `scripts/proof-counterexamples` replays the
+string literals, and fails if anything outside the tree imports it (one
+exemption: `binary/bridge/C2Bridge.lean` may import the four modules
+`Leanux.Proofs.WG.CounterWindow.Model`, `.Refinement`, `.MirrorCalls` and
+`.Bounds`, and nothing else of the tree), if the root misses a result's
+`Statements`, or if `LeanuxProofs` is a default lake target. Beside it, a
+speedbump: `scripts/proof-counterexamples` replays the
 published counterexample and witness recipes through the interpreter, which
 the gate's build does not cover.
 
+The exempt file is the binary track's bridge: it joins the replay-window
+refinement proved in the binary package with the landed `CounterWindow`
+theorems. Its gate, run at the binary track's claim points and after a
+change to any of the four modules (the proof gate does not build the bridge):
+`capped -- scripts/in-bundle scripts/c2-bridge-gate` builds the lake target
+`C2Bridge` of `binary/lakefile.toml`, fails on an axiom of its theorems
+beyond the standard three or on a forbidden token in `binary/bridge/`, and
+compares what `headline` and `no_counter_accepted_twice` state with
+`binary/bridge/C2Bridge.expected.txt`. It prints the commits for the lag
+report; the register (`docs/proofs.md`) says when the bridge's result lags.
```

`scripts/proof-gate`, the whole of its change (the docstring's item 4 says
the same):

```diff
 TARGET = 'LeanuxProofs'
+# The binary track's bridge (AGENTS.md): one exact path, four exact modules.
+BRIDGE = ROOT / 'binary' / 'bridge' / 'C2Bridge.lean'
+BRIDGE_IMPORTS = {'Leanux.Proofs.WG.CounterWindow.' + name
+                  for name in ('Model', 'Refinement', 'MirrorCalls', 'Bounds')}
@@
         for number, line in enumerate(path.read_text().splitlines(), 1):
-            if re.match(r'^import\s+Leanux\.Proofs(\.|\s|$)', line):
+            m = re.match(r'^import\s+(Leanux\.Proofs(?:\.\S*)?)(?:\s|$)', line)
+            if m and not (path == BRIDGE and m.group(1) in BRIDGE_IMPORTS):
                 fail(f'{rel}:{number} imports the proof tree')
```

The pattern matches exactly the lines main's pattern matches; the only
change is the exemption.

What the gates are for. The import check is a speedbump against an honest
stray import in the ordinary spelling, which it catches. It is not built to
resist unusual spellings of an import, and the bridge gate does not check
the bridge's imports at all: step 4 does. At this head the bridge's
transitive imports from the proof tree are exactly the four (2500 modules;
found by the reviewer and again here with a scratch `#eval`).

A change in the proof tree can break the bridge while the proof gate is
green: the proof gate does not build `C2Bridge`, so a renamed lemma or a
changed hypothesis in one of the four modules passes it. The bridge gate,
run at the binary track's claim points and after a change to any of the four
modules, is what catches that; it rebuilds the four modules from source, so
a pass means the result holds over the tree as it stands.

If the owner declines the rule change, the commits of the bridge, the gate
change, the `AGENTS.md` change and the bridge gate are dropped;
`exits_cleanly`, `refines` and `replay_witness` stand without them, and the
third clause falls back to the statement packet's alternative (a copy of the
window model in the package).

## 7. Open items

1. The owner's signature on the final statement, with the one-word docstring
   correction of section 9 (D1) if he takes it.
2. The owner's signoff on section 6, and on the merge.
3. The kernel replay outside the sandbox (section 5).
4. The bridge's row in the register lags when `ReplayWindow` S2 lags; the
   bridge gate prints the commits at every claim point.
5. The tests that the ten Kraken patches carry are compiled by no gate; they
   are a by-hand check (section 9, S5).

## 8. How to reproduce

From the worktree root, on `task/binary-c2`:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
py=$(command -v python3)
cap scripts/in-bundle "$py" -B binary/run.py --bootstrap-only   # upstream + ten patches = 96d48487
cap scripts/in-bundle lake -d binary build
cap scripts/in-bundle "$py" scripts/binary-proof-gate
cap scripts/in-bundle "$py" scripts/c2-bridge-gate              # builds C2Bridge
cap scripts/in-bundle "$py" -B binary/generate_c2.py --check    # needs the saved ELF and pyelftools
binary/packets/c2/check                                         # the statement's tests, about 30 minutes
binary/packets/c2/proof/check                                   # the cut's tests, about 4 minutes
```

and the replay of section 5. The whole proof gate (`capped -- scripts/in-bundle
scripts/proof-gate`, about 30 minutes from an unbuilt proof tree) is not needed
for the binary track's claim; it was run once here to show that it passes with
the changed rule.

## 9. Dispositions of the landing review's findings

Each finding of `docs/2026-11-10-review-c2-landing.md` (`bf36a236`), one
commit each on this branch where something changed. "Not done" is a
decision, taken on the coordinator's correction: the gates here catch honest
mistakes and are not built to resist someone defeating them, and over-strong
gating is a defect (AGENTS.md, "Gates and speedbumps").

| Finding | Disposition | Where, and the reason |
| --- | --- | --- |
| S1: the bridge gate checks axioms and names, never a type | Fixed, in the smallest form | `scripts/c2-bridge-gate` prints `headline` and `no_counter_accepted_twice` with their types and compares them with `binary/bridge/C2Bridge.expected.txt` (two lines). Honest drift of what the headline states is a real class of mistake and the check is one `lean` run. The reviewer's two restatements, run once as mutants, both fail. Commits `1e0126da`, `7a245ff0` |
| S2: the four-module limit is enforced on the spelling of one line, and the bridge gate accepts any package module | Not done: adversarial hardening, gate cruft | The import check is a speedbump against an honest stray import in the ordinary spelling, which it catches; evading it by an unusual spelling is not a class of honest mistake. The condition holds at the head: the bridge's transitive proof-tree imports are exactly the four (the reviewer's check, repeated here). A transitive-import check in the bridge gate and an every-spelling match in step 4 were written, then reverted (`27f76fe3`, `0e9ffea9`; reverts `b39cdb3e`, `aecaa2d6`). The `public import` pattern change drafted in the first version of this report is withdrawn for the same reason. The only change to `scripts/proof-gate` is the exemption |
| S3: the branch calls the statement signed and holds no record of a signature | Fixed | The owner has not yet signed the final statement: he left the choices to the coordinator's recommendation and is to see the final text before any proof is accepted. The closing report, the register and the final-statement document now say the final statement as put to the owner, whose signature is given at the landing. Not changed: commit messages (`c499a310` says "the signed C2 statement"; history is not rewritten) and the coordinator's entry in `docs/decisions.md` on main ("C2 is signed in the refinement form"), which is the coordinator's to word. No [USER] entry is added here. Commit `0edab70b` |
| S4: the register rows leave the limits out | Fixed | Both rows of `docs/proofs.md` name the single-CPU instrumented build with no lock and the gap to "a replayed packet is dropped"; the bridge's row states the window-unchanged-between-visits premise in the result; the review cell links the review. Commit `67d69a01` |
| S5: patch ten's tests are run by nothing | Answered; documented, no gate step | The landed practice, as found: no build and no gate compiles the in-patch tests of any of the ten patches; they were run when each patch was made. Patch ten is treated identically. `binary/README.md` now gives the by-hand command for the eleven test modules; run once here, 24 jobs, every guard holds. A gate step was written and discarded uncommitted. Commit `71ddba49` |
| S6: the image terms are pinned by the generator only | Answered; no change needed | `generate_c2.py --check` is already where the landed generators' checks are: the by-hand block of `binary/README.md`, which needs the saved ELF and pyelftools and is not a gate. Run once here: matches the pinned ELF. The landed gate prints no image terms for any result, so `C2Image` is not added to the printed surface |
| S7: a proof-tree change can break the bridge with the proof gate green; the README's check block stops at the binary gate | Fixed, documentation only | The check block of `binary/README.md` carries the bridge gate; the `AGENTS.md` paragraph names a change to any of the four modules as a claim point for it; section 6 above says what catches the break. No gate is wired into another. Commit `e426d95d` |
| S8: working papers would land under `binary/packets/c2/proof/` | Fixed | `PLAN.md`, `WP1.md` to `WP3.md`, `BRIDGE.md`, `C1-ADAPTER.md` removed; what was still a fact about the result is in sections 4 and 6; the executed tests stay. Commit `c4ecd599` |
| N2: the replay accepts whatever was built | Fixed | The owner's command block builds `C2Bridge` immediately before the export and says why (section 5) |
| N3: the report listed the four `CounterWindow` modules as assumed | Fixed | Section 2 says they are compiled from source and covered by the axioms and the export |
| N4: the validation table gave the gate commands unwrapped | Fixed | Section 5 gives the wrapped form; both gates were rerun wrapped; `binary/README.md` says why |
| The witness is described more shortly than the fact | Fixed | Section 1 says the second visit's entry is not a state the kernel is ever in |
| D1 (N5): the docstring of `HeadlineRefinement` names the removed `AdvanceAccepted` | Left for the owner, with his signature | The statement's text is not changed here. Proposed diff below |
| The bridge gate as a whole | Trimmed | It builds the bridge, prints axioms, compares the two statements, scans for forbidden tokens, and prints the lag commits without failing on them. Removed: the reading of the bridge's import lines, the other-Lean-file check, the default-target check, the failure on a build warning, and the register-row parsing with a content diff. Kept beside the axioms, three lines: the bridge's theorem names against the gate's list, so that a theorem added to the bridge has its axioms printed. Commit `7a245ff0` |

D1, the proposed diff to `binary/C2Statement.lean`, for the owner:

```diff
 /-- THE HEADLINE. What the code computes (`Refines`), that it exits cleanly, the
 transported property, and a witness that all of it is inhabited. (Rejected alternative:
-a machine-states-only conjunction with `AdvanceAccepted` in place of `Refines`, which
-holds of code that permutes the bits of a bitmap word.) -/
+a machine-states-only conjunction with an advance-is-accepted clause in place of `Refines`,
+which holds of code that permutes the bits of a bitmap word.) -/
```
