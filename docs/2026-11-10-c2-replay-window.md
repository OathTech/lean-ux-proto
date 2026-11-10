# C2, the receive replay window: closing report

Branch `task/binary-c2`. Status: the headline is closed on the branch; it is
not on `main`. Three things stand between it and a landed result: the
independent landing review, the owner's signoff on a change to a standing
rule (section 6), and the kernel replay run outside the sandbox (section 5).

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
- `ReplayWitness`: the premises are met by a concrete state on which one
  counter is accepted and then refused.

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
| The four `CounterWindow` modules of the proof tree | the bridge | `mirror_step` and `accepted_nodup` as validated by the proof gate over mirror `218d3ffd` |

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

| Part | Files | Lines | Elapsed agent time |
| --- | --- | ---: | ---: |
| Statement and image terms | `C2Statement`, `C2Image` | 336 | (earlier phases) |
| Cut: pivot, interfaces, assembly, shared callback statement | `C2Cut`, `C2CutInterfaces`, `C2CutAssembly`, `CallbackCmp8Image`, `CallbackCmp8Rule` | 983 | (earlier phase) |
| Package 1: callback rules, layout, `bts` support, call sites | `CallbackCmp8`, `C2Callbacks` | 871 | about 15 minutes |
| Package 2: the five segments | `C2Range` and six `C2Range*` modules | 1,408 | about 21 minutes |
| Package 3: representation, mirror link, sequences, witness | `C2Sequences` | 1,318 | about 42 minutes |
| Integration: closed theorems, bridge, gate | `C2Headline`, `bridge/C2Bridge.lean`, `scripts/c2-bridge-gate` | 80, 141, 204 | about 50 minutes |

No file carries a resource raise. Each package module compiles in one to
three seconds. The plan estimated 20 to 33 worker-hours for the three
packages; they took about 78 agent-minutes. That gap is reported here as a
fact for the landing review, not explained: the integration pass checked
types, axioms and builds, and did not re-derive the mathematics.

## 5. Validation

On the integrated code (the commit before this report; the report and its
index row are the only later changes).

| Check | Command | Result |
| --- | --- | --- |
| Binary package build | `capped -m 24G -- scripts/in-bundle lake -d binary build` | 1137 jobs, no warning in the C2 files |
| Binary gate | `scripts/in-bundle "$(command -v python3)" scripts/binary-proof-gate` | PASS: pin `96d48487`, 74 terminal statements on the standard axioms (71 before, 3 new), surface diff PASS, no forbidden token |
| Bridge gate | `scripts/in-bundle python3 scripts/c2-bridge-gate` | PASS: 130 jobs, 5 theorems on the standard three axioms, lag report: four modules at `b32bb164`, mirror at `1b7a3b70`, register names `218d3ffd`, no mirror file differs |
| Bridge gate, one-off mutants (run once, deleted) | a fifth proof-tree import; a second Lean file in `binary/bridge/`; `sorry` in `headline`; a register row saying Current over a commit the mirror differs from | 4 of 4 rejected |
| Types of the packages' theorems | a scratch file comparing each constant's type with its proposition, syntactically | 25 closed and 5 conditional theorems have exactly the stated types |
| Proof gate, step 4 alone | `check_imports` of `scripts/proof-gate` | 0 findings before the bridge; 4 with the bridge and the old rule; 0 with the changed rule; 1 with a fifth proof-tree import in the bridge; 4 with the same four imports in another file |
| Whole proof gate, with the changed rule | `capped -m 24G -- scripts/in-bundle scripts/proof-gate` | PASS: 6681 jobs, 2455 terminal statements over 20 root modules on the standard three axioms; about 30 minutes |
| Statement tests | `binary/packets/c2/check` | exit 0, about 24 minutes. Every count equals the final statement's table (its section 4): 972 runs, 564 accepted, 0 failures; the eleven wrong variants fail 16, 8, 56, 160, 216, 112, 112, 108, 108, 112, 108 of 216 runs; six sequences, 465 visits, 2, 8, 145, 143, 113, 3 accepted; search 775 and 921 layouts, broken on 0 under the revised `Context`; capacity loop 28,568 states, 9,442 meeting the revised `Context`, broken on 0, replay accepted on 0 |
| Cut tests | `binary/packets/c2/proof/check` | exit 0, about 4 minutes: the pivot agrees with the mirror on 2,925 cases; 512 runs, 41,760 calls, 18,544 loop iterations, every cut predicate held |
| Kraken bootstrap from nothing | `binary/test_bootstrap.py` (a scratch root with no checkout) | 10 patches applied, identity equals the lock (`96d48487`), 1 test OK |
| Mirror build | `capped -m 24G -- scripts/in-bundle lake build` | 66 jobs, completed |
| Unit tier | the `unittest` line of AGENTS.md | 149 tests, OK (1 skipped) |
| Kernel replay export | `lake env leanexport C2Headline C2Bridge` | exit 0; 17,824,663 lines, 1,095,410,711 bytes |
| Kernel replay, diagnostic inside the sandbox | `lake check --from-export=… --inadvisably-no-sandbox` | exit 0 in about 3 minutes: "Lean default kernel accepts the solution", axioms `propext`, `Quot.sound`, `Classical.choice`. Not trustworthy by its own banner (sandbox disabled); it needed `/usr/bin` appended to `PATH` for `git` |

`binary/bridge/check` no longer exists: it compiled the staged copy of the
bridge and is replaced by the named gate.

The gate proper is the same replay run by the owner outside the sandbox.
From the worktree root, after `capped -- scripts/in-bundle lake -d binary
build C2Bridge`:

```sh
cd binary
capped -- ../scripts/in-bundle lake env leanexport C2Headline C2Bridge > ../.tmp/c2-check.ndjson   # exit 0 required
capped -- ../scripts/in-bundle lake check --from-export ../.tmp/c2-check.ndjson
```

## 6. The rule change the bridge needs

The bridge is the one file outside `Leanux/Proofs/` that imports the proof
tree. That needs a change to a standing rule, decided in principle on
2026-11-10 on four conditions and put to the owner here as two diffs, each
its own commit on the branch. Neither is in force until signed.

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
+theorems. It has its own gate, run at the binary track's claim points:
+`capped -- scripts/in-bundle scripts/c2-bridge-gate`, which builds the lake
+target `C2Bridge` of `binary/lakefile.toml`, prints the axioms of its
+theorems and fails on any beyond the standard three, applies the proof
+tree's forbidden-token scan to `binary/bridge/`, and fails if the bridge
+imports the proof tree beyond the four modules, if `binary/bridge/` holds
+another Lean file, or if `C2Bridge` is a default target. The register
+(`docs/proofs.md`) names the mirror commit the four modules hold over; the
+bridge's result lags when they lag.
```

`scripts/proof-gate` (the docstring's item 4 says the same):

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

Two departures from the text proposed in `binary/packets/c2/proof/BRIDGE.md`.
The pattern there ended in `\s*$`, which would have stopped matching an
import followed by a comment in every file; the one applied matches exactly
the lines the old pattern matched. And `AGENTS.md` says "its theorems" where
the proposal said "its three theorems": there are five.

If the owner declines, the commits of the bridge, the gate change, the
`AGENTS.md` change and the bridge gate are dropped; `exits_cleanly`,
`refines` and `replay_witness` stand without them, and the third clause
falls back to the statement packet's alternative (a copy of the window model
in the package).

## 7. Open items

1. The independent landing review of the whole.
2. The owner's signoff on section 6, and on the merge.
3. The kernel replay outside the sandbox (section 5).
4. Two statements outside the text put for signature were removed from
   `C2Statement.lean` (`AcceptedWithinWindow`, `AdvanceAccepted`): in no
   headline, in no package, and not a few lines from what exists. The file
   otherwise equals the text put to the owner. The docstring of
   `HeadlineRefinement` still names `AdvanceAccepted` as the rejected
   alternative; it was left as put to the owner (section 9, item D1).
5. The packages could not be imported together as delivered: packages 1 and
   2 each declared `Binary.C2.WindowAt.frame`, with different statements.
   Package 1's was renamed (`WindowAt.ofEqualOutside`), statement and proof
   unchanged, in its own commit.
6. An existing weakness of step 4 of `scripts/proof-gate`, not changed: the
   pattern anchors `import` at the start of the line, so `public import
   Leanux.Proofs…` in a file that uses the module system passes it. A
   one-line fix, for the owner:

   ```diff
   -            m = re.match(r'^import\s+(Leanux\.Proofs(?:\.\S*)?)(?:\s|$)', line)
   +            m = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(Leanux\.Proofs(?:\.\S*)?)(?:\s|$)', line)
   ```
7. The bridge's row in the register lags when `ReplayWindow` S2 lags; the
   bridge gate prints the commits at every claim point.

## 8. How to reproduce

From the worktree root, on `task/binary-c2`:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
py=$(command -v python3)
cap scripts/in-bundle "$py" -B binary/run.py --bootstrap-only   # upstream + ten patches = 96d48487
cap scripts/in-bundle lake -d binary build
cap scripts/in-bundle "$py" scripts/binary-proof-gate
cap scripts/in-bundle "$py" scripts/c2-bridge-gate              # builds C2Bridge
binary/packets/c2/check                                         # the statement's tests, about 30 minutes
binary/packets/c2/proof/check                                   # the cut's tests, about 4 minutes
```

and the replay of section 5. The whole proof gate (`capped -- scripts/in-bundle
scripts/proof-gate`, about 30 minutes from an unbuilt proof tree) is not needed
for the binary track's claim; it was run once here to show that it passes with
the changed rule.
