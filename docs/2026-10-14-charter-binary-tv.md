# Charter: binary-level translation validation, scoping and derisking

A scoping assignment for a Codex agent: decide whether the mirror can be
proved to simulate the compiled oracle kernel under Kraken's x86-64 semantics
by translation validation at the mirror's decision level, and derisk the
approach on one WireGuard function. The deliverable is a report with a
go/no-go, the blockers ranked, and a reproducible probe. No proof is
expected from this assignment; a probe that runs is.

Provenance: [USER 2026-10-14] the user wants the code-to-mirror simulation
and has struggled to get a Cerberus-based separation logic to carry it; the
C semantics will not execute this kernel's code (inline assembly). The user
proposed translation validation over the compiled code under a machine
semantics, chose WireGuard as the first target, and pulled Kraken into
`.deps/`. [AGENT, coordinator] wrote the charter and tested the toolchains
(section 3).

## 1. What this is, and what it is not

The project's correspondence claim is at one altitude: each C choice point
on a modelled path has a mirror choice point in the same order, the declared
operands agree, and hidden inputs are consumed where the kernel reads them.
The differential check tests that claim on traces against the oracle. This
assignment asks whether the same claim can be *proved*, for all inputs a
certificate covers, against the oracle image itself, with the mirror on one
side and the machine code on the other. The C disappears from the trusted
chain: inline assembly, GNU extensions and undefined behaviour are
instructions like any other, and the compiler-bound witnesses the
[compiler experiment](2026-10-13-compiler-experiment.md) found become the
checker's ordinary business, since the certificate is per build.

It is the shape of seL4's binary verification (Sewell, Myreen, Klein,
*Translation validation for a verified OS kernel*, PLDI 2013), with the
mirror in place of the C semantics. It is not a program logic, not a frame
rule, and not a proof about the unanchored kernel, which enters only through
the records.

## 2. The approach to scope

Per anchored function `f` with mirror `m_f`:

- The binary's control-flow graph from `objdump` and the DWARF line and
  inlining tables (the evaluator already resolves PCs this way,
  `evaluator/coverage.py`). Inlined callees are DWARF ranges inside the
  caller's symbol; compiler clones and cold splits are symbols of their own.
- The mirror's decision tree, reflected from its monadic definition (the
  branch, comparison, record and call sites are explicit calls in the
  do-blocks).
- A state relation `R`, generated from DWARF types: each mirror structure's
  fields to base-plus-offset locations, intrusive lists by following links,
  rings by slots; locals via DWARF location lists at the matched points;
  registers at call boundaries by the ABI.
- A certificate: decision to branch instruction, outcome to block, declared
  comparison to compare instruction, record consumption to hook call, mirror
  update to the stores between matched points, and a classification of every
  call site as mirrored callee, service (assumed to compute the function the
  mirror computes: the assembly crypto, the allocators' recorded outcomes),
  environment (effects outside `R`'s domain: locks, RCU, the scheduler), cut
  (no effect on `R`), or instrumentation (coverage and comparison calls write
  only to the coverage area; the choice-stream hooks return the recorded
  hidden input). An unclassified call site is a rejection.
- A checker that symbolically executes each straight-line region between
  matched points under Kraken and compares path conditions and memory effects
  with the mirror's branch condition and update under `R`. Arithmetic goals
  are bitvector equalities; `bv_decide` discharges them.
- One soundness theorem over Kraken's step relation: an accepted certificate
  implies the simulation. Per-function proofs are then the theorem applied to
  the checker's result.

The end-state property: executions from related states end in related
states, composed over the recorded sequence of anchored entries. The
environment assumptions are stated once: one CPU, no preemption, interrupts
confined to the recorded yields and softirq placements plus the tick's
jiffies writes, kernel memory mapped so the mirrored regions take no faults,
the hooks returning the recorded inputs, and the unanchored kernel making
exactly the recorded anchored entries with related arguments (the
differential check's empirical content, not proved here).

Tractability rests on one fact: the mirror's decision density equals the
binary's coverage-point density by construction, so the checker works per
block between matched points, never per path.

## 3. Setup

- Repository `/home/dev/projects/lean-ux-proto`. Worktree
  `.worktrees/binary-tv`, branch `task/binary-tv` from `main`, created for
  you; work only there with absolute paths. Nothing on `main`, nothing
  pushed, the mirror not edited (the one exception in section 4).
- The oracle image: `.artifacts/kernel-net-choice-s4/vmlinux` in the main
  checkout, identity `6b2018b9` in `kernel/identity-x86_64-net-choice.txt`,
  built from the locked source with `kernel/patches/choice-stream.patch`
  (the hooks of kinds 305 to 312; read `kernel/patches/gen-choice-stream.py`
  for what each hook does and where). Read-only.
- Kraken: `.deps/kraken`, a full clone at `8af7806` (2026-10-14), its
  `lean-toolchain` a nightly. Tested by the coordinator on 2026-10-14: its
  `Kraken` library fails on v4.33.1 (meta API changes in `Kraken/Tactics.lean`),
  builds cleanly on v4.34.1, builds on v4.35.0 with one `sorry` warning in
  an example file. Its README states the x64 model's scope: sequential code;
  faults, virtual memory, segment registers, MSRs and mutable globals out of
  scope; AT&T-to-Intel parsing; `OmniSemantics`; `Sep`; a runner.
- Toolchain: the probe's package pins `leanprover/lean4:v4.35.0` (elan has
  it installed). `main` stays at v4.33.1 while the proof campaign runs; the
  main bump is a separate, later step. Under v4.35.0 the mirror needs one
  type ascription, tested: in `Leanux/WG/NetlinkDump.lean`,
  `let fromPeers := match ...` becomes `let fromPeers : List PeerId := match ...`;
  with it the mirror, the model executable and the proof tree build as on
  v4.33.1. Make that edit on your branch; it changes no behaviour.
- The probe's package: `binary/` with its own `lakefile.toml` and
  `lean-toolchain`, requiring Kraken by path (`../.deps/kraken`) and the
  mirror by path (`..`), outside the main package's default targets. Lake
  compiles the mirror's sources under the probe's toolchain into the probe's
  own build directory.
- Tools on the box: binutils 2.42 (`objdump`, `readelf`, `addr2line`,
  `nm`); the system Python has pyelftools 0.30 (installed by the user; not
  in the project's bundle, so run DWARF extraction with the system `python3`
  or use `readelf --debug-dump=info`); `bv_decide`'s solver ships with Lean.
- References, read-only: `/home/dev/projects/_retired/gc-verified` (Kraken
  packaging; its axiom gate `scripts/check-kraken-axioms` and
  `tools/kraken/`; the note that upstream examples using `sorry` and the
  `bv_decide` native axiom are excluded from its gate) and
  `/home/dev/projects/rustc-verified` (the certificate-per-compilation
  pattern across semantic layers).
- Read first in this repository: `README.md`, `AGENTS.md`,
  `docs/2026-10-14-pre-release-review.md` sections 7 and 9,
  `docs/2026-10-13-compiler-experiment.md`, `correspondence/kcov.json` (the
  anchored functions, branch-free functions, helper cuts, shared exits,
  operand exclusions), `evaluator/coverage.py`, `docs/proofs.md`, and the
  WireGuard modules of the mirror.
- `capped` for every build; never kill processes by name; `LEANUX_QEMU_SLOTS`
  default 8 if you run the differential check to obtain a trace's coverage.

## 4. The questions, in order

Report after questions 1 to 3 with a first go/no-go on instruction
coverage, then continue.

1. **Toolchain and axioms.** Confirm Kraken and the probe package build on
   v4.35.0 together. Check `bv_decide` on bitvector goals of the operand
   widths used (8, 32 and 64 bits) and name the axiom it adds; this
   project's proof gate admits only `propext`, `Classical.choice` and
   `Quot.sound`, so state exactly what a binary-proof gate would have to
   admit beyond them and whether `decide` or `omega` could replace
   `bv_decide` on the goals that arise.
2. **Instruction coverage.** Disassemble every WireGuard anchored symbol (the
   listed functions in kcov.json plus their DWARF inlined ranges) and
   classify each instruction and addressing form against Kraken's parser and
   semantics: supported; unsupported but shallow (rip-relative globals,
   `lock`-prefixed read-modify-write, `endbr64`, indirect calls, bit
   instructions, `rep` string operations); unsupported and deep
   (`%gs`-relative per-cpu access, `swapgs`, interrupt-flag changes, MSRs).
   A table per function with counts and the first blocker. Say what the
   per-cpu accesses are for (`current`, the preempt count, per-cpu caches)
   and how a single-CPU model gives `%gs` a constant base.
3. **Globals.** Kraken excludes mutable data; the anchored code reads and
   writes globals and per-cpu data. Propose the memory-model extension (a
   flat memory initialised from the image's sections at their link
   addresses, the per-cpu area for CPU 0 at its address) and estimate it.
4. **The concrete probe, WireGuard only.** Pick one anchored function that
   is a standalone symbol at this optimisation level, pure or nearly so,
   with few calls, and has a mirror function: the allowed-IPs lookup first
   (the campaign proves the trie on the mirror side), the index-hashtable
   lookup second, `counter_validate` third if it survives inlining as a
   symbol. Build the machine state for one recorded operation from a corpus
   trace (registers per the ABI; memory for the structures from the mirror's
   state through the DWARF layouts), run Kraken concretely from the entry to
   the return, and compare three ways: the return value and memory effects
   against the mirror function on the same input; the sequence of block
   entries Kraken took against the KCOV coverage the real kernel recorded
   for that operation (the check's witness data, `.artifacts/check/*` of a
   run you make); and the mirror's decision sequence. Three-way agreement on
   one function is the result that makes the approach credible. Report any
   disagreement verbatim; a disagreement between Kraken and the recorded
   coverage is a finding about the semantics, not about the mirror.
5. **The symbolic step.** Whether Kraken's `OmniSemantics` or `Sep` supports
   symbolic execution of one basic block. Try the block holding the chosen
   function's first compare, obtain its condition as a bitvector term, and
   discharge equality with the mirror's condition.
6. **The state relation.** Extract the DWARF layouts for the structures the
   chosen function touches and write `R` for them; say what the
   intrusive-list and trie-node cases need, and how `R` would be generated
   rather than written.
7. **Instrumentation and environment.** Confirm the coverage calls,
   comparison calls and record hooks are plain `call` instructions in the
   anchored code, and state how the checker treats each kind.
8. **Scale.** Instruction counts for the WireGuard anchored set, blocks
   between matched points, and an estimate in agent-days for the checker,
   the soundness theorem and the first three functions, with the risks
   ranked.

## 5. Deliverables and success criterion

- `docs/2026-10-15-binary-tv-scoping.md`: the report, table-driven, with
  the go/no-go first, the blockers ranked, the three-way comparison of the
  probe, and the estimate.
- `binary/`: the probe package, with one command that reproduces the
  concrete run and its comparison.
- The dependency notes: a row for Kraken in `dependencies/sources.lock.json`
  naming the commit used, and the toolchain choice.

The assignment succeeds with a report that answers the eight questions with
evidence and a probe that runs, whatever the go/no-go. A no-go with the
blocker named precisely is a success; a go without the three-way comparison
is not.

## 6. Working conditions

- Budget three days. Report after questions 1 to 3, then at the end; the
  user relays.
- No hard stops: a question that cannot be answered is written down with
  what would answer it, and the next question starts.
- Mistakes in form are corrected in the next commit; nothing in this
  charter is a reason to stop except the user's word.
- Commit with the provenance `[AGENT, scoping]` and your own attribution.
  No merge, no push.
- Do not touch `.worktrees/proofs-campaign` (the running proof campaign) or
  any other worktree.

## Paste for the agent

> Scoping and derisking of binary-level translation validation: can the
> mirror be proved to simulate the compiled oracle kernel under Kraken's
> x86-64 semantics, by translation validation at the mirror's decision
> level? Charter: `docs/2026-10-14-charter-binary-tv.md` (read it whole).
> Worktree `.worktrees/binary-tv`, branch `task/binary-tv`, already created;
> work only there. Kraken is at `.deps/kraken` (head `8af7806`, builds on
> Lean v4.35.0); the probe's package goes under `binary/` with its own
> toolchain file at v4.35.0, requiring Kraken and the mirror by path; the one
> mirror edit v4.35.0 needs is the type ascription named in section 3. The
> oracle is `.artifacts/kernel-net-choice-s4/vmlinux`, read-only. WireGuard
> only: the probe is one standalone anchored function, run concretely under
> Kraken from entry to return on a recorded operation and compared three
> ways (the mirror's result, the kernel's recorded coverage, the mirror's
> decision sequence). Eight questions in section 4; report after the first
> three with a go/no-go on instruction coverage, then at the end. Three
> days. No proof expected, a probe that runs is. Nothing on `main`, no push,
> `capped` for builds, do not touch other worktrees.
