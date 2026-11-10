# Independent review: statement packet C2 (the receive replay window)

2026-11-10. Reviewed: `docs/2026-11-10-statement-packet-c2-replay-window.md`
and `binary/packets/c2/` at `e05ffd8f` (branch `task/binary-c2-statement`).
Written on `task/review-c2-statement` in its own worktree
(`.worktrees/review-c2-statement`). The packet's files were compiled and run
here against the build outputs of `.worktrees/binary-reassessment` (read
only; `git diff 02e48bae e05ffd8f -- binary Leanux` shows only the packet's
nine new files). Inputs read: the packet and all nine files;
`binary/TrustBase.lean`, `Memory.lean`, `Execution.lean`, `History.lean`,
`FiniteExecution.lean`, `Layouts.lean`; Kraken's `Eventually`; the proof
tree's `CounterWindow/*` and `AntiReplay/Statements.lean`; the s5 `vmlinux`
(SHA-256 `06513d05…e88e`) and its `.config`; `drivers/net/wireguard/` in
`.deps/linux`; `scripts/proof-gate`; the 2026-10-14 and 2026-11-10 entries of
`docs/decisions.md` (the last from `5accd5fb`); the reassessment and its
review (`921a125d`). The judgements are mine [AGENT].

## Verdict

**Do not sign the statement as written. Both clauses of the proposed headline
are false under the premises as the Lean states them, and the proposed
headline is the weaker of the two things the track exists to show.** The
first is a small, definite repair; the second is a choice for the owner, and
my advice on it differs from the packet's.

What can be relied on:

- The packet's measurements reproduce exactly: the generator check, the 972
  single visits, the eleven wrong variants, the six sequences, the surface
  line counts, the host `bts` table (section 1).
- Its reading of the image is right wherever I checked it against the ELF,
  the configuration and the C: the range, the three exits, the inlining
  context, the absence of any lock, the single `bts`.
- Its lists of what is not claimed are candid, and it reported against itself
  the one variant its headline does not exclude.
- The mirror agreed with the binary in every run, the packet's and mine. No
  Rule Zero discrepancy.

What cannot:

- `ExitsCleanly`, `NoCounterAcceptedTwice` and `Refines` as written (H1).
- The proposed headline as a statement of what the track set out to show
  (H2), and as something that is non-vacuous on its face (M1).
- The tests as evidence about the premises (M2).

## 1. Checks run

All from the review worktree, heavy steps through `capped`.

| Check | Result |
| --- | --- |
| `C2_BUILT_TREE=…/binary-reassessment binary/packets/c2/check` | All five modules compile. 972 runs, 564 accepted, 0 failures; the eleven variants fail 16, 8, 56, 160, 216, 112, 112, 108, 108, 112, 108 of 216; six sequences, 465 visits; the four sequence variants caught on 6, 6, 0, 2. Identical to the packet |
| `python3 -B binary/packets/c2/gen.py --check` | `C2Image.lean matches the pinned ELF`; 67 + 1 + 2 instructions, 324 bytes, 13 call sites, three callees |
| `binary/packets/c2/surface` | 115, 51, 47, 73 printed lines; 107 image lines. Identical |
| `bts_host.c` on this box (AMD Ryzen 9 7950X3D) | 1,536 runs, 0 disagreements; no flag but CF changed; the six out-of-range offsets address the quadword at `offset asr 6` |
| `objdump -d --disassemble=wg_packet_rx_poll` on the s5 ELF | The range, the exits, the code before the entry cut and after the exit cut read as the packet says (section 3) |
| `.config` of the s5 build | `CONFIG_SMP`, `DEBUG_SPINLOCK`, `PROVE_LOCKING`, `DEBUG_LOCK_ALLOC`, `LOCK_STAT`, `PREEMPT`, `RELOCATABLE`, `WIREGUARD_DEBUG` all unset; `NR_CPUS=1`; `PREEMPT_NONE`; KCOV with comparisons, instrumenting everything |
| Census of WireGuard's text (`handshake_init` to the end of `wg_get_device_dump`) | 14,208 instructions (the packet says about 14,500); one `bts`, two `bt`, no `btr`/`btc`, no LOCK prefix |
| `grep receiving_counter\|backtrack drivers/net/wireguard` | Writers of the window: `counter_validate` only (receive.c:319-326). Readers: receive.c:254 and 466. One caller (receive.c:461); `selftest/counter.c` is not built |
| My two-visit state (appendix) | **Both visits accept packet counter 63** with the window retained and every field of `Context` met; the coverage metadata is changed at the exit (H1) |
| My minimal-mapping run (appendix) | 2,430 runs on states that map only the bytes `Context` requires (27 cases, nine coverage settings including full buffers and unknown modes, five preempt counts, an aligned and an unaligned keypair address): all reach an exit, no fault |
| Intel's BTS and BT pages | Read through a mirror of the SDM text (section 2, L3). AMD's page could not be fetched |

## 2. Findings

Severity: **H** changes whether the statement can be signed; **M** changes
what is signed or what the evidence shows; **L** is a correction or a note.

### H1. Both clauses of the headline are false as written: the coverage buffer is not kept apart from the coverage metadata

`Context.coverageApart` (`C2Statement.lean:69`) keeps the coverage bytes away
from the range's own footprint (stack slots, window, preempt count). Nothing
keeps the coverage *buffer* away from the coverage *metadata*: `KcovState`
(`TrustBase.lean:257`) has no separation in it, and `Context` adds none. The
landed entries do have this premise (`LookupEntry.coverageMetadata`,
`TrustBase.lean:538`). The packet's premise table says more than the Lean
does: P7 lists the metadata and the buffer among things that are "pairwise
disjoint".

With a recording layout whose buffer covers the task's `kcov_area` field, the
first PC callback writes its return address over that field, and every later
callback in the visit records into wherever that address points. Since data
memory in the model is an arbitrary map, the window may be there.

The state (appendix, `Counter.lean`): task `T`, mode 2, capacity 8, area
`T+0x6d8` with count 1, so buffer word 2 is `T+0x6e8`, the area field; keypair
address chosen so that bitmap word 1 is at `0xffffffff8139d2dc`, the return
address of the first `__sanitizer_cov_trace_pc` call of the range; window
zero, stored counter 0.

- Visit 1, coverage off, packet counter 63: accepted; the window then holds
  counter 64 and word 1 = 1.
- Visit 2, the recording layout above, the same window bytes, packet counter
  63 again: the first PC callback redirects the area; the next three treat
  bitmap word 1 as the record count and step it 1, 2, 3, 4; the `bts` finds
  bit 0 clear. **Accepted.**

Output:

```
Context separation premises hold numerically for the aliased layout: true
visit 1 (coverage off, nonce 63): pc=donePC true, accepted true
window bytes retained between visit 1 exit and visit 2 entry: true
visit 2 (recording PCs, aliased layout, nonce 63): pc=donePC true, accepted true
acceptedNonces [visit1, visit2] = [63, 63]
kcov_area field at visit 2 exit: 18446744071582634716 (entry: 5244632); Kept.coverage needs it unchanged
```

So, for the statement with a real `bts` in place of the placeholder:

- `NoCounterAcceptedTwice` is false: `acceptedNonces` is `[63, 63]`.
- `ExitsCleanly` is false: at visit 2's exit `Kept.coverage` asks for
  `KcovMetadata layout`, and the area field no longer holds `layout.area`.
- `Refines` is false twice over (the mirror refuses the second 63; `Kept`).

This is a defect of the statement, not of the kernel or the mirror: no
running kernel has its coverage buffer over its own task structure. It is
evidence by execution in the packet's own harness (Kraken's interpreter for
69 instructions and the image's callbacks, the placeholder for the `bts`),
with the premises checked by reading and by arithmetic, not a kernel-checked
refutation.

*Repair.* One more field in `Context`, the landed discipline:
`∀ a, (layout.mode = 2 ∨ layout.mode = 3) → KcovStorageBytes layout a →
¬KcovMetadataBytes layout a`. By my reading that is the only missing pair:
the range writes only its footprint, the callbacks only the storage, and
every other pair is already separated. It is a new assumed line and a premise
the proof would have forced; it is not a narrowing to fit the mirror. The
owner should see the repaired `Context`, not this one.

*What it shows about the packet.* The premises that carry the difficulty are
the separation premises (P7, P9), and the packet's tests never probe them
(M2). The cost table's "main uncertainty" is the same place.

### H2. The proposed headline is the weaker half of the objective, and its evidence against vacuity is outside what is signed

In my words, a signer of `Headline` asserts, for the 70 instructions as
Kraken (plus one new instruction) executes them, one after another:

1. from any state at the entry address in which `%r13` and `%rbx` are any two
   addresses, 1032 bytes at `%r13+136` are mapped, three stack ranges are
   mapped, the coverage fields are readable, and the listed ranges are apart,
   execution reaches one of three addresses, with four registers and all
   memory outside the listed ranges unchanged and the preempt count 0x200
   higher;
2. over any list of such executions on one address whose 1032 bytes are equal
   from each exit to the next entry, the quadwords read at `%rbx+0x28` in the
   executions that end at the last address with `%bpl = 0` are distinct.

Nothing in it says a packet counter is ever accepted, that the bytes are a
counter and a bitmap, that the window advances, or that the mirror describes
this code.

**It is weaker than the words around it.** The packet's title is "machine
code to anti-replay" and the result is described as the landed theorem
transported. Clause 2 is a safety property alone. The packet reports one
wrong `bts` (the neighbouring bit) that the headline holds of. That is not a
slip in the headline; it is what a uniqueness-only claim is. Others of the
same kind, each of which would leave both clauses true:

- code that refuses everything (the packet says so);
- any fixed permutation of the bits within a word (the reported variant is
  one);
- a loop that clears no words, or fewer, on an advance (stale bits only cause
  refusals);
- a tighter too-old test or a lower limit (more refusals).

`AdvanceAccepted` excludes the first for counters that move to a later word
and nothing for counters inside the current window. It, `ReplayWitness` and
`ReplayRefused` are stated as "evidence the result would carry"
(`C2Statement.lean:195-225`) but are not conjuncts of `Headline` (line 151).
A signature on `Headline` does not commit the proof to them.

**The track's objective names both things.** The 2026-10-14 decision gives
the objective as the binary-level adequacy of the mirror and the transport of
its landed results. `Refines` is the adequacy statement for this function;
`NoCounterAcceptedTwice` is the transport. The packet proposes to sign the
transport and register adequacy as an internal lemma, on the ground that it
keeps the claimed surface small. Under the owner's definition, material the
headline does not mention is not charged to the reader; that makes the
measure reward a weaker claim, and here it does. The 73 printed lines saved
are the lines that say what the code does.

**Advice.** Sign the conjunction: `ExitsCleanly ∧ Refines ∧
NoCounterAcceptedTwice ∧ ReplayWitness`, with the floor clause if wanted.
`Refines` is proved either way (the packet says so), so the proof cost is the
same. What it adds to the claimed surface is `exitPC` (five lines, read
against the three tests in the disassembly: I did, and it matches),
`Layouts.ReplayFields` (five lines, landed), `windowOf` and the mirror's
`counterValidate`, which is the project's deliverable and already checked
against the kernel differentially. With `Refines` signed, `AdvanceAccepted`
is redundant. If the owner prefers the small headline, then at least
`ReplayWitness` and `AdvanceAccepted` belong in it, and the register should
call the result uniqueness, not the replay window.

`Refines` has one soft spot of its own: its premise that the mirror run
succeeds. That it always does for a 128-word bitmap is the landed
`mirror_step`, and `ReplayWitness` would show the conjunction inhabited.

### M1. What is signed is not what would land, and today it holds vacuously

`Reading` includes `Placeholder.BtsAt`, which asks the decoder for an
instruction at `…d3dd` that behaves as `bts`. The pinned Kraken has none, so
no decoder satisfies `Reading`, every statement with `Reading` as a premise is
true for no reason, and `ReplayWitness` is false. The packet says this in
section 12 in milder terms. The consequences for the signer:

- The statement that lands differs in form: `Reading` loses a field, the
  image gains a term, and the semantics moves into Kraken. What is signed now
  should be recorded as "this statement with `BtsAt` discharged by the patch",
  and the final text shown again with its diff before the proof is accepted.
- The packet's order (headline and budget first, patch second) should be
  reversed: the patch's semantics is part of what the headline means.

### M2. The tests exercise the conclusions directly and the premises only through one rendering

Used directly by the tests: `exitPC`, `accepted`, `windowOf`,
`Placeholder.btsResult`, `Range.fetch`, the `Layouts` constants, the mirror's
`counterValidate`. Re-rendered as code: `Context` (`Test.initial`/`memory`),
`Kept` (`Test.kept`), `ReplayFields` (`represented`), `WindowRetained` and
`Visits` (the loop in `Sequence.machine`), `BtsDefined`, and the step relation
(`Test.effects`, the packet's own interpreter of Kraken's effects, not
`instructionStep`).

- No test shows that a constructed state satisfies `Context`; the states are
  built to, by the author's reading. All of them come from one family: fixed,
  far-apart, aligned addresses and a stack mapped well beyond what `Context`
  requires. No test looks for a state that meets `Context` and breaks the
  conclusion, which is how H1 was missed. `Test.kept` does not check the
  metadata half of `Kept.coverage`.
- I added the opposite test: states mapping only the required bytes. 2,430
  runs, no fault, so the mapping premises (P6, P8, P9) look sufficient.
- The eleven variants: five perturb `exitPC`, `accepted` or the preempt step,
  two the representation, four the placeholder. All eleven are caught by the
  byte comparison with the mirror, that is by the rendering of `Refines` and
  `Kept`. None perturbs a premise of `Context`. They show the single-visit
  check is sensitive; they show nothing about the proposed headline, whose
  clause 2 is exercised only in `C2Sequence`, where of four variants one is
  caught by uniqueness, one only by the mirror comparison, one by neither, and
  one is the broken premise.
- Undefined flags are driven by two seeds; the host run changed no undefined
  flag, so hardware never exercised that freedom.

### M3. Where the joining proof lives: option A does weaken a gate check, and the choice depends on H2

The proof gate fails "if anything outside the tree imports it"
(`scripts/proof-gate`, check 4; AGENTS.md). Option A exempts one path. The
packet says so. Three things it does not say:

- Under option A with the machine-level headline, **the headline theorem
  itself lives in the bridge**, a third target. "The binary gate or a sibling
  prints the bridge's axioms" is not a commitment. Unless a named gate builds
  the bridge and checks its axioms, the track's headline is in no gate.
- If `Refines` is in the headline (H2), the adequacy claim needs no import of
  the proof tree and no rule change: it mentions only the mirror and stays in
  the binary package under the existing rule. Only the transported clause
  needs the join.
- The scratch check that `AcceptsAsPureWindow` elaborates against both sides
  is not committed and I did not reproduce it.

If the owner takes option A, the conditions I would attach: the exemption is
one exact path written into AGENTS.md by the owner; the import is limited to
the four `CounterWindow` modules; a named gate builds the bridge and applies
the axiom check and the forbidden-token scan to it; the register records the
bridge's result as lagging when those modules change. With those, the
weakening is one line of an import check and no check of proofs is lost.
Option B changes no rule and is honest if described as a re-checked copy.
Option C should not be taken. I agree with the packet against option D.

### M4. The gap to "a replayed packet is dropped by this receive path"

The packet's five items are right. The full list of what would still have to
be shown, as I read the code:

1. After the range: `__local_bh_enable_ip` and the comparison callback
   preserve `%bpl`; the `jne` at `…d402` goes to `…d823`; that path drops the
   references and frees the packet without delivering it (`wg_noise_keypair_put`,
   `wg_peer_put`, then `sk_skb_reason_drop` on the packet at `…d84a`). Both rejection exits reach the same path
   without testing `%bpl` (`…d80d` falls into `…d823`; `…d9c3` jumps to
   `…d828`). I read this in the disassembly; none of it is in the statement.
2. Before the range: `%r13` is the keypair the packet was decrypted under and
   the quadword at `skb+0x28` is the counter that was used as the AEAD nonce,
   unchanged since decryption. I confirmed the loads (`mov 0x30(%rbx),%r13` at
   `…d28f`, state test at `…d298`), that the entry cut is reached only by
   falling through from `…d2a1`, and that the two callbacks between do not
   touch `%r13` or `%rbx`.
3. The premises of `Context` hold there: the frame, the keypair as an object
   apart from the stack, the coverage state. Argued, not derived.
4. Every reception that leads to delivery passes through the range, and the
   list of visits is all executions on that window. The second is folded
   into `WindowRetained`.
5. No other code writes a live keypair's window; address reuse after a free is
   a different key. I found no other writer in the driver.
6. One CPU, no interrupt between instructions, fixed text: the model. The
   image's text is what runs (no alternatives in the range, not relocatable:
   checked).
7. Kraken's semantics for 69 instructions and the new one.
8. That a replayed packet has the same counter under the same key: the
   protocol and the AEAD, outside this result.
9. This build: one CPU, coverage-instrumented. Nothing carries to an SMP
   build, where the lock and `lock bts` are real.

### M5. The premises against the image, the source and the caller

- *Inlining context (P5).* Believable; checked as in M4 item 2.
- *Mapping (P6, P8).* Sufficient on my minimal-mapping run. The spill slots
  `0x10(%rsp)` and `0x18(%rsp)` are inside the frame (`sub $0x68,%rsp`).
- *Separation (P7).* Short by one pair: H1.
- *Coverage (P9).* The callbacks are read from the image, not assumed, which
  is right. `KcovState` asks that the buffer's count be within capacity; in a
  running kernel that word is in memory shared with a user process. This is
  inherited from the landed results and satisfiable, but it is an assumption
  about another party.
- *Window unchanged (P10).* Believable for the C as written; it is the place
  where keypair lifetime, the completeness of the visit list and the absence
  of other writers all sit. It is a premise about the rest of the kernel and
  should be called that in the register.
- *No lock.* Confirmed: the configuration, the single `addl $0x200`, no LOCK
  prefix. The `0x200` step also shows `PREEMPT_COUNT` is off. The packet is
  right that this is the main limit on what the result means.
- I found no premise that is unsatisfiable in a running kernel.

### L1. `Kept` does not carry what the next instruction needs

The range ends between `mov $0x200,%esi` and the `lea`/`call` of the unlock
that uses it. `Kept` does not say `%esi = 0x200` at `donePC`, so the result
as stated does not compose with a later result about the unlock (decision 6).
Either state it or move the cut.

### L2. Surface figures

They reproduce. Under the owner's definition I would add to the assumed side:
the new premise of H1; the parser case and the `Operation` constructor of the
tenth patch (the packet counts only the semantics, about 12 lines); the label
instance `Image.linkedLabels` through which the `L_…` targets get their
addresses. If H2's advice is taken the claimed side grows by the 73 "internal"
lines less the three vacuity statements, plus `ReplayFields` and the mirror
function. I did not recount the "about 85" and "about 80" inherited lines.

### L3. The proposed `bts` semantics

- *Intel* (SDM vol. 2A, BTS and BT, read through a mirror of the text): CF
  receives the selected bit, then the bit is set; "The ZF flag is unaffected.
  The OF, SF, AF, and PF flags are undefined"; with a memory bit base the
  operand addresses the byte holding bit 0 of a bit string and a register
  offset may reach outside the operand; the processor may access the whole
  operand-sized unit at `EA + size * (offset DIV bits)`. The proposal agrees.
  The mirrored text gives the access formula for 16 and 32 bits only; the
  host run confirms the 64-bit analogue.
- *AMD* (APM vol. 3): I could not fetch it either. From memory it lists OF,
  SF, ZF, AF and PF undefined and treats a register index on a memory operand
  as a signed offset; the host, an AMD processor, behaves so. **Unverified
  against the page.**
- Taking ZF as undefined is the sound choice for a universally quantified
  claim: it contains "unaffected".
- The restriction to offsets 0..63 is sound for this instruction: `%r15` is
  set by `and $0x3f,%r15d` at `…d3d1`, which also clears the upper half, and
  only a `lea` into `%rax` lies between. A declined offset is a failing step,
  so it cannot make a reaching claim true. One caution for the patch's
  description: for statements with an actual-history premise (`FirstExit`), a
  declined step removes histories; that is harmless here only because
  `ExitsCleanly` shows the step is never declined.
- Reading and writing all eight bytes is what the manuals permit and at
  least as demanding as the hardware.

### L4. Cost

The 12 to 22 worker-hours cannot be checked; its basis is a trial that the
reassessment's review found unreviewed and differently shaped. It leaves out
the repair of H1 and a search for further aliasing counterexamples, the
re-presentation of the final statement (M1), the gate work of option A, and
the review of the patch against the manuals. The item it names as the main
uncertainty, coverage state through up to 256 callbacks, is where H1 was
found. I would plan on the upper end and treat the lower as unlikely.

### L5. Slips

- `AcceptedWithinWindow` is said to follow "the same way" from
  `step_accepted_bounds`. That theorem bounds the stored counter; the clause
  is about pairs of accepted counters and needs the stored counter's
  monotonicity as well.
- P7 says "pairwise disjoint"; the Lean is not (H1).

## 3. Verified, inferred, not checked

*Verified by running or reading the artifact:* everything in section 1; the
disassembly facts in M4 and M5; `exitPC` against the three tests; the landed
theorems' statements (`mirror_step`, `accepted_nodup`, `pure_uniqueness`,
`step_accepted_bounds`) and that `windowOf` is `counterAt` textually;
`Eventually` is inductive, so clause 1 is a reaching claim.

*Inferred:* that no decoder satisfies `Reading` today (M1: no instruction of
the pinned Kraken sets a memory bit from a register offset); that one added
premise repairs H1; that the statements are true once repaired.

*Not checked:* AMD's manual; the scratch elaboration of
`AcceptsAsPureWindow`; the inherited line counts; the binary package's own
suites and gates; anything in a guest. No proof was attempted.

## 4. To the signer

**Do not sign as is. Sign with these named changes:**

1. `Context` gains the separation of the coverage buffer from the coverage
   metadata (H1), and the author reruns a search for states that meet
   `Context` and break a conclusion. Without this the headline is false.
2. The headline is `ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧
   ReplayWitness` (H2). If you prefer the machine-level form, add
   `ReplayWitness` and `AdvanceAccepted` to it and have the register call the
   result uniqueness of accepted counters in a single-CPU, instrumented
   build.
3. Decide the tenth patch first; record that what you sign is the statement
   with `BtsAt` discharged, and see the final text and its diff before the
   proof is accepted (M1).
4. If the join goes in a bridge, a named gate builds it and checks its axioms
   (M3).

Why: the first is a falsehood with a two-line repair; the second is the
difference between a result that says this code is the replay window the
mirror describes and one that says only that it never accepts a counter
twice, at the same proof cost. The rest of the packet (the reading of the
image, the limits it states, the `bts` proposal, the candour about its own
tests) I found sound.

## Appendix: the two scratch tests

Compiled as the packet's `check` compiles its modules, with
`LEAN_PATH=<built tree's>:.tmp/c2-packet/build`, after `check` has run. Not
committed as files; they are reproduced from this text.

`Counter.lean` (H1):

```lean
import C2Sequence
namespace Review
open Binary TrustBase Leanux Binary.C2 Binary.C2.Test

def R : Nat := 0xffffffff8139d2dc   -- return address of the range's first trace_pc call
def kpR : Nat := R - 152            -- bitmap word 1 (kp+144+8) is at R
def T : Nat := 0x500000
def A : Nat := T + 0x6d8            -- coverage area: word 2 is the task's kcov_area field
def cap : Nat := 8

def mem (nonce : Nat) (rogue : Bool) (window : Option DataMem) : DataMem := Id.run do
  let mut m : DataMem := ∅
  for (a, n) in [(sp - 0x40, 16), (skb, 8), (T + 0x6c0, 12), (taskAddr, 6)] do
    for i in [:n] do m := put m (a + 8*i) 8 (filler (a + 8*i))
  for i in [:129] do
    let v := match window with
      | some old => ((old.loadInt (.ofNat 64 (kpR + 136 + 8*i)) 8).getD 0).toNat
      | none => 0
    m := put m (kpR + 136 + 8*i) 8 v
  m := put m (skb + 0x28) 8 nonce
  m := put m taskAddr 8 T
  m := put m preemptAddr 4 0
  m := put m (T + 0x6e0) 4 (if rogue then 2 else 0)
  m := put m (T + 0x6e4) 4 cap
  m := put m (T + 0x6e8) 8 A
  m := put m (T + 0x704) 4 1
  m := put m A 8 1
  return m

def st (m : DataMem) : MachineState :=
  ⟨{ regs := { rsp := .ofNat sp, r13 := .ofNat kpR, rbx := .ofNat skb, r12 := 0x1234 }, dmem := m }, Range.entry⟩

def apart (lo n lo' n' : Nat) : Bool := lo + n ≤ lo' || lo' + n' ≤ lo
def contextSeparation : Bool :=
  let foot := [(sp - 8, 8), (sp + 0x10, 16), (kpR + 136, 1032), (preemptAddr, 4)]
  let cov := [(taskAddr, 8), (T + 0x6e0, 4), (T + 0x6e4, 4), (T + 0x6e8, 8), (T + 0x704, 4), (A, 8 * cap)]
  cov.all fun (a, n) => foot.all fun (b, k) => apart a n b k

#eval show IO Unit from do
  IO.println s!"Context separation premises hold numerically for the aliased layout: {contextSeparation}"
  let s1 := st (mem 63 false none)
  let (t1, _) ← IO.ofExcept (run .image .placeholder 1 s1)
  IO.println s!"visit 1 (coverage off, nonce 63): pc=donePC {t1.pc == Range.donePC}, accepted {accepted t1}"
  let s2 := st (mem 63 true (some t1.data.dmem))
  let same := (List.range 1032).all fun i =>
    s2.data.dmem.get? (.ofNat 64 (kpR + 136 + i)) == t1.data.dmem.get? (.ofNat 64 (kpR + 136 + i))
  IO.println s!"window bytes retained between visit 1 exit and visit 2 entry: {same}"
  let (t2, _) ← IO.ofExcept (run .image .placeholder 1 s2)
  IO.println s!"visit 2 (recording PCs, aliased layout, nonce 63): pc=donePC {t2.pc == Range.donePC}, accepted {accepted t2}"
  IO.println s!"acceptedNonces [visit1, visit2] = {acceptedNonces [⟨s1, t1, 63⟩, ⟨s2, t2, 63⟩] |>.map (·.toNat)}"
  let area ← IO.ofExcept (readNat t2.data.dmem (T + 0x6e8) 8)
  IO.println s!"kcov_area field at visit 2 exit: {area} (entry: {A}); Kept.coverage needs it unchanged"
```

The layout witnessing `Context` for visit 2 is task `T`, area `A`, capacity
8, mode 2, softirq flag 1, preempt 0. The stack, window and preempt ranges
are apart from each other by inspection (`0x4007f8…`, `0xffffffff8139d2cc` to
`…d6d4`, `0xffffffff81cc85c8`).

`Minimal.lean` (M2): builds states from the empty memory by mapping, byte by
byte, only `[sp-8,sp)`, `[sp+0x10,sp+0x20)`, the 1032 window bytes, the
quadword at `skb+0x28`, the current-task word, the preempt count, the four
task fields at `0x6e0`, `0x6e4`, `0x6e8`, `0x704`, and in modes 2 and 3 the
64-word buffer; then runs `Test.run .image .placeholder` over the packet's 27
`cases`, the settings (mode, records) `(0,0) (2,0) (2,62) (2,64) (3,0) (3,9)
(3,64) (1,0) (7,0)`, preempt counts `0, 0x100, 0xfffffe00, 0x10000,
0xfffffd00`, and keypair addresses `kp` and `kp+3`. Output: `minimal mapping:
2430 runs, 0 failures`.

## Follow-up on revision 2 (2026-11-10)

Reviewed: `cf8798e5` on `task/binary-c2-statement`, the revision made after
the review above: the revised `C2Statement.lean`, the new
`C2Adversarial.lean`, the revised `C2Test.lean`, `check` and `surface`, and
the rewritten packet document with its dispositions table (section 12). I
read the Lean diff first and the table afterwards. The original findings
above are left as written; they describe `e05ffd8f`. Judgements mine [AGENT].

### Verdict

**The statement can now be signed in the recommended form,
`HeadlineRefinement`, on the terms revision 2 itself sets (the patch decided
first; the final text and its diff seen again before a proof is accepted).**
Every finding is resolved in the Lean or honestly answered; the repair
introduced nothing I could find; my own search, built differently from the
author's, found no state meeting the revised premises that breaks a
conclusion. Two residual points (F1, F2) are improvements I would ask for,
not conditions.

That is a judgement on the statement, not a claim that it is true: no proof
exists, and until the patch exists every statement here is still vacuous, as
revision 2 now says in its first section.

### Checks run

| Check | Result |
| --- | --- |
| Revision 2's `check`, from a copy of its `binary/packets/c2` extracted with `git archive` | All six modules compile. Single visits, variants and sequences as before. Search: 775 single placements, 6,200 states, 2,595 meet the old `Context`, 2,377 the revised, broken on 100 (old only) and 0 (revised), replay accepted on 13 and 0; 921 pairs, 3,684 states, 1,084 and 896, broken on 87 and 0, replay 1 and 0. Identical to the packet |
| Revision 2's `surface` | 122 assumed, 51 placeholder, 95 claimed with `Refines`, 76 machine-only, 15 other. Identical |
| My random-arena search (below) | 6,000 states; 1,565 meet the old `Context`, 1,548 the revised; conclusions broken on 2 (old only), **0 (revised)**; replay accepted on 0 |
| The author's single placements at capacities 0, 1, 2, 3 and 40 (the packet runs capacity 8 only) | 28,568 states, 9,442 meeting the revised `Context`; broken on 0, 0, 18, 49, 87 meeting only the old, **0 meeting the revised**; replay accepted on 0, 0, 4, 13, 13 (old), **0 (revised)** |
| `step_counter_mono`, `accepted_remembered` | Exist in `CounterWindow/Model.lean` (lines 109, 164), as the revised floor argument says |

The random-arena search places all five objects (stack pointer, keypair,
packet, task, coverage area) uniformly in one arena of 1,500 or 2,400 bytes,
so that near-overlaps of several objects at once are the norm rather than
constructed one pair at a time; capacity 0 to 6, record count up to capacity,
modes 0, 2 and 3, three preempt counts, three build orders, random or zero
window contents, six shapes of stored and packet counter. It reuses the
author's `build`, `contextHolds`, `broken` and `replayAccepted`, so it is
decorrelated in where it looks, not in how it judges.

### The findings, one by one, against the Lean

| Finding | Resolved? | Basis |
| --- | --- | --- |
| H1 | **Yes.** | `Context.coverageMetadata` (`C2Statement.lean`, the new last field): in a recording mode no byte of `KcovStorageBytes` (header and buffer) is a byte of `KcovMetadataBytes`. That is the pair that was missing, in the landed form. I went through the written and read regions again: the range writes its footprint, the callbacks write storage, and each of those is now separated from everything read afterwards (window, spill slots, return slot, preempt count, metadata). The packet counter is read once, first, so it needs no separation. The premise table's P7 now lists exactly the pairs the Lean has, with P7b for the new one |
| H1, the search | **Yes, within what a search is.** | See the next subsection |
| H2 | **Yes.** | `HeadlineRefinement` (`ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness`) is defined and recommended; `HeadlineMachine` carries `ReplayWitness` and `AdvanceAccepted` as conjuncts. The comparison table's row on which wrong implementations survive each form is accurate, including what form (i) leaves free |
| M1 | **Yes.** | Section 0 states the vacuity and what is signed now and later; the patch is decision 1. Nothing in the Lean could change here before the patch |
| M2 | **In part, and the rest is stated as a limit.** | `Test.kept` now checks the metadata half and `%esi`. Premises are checked on every searched state. Still true, and said in section 8: the checks are renderings; the interpreter is the packet's own; two flag seeds |
| M3 | **Yes.** | Section 9 states the weakening, adopts the four conditions, and says without the named gate option A should not be taken. It also notes that only the transported clause needs the join |
| M4, M5 | **Yes.** | The nine items and the premise notes are in sections 4 and 5 |
| L1 | **Yes.** | `Kept.unlockArgument : t.pc = Range.donePC → t.data.regs.rsi.toNat % 2 ^ 32 = 0x200`. True of the code (`mov $0x200,%esi`, then only `setb`), and what the unlock's 32-bit argument needs |
| L2 | **Yes.** | Counted in section 7; reproduced |
| L3 | **Answered.** | AMD's page is still unread by anyone and is named as an item for the patch's review. That is the right place for it; the owner should know the patch decision is being taken with one vendor's text checked |
| L4, L5 | **Yes.** | 16 to 29 hours with the upper end advised; the floor argument names the two further lemmas, which exist |

### Did the repair introduce anything new?

- *A premise too strong for a running kernel?* No. The coverage buffer is a
  vmalloc area and the metadata is a per-CPU word and four fields of a task
  structure. The premise binds only in recording modes.
- *A conclusion weakened?* No. `Kept` gained a field and lost none;
  `ExitsCleanly`, `Refines`, `NoCounterAcceptedTwice`, `ReplayWitness` and
  `AdvanceAccepted` are textually unchanged apart from comments. The headline
  conjunction is stronger than revision 1's.
- *Prose that no longer matches?* I found none. Section 3's abridged Lean, the
  premise listing in section 5 and the statement file agree; the line counts
  are the ones the script prints.

### The adversarial search: what it tests, and what it leaves

It tests a **rendering** of the premises, not the Lean `Context`:
`contextHolds` is a hand-written decision of each field over explicit byte
sets modulo 2^64. I read it field by field against `Context`, `KcovState`,
`KcovMetadataBytes` and `KcovStorageBytes` and found it faithful, including
the new field; nothing connects the two but that reading. If it were stricter
than `Context` somewhere, it would hide counterexamples; I found no such
place. The conclusions are likewise rendered (`broken`), now including the
metadata. The search has a sound control built in: it fails unless it
rediscovers the old hole by itself, and it does, in three kinds, one of
which (a fault) my example had not shown.

What it leaves uncovered:

- Capacity was fixed at 8 and placements were single or paired. My two
  additional runs cover capacities 0 to 6 and 40 and many-object proximity,
  and found nothing; I suggest the author fold the capacity loop into the
  committed search, which costs minutes.
- Clause 3 is exercised only as one shape: an accepting visit with coverage
  off, then one adversarial visit with the same counter. Longer sequences
  under adversarial layouts, and an adversarial first visit, are not run.
  Since a single visit's window bytes are compared with the mirror on every
  passing state, and the sequence property follows from that by the landed
  theorem, this is a small gap.
- Nothing probes the instruction semantics, the undefined flags beyond one
  seed, or coincidences involving the wrap of a very large buffer.
- None of this is kernel-checked. The piece that will be is `ReplayWitness`.

I would not hold the signature for any of these.

### Is `HeadlineRefinement` what I would advise signing?

Yes. Two residual points:

**F1 (low). `Refines` is not shown inhabited by the headline itself.**
`ReplayWitness` exhibits states meeting `Reading`, `Context` and `Visits`.
`Refines` has three further premises: a replay state the bytes represent, a
world holding it, and a successful run of the mirror's function. That these
can always be met is true (the representation is total on mapped bytes; the
landed `mirror_step` gives the run), but the first is a lemma outside the
headline and the second lives in the proof tree, which the binary package
may not import. A reader of the headline alone cannot tell that `Refines` is
not conditional on something rare. Cheap repair, the author's choice of
form: extend `ReplayWitness` so that its first visit also comes with a
world, a replay state and a successful mirror run (a closed evaluation, the
kind the tests already do); or state a totality conjunct, "for every state
meeting `Context` there are a replay state, a world and a successful run".
The second is the stronger and is what makes `Refines` a description of the
code on every premise-meeting state, which is how section 3's table
describes it.

**F2 (note). The renderings are the author's.** Before the proof is
accepted, the reviewer of the final text should check `contextHolds` against
the then-current `Context` again, since both will have been touched by the
patch's arrival.

Unchanged from the first review and still for the owner to weigh: the result
is about a single-CPU, coverage-instrumented build under a sequential model;
`WindowRetained` is a premise about the rest of the kernel; AMD's manual page
is unread; the cost is uncheckable and the upper end should be planned on.

### To the signer, updated

**Sign `HeadlineRefinement` as written in `cf8798e5`, in the order revision 2
sets: the `bts` patch first; then the headline, as the statement with `BtsAt`
discharged; the final text and its diff back to you before any proof is
accepted.** Ask for F1 with the final text; it does not need another round
now. For the joining proof, option A only with its four conditions, the
named gate among them; otherwise option B. My first review's "do not sign"
applied to `e05ffd8f` and is met by this revision.

Not checked in this follow-up: the packet's `gen.py --check` and host `bts`
run were not repeated (their inputs are unchanged); AMD's manual; the
scratch elaboration of the join; anything in a guest.
