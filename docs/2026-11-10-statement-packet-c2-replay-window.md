# Statement packet C2: the receive replay window, machine code to anti-replay

2026-11-10, on `task/binary-c2-statement`. **Revision 2**, after the
independent review of revision 1 (`e05ffd8f`; the review is
`docs/2026-11-10-review-statement-packet-c2.md` at `c9ee6100` on
`task/review-c2-statement`, not on this branch). The
review's advice was not to sign revision 1 as written. Every finding is
disposed of in [section 12](#12-dispositions-of-the-review-findings); the two
that change what is signed are:

- **Revision 1's statements were false as the Lean stated them** (finding H1):
  nothing kept the coverage buffer off the coverage metadata, and the reviewer
  built a state meeting the premises on which packet counter 63 is accepted
  twice. I reproduced it, added the missing premise in the landed form, kept
  the counterexample as a test, and ran the search for premise-meeting,
  conclusion-breaking states that revision 1 lacked (section 8). Nothing else
  fell out; that is a search result, not a proof.
- **The headline I proposed was the weaker half of the track's objective**
  (finding H2). Both forms are now laid out side by side (section 3) and I
  recommend the reviewer's.

Statements and their justification for one proposed result of the binary
track; **no proof exists and none was attempted**. Everything here is a
proposal [AGENT] for the owner's decision under the 2026-11-10 entry of
[decisions.md](decisions.md). It scopes the result the
[reassessment](2026-11-10-binary-track-reassessment.md) calls C2.

The Lean is in `binary/packets/c2/`, in no lake target and scanned by no gate:
`C2Statement.lean` (every statement, as `def`s and `structure`s of
propositions), `C2Placeholder.lean` (the missing instruction), `C2Image.lean`
(generated terms), and the executed tests `C2Test.lean`, `C2Sequence.lean`
and `C2Adversarial.lean`. No tracked file other than the index row was
changed.

Reading guide: sections 0 to 6 and 10 are what there is to sign; 7 to 9, 11
and 12 are the measurements and arguments behind them.

## 0. What is asked for, in order

**First, the Kraken patch (section 1).** The range contains one instruction,
`bts %r15,(%rax)`, that the pinned Kraken cannot express. Its meaning is part
of what every statement below means, so that decision comes before the
headline.

**Until that patch exists, every statement here is vacuous.** Each has the
premise `Reading fetch`, which includes the placeholder `BtsAt fetch`: that
the decoder holds, at the `bts`'s address, an instruction behaving as section
1 specifies. The pinned Kraken has no such instruction, so no decoder
satisfies `Reading`; every statement with that premise is true for no reason,
and the witness `ReplayWitness` is false. Consequently:

- *What would be signed now:* the semantics of section 1 as the content of a
  tenth patch, and the statements of section 3 **with `BtsAt` discharged by
  that patch**: their shape, premises and conclusions.
- *What would be signed after the patch, before any proof is accepted:* the
  final text and its diff against this one. `Reading` loses its `bts` field,
  `C2Image.lean` gains the seventieth term, `C2Placeholder.lean` is deleted,
  the semantics is in Kraken. Nothing else should differ; if it does, the
  difference is shown.

**Second, the headline (section 3).** Two forms are put side by side. I
recommend `ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness`:

1. *Exits cleanly.* From any state at `0xffffffff8139d2a6` meeting the entry
   premises, Kraken's sequential execution of the 70 instructions of the
   inlined `counter_validate` reaches one of three exits without faulting,
   having written only its call-return slot, two spill slots, the 1032 window
   bytes, the preempt count (0x200 higher) and the coverage buffer.
2. *Refines the mirror.* If the window bytes represent a replay state and the
   mirror's `counterValidate` on that state returns a result and a new state,
   the machine takes the exit the three tests name, the byte it branches on
   next (`%bpl`) agrees with the mirror's result, and the window bytes
   represent the mirror's new state.
3. *No counter accepted twice.* Over any sequence of executions of the range
   on one keypair address, between which the window bytes are unchanged,
   starting from any mapped contents, the packet counters of the accepting
   executions are pairwise distinct. This is the landed anti-replay theorem
   transported.
4. *A witness.* The premises can be met, by a replay that is accepted once
   and refused once.

**Then** the home of the proof that joins the binary package to the proof
tree (needed by clause 3 only; section 9), the budget, and four smaller
decisions (section 10).

**Testing found no discrepancy between the mirror and the binary.**

## 1. First decision: the missing instruction, a proposal for a tenth Kraken patch

Verified: the pinned Kraken (`43df9468`, the checkout the nine patches
produce) has no `bts`, `btr` or `btc` in any form: no `Operation` constructor,
no parser case; only register-register `bt` (patch nine), whose tests assert
that `bt %ecx,(%rax)` and `lock bt` fail to parse.

*Forms used.* The range uses exactly one: `bts r64, m64` with a register bit
offset, `REX.W 0F AB /r`, unlocked, with the offset already masked to 0..63 by
the preceding `and $0x3f,%r15d`. In WireGuard's text (`handshake_init` to the
end of `wg_get_device_dump`, about 14,500 instructions) it is the only `bts`,
`btr` or `btc`; the only other bit tests are the two register `bt` of
`add.isra.0` that patch nine covers. No instruction in that text carries a
LOCK prefix, and `.smp_locks` is empty.

*Proposed semantics* (the placeholder, `C2Placeholder.lean`; until the patch exists it is the premise `BtsAt`, which nothing satisfies):

- Syntax: one new `Operation`, `bts (dst : Mem) (index : Reg w)`, parsed for
  `bts`/`btsq` with a 64-bit register source and a memory destination only.
  Register destinations, immediates, 16- and 32-bit forms and any LOCK prefix
  fail to parse, as patch nine does for `bt`.
- Defined when the register's value is below 64 and the eight bytes at the
  effective address are mapped. A larger or negative offset, where the
  hardware addresses another quadword at `ea + 8 * (offset asr 6)`, is an
  explicit `unimplemented`, not modelled. (Alternative: model it. It is three
  more lines and was confirmed on the host, but nothing in the image needs it
  and it is more to trust.) A caution for the patch's description: a declined
  step is a failing step, so it cannot make a reaching claim such as
  `ExitsCleanly` true; but for a statement with an actual-history premise
  (`FirstExit`) a declined step removes histories. That is harmless here only
  because `ExitsCleanly` shows the step is never declined.
- Effect: read the quadword; `CF :=` the selected bit; write the quadword back
  with that bit set; advance the PC. The write is unconditional, as on
  hardware (the destination is written even when the bit was set).
- Flags: CF defined. OF, SF, AF, PF undefined (Intel SDM vol. 2A, BTS; AMD APM
  vol. 3, BTS). ZF: Intel says unaffected, AMD lists it undefined; taken as
  undefined, the choice patch nine made for `bt`. Nothing after the
  instruction reads a flag but CF (`setb`). Undefined contains "unaffected",
  so it is the sound choice for a universally quantified claim. Verification:
  the reviewer read Intel's BTS and BT pages through a mirror of the SDM text
  and found the proposal in agreement (the mirrored text gives the access
  formula for 16 and 32 bits only; the host run confirms the 64-bit
  analogue). **AMD's page has not been read by me or by the reviewer**; what
  is said of it is from memory and from patch nine's message, and the host,
  an AMD processor, behaves so. Checking it is an item for the patch's
  review.
- Atomicity: there is no LOCK prefix to model. In the sequential model the
  instruction is one step. On one CPU that is also what the hardware does with
  respect to interrupts, which are taken between instructions; nothing is
  claimed about another processor.

*Tests the patch would carry*, in patch nine's form: `#guard`s for CF and the
stored word at offsets 0, 1, 63 on words with the bit clear and set; that the
neighbouring quadwords and every register are unchanged; that each of the five
undefined flags can come out either way from either incoming value; that
offset 64 and an unmapped address do not execute; that the register,
immediate, narrow and locked forms do not parse; a native comparison of CF and
memory in the Kraken runner; and `bts_host.c`'s table.

*Also needed in the package* (tracked files, so part of the proof work, not of
this packet): `bts` in `RegionOperation`/`operation_mono`; the patch hash and
the Kraken identity in `dependencies/sources.lock.json`, `TrustBase.lean` and
`binary/README.md`.

## 2. The code

`counter_validate` (drivers/net/wireguard/receive.c:295-331) has one caller
and is inlined into `wg_packet_rx_poll`. In the pinned s5 image (ELF SHA-256
`06513d05…e88e`, found at `.artifacts/kernel-net-choice-s5` in the main
checkout and used for everything below):

| Addresses | Instructions | What |
| --- | ---: | --- |
| `…d2a6` (entry cut) | 1 | `mov 0x28(%rbx),%r14`: the packet's counter, `PACKET_CB(skb)->nonce` |
| `…d2aa` | 1 | `addl $0x200, pcpu_hot+8`: all of `spin_lock_bh` in this build |
| `…d2b4`–`…d321` | 22 | the three rejection tests, each preceded by a comparison callback |
| `…d326`–`…d3ad` | 35 | the advance test and the loop clearing bitmap words |
| `…d3b2`–`…d3d5` | 8 | store of the new counter; word index and bit |
| `…d3dd` | 1 | `bts %r15,(%rax)` (`4c 0f ab 38`): test and set, no LOCK prefix |
| `…d3e1`, `…d3e6` | 2 | `mov $0x200,%esi`; `setb %bpl` |
| `…d3ea` (exit cut `donePC`) | | next: `__local_bh_enable_ip`, then `test %bpl,%bpl; jne` |

70 instructions, 324 bytes, 13 call sites to three KCOV callbacks
(`__sanitizer_cov_trace_pc`, `_trace_cmp8`, `_trace_const_cmp8`). Three exits:

- `donePC` `0xffffffff8139d3ea`, with `%bpl` = the bit's old value: 0 is
  acceptance, 1 a replay inside the window;
- `rejectWindowPC` `0xffffffff8139d80d`: the stored counter is past the limit,
  or the packet is older than the window (two C tests, one exit);
- `rejectLimitPC` `0xffffffff8139d9c3`: the packet's counter is at the limit.

The image has two rejection exits where the C has one `goto out`. Bottom halves
are still disabled at every exit: the unlock comes after each.

The build is single-CPU (`CONFIG_SMP` not set, no lock debugging): `spinlock_t`
has size zero (the DWARF layout puts `lock` and `backtrack` at the same offset
8), the lock is the one `addl`, and the `bts` carries no LOCK prefix. **There
is no lock in this code to reason about.** The model executes the `addl` as a
32-bit add to a memory word; the callbacks read that word, and what they do
with it is inside their contracts.

## 3. The statements in Lean, and the two headline forms

From `binary/packets/c2/C2Statement.lean`, abridged: binder types omitted and
three of `Kept`'s four register fields elided.

```lean
def exits : List Int64 := [Range.donePC, Range.rejectWindowPC, Range.rejectLimitPC]

def accepted (t : MachineState) : Bool :=
  t.pc == Range.donePC && t.data.regs.rbp.toNat % 256 == 0

structure Kept (layout) (preempt : BitVec 32) (kp : BitVec 64) (s t : MachineState) : Prop where
  coverage : KcovState layout (preempt + 0x200) t.data.dmem
  rsp : t.data.regs.rsp = s.data.regs.rsp      -- likewise rbx, r12, r13
  unlockArgument : t.pc = Range.donePC → t.data.regs.rsi.toNat % 2 ^ 32 = 0x200
  frame : EqualOutside
    (fun a => Footprint s.data.regs.rsp.toBitVec kp a ∨
      ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout a))
    s.data.dmem t.data.dmem

def ExitsCleanly : Prop :=
  ∀ fetch layout preempt s kp skb nonce,
    Reading fetch → Context layout preempt s kp skb nonce →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        Kept layout preempt kp s e.machine)
      ⟨s, [s]⟩

structure Visit where
  entry : MachineState
  exit : MachineState
  nonce : BitVec 64

structure Visits (fetch) (kp : BitVec 64) (visits : List Visit) : Prop where
  entries : ∀ v ∈ visits, ∃ layout preempt skb, Context layout preempt v.entry kp skb v.nonce
  exits : ∀ v ∈ visits, FirstExit fetch v.entry v.exit
  retained : WindowRetained kp visits

def acceptedNonces (visits : List Visit) : List (BitVec 64) :=
  (visits.filter (fun v => accepted v.exit)).map (·.nonce)

def NoCounterAcceptedTwice : Prop :=
  ∀ fetch kp visits, Reading fetch → Visits fetch kp visits → (acceptedNonces visits).Nodup
```

`FirstExit fetch s t` says `t` is the first state at an exit address on an
actual instruction history from `s` (the landed `ActualHistory`).
`WindowRetained` says that from each visit's exit to the next visit's entry
the 1032 bytes at `kp + 136` are equal; nothing else about the machine is
constrained between visits. `Reading` and `Context` are the premises
(section 5). `Kept.unlockArgument` is new in revision 2: the instruction
before `setb` loads the unlock's argument, and the conclusion now says so, so
that a later result about the unlock can be joined on.


**The refinement** (`Refines`: the binary-level statement against the mirror).
If the window bytes represent a replay state `c` under the landed
`Layouts.ReplayFields` (counter at `kp+136`, 128 little-endian words from
`kp+144`), and the mirror's `Leanux.WG.counterValidate id nonce` on a world
whose keypair `id` holds `c` returns `result` and leaves `world'`, then the
machine reaches as its first exit the address `exitPC c nonce` (the image's
three tests in order, which are the mirror's decisions `ctrRejectCounter`,
`ctrRejectTheirs`, `ctrTooOld` in order); `accepted` at that exit equals
`result`; the window bytes represent the replay state of `world'`; and `Kept`
holds.

```lean
def Refines : Prop :=
  ∀ fetch layout preempt s kp skb nonce world world' ambient ambient' id c result,
    Reading fetch → Context layout preempt s kp skb nonce →
    Layouts.ReplayFields s.data.dmem (kp + .ofNat 64 Layouts.keypair_receiving_counter) c →
    windowOf world id = some c →
    ((WG.counterValidate id nonce.toNat).run world).run ambient = .ok ((result, world'), ambient') →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc = exitPC c nonce.toNat ∧
        (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        accepted e.machine = result ∧
        (∃ c', windowOf world' id = some c' ∧
          Layouts.ReplayFields e.machine.data.dmem (kp + .ofNat 64 Layouts.keypair_receiving_counter) c') ∧
        Kept layout preempt kp s e.machine)
      ⟨s, [s]⟩
```

The mirror's recorded decisions (`ambient'`) are not described beyond the
exit.

**The witness and the exclusion.**

```lean
def ReplayWitness : Prop :=
  ∃ fetch kp first second,
    Reading fetch ∧ Visits fetch kp [first, second] ∧ first.nonce = second.nonce ∧
    accepted first.exit = true ∧ accepted second.exit = false

def AdvanceAccepted : Prop :=
  ∀ fetch layout preempt s t kp skb nonce high,
    Reading fetch → Context layout preempt s kp skb nonce → FirstExit fetch s t →
    s.data.dmem.loadInt (kp + .ofNat 64 Layouts.keypair_receiving_counter) 8 = some (high.toNat : Int) →
    high.toNat ≤ 0xffffffffffffe03e → nonce.toNat < 0xffffffffffffe03e →
    high.toNat / 64 < (nonce.toNat + 1) / 64 →
    accepted t = true
```

`ReplayWitness` says the premises (`Reading`, `Context`, `Visits`) are
satisfiable together, by the same packet counter presented twice to one
retained window, accepted then refused. Its realism: a constructed state of
the kind executed in section 8, with the image's own callback code; not a
captured kernel state. It is false until the patch exists. `AdvanceAccepted`
says a counter below the limit whose bitmap word lies beyond the stored
counter's word is accepted; it is what excludes "refuses everything" when
`Refines` is not claimed, and is redundant when it is. (`ReplayRefused`, a
corollary of uniqueness, is also stated in the file.)

### The two headline forms

```lean
/-- (i) RECOMMENDED: the reviewer's form. -/
def HeadlineRefinement : Prop :=
  ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness

/-- (ii) ALTERNATIVE: machine states only. -/
def HeadlineMachine : Prop :=
  ExitsCleanly ∧ NoCounterAcceptedTwice ∧ ReplayWitness ∧ AdvanceAccepted
```

| | (i) with `Refines` | (ii) machine states only |
| --- | --- | --- |
| Says | What the code computes on every premise-meeting state, in the mirror's terms; that it exits cleanly; that no counter is accepted twice; that all of this is inhabited | That it exits cleanly; never accepts a counter twice; accepts a counter that advances to a later bitmap word; inhabited |
| Claimed, new printed lines | 95 | 76 |
| Claimed, inherited | As (ii), plus `Layouts.ReplayFields` (5 lines, landed) and the mirror's `counterValidate` (27 lines of `Leanux/WG/RxData.lean`, the project's deliverable, checked differentially against the kernel) with the mirror's monad under it | `Eventually`, `historyStep`, `ActualHistory`, `EqualOutside`, `KcovState` and its closure, `List.Nodup` |
| A wrong implementation that would still satisfy it | None that differs in exit, acceptance byte or window bytes on a premise-meeting state: those are fixed to the mirror's function. What is left free: the caller-saved registers and flags, the contents of the spill slots and of the coverage buffer, and anything outside the premises. A defect shared by the mirror and the code would pass; the differential check is what stands against that | Code that refuses every counter not strictly beyond the stored counter's word (no tolerance of reordering at all); any fixed permutation of the bits inside each word (section 8 has one); a clear loop that clears fewer words where the advancing word itself is still cleared; a tighter too-old test. `AdvanceAccepted` excludes only "refuses everything" |
| Serves the 2026-10-14 objective | Both halves: adequacy of the mirror for this function (`Refines`) and transport of a landed result | Transport only; adequacy is proved on the way but not claimed |
| Needs the proof tree | Clause 3 only. `ExitsCleanly`, `Refines` and `ReplayWitness` mention and need only the mirror and stay in the binary package under the existing rule | Clause `NoCounterAcceptedTwice` only |
| Proof cost | The same: `Refines` is proved either way | The same, plus `AdvanceAccepted` (small; it follows from `Refines`) |
| What the register would call it | The replay window of this build refines the mirror's; anti-replay uniqueness transported | Uniqueness of accepted counters in a single-CPU, instrumented build |

**Recommendation: (i).** Revision 1 proposed (ii) without its last two
conjuncts, on the ground that it kept the claimed text small. That was the
wrong economy: the claimed part is surface because it can be weaker than it
looks, and (ii) *is* weaker than the words "replay window" suggest, at no
saving in proof. The extra text of (i) is `exitPC` (five lines, to be read
against the three tests in the disassembly), `windowOf`, `ReplayFields` and
the mirror function, which is what the project exists to make trustworthy.
`Refines` has one soft spot: it is conditional on the mirror's run
succeeding. That it always succeeds on a 128-word bitmap is the landed
`mirror_step`, and `ReplayWitness` shows the conjunction inhabited. The choice
is the owner's.

The optional floor clause `AcceptedWithinWindow` (an accepted counter is at
most 8128 behind every counter accepted before it) can be added to either.

## 4. The landed theorems used, and the gap

**Which landed theorems are used, and how.** Two, both in the proof tree and
both current in [the register](proofs.md) (`ReplayWindow` S2 and R1):

- `Leanux.Proofs.WG.CounterWindow.mirror_step` (the S2 refinement):
  `counterValidate` on a world holding `c` with a 128-word bitmap always
  succeeds, returns `(step c nonce).1` and leaves `(step c nonce).2`. It
  supplies the accepted mirror run that `Refines` asks for and identifies it
  with the pure window `step`.
- `Leanux.Proofs.WG.AntiReplay.pure_uniqueness` (which is
  `CounterWindow.accepted_nodup`): for any `c` with a 128-word bitmap and any
  list of counters, the counters `step` accepts in sequence are distinct.

The join is one statement, checked to elaborate against both (scratch file,
not committed, because nothing outside the proof tree may import it):

```lean
def AcceptsAsPureWindow : Prop :=
  ∀ fetch kp visits c, Reading fetch → Visits fetch kp visits →
    (∀ first, visits.head? = some first →
      Layouts.ReplayFields first.entry.data.dmem (kp + .ofNat 64 Layouts.keypair_receiving_counter) c) →
    (acceptedNonces visits).map (·.toNat) =
      Leanux.Proofs.WG.CounterWindow.accepted c (visits.map (·.nonce.toNat))
```

`Refines` and `mirror_step` give `AcceptsAsPureWindow` by induction on the
visits (every mapped window represents exactly one `c`; a world holding it is
constructed); `pure_uniqueness` then gives `NoCounterAcceptedTwice`. The
floor clause needs more than one landed lemma (revision 1 was wrong to say it
follows the same way): `step_accepted_bounds` bounds the *stored* counter at
an acceptance, and the clause is about pairs of accepted counters, so it also
needs the stored counter's monotonicity (`step_counter_mono`) and that an
accepted counter is below it (`accepted_remembered`), all in
`CounterWindow`. The packet's `windowOf` is the proof tree's `counterAt` by
`rfl`. The scratch check compiled `CounterWindow`'s `Model`, `Refinement` and
`MirrorCalls` against the same mirror build and applied `mirror_step` and
`accepted_nodup` at these types.

Not used: `AntiReplay.runner_uniqueness` and `runner_floor`, the results over
whole accepted runner executions with keypair-slot reuse. Campaign 3's T4
([report](2026-10-18-proof-campaign-3.md#t4--handshake-replay-resistance)) is
about handshake replay and is conditional; it has no bearing here.

**The gap between this and "a replayed packet is dropped by this receive
path".** Nine things would still have to be shown; none is in any statement
here. (The list is the reviewer's, which is fuller than revision 1's five;
the disassembly facts in items 1 and 2 are the reviewer's reading, which I
checked for the instructions named.)

1. *After the range.* `__local_bh_enable_ip` and the comparison callback keep
   `%bpl`; the `jne` at `…d402` goes to `…d823`; that path drops the
   references and frees the packet without delivering it. Both rejection
   exits reach the same path without testing `%bpl` (`…d80d` falls into
   `…d823`; `…d9c3` jumps to `…d828`).
2. *Before the range.* `%r13` is the keypair the packet was decrypted under,
   and the quadword at `skb+0x28` is the counter used as the AEAD nonce,
   unchanged since decryption (`mov 0x30(%rbx),%r13` at `…d28f`; the state
   test at `…d298`; the entry cut is reached only by falling through from
   `…d2a1`).
3. *The premises of `Context` hold there*: the frame, the keypair as an
   object apart from the stack, the coverage state. Argued, not derived.
4. *Every reception that leads to delivery passes through the range*, and the
   list of visits is all executions on that window. One caller in the C; the
   second half is folded into `WindowRetained`.
5. *No other code writes a live keypair's window*, and address reuse after a
   free is a different key. `counter_validate` is the only writer in the
   driver's source.
6. *One CPU, no interrupt between instructions, fixed text*: the model.
7. *Kraken's semantics* for 69 instructions and the new one.
8. *That a replayed packet has the same counter under the same key*: the
   protocol and the AEAD.
9. *This build*: one CPU, coverage-instrumented. Nothing carries to an SMP
   build, where the lock and `lock bts` are real.

## 5. Premises

The entry premises as revised (the last field is the repair of H1):

```lean
structure Context (layout : KcovLayout) (preempt : BitVec 32) (s : MachineState)
    (kp skb nonce : BitVec 64) : Prop where
  pc : s.pc = Range.entry
  keypair : s.data.regs.r13.toBitVec = kp
  packet : s.data.regs.rbx.toBitVec = skb
  nonce : s.data.dmem.loadInt (skb + 0x28) 8 = some (nonce.toNat : Int)
  window : ∀ a, windowBytes kp a → (s.data.dmem.get? a).isSome = true
  aligned : s.data.regs.rsp.toNat % 8 = 0
  stack : ∀ a, stackBytes s.data.regs.rsp.toBitVec a → (s.data.dmem.get? a).isSome = true
  coverage : KcovState layout preempt s.data.dmem
  stackWindow : ∀ a, stackBytes s.data.regs.rsp.toBitVec a → ¬windowBytes kp a
  stackPreempt : ∀ a, stackBytes s.data.regs.rsp.toBitVec a → ¬InRange preemptCountAddress 4 a
  windowPreempt : ∀ a, windowBytes kp a → ¬InRange preemptCountAddress 4 a
  coverageApart : ∀ a, coverageBytes layout a → ¬Footprint s.data.regs.rsp.toBitVec kp a
  -- new in revision 2 (review finding H1):
  coverageMetadata : ∀ a, (layout.mode = 2 ∨ layout.mode = 3) → KcovStorageBytes layout a →
    ¬KcovMetadataBytes layout a
```

"Weight" marks the ones a reader should spend time on.

| # | Premise | Says | Why needed | Status |
| --- | --- | --- | --- | --- |
| P1 **weight** | `Reading.range` (`RangeDecoderAgreement`) | The decoder returns the 69 committed range terms and the 10 terms of the two comparison-callback entries | The theorem is about these terms | Tested, not proved: `gen.py --check` compares objdump's bytes with the ELF, every branch encoding with its target, and checks that no alternatives entry touches the range or the callbacks, `.smp_locks` is empty and the image has no jump-table, retpoline, return-thunk or paravirt patch sections. Trusted: objdump's text, Kraken's parser. That the running kernel executes these bytes is assumed |
| P2 | `Reading.services` (landed `ServiceDecoderAgreement`) | The same for the PC callback and the body `write_comp_data` shared by the comparison callbacks | The 13 calls execute that code | Landed premise, same status as P1 |
| P3 **weight** | `Reading.bts` (`Placeholder.BtsAt`) | The instruction at `…d3dd` executes as section 1 specifies | Kraken has no `bts` | **Placeholder.** Becomes a lemma once a tenth patch exists; until then an assumption about one instruction, tested against the host processor (section 8). **Unsatisfiable today**: no instruction of the pinned Kraken behaves so, hence every statement is vacuous until the patch (section 0) |
| P4 **weight** | Kraken at `43df9468` with nine patches | The meaning of the other 69 + callback instructions; sequential, no interrupt, no other CPU | Semantic base | Landed assumption; tested by the package's suites, not proved |
| P5 **weight** | `Context.keypair`, `.packet`, `.nonce` | At the entry cut `%r13` is the keypair's address, `%rbx` the packet's, and the packet counter is the quadword at `skb+0x28` | The inlining context: the range starts mid-function | Assumed, argued from the disassembly (gap item 2). Constructed states only |
| P6 **weight** | `Context.window` | The 1032 bytes at `kp+136` are mapped. Nothing about their contents | The code reads and writes them | Assumed; satisfiable (constructed). The offsets are the package's DWARF-generated `Layouts` |
| P7 **weight** | `Context.stackWindow`, `.stackPreempt`, `.windowPreempt`, `.coverageApart` | Exactly these pairs, no others: stack slots from window; stack slots from preempt count; window from preempt count; coverage metadata and (when recording) the coverage buffer from the footprint (stack slots, window, preempt count) | Otherwise a spill or a coverage record overwrites the window | Assumed; satisfiable (constructed). True in a kernel where the keypair is a slab object, the stack is the softirq stack and the buffer is a vmalloc area, but that is an argument, not a proof. Revision 1 called these "pairwise disjoint", which the Lean was not |
| P7b **weight** | `Context.coverageMetadata` (**new in revision 2**) | When recording, the coverage buffer does not overlap the coverage metadata (the current-task word and the four task fields) | Without it the statements are false: a record written over the task's `kcov_area` field sends later records anywhere, the window included (review H1; reproduced, section 8) | Assumed; the landed entries carry the same premise. No running kernel has its coverage buffer over its own task structure |
| P8 | `Context.aligned`, `.stack` | `%rsp` is 8-aligned; `[rsp-8,rsp)` and `[rsp+0x10,rsp+0x20)` are mapped | Calls and two spills | Assumed; satisfiable. Not derived from the function's prologue |
| P9 **weight** | `Context.coverage` (landed `KcovState`) | The current task's KCOV fields and the preempt count are readable; in a recording mode the buffer is mapped and its count is within capacity | The 13 callbacks read them; this is the instrumented oracle image | Assumed; satisfiable (constructed, three modes). No assumption on the mode or on the preempt count's value. That the buffer's record count is within capacity is an assumption about another party: in a running kernel that word is in memory shared with a user process (inherited from the landed results) |
| P10 **weight** | `Visits.retained` (`WindowRetained`) | Between visits the window bytes are unchanged | The property is about one window's history | Assumed. **A premise about the rest of the kernel**: keypair lifetime, the completeness of the list of visits and the absence of other writers all sit here (gap items 4 and 5) |
| P11 | `Visits.exits` (`FirstExit`) | Each visit's exit state is the first exit on an actual history from its entry | Names the state the observation is read from | Definitional; non-empty by `ExitsCleanly` |

Not premises, because the proof would discharge them: the callbacks' behaviour
(the landed `Callback.pc_contract` proves the PC callback from the image; the
two 8-byte comparison callbacks are five instructions each in front of the
body the landed package already proves for the 1- and 4-byte ones, and their
contracts are part of the work); the memory representation; the mirror.

## 6. What is not claimed

- **Nothing about concurrency.** The model executes one instruction after
  another with no interrupt, preemption or second CPU. In this image that is
  less of a fiction than usual (one CPU; the code runs in softirq context with
  bottom halves disabled), but a hard interrupt between two instructions is
  simply absent from the model, and the claim that no interrupt handler writes
  these bytes is not made.
- **Nothing about the lock.** The kernel source takes a spinlock around this
  code; this binary contains none. The result says nothing about an SMP build,
  where the lock is real and the `bts` is `lock bts`: different bytes, and a
  property that depends on mutual exclusion this result never mentions.
- **Not the kernel anyone runs.** The image is the KCOV-instrumented oracle
  build: 13 of the 70 instructions are coverage calls.
- **Not that replayed packets are dropped.** Section 4's gap, all nine items.
- **Not the cryptographic meaning of a counter.** Nothing says a counter is
  unique per packet or authenticated.
- **Under headline form (ii), not acceptance in general.**
  `NoCounterAcceptedTwice` is satisfied by code that refuses everything;
  `AdvanceAccepted` excludes only that. Which counters are accepted is said by
  `Refines`, which form (i) claims and form (ii) does not (section 3).
- **Under form (i), not more than the mirror says.** `Refines` ties the code
  to the mirror's function; a defect shared by both would pass. The mirror's
  recorded decisions are not described beyond the exit taken.
- **Not a reachable-state invariant.** The window may hold any bytes at the
  first visit. From unreachable contents (a set bit above the stored counter
  in its own word) a never-seen counter can be refused; that is the C's
  behaviour and the mirror's.
- **No permission (paging) conclusion** of the kind some landed headlines
  carry, and no history conclusion beyond first-exit.
- **Not `bts` in general**: one encoding, bit offsets 0..63.
- **Not that the entry premises hold in the kernel**, or hold together with
  those of any other landed result.

## 7. Trust surface

By the owner's definition: what could be wrong while every proof checks, in
two kinds. Measured as `scripts/binary-proof-gate` prints (`#print` at width
110, by `binary/packets/c2/surface`); the landed file is 4,713 lines, 755 of
them `TrustBase.lean`.

**Kind 1, assumed** (may be false or unsatisfiable):

| Content | Lines | Proposed budget |
| --- | ---: | ---: |
| Premises, new: `Reading`, `RangeDecoderAgreement`, `Context` (with revision 2's `coverageMetadata`) and its four footprint definitions, `Visits`, `Visit`, `WindowRetained`, `FirstExit`, `exits` | 122 printed (115 before the H1 premise) | 140 |
| The placeholder: `BtsAt`, `BtsDefined`, `BtsSuccessor`, `btsResult`; present only until Kraken has `bts` | 51 printed | 0 at landing |
| The tenth patch in Kraken: the semantics case (about 12 lines), the parser case (about 9), the `Operation` constructor and two printer cases (3). Revision 1 counted the semantics only | about 25 | 40 |
| Reading of the image: `C2Image.lean`, 70 + 10 literal instructions; the landed gate does not print image terms | 107 generated | not budgeted; regenerated and compared by `gen.py --check` |
| Inherited, landed: `ServiceDecoderAgreement` and the callback terms behind it; `KcovState` and its closure; the fixed addresses; `InRange`; `ActualHistory` and its successor relation; and the label instance `Image.linkedLabels` with `canonicalAddress`, through which every `L_…` branch target gets its address (30 lines; omitted in revision 1) | about 115 source lines, 54 of them in `TrustBase.lean` (the reviewer did not recount these, nor have I beyond adding the label instance) | 0 new |

**Kind 2, claimed** (may be weaker than it looks, or vacuous), for each
headline form of section 3:

| Content | (i) with `Refines` | (ii) machine only |
| --- | ---: | ---: |
| New printed lines: the headline, `ExitsCleanly`, `NoCounterAcceptedTwice`, `ReplayWitness`, `Kept`, `accepted`, `acceptedNonces`; plus for (i) `Refines`, `exitPC`, `windowOf`; for (ii) `AdvanceAccepted` (`exits`, `Footprint` are counted under kind 1) | 95 | 76 |
| Inherited | As (ii), plus `Layouts.ReplayFields` (5 lines) and the mirror's `counterValidate` (27 lines) with its monad | `Eventually`, `historyStep`, `instructionStep`, `EqualOutside`, `KcovState` and its closure, `List.Nodup`: about 80 source lines |
| Proposed budget, new printed | 110 | 90 |

Not surface: proofs, the join `AcceptsAsPureWindow`, the proof tree's
definitions, the callback contracts; and whichever of `Refines` /
`AdvanceAccepted` the chosen form leaves out. The optional floor clause and
`ReplayRefused` print 15 lines.

Structures print twice in that form (fields, then the constructor), so
`Context`, `Visits` and `Kept` count double. Beneath both kinds lies the
semantic base itself (Kraken's instruction semantics at the pin, Lean's
core), which no line count here includes.

**Evidence against vacuity carried by the result** (kernel-checked when
proved): `ReplayWitness`, a conjunct of both forms; realism and its present
falsity as in section 3. Under form (i) the definitions the claim mentions
are pinned as follows other than by reading:

| Part | Pinned by |
| --- | --- |
| Counter at `kp+136`, bitmap words at `kp+144+8j` (`ReplayFields`) | Functional (`ReplayFields.functional`, landed) and total on mapped bytes, so it cannot be weak by admitting several values or none. Executed: counter and all 128 words compared with the mirror after every run; two wrong layouts rejected. Offsets generated from DWARF (`binary/generate.py --check`, rerun: `Layouts.lean` checked) |
| `exitPC` | A consumer: `accepted` at the exit. Read against the three tests in the disassembly by the reviewer and by me. Executed: three wrong variants rejected |
| `windowOf` | Equal to the proof tree's `counterAt` by `rfl` (scratch check) |

## 8. What executing the statements showed

All of it with the saved s5 ELF's bytes. The range terms, the two callback
entries and the landed terms of the PC callback and the comparison body were
run with Kraken's interpreter; the `bts` by the placeholder. So: **69 of the
70 range instructions and the real callback code were executed under the
landed semantics; the `bts` could not be, and was executed by the proposal
for it.** The mirror side is the mirror's own `Leanux.WG.counterValidate`,
run on a constructed world.

**Single visits** (`C2Test.lean`, executable forms of `Refines` and `Kept`):
27 pairs of stored counter and packet counter (fresh window; in window and
unseen; in window and seen; exactly at the old edge and one past it; far ahead
with one, 127, 128 and more words cleared; at and one either side of both
limits), each with three initial bitmaps (a pattern, all clear, all set), six
callback settings (the image's callbacks with coverage off, recording
comparisons into an empty and a part-filled buffer, recording PCs with room
and nearly full; and callbacks replaced by a return that overwrites every
caller-saved register), two seeds for the undefined flags and two preempt
counts. **972 runs, 564 accepting, no failure**: every run took the exit
`exitPC` names, `accepted` equalled the mirror's result, and the counter and
all 128 words read back from memory equalled the mirror's final replay state.
The longest run executes 7,697 instructions (128 words cleared).

**The frame** is compared on every mapped byte outside the footprint (and
outside the coverage buffer when recording), not on canaries. Revision 2 adds
to this check the coverage metadata as `KcovMetadata` reads it and `%esi =
0x200` at the last exit; the numbers are unchanged.

**Wrong variants, each rejected** (`C2Test.lean`):

| Wrong variant | Runs failing, of 216 |
| --- | ---: |
| Statement: stored-counter limit one lower | 16 |
| Statement: packet-counter limit strict | 8 |
| Statement: the two rejection exits swapped | 56 |
| Statement: `%bpl = 1` read as acceptance | 160 |
| Statement: bottom halves re-enabled at the exit | 216 |
| Representation: bitmap word order reversed | 112 |
| Representation: bitmap one word later | 112 |
| Placeholder: CF is the new bit | 108 |
| Placeholder: the quadword is not written back | 108 |
| Placeholder: the next quadword | 112 |
| Placeholder: the next bit | 108 |

**Sequences** (`C2Sequence.lean`: only the window bytes carried between
visits; registers, the rest of memory, coverage mode and preempt count rebuilt
each time; compared with the mirror called in sequence, and checked for
uniqueness and the floor):
six sequences, 465 visits, among them the landed boundary witness `[8129, 1, 0,
1]` (accepted: 8129 and 1, as the landed theorem says), a start from arbitrary
window bytes, and counters at the limit. In all six the accepted counters are
distinct, within the floor, and identical to the mirror's. The same counter
twice on a zeroed window is accepted then refused (`ReplayWitness`'s shape);
four advancing counters over an all-ones bitmap are accepted
(`AdvanceAccepted`'s shape). Wrong variants:

| Wrong variant | Outcome over the six sequences |
| --- | --- |
| Placeholder does not write the quadword back | Caught on all six: a counter is accepted twice |
| Window zeroed between two visits (the premise `WindowRetained` broken) | Caught on two: a counter is accepted twice. The premise is needed |
| Placeholder reports the new bit (so everything is refused) | Uniqueness and the floor hold vacuously; caught on all six only by the comparison with the mirror. This is what `AdvanceAccepted` is for |
| Placeholder consistently uses the neighbouring bit | **Not caught by any sequence check**, and rightly: it rotates each word's bits, so every sequence of acceptances is unchanged. The machine-level headline does not depend on which bit of a word is used. Only the byte-level comparison with the mirror rejects it (108 of 216 single visits) |

The last row is the concrete form of the choice in section 3: form (ii) is
true of that variant too, and what fixes the bit is `Refines`.

**The search revision 1 lacked: states that meet the premises and break a
conclusion** (`C2Adversarial.lean`). Revision 1 built every state from one
family of far-apart, aligned addresses with generous mappings and never
checked a state against `Context`; that is how H1 was missed. Now:

- `contextHolds` decides every field of `Context` numerically on the
  constructed state (loads, mappings, alignment, each disjointness over the
  actual byte sets, modulo 2^64), for revision 1's `Context` and for the
  revised one. A state is run only if it passes.
- States map only the bytes `Context` requires, and the regions are written
  in three different orders, so that where two overlap either may win.
- *Placements.* Five movable objects (stack pointer, keypair, packet,
  task structure, coverage area), each with its interesting parts (the return
  slot and the spill slots; the whole window, the counter word, bitmap words
  0, 1 and 127; the packet-counter slot; each of the four task fields; the
  buffer's header, words 1 and 2, its last word and the whole buffer). Each
  part is placed immediately before and after, one byte into from either
  side, and exactly over the start and the end of every region belonging to
  another object, and of three fixed targets: a return address inside the
  range (the reviewer's device), the top of the address space (regions
  wrapping past 2^64), and address zero. Then sampled pairs of such
  placements of different objects.
- *Settings per placement.* Recording PCs with one record and with a nearly
  full buffer, recording comparisons, coverage off, three write orders, three
  (stored counter, packet counter) pairs; capacity 8, so buffers fill within
  a visit.
- *Checked on every passing state*: no fault; the exit `exitPC` names; the
  acceptance byte and all 1032 window bytes against the mirror; the four
  registers; `%esi`; the preempt count; **the coverage metadata** (the half of
  `Kept.coverage` that revision 1's `Test.kept` did not check, now checked
  there too); the buffer count; the frame over every mapped byte.
- *And the replay shape*: an accepting visit with coverage off, then a visit
  in the adversarial layout with the same counter on the retained window,
  which must refuse.

Results:

| | Single placements | Pairs of placements |
| --- | ---: | ---: |
| Layouts | 775 | 921 |
| States built and checked against `Context` | 6,200 | 3,684 |
| Meeting revision 1's `Context` | 2,595 | 1,084 |
| Meeting the revised `Context` | 2,377 | 896 |
| **Conclusion broken, state meets only revision 1's `Context`** | **100** | **87** |
| **Conclusion broken, state meets the revised `Context`** | **0** | **0** |
| Replay accepted (same counter accepted on both visits), revision 1's premises | 13 | 1 |
| Replay accepted, revised premises | 0 | 0 |

Under revision 1's premises the breaks are of three kinds: the coverage
metadata changed at the exit; a counter accepted twice; and outright faults
(a callback following an overwritten `kcov_area` field into unmapped memory),
so `ExitsCleanly` was false there in its "never faults" part as well, which
the reviewer's example did not show.

So the search rediscovers the missing separation on its own under revision
1's premises, and finds nothing under the revised ones. **What that is worth:**
it covers single and paired boundary placements of the regions the statement
names, at one capacity and a handful of counter values. It does not cover
triple coincidences, large capacities, or anything about the instruction
semantics. The proof is what would settle it; by my reading and the
reviewer's, buffer-over-metadata was the only unseparated pair (the range
writes only its footprint, the callbacks only the buffer, and every other
pair of written and read regions is separated by a field of `Context`).

**The reviewer's counterexample, kept as a test.** In this builder: task `T`,
recording PCs, capacity 8, area `T+0x6d8` with one record (so buffer word 2 is
the task's `kcov_area` field), keypair placed so that bitmap word 1 is at
`0xffffffff8139d2dc`. It passes revision 1's `Context`, fails the revised
one, and on the old premises both visits accept counter 63. The test fails if
any of the three stops being so.

**The proposed `bts` semantics against the host processor**
(`bts_host.c`, the same four bytes, AMD Ryzen 9 7950X3D): 1,536 runs over six
word values, all 64 offsets and four incoming flag settings; no disagreement
on CF, the written word or its neighbours. This processor changed none of PF,
AF, ZF, SF, OF. For offsets outside 0..63, which the proposal declines, the
processor addressed the quadword at `8 * (offset asr 6)` as the manuals say.
One processor is a test, not ISA fidelity.

**Limits of this evidence.** The tests run the packet's own interpreter of
Kraken's effect trees (`Test.effects`), not the package's `instructionStep`;
`Context`, `Kept`, `ReplayFields` and `WindowRetained` are re-rendered as
code, by me. The eleven single-visit variants perturb conclusions, the
representation and the placeholder, not premises; the premise side is covered
only by the search above and by two broken-premise cases (the kept
counterexample; the zeroed window). The undefined flags are driven by two
seeds, and the host run changed no undefined flag, so that freedom was never
exercised by hardware. The reviewer reran everything of revision 1 and got
identical numbers, and separately ran 2,430 minimal-mapping states without a
fault.

**Not run:** nothing in QEMU, no captured kernel state, no guest. The
package's own suites were not rerun. The package was not rebuilt: the
statement files were compiled against the build outputs in
`.worktrees/binary-reassessment` (same `binary/` and mirror sources as this
branch), read-only.


## 9. Where the joining proof lives

**Which form needs it.** Under either headline form only the transported
clause, `NoCounterAcceptedTwice` (and the floor, if taken), needs the landed
theorems. `ExitsCleanly`, `Refines` and `ReplayWitness` mention and need only
the mirror: they stay in the binary package under the existing rule (B1),
with no import of the proof tree and no rule change. So with form (i) the
adequacy claim lands whatever is decided here, and this decision gates one
clause.

| Option | What changes | Cost | Loses |
| --- | --- | --- | --- |
| A. A bridge target | A third, non-default lake library (for example `binary/bridge/`, root `C2Bridge`) that alone may import both `BinaryProofs` and `Leanux.Proofs.WG.CounterWindow.*`; it holds `AcceptsAsPureWindow`, `NoCounterAcceptedTwice` and the headline conjunction, about 100 lines | **It weakens a gate check**: `scripts/proof-gate` fails if anything outside the proof tree imports it, and this exempts one path. Under option A the track's headline theorem itself lives in the bridge, so unless a named gate builds the bridge and checks it, the headline is in no gate | The clean separation of the two gates |
| B. Copy into the binary package | No rule changes. `step`, `accepted` and the uniqueness proof (about 230 lines of `CounterWindow/Model.lean`) are copied with origin comments, as B1 did for the allowed-IPs model; the mirror link is needed in the package anyway for `Refines` | About 250 duplicated lines to keep in step by hand | The claim "the landed theorem, transported": it becomes "a copy of the landed proof, re-checked". Nothing in the headline changes |
| C. The landed theorem as a premise of the headline | No import, no copy | Assumed surface that no kernel check connects to the landed result | Most of the point. Should not be taken |
| D. The bridge inside the proof tree | `Leanux/Proofs/` imports the binary package | The proof tree's build and gate come to depend on Kraken and a 1,100-job package | The proof tree's independence from the semantics pin |

**Conditions for option A** (the reviewer's, which I adopt as part of the
proposal):

1. the exemption is one exact path, written into AGENTS.md by the owner;
2. the import is limited to the four `CounterWindow` modules (644 lines,
   importing only the mirror; R1's `pure_uniqueness` is a one-line restatement
   of `accepted_nodup` there);
3. a named gate builds the bridge and applies the axiom check and the
   forbidden-token scan to it;
4. the register records the bridge's result as lagging when those modules
   change.

With those, the weakening is one line of an import check and no check of
proofs is lost. Without condition 3 the option should not be taken.

The joining statement (`AcceptsAsPureWindow`, section 4) was checked to
elaborate against both sides in a scratch file that is not committed, because
a committed file importing the proof tree would trip the gate. The reviewer
did not reproduce that check; its text is in section 4 for anyone who wants
to.

## 10. Decisions for the owner

In the order they need taking.

1. **A tenth Kraken patch for `bts`, with section 1's semantics and tests.**
   Recommended: yes, in the partial form (offsets 0..63, ZF undefined, no
   locked form). Alternatives: the full offset addressing; or no patch, with
   `BtsAt` kept as a permanent premise about one instruction; or stop C2.
   What is signed now is the statement with `BtsAt` discharged by the patch;
   the final text and its diff are shown again before the proof is accepted.
2. **The headline's form** (section 3). Recommended: (i)
   `ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness`.
   Alternative: (ii) `ExitsCleanly ∧ NoCounterAcceptedTwice ∧ ReplayWitness ∧
   AdvanceAccepted`, with the register calling the result uniqueness of
   accepted counters in a single-CPU, instrumented build.
3. **The joining proof's home** (section 9; it gates the transported clause
   only). Recommended: option A under its four conditions, the named gate
   among them. Alternative: option B, no rule change, the clause described as
   a re-checked copy. Not C or D.
4. **The budget.** Recommended, for this result at landing with form (i): 140
   new printed lines assumed, 40 lines of Kraken patch (semantics, parser
   case, constructor), 110 claimed; the image terms regenerated and compared,
   not budgeted. With form (ii): 90 claimed. Alternative: a single figure, as
   the reassessment suggested (300).
5. **What the gate's expected file prints** (a proposal only; nothing was
   edited). Under the owner's definition it would print two sections per
   headline, assumed and claimed, and stop printing intermediate cut theorems
   and proof-internal relations. Alternative: leave it, and keep this
   packet's `surface` script as the measure for C2 alone.
6. **Where the range ends.** Recommended: at `setb`, as stated, with `%esi =
   0x200` now in the conclusion so that a result about the unlock can be
   joined on. Alternative: extend through `spin_unlock_bh` and the branch to
   the two successors `…d408` and `…d823`, using the landed
   `Callback.bh_contract`; about nine more instructions and three more call
   sites, a readiness premise on pending softirqs, and the preempt count
   restored in the conclusion. It closes gap item 1 up to the branch, not the
   drop.
7. **`KcovKind` gains `constCmp8`** in `TrustBase.lean` (three lines of a
   landed trust declaration), so that the fifth callback's contract can be
   stated like the others and proved. Recommended: yes. Alternative: a local
   plan definition in the new files.
8. **The optional floor clause.** Recommended: include. Alternative:
   uniqueness only.

## 11. Cost, order, differences from the reassessment, and what blocks an honest statement

**Cost.** Basis: trial T3, which took 50 worker-minutes to a checked theorem
at the `bts` with the callbacks assumed. That trial is unreviewed and
differently shaped, so the figures below cannot be checked, and the reviewer
is right that revision 1's total left items out. **Plan on the upper end; the
lower end is unlikely.**

| Piece | Worker-hours | Basis |
| --- | ---: | --- |
| Patch ten with tests, pin, `RegionOperation`; its review against both vendors' manual pages | 2–4 | Patch nine is 127 lines; neither I nor the reviewer could fetch AMD's page |
| The two 8-byte callback contracts | 1–3 | Five instructions each before a body already proved for two widths |
| Coverage state carried through 13 call sites and the loop, with every separation actually used | 4–8 | **The main uncertainty, and where H1 was found.** T3 avoided it with an abstract invariant; the landed exact contracts need the buffer's state carried through up to 256 calls |
| `ExitsCleanly` and `Refines` in first-exit form, the last three instructions | 2–4 | T3's proof, restated |
| The mirror link in the package | 1 | T3: ten minutes, 333 lines |
| Sequences, the join, the floor | 2–3 | An induction over visits |
| `ReplayWitness` (and `AdvanceAccepted` under form (ii)) | 2–3 | A closed two-visit execution; landed witnesses are the model |
| Option A's gate and rule work, if taken | 1–2 | A named gate for the bridge |
| Re-presentation of the final statement and its diff after the patch | 1 | Decision 1 |
| **Total** | **16–29** | Plan on 25 to 30 |

Elapsed: a day to a day and a half with three workers, then independent
review (3 to 5 agent hours) and repairs: three days. Owner: this document;
then the claimed and assumed text of section 7, 107 generated lines to skim,
the patch; the final diff; one run of the external `lake check` outside the
sandbox.

**Order.** (1) Decision 1, the patch: its semantics is part of what the
headline means. Work up to the `bts` does not wait for the patch itself.
(2) Decisions 2 and 4, which fix what is proved. (3) Decision 3: needed only
for the transported clause. (4) Proof: callbacks, single visit, sequences,
the join, the witness. (5) The final text and diff to the owner.
(6) Independent review. (7) External gate and landing.

**Differences from the reassessment.**

- It proposed stating the result against the proof tree's `step` in the binary
  package. That needs the import; `Refines` against the mirror's function
  needs none, and only the transported clause does.
- It counted eleven callback sites; there are thirteen in the range.
- It took the 8-byte callbacks as the place the result could fail. They are
  five-instruction entries into code the landed package already proves.
- It did not say that the build has no lock at all, which is the main limit
  on what the result means.
- T3 stopped at the `bts` with a function of its own; here the statement runs
  to `setb` against the mirror's function and is executed end to end.

**What blocks an honest statement today.**

- Until Kraken has `bts`, `Reading` is unsatisfiable: every statement is
  vacuously true and `ReplayWitness` is false (section 0).
- The entry premises are not derived from the caller, and no captured kernel
  state has been checked against them.
- "Sequential" is not a premise that can be discharged: it is the model.
- Revision 1 was false for want of one separation premise. The search of
  section 8 found no second one; only the proof can show there is none.

No Rule Zero discrepancy was found, by me or by the reviewer.

## 12. Dispositions of the review findings

Review: `docs/2026-11-10-review-statement-packet-c2.md` at `c9ee6100`.

| Finding | What it says | Disposition |
| --- | --- | --- |
| H1 | Both clauses of revision 1's headline, and `Refines`, are false as written: nothing separates the coverage buffer from the coverage metadata; a two-visit state accepts counter 63 twice | **Fixed.** Accepted in full: the statement was false. Reproduced (section 8). `Context` gains `coverageMetadata`, in the form of the landed `LookupEntry.coverageMetadata`. The counterexample is a test that passes the old `Context`, fails the new, and accepts twice on the old. The premise table's P7, which said more than the Lean did, now matches it |
| H1, the search asked for | Rerun a search for states that meet `Context` and break a conclusion | **Done** (`C2Adversarial.lean`, section 8): the premises are checked on every state; the search rediscovers H1 under the old premises and finds nothing under the new. Its limits are stated there |
| H2 | The proposed headline is the weaker half of the objective, holds of code that refuses everything, of bit permutations, of weaker clear loops and tighter tests; the vacuity statements were not conjuncts | **Owner decision, recommendation changed.** Both forms are stated in Lean and compared (section 3). I now recommend the reviewer's conjunction. The alternative carries `ReplayWitness` and `AdvanceAccepted` as conjuncts, and the name the reviewer asks the register to use |
| M1 | What is signed is not what would land; today every statement is vacuous and `ReplayWitness` false; the patch decision should come first | **Fixed.** Section 0 says so plainly and says what is signed now and after the patch; the `bts` proposal is section 1; the decisions and the order put the patch first; the final text and diff go back to the owner before the proof is accepted |
| M2 | The tests exercise the conclusions and never the premises; all states from one family; no state checked against `Context`; `Test.kept` omits the metadata half of `Kept.coverage`; the variants perturb no premise; two flag seeds only | **Fixed in part, the rest answered.** Fixed: the premise check, the adversarial and minimal-mapping states, the metadata half in `Test.kept` and in the search. Answered: the eleven single-visit variants still perturb conclusions, representation and placeholder only; the premise-side evidence is now the search and the kept counterexample (a premise removed, a conclusion broken). Not changed: undefined flags are still driven by two seeds, and the tests use the packet's own interpreter of Kraken's effects, not `instructionStep`; both remain limits of the evidence (section 8) |
| M3 | Option A weakens a gate check; under it the headline lives in a third target that no named gate builds; with `Refines` in the headline the adequacy claim needs no import; the scratch check is not committed | **Fixed** in section 9: the weakening is stated, the reviewer's four conditions are adopted, which form needs the import is stated. **Answered:** the scratch file stays uncommitted because a committed file importing the proof tree outside it would fail `scripts/proof-gate`; its text is in section 4 |
| M4 | The gap to "a replayed packet is dropped" has nine items, not five | **Fixed.** Section 4 carries the nine |
| M5 | The premises against the image and the caller: P7 short by one pair; `KcovState`'s count is in memory shared with a user process; `WindowRetained` is a premise about the rest of the kernel | **Fixed** in the premise table: P7/P7b, a note on P9, and P10 called a premise about the rest of the kernel |
| L1 | `Kept` does not say `%esi = 0x200` at `donePC`, so the result does not compose with one about the unlock | **Fixed.** `Kept.unlockArgument`; checked in every test run that ends there |
| L2 | Assumed lines omitted: the H1 premise, the patch's parser case and constructor, the label instance | **Fixed.** Section 7 counts them; the claimed side is given for both forms |
| L3 | The `bts` semantics: agrees with Intel's page; AMD's unverified; a declined offset removes histories from actual-history premises | **Fixed/answered.** Section 1 records what was and was not verified and carries the caution; AMD's page remains unverified by anyone and is an item for the patch's review |
| L4 | The cost leaves items out; plan on the upper end | **Fixed.** Section 11: items added, range 16 to 29, upper end advised |
| L5 | Two slips: the floor does not follow from `step_accepted_bounds` alone; P7 said "pairwise disjoint" | **Fixed.** Section 4 names the monotonicity lemmas too; P7 corrected |

## Reproduction

From the worktree root, with a built binary package (here or named by
`C2_BUILT_TREE`) and, for the first command, pyelftools and the saved ELF:

```sh
python3 -B binary/packets/c2/gen.py --check      # terms against the ELF
binary/packets/c2/check                          # compiles all six, runs the tests and the search: about 9 minutes
binary/packets/c2/surface                        # the line counts of section 7
cc -O1 -o .tmp/c2-packet/bts_host binary/packets/c2/bts_host.c && .tmp/c2-packet/bts_host
```
