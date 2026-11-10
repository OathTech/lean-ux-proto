# C2, the final statement: the receive replay window, for the owner's signature

2026-11-10, on `task/binary-c2` (local, not pushed). Phase A of the
commissioned result C2: the tenth Kraken patch and the final statement
text. **No proof of the headline exists and none was started.** This is the
text the 2026-11-10 decision says comes back to the owner, with its diff,
before any proof is accepted. Judgements here are mine [AGENT] unless
marked.

It follows [the statement packet, revision 2](2026-11-10-statement-packet-c2-replay-window.md)
(`cf8798e5`), [its review and follow-up](2026-11-10-review-statement-packet-c2.md)
and the last 2026-11-10 entry of [decisions.md](decisions.md). Read sections
1 to 5; the appendix is reference.

**What is asked:** a signature on section 1 (the headline and what it
mentions), knowing section 5. Three things to weigh first:

1. The claimed part prints at **111 lines, one over the proposed budget of
   110**; the sixteen lines of the witness extension (finding F1) are the
   cause. Section 1 has the counts.
2. Carrying the patch needed **one new proof case in each of two landed
   files** (`MemoryInvariant.lean`, `SystemInvariant.lean`), which is more
   than a rebuild. Appendix A4.
3. Every rerun number equals the placeholder runs'. Section 4.

## 1. The signed text

Verbatim from `binary/C2Statement.lean` at `8200bf7e`, namespace
`Binary.C2`, in reading order: the headline, then what it assumes, then
what it claims. The file holds three more declarations that the headline
does not mention (`AcceptedWithinWindow`, `ReplayRefused`,
`AdvanceAccepted`); they are not signed.

```lean
/-- THE HEADLINE. What the code computes (`Refines`), that it exits cleanly, the
transported property, and a witness that all of it is inhabited. (Rejected alternative:
a machine-states-only conjunction with `AdvanceAccepted` in place of `Refines`, which
holds of code that permutes the bits of a bitmap word.) -/
def HeadlineRefinement : Prop :=
  ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness
```

**Assumed** (premises: may be false or unsatisfiable; nothing checks them).
120 lines as the gate's printer prints them (`#print` at width 110; packet
revision 2: 122, the two lines of the `bts` field gone), against a proposed
budget of 140. Beside them, also assumed: the Kraken patch (section 3; 39
added lines in the semantics, the parser case and the constructor, 24 of
them code and the rest comment, against a budget of 40; two printer lines
beside), the 70 + 10 generated image terms of `binary/C2Image.lean` (103 lines, regenerated and
compared with the ELF, not budgeted), and the landed definitions these
mention (`ServiceDecoderAgreement`, `KcovState` and its closure, `InRange`,
`ActualHistory`, the label instance), unchanged.

```lean
/-- The ambient decoder agrees with the committed literal terms of the range (70
instructions, the `bts` among them) and of the two callback entries. -/
def RangeDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Range.fetch pc = some instruction → fetch pc = some instruction

/-- What is assumed of the code: two readings of the image.
`ServiceDecoderAgreement` is the landed one: it covers the PC callback and the body
shared by the comparison callbacks. -/
structure Reading (fetch : Int64 → Option Decoded) : Prop where
  range : RangeDecoderAgreement fetch
  services : ServiceDecoderAgreement fetch

/-- `struct noise_replay_counter` inside the keypair at `kp`: 1032 bytes at offset 136
(the counter, then 128 bitmap words; the spinlock has size zero in this build). -/
def windowBytes (kp : BitVec 64) : BitVec 64 → Prop :=
  InRange (kp + .ofNat 64 Layouts.keypair_receiving_counter) Layouts.replaySize

/-- Stack bytes the range writes: the return-address slot of its calls, and the two
spill slots `0x10(%rsp)` and `0x18(%rsp)`. -/
def stackBytes (sp : BitVec 64) (a : BitVec 64) : Prop :=
  InRange (sp - 8) 8 a ∨ InRange (sp + 0x10) 16 a

/-- Everything the range itself writes, the coverage buffer apart. -/
def Footprint (sp kp : BitVec 64) (a : BitVec 64) : Prop :=
  stackBytes sp a ∨ windowBytes kp a ∨ InRange preemptCountAddress 4 a

/-- Bytes the coverage callbacks read as metadata or, in a recording mode, write. -/
def coverageBytes (layout : KcovLayout) (a : BitVec 64) : Prop :=
  KcovMetadataBytes layout a ∨ ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout a)

/-- The machine state at the entry cut `0xffffffff8139d2a6`, without any reference to
the mirror. `r13` and `rbx` are the inlining context: the caller loaded the keypair
pointer and holds the packet. The window is only required to be mapped. -/
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
  /-- Revision 2 (review finding H1): the coverage buffer does not lie over the coverage
  metadata. The landed entries carry the same premise (`LookupEntry.coverageMetadata`).
  Without it a callback's record can overwrite the task's `kcov_area` field and later
  records land anywhere, the window included. -/
  coverageMetadata : ∀ a, (layout.mode = 2 ∨ layout.mode = 3) → KcovStorageBytes layout a →
    ¬KcovMetadataBytes layout a

def exits : List Int64 := [Range.donePC, Range.rejectWindowPC, Range.rejectLimitPC]

/-- `t` is the first state at an exit on an actual execution from `s`. -/
def FirstExit (fetch : Int64 → Option Decoded) (s t : MachineState) : Prop :=
  ∃ history, ActualHistory fetch s history ∧ history.getLast? = some t ∧
    t.pc ∈ exits ∧ ∀ u ∈ history.dropLast, u.pc ∉ exits

/-- One execution of the range: its entry state, its first exit state, and the packet
counter the entry state holds at `skb + 0x28`. -/
structure Visit where
  entry : MachineState
  exit : MachineState
  nonce : BitVec 64

/-- Between one visit's exit and the next visit's entry the 1032 window bytes are the
same. Anything else may have happened to the machine. -/
def WindowRetained (kp : BitVec 64) : List Visit → Prop
  | first :: second :: rest =>
    (∀ a, windowBytes kp a → first.exit.data.dmem.get? a = second.entry.data.dmem.get? a) ∧
      WindowRetained kp (second :: rest)
  | _ => True

/-- The visits of one keypair's window, in order. -/
structure Visits (fetch : Int64 → Option Decoded) (kp : BitVec 64) (visits : List Visit) : Prop where
  entries : ∀ v ∈ visits, ∃ layout preempt skb, Context layout preempt v.entry kp skb v.nonce
  exits : ∀ v ∈ visits, FirstExit fetch v.entry v.exit
  retained : WindowRetained kp visits
```

**Claimed** (conclusions: may be weaker than they look). 111 printed lines
(packet revision 2: 95; the extension of `ReplayWitness` adds 16), against a
proposed budget of 110. Inherited and unchanged: `Eventually`,
`historyStep`, `EqualOutside`, `KcovState`, `List.Nodup`,
`Layouts.ReplayFields`, and the mirror's `WG.counterValidate`.

```lean
/-- The observation: the range left by its last instruction with `%bpl = 0`. This is
the byte the branch at `0xffffffff8139d3ff` tests after the range; `%bpl = 1` there, and
either rejection exit, is a refusal. -/
def accepted (t : MachineState) : Bool :=
  t.pc == Range.donePC && t.data.regs.rbp.toNat % 256 == 0

/-- What holds at every exit whatever the outcome: bottom halves are still disabled
(the count is 0x200 higher), the coverage state is intact, the registers the caller
relies on are kept, and only the footprint and the coverage buffer were written. At
`donePC` the low half of `%rsi` is 0x200, the argument the unlock that follows passes
(revision 2, review finding L1: so a later result about the unlock can compose). -/
structure Kept (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s t : MachineState) : Prop where
  coverage : KcovState layout (preempt + 0x200) t.data.dmem
  rsp : t.data.regs.rsp = s.data.regs.rsp
  rbx : t.data.regs.rbx = s.data.regs.rbx
  r12 : t.data.regs.r12 = s.data.regs.r12
  r13 : t.data.regs.r13 = s.data.regs.r13
  unlockArgument : t.pc = Range.donePC → t.data.regs.rsi.toNat % 2 ^ 32 = 0x200
  frame : EqualOutside
    (fun a => Footprint s.data.regs.rsp.toBitVec kp a ∨
      ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout a))
    s.data.dmem t.data.dmem

/-- CLAUSE 1. From every entry state the code reaches an exit, never
faulting, and `Kept` holds at the first one. -/
def ExitsCleanly : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64),
    Reading fetch → Context layout preempt s kp skb nonce →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧
        Kept layout preempt kp s e.machine)
      ⟨s, [s]⟩

def acceptedNonces (visits : List Visit) : List (BitVec 64) :=
  (visits.filter (fun v => accepted v.exit)).map (·.nonce)

/-- CLAUSE 2. Over any sequence of executions of the range on one keypair
address between which the window bytes are not changed, starting from any mapped window
contents, no packet counter is accepted twice. -/
def NoCounterAcceptedTwice : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (visits : List Visit),
    Reading fetch → Visits fetch kp visits → (acceptedNonces visits).Nodup

/-- The keypair's replay state in the mirror's world. -/
def windowOf (world : WGWorld) (id : WG.KeypairId) : Option WG.ReplayCounter :=
  (world.dev.bind fun d => d.keypairs.get? id).map (·.receivingCounter)

/-- Which exit the image takes: its three rejection tests in their order, two of which
share an exit. The same tests, in the same order, are the mirror's decisions
`ctrRejectCounter`, `ctrRejectTheirs`, `ctrTooOld`. -/
def exitPC (c : WG.ReplayCounter) (nonce : Nat) : Int64 :=
  if c.counter ≥ WG.REJECT_AFTER_MESSAGES + 1 then Range.rejectWindowPC
  else if nonce ≥ WG.REJECT_AFTER_MESSAGES then Range.rejectLimitPC
  else if WG.COUNTER_WINDOW_SIZE + (nonce + 1) < c.counter then Range.rejectWindowPC
  else Range.donePC

/-- THE REFINEMENT. If the window bytes represent `c` (the landed `Layouts.ReplayFields`)
and the mirror's `counterValidate` on a world holding `c` returns `result` and leaves
`world'`, then the machine reaches, as its first exit, the exit the tests name; it
accepts exactly when the mirror returns `true`; and the window bytes then represent the
replay state of `world'`. -/
def Refines : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64)
    (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
    (c : WG.ReplayCounter) (result : Bool),
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

/-- The premises are satisfiable, by a replay: the same packet counter presented twice
to one retained window is accepted the first time and refused the second. And the
further premises of `Refines` are satisfiable with them (review finding F1): the first
visit's window bytes represent a replay state `c`, a world holds `c`, and the mirror's
`counterValidate` on that world succeeds, accepting, as the machine does. -/
def ReplayWitness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (first second : Visit),
    Reading fetch ∧ Visits fetch kp [first, second] ∧ first.nonce = second.nonce ∧
    accepted first.exit = true ∧ accepted second.exit = false ∧
    ∃ (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
      (c : WG.ReplayCounter),
      Layouts.ReplayFields first.entry.data.dmem
        (kp + .ofNat 64 Layouts.keypair_receiving_counter) c ∧
      windowOf world id = some c ∧
      ((WG.counterValidate id first.nonce.toNat).run world).run ambient =
        .ok ((true, world'), ambient')
```

How finding F1 is repaired, and why this way. `Refines` has three premises
beyond `Reading` and `Context`: a replay state the bytes represent, a world
holding it, a successful run of the mirror's function. `ReplayWitness` now
exhibits all three for its first visit, with the mirror accepting as the
machine does, so the headline alone shows the premises of `Refines` met
together. The alternative the reviewer offered, a totality conjunct ("every
state meeting `Context` has such a state, world and run"), is stronger and I
did not take it: the 2026-11-10 decision names the witness form; totality is
a new universal claim whose proof is the proof tree's `mirror_step`, which
the binary package may not import, so it would have to be reproved here or
moved to the bridge; and it changes the shape of the headline where the
witness changes only its evidence. If the owner prefers totality, it is one
more conjunct and belongs with the bridge.

## 2. The diff against packet revision 2

`git diff` of `cf8798e5:binary/packets/c2/C2Statement.lean` against
`binary/C2Statement.lean`, complete. Five hunks:

| Hunk | Reason |
| --- | --- |
| 1 (imports, header) | The placeholder file is deleted, so the image is imported directly; the file is now a root of the package, built and scanned by the gate |
| 2 (`RangeDecoderAgreement`, `Reading`) | The `bts` is the seventieth committed term under Kraken patch ten: `Reading` loses its `bts` field and the comments stop saying 69 |
| 3 (Part 3 comment) | There is one headline, so the comment no longer speaks of an alternative |
| 4 (Part 4 comment, `ReplayWitness`) | Finding F1: the witness also exhibits the further premises of `Refines`. The comment says where the two exclusions now stand |
| 5 (Part 5) | `HeadlineRefinement` is the headline; `HeadlineMachine` is removed and named once as the rejected alternative |

No premise or conclusion of `Context`, `Kept`, `ExitsCleanly`, `Refines`,
`Visits`, `WindowRetained`, `FirstExit` or `NoCounterAcceptedTwice` changes.

```diff
@@ -1,11 +1,12 @@
-import C2Placeholder
+import C2Image
 import TrustBase
 import Layouts
 import Leanux.WG.RxData
 
-/-! C2 statement packet: the receive replay window in the pinned s5 image.
+/-! Result C2, the final statement: the receive replay window in the pinned s5 image.
 Statements only: every declaration here is a `def` or a `structure` of propositions.
-Nothing here is proved. In no lake target; compiled by `binary/packets/c2/check`.
+Nothing here is proved. A root of `BinaryProofs`, so that it is built and scanned by
+`scripts/binary-proof-gate`; the headline is `HeadlineRefinement`, at the end.
 
 Range: `counter_validate` (drivers/net/wireguard/receive.c) as inlined in
 `wg_packet_rx_poll`, `[0xffffffff8139d2a6, 0xffffffff8139d3ea)`, 70 instructions:
@@ -19,18 +20,17 @@ local instance : Labels := Binary.Image.linkedLabels
 
 /-! ## Part 1. Premises: nothing checks these; a reader has to judge them -/
 
-/-- The ambient decoder agrees with the committed literal terms of the range (69
-instructions; the `bts` is the placeholder's) and of the two callback entries. -/
+/-- The ambient decoder agrees with the committed literal terms of the range (70
+instructions, the `bts` among them) and of the two callback entries. -/
 def RangeDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
   ∀ pc instruction, Range.fetch pc = some instruction → fetch pc = some instruction
 
-/-- What is assumed of the code: two readings of the image and the placeholder.
+/-- What is assumed of the code: two readings of the image.
 `ServiceDecoderAgreement` is the landed one: it covers the PC callback and the body
 shared by the comparison callbacks. -/
 structure Reading (fetch : Int64 → Option Decoded) : Prop where
   range : RangeDecoderAgreement fetch
   services : ServiceDecoderAgreement fetch
-  bts : Placeholder.BtsAt fetch
 
 /-- `struct noise_replay_counter` inside the keypair at `kp`: 1032 bytes at offset 136
 (the counter, then 128 bitmap words; the spinlock has size zero in this build). -/
@@ -159,8 +159,8 @@ def AcceptedWithinWindow : Prop :=
 /-! ## Part 3. The refinement: what the code computes, in the mirror's terms
 
 The adequacy half of the track's objective for this function. A clause of the
-recommended headline (`HeadlineRefinement`, at the end of the file); a checked lemma
-under the alternative. It mentions only the mirror, never the proof tree. -/
+headline (`HeadlineRefinement`, at the end of the file). It mentions only the mirror,
+never the proof tree. -/
 
 /-- The keypair's replay state in the mirror's world. -/
 def windowOf (world : WGWorld) (id : WG.KeypairId) : Option WG.ReplayCounter :=
@@ -201,15 +201,25 @@ def Refines : Prop :=
 /-! ## Part 4. Against vacuity: a witness and two exclusions
 
 A witness that the premises can be met, and two statements naming behaviours to rule
-out or in. `NoCounterAcceptedTwice` alone is satisfied by code that refuses
-everything; `AdvanceAccepted` excludes that for counters moving to a later word. -/
+out or in. The two exclusions (`ReplayRefused`, `AdvanceAccepted`) are in no headline:
+the first is a corollary of `NoCounterAcceptedTwice`, the second of `Refines`. -/
 
 /-- The premises are satisfiable, by a replay: the same packet counter presented twice
-to one retained window is accepted the first time and refused the second. -/
+to one retained window is accepted the first time and refused the second. And the
+further premises of `Refines` are satisfiable with them (review finding F1): the first
+visit's window bytes represent a replay state `c`, a world holds `c`, and the mirror's
+`counterValidate` on that world succeeds, accepting, as the machine does. -/
 def ReplayWitness : Prop :=
   ∃ (fetch : Int64 → Option Decoded) (kp : BitVec 64) (first second : Visit),
     Reading fetch ∧ Visits fetch kp [first, second] ∧ first.nonce = second.nonce ∧
-    accepted first.exit = true ∧ accepted second.exit = false
+    accepted first.exit = true ∧ accepted second.exit = false ∧
+    ∃ (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
+      (c : WG.ReplayCounter),
+      Layouts.ReplayFields first.entry.data.dmem
+        (kp + .ofNat 64 Layouts.keypair_receiving_counter) c ∧
+      windowOf world id = some c ∧
+      ((WG.counterValidate id first.nonce.toNat).run world).run ambient =
+        .ok ((true, world'), ambient')
 
 /-- Excluded: accepting a packet counter that an earlier visit accepted. -/
 def ReplayRefused : Prop :=
@@ -230,17 +240,13 @@ def AdvanceAccepted : Prop :=
     high.toNat / 64 < (nonce.toNat + 1) / 64 →
     accepted t = true
 
-/-! ## Part 5. The two headline forms put to the owner (revision 2) -/
+/-! ## Part 5. The headline -/
 
-/-- RECOMMENDED (the reviewer's form). What the code computes (`Refines`), that it
-exits cleanly, the transported property, and a witness that all of it is inhabited. -/
+/-- THE HEADLINE. What the code computes (`Refines`), that it exits cleanly, the
+transported property, and a witness that all of it is inhabited. (Rejected alternative:
+a machine-states-only conjunction with `AdvanceAccepted` in place of `Refines`, which
+holds of code that permutes the bits of a bitmap word.) -/
 def HeadlineRefinement : Prop :=
   ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness
 
-/-- ALTERNATIVE. Machine states only: no mirror, no representation. Says the code
-never accepts a counter twice and accepts one advancing to a later word; it does not
-say which counters inside the window are accepted, nor what the bytes mean. -/
-def HeadlineMachine : Prop :=
-  ExitsCleanly ∧ NoCounterAcceptedTwice ∧ ReplayWitness ∧ AdvanceAccepted
-
 end Binary.C2
```

The other two files: `C2Placeholder.lean` (49 lines) is deleted;
`C2Image.lean` is regenerated with one list `code` of 70 instructions
where it had `head` (67) and `tail` (2) around the missing one, the three
lines `bts    %r15,(%rax)` / size 4 / `count := 70` in, and `btsPC`,
`afterBts`, `headCount`, `tailCount` out. `binary/generate_c2.py --check`
compares it with the saved s5 ELF (present at
`.artifacts/kernel-net-choice-s5` in the main checkout): 70 instructions, 324
bytes, 13 call sites, matching.

## 3. The Kraken patch: the semantics

`binary/kraken-patches/0010-memory-bts.patch`, its hunk on
`Kraken/X64/Semantics.lean`, verbatim. This is the meaning of the seventieth
instruction and so part of what section 1 means.

```diff
diff --git a/Kraken/X64/Semantics.lean b/Kraken/X64/Semantics.lean
index 7145d79..a6f198a 100644
--- a/Kraken/X64/Semantics.lean
+++ b/Kraken/X64/Semantics.lean
@@ -832,6 +832,32 @@ set_option maxHeartbeats 1000000
     let cf := (s.regs.get base).getLsbD ((s.regs.get index).toNat % w.bits)
     undefined (fun pf => undefined (fun af => undefined (fun zf => undefined (fun sf => undefined (fun of =>
       next {s with status := {cf, pf, af, zf, sf, of}})))))
+  -- BTS r64, m64 without LOCK (REX.W 0F AB /r), one sequential step.
+  -- Modeled only where the bit lies in the addressed quadword: the offset
+  -- register is below 64 and the eight bytes at the effective address are
+  -- mapped. Outside that (where hardware addresses another quadword, at
+  -- ea + 8 * (offset asr 6), or the memory is not data memory) the step is an
+  -- explicit `unimplemented`, never an MMIO access.
+  -- CF receives the old bit; the quadword is written back with the bit set
+  -- whether or not it was set already. OF, SF, AF and PF are undefined on
+  -- Intel and AMD; ZF is unaffected on Intel and undefined on AMD, taken as
+  -- undefined, which contains both.
+  | .bts dst index =>
+    if w != .W64 then unimplemented "BTS: only the 64-bit form is modeled" else
+    let addr := (dst.interp s.regs p).zeroExtend 64
+    let offset := (s.regs.get index).toNat
+    if offset ≥ 64 then unimplemented "BTS: bit offset outside the addressed quadword" else
+    require_read_access addr .W64 (fun _unit =>
+      match Mem.loadInt s.dmem addr 8 with
+      | .none => unimplemented "BTS: destination quadword is not mapped data memory"
+      | .some old =>
+        let word : BitVec 64 := .ofInt 64 old
+        let cf := word.getLsbD offset
+        undefined (fun pf => undefined (fun af => undefined (fun zf => undefined (fun sf => undefined (fun of =>
+        require_write_access addr .W64 (fun _unit =>
+          next { s with
+            dmem := Mem.storeInt s.dmem addr 8 (word ||| (1#64 <<< offset)).toInt
+            status := {cf, pf, af, zf, sf, of} })))))))
   | .bsr dst src =>
     if w == .W8 then unimplemented "BSR has no 8-bit form" else
     src.interp s p (fun a s =>
```

Against the decision, clause by clause:

| Decided | In the hunk |
| --- | --- |
| 64-bit register offset, memory destination only | The constructor is `bts (dst : AddrExpr) (index : Reg w)`: a register destination cannot be written. Other widths are `unimplemented` here and do not parse (appendix A1) |
| Defined when the offset is below 64 and the quadword is mapped; `unimplemented` otherwise | The two `unimplemented` branches. The read does not go through Kraken's `load`, which would make an unmapped address an MMIO effect; that is my choice inside the decided semantics |
| CF takes the old bit | `cf := word.getLsbD offset`, on the word read |
| The quadword is written back with the bit set, unconditionally | `Mem.storeInt … (word ||| (1#64 <<< offset))`, on every path that reaches it |
| OF, SF, ZF, AF, PF undefined | Five `undefined` binders, as patch nine has them |
| One sequential step | One `Operation.interp` case; no intermediate state is observable |
| LOCK, immediates, register destinations, narrower widths refused | Parser (appendix A1); tested |

The patch's commit message records both vendor texts as the decision gives
them: Intel SDM vol. 2A (CF the old bit, ZF unaffected, OF/SF/AF/PF
undefined), read by the statement reviewer; AMD APM vol. 3, publication
24594 rev. 3.37, pages 132-133 (CF modified, OF/SF/ZF/AF/PF undefined; a
register bit index on a memory bit base is a signed offset over the
operand-size range, from bit 0 of the addressed byte), read by the
coordinator. **I read neither**; I recorded them. It also says why undefined
ZF (the superset of the two vendors; nothing after the instruction reads a
flag but CF) and the below-64 restriction (the offset is masked by
`and $0x3f,%r15d` with only a `lea` between) are sound for this image.

New identity: Kraken **`96d484872c2c438a4d02f47e6390507f587a095c`** =
upstream `8af78062` plus the ten patches. From a deleted checkout,
`binary/run.py --bootstrap-only` rebuilt exactly that commit and
`pin.verify_pin` accepted it.

## 4. What was rerun, and its numbers

Everything below ran on the final text with **Kraken's own `bts`** from the
committed term, under Kraken's interpreter: all 70 range instructions and
the image's callback code. No placeholder executes anything. The packet's
proposed semantics survives only as test code, as the reference every
executed `bts` step is compared with (PC, every register, all six flags,
the system flags, the destination quadword and its two neighbours): no step
differed in any run.

| Run | Final text, real `bts` | Packet revision 2, placeholder |
| --- | --- | --- |
| Single visits | 972 runs, 564 accepting, 0 failures; longest 7,697 instructions | the same |
| Eleven wrong variants, failing runs of 216 | 16, 8, 56, 160, 216, 112, 112, 108, 108, 112, 108 | the same |
| Sequences | Six sequences, 465 visits; 2, 8, 145, 143, 113 and 3 accepted; in all six the accepted counters are distinct, within the floor and identical to the mirror's | the same |
| Sequence wrong variants | No write-back: caught on 6 of 6. New bit reported: 6 of 6, by the comparison with the mirror only. Neighbouring bit, consistently: 0 of 6 (as before: only the byte-level comparison of single visits rejects it). Window zeroed between visits: 2 of 6 | the same |
| Witness, concretely | Counter 41 twice on a zeroed window: accepted, then refused; and (new, F1) the first visit's bytes represent a state on which the mirror's run succeeds and accepts | the first half |
| Search, single placements, capacity 8 | 775 layouts, 6,200 states; 2,595 meet the old `Context`, 2,377 the revised; broken on 100 (old only) and **0** (revised); replay accepted on 13 (old) and **0** (revised) | the same |
| Search, pairs of placements | 921 layouts, 3,684 states; 1,084 meet the old `Context`, 896 the revised; broken on 87 (old only) and **0** (revised); replay accepted on 1 (old) and **0** (revised) | the same |
| Review counterexample (H1) | Meets the old `Context`, fails the revised, accepts counter 63 twice on the old | the same |
| **Capacity loop, new** (capacities 0, 1, 2, 3, 40) | 28,568 states, 9,442 meeting the revised `Context`; broken on 0, 0, 18, 49, 87 (old only) and **0, 0, 0, 0, 0** (revised); replay accepted on 0, 0, 4, 13, 13 (old) and **0, 0, 0, 0, 0** (revised) | not run by the packet; the reviewer's own run of it reported 28,568 states, 9,442 meeting the revised `Context`, broken on 0, 0, 18, 49, 87 (old only) and 0 (revised), replay accepted on 0, 0, 4, 13, 13 (old) and 0 (revised) |
| Host processor (`bts_host.c`, AMD Ryzen 9 7950X3D) | 1,536 runs, 0 disagreements; no undefined flag changed | the same |
| Native comparison in Kraken's runner (`test_bts.S`), new | passes; whole assembly suite 46 of 46 | none |

**Differences from the placeholder runs: none.** A baseline rerun of the
packet at `cf8798e5` (placeholder, nine-patch Kraken) beside the new run
gives the same output line for line: the 27 per-case exits, `%bpl` values
and instruction counts, every count in the table, and the six example
layouts the search prints. The new run adds one line (the F1 witness check)
and the capacity loop. **The capacity loop's counts equal the reviewer's own
run of it.**

Two changes to the test code that could have produced one and did not.
The wrong variants of the `bts` used to perturb the placeholder; they now
replace the real instruction at its address with the same four wrong
behaviours. And the test interpreter now draws the n-th undefined value of
an instruction from the seed shifted by n, so that the real `bts`'s five
flags take the same values the placeholder runs gave them (it also makes the
two seeds differ on other instructions' undefined flags, where before both
gave the same value).

**The rendering `contextHolds`, re-read against the final `Context`**
(follow-up finding F2). Both are textually unchanged since `cf8798e5` (the
patch touched neither), and I re-read them field by field; table in
appendix A3. I found no field missing and none stricter than the Lean.
It is still a reading: nothing but that connects the two.

No discrepancy between the mirror and the binary was found (Rule Zero:
nothing to report).

## 5. What the owner accepts knowingly

From the packet and the reviews; none of it is changed by this phase.

1. **A single-CPU, coverage-instrumented build, with no lock.**
   `CONFIG_SMP` is off: the spinlock has size zero, `spin_lock_bh` is one
   `addl` to the preempt count, and the `bts` carries no LOCK prefix.
   Thirteen of the 70 instructions are KCOV calls. Nothing carries to an SMP
   build, where the lock and `lock bts` are real. The model is sequential:
   no interrupt between instructions.
2. **The entry context is argued from the disassembly, not derived.** That
   `%r13` is the keypair, `%rbx` the packet, the counter is the quadword at
   `skb+0x28`, the stack and the coverage state are as `Context` says and
   apart as it says: constructed states meet it; no captured kernel state
   has been checked against it.
3. **The window is unchanged between visits** (`WindowRetained`): a premise
   about the rest of the kernel. Keypair lifetime, the completeness of the
   list of visits and the absence of other writers all sit in it.
4. **The gap between the range and "a replayed packet is dropped".** The
   range ends at `setb %bpl`. What follows (the unlock, the branch, the drop
   path), what precedes (that this is the keypair and counter the packet was
   decrypted under), that every delivery passes through the range, and the
   protocol's meaning of a counter are not in any statement: the packet's
   nine items (its section 4).
5. **Decoder agreement is tested, not proved.** `Reading` assumes the
   decoder returns the committed terms. `generate_c2.py --check` compares
   objdump's bytes with the ELF and every branch with its target; objdump's
   text and Kraken's parser are trusted, and that the running kernel
   executes these bytes is assumed.
6. **Kraken's semantics, the tenth patch included**, is the base: tested
   against one processor and read against two manuals by two readers, not
   proved faithful.
7. **`Refines` says no more than the mirror.** A defect shared by the mirror
   and the code passes; the differential check is what stands against that.
   It is conditional on the mirror's run succeeding, which the witness shows
   possible and the landed `mirror_step` shows general (outside this
   headline).
8. **The search is not a proof.** It found nothing under the revised
   premises at six capacities; triple coincidences and the instruction
   semantics are outside it.

## Appendix

### A1. The rest of the patch

Parser and constructor hunks, verbatim (the two printer lines and the tests
are in the patch file):

```diff
diff --git a/Kraken/X64/Parser/Basic.lean b/Kraken/X64/Parser/Basic.lean
index 6e8dfd8..f216d8a 100644
--- a/Kraken/X64/Parser/Basic.lean
+++ b/Kraken/X64/Parser/Basic.lean
@@ -1067,6 +1067,18 @@ def parseInstr : Parser Instr := do
     | .regular _ .W8 _ => fail "BT has no 8-bit form"
     | _ => pure instruction
 
+  -- BTS: only `bts r64, m64` (REX.W 0F AB /r), the one form in the pinned
+  -- WireGuard text. Register destinations, immediate offsets and the 16- and
+  -- 32-bit forms are rejected here; a LOCK prefix is not a mnemonic this
+  -- parser knows, so `lock bts` is rejected as well.
+  | "bts" | "btsq" => do
+    let (_, index) ← parseAO parseRegA .W64
+    parseComma
+    let (addr_w, dst) ← parseAO parseRegOrMem .W64
+    match dst with
+    | .mem a => pure (toInstr addr_w (.bts a index))
+    | .reg _ => fail "BTS: register destination is not modeled"
+
   -- Byte swap
   | "bsr" | "bsrw" | "bsrl" | "bsrq" => do
     let width ← if mn == "bsr" then pure none else some <$> instrWidth mn
diff --git a/Kraken/X64/Syntax.lean b/Kraken/X64/Syntax.lean
index 4fc9d7a..a744802 100644
--- a/Kraken/X64/Syntax.lean
+++ b/Kraken/X64/Syntax.lean
@@ -238,6 +238,7 @@ inductive Operation (w : Width)
   | bswap  (dst : Reg w) -- (_ : w = .W32 ∨ w = .W64)
   | bsr (dst : Reg w) (src : RegOrMem w)
   | bt (base : Reg w) (index : Reg w)
+  | bts (dst : AddrExpr) (index : Reg w) -- memory bit base, register bit offset; 64-bit only
   -- Control flow
   | jcc (cc : CondCode) (target : Label)
   | jmp (target : RelRegOrMem)
```

Tests in the patch, as patch nine has them. `Kraken/X64/BtsTests.lean`:
the one accepted form parses with and without the `q` suffix; fifteen
other spellings do not (register destination, immediate offset, 32-, 16-
and 8-bit forms, `lock`, `btr`, `btc`); both printers and the AT&T round
trip; CF, the written quadword, both neighbouring quadwords, every register
and the system flags at all 64 offsets on four words with the bit clear and
set; exactly one 8-byte read and one 8-byte write, also when the bit was
already set; each undefined flag taking both values from either incoming
value, and all five set or clear together; offsets 64, 65, 127, 128, 2^32,
2^63, 2^64-64 and 2^64-1 declined before any access; an unmapped and two
partly mapped quadwords declined with `unimplemented`, not an MMIO effect;
the three narrower widths declined if constructed directly.
`Kraken/X64/Test/asm/test_bts.S` is the native comparison (CF and the
written quadword, three cases) in Kraken's assembly runner.

Two one-off mutants of the semantics, run once in a scratch clone and
deleted: CF taken from the new bit, and the quadword written back without
the bit. Each fails `BtsTests` (five and four guards) and fails the native
comparison.

### A2. Where the statement lives, and the wiring

`binary/C2Image.lean` and `binary/C2Statement.lean`, flat in `binary/`, added
to the `roots` of `BinaryProofs` in `binary/lakefile.toml`. Reason: the gate
builds the package's default targets and scans `binary/*.lean` (not
subdirectories) for `sorry`, `axiom` and the other escapes, so this is where
the files are both built and scanned with no change to a script. There is no
theorem and no `sorry`; the gate's axiom list (71 terminal statements) is
unchanged because there is nothing of C2 to list yet. The generator is
`binary/generate_c2.py`, beside the package's other generators. The executed
tests stay in `binary/packets/c2/` (`C2Test.lean`, `C2Sequence.lean`,
`C2Adversarial.lean`, `check`, `surface`, `bts_host.c`), in no lake target,
compiled against the built package.

Not done, deliberately: `binary/surface.py` and `TrustSurface.expected.txt`
do not print the C2 statements. What the gate prints is a separate proposal
under the 2026-11-10 decision; the expected file changes in exactly one
line, the Kraken commit.

### A3. `contextHolds` against `Context`, field by field

The search's layout gives `kp`, `skb`, `task`, `area` modulo 2^64, the
capacity, mode and softirq word as the `KcovLayout`, and takes `nonce` to be
the quadword the state holds at `skb + 0x28`. `span b n` is the set
`{(b + i) mod 2^64 | i < n}`, which is `InRange b n`.

| `Context` field | Rendering in `contextHolds` | Same? |
| --- | --- | --- |
| `pc` | `s.pc == Range.entry` | yes |
| `keypair` | `r13.toNat == kp % 2^64` | yes |
| `packet` | `rbx.toNat == skb % 2^64` | yes |
| `nonce` | the 8-byte load at `skb + 0x28` succeeds; `nonce` is then its value | yes: the field only asks that some 64-bit value is loaded |
| `window` | every byte of `span (kp+136) 1032` is mapped | yes (`windowBytes` is `InRange (kp+136) 1032`; 136 and 1032 are the `Layouts` constants) |
| `aligned` | `sp % 8 == 0` | yes (2^64 is a multiple of 8) |
| `stack` | every byte of `span (sp-8) 8` and `span (sp+0x10) 16` is mapped | yes |
| `coverage` (`KcovState`) | the five metadata loads equal the layout (task word at `0xffffffff81cc85c0`; mode, capacity, area, softirq at task + `0x6e0`, `0x6e4`, `0x6e8`, `0x704`, widths 4, 4, 8, 4); the 4-byte preempt load equals `preempt`; in modes 2 and 3 every buffer word loads and the header word is at most the capacity | yes; the buffer clause is skipped outside modes 2 and 3, as in `KcovState` |
| `stackWindow` | the stack spans and the window span share no byte | yes |
| `stackPreempt` | the stack spans and `span preempt 4` share no byte | yes |
| `windowPreempt` | the window span and `span preempt 4` share no byte | yes |
| `coverageApart` | the metadata spans, with the storage spans in modes 2 and 3, share no byte with the footprint (stack spans, window, preempt) | yes (`coverageBytes` against `Footprint`) |
| `coverageMetadata` | in modes 2 and 3 the storage spans (`span area 8`, `span area (8·cap)`) share no byte with the five metadata spans | yes |

The first twelve rows are the search's "old" `Context`; all thirteen are the
"revised" one, which is the final text's.

### A4. What changed beyond a rebuild, and the gate

`MemoryInvariant.operation` and `SystemInvariant.operation` prove a property
of every Kraken operation by cases, with a shared tactic that knows Kraken's
`load` and `store`. The new instruction reads and writes its quadword
directly (so that an unmapped one is `unimplemented`), and the tactic does
not close its case. Each proof gains one explicit `bts` case, fourteen lines
with its comment, no statement changed; both still print the three standard axioms. Earlier
patches left the same kind of mark there (`case' xadd`, `case' cmpxchg`).
I judged this within "carrying the patch"; it is in the patch's commit and
its message says so. `RegionExecution.RegionOperation` is untouched (`bts`
joins it with the proof work).

Not changed and for the landing to consider: the binary rows of the
register (`docs/proofs.md`) name the commits their results were validated
at, and one says patch nine is pinned. The pin has moved; every landed
result rebuilt and passed the gate under it, but the register does not say
so yet.

`scripts/binary-proof-gate` on the final tree: **PASS**. Kraken pin and
clean tree `96d48487…`; build 1,121 jobs (1,119 and the two statement
files); 71 terminal statements, each on `propext`, `Classical.choice`,
`Quot.sound` only; trust-surface comparison PASS (4,713 lines, one changed:
`def krakenCommit`); source-escape scan over 946 files, the two new ones
among them. The external `lake check` outside the sandbox was not run and is
the owner's at the claim point.

### A5. Reproduction

From the worktree root; the second needs pyelftools and the saved ELF.

```sh
scripts/in-bundle python3 -B binary/run.py --bootstrap-only     # upstream + ten patches = 96d48487
scripts/in-bundle python3 -B binary/generate_c2.py --check      # the 70 + 10 terms against the ELF
capped -- scripts/in-bundle lake -d binary build
capped -- scripts/in-bundle python3 scripts/binary-proof-gate
binary/packets/c2/check                                         # tests and search: about 30 minutes
binary/packets/c2/surface                                       # the printed line counts of section 1
(cd .deps/kraken && python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm/test_bts.S)   # after lake build krakenrunner_x64 att2intel there
```
