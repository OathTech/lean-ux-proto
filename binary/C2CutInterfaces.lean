import C2Cut

/-! Result C2, the cut of the proof: the interface propositions.

Every lemma that crosses a work-package boundary is here as `def Name : Prop`. A
package proves the propositions assigned to it (as `theorem name : Name`) and may use
any other proposition only as a hypothesis of that exact name. `C2CutAssembly` proves
the headline's clauses from these propositions, so they are known to suffice.

| Package | Propositions |
| --- | --- |
| WP1 (callbacks and call sites; roots `CallbackCmp8`, `C2Callbacks`) | `Callback.Cmp8.PcRule`, `Cmp8Rule`, `ConstCmp8Rule` (in `CallbackCmp8Rule`); `StubsAgree`, `BtsSupported`, `RegionsLaidOut`, `PcSite`, `Cmp8Site`, `ConstCmp8Site` |
| WP2 (the range; root `C2Range`) | `HeadSegment`, `AdvanceEnters`, `LoopIteration`, `AdvanceStores`, `TailSegment` |
| WP3 (representation, mirror, sequences, witness; root `C2Sequences`) | `WindowMapped`, `WindowOfFields`, `FieldsOfWindow`, `FieldsFit`, `FieldsRetained`, `FieldsMapped`, `MirrorFollowsSpec`, `WorldHolds`, `FirstExitDetermined`, `FirstExitExists`, `WitnessStart` |
-/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ## WP1. Layout, `bts`, and the call sites -/

/-- THE ADAPTER to the shared callback module. A decoder that agrees with the range's
literal terms (which include the two 8-byte entries, `Range.cmp8Stub` and
`Range.constCmp8Stub`) agrees with the neutral copy of those entries that
`CallbackCmp8Rule` is stated against. The C2 side of the single statement of the
callback; C1 proves the same of its own image terms on its branch. -/
def StubsAgree : Prop :=
  ∀ (fetch : Int64 → Option Decoded), RangeDecoderAgreement fetch →
    Callback.Cmp8.Agreement fetch

/-- REGION SUPPORT FOR `bts`. Kraken's `bts` (patch ten) is monotone in its
continuations, as `RegionExecution.operation_mono` shows for the operations
`RegionOperation` lists; `bts` is not in that list. Proved beside the landed lemma, not
by editing it (`RegionExecution` is shared with C1). -/
def BtsSupported : Prop :=
  ∀ (dst : AddrExpr) (index : Reg .W64), CpsMono (.regular .W64 .W64 (.bts dst index))

/-- LAYOUT. Under a decoder that agrees with the range's literal terms, every run of
consecutive instructions of the range is laid out at its address, the `bts` included.
The execution package chooses its own regions. -/
def RegionsLaidOut : Prop :=
  ∀ (fetch : Int64 → Option Decoded), RangeDecoderAgreement fetch →
    ∀ first count, first + count ≤ Range.count →
      LaidOut fetch (regionPC first) (regionCode first count)

/-- A CALL SITE. From a state at a `call` to `callee` that satisfies the carried
invariant, the machine comes back to the instruction after the call with the invariant
again; `%rbp`, `%r14`, `%r15` and the two spill slots are as they were; and if no state
so far was at an exit then none is now. Everything else the callee may have changed:
the caller-saved registers and the flags are not described.

This carries the coverage readiness: the callee's readiness is derived here from
`Carried.coverage` and the address-only premises of `Context`, and `Carried.coverage`
is re-established from the callee's exact stores. -/
def CallSite (callee : Int64) : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s0 : MachineState) (kp skb nonce : BitVec 64) (w : Window)
    (d : MachineData) (pc : Int64) (target : Label) (history : List MachineState),
    Reading fetch → Context layout preempt s0 kp skb nonce →
    fetch pc = some ⟨Instrumentation.callInstruction target, 5⟩ → label target = callee →
    pc + 5 ∉ exits →
    Carried layout preempt kp s0 w d →
    Eventually (historyStep fetch)
      (fun e => e.machine.pc = pc + 5 ∧
        Carried layout preempt kp s0 w e.machine.data ∧
        e.machine.data.regs.rbp = d.regs.rbp ∧
        e.machine.data.regs.r14 = d.regs.r14 ∧
        e.machine.data.regs.r15 = d.regs.r15 ∧
        e.machine.data.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x10) 8 =
          d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x10) 8 ∧
        e.machine.data.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x18) 8 =
          d.dmem.loadInt (s0.data.regs.rsp.toBitVec + 0x18) 8 ∧
        ((∀ u ∈ history, u.pc ∉ exits) → Quiet e))
      ⟨⟨d, pc⟩, history⟩

/-- The seven sites that call `__sanitizer_cov_trace_pc` (2, 4, 6, 8, 10, 12, 13). -/
def PcSite : Prop := CallSite (.ofNat 0xffffffff810f31f0)

/-- The four sites that call `__sanitizer_cov_trace_cmp8` (5, 7, 9, 11). -/
def Cmp8Site : Prop := CallSite Callback.Cmp8.cmp8Entry

/-- The two sites that call `__sanitizer_cov_trace_const_cmp8` (1, 3). -/
def ConstCmp8Site : Prop := CallSite Callback.Cmp8.constCmp8Entry

/-! ## WP2. The range, segment by segment -/

/-- What holds when the head of the range (+0 to +161, call sites 1 to 7) is done: an
exit if one of the three tests rejects, else one of the two cuts. -/
def HeadPost (layout : KcovLayout) (preempt : BitVec 32) (kp : BitVec 64)
    (s0 : MachineState) (w : Window) (nonce : BitVec 64) (e : Executed) : Prop :=
  if Rejects w nonce then AtExit layout preempt kp s0 (validate w nonce) e
  else if w.counter < nonce + 1 then AtAdvance layout preempt kp s0 w (nonce + 1) e
  else AtTail layout preempt kp s0 w (nonce + 1) e

/-- SEGMENT, the head: the load of the packet counter, the add to the preempt count,
the limit rejections, the too-old rejection and the in-window branch. -/
def HeadSegment : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window),
    Reading fetch → Context layout preempt s kp skb nonce →
    WindowAt s.data.dmem (windowBase kp) w →
    Eventually (historyStep fetch) (HeadPost layout preempt kp s w nonce) ⟨s, [s]⟩

/-- SEGMENT, entering the advance path (+161 to +219 or +263, call sites 8 and 9): the
iteration count is computed and capped, and the loop is skipped when the two word
indices are equal. -/
def AdvanceEnters : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window) (t : BitVec 64) (e : Executed),
    Reading fetch → Context layout preempt s kp skb nonce →
    AtAdvance layout preempt kp s w t e →
    Eventually (historyStep fetch)
      (fun e' => if top w t = 0 then AtStore layout preempt kp s w t e'
        else AtLoop layout preempt kp s w t 0 e') e

/-- SEGMENT, one iteration of the clear loop (+219 to +263, call sites 10 and 11): one
more word is cleared, and the loop goes round again or is left. -/
def LoopIteration : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window) (t : BitVec 64) (i : Nat)
    (e : Executed),
    Reading fetch → Context layout preempt s kp skb nonce →
    AtLoop layout preempt kp s w t i e →
    Eventually (historyStep fetch)
      (fun e' => if i + 1 < top w t then AtLoop layout preempt kp s w t (i + 1) e'
        else AtStore layout preempt kp s w t e') e

/-- SEGMENT, the store of the counter (+263 to +280, call site 12). -/
def AdvanceStores : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window) (t : BitVec 64) (e : Executed),
    Reading fetch → Context layout preempt s kp skb nonce →
    AtStore layout preempt kp s w t e →
    Eventually (historyStep fetch) (AtTail layout preempt kp s (advance w t) t) e

/-- SEGMENT, the tail (+280 to the exit at +324, call site 13): `bts`, the unlock
argument, `setb`. -/
def TailSegment : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64) (w : Window) (t : BitVec 64) (e : Executed),
    Reading fetch → Context layout preempt s kp skb nonce →
    AtTail layout preempt kp s w t e →
    Eventually (historyStep fetch) (AtExit layout preempt kp s (tested w t)) e

/-! ## WP3. Representation, the mirror, sequences, the witness -/

/-- REPRESENTATION. Mapped window bytes hold some machine window. -/
def WindowMapped : Prop :=
  ∀ (m : Mem 64) (kp : BitVec 64),
    (∀ a, windowBytes kp a → (m.get? a).isSome = true) → ∃ w, WindowAt m (windowBase kp) w

/-- REPRESENTATION. Bytes that represent a mirror replay state hold its machine window. -/
def WindowOfFields : Prop :=
  ∀ (m : Mem 64) (base : BitVec 64) (c : WG.ReplayCounter),
    Layouts.ReplayFields m base c → WindowAt m base (ofCounter c)

/-- REPRESENTATION. Bytes that hold a machine window represent its mirror replay state. -/
def FieldsOfWindow : Prop :=
  ∀ (m : Mem 64) (base : BitVec 64) (w : Window),
    WindowAt m base w → Layouts.ReplayFields m base (toCounter w)

/-- REPRESENTATION. A represented replay state fits the machine's widths. -/
def FieldsFit : Prop :=
  ∀ (m : Mem 64) (base : BitVec 64) (c : WG.ReplayCounter),
    Layouts.ReplayFields m base c → Fits c

/-- REPRESENTATION. The representation reads only the 1032 window bytes. -/
def FieldsRetained : Prop :=
  ∀ (m m' : Mem 64) (kp : BitVec 64) (c : WG.ReplayCounter),
    Layouts.ReplayFields m (windowBase kp) c →
    (∀ a, windowBytes kp a → m.get? a = m'.get? a) →
    Layouts.ReplayFields m' (windowBase kp) c

/-- REPRESENTATION. Represented window bytes are mapped. -/
def FieldsMapped : Prop :=
  ∀ (m : Mem 64) (kp : BitVec 64) (c : WG.ReplayCounter),
    Layouts.ReplayFields m (windowBase kp) c →
    ∀ a, windowBytes kp a → (m.get? a).isSome = true

/-- THE MIRROR LINK, step by step collapsed to its result. A successful run of the
mirror's `counterValidate` on a world holding a fitting `c` returns what the pivot
returns on `c`'s machine window, leaves the pivot's window as the keypair's replay
state, and the exit the statement names is the pivot's. The mirror's own function, in
the binary package, with no reference to the proof tree. -/
def MirrorFollowsSpec : Prop :=
  ∀ (world world' : WGWorld) (ambient ambient' : Ambient) (id : WG.KeypairId)
    (c : WG.ReplayCounter) (nonce : BitVec 64) (result : Bool),
    Fits c → windowOf world id = some c →
    ((WG.counterValidate id nonce.toNat).run world).run ambient = .ok ((result, world'), ambient') →
    result = (validate (ofCounter c) nonce).accepted ∧
    windowOf world' id = some (toCounter (validate (ofCounter c) nonce).window) ∧
    exitPC c nonce.toNat = (validate (ofCounter c) nonce).exit

/-- THE WORLD. Every replay state is held by some world, and there is an ambient state
to run the mirror in. -/
def WorldHolds : Prop :=
  ∀ c : WG.ReplayCounter, ∃ (world : WGWorld) (id : WG.KeypairId) (_ : Ambient),
    windowOf world id = some c

/-- SEQUENCES. A proof that every execution from `s` reaches an exit first with `P`
speaks about each actual first exit: Kraken's undefined values are all quantified over,
and the first exit of an actual history is on one of the proved paths. -/
def FirstExitDetermined : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (s t : MachineState) (P : MachineState → Prop),
    Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧ P e.machine)
      ⟨s, [s]⟩ →
    FirstExit fetch s t → P t

/-- SEQUENCES. Such a proof has an actual first exit. -/
def FirstExitExists : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (s : MachineState) (P : MachineState → Prop),
    Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧ P e.machine)
      ⟨s, [s]⟩ →
    ∃ t, FirstExit fetch s t ∧ P t

/-- THE WITNESS, its concrete part: a decoder that reads the image; an entry state
that meets `Context`, whose window bytes represent a replay state `c`; a world holding
`c` on which the mirror accepts the packet counter and then, run again on the world it
left, refuses it; and the state is revisitable: any exit state that keeps what `Kept`
says, with the stack slots and the window still mapped, is again an entry state for the
same keypair, packet and counter once its program counter is put back at the entry.

The two executions under Kraken and their first exits are not asked for here: the
assembly derives them from `Refines` and `FirstExitExists`. -/
def WitnessStart : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (layout : KcovLayout) (preempt : BitVec 32)
    (s : MachineState) (kp skb nonce : BitVec 64)
    (world world₁ world₂ : WGWorld) (ambient ambient₁ ambient₂ : Ambient)
    (id : WG.KeypairId) (c : WG.ReplayCounter),
    Reading fetch ∧ Context layout preempt s kp skb nonce ∧
    Layouts.ReplayFields s.data.dmem (windowBase kp) c ∧
    windowOf world id = some c ∧
    ((WG.counterValidate id nonce.toNat).run world).run ambient =
      .ok ((true, world₁), ambient₁) ∧
    ((WG.counterValidate id nonce.toNat).run world₁).run ambient₁ =
      .ok ((false, world₂), ambient₂) ∧
    ∀ t : MachineState, Kept layout preempt kp s t →
      (∀ a, stackBytes s.data.regs.rsp.toBitVec a → (t.data.dmem.get? a).isSome = true) →
      (∀ a, windowBytes kp a → (t.data.dmem.get? a).isSome = true) →
      Context layout (preempt + 0x200) ⟨t.data, Range.entry⟩ kp skb nonce

end Binary.C2
