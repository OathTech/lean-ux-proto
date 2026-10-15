import ScanFrame
import PeerLoad
import PeerCompareHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

theorem refcount_word_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (count : UInt32) (history : List MachineState)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec + 0x420) 4 = some count.toNat) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨LookupHistory.indexLoaded s count, Image.PeerGet.entry + 0x26⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s, Image.PeerGet.entry + 0x20⟩, history⟩ := by
  have here := agree (Image.PeerGet.entry + 0x20)
    ⟨.regular .W64 .W32 (.mov (.reg (.low .rbp .W32))
      (.regOrMem (.mem {base := some (.reg .rbx), idx := none, disp := .int64 0x420}))), 6⟩ (by rfl)
  refine instruction_history fetch ⟨s, Image.PeerGet.entry + 0x20⟩ history
    (fun t => t = ⟨LookupHistory.indexLoaded s count, Image.PeerGet.entry + 0x26⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, AddrExpr.interp, Reg64s.get64,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, LookupHistory.indexLoaded, BitVec.take, Image.PeerGet.entry] at field ⊢
  rw [field]
  simp [Effects.All, BitVec.ofInt_ofNat]


/-- LEA computes the refcount address without touching memory or flags. -/
theorem refcount_address_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨{s with regs := {s.regs with r13 := s.regs.rbx+0x420}}, Image.PeerGet.entry+0x2d⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x26⟩, history⟩ := by
  have here := agree (Image.PeerGet.entry+0x26)
    ⟨.regular .W64 .W64 (.lea (.low .r13 .W64)
      {base := some (.reg .rbx), idx := none, disp := .int64 0x420}), 7⟩ (by rfl)
  refine instruction_history fetch ⟨s, Image.PeerGet.entry+0x26⟩ history
    (fun t => t = ⟨{s with regs := {s.regs with r13 := s.regs.rbx+0x420}}, Image.PeerGet.entry+0x2d⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, MachineData.setReg, AddrExpr.interp,
    Reg64s.get64, BitVec.take, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add,
    BitVec.ofInt_toInt, BitVec.ofInt_ofNat, Effects.All, Image.PeerGet.entry]

/-- Both actual load-prefix successors; the physical count is not supplied
    as a postcondition, but obtained from the mapped memory word. -/
theorem refcount_load_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (s : MachineData) (count : UInt32) (history : List MachineState)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+0x420) 4 = some count.toNat) :
    historySteps fetch 2 (fun t =>
      t.machine = ⟨loaded s count, Image.PeerGet.entry+0x2d⟩ ∧
      t.history = history ++ [⟨indexLoaded s count, Image.PeerGet.entry+0x26⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x20⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (refcount_word_history fetch agree s count history field)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨indexLoaded s count, Image.PeerGet.entry+0x26⟩,
      history ++ [⟨indexLoaded s count, Image.PeerGet.entry+0x26⟩]⟩ := by cases t; simp_all
  rw [cursor]
  have next := refcount_address_history fetch agree (indexLoaded s count)
    (history ++ [(⟨indexLoaded s count, Image.PeerGet.entry+0x26⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ next
  rintro final ⟨machine, recorded⟩
  have state : final.machine = ⟨loaded s count, Image.PeerGet.entry+0x2d⟩ := by
    simpa [indexLoaded, loaded, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg.base, Reg.offset, BitVec.drop, BitVec.take] using machine
  exact ⟨state, by simpa only [List.append_assoc, List.singleton_append] using recorded⟩

#print axioms refcount_word_history
#print axioms refcount_address_history
#print axioms refcount_load_history

/-- The load stage changes R13 before its next cut. The intermediate MOV
    successor is retained, and proved not to be a correspondence point. -/
theorem refcount_load_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (body : MachineData) (count : UInt32)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x20⟩) :
    historySteps fetch 2 (fun t =>
      t.machine = ⟨loaded body count, Image.PeerGet.entry+0x2d⟩ ∧
      StableTrace (loaded body count) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x20⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (refcount_load_history fetch agree body count history field)
  rintro t ⟨machine, recorded⟩
  have frame : ScanFrame (loaded body count) coverage preempt (loaded body count) :=
    ScanFrame.initial _ _ _ (ready.congr rfl rfl)
  rw [machine] at recorded
  refine ⟨machine, StableTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using frame
  · simp [machine]
  · simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member cut
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact False.elim ((by decide : Image.PeerGet.entry+0x26 ∉ Image.cutPoints) cut)
    · exact frame

/-- Old-count comparison arguments emit no decision; the TEST/JE that
    follows its callback supplies the decision and its actual operands. -/
theorem old_arguments_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x32⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af,
        Image.PeerGet.entry+0x36⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x32⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (old_arguments_history fetch agree body history)
  rintro t ⟨af, machine, recorded⟩
  have first : ScanFrame base coverage preempt (zeroed body (.low .rdi .W32) af) := by
    apply frame.congr <;> rfl
  have second : ScanFrame base coverage preempt
      (xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af) := by
    apply frame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af, machine, StableTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using second
  · simp [machine]
  · simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

/-- Load the physical count and execute both comparison-setup callbacks,
    retaining every instruction and the count in EBP at the zero guard. -/
theorem load_body_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (body : MachineData) (count : UInt32)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x20⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = Image.PeerGet.entry+0x3b ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧
      t.machine.data.regs.rbp = count.toUInt64 ∧
      StableTrace (loaded body count) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x20⟩, history⟩ := by
  have load := historySteps_eventually fetch 2 _ _
    (refcount_load_trace fetch agree body count field coverage preempt ready
      rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ load
  rintro loadedState ⟨machine₁, trace₁⟩
  have pc₁ : loadedState.machine.pc = Image.PeerGet.entry+0x2d := congrArg MachineState.pc machine₁
  have call := scan_call_cursor fetch "L_ffffffff810f3100" loadedState
    (by rw [pc₁]; exact agree _ _ (by rfl)) .pc tracePc (loaded body count) coverage preempt trace₁.frame (trace₁.frame).ready.pc_allowed
    rxSection events trace₁.observed trace₁.last (by
      simp [LookupObservation.edge, pc₁, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro afterPc ⟨pc₂, bx₂, bp₂, trace₂⟩
  have pc₂ : afterPc.machine.pc = Image.PeerGet.entry+0x32 := by rw [pc₂, pc₁]; rfl
  have setup := historySteps_eventually fetch 2 _ _
    (old_arguments_trace fetch agree (loaded body count) afterPc.machine.data coverage preempt trace₂.frame
      rxSection afterPc.history events trace₂.observed (by rw [← pc₂]; exact trace₂.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0x32⟩, afterPc.history⟩ : Executed) = afterPc := by rw [← pc₂]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af, machine₃, trace₃⟩
  have pc₃ : afterSetup.machine.pc = Image.PeerGet.entry+0x36 := congrArg MachineState.pc machine₃
  have call := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₃]; exact agree _ _ (by rfl)) .constCmp4 traceCmp (loaded body count) coverage preempt trace₃.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection events trace₃.observed trace₃.last (by
      simp [LookupObservation.edge, pc₃, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro final ⟨pc₄, bx₄, bp₄, trace₄⟩
  refine ⟨by rw [pc₄, pc₃]; rfl, ?_, ?_, trace₁.trans (trace₂.trans (trace₃.trans trace₄))⟩
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bx₂, machine₁, loaded] using bx₄
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bp₂, machine₁, loaded] using bp₄

#print axioms refcount_load_trace
#print axioms old_arguments_trace
#print axioms load_body_history

end Binary.PeerGet
