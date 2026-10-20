import PeerLoadHistory
import PeerFirstStack
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem refcount_load_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (body : MachineData) (safe : CallStackSafe outer body.regs.rsp) (count : UInt32)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x20⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine = ⟨loaded body count, Image.PeerGet.entry+0x2d⟩ ∧
      StableTrace (loaded body count) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x20⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (refcount_load_history fetch agree body count history field)) last (by
    rintro t ⟨machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
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
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x32⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af,
        Image.PeerGet.entry+0x36⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x32⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (old_arguments_history fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
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
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f4100) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (body : MachineData) (safe : CallStackSafe outer body.regs.rsp) (count : UInt32)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x20⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine.pc = Image.PeerGet.entry+0x3b ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧
      t.machine.data.regs.rbp = count.toUInt64 ∧
      StableTrace (loaded body count) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x20⟩, history⟩ := by
  have load := refcount_load_trace fetch agree body safe count field coverage preempt ready
      rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ load
  rintro loadedState ⟨machine₁, trace₁⟩
  have pc₁ : loadedState.machine.pc = Image.PeerGet.entry+0x2d := congrArg MachineState.pc machine₁
  have call := scan_call_cursor fetch "L_ffffffff810f31f0" loadedState
    (by rw [pc₁]; exact agree _ _ (by rfl)) .pc tracePc (loaded body count) coverage preempt safe trace₁.frame (trace₁.frame).ready.pc_allowed
    rxSection events trace₁.observed trace₁.last (by
      simp [LookupObservation.edge, pc₁, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ call
  rintro afterPc ⟨pc₂, bx₂, bp₂, trace₂⟩
  have pc₂ : afterPc.machine.pc = Image.PeerGet.entry+0x32 := by rw [pc₂, pc₁]; rfl
  have setup := old_arguments_trace fetch agree (loaded body count) afterPc.machine.data coverage preempt safe trace₂.frame
      rxSection afterPc.history events trace₂.observed (by rw [← pc₂]; exact trace₂.last)
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0x32⟩, afterPc.history⟩ : Executed) = afterPc := by rw [← pc₂]
  rw [cursor] at setup
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ setup
  rintro afterSetup ⟨af, machine₃, trace₃⟩
  have pc₃ : afterSetup.machine.pc = Image.PeerGet.entry+0x36 := congrArg MachineState.pc machine₃
  have call := scan_call_cursor fetch "L_ffffffff810f4100" afterSetup
    (by rw [pc₃]; exact agree _ _ (by rfl)) .constCmp4 traceCmp (loaded body count) coverage preempt safe trace₃.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection events trace₃.observed trace₃.last (by
      simp [LookupObservation.edge, pc₃, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ call
  rintro final ⟨pc₄, bx₄, bp₄, trace₄⟩
  refine ⟨by rw [pc₄, pc₃]; rfl, ?_, ?_, trace₁.trans (trace₂.trans (trace₃.trans trace₄))⟩
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bx₂, machine₁, loaded] using bx₄
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bp₂, machine₁, loaded] using bp₄

#print axioms refcount_load_trace
#print axioms old_arguments_trace
#print axioms load_body_history

end Binary.PeerGet.First
