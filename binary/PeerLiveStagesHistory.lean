import PeerLiveSetupHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- Guard, PC callback, argument setup and actual comparison callback. -/
theorem live_retry_stage (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base body : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body) (accepted : body.regs.get (.low .r15 .W8) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x60⟩) :
    Eventually (historyStep fetch) (fun t => ∃ point : MachineState,
      t.machine.pc = Image.PeerGet.entry+0x77 ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧ t.machine.data.regs.rbp = body.regs.rbp ∧
      EqualOutside (scanWrites base coverage) base.dmem point.data.dmem ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false point]) t)
      ⟨⟨body, Image.PeerGet.entry+0x60⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (retry_guard_trace fetch agree base body coverage preempt frame accepted rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, guardMachine, guardTrace⟩
  have pc₁ : guarded.machine.pc = Image.PeerGet.entry+0x69 := congrArg MachineState.pc guardMachine
  let event := LookupObservation.decision rxSection .refcountAddNzRetry false guarded.machine
  have call := scan_call_cursor fetch "L_ffffffff810f3100" guarded
    (by rw [pc₁]; exact agree _ _ (by rfl)) .pc tracePc base coverage preempt guardTrace.frame
    rxSection (events ++ [event]) guardTrace.observed guardTrace.last (by
      simp [LookupObservation.edge, pc₁, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro afterPc ⟨pc₂, bx₂, bp₂, trace₂⟩
  have pc₂ : afterPc.machine.pc = Image.PeerGet.entry+0x6e := by rw [pc₂, pc₁]; rfl
  have setup := historySteps_eventually fetch 2 _ _
    (live_negative_arguments_trace fetch agree base afterPc.machine.data coverage preempt trace₂.frame
      rxSection afterPc.history (events ++ [event]) trace₂.observed (by rw [← pc₂]; exact trace₂.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0x6e⟩, afterPc.history⟩ : Executed) = afterPc := by rw [← pc₂]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af₂, machine₃, trace₃⟩
  have pc₃ : afterSetup.machine.pc = Image.PeerGet.entry+0x72 := congrArg MachineState.pc machine₃
  have call := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₃]; exact agree _ _ (by rfl)) .constCmp4 traceCmp base coverage preempt trace₃.frame
    rxSection (events ++ [event]) trace₃.observed trace₃.last (by
      simp [LookupObservation.edge, pc₃, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro final ⟨pc₄, bx₄, bp₄, trace₄⟩
  refine ⟨guarded.machine, by rw [pc₄, pc₃]; rfl, ?_, ?_, guardTrace.frame.memory,
    guardTrace.trans (trace₂.trans (trace₃.trans trace₄))⟩
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bx₂, guardMachine, tested] using bx₄
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bp₂, guardMachine, tested] using bp₄

#print axioms live_retry_stage

/-- Guard, PC callback, argument setup and actual comparison callback. -/
theorem live_negative_stage (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base body : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body) (accepted : (body.regs.get (.low .rbp .W32)).msb = false)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x77⟩) :
    Eventually (historyStep fetch) (fun t => ∃ point : MachineState,
      t.machine.pc = Image.PeerGet.entry+0x8a ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧ t.machine.data.regs.rbp = body.regs.rbp ∧
      EqualOutside (scanWrites base coverage) base.dmem point.data.dmem ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false point]) t)
      ⟨⟨body, Image.PeerGet.entry+0x77⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (negative_guard_trace fetch agree base body coverage preempt frame accepted rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, guardMachine, guardTrace⟩
  have pc₁ : guarded.machine.pc = Image.PeerGet.entry+0x7b := congrArg MachineState.pc guardMachine
  let event := LookupObservation.decision rxSection .refcountAddNzNegative false guarded.machine
  have call := scan_call_cursor fetch "L_ffffffff810f3100" guarded
    (by rw [pc₁]; exact agree _ _ (by rfl)) .pc tracePc base coverage preempt guardTrace.frame
    rxSection (events ++ [event]) guardTrace.observed guardTrace.last (by
      simp [LookupObservation.edge, pc₁, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro afterPc ⟨pc₂, bx₂, bp₂, trace₂⟩
  have pc₂ : afterPc.machine.pc = Image.PeerGet.entry+0x80 := by rw [pc₂, pc₁]; rfl
  have setup := historySteps_eventually fetch 2 _ _
    (live_wrap_arguments_trace fetch agree base afterPc.machine.data coverage preempt trace₂.frame
      rxSection afterPc.history (events ++ [event]) trace₂.observed (by rw [← pc₂]; exact trace₂.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0x80⟩, afterPc.history⟩ : Executed) = afterPc := by rw [← pc₂]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af₂, machine₃, trace₃⟩
  have pc₃ : afterSetup.machine.pc = Image.PeerGet.entry+0x85 := congrArg MachineState.pc machine₃
  have call := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₃]; exact agree _ _ (by rfl)) .constCmp4 traceCmp base coverage preempt trace₃.frame
    rxSection (events ++ [event]) trace₃.observed trace₃.last (by
      simp [LookupObservation.edge, pc₃, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro final ⟨pc₄, bx₄, bp₄, trace₄⟩
  refine ⟨guarded.machine, by rw [pc₄, pc₃]; rfl, ?_, ?_, guardTrace.frame.memory,
    guardTrace.trans (trace₂.trans (trace₃.trans trace₄))⟩
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bx₂, guardMachine, tested] using bx₄
  · simpa only [machine₃, xorMoved, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bp₂, guardMachine, tested] using bp₄

#print axioms live_negative_stage

/-- The final sign guard and folded live-result decision before return. -/
theorem live_wrap_stage (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base body : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (positive : (body.regs.get (.low .r12 .W32)).msb = false)
    (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x8a⟩) :
    Eventually (historyStep fetch) (fun t => ∃ wrap dead : MachineState,
      t.machine.pc = Image.PeerGet.entry+0x9d ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧ t.machine.data.regs.rbp = body.regs.rbp ∧
      EqualOutside (scanWrites base coverage) base.dmem wrap.data.dmem ∧
      EqualOutside (scanWrites base coverage) base.dmem dead.data.dmem ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
          LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead]) t)
      ⟨⟨body, Image.PeerGet.entry+0x8a⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (wrap_guard_trace fetch agree base body coverage preempt frame positive rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, guardMachine, guardTrace⟩
  have pc₁ : guarded.machine.pc = Image.PeerGet.entry+0x8f := congrArg MachineState.pc guardMachine
  let event := LookupObservation.decision rxSection .refcountAddNzWraps false guarded.machine
  have call := scan_call_cursor fetch "L_ffffffff810f3100" guarded
    (by rw [pc₁]; exact agree _ _ (by rfl)) .pc tracePc base coverage preempt guardTrace.frame
    rxSection (events ++ [event]) guardTrace.observed guardTrace.last (by
      simp [LookupObservation.edge, pc₁, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro afterPc ⟨pc₂, bx₂, bp₂, trace₂⟩
  have pc₂ : afterPc.machine.pc = Image.PeerGet.entry+0x94 := by rw [pc₂, pc₁]; rfl
  have nonzero₂ : afterPc.machine.data.regs.get (.low .rbp .W32) ≠ 0 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bp₂, guardMachine, tested] using nonzero
  have setup := historySteps_eventually fetch 2 _ _
    (live_result_arguments_trace fetch agree base afterPc.machine.data coverage preempt trace₂.frame nonzero₂
      rxSection afterPc.history (events ++ [event]) trace₂.observed (by rw [← pc₂]; exact trace₂.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0x94⟩, afterPc.history⟩ : Executed) = afterPc := by rw [← pc₂]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af₂, machine₃, trace₃⟩
  let dead : MachineState := ⟨afterPc.machine.data.setReg (.low .rsi .W32)
    (afterPc.machine.data.regs.get (.low .rbp .W32)), Image.PeerGet.entry+0x96⟩
  let resultEvent := LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead
  have pc₃ : afterSetup.machine.pc = Image.PeerGet.entry+0x98 := congrArg MachineState.pc machine₃
  have call := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₃]; exact agree _ _ (by rfl)) .constCmp4 traceCmp base coverage preempt trace₃.frame
    rxSection ((events ++ [event]) ++ [resultEvent]) trace₃.observed trace₃.last (by
      simp [LookupObservation.edge, pc₃, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro final ⟨pc₄, bx₄, bp₄, trace₄⟩
  refine ⟨guarded.machine, dead, by rw [pc₄, pc₃]; rfl, ?_, ?_,
    guardTrace.frame.memory, trace₂.frame.memory, ?_⟩
  · simpa only [machine₃, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bx₂, guardMachine, tested] using bx₄
  · simpa only [machine₃, zeroed, MachineData.setReg, Reg64s.set,
      Reg64s.set64, bp₂, guardMachine, tested] using bp₄
  · simpa only [event, resultEvent, List.append_assoc, List.cons_append, List.nil_append] using
      guardTrace.trans (trace₂.trans (trace₃.trans trace₄))

#print axioms live_wrap_stage
end Binary.PeerGet
