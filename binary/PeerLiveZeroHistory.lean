import PeerIncrementFinishHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- The nonzero guard and its real PC callback preserve the count address
    and frame memory outside callback writes, before any increment. The
    enclosing caller must separate the count word from those writes.
    Comparison operands are actual EBP. -/
theorem live_zero_call_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (body : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body) (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    Eventually (historyStep fetch) (fun t => ∃ af,
      t.machine.pc = Image.PeerGet.entry+0x44 ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧ t.machine.data.regs.rbp = body.regs.rbp ∧
      ScanTrace body coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzZero false
          ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x3f⟩
          (some ((body.regs.get (.low .rbp .W32)).toNat, 0))]) t)
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (nonzero_guard_trace fetch agree body body coverage preempt (ScanFrame.initial body coverage preempt ready)
      nonzero rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, machine, trace⟩
  have pc : guarded.machine.pc = Image.PeerGet.entry+0x3f := congrArg MachineState.pc machine
  have call := scan_call_cursor fetch "L_ffffffff810f3100" guarded
    (by rw [pc]; exact agree _ _ (by rfl)) .pc tracePc body coverage preempt trace.frame
    rxSection _ trace.observed trace.last (by
      simp [LookupObservation.edge, pc, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro t ⟨pc₂, bx₂, bp₂, trace₂⟩
  refine ⟨af, by rw [pc₂, pc]; rfl, ?_, ?_, ?_⟩
  · simpa only [machine, tested] using bx₂
  · simpa only [machine, tested] using bp₂
  · simpa only [machine] using trace.trans trace₂

#print axioms live_zero_call_history
end Binary.PeerGet
