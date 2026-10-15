import PeerReturnHistory

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

/-- The saved physical stack supplies all eight actual epilogue steps.
    Every successor remains in the history for later cut correspondence. -/
theorem return_from_saved_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (history : List MachineState)
    (entry : TrustBase.EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (separate : ∀ address, InRange (initial.data.regs.rsp.toBitVec - 48) 56 address →
      ¬writes address) :
    historySteps fetch 8 (fun final =>
      TrustBase.Returned initial final.machine returnAddress ∧
      final.machine.data.regs.rax = body.regs.rbx ∧
      final.machine.data.dmem = body.dmem ∧
      final.history = history ++ restoreStates body initial.data.regs.rbx initial.data.regs.rbp
        initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 returnAddress)
      ⟨⟨body, Image.PeerGet.entry+0xa2⟩, history⟩ := by
  have base : body.regs.rsp.toBitVec = initial.data.regs.rsp.toBitVec - 48 := by
    simp [sp]
  have read (j : Nat) (bound : j ≤ 6) :
      (saveMemory initial.data 7).loadInt
        (body.regs.rsp.toBitVec + .ofNat 64 (8*j)) 8 =
      body.dmem.loadInt (body.regs.rsp.toBitVec + .ofNat 64 (8*j)) 8 := by
    apply frame.loadInt
    intro byte byteBound
    apply separate
    refine ⟨8*j+byte, by omega, ?_⟩
    simp only [base, BitVec.ofNat_add, BitVec.add_assoc]
  have saved (j : Nat) (bound : j < 6) :
      body.dmem.loadInt (body.regs.rsp.toBitVec + .ofNat 64 (8*j)) 8 =
        some (((savedWords initial.data)[5-j]?.getD 0).toNat : Int) := by
    have index : 5-(5-j) = j := by omega
    have pushed := saveMemory_read initial.data 7 (5-j) (by decide) (by omega)
    rw [slot_restore_window initial.data (5-j) (by omega), index, ← base] at pushed
    exact (read j (by omega)).symm.trans pushed
  have original : body.dmem.loadInt (body.regs.rsp.toBitVec + 48) 8 =
      some (returnAddress.toNat : Int) := by
    have framed := read 6 (by decide)
    simp only [Nat.reduceMul] at framed
    have returned := saveMemory_return initial.data 7 (by decide)
    rw [entry.2] at returned
    have address : body.regs.rsp.toBitVec + BitVec.ofNat 64 48 = initial.data.regs.rsp.toBitVec := by
      rw [base]
      exact BitVec.sub_add_cancel _ _
    rw [address] at framed
    simpa only [base, BitVec.sub_add_cancel] using framed.symm.trans returned
  have executed := epilogue_history fetch agree body history
    initial.data.regs.rbx initial.data.regs.rbp initial.data.regs.r12
    initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 returnAddress
    (by simpa [savedWords] using saved 0 (by decide))
    (by simpa [savedWords] using saved 1 (by decide))
    (by simpa [savedWords] using saved 2 (by decide))
    (by simpa [savedWords] using saved 3 (by decide))
    (by simpa [savedWords] using saved 4 (by decide))
    (by simpa [savedWords] using saved 5 (by decide)) original
  apply historySteps_mono fetch 8 _ _ _ _ executed
  rintro final ⟨machine, traced⟩
  rw [machine]
  refine ⟨⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, traced⟩
  change body.regs.rsp + 56 = initial.data.regs.rsp + 8
  rw [sp]
  apply UInt64.toBitVec_inj.mp
  change initial.data.regs.rsp.toBitVec - 48 + 56 = initial.data.regs.rsp.toBitVec + 8
  rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

#print axioms return_from_saved_history
end Binary.PeerGet
