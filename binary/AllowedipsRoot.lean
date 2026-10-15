import AllowedipsOuterGuards
import AllowedipsOuterScalar
import AllowedipsLoopCalls

namespace Binary.AllowedipsOuter
open TrustBase AllowedipsLoop LookupObservation
local instance : Labels := Image.linkedLabels

/-- Initial root TEST, including the compiler-merged empty-root/found-false
exit. A non-null root executes the callback and clears the candidate before
entering the trie loop. Every decision carries its actual guard successor. -/
theorem root_branch (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x7e⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.data.regs.rbx = s.regs.rbx ∧
      (if s.regs.get (.low .rbx .W64) == 0 then t.machine.pc = AllowedipsImage.Lookup.entry+0x184
        else t.machine.pc = AllowedipsImage.Lookup.entry+0xd5 ∧ t.machine.data.regs.rbp = 0) ∧
      ∃ guard, Trace base coverage rxSection history
        (events ++ rootPoints rxSection (s.regs.get (.low .rbx .W64) == 0) guard) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x7e⟩,history⟩ := by
  have first := historySteps_eventually fetch 2 _ _
    (root_guard fetch agree base s coverage frame rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro guard ⟨pc,regs,trace⟩
  cases zero : s.regs.get (.low .rbx .W64) == 0 with
  | true =>
    apply Eventually.done
    refine ⟨by rw [regs],?_,guard.machine,by simpa only [zero] using trace⟩
    exact pc.trans (ite_eq_left zero)
  | false =>
    have pc87 : guard.machine.pc = AllowedipsImage.Lookup.entry+0x87 := by
      exact pc.trans (ite_eq_right (by rw [zero]; decide))
    have called := AllowedipsLoop.call fetch (AllowedipsImage.Lookup.entry+0x87) "L_ffffffff810f3100"
      (agree _ _ (by rfl)) .pc contract base guard.machine.data coverage trace.frame rxSection
      guard.history (events ++ rootPoints rxSection (s.regs.get (.low .rbx .W64) == 0) guard.machine)
      trace.observed (by simpa only [←pc87] using trace.last)
      (by unfold Quiet; decide) (by decide)
    have cursor : (⟨⟨guard.machine.data,AllowedipsImage.Lookup.entry+0x87⟩,guard.history⟩ : Executed) = guard := by
      rw [←pc87]
    rw [cursor] at called
    apply eventually_trans (historyStep fetch) _ _ _ called
    rintro afterCall ⟨pc8c,bx,bp,r14,r15,callTrace⟩
    change afterCall.machine.pc = AllowedipsImage.Lookup.entry+0x8c at pc8c
    have composed := trace.trans callTrace
    have cleared := clear_found fetch agree base afterCall.machine.data coverage callTrace.frame rxSection
      afterCall.history _ callTrace.observed (by simpa only [←pc8c] using callTrace.last)
    have cursor : (⟨⟨afterCall.machine.data,AllowedipsImage.Lookup.entry+0x8c⟩,afterCall.history⟩ : Executed) = afterCall := by
      rw [←pc8c]
    rw [cursor] at cleared
    apply eventually_weaken (historyStep fetch) _ _ _ _ cleared
    rintro final ⟨⟨pcd5,registers⟩,clearTrace⟩
    refine ⟨?_,?_,guard.machine,by simpa only [zero] using composed.trans clearTrace⟩
    · rw [registers]
      exact bx.trans (by rw [regs])
    · exact ⟨pcd5,by rw [registers]⟩


/-- The initial callback and saved-root load establish the loop cursor from
physical memory. Empty roots take the same compiled merged exit as the mirror. -/
theorem root_start (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context) (value : BitVec 64)
    (root : base.dmem.loadInt (base.regs.rsp.toBitVec+8) 8 = some value.toNat)
    (apart : ∀ a, InRange (base.regs.rsp.toBitVec+8) 8 a → ¬writes base.regs.rsp coverage a)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x74⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.data.regs.rbx = .ofBitVec value ∧
      (if value == 0 then t.machine.pc = AllowedipsImage.Lookup.entry+0x184
        else t.machine.pc = AllowedipsImage.Lookup.entry+0xd5 ∧ t.machine.data.regs.rbp = 0) ∧
      ∃ guard, Trace base coverage rxSection history
        (events ++ rootPoints rxSection (value == 0) guard) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x74⟩,history⟩ := by
  have called := AllowedipsLoop.call fetch (AllowedipsImage.Lookup.entry+0x74) "L_ffffffff810f3100"
    (agree _ _ (by rfl)) .pc contract base s coverage frame rxSection history events observed last
    (by unfold Quiet; decide) (by decide)
  apply eventually_trans (historyStep fetch) _ _ _ called
  rintro afterCall ⟨pc79,bx,bp,r14,r15,callTrace⟩
  change afterCall.machine.pc = AllowedipsImage.Lookup.entry+0x79 at pc79
  have field : afterCall.machine.data.dmem.loadInt (afterCall.machine.data.regs.rsp.toBitVec+8) 8 = some value.toNat := by
    rw [callTrace.frame.stack]
    exact (callTrace.frame.memory.loadInt _ 8 (fun i hi => apart _ ⟨i,hi,rfl⟩)).symm.trans root
  have loaded := root_load fetch agree base afterCall.machine.data coverage value field callTrace.frame
    rxSection afterCall.history events callTrace.observed (by simpa only [←pc79] using callTrace.last)
  have cursor : (⟨⟨afterCall.machine.data,AllowedipsImage.Lookup.entry+0x79⟩,afterCall.history⟩ : Executed) = afterCall := by rw [←pc79]
  rw [cursor] at loaded
  apply eventually_trans (historyStep fetch) _ _ _ loaded
  rintro afterLoad ⟨⟨pc7e,registers⟩,loadTrace⟩
  have branched := root_branch fetch agree contract base afterLoad.machine.data coverage loadTrace.frame
    rxSection afterLoad.history events loadTrace.observed (by simpa only [←pc7e] using loadTrace.last)
  have cursor : (⟨⟨afterLoad.machine.data,AllowedipsImage.Lookup.entry+0x7e⟩,afterLoad.history⟩ : Executed) = afterLoad := by rw [←pc7e]
  rw [cursor] at branched
  apply eventually_weaken (historyStep fetch) _ _ _ _ branched
  rintro final ⟨bx,pc,guard,branchTrace⟩
  have query : afterLoad.machine.data.regs.get (.low .rbx .W64) = value := by
    rw [registers]
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  refine ⟨bx.trans (by rw [registers]),?_,guard,?_⟩
  · simpa only [query] using pc
  · simpa only [query] using (callTrace.trans loadTrace).trans branchTrace

#print axioms root_start

#print axioms root_branch
end Binary.AllowedipsOuter
