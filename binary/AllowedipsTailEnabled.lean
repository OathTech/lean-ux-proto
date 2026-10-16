import AllowedipsTailBhTrace

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage CommonBits AllowedipsEntry
local instance : Labels := Image.linkedLabels

structure Enabled (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra result : UInt64) (s : MachineData) : Prop where
  stack : s.regs.rsp=initial.data.regs.rsp-80
  saved : ∀ i<6, s.dmem.loadInt (Allowedips.entrySlot initial.data i) 8 =
    some (((Allowedips.entryWords initial.data)[i]?.getD 0).toNat : Int)
  returnWord : s.dmem.loadInt initial.data.regs.rsp.toBitVec 8=some ra.toNat
  value : s.dmem.loadInt s.regs.rsp.toBitVec 8=some result.toNat
  before : AllowedipsCoverageAt coverage old s.dmem
  during : AllowedipsCoverageAt coverage (old+512) s.dmem
  preempt : s.dmem.loadInt preemptCountAddress 4=some old.toNat
  pending : LookupPendingRead old → s.dmem.loadInt softirqPendingAddress 2=some 0

theorem enable (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsBhEnableContract fetch)
    {c coverage old ra initial world v result}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (stored : Stored initial coverage old ra result s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x13c ∧ Enabled initial coverage old ra result t.machine.data) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x12b⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x12b⟩,[⟨s,AllowedipsImage.Lookup.entry+0x12b⟩]⟩ := by
  apply eventually_weaken (historyStep fetch) _ _ _ _ (bh_trace fetch agree contract pre s stored.ready rx)
  rintro t ⟨⟨pc,sp,count⟩,trace⟩
  have frame : EqualOutside (fun a => InRange (slot initial 11) 8 a ∨ InRange preemptCountAddress 4 a)
      s.dmem t.machine.data.dmem := by simpa only [stored.ready.call_slot] using trace.frame
  have localTrace := trace.mono (large := Writes initial coverage old) (fun a written => by
    rcases written with stack | preempt
    · exact .inr (.inl (by simpa only [stored.ready.call_slot] using stack))
    · exact .inr (.inr (.inr preempt)))
  have oldCoverage : AllowedipsCoverageAt coverage old t.machine.data.dmem := by
    apply coverage_metadata_frame ⟨coverage,old⟩ _ _ stored.ready.before _ frame
    · intro a member written
      have metadata := AllowedipsCoverage.metadata_before coverage old a member
      rcases written with stack | preempt
      · exact pre.stackServices a (.inl (.inl metadata)) (slot_writes initial 11 (by decide) (by decide) a stack)
      · exact pre.preemptServices a (.inl metadata) preempt
    · intro needed
      exact Kcov.buffer_frame coverage _ _ (stored.ready.before.2.2.2 needed).2.2 _ frame (by
        intro a read written
        rcases written with stack | preempt
        · exact pre.stackServices a (.inl (.inr ⟨.inl needed,read⟩)) (slot_writes initial 11 (by decide) (by decide) a stack)
        · exact pre.preemptServices a (.inr ⟨.inl needed,read⟩) preempt)
  have currentCoverage : AllowedipsCoverageAt coverage (old+512) t.machine.data.dmem := by
    apply coverage_metadata_frame ⟨coverage,old+512⟩ _ _ stored.ready.calls.state.1 _ frame
    · intro a member written
      have metadata := AllowedipsCoverage.metadata_during coverage old a member
      rcases written with stack | preempt
      · exact pre.stackServices a (.inl (.inl metadata)) (slot_writes initial 11 (by decide) (by decide) a stack)
      · exact pre.preemptServices a (.inl metadata) preempt
    · intro needed
      exact Kcov.buffer_frame coverage _ _ (stored.ready.calls.state.1.2.2.2 needed).2.2 _ frame (by
        intro a read written
        rcases written with stack | preempt
        · exact pre.stackServices a (.inl (.inr ⟨.inr needed,read⟩)) (slot_writes initial 11 (by decide) (by decide) a stack)
        · exact pre.preemptServices a (.inr ⟨.inr needed,read⟩) preempt)
  refine ⟨⟨pc,sp.trans stored.ready.stack,?_,?_,?_,oldCoverage,currentCoverage,count,?_⟩,localTrace⟩
  · intro i hi
    exact (localTrace.frame.loadInt _ 8 (fun j hj => saved_separate pre i hi _ ⟨j,hj,rfl⟩)).symm.trans (stored.ready.saved i hi)
  · exact (localTrace.frame.loadInt _ 8 (fun j hj => return_separate pre _ ⟨j,hj,rfl⟩)).symm.trans stored.ready.returnWord
  · rw [sp,stored.ready.result_slot]
    apply Eq.trans _ (show s.dmem.loadInt (slot initial 10) 8=some result.toNat from by simpa only [stored.ready.result_slot] using stored.value)
    apply Eq.symm
    apply frame.loadInt
    intro i hi written
    rcases written with stack | preempt
    · exact slot_apart initial 10 11 (by decide) (by decide) (by decide) _ ⟨i,hi,rfl⟩ stack
    · exact pre.preemptStack _ (slot_live initial 10 (by decide) _ ⟨i,hi,rfl⟩) preempt
  · intro needed
    exact (localTrace.frame.loadInt _ 2 (fun j hj => pending_separate pre needed _ ⟨j,hj,rfl⟩)).symm.trans (stored.ready.pending needed)

#print axioms enable
end Binary.AllowedipsTail
