import WordAlignment
import AllowedipsTailExecution

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage AllowedipsEntry

/-- Exact frame needed from the search and selected helper: their scratch is
below outer RSP, their callbacks use the BH-disabled phase, and only the
selected count can change. This is an intermediate proof frame, not Pre. -/
def MiddleWrites (c : AllowedipsRelation.Config) (v : AllowedipsRelation.View)
    (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32) (a : BitVec 64) : Prop :=
  InRange (initial.data.regs.rsp.toBitVec-144) 64 a ∨
    (Context.mk coverage (old+512)).writes a ∨ AllowedipsCountWrites c v a

theorem upper_apart_scratch (initial : MachineState) (n : Nat) (bound : n≤10)
    (a : BitVec 64) (inside : InRange (slot initial n) 8 a) :
    ¬InRange (initial.data.regs.rsp.toBitVec-144) 64 a := by
  rw [slot_window initial n (by omega)] at inside
  have apart := InRange.offset_disjoint (initial.data.regs.rsp.toBitVec-144)
    (144-n*8) 8 0 64 (by omega) (by decide) (by omega) a inside
  simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using apart

theorem upper_separate {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (n : Nat) (bound : n≤10) (a : BitVec 64) (read : InRange (slot initial n) 8 a) :
    ¬MiddleWrites c v initial coverage old a := by
  rintro (scratch | buffer | count)
  · exact upper_apart_scratch initial n bound a read scratch
  · exact pre.bufferStack a ⟨.inr buffer.1,buffer.2⟩ (slot_live initial n (by omega) a read)
  · exact pre.countStack a count (slot_live initial n (by omega) a read)

theorem middle_service_separate {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (a : BitVec 64) (read : AllowedipsMetadata coverage old a) :
    ¬MiddleWrites c v initial coverage old a := by
  rintro (scratch | buffer | count)
  · obtain ⟨i,hi,eq⟩ := scratch
    exact pre.stackServices a (.inl (.inl read)) ⟨i,by omega,eq⟩
  · exact pre.bufferMetadata a ⟨.inr buffer.1,buffer.2⟩ read
  · exact pre.countServices a count (.inl (.inl read))

/-- Tail readiness follows from actual entry postconditions and the proved
middle write footprint. Only the overwritten call word needs its physical
mapping supplied by the executed loop/helper; all other reads are framed. -/
theorem Ready.of_middle_frame {c coverage old ra initial world v entry current}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (entryPost : AllowedipsEntry.Post c initial coverage old ra entry)
    (stack : current.regs.rsp=initial.data.regs.rsp-80)
    (state : (Context.mk coverage (old+512)).At current.dmem)
    (mappedCall : (current.dmem.loadInt (current.regs.rsp.toBitVec-8) 8).isSome=true)
    (frame : EqualOutside (MiddleWrites c v initial coverage old) entry.data.dmem current.dmem) :
    Ready initial coverage old ra current := by
  have resultSlot : current.regs.rsp.toBitVec=slot initial 10 := by rw [stack]; rfl
  have callSlot : current.regs.rsp.toBitVec-8=slot initial 11 := by
    rw [stack,UInt64.toBitVec_sub]
    change (initial.data.regs.rsp.toBitVec-80)-8=initial.data.regs.rsp.toBitVec-88
    rw [BitVec.sub_sub]; rfl
  have before : AllowedipsCoverageAt coverage old current.dmem := by
    apply coverage_metadata_frame ⟨coverage,old⟩ _ _ entryPost.before _ frame
    · intro a read
      exact middle_service_separate pre a (AllowedipsCoverage.metadata_before coverage old a read)
    · intro needed
      by_cases active : AllowedipsCoverageNeeded coverage (old+512)
      · exact (state.1.2.2.2 active).2.2
      · exact Kcov.buffer_frame coverage _ _ (entryPost.before.2.2.2 needed).2.2 _ frame (by
          intro a stored written
          rcases written with scratch | buffer | count
          · obtain ⟨i,hi,eq⟩ := scratch
            exact pre.stackServices a (.inl (.inr ⟨.inl needed,stored⟩)) ⟨i,by omega,eq⟩
          · exact active buffer.1
          · exact pre.countServices a count (.inl (.inr ⟨.inl needed,stored⟩)))
  have calls : CallsReady ⟨coverage,old+512⟩ current := by
    refine ⟨state,?_,mappedCall,?_,?_,?_,?_⟩
    · rw [stack]
      exact aligned_sub _ 80 pre.entry.1 (by decide)
    · intro a read written
      rw [callSlot] at written
      exact pre.stackServices a (AllowedipsCoverage.bytes_during coverage old a read)
        (slot_writes initial 11 (by decide) (by decide) a written)
    · intro a written read
      rw [callSlot] at read
      exact pre.bufferStack a ⟨.inr written.1,written.2⟩ (slot_live initial 11 (by decide) a read)
    · intro a written read
      exact pre.bufferMetadata a ⟨.inr written.1,written.2⟩ (AllowedipsCoverage.metadata_during coverage old a read)
    · intro a written read
      exact pre.bufferPreempt a ⟨.inr written.1,written.2⟩ read
  refine ⟨stack,?_,?_,?_,calls,before,?_⟩
  · intro i hi
    have same := frame.loadInt (Allowedips.entrySlot initial.data i) 8 (by
      intro j hj
      apply upper_separate pre (i+1) (by omega)
      rw [saved_slot initial i (by omega),ite_eq_left hi]
      exact ⟨j,hj,rfl⟩)
    exact same.symm.trans (entryPost.saved i (by omega))
  · have same := frame.loadInt initial.data.regs.rsp.toBitVec 8 (by
      intro j hj
      apply upper_separate pre 0 (by decide)
      simpa only [slot,Nat.zero_mul,BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using (show InRange initial.data.regs.rsp.toBitVec 8 (initial.data.regs.rsp.toBitVec+.ofNat 64 j) from ⟨j,hj,rfl⟩))
    exact same.symm.trans entryPost.returnWord
  · rw [resultSlot]
    have same := frame.loadInt (slot initial 10) 8 (fun j hj => upper_separate pre 10 (by decide) _ ⟨j,hj,rfl⟩)
    rw [←same]
    exact entryPost.mapped 9 (by decide)
  · intro needed
    have same := frame.loadInt softirqPendingAddress 2 (fun j hj =>
      middle_service_separate pre _ (.inr (.inr (.inr (.inr ⟨needed,j,hj,rfl⟩)))))
    exact same.symm.trans (entryPost.pending pre needed)

#print axioms Ready.of_middle_frame
end Binary.AllowedipsTail
