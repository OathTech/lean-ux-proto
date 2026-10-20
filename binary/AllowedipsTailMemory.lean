import AllowedipsTailState

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage AllowedipsEntry

theorem Ready.advance {c coverage old ra initial world v before after}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (ready : Ready initial coverage old ra before)
    (stack : after.regs.rsp=before.regs.rsp)
    (calls : CallsReady ⟨coverage,old+512⟩ after)
    (covered : AllowedipsCoverageAt coverage old after.dmem)
    (mapped : (after.dmem.loadInt after.regs.rsp.toBitVec 8).isSome=true)
    (frame : EqualOutside (Writes initial coverage old) before.dmem after.dmem) :
    Ready initial coverage old ra after := by
  refine ⟨stack.trans ready.stack,?_,?_,mapped,calls,covered,?_⟩
  · intro i hi
    exact (frame.loadInt _ 8 (fun j hj => saved_separate pre i hi _ ⟨j,hj,rfl⟩)).symm.trans (ready.saved i hi)
  · exact (frame.loadInt _ 8 (fun j hj => return_separate pre _ ⟨j,hj,rfl⟩)).symm.trans ready.returnWord
  · intro needed
    exact (frame.loadInt _ 2 (fun j hj => pending_separate pre needed _ ⟨j,hj,rfl⟩)).symm.trans (ready.pending needed)

theorem Ready.store_result {c coverage old ra initial world v s t}
    (pre : AllowedipsEntry c coverage old ra initial world v) (ready : Ready initial coverage old ra s)
    (regs : t.regs=s.regs) (memory : t.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt) :
    Ready initial coverage old ra t := by
  have frame : EqualOutside (InRange (slot initial 10) 8) s.dmem t.dmem := by
    rw [memory,ready.result_slot]; exact storeInt_frame _ _ _ _
  have context : (Context.mk coverage (old+512)).At t.dmem := by
    apply state_frame _ _ _ ready.calls.state _ frame
    intro a member written
    exact pre.stackServices a (AllowedipsCoverage.bytes_during coverage old a member)
      (slot_writes initial 10 (by decide) (by decide) a written)
  have covered : AllowedipsCoverageAt coverage old t.dmem := by
    apply coverage_frame ⟨coverage,old⟩ _ _ ready.before _ frame
    intro a member written
    exact pre.stackServices a (AllowedipsCoverage.bytes_before coverage old a member)
      (slot_writes initial 10 (by decide) (by decide) a written)
  have mappedCall : (t.dmem.loadInt (t.regs.rsp.toBitVec-8) 8).isSome=true := by
    rw [memory,regs]
    exact storeInt_defined _ _ _ _ _ _ ready.calls.mapped
  have calls : CallsReady ⟨coverage,old+512⟩ t :=
    ⟨context,by simpa only [regs] using ready.calls.aligned,mappedCall,
     by simpa only [regs] using ready.calls.pushSeparate,
     by simpa only [regs] using ready.calls.returnSeparate,
     ready.calls.metadataSeparate,ready.calls.preemptSeparate⟩
  apply ready.advance pre (by simp only [regs]) calls covered
  · rw [memory,regs]
    exact storeInt_defined _ _ _ _ _ _ ready.mappedResult
  · intro a outside; exact frame a (fun h => outside (.inl h))

theorem callback_before {c coverage old ra initial world v before after}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (covered : AllowedipsCoverageAt coverage old before)
    (next : AllowedipsCoverageAt coverage (old+512) after)
    (frame : EqualOutside (fun a => InRange (slot initial 11) 8 a ∨
      (Context.mk coverage (old+512)).writes a) before after) :
    AllowedipsCoverageAt coverage old after := by
  apply coverage_metadata_frame ⟨coverage,old⟩ before after covered _ frame
  · intro a member written
    rcases written with stack | buffer
    · exact pre.stackServices a (.inl (.inl (AllowedipsCoverage.metadata_before coverage old a member)))
        (slot_writes initial 11 (by decide) (by decide) a stack)
    · exact pre.bufferMetadata a ⟨.inr buffer.1,buffer.2⟩ (AllowedipsCoverage.metadata_before coverage old a member)
  · intro needed
    by_cases active : AllowedipsCoverageNeeded coverage (old+512)
    · exact (next.2.2.2 active).2.2
    · exact Kcov.buffer_frame coverage before after (covered.2.2.2 needed).2.2 _ frame (by
        intro a stored written
        rcases written with stack | buffer
        · exact pre.stackServices a (.inl (.inr ⟨.inl needed,stored⟩))
            (slot_writes initial 11 (by decide) (by decide) a stack)
        · exact active buffer.1)

theorem callback_result_separate {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (a : BitVec 64)
    (read : InRange (slot initial 10) 8 a) :
    ¬(InRange (slot initial 11) 8 a ∨ (Context.mk coverage (old+512)).writes a) := by
  rintro (stack | buffer)
  · exact slot_apart initial 10 11 (by decide) (by decide) (by decide) a read stack
  · exact pre.bufferStack a ⟨.inr buffer.1,buffer.2⟩ (slot_live initial 10 (by decide) a read)

#print axioms Ready.store_result
#print axioms callback_before
end Binary.AllowedipsTail
