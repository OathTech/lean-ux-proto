import PairRemoveSplice

namespace Binary.Pair.Remove
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem clear_callback (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra shadow original s}
    (facts : CallFacts n o c initial ra 4) (core : Core c initial ra true shadow s)
    (layout : Layout o) (f : UnlinkFocus n o original)
    (cursor : initial.data.regs.rsi.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev))
    (mapped : (shadow.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x48 ∧
      Core c initial ra true (write64 shadow (f.removed+o.pprev) 0) t.data)
      ⟨s,codeEntry+0x3b⟩ := by
  have run := core.callback fetch (codeEntry+0x3b) "L_ffffffff810f31f0" trace (agree _ _ (by rfl)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro t ⟨pc,core,_,_⟩
  apply at_pc pc
  exact clear fetch agree facts core layout f (by rw [core.owner]; exact cursor) mapped

/-- All real unlink stores and intervening callbacks, over one shadow heap.
Reconstruction is restored by the combined effect, not between its stores. -/
theorem body (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra original s}
    (facts : CallFacts n o c initial ra 4) (core : Core c initial ra true original s)
    (layout : Layout o) (f : UnlinkFocus n o original)
    (cursor : initial.data.regs.rsi.toBitVec+8=BitVec.ofNat 64 f.removed)
    (previous : s.regs.rbp.toBitVec=BitVec.ofNat 64 f.previous) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x48 ∧
      Core c initial ra true (unlinkMemory original o f.removed f.previous f.next) t.data)
      ⟨s,codeEntry+0x1f⟩ := by
  have clearCursor : initial.data.regs.rsi.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev) := by
    rw [show (16 : BitVec 64)=8+8 from rfl,←BitVec.add_assoc,cursor,layout.pprev,BitVec.ofNat_add]
    rfl
  have mappedOriginal : (original.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true := by
    rw [word_loadInt _ _ _ _ _ f.fields.back]
    rfl
  have mappedFirst : ((write64 original f.previous f.next).loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true :=
    storeInt_defined _ _ _ _ _ _ mappedOriginal
  have first := core.callback fetch (codeEntry+0x1f) "L_ffffffff810f31f0" trace (agree _ _ (by rfl)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro called ⟨pc,core,bp0,_⟩
  have splice := predecessor fetch agree facts core layout f (by rw [core.owner]; exact cursor)
    (by rw [bp0]; exact previous)
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc splice)
  rintro linked ⟨pc,core,bp,next⟩
  by_cases zero : f.next=0
  · rw [ite_eq_left zero] at pc
    have tail := clear_callback fetch agree trace facts core layout f clearCursor mappedFirst
    simpa only [unlinkMemory,zero,↓reduceIte] using at_pc pc tail
  · rw [ite_eq_right zero] at pc
    have callback := core.callback fetch (codeEntry+0x31) "L_ffffffff810f31f0" trace (agree _ _ (by rfl)) facts
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc callback)
    rintro called ⟨pc,core,bp',next'⟩
    obtain ⟨entry,tail,fields⟩ := f.nextFields zero
    have mappedNext : ((write64 original f.previous f.next).loadInt (.ofNat 64 (f.next+o.pprev)) 8).isSome=true := by
      apply storeInt_defined
      rw [word_loadInt _ _ _ _ _ fields.back]
      rfl
    have repair := successor fetch agree facts core layout f zero
      (by rw [next',next]; rfl) (by rw [bp',bp,bp0]; exact previous) mappedNext
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc repair)
    rintro repaired ⟨pc,core,_⟩
    have mappedSecond : ((write64 (write64 original f.previous f.next) (f.next+o.pprev) f.previous).loadInt
        (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true := storeInt_defined _ _ _ _ _ _ mappedFirst
    have tail := clear_callback fetch agree trace facts core layout f clearCursor mappedSecond
    simpa only [unlinkMemory,zero,↓reduceIte] using at_pc pc tail

#print axioms clear_callback
#print axioms body
end Binary.Pair.Remove
