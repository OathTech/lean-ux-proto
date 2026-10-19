import PairInsertSplice

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem unlink_clear_callback (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra shadow original s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .outer shadow s)
    (layout : Layout o) (f : UnlinkFocus n o original)
    (cursor : initial.data.regs.rsi.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev))
    (mapped : (shadow.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x4f ∧
      Core n o c initial ra .outer (write64 shadow (f.removed+o.pprev) 0) t.data)
      ⟨s,codeEntry+0x42⟩ := by
  have run := core.callback fetch (codeEntry+0x42) "L_ffffffff810f31f0" trace (agree _ _ (by rfl)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro t ⟨pc,core,_,_,_,_⟩
  apply at_pc pc
  exact unlink_clear_endpoint fetch agree facts core layout f (by rw [core.owner]; exact cursor) mapped

/-- The complete nonempty unhash segment, including its intervening real
callbacks. Reconstruction is restored after the combined stores. -/
theorem unhash_body (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra original s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .outer original s)
    (layout : Layout o) (f : UnlinkFocus n o original)
    (cursor : initial.data.regs.rsi.toBitVec+8=BitVec.ofNat 64 f.removed)
    (previous : s.regs.rbx.toBitVec=BitVec.ofNat 64 f.previous) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x4f ∧
      Core n o c initial ra .outer (unlinkMemory original o f.removed f.previous f.next) t.data)
      ⟨s,codeEntry+0x28⟩ := by
  have clearCursor : initial.data.regs.rsi.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev) := by
    rw [show (16 : BitVec 64)=8+8 from rfl,←BitVec.add_assoc,cursor,layout.pprev,BitVec.ofNat_add]
    rfl
  have mappedOriginal : (original.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true := by
    rw [word_loadInt _ _ _ _ _ f.fields.back]
    rfl
  have mappedFirst : ((write64 original f.previous f.next).loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true :=
    storeInt_defined _ _ _ _ _ _ mappedOriginal
  have first := core.callback fetch (codeEntry+0x28) "L_ffffffff810f31f0" trace (agree _ _ (by rfl)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro called ⟨pc,core,bx0,_,_,_⟩
  have splice := unlink_predecessor fetch agree facts core layout f (by rw [core.owner]; exact cursor)
    (by rw [bx0]; exact previous)
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc splice)
  rintro linked ⟨pc,core,bx,next⟩
  by_cases zero : f.next=0
  · rw [ite_eq_left zero] at pc
    have tail := unlink_clear_callback fetch agree trace facts core layout f clearCursor mappedFirst
    simpa only [unlinkMemory,zero,↓reduceIte] using at_pc pc tail
  · rw [ite_eq_right zero] at pc
    have callback := core.callback fetch (codeEntry+0x39) "L_ffffffff810f31f0" trace (agree _ _ (by rfl)) facts
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc callback)
    rintro called ⟨pc,core,bx',next',_,_⟩
    obtain ⟨entry,tail,fields⟩ := f.nextFields zero
    have mappedNext : ((write64 original f.previous f.next).loadInt (.ofNat 64 (f.next+o.pprev)) 8).isSome=true := by
      apply storeInt_defined
      rw [word_loadInt _ _ _ _ _ fields.back]
      rfl
    have repair := unlink_successor_endpoint fetch agree facts core layout f zero
      (by rw [next',next]; rfl) (by rw [bx',bx,bx0]; exact previous) mappedNext
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc repair)
    rintro repaired ⟨pc,core,_⟩
    have mappedSecond : ((write64 (write64 original f.previous f.next) (f.next+o.pprev) f.previous).loadInt
        (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true := storeInt_defined _ _ _ _ _ _ mappedFirst
    have tail := unlink_clear_callback fetch agree trace facts core layout f clearCursor mappedSecond
    simpa only [unlinkMemory,zero,↓reduceIte] using at_pc pc tail

#print axioms unlink_clear_callback
#print axioms unhash_body
end Binary.Pair.Insert
