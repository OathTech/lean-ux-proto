import PairReplaceFirstPrefix
import PairReplacePrefixMemory
import PairReplaceFirstSuffix

namespace Binary.Pair.Replace.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem prefix_mapped (m : DataMem) (o : Offsets) (new previous next index : Nat)
    (address : BitVec 64) (width : Nat) (mapped : (m.loadInt address width).isSome=true) :
    ((replacePrefixMemory m o new previous next index).loadInt address width).isSome=true := by
  apply storeInt_defined
  apply storeInt_defined
  apply storeInt_defined
  exact storeInt_defined _ _ _ _ _ _ mapped

theorem clear_callback (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    (trace : GuardedPc fetch) {n o c initial ra shadow original result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra true shadow result s)
    (layout : Layout o) (f : UnlinkFocus n o original)
    (nextAddress : initial.data.regs.rsi.toBitVec+8=BitVec.ofNat 64 (f.removed+o.next))
    (backAddress : initial.data.regs.rsi.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev))
    (mappedNext : (shadow.loadInt (.ofNat 64 (f.removed+o.next)) 8).isSome=true)
    (mappedBack : (shadow.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x81 ∧
      Core c initial ra true
        (write64 (write64 (write64 shadow (f.removed+o.next) 0) (f.removed+o.pprev) 0xdead000000000122)
          (f.removed+o.pprev) 0) result t.data) ⟨s,codeEntry+0x5e⟩ := by
  have call := core_callback fetch (codeEntry+0x5e) "L_ffffffff810f3100" trace (agree _ _ (by rfl)) facts core
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ call
  rintro t ⟨pc,core,_,_⟩
  exact Callback.at_pc pc (clear fetch agree facts core layout f
    (by rw [core.owner]; exact nextAddress) (by rw [core.owner]; exact backAddress) mappedNext mappedBack)

/-- The complete successful mutation, with callbacks interspersed in the
actual instruction order. Only the endpoint restores source reconstruction. -/
theorem body (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    (trace : GuardedPc fetch) {n o c initial ra original result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra true original result s)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) (f : ReplaceFocus n o original)
    (oldBase : initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 (f.old.removed-o.hash))
    (newBase : initial.data.regs.rdx.toBitVec=BitVec.ofNat 64 f.base)
    (mappedNext : (original.loadInt (.ofNat 64 (f.base+8)) 8).isSome=true)
    (mappedIndex : (original.loadInt (.ofNat 64 (f.base+28)) 4).isSome=true) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x81 ∧
      Core c initial ra true f.after result t.data) ⟨s,codeEntry+0x26⟩ := by
  have layout := (validate_basic validated).1
  have nextAddress : initial.data.regs.rsi.toBitVec+8=BitVec.ofNat 64 (f.old.removed+o.next) := by
    rw [oldBase]
    change BitVec.ofNat 64 (f.old.removed-o.hash)+BitVec.ofNat 64 8=_
    rw [←BitVec.ofNat_add]
    congr 1
    have valid := f.old.fields.valid
    rw [layout.hash,layout.next] at *
    omega
  have backAddress : initial.data.regs.rsi.toBitVec+16=BitVec.ofNat 64 (f.old.removed+o.pprev) := by
    rw [oldBase]
    change BitVec.ofNat 64 (f.old.removed-o.hash)+BitVec.ofNat 64 16=_
    rw [←BitVec.ofNat_add]
    congr 1
    have valid := f.old.fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  let first := replacePrefixMemory original o f.link f.old.previous f.old.next f.old.entry.index
  have oldNext : (first.loadInt (.ofNat 64 (f.old.removed+o.next)) 8).isSome=true := by
    apply prefix_mapped
    rw [word_loadInt _ _ _ _ _ f.old.fields.forward]
    rfl
  have oldBack : (first.loadInt (.ofNat 64 (f.old.removed+o.pprev)) 8).isSome=true := by
    apply prefix_mapped
    rw [word_loadInt _ _ _ _ _ f.old.fields.back]
    rfl
  have call := core_callback fetch (codeEntry+0x26) "L_ffffffff810f3100" trace (agree _ _ (by rfl)) facts core
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ call
  rintro called ⟨pc,core,_,_⟩
  have spliceRun := splice fetch agree facts core layout storage f
    (by rw [core.owner]; exact oldBase) (by rw [core.new]; exact newBase) mappedNext mappedIndex
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ (Callback.at_pc pc spliceRun)
  rintro linked ⟨pc,core,link⟩
  by_cases zero : f.old.next=0
  · rw [ite_eq_left zero] at pc
    have tail := clear_callback fetch agree trace facts core layout f.old nextAddress backAddress oldNext oldBack
    simpa only [ReplaceFocus.after,replaceMemory_split,zero,↓reduceIte] using Callback.at_pc pc tail
  · rw [ite_eq_right zero] at pc
    have callback := core_callback fetch (codeEntry+0x51) "L_ffffffff810f3100" trace (agree _ _ (by rfl)) facts core
    apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ (Callback.at_pc pc callback)
    rintro called ⟨pc,core,_,linkKept⟩
    obtain ⟨entry,next,fields⟩ := f.old.nextFields zero
    have successorMapped : (first.loadInt (.ofNat 64 (f.old.next+o.pprev)) 8).isSome=true := by
      apply prefix_mapped
      rw [word_loadInt _ _ _ _ _ fields.back]
      rfl
    have repaired := successor fetch agree facts core layout f zero
      (by rw [core.new]; exact newBase) (by rw [linkKept,link,layout.next]; rfl)
      (f.prefix_next validated storage "new.next") successorMapped
    apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ (Callback.at_pc pc repaired)
    rintro repaired ⟨pc,core⟩
    have tail := clear_callback fetch agree trace facts core layout f.old nextAddress backAddress
      (storeInt_defined _ _ _ _ _ _ oldNext) (storeInt_defined _ _ _ _ _ _ oldBack)
    simpa only [ReplaceFocus.after,replaceMemory_split,zero,↓reduceIte] using Callback.at_pc pc tail

#print axioms body
end Binary.Pair.Replace.First
