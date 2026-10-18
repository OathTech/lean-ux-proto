import PairInsertPrependStores

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem prepend_repair (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra original s} (facts : FrameFacts n o c initial ra) (layout : Layout o)
    (focus : InsertFocus n o original) (nonzero : Index.head focus.nodes≠0)
    (core : Core n o c initial ra .inner (prefixMemory focus) s)
    (link : s.regs.r13.toBitVec=BitVec.ofNat 64 focus.fresh.link)
    (first : s.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head focus.nodes)) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x15b ∧
      Core n o c initial ra .inner focus.after t.data) ⟨s,codeEntry+0x157⟩ := by
  obtain ⟨entry,next,fields⟩ := focus.firstFields nonzero
  have slot := fields.backSlot layout
  have originalMapped : (original.loadInt (.ofNat 64 (Index.head focus.nodes+o.pprev)) 8).isSome=true := by
    rw [word_loadInt _ _ _ _ _ fields.back]
    rfl
  have mapped : ((prefixMemory focus).loadInt (.ofNat 64 (Index.head focus.nodes+o.pprev)) 8).isSome=true :=
    storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ originalMapped))
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have address : s.regs.rbx.toBitVec+8=BitVec.ofNat 64 (Index.head focus.nodes+o.pprev) := by
    rw [first,layout.pprev,BitVec.ofNat_add]
    rfl
  have current : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some old := by
    rw [address,←core.frame.loadInt _ _ (slot.heap layout),read]
  have run := region_eventually (IndexInsertImage.Insert_r157_layout.agreement decoder) s _ (prepend_successor s old current)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨regs,heap,pc⟩
  have memory : t.data.dmem=write64 s.dmem (Index.head focus.nodes+o.pprev) focus.fresh.link := by
    simpa only [address,link,write64] using heap
  have stored := (core.store64 facts layout slot focus.fresh.link).same regs memory
  refine ⟨pc,?_⟩
  have after : focus.after=write64 (prefixMemory focus) (Index.head focus.nodes+o.pprev) focus.fresh.link := by
    simp [InsertFocus.after,insertMemory,insertionStores,nonzero,write64s,layout.next,prefixMemory]
  rw [after]
  exact stored

/-- The full prepend, with the optional old-head back-pointer repair and
its real callbacks. The combined heap is the tested insertion-store plan. -/
theorem prepend (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .inner shadow s) (layout : Layout o)
    (focus : InsertFocus n o shadow) (resident : Resident n o shadow focus.fresh.owner focus.fresh.base)
    (table : initial.data.regs.rdi.toNat=n.table) (owner : initial.data.regs.rsi.toNat=focus.fresh.base)
    (registers : WalkRegisters true focus.index s) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x160 ∧
      Core n o c initial ra .inner focus.after t.data) ⟨s,codeEntry+0x136⟩ := by
  have setup := prepend_setup_endpoint fetch decoder core layout focus table owner registers
  apply eventually_trans (instructionStep fetch) _ _ _ setup
  rintro prepared ⟨pc,core,registers⟩
  have stores := prepend_stores fetch decoder facts core layout focus resident owner registers
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc stores)
  rintro stored ⟨pc,core,registers⟩
  have finish : ∀ t : MachineState, t.pc=codeEntry+0x15b → Core n o c initial ra .inner focus.after t.data →
      Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x160 ∧
        Core n o c initial ra .inner focus.after t.data) t := by
    intro t pc core
    have call := core.callback fetch (codeEntry+0x15b) "L_ffffffff810f3100" trace (decoder _ _ (by rfl)) facts
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc call)
    rintro final ⟨pc,core,_,_,_,_⟩
    exact ⟨pc,core⟩
  by_cases zero : Index.head focus.nodes=0
  · have atEnd : stored.pc=codeEntry+0x15b := by simpa only [zero,show BitVec.ofNat 64 0=(0 : BitVec 64) from rfl,↓reduceIte] using pc
    apply finish stored atEnd
    simpa only [InsertFocus.after,insertMemory,insertionStores,zero,↓reduceIte,List.append_nil,write64s,prefixMemory] using core
  · have notZero : BitVec.ofNat 64 (Index.head focus.nodes)≠0 := by
      intro equal
      apply zero
      have equal := congrArg BitVec.toNat equal
      change Index.head focus.nodes%2^64=0 at equal
      simpa only [Nat.mod_eq_of_lt (word_bound focus.headRead)] using equal
    have atVisit : stored.pc=codeEntry+0x152 := by simpa only [ite_eq_right notZero] using pc
    have call := core.callback fetch (codeEntry+0x152) "L_ffffffff810f3100" trace (decoder _ _ (by rfl)) facts
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc atVisit call)
    rintro called ⟨pc,core,bx,r13,_,_⟩
    have repair := prepend_repair fetch decoder facts layout focus zero core
      (by rw [r13]; exact registers.link) (by rw [bx]; exact registers.first)
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc repair)
    rintro repaired ⟨pc,core⟩
    exact finish repaired pc core

#print axioms prepend_repair
#print axioms prepend
end Binary.Pair.Insert
