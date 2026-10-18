import PairInsertPrependSetup

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem prepend_stores (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .inner shadow s) (layout : Layout o)
    (focus : InsertFocus n o shadow) (resident : Resident n o shadow focus.fresh.owner focus.fresh.base)
    (owner : initial.data.regs.rsi.toNat=focus.fresh.base) (registers : PrependRegisters focus s) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if BitVec.ofNat 64 (Index.head focus.nodes)=0 then codeEntry+0x15b else codeEntry+0x152) ∧
      Core n o c initial ra .inner (prefixMemory focus) t.data ∧ PrependRegisters focus t.data)
      ⟨s,codeEntry+0x142⟩ := by
  let back := focus.fresh.link+o.pprev
  let next := focus.fresh.link+o.next
  have backSlot : LinkSlot n o back := focus.fresh.backSlot layout
  have nextSlot : LinkSlot n o next := focus.fresh.nextSlot layout
  have rootSlot : LinkSlot n o focus.root := .table _ (Nat.mod_lt _ (by decide))
  have backAddress : ∀ {p m t}, Core n o c initial ra p m t →
      t.regs.rbp.toBitVec+16=BitVec.ofNat 64 back := by
    intro p m t core
    rw [core.owner_address owner]
    simp only [back,UnlinkedEntry.link,layout.hash,layout.pprev,Nat.add_assoc,BitVec.ofNat_add]
    rfl
  have nextAddress : ∀ {p m t}, Core n o c initial ra p m t →
      t.regs.rbp.toBitVec+8=BitVec.ofNat 64 next := by
    intro p m t core
    rw [core.owner_address owner]
    simp only [next,UnlinkedEntry.link,layout.hash,layout.next,Nat.add_zero,BitVec.ofNat_add]
    rfl
  have backRead : s.dmem.loadInt (s.regs.rbp.toBitVec+16) 8=some (0 : Int) := by
    rw [backAddress core,←core.frame.loadInt _ _ (backSlot.heap layout)]
    exact word_loadInt _ _ _ _ _ focus.fresh.unlinked
  have originalNext : (shadow.loadInt (.ofNat 64 next) 8).isSome=true := by
    obtain ⟨value,read⟩ := resident.next
    have current : shadow.loadInt (.ofNat 64 next) 8=some (value : Int) := word_loadInt _ _ _ _ _ read
    rw [current]
    rfl
  have originalRoot : (shadow.loadInt (.ofNat 64 focus.root) 8).isSome=true := by
    have current : shadow.loadInt (.ofNat 64 focus.root) 8=some (Index.head focus.nodes : Int) :=
      word_loadInt _ _ _ _ _ focus.headRead
    rw [current]
    rfl
  have first := region_eventually (prepend_back_layout.agreement decoder) s _ (prepend_back s 0 backRead)
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro backed ⟨regs,heap,pc⟩
  have memory : backed.data.dmem=write64 s.dmem back focus.root := by
    simpa only [backAddress core,registers.root,write64] using heap
  have core := (core.store64 facts layout backSlot focus.root).same regs memory
  have registers := registers.same regs
  have nextMapped : ((write64 shadow back focus.root).loadInt (.ofNat 64 next) 8).isSome=true :=
    storeInt_defined _ _ _ _ _ _ originalNext
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp nextMapped
  have nextRead : backed.data.dmem.loadInt (backed.data.regs.rbp.toBitVec+8) 8=some old := by
    rw [nextAddress core,←core.frame.loadInt _ _ (nextSlot.heap layout)]
    exact read
  have second := region_eventually (prepend_next_layout.agreement decoder) backed.data _ (prepend_next backed.data old nextRead)
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc second)
  rintro linked ⟨regs,heap,pc⟩
  have memory : linked.data.dmem=write64 backed.data.dmem next (Index.head focus.nodes) := by
    simpa only [nextAddress core,registers.first,write64] using heap
  have core := (core.store64 facts layout nextSlot (Index.head focus.nodes)).same regs memory
  have registers := registers.same regs
  have rootMapped : ((write64 (write64 shadow back focus.root) next (Index.head focus.nodes)).loadInt
      (.ofNat 64 focus.root) 8).isSome=true :=
    storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ originalRoot)
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp rootMapped
  have rootRead : linked.data.dmem.loadInt linked.data.regs.rax.toBitVec 8=some old := by
    rw [registers.root,←core.frame.loadInt _ _ (rootSlot.heap layout)]
    exact read
  have third := region_eventually (prepend_root_layout.agreement decoder) linked.data _ (prepend_root linked.data old rootRead)
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc third)
  rintro rooted ⟨regs,heap,pc⟩
  have memory : rooted.data.dmem=write64 linked.data.dmem focus.root focus.fresh.link := by
    simpa only [registers.root,registers.link,write64] using heap
  have core := (core.store64 facts layout rootSlot focus.fresh.link).same regs memory
  have registers := registers.same regs
  have test := region_eventually (prepend_test_layout.agreement decoder) rooted.data _ (prepend_test rooted.data)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc test)
  rintro final ⟨regs,heap,pc⟩
  exact ⟨by simpa only [registers.first] using pc,core.same regs heap,registers.same regs⟩

#print axioms prepend_stores
end Binary.Pair.Insert
