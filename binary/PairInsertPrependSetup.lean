import PairInsertPrependRegion
import PairInsertSearch

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

structure PrependRegisters {n o m} (focus : InsertFocus n o m) (s : MachineData) : Prop where
  root : s.regs.rax.toBitVec=BitVec.ofNat 64 focus.root
  link : s.regs.r13.toBitVec=BitVec.ofNat 64 focus.fresh.link
  first : s.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head focus.nodes)

theorem PrependRegisters.same {n o m focus s t} (ready : @PrependRegisters n o m focus s)
    (regs : t.regs=s.regs) : PrependRegisters focus t :=
  ⟨by rw [regs]; exact ready.root,by rw [regs]; exact ready.link,by rw [regs]; exact ready.first⟩

theorem prepend_setup_endpoint (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s}
    (core : Core n o c initial ra .inner shadow s) (layout : Layout o)
    (focus : InsertFocus n o shadow)
    (table : initial.data.regs.rdi.toNat=n.table) (owner : initial.data.regs.rsi.toNat=focus.fresh.base)
    (registers : WalkRegisters true focus.index s) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x142 ∧
      Core n o c initial ra .inner shadow t.data ∧ PrependRegisters focus t.data) ⟨s,codeEntry+0x136⟩ := by
  have root : prependRootAddress s=BitVec.ofNat 64 focus.root := by
    rw [prependRootAddress,core.table_address table,u64_address (registers.bucket rfl)]
    simp only [InsertFocus.root,tableHead,layout.buckets,layout.headSize,layout.first,Nat.add_zero,
      BitVec.ofNat_add,BitVec.ofNat_mul]
    rfl
  have headValue : (UInt64.ofNat (Index.head focus.nodes)).toNat=Index.head focus.nodes := by
    change Index.head focus.nodes%2^64=Index.head focus.nodes
    exact Nat.mod_eq_of_lt (word_bound focus.headRead)
  have read : s.dmem.loadInt (prependRootAddress s) 8=some (UInt64.ofNat (Index.head focus.nodes)).toNat := by
    have slot : LinkSlot n o focus.root := .table _ (Nat.mod_lt _ (by decide))
    rw [root,headValue,←core.frame.loadInt _ _ (slot.heap layout)]
    exact word_loadInt _ _ _ _ _ focus.headRead
  have run := region_eventually (prepend_setup_layout.agreement decoder) s _
    (prepend_setup s (.ofNat (Index.head focus.nodes)) read)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨regs,heap,pc⟩
  refine ⟨pc,⟨by rw [regs]; exact core.stack,by rw [regs]; exact core.table,
    by rw [regs]; exact core.owner,heap ▸ core.memory,heap ▸ core.frame,heap ▸ core.outside⟩,?_,?_,?_⟩
  · rw [regs]
    exact root
  · rw [regs,UInt64.toBitVec_add,core.owner_address owner]
    simp only [UnlinkedEntry.link,layout.hash,BitVec.ofNat_add]
    rfl
  · rw [regs]
    rfl

def prefixMemory {n o m} (f : InsertFocus n o m) : DataMem :=
  write64 (write64 (write64 m (f.fresh.link+o.pprev) f.root)
    (f.fresh.link+o.next) (Index.head f.nodes)) f.root f.fresh.link

#print axioms prepend_setup_endpoint
end Binary.Pair.Insert
