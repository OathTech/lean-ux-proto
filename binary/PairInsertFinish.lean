import PairInsertPrepend
import PairInsertEnableSites

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem restore (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s base owner index}
    (core : Core n o c initial ra .enabled shadow s) (layout : Layout o)
    (named : (owner,base) ∈ n.owners) (argument : initial.data.regs.rsi.toNat=base)
    (indexRead : word shadow "insert.index" (base+o.index) 4=.ok index) :
    Eventually (instructionStep fetch) (fun t => Returned initial t ra ∧
      MemoryReady c initial ra (savedWords initial.data) .enabled t.data.dmem ∧
      StorageFrame n o shadow t.data.dmem ∧ t.data.regs.rax.toNat=index) ⟨s,codeEntry+0x181⟩ := by
  have slot (i : Nat) (bound : i≤6) :
      s.regs.rsp.toBitVec+BitVec.ofNat 64 (8*i)=Stack.slot initial.data.regs.rsp.toBitVec (6-i) := by
    rw [core.stack,UInt64.toBitVec_sub]
    change Stack.slot initial.data.regs.rsp.toBitVec 6+BitVec.ofNat 64 (8*i)=_
    rw [Stack.window _ 6 (6-i) (by omega)]
    rw [show 6-(6-i)=i by omega]
  have h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some initial.data.regs.rbx.toNat := by
    have address := slot 0 (by decide)
    change s.regs.rsp.toBitVec+0#64=Stack.slot initial.data.regs.rsp.toBitVec 6 at address
    rw [BitVec.add_zero] at address
    rw [address]
    exact core.memory.saved 5 (by decide)
  have h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some initial.data.regs.rbp.toNat := by
    have address := slot 1 (by decide)
    change s.regs.rsp.toBitVec+8=Stack.slot initial.data.regs.rsp.toBitVec 5 at address
    rw [address]
    exact core.memory.saved 4 (by decide)
  have h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some initial.data.regs.r12.toNat := by
    have address := slot 2 (by decide)
    change s.regs.rsp.toBitVec+16=Stack.slot initial.data.regs.rsp.toBitVec 4 at address
    rw [address]
    exact core.memory.saved 3 (by decide)
  have h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some initial.data.regs.r13.toNat := by
    have address := slot 3 (by decide)
    change s.regs.rsp.toBitVec+24=Stack.slot initial.data.regs.rsp.toBitVec 3 at address
    rw [address]
    exact core.memory.saved 2 (by decide)
  have h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8=some initial.data.regs.r14.toNat := by
    have address := slot 4 (by decide)
    change s.regs.rsp.toBitVec+32=Stack.slot initial.data.regs.rsp.toBitVec 2 at address
    rw [address]
    exact core.memory.saved 1 (by decide)
  have h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8=some initial.data.regs.r15.toNat := by
    have address := slot 5 (by decide)
    change s.regs.rsp.toBitVec+40=Stack.slot initial.data.regs.rsp.toBitVec 1 at address
    rw [address]
    exact core.memory.saved 0 (by decide)
  have h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8=some ra.toNat := by
    have address := slot 6 (by decide)
    change s.regs.rsp.toBitVec+48=Stack.slot initial.data.regs.rsp.toBitVec 0 at address
    rw [address]
    change s.dmem.loadInt (initial.data.regs.rsp.toBitVec-0#64) 8=some ra.toNat
    rw [BitVec.sub_zero]
    exact core.memory.returnWord
  have small : index<2^32 := word_bound indexRead
  have address : s.regs.rbp.toBitVec+28=BitVec.ofNat 64 (base+o.index) := by
    rw [core.owner_address argument,layout.index,BitVec.ofNat_add]
    rfl
  have read : s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4=some (BitVec.ofNat 32 index).toNat := by
    have slot : DataSlot n o (base+o.index) 4 := by
      rw [layout.index]
      exact .entry owner base 28 4 named (.inr (.inr rfl))
    rw [address,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,←core.frame.loadInt _ _ (slot.heap layout)]
    exact word_loadInt _ _ _ _ _ indexRead
  have region := region_eventually (IndexInsertImage.Insert_r181_layout.agreement decoder) s _
    (restore_return s (.ofNat 32 index) initial.data.regs.rbx initial.data.regs.rbp initial.data.regs.r12
      initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 ra read h0 h1 h2 h3 h4 h5 h6)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ region
  rintro t ⟨registers,memory,pc⟩
  refine ⟨⟨pc,?_,by rw [registers],by rw [registers],by rw [registers],by rw [registers],
    by rw [registers],by rw [registers]⟩,memory ▸ core.memory,memory ▸ core.frame,?_⟩
  · rw [registers,core.stack]
    apply UInt64.toBitVec_inj.mp
    change (initial.data.regs.rsp.toBitVec-48)+56=initial.data.regs.rsp.toBitVec+8
    rw [show (56 : BitVec 64)=48+8 from rfl,←BitVec.add_assoc,BitVec.sub_add_cancel]
  · rw [registers]
    change (index%2^32)%2^64=index
    rw [Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (by omega : index<2^64)]

theorem finish (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (bh : BhEnableContract fetch) {n o c initial ra shadow s base owner index}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .inner shadow s)
    (layout : Layout o) (named : (owner,base) ∈ n.owners) (argument : initial.data.regs.rsi.toNat=base)
    (indexRead : word shadow "insert.index" (base+o.index) 4=.ok index) :
    Eventually (instructionStep fetch) (fun t => Returned initial t ra ∧
      MemoryReady c initial ra (savedWords initial.data) .enabled t.data.dmem ∧
      StorageFrame n o shadow t.data.dmem ∧ t.data.regs.rax.toNat=index) ⟨s,codeEntry+0x160⟩ := by
  have inner := enable_nested fetch decoder bh facts core
  apply eventually_trans (instructionStep fetch) _ _ _ inner
  rintro enabled ⟨pc,core,_⟩
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc (enable_outer fetch decoder bh facts core))
  rintro enabled ⟨pc,core⟩
  exact at_pc pc (restore fetch decoder core layout named argument indexRead)

#print axioms restore
#print axioms finish
end Binary.Pair.Insert
