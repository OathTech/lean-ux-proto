import PairInsertState
import PairRemoveGuard

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem disable_unhash (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s owner base} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .enabled shadow s) (layout : Layout o)
    (named : (owner,base) ∈ n.owners) (argument : initial.data.regs.rsi.toNat=base)
    (previous : BitVec 64) (read : shadow.loadInt (.ofNat 64 (base+16)) 8=some previous.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if previous=0 then codeEntry+0x4f else codeEntry+0x28) ∧
      Core n o c initial ra .outer shadow t.data ∧ t.data.regs.rbx=UInt64.ofBitVec previous)
      ⟨s,codeEntry+21⟩ := by
  have frame := storeInt_frame s.dmem preemptCountAddress 4 (BitVec.ofInt 32 (512+c.preempt.toNat)).toInt
  have memory := core.memory.preempt_transition (q := .outer) facts frame (Remove.preempt_read s c.preempt)
  have externalFrame : EqualOutside (External c initial 7) shadow (Remove.preemptMemory s c.preempt) :=
    external_trans core.outside (fun a outside => frame a (fun h => outside (.inr (.inr h))))
  have shadowFrame : StorageFrame n o shadow (Remove.preemptMemory s c.preempt) := by
    apply core.frame.trans
    apply external_storage facts.toCallFacts.geometry
    intro a outside
    exact frame a (fun h => outside (.inr (.inr h)))
  have slot : LinkSlot n o (base+16) := .entry owner base 16 named (.inr rfl)
  have addr : s.regs.rbp.toBitVec+16=BitVec.ofNat 64 (base+16) := by
    rw [core.owner]
    have baseEq : initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 base := by
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec,BitVec.toNat_ofNat,←argument,Nat.mod_eq_of_lt initial.data.regs.rsi.toNat_lt_size]
    rw [baseEq,BitVec.ofNat_add]
    rfl
  have same := shadowFrame.loadInt (.ofNat 64 (base+16)) 8 (slot.heap layout)
  have currentRead : (Remove.preemptMemory s c.preempt).loadInt (s.regs.rbp.toBitVec+16) 8=some previous.toNat := by
    rw [addr,←same]
    exact read
  have physical := entry_guard s c.preempt previous (load32_raw _ _ _ core.memory.preempt) currentRead
  have run := region_eventually (IndexInsertImage.Insert_r15_layout.agreement agree) s _ physical
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨registers,mem,pc⟩
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.table,
    by simpa only [registers] using core.owner,
    by simpa [mem,Remove.preemptMemory,Int.natCast_add] using memory,
    by simpa only [mem] using shadowFrame,by simpa only [mem] using externalFrame⟩,by simp only [registers]⟩

#print axioms disable_unhash
end Binary.Pair.Insert
