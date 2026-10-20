import PairReplaceFirstState
import PairRemoveGuard

namespace Binary.Pair.Replace.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem disable (fetch : Int64 → Option Decoded) (agree : IndexReplaceDecoderAgreement fetch)
    {n o c initial ra shadow result s owner base} (facts : CallFacts n o c initial ra 5)
    (core : Core c initial ra false shadow result s) (layout : Layout o)
    (named : (owner,base) ∈ n.owners) (argument : initial.data.regs.rsi.toNat=base)
    (previous : BitVec 64) (read : shadow.loadInt (.ofNat 64 (base+16)) 8=some previous.toNat) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t =>
      t.pc=(if previous=0 then codeEntry+0x81 else codeEntry+0x26) ∧
      Core c initial ra true shadow (resultWord result previous) t.data)
      ⟨s,codeEntry+17⟩ := by
  have frame := storeInt_frame s.dmem preemptCountAddress 4 (BitVec.ofInt 32 (512+c.preempt.toNat)).toInt
  have memory := core.memory.preempt_transition (second := true) facts.geometry frame (Remove.preempt_read s c.preempt)
  have shadowFrame : EqualOutside (External c initial 5) shadow (Remove.preemptMemory s c.preempt) := by
    apply external_trans core.frame
    intro a outside
    exact frame a (fun h => outside (.inr (.inr h)))
  have slot : LinkSlot n o (base+16) := .entry owner base 16 named (.inr rfl)
  have addr : s.regs.rbx.toBitVec+16=BitVec.ofNat 64 (base+16) := by
    rw [core.owner]
    have baseEq : initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 base := by
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec,BitVec.toNat_ofNat,←argument,Nat.mod_eq_of_lt initial.data.regs.rsi.toNat_lt_size]
    rw [baseEq,BitVec.ofNat_add]
    rfl
  have same := external_read facts.geometry shadowFrame (slot.heap layout)
  have currentRead : (Remove.preemptMemory s c.preempt).loadInt (s.regs.rbx.toBitVec+16) 8=some previous.toNat := by
    rw [addr,←same]
    exact read
  have physical := entry_guard s c.preempt previous (load32_raw _ _ _ core.memory.preempt) currentRead
  have run := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Replace_r11_layout.agreement agree) s _ (by rw [core.stack]; stack_path) physical
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ run
  rintro t ⟨registers,mem,pc⟩
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.owner,
    by simpa only [registers] using core.new,by simp only [registers,core.r13],
    by simpa only [registers] using core.r14,
    by simpa only [registers] using core.r15,by simpa [mem,Remove.preemptMemory,Int.natCast_add] using memory,
    by simpa only [mem] using shadowFrame⟩⟩

#print axioms disable
end Binary.Pair.Replace.First
