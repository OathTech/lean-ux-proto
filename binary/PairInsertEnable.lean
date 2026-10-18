import PairInsertState
import PairInsertTailRegions
import PairCallSlot

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

def beforeEnable (nested : Bool) : Phase := if nested then .inner else .outer
def afterEnable (nested : Bool) : Phase := if nested then .outer else .enabled

theorem enable_count (c : Context) (nested : Bool) :
    ((beforeEnable nested).context c).preempt=(Index.phase c nested).preempt+512 := by
  cases nested with
  | false => rfl
  | true => change c.preempt+1024=c.preempt+512+512; rw [BitVec.add_assoc]; rfl

theorem enabled_count (c : Context) (nested : Bool) :
    ((afterEnable nested).context c).preempt=(Index.phase c nested).preempt := by
  cases nested <;> rfl

/-- One service composition for all three BH-enable sites. The nested case
uses the separately checked pending-word read at the once-disabled count. -/
theorem Core.enable_region (fetch : Int64 → Option Decoded) (bh : BhEnableContract fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (nested : Bool) (core : Core n o c initial ra (beforeEnable nested) shadow s)
    (start : MachineState) (returnPC : Int64) (registers : Reg64s)
    (owner : registers.rbp=s.regs.rbp) (table : registers.r12=s.regs.r12)
    (argument : registers.get (.low .rsi .W32)=512#32)
    (region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs={registers with rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810732c0) start) :
    Eventually (instructionStep fetch) (fun t => t.pc=returnPC ∧
      Core n o c initial ra (afterEnable nested) shadow t.data ∧
      t.data.regs.rbx=registers.rbx ∧ t.data.regs.r13=registers.r13 ∧
      t.data.regs.r14=registers.r14 ∧ t.data.regs.r15=registers.r15) start := by
  apply eventually_trans (instructionStep fetch) _ _ _ region
  rintro entered ⟨regs,heap,pc⟩
  have sp : entered.data.regs.rsp.toBitVec=Stack.slot initial.data.regs.rsp.toBitVec 7 := by
    rw [regs,UInt64.toBitVec_sub]
    exact core.call_slot
  have mem : MemoryReady c initial ra (savedWords initial.data) (beforeEnable nested) entered.data.dmem := by
    rw [heap,core.call_slot]
    exact core.memory.call_store facts _
  have count : entered.data.dmem.loadInt preemptCountAddress 4=
      some (((Index.phase c nested).preempt+512).toNat : Int) := by
    have read := load32_raw _ _ _ mem.preempt
    rw [enable_count] at read
    exact read
  have arg : entered.data.regs.get (.low .rsi .W32)=512#32 := by
    simpa only [regs,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset] using argument
  have ready : BhEnableReady entered := by
    refine ⟨(Index.phase c nested).preempt+512,count,?_,?_,?_⟩
    · cases nested with
      | false => exact facts.hardirq
      | true =>
        change (c.preempt+512+512) &&& 0x000f0000=0
        rw [BitVec.add_assoc]
        exact facts.nestedHardirq
    · intro gate
      rw [arg] at gate
      change ((Index.phase c nested).preempt+512+1-512) &&& 0x00ffff00=0 at gate
      have arithmetic : (Index.phase c nested).preempt+512+1-512=
          (Index.phase c nested).preempt+1 := by
        rw [BitVec.add_assoc,BitVec.add_comm (512 : BitVec 32) 1,←BitVec.add_assoc,BitVec.add_sub_cancel]
      rw [arithmetic] at gate
      exact mem.pending nested gate
    · intro a written inside
      rw [sp] at inside
      exact facts.toCallFacts.geometry.preemptLive a (Stack.inside _ 7 7 (by decide) a inside) written
  have entryFrame : EntryFrame entered returnPC.toUInt64 := by
    refine ⟨?_,?_⟩
    · rw [regs,core.stack]
      have arithmetic : initial.data.regs.rsp-48-8=initial.data.regs.rsp-56 := by
        apply UInt64.toBitVec_inj.mp
        change (initial.data.regs.rsp.toBitVec-48)-8=initial.data.regs.rsp.toBitVec-56
        rw [BitVec.sub_sub]
        rfl
      rw [arithmetic]
      exact aligned_sub _ 56 facts.entry.1 (by decide)
    · rw [sp,heap,core.call_slot,load64_store]
      rfl
  apply Sequential.forget (bh entered returnPC.toUInt64 pc ready entryFrame)
  rintro t ⟨returned,frame,effect,_⟩
  have restored : load32 t.machine.data.dmem preemptCountAddress=
      some ((afterEnable nested).context c).preempt := by
    have read := effect ((Index.phase c nested).preempt+512) count
    rw [arg] at read
    change t.machine.data.dmem.loadInt preemptCountAddress 4=
      some (((Index.phase c nested).preempt+512-512).toNat : Int) at read
    rw [BitVec.add_sub_cancel] at read
    simp only [load32,read,Option.map_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq,enabled_count]
  refine ⟨returned.1,⟨?_,?_,?_,mem.preempt_transition facts frame restored,?_⟩,?_,?_,?_,?_⟩
  · rw [returned.2.1,regs,UInt64.sub_add_cancel]
    exact core.stack
  · rw [returned.2.2.2.2.1,regs,table]
    exact core.table
  · rw [returned.2.2.2.1,regs,owner]
    exact core.owner
  · apply core.frame.trans
    apply Index.external_storage facts.toCallFacts.geometry
    intro a outside
    have first := storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt a (by
      rw [core.call_slot]
      intro inside
      exact outside (.inl (Stack.scratch _ 7 7 (by decide) (by decide) a inside)))
    rw [←heap] at first
    exact first.trans (frame a (fun inside => outside (.inr (.inr inside))))
  · simpa only [regs] using returned.2.2.1
  · simpa only [regs] using returned.2.2.2.2.2.1
  · simpa only [regs] using returned.2.2.2.2.2.2.1
  · simpa only [regs] using returned.2.2.2.2.2.2.2

#print axioms Core.enable_region
end Binary.Pair.Insert
