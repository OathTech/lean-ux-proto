import CallbackExecution
import StackFrame

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels

def BhPost (s : MachineData) (ra : UInt64) (count : BitVec 32) (t : MachineState) : Prop :=
  Returned ⟨s,.ofNat 0xffffffff810732c0⟩ t ra ∧
    EqualOutside (InRange preemptCountAddress 4) s.dmem t.data.dmem ∧
    t.data.dmem.loadInt preemptCountAddress 4=
      some ((count-s.regs.get (.low .rsi .W32)).toNat : Int)

macro "callback_step" : tactic => `(tactic|
  (apply leaf_step (by rfl) (by decide) (by rfl) (by rfl)
   simp only [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
     AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set,
     Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
     BitVec.toAddressSize, Effects.All]))

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem bh_decrement {rsp : UInt64} (s : MachineData) (ra : UInt64) (count : BitVec 32)
    (stack : s.regs.rsp=rsp)
    (read : s.dmem.loadInt preemptCountAddress 4=some (count.toNat : Int))
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (apart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange s.regs.rsp.toBitVec 8 a)
    (P : MachineState → Prop)
    (finish : ∀ t, Returned ⟨s,.ofNat 0xffffffff810732e3⟩ t ra →
      t.data.dmem=s.dmem.storeInt preemptCountAddress 4 (count-1).toInt → P t) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp)) P
      ⟨s,.ofNat 0xffffffff810732e3⟩ := by
  have scalar : (count-1).toInt=((count.toNat : Int)-1).bmod 4294967296 := by
    calc
      (count-1).toInt=(count.toInt-1).bmod 4294967296 := by rw [BitVec.toInt_sub]; rfl
      _ = _ := by rw [BitVec.toInt_eq_toNat_bmod,Int.bmod_sub_bmod]
  have preserved := (storeInt_frame s.dmem preemptCountAddress 4 (count-1).toInt).loadInt
    s.regs.rsp.toBitVec 8 (by
      intro i hi written
      exact apart _ written ⟨i,hi,rfl⟩)
  have returnRead := preserved.symm.trans ret
  apply leaf_step (by rfl) (by decide) (by exact stack) (by rfl)
  simp only [Instr.interp,Operation.interp,RegOrMem.interp,MachineData.load,
    MachineData.store,MachineData.set,AddrExpr.interp,ConstExpr.interp,Effects.All]
  simp [preemptCountAddress] at read ⊢
  rw [read]
  simp [Effects.All,-BitVec.toInt_sub]
  apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by exact stack)
  · simpa only [scalar,preemptCountAddress] using returnRead
  · apply finish
    · simp [Returned]
    · simp only [scalar,preemptCountAddress]

theorem bh_test {rsp : UInt64} (s : MachineData) (ra : UInt64) (count : BitVec 32)
    (stack : s.regs.rsp=rsp)
    (read : s.dmem.loadInt preemptCountAddress 4=some (count.toNat : Int))
    (pending : count &&& 0x00ffff00#32=0#32 → s.dmem.loadInt softirqPendingAddress 2=some 0)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (apart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange s.regs.rsp.toBitVec 8 a)
    (P : MachineState → Prop)
    (finish : ∀ t, Returned ⟨s,.ofNat 0xffffffff810732d7⟩ t ra →
      t.data.dmem=s.dmem.storeInt preemptCountAddress 4 (count-1).toInt → P t) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp)) P
      ⟨s,.ofNat 0xffffffff810732d7⟩ := by
  apply leaf_step (by rfl) (by decide) (by exact stack) (by rfl)
  simp only [Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,AddrExpr.interp,ConstExpr.interp,Effects.All]
  simp [preemptCountAddress] at read ⊢
  rw [read]
  simp only [Effects.All]
  intro af
  apply leaf_step (by rfl) (by decide) (by exact stack) (by rfl)
  simp [Instr.interp,Operation.interp,StatusFlags.from_result,CondCode.interp]
  by_cases zero : count &&& 0x00ffff00#32=0#32
  · simp only [zero,ite_true,Effects.All]
    have destination : label "L_ffffffff810732ee" = .ofNat 0xffffffff810732ee := by decide +kernel
    rw [destination]
    apply leaf_step (by rfl) (by decide) (by exact stack) (by rfl)
    simp only [Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
      MachineData.load,AddrExpr.interp,ConstExpr.interp,Effects.All]
    have hp := pending zero
    simp [softirqPendingAddress] at hp ⊢
    rw [hp]
    simp only [Effects.All]
    apply leaf_step (by rfl) (by decide) (by exact stack) (by rfl)
    simp [Instr.interp,Operation.interp,StatusFlags.from_result,CondCode.interp,Effects.All]
    apply bh_decrement _ ra count (by exact stack) (by exact read) (by exact ret) (by exact apart) P
    intro t returned memory
    exact finish t returned memory
  · simp only [zero,ite_false,Effects.All]
    apply bh_decrement _ ra count (by exact stack) (by exact read) (by exact ret) (by exact apart) P
    intro t returned memory
    exact finish t returned memory

theorem bh_run (s : MachineData) (ra : UInt64) (count : BitVec 32)
    (read : s.dmem.loadInt preemptCountAddress 4=some count.toNat)
    (hardirq : count &&& 0x000f0000=0)
    (pending : (count+1-s.regs.get (.low .rsi .W32)) &&& 0x00ffff00=0 →
      s.dmem.loadInt softirqPendingAddress 2=some 0)
    (apart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange s.regs.rsp.toBitVec 8 a)
    (frame : EntryFrame ⟨s,.ofNat 0xffffffff810732c0⟩ ra) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
      (BhPost s ra count)
      ⟨s,.ofNat 0xffffffff810732c0⟩ := by
  change count &&& 983040#32 = 0#32 at hardirq
  change (count+1-s.regs.get (.low .rsi .W32)) &&& 0x00ffff00#32=0#32 → _ at pending
  callback_step
  simp [preemptCountAddress] at read ⊢
  rw [read]
  simp only [Effects.All]
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp]
  rw [hardirq]
  simp only [ite_true, Effects.All]
  callback_step
  callback_step
  callback_step
  simp [read,Effects.All,BitVec.extractLsb'_setWidth_of_le,
    -BitVec.toInt_add,-BitVec.toInt_sub]
  let adjusted : BitVec 32 := -(s.regs.rsi.toBitVec.extractLsb' 0 32-1#32)+count
  have algebra : adjusted=count+1-s.regs.get (.low .rsi .W32) := by
    simp only [adjusted,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
      BitVec.drop,BitVec.take,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self]
    change -(s.regs.rsi.toBitVec.extractLsb' 0 32-1#32)+count=
      count+1#32-s.regs.rsi.toBitVec.extractLsb' 0 32
    rw [BitVec.neg_sub]
    simp only [BitVec.sub_eq_add_neg]
    ac_rfl
  have decremented : adjusted-1=count-s.regs.get (.low .rsi .W32) := by
    rw [algebra]
    calc
      count+1-s.regs.get (.low .rsi .W32)-1 =
          (count-s.regs.get (.low .rsi .W32))+(1-1) := by
        simp only [BitVec.sub_eq_add_neg]
        ac_rfl
      _ = _ := by simp
  have firstFrame := storeInt_frame s.dmem preemptCountAddress 4 adjusted.toInt
  have keepReturn := firstFrame.loadInt s.regs.rsp.toBitVec 8 (by
    intro i hi written
    exact apart _ written ⟨i,hi,rfl⟩)
  have keepPending := firstFrame.loadInt softirqPendingAddress 2 (by
    intro i hi written
    exact InRange.offset_disjoint preemptCountAddress 0 4 24 2
      (by decide) (by decide) (.inl (by decide)) _ (by simpa using written)
      ⟨i,hi,by rfl⟩)
  apply bh_test _ ra adjusted (by rfl)
  · exact load32_store _ _ adjusted
  · intro zero
    change (s.dmem.storeInt preemptCountAddress 4 adjusted.toInt).loadInt softirqPendingAddress 2=some 0
    exact keepPending.symm.trans (pending (by simpa only [algebra] using zero))
  · exact keepReturn.symm.trans frame.2
  · exact apart
  · intro t returned memory
    unfold BhPost
    refine ⟨?_,?_,?_⟩
    · simpa only [Returned] using returned
    · rw [memory]
      have secondFrame := storeInt_frame
        (s.dmem.storeInt preemptCountAddress 4 adjusted.toInt) preemptCountAddress 4 (adjusted-1).toInt
      exact fun a outside => (firstFrame a outside).trans (secondFrame a outside)
    · rw [memory]
      calc
        _ = some ((adjusted-1).toNat : Int) := load32_store _ _ (adjusted-1)
        _ = _ := by rw [decremented]

/-- The actual image discharges the former no-work BH behavioral premise. -/
theorem bh_image_contract : BhEnableContract ServiceImage.fetch := by
  apply leaf_contract
  intro initial ra pc ready frame
  rcases initial with ⟨s,p⟩
  change p=_ at pc
  subst p
  rcases ready with ⟨count,read,hardirq,pending,apart⟩
  apply eventually_weaken (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
    _ _ _ _ (bh_run s ra count read hardirq pending apart frame)
  rintro t ⟨returned,framed,changed⟩
  refine ⟨returned,framed,?_⟩
  intro old oldRead
  have equal : old=count := by
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast Option.some.inj (oldRead.symm.trans read)
  subst old
  exact changed

#print axioms bh_image_contract
end Binary.Callback
