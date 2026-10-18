import PairRemoveRegions
import PairStack

namespace Binary.Pair.Replace
open Kraken.X64.Parser
local instance : Labels := Image.linkedLabels
abbrev codeEntry := IndexMutatorImage.Replace.entry

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (codeEntry+.ofNat offset) (fun pc data => .done ⟨data,pc⟩)

def savedWords (s : MachineData) : List UInt64 :=
  [s.regs.r13,s.regs.r12,s.regs.rbp,s.regs.rbx,(codeEntry+17).toUInt64]

def saveMemory (s : MachineData) (n : Nat) : DataMem :=
  Stack.save s.dmem s.regs.rsp.toBitVec (savedWords s) n

theorem prologue (s : MachineData)
    (stack : ∀ n<5, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true) :
    (run IndexMutatorImage.Replace.r00 0 s).All (fun t =>
      t.data.regs={s.regs with rbx := s.regs.rsi,rbp := s.regs.rdx,rsp := s.regs.rsp-40} ∧
      t.data.dmem=saveMemory s 5 ∧ t.pc=.ofNat 0xffffffff810f3100) := by
  have mapped (n : Nat) (bound : n<5) :=
    Stack.mapped s.dmem s.regs.rsp.toBitVec (savedWords s) n _ 8 (stack n bound)
  obtain ⟨v0,h0⟩ := Option.isSome_iff_exists.mp (mapped 0 (by decide))
  obtain ⟨v1,h1⟩ := Option.isSome_iff_exists.mp (mapped 1 (by decide))
  obtain ⟨v2,h2⟩ := Option.isSome_iff_exists.mp (mapped 2 (by decide))
  obtain ⟨v3,h3⟩ := Option.isSome_iff_exists.mp (mapped 3 (by decide))
  obtain ⟨v4,h4⟩ := Option.isSome_iff_exists.mp (mapped 4 (by decide))
  simp [run,IndexMutatorImage.Replace.r00,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,RelRegOrMem.interp,ConstExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexMutatorImage.Replace.entry,
    saveMemory,Stack.save,Stack.slot,savedWords,BitVec.sub_sub] at h0 h1 h2 h3 h4 ⊢
  simp_all [Effects.All]
  decide

def resultWord (old : UInt64) (previous : BitVec 64) : UInt64 :=
  .ofBitVec (old.toBitVec.replaceLow (if previous=0 then (0 : BitVec 8) else 1))

theorem entry_guard (s : MachineData) (old : BitVec 32) (previous : BitVec 64)
    (preempt : s.dmem.loadInt TrustBase.preemptCountAddress 4=some old.toNat)
    (read : (Remove.preemptMemory s old).loadInt (s.regs.rbx.toBitVec+16) 8=some previous.toNat) :
    (run IndexMutatorImage.Replace.r11 17 s).All (fun t =>
      t.data.regs={s.regs with r13 := resultWord s.regs.r13 previous} ∧
      t.data.dmem=Remove.preemptMemory s old ∧
      t.pc=(if previous=0 then codeEntry+0x81 else codeEntry+0x26)) := by
  simp [run,IndexMutatorImage.Replace.r11,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexMutatorImage.Replace.entry,TrustBase.preemptCountAddress] at preempt read ⊢
  rw [preempt]
  simp [Effects.All,Remove.preemptMemory,TrustBase.preemptCountAddress] at read ⊢
  rw [read]
  simp [Effects.All,StatusFlags.from_result,CondCode.interp,resultWord]
  split <;> simp_all [Effects.All]
  decide
  rename_i nonzero
  rw [beq_eq_false_iff_ne.mpr nonzero]
  rfl

#print axioms prologue
#print axioms entry_guard
end Binary.Pair.Replace
