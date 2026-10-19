import PairRemoveRegions
import PairStack
import IndexInsertLayout

namespace Binary.Pair.Insert
open Kraken.X64.Parser
local instance : Labels := Image.linkedLabels
abbrev codeEntry := IndexInsertImage.Insert.entry

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (codeEntry+.ofNat offset) (fun pc data => .done ⟨data,pc⟩)

def savedWords (s : MachineData) : List UInt64 :=
  [s.regs.r15,s.regs.r14,s.regs.r13,s.regs.r12,s.regs.rbp,s.regs.rbx,(codeEntry+21).toUInt64]

def saveMemory (s : MachineData) (n : Nat) : DataMem :=
  Stack.save s.dmem s.regs.rsp.toBitVec (savedWords s) n

theorem prologue (s : MachineData)
    (stack : ∀ n<7, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true) :
    (run IndexInsertImage.Insert.r00 0 s).All (fun t =>
      t.data.regs={s.regs with r12 := s.regs.rdi,rbp := s.regs.rsi,rsp := s.regs.rsp-56} ∧
      t.data.dmem=saveMemory s 7 ∧ t.pc=.ofNat 0xffffffff810f31f0) := by
  have mapped (n : Nat) (bound : n<7) :=
    Stack.mapped s.dmem s.regs.rsp.toBitVec (savedWords s) n _ 8 (stack n bound)
  obtain ⟨v0,h0⟩ := Option.isSome_iff_exists.mp (mapped 0 (by decide))
  obtain ⟨v1,h1⟩ := Option.isSome_iff_exists.mp (mapped 1 (by decide))
  obtain ⟨v2,h2⟩ := Option.isSome_iff_exists.mp (mapped 2 (by decide))
  obtain ⟨v3,h3⟩ := Option.isSome_iff_exists.mp (mapped 3 (by decide))
  obtain ⟨v4,h4⟩ := Option.isSome_iff_exists.mp (mapped 4 (by decide))
  obtain ⟨v5,h5⟩ := Option.isSome_iff_exists.mp (mapped 5 (by decide))
  obtain ⟨v6,h6⟩ := Option.isSome_iff_exists.mp (mapped 6 (by decide))
  simp [run,IndexInsertImage.Insert.r00,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,RelRegOrMem.interp,ConstExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexInsertImage.Insert.entry,
    saveMemory,Stack.save,Stack.slot,savedWords,BitVec.sub_sub] at h0 h1 h2 h3 h4 h5 h6 ⊢
  simp_all [Effects.All]
  decide

theorem entry_guard (s : MachineData) (old : BitVec 32) (previous : BitVec 64)
    (preempt : s.dmem.loadInt TrustBase.preemptCountAddress 4=some old.toNat)
    (read : (Remove.preemptMemory s old).loadInt (s.regs.rbp.toBitVec+16) 8=some previous.toNat) :
    (run IndexInsertImage.Insert.r15 21 s).All (fun t =>
      t.data.regs={s.regs with rbx := .ofBitVec previous} ∧
      t.data.dmem=Remove.preemptMemory s old ∧
      t.pc=(if previous=0 then codeEntry+0x4f else codeEntry+0x28)) := by
  simp [run,IndexInsertImage.Insert.r15,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexInsertImage.Insert.entry,TrustBase.preemptCountAddress] at preempt read ⊢
  rw [preempt]
  simp [Effects.All,Remove.preemptMemory,TrustBase.preemptCountAddress] at read ⊢
  rw [read]
  simp [Effects.All,StatusFlags.from_result,CondCode.interp]
  split <;> simp_all [Effects.All]
  decide

theorem predecessor (s : MachineData) (next : BitVec 64) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbp.toBitVec+8) 8=some next.toNat)
    (mapped : s.dmem.loadInt s.regs.rbx.toBitVec 8=some old) :
    (run IndexInsertImage.Insert.r2d 0x2d s).All (fun t =>
      t.data.regs={s.regs with r13 := .ofBitVec next} ∧
      t.data.dmem=s.dmem.storeInt s.regs.rbx.toBitVec 8 next.toInt ∧
      t.pc=(if next=0 then codeEntry+0x42 else codeEntry+0x39)) := by
  simp [run,IndexInsertImage.Insert.r2d,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexInsertImage.Insert.entry] at read mapped ⊢
  rw [read]
  simp [Effects.All,mapped,StatusFlags.from_result,CondCode.interp,BitVec.toInt_eq_toNat_bmod]
  split <;> simp_all [Effects.All]
  decide

theorem clear (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbp.toBitVec+16) 8=some old) :
    (run IndexInsertImage.Insert.r47 0x47 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem.storeInt (s.regs.rbp.toBitVec+16) 8 0 ∧
      t.pc=codeEntry+0x4f) := by
  simp [run,IndexInsertImage.Insert.r47,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at mapped ⊢
  simp [mapped,Effects.All,codeEntry,IndexInsertImage.Insert.entry]

#print axioms prologue
#print axioms entry_guard
#print axioms predecessor
#print axioms clear
end Binary.Pair.Insert
