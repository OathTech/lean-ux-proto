import IndexMutatorLayout
import PairRemoveRegion
import TrustBase

namespace Binary.Pair.Remove
open Kraken.X64.Parser
local instance : Labels := Image.linkedLabels

abbrev codeEntry := IndexMutatorImage.Remove.entry

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (codeEntry+.ofNat offset) (fun pc data => .done ⟨data,pc⟩)

def savedWords (s : MachineData) : List UInt64 :=
  [s.regs.r12,s.regs.rbp,s.regs.rbx,(codeEntry+12).toUInt64]

def saveMemory (s : MachineData) : Nat → DataMem
  | 0 => s.dmem
  | n+1 => (saveMemory s n).storeInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt

theorem saves_mapped (s : MachineData) (n : Nat) (address : BitVec 64)
    (mapped : (s.dmem.loadInt address 8).isSome=true) :
    ((saveMemory s n).loadInt address 8).isSome=true := by
  induction n with
  | zero => exact mapped
  | succ n ih => exact storeInt_defined _ _ _ _ _ _ ih

theorem prologue (s : MachineData)
    (stack : ∀ n<4, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true) :
    (run IndexMutatorImage.Remove.r00 0 s).All (fun t =>
      t.data.regs={s.regs with rbx := s.regs.rsi,rsp := s.regs.rsp-32} ∧
      t.data.dmem=saveMemory s 4 ∧ t.pc=.ofNat 0xffffffff810f31f0) := by
  have mapped (n : Nat) (bound : n<4) := saves_mapped s n _ (stack n bound)
  obtain ⟨v0,h0⟩ := Option.isSome_iff_exists.mp (mapped 0 (by decide))
  obtain ⟨v1,h1⟩ := Option.isSome_iff_exists.mp (mapped 1 (by decide))
  obtain ⟨v2,h2⟩ := Option.isSome_iff_exists.mp (mapped 2 (by decide))
  obtain ⟨v3,h3⟩ := Option.isSome_iff_exists.mp (mapped 3 (by decide))
  simp [run,IndexMutatorImage.Remove.r00,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,RelRegOrMem.interp,ConstExpr.interp,
    Effects.All,Width.bytesv,codeEntry,IndexMutatorImage.Remove.entry,
    saveMemory,savedWords,BitVec.sub_sub] at h0 h1 h2 h3 ⊢
  simp_all [Effects.All]
  decide

def preemptMemory (s : MachineData) (old : BitVec 32) : DataMem :=
  s.dmem.storeInt TrustBase.preemptCountAddress 4 (BitVec.ofInt 32 (512+old.toNat)).toInt

theorem entry_guard (s : MachineData) (old : BitVec 32) (previous : BitVec 64)
    (preempt : s.dmem.loadInt TrustBase.preemptCountAddress 4=some old.toNat)
    (read : (preemptMemory s old).loadInt (s.regs.rbx.toBitVec+16) 8=some previous.toNat) :
    (run IndexMutatorImage.Remove.r0c 12 s).All (fun t =>
      t.data.regs={s.regs with rbp := .ofBitVec previous} ∧ t.data.dmem=preemptMemory s old ∧
      t.pc=(if previous=0 then codeEntry+0x48 else codeEntry+0x1f)) := by
  simp [run,IndexMutatorImage.Remove.r0c,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexMutatorImage.Remove.entry,TrustBase.preemptCountAddress] at preempt read ⊢
  rw [preempt]
  simp [Effects.All,preemptMemory,TrustBase.preemptCountAddress] at read ⊢
  rw [read]
  simp [Effects.All,StatusFlags.from_result,CondCode.interp]
  split <;> simp_all [Effects.All]
  decide

theorem predecessor_guard (s : MachineData) (next : BitVec 64) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat)
    (mapped : s.dmem.loadInt s.regs.rbp.toBitVec 8=some old) :
    (run IndexMutatorImage.Remove.r24 0x24 s).All (fun t =>
      t.data.regs={s.regs with r12 := .ofBitVec next} ∧
      t.data.dmem=s.dmem.storeInt s.regs.rbp.toBitVec 8 next.toInt ∧
      t.pc=(if next=0 then codeEntry+0x3b else codeEntry+0x31)) := by
  simp [run,IndexMutatorImage.Remove.r24,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    codeEntry,IndexMutatorImage.Remove.entry] at read mapped ⊢
  rw [read]
  simp [Effects.All,mapped,StatusFlags.from_result,CondCode.interp,BitVec.toInt_eq_toNat_bmod]
  split <;> simp_all [Effects.All]
  decide

theorem successor_store (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.r12.toBitVec+8) 8=some old) :
    (run IndexMutatorImage.Remove.r36 0x36 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem.storeInt (s.regs.r12.toBitVec+8) 8 s.regs.rbp.toBitVec.toInt ∧
      t.pc=codeEntry+0x3b) := by
  simp [run,IndexMutatorImage.Remove.r36,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.store,MachineData.set,AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
    BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_add,BitVec.ofInt_ofNat,
    Effects.All,codeEntry,IndexMutatorImage.Remove.entry] at mapped ⊢
  simp [mapped,Effects.All]

theorem clear_store (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some old) :
    (run IndexMutatorImage.Remove.r40 0x40 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+16) 8 0 ∧
      t.pc=codeEntry+0x48) := by
  have proved := clear_region s old mapped
  change (run IndexMutatorImage.Remove.r40 0x40 s).All (fun t =>
    t.pc=codeEntry+0x48 ∧ t.data.regs=s.regs ∧ t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+16) 8 0) at proved
  exact all_mono _ _ _ (fun _ h => ⟨h.2.1,h.2.2,h.1⟩) proved

theorem tail_to_bh (s : MachineData) (bx bp r12 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some r12.toNat) :
    (run IndexMutatorImage.Remove.r4d 0x4d s).All (fun t =>
      t.data.regs={s.regs with rbx := bx,rbp := bp,r12 := r12,rsi := 512,rdi := (codeEntry+0x5d).toUInt64,rsp := s.regs.rsp+24} ∧
      t.data.dmem=s.dmem ∧ t.pc=.ofNat 0xffffffff810732c0) := by
  simp [run,IndexMutatorImage.Remove.r4d,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,
    Effects.All,
    codeEntry,IndexMutatorImage.Remove.entry,UInt64.toBitVec_add,
    UInt64.ofBitVec_add,BitVec.add_assoc] at h0 h1 h2 ⊢
  simp_all [Effects.All]
  decide

#print axioms prologue
#print axioms entry_guard
#print axioms predecessor_guard
#print axioms successor_store
#print axioms clear_store
#print axioms tail_to_bh
end Binary.Pair.Remove
