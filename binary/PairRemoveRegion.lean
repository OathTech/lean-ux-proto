import PairRemove
import LayoutTactic
import StackFrame

namespace Binary.Pair.Remove
open Kraken.X64.Parser
local instance : Labels := Image.linkedLabels

/-- Actual bytes at wg_index_hashtable_remove+0x24: load the successor and
write it through the predecessor's link. remove_probe.py checks both bytes
and addresses against the pinned ELF before running the paired cases. -/
def predecessorCode : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d,n⟩) (parse("mov 0x8(%rbx),%r12
mov %r12,0x0(%rbp)")) [4,4]

def predecessorPC : Int64 := .ofNat (entry+0x24)
def predecessorFetch : Int64 → Option Decoded := Image.fetchIn predecessorPC predecessorCode

theorem predecessor_layout : LaidOut predecessorFetch predecessorPC predecessorCode := by
  binary_layout

/-- Fresh symbolic execution, not a reused M1/M2 instruction lemma. It
allows pointer aliases; mapping and the source load are the only data facts. -/
theorem predecessor_region (s : MachineData) (next : BitVec 64) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat)
    (mapped : s.dmem.loadInt s.regs.rbp.toBitVec 8=some old) :
    (Directives.interp predecessorCode s predecessorPC (fun pc data => .done ⟨data,pc⟩)).All
      (fun t => t.pc=predecessorPC+8 ∧ t.data.regs={s.regs with r12 := .ofBitVec next} ∧
        t.data.dmem=s.dmem.storeInt s.regs.rbp.toBitVec 8 next.toInt) := by
  simp [predecessorCode,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at read mapped ⊢
  rw [read]
  simp [Effects.All,mapped,predecessorPC,entry,BitVec.toInt_eq_toNat_bmod]

theorem predecessor_effect (s : MachineData) (next : BitVec 64) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat)
    (mapped : s.dmem.loadInt s.regs.rbp.toBitVec 8=some old) :
    Eventually (instructionStep predecessorFetch) (fun t =>
      t.pc=predecessorPC+8 ∧ t.data.regs.r12.toBitVec=next ∧
      t.data.dmem.loadInt s.regs.rbp.toBitVec 8=some next.toNat ∧
      EqualOutside (InRange s.regs.rbp.toBitVec 8) s.dmem t.data.dmem) ⟨s,predecessorPC⟩ := by
  have run := region_eventually predecessor_layout s _ (predecessor_region s next old read mapped)
  apply eventually_weaken (instructionStep predecessorFetch) _ _ _ _ run
  rintro t ⟨pc,regs,memory⟩
  exact ⟨pc,by rw [regs],by rw [memory]; exact load64_store _ _ _,
    by rw [memory]; exact storeInt_frame _ _ _ _⟩

#print axioms predecessor_effect

def clearCode : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d,n⟩) (parse("movq $0x0,0x10(%rbx)")) [8]

def clearPC : Int64 := .ofNat (entry+0x40)
def clearFetch : Int64 → Option Decoded := Image.fetchIn clearPC clearCode

theorem clear_layout : LaidOut clearFetch clearPC clearCode := by binary_layout

theorem clear_region (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some old) :
    (Directives.interp clearCode s clearPC (fun pc data => .done ⟨data,pc⟩)).All
      (fun t => t.pc=clearPC+8 ∧ t.data.regs=s.regs ∧
        t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+16) 8 0) := by
  simp [clearCode,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at mapped ⊢
  simp [mapped,Effects.All,clearPC,entry]

theorem clear_effect (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some old) :
    Eventually (instructionStep clearFetch) (fun t =>
      t.pc=clearPC+8 ∧ t.data.regs=s.regs ∧
      t.data.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some 0 ∧
      EqualOutside (InRange (s.regs.rbx.toBitVec+16) 8) s.dmem t.data.dmem) ⟨s,clearPC⟩ := by
  have run := region_eventually clear_layout s _ (clear_region s old mapped)
  apply eventually_weaken (instructionStep clearFetch) _ _ _ _ run
  rintro t ⟨pc,regs,memory⟩
  exact ⟨pc,regs,by rw [memory]; exact load64_store _ _ 0,
    by rw [memory]; exact storeInt_frame _ _ _ _⟩

#print axioms clear_effect
end Binary.Pair.Remove
