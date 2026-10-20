import AllowedipsHeaderWord

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def parentMemory (s : MachineData) (slot : BitVec 64) : DataMem :=
  s.dmem.storeInt (s.regs.rbx.toBitVec+48) 8 (slot ||| 2).toInt

def rootMemory (s : MachineData) (slot : BitVec 64) : DataMem :=
  (parentMemory s slot).storeInt slot 8 s.regs.rbx.toBitVec.toInt

/-- The root-slot load is after the key copy. A packed parent is installed
before publishing the new root, exactly as in the image. -/
theorem connect (s : MachineData) (slot : BitVec 64)
    (saved : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some slot.toNat)
    (parentMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+48) 8).isSome=true)
    (rootMapped : ((parentMemory s slot).loadInt slot 8).isSome=true) :
    (Placement.physical Add.r4d6 0x4d6 s).All (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=rootMemory s slot ∧
      t.data.regs={s.regs with rdx:=.ofBitVec slot,rax:=.ofBitVec (slot ||| 2),rbx:=0}) := by
  obtain ⟨oldParent,parentRead⟩ := Option.isSome_iff_exists.mp parentMapped
  obtain ⟨oldRoot,rootRead⟩ := Option.isSome_iff_exists.mp rootMapped
  simp [Placement.physical,Add.r4d6,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    parentMemory,rootMemory] at saved parentRead rootRead ⊢
  rw [saved]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat]
  rw [parentRead]
  simp only [Effects.All]
  have slotMod : (slot.toNat : Int)%18446744073709551616=slot.toNat :=
    Int.emod_eq_of_lt (by omega) (by have := slot.isLt; omega)
  simp only [slotMod,Int.toNat_natCast,AllowedipsChild.ofInt_bmod64,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rw [rootRead]
  simp [Effects.All,Add.entry]
  all_goals rfl

def first4Memory (s : MachineData) (word : BitVec 32) : DataMem :=
  s.dmem.storeInt (s.regs.rbx.toBitVec+32) 4 word.toInt

def copied4Memory (s : MachineData) (first again : BitVec 32) : DataMem :=
  (first4Memory s first).storeInt (s.regs.rbx.toBitVec+32) 4 again.toInt

theorem stored32 (v : BitVec 32) :
    ((max ((v.toNat : Int)%4294967296) 0%18446744073709551616).bmod 4294967296)=v.toInt := by
  have small := v.isLt
  have mod32 : (v.toNat : Int)%4294967296=v.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  have mod64 : (v.toNat : Int)%18446744073709551616=v.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [mod32,show max (v.toNat : Int) 0=v.toNat from by omega,mod64,BitVec.toInt_eq_toNat_bmod]

/-- The compiler copies the same IPv4 word twice. The second read is from
the first store's memory, rather than an extra disjointness assumption. -/
theorem copy4 (s : MachineData) (first again : BitVec 32)
    (size : s.regs.rax=4) (dest : s.regs.rsi.toBitVec=s.regs.rbx.toBitVec+32)
    (readFirst : s.dmem.loadInt s.regs.r13.toBitVec 4=some first.toNat)
    (firstMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+32) 4).isSome=true)
    (readAgain : (first4Memory s first).loadInt s.regs.r13.toBitVec 4=some again.toNat)
    (againMapped : ((first4Memory s first).loadInt (s.regs.rbx.toBitVec+32) 4).isSome=true) :
    (Placement.physical Add.r757 0x757 s).All (fun t =>
      t.pc=Add.entry+0x4d6 ∧ t.data.dmem=copied4Memory s first again ∧
      t.data.regs={s.regs with rdx:=.ofBitVec (again.setWidth 64)}) := by
  obtain ⟨oldFirst,firstRead⟩ := Option.isSome_iff_exists.mp firstMapped
  obtain ⟨oldAgain,againRead⟩ := Option.isSome_iff_exists.mp againMapped
  simp [Placement.physical,Add.r757,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    first4Memory,copied4Memory,size] at readFirst firstRead readAgain againRead ⊢
  rw [readFirst]
  simp only [Effects.All,AllowedipsChild.extract32]
  rw [firstRead]
  simp only [Effects.All,stored32,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero,dest]
  rw [readAgain]
  simp only [Effects.All]
  rw [againRead]
  simp [Effects.All,Add.entry,stored32]
  all_goals rfl

#print axioms connect
#print axioms copy4
end Binary.Pair.Allowedips.Root
