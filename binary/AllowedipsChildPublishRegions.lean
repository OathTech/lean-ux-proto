import PairAllowedipsChildPublish
import AllowedipsRootStore

namespace Binary.Pair.Allowedips.ChildPublish
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

private theorem increment_byte : ∀ direction : Fin 256,
    let d := direction.val
    let extended := BitVec.ofInt 64 ((max ((d : Int)%256) 0).bmod 18446744073709551616)
    let incremented := (extended+1#64).setWidth 32
    UInt64.ofBitVec ((BitVec.extractLsb' 0 8 (incremented.setWidth 64)).setWidth 64)=
      UInt64.ofNat ((d+1)%256) := by
  decide +kernel

theorem prepare (s : MachineData) (direction : BitVec 8) (base : BitVec 64)
    (directionRead : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 1=some direction.toNat)
    (baseRead : s.dmem.loadInt s.regs.rsp.toBitVec 8=some base.toNat) :
    (Placement.physical (Add.r6f2.take 4) 0x6f2 s).All (fun t =>
      t.pc=Add.entry+0x701 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with
        rdx:=.ofBitVec (direction.setWidth 64),r8:=.ofBitVec base,
        rcx:=.ofNat ((direction.toNat+1)%256)}) := by
  simp [Placement.physical,Add.r6f2,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All]
    at directionRead baseRead ⊢
  rw [directionRead]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat]
  rw [baseRead]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine ⟨rfl,True.intro,?_⟩
  congr 1
  exact increment_byte ⟨direction.toNat,direction.isLt⟩

def slot (s : MachineData) : BitVec 64 := s.regs.rbx.toBitVec+s.regs.rcx.toBitVec*8
def packed (s : MachineData) : BitVec 64 := s.regs.rdx.toBitVec ||| slot s
def parentMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt (s.regs.r8.toBitVec+48) 8 (packed s).toInt

theorem parent_store (s : MachineData) (index : BitVec 64)
    (mapped : (s.dmem.loadInt (s.regs.r8.toBitVec+48) 8).isSome=true)
    (indexRead : (parentMemory s).loadInt (s.regs.rsp.toBitVec+16) 8=some index.toNat) :
    (Placement.physical (Add.r6f2.drop 4) 0x701 s).All (fun t =>
      t.pc=Add.entry+0x711 ∧ t.data.dmem=parentMemory s ∧
      t.data.regs={s.regs with rax:=.ofBitVec index,rcx:=.ofBitVec (slot s),rdx:=.ofBitVec (packed s)}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r6f2,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_mul,BitVec.ofInt_ofNat,Effects.All,
    parentMemory,packed,slot] at oldRead indexRead ⊢
  rw [oldRead]
  simp only [Effects.All]
  rw [indexRead]
  simp [Effects.All,Add.entry]

theorem child_store (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+s.regs.rax.toBitVec*8+8) 8).isSome=true) :
    (Placement.physical Add.r711 0x711 s).All (fun t =>
      t.pc=Add.entry+0x549 ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+s.regs.rax.toBitVec*8+8) 8 s.regs.r8.toBitVec.toInt ∧
      t.data.regs={s.regs with rbx:=0}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r711,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_mul,BitVec.ofInt_ofNat,Effects.All]
    at oldRead ⊢
  rw [oldRead]
  simp [Effects.All,Add.entry]
  rfl

#print axioms prepare
#print axioms parent_store
#print axioms child_store
end Binary.Pair.Allowedips.ChildPublish
