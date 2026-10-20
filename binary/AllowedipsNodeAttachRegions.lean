import AllowedipsRootRegions
import PairAllowedipsNodeInit

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem first (s : MachineData) (base : BitVec 64) (cidr : BitVec 32) (last : BitVec 64)
    (width : Nat) (family : width=32 ∨ width=128) (bits : s.regs.rbp=.ofNat width)
    (allocation : s.dmem.loadInt s.regs.rsp.toBitVec 8=some base.toNat)
    (requested : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 4=some cidr.toNat)
    (tailRead : s.dmem.loadInt (s.regs.r14.toBitVec+1104) 8=some last.toNat)
    (ownerMapped : (s.dmem.loadInt base 8).isSome=true) :
    (Placement.physical Add.r156 0x156 s).All (fun t =>
      t.pc=Add.entry+0x17a ∧
      t.data.dmem=s.dmem.storeInt base 8 s.regs.r14.toBitVec.toInt ∧
      t.data.regs={s.regs with
        r8:=.ofBitVec base,r9:=.ofNat (width/8),rdi:=.ofBitVec (cidr.setWidth 64),
        rax:=.ofBitVec last,rdx:=.ofBitVec (base+56),r14:=.ofBitVec (s.regs.r14.toBitVec+1096)}) := by
  obtain ⟨oldOwner,ownerRead⟩ := Option.isSome_iff_exists.mp ownerMapped
  simp [Placement.physical,Add.r156,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,bits] at allocation requested tailRead ownerRead ⊢
  rw [allocation]
  simp only [Effects.All]
  rw [requested]
  simp only [Effects.All]
  rw [tailRead]
  simp only [Effects.All,AllowedipsChild.ofInt_bmod64,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rw [ownerRead]
  rcases family with rfl|rfl <;> simp [Effects.All,Add.entry,UInt64.add_comm]
  all_goals rfl

def headMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt (s.regs.r14.toBitVec+8) 8 s.regs.rdx.toBitVec.toInt

def backMemory (s : MachineData) : DataMem :=
  (headMemory s).storeInt (s.regs.r8.toBitVec+64) 8 s.regs.rax.toBitVec.toInt

def forwardMemory (s : MachineData) : DataMem :=
  (backMemory s).storeInt (s.regs.r8.toBitVec+56) 8 s.regs.r14.toBitVec.toInt

def linkedMemory (s : MachineData) : DataMem :=
  (forwardMemory s).storeInt s.regs.rax.toBitVec 8 s.regs.rdx.toBitVec.toInt

theorem second (s : MachineData) (bytes : Nat) (family : bytes=4 ∨ bytes=16)
    (count : s.regs.r9=.ofNat bytes)
    (headMapped : (s.dmem.loadInt (s.regs.r14.toBitVec+8) 8).isSome=true)
    (backMapped : ((headMemory s).loadInt (s.regs.r8.toBitVec+64) 8).isSome=true)
    (forwardMapped : ((backMemory s).loadInt (s.regs.r8.toBitVec+56) 8).isSome=true)
    (tailMapped : ((forwardMemory s).loadInt s.regs.rax.toBitVec 8).isSome=true) :
    (Placement.physical Add.r17a 0x17a s).All (fun t =>
      t.pc=Add.entry+0x198 ∧ t.data.dmem=linkedMemory s ∧
      t.data.regs={s.regs with
        rbp:=.ofNat bytes,r14:=.ofBitVec (s.regs.r8.toBitVec+32),rax:=.ofNat ((bytes-1)%8)}) := by
  obtain ⟨oldHead,headRead⟩ := Option.isSome_iff_exists.mp headMapped
  obtain ⟨oldBack,backRead⟩ := Option.isSome_iff_exists.mp backMapped
  obtain ⟨oldForward,forwardRead⟩ := Option.isSome_iff_exists.mp forwardMapped
  obtain ⟨oldTail,tailRead⟩ := Option.isSome_iff_exists.mp tailMapped
  simp [Placement.physical,Add.r17a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    headMemory,backMemory,forwardMemory,linkedMemory,count] at headRead backRead forwardRead tailRead ⊢
  rw [headRead]
  simp only [Effects.All]
  rw [backRead]
  simp only [Effects.All]
  rw [forwardRead]
  simp only [Effects.All]
  rw [tailRead]
  rcases family with rfl|rfl <;> simp [Effects.All,Add.entry] <;> decide

#print axioms first
#print axioms second
end Binary.Pair.Allowedips.NodeInit
