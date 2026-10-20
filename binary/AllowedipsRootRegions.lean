import AllowedipsExactTotal
import PairAllowedipsRoot

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def ownerMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt s.regs.rbx.toBitVec 8 s.regs.r14.toBitVec.toInt

def headMemory (s : MachineData) : DataMem :=
  (ownerMemory s).storeInt (s.regs.r14.toBitVec+1104) 8 (s.regs.rbx.toBitVec+56).toInt

def forwardMemory (s : MachineData) : DataMem :=
  (headMemory s).storeInt (s.regs.rbx.toBitVec+56) 8 (s.regs.r14.toBitVec+1096).toInt

/-- First eight instructions after a successful empty-root allocation. All
read and write premises refer to the memory at their actual execution time. -/
theorem attach_first (s : MachineData) (cidr : BitVec 32) (last : BitVec 64)
    (ownerMapped : (s.dmem.loadInt s.regs.rbx.toBitVec 8).isSome=true)
    (cidrRead : (ownerMemory s).loadInt (s.regs.rsp.toBitVec+16) 4=some cidr.toNat)
    (tailRead : (ownerMemory s).loadInt (s.regs.r14.toBitVec+1104) 8=some last.toNat)
    (forwardMapped : ((headMemory s).loadInt (s.regs.rbx.toBitVec+56) 8).isSome=true) :
    (Placement.physical Add.r443 0x443 s).All (fun t =>
      t.pc=Add.entry+0x469 ∧ t.data.dmem=forwardMemory s ∧
      t.data.regs={s.regs with
        rdx:=.ofBitVec (s.regs.rbx.toBitVec+56),rdi:=.ofBitVec (cidr.setWidth 64),
        rax:=.ofBitVec last,r14:=.ofBitVec (s.regs.r14.toBitVec+1096),rsi:=.ofBitVec (cidr.setWidth 64)}) := by
  obtain ⟨oldOwner,ownerRead⟩ := Option.isSome_iff_exists.mp ownerMapped
  obtain ⟨oldForward,forwardRead⟩ := Option.isSome_iff_exists.mp forwardMapped
  simp [Placement.physical,Add.r443,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ownerMemory,headMemory,forwardMemory] at ownerRead cidrRead tailRead forwardRead ⊢
  rw [ownerRead]
  simp only [Effects.All]
  rw [cidrRead]
  simp only [Effects.All]
  rw [tailRead]
  simp only [Effects.All]
  rw [forwardRead]
  simp [Effects.All,Add.entry,AllowedipsChild.extract32,UInt64.add_comm,Int.add_comm]
  all_goals rfl

#print axioms attach_first

def backwardMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt (s.regs.rbx.toBitVec+64) 8 s.regs.rax.toBitVec.toInt

def linkedMemory (s : MachineData) : DataMem :=
  (backwardMemory s).storeInt s.regs.rax.toBitVec 8 s.regs.rdx.toBitVec.toInt

private theorem cidr_registers : ∀ cidr : Fin 129,
    (UInt64.ofBitVec ((0 : BitVec 64).replaceLow
      (BitVec.extractLsb' 0 8 (UInt64.ofNat cidr.val).toBitVec))=UInt64.ofNat cidr.val) ∧
    (UInt64.ofBitVec ((UInt64.ofNat cidr.val).toBitVec.replaceLow
      (BitVec.extractLsb' 0 8 (UInt64.ofNat cidr.val).toBitVec >>> 3))=
      UInt64.ofNat (cidr.val/8)) := by
  decide +kernel

theorem attach_second (s : MachineData) (width cidr : Nat)
    (family : width=32 ∨ width=128) (bound : cidr≤width)
    (bits : s.regs.rbp=.ofNat width) (requested : s.regs.rdi=.ofNat cidr)
    (copied : s.regs.rsi=.ofNat cidr)
    (backMapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+64) 8).isSome=true)
    (lastMapped : ((backwardMemory s).loadInt s.regs.rax.toBitVec 8).isSome=true) :
    (Placement.physical Add.r469 0x469 s).All (fun t =>
      t.pc=Add.entry+0x481 ∧ t.data.dmem=linkedMemory s ∧
      t.data.regs={s.regs with
        rsi:=.ofNat (cidr/8),rax:=.ofNat (width/8),rdx:=.ofNat cidr,rcx:=.ofNat (width/8-1)}) := by
  obtain ⟨oldBack,backRead⟩ := Option.isSome_iff_exists.mp backMapped
  obtain ⟨oldLast,lastRead⟩ := Option.isSome_iff_exists.mp lastMapped
  have regs := cidr_registers ⟨cidr,by rcases family with h|h <;> omega⟩
  simp [Placement.physical,Add.r469,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,
    backwardMemory,linkedMemory,bits,requested,copied] at backRead lastRead ⊢
  rw [backRead]
  simp only [Effects.All]
  rw [lastRead]
  simp only [Effects.All]
  rcases family with rfl|rfl <;> simp [Add.entry]
  all_goals exact ⟨by decide,by decide,regs⟩

#print axioms attach_second
end Binary.Pair.Allowedips.Root
