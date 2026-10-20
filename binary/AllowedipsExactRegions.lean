import AllowedipsPlacementRegions
import AllowedipsChild
import PairAllowedipsExact

namespace Binary.Pair.Allowedips.Exact
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- The destination tail is read after unlinking. This covers moving the last
node within its own list and moving a self-linked internal node. -/
theorem remove (s : MachineData) (previous next last : BitVec 64)
    (back : s.dmem.loadInt (s.regs.rbx.toBitVec+64) 8=some (previous.toNat : Int))
    (forward : s.dmem.loadInt (s.regs.rbx.toBitVec+56) 8=some (next.toNat : Int))
    (ownerMapped : (s.dmem.loadInt s.regs.rbx.toBitVec 8).isSome=true)
    (nextMapped : ((ownerMemory s).loadInt (next+8) 8).isSome=true)
    (previousMapped : ((nextMemory s previous next).loadInt previous 8).isSome=true)
    (tail : (removedMemory s previous next).loadInt (s.regs.r14.toBitVec+1104) 8=some (last.toNat : Int)) :
    (Placement.physical Add.r3e5 0x3e5 s).All (fun t =>
      t.pc=Add.entry+0x406 ∧ t.data.dmem=removedMemory s previous next ∧
      t.data.regs={s.regs with
        rax := .ofBitVec last,rcx := .ofBitVec next,
        rdx := .ofBitVec (s.regs.rbx.toBitVec+56),r14 := .ofBitVec (s.regs.r14.toBitVec+1096)}) := by
  obtain ⟨oldOwner,ownerRead⟩ := Option.isSome_iff_exists.mp ownerMapped
  obtain ⟨oldBack,backRead⟩ := Option.isSome_iff_exists.mp nextMapped
  obtain ⟨oldNext,nextRead⟩ := Option.isSome_iff_exists.mp previousMapped
  simp [Placement.physical,Add.r3e5,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ownerMemory,nextMemory,removedMemory] at back forward ownerRead backRead nextRead tail ⊢
  rw [back]
  simp only [Effects.All]
  rw [←BitVec.toInt_eq_toNat_bmod previous,forward]
  simp only [Effects.All]
  rw [←BitVec.toInt_eq_toNat_bmod next,ownerRead]
  simp only [Effects.All,BitVec.ofInt_toInt]
  rw [backRead]
  simp only [Effects.All]
  rw [nextRead]
  simp only [Effects.All]
  have address : BitVec.ofInt 64 ((1096+s.regs.r14.toBitVec.toInt).bmod 18446744073709551616)+8#64=
      s.regs.r14.toBitVec+1104#64 := by
    rw [AllowedipsChild.ofInt_bmod64,BitVec.ofInt_add,BitVec.ofInt_toInt]
    change (1096#64+s.regs.r14.toBitVec)+8#64=s.regs.r14.toBitVec+1104#64
    rw [BitVec.add_comm 1096#64,BitVec.add_assoc]
    rfl
  rw [address,tail]
  simp [Effects.All,Add.entry,UInt64.add_comm]

/-- The actual list_add_tail stores and success jump. All reads and writes are
against the progressively updated memory, allowing legitimate list aliases. -/
theorem append (s : MachineData)
    (headMapped : (s.dmem.loadInt (s.regs.r14.toBitVec+8) 8).isSome=true)
    (forwardMapped : ((headMemory s).loadInt (s.regs.rbx.toBitVec+56) 8).isSome=true)
    (backMapped : ((forwardMemory s).loadInt (s.regs.rbx.toBitVec+64) 8).isSome=true)
    (lastMapped : ((backwardMemory s).loadInt s.regs.rax.toBitVec 8).isSome=true) :
    (Placement.physical Add.r406 0x406 s).All (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=addedMemory s ∧
      t.data.regs={s.regs with rbx := 0}) := by
  obtain ⟨head,headRead⟩ := Option.isSome_iff_exists.mp headMapped
  obtain ⟨forward,forwardRead⟩ := Option.isSome_iff_exists.mp forwardMapped
  obtain ⟨back,backRead⟩ := Option.isSome_iff_exists.mp backMapped
  obtain ⟨last,lastRead⟩ := Option.isSome_iff_exists.mp lastMapped
  simp [Placement.physical,Add.r406,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,RelRegOrMem.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    headMemory,forwardMemory,backwardMemory,addedMemory] at headRead forwardRead backRead lastRead ⊢
  rw [headRead]
  simp only [Effects.All]
  rw [forwardRead]
  simp only [Effects.All]
  rw [backRead]
  simp only [Effects.All]
  rw [lastRead]
  simp [Effects.All,Add.entry]
  all_goals rfl

#print axioms remove
#print axioms append
end Binary.Pair.Allowedips.Exact
