import C1BelowInternalCopy

/-! Result C1, work package 3: `choose(node, down->bits)` for the internal
node (`add+0x31d` to `add+0x338`): the node below is reloaded from the
stack, one byte of its key is read at the node's byte selector, and `bt`
/`setb` select the bit. -/
namespace Binary.Pair.Allowedips.C1Internal
open AllowedipsMutationImage Root AllowedipsChild
local instance : Labels := Image.linkedLabels

theorem choose_region (s : MachineData) (down : BitVec 64) (byteIndex shift byte : Nat)
    (indexBound : byteIndex<16) (shiftBound : shift<8) (byteBound : byte<256)
    (downRead : s.dmem.loadInt s.regs.rsp.toBitVec 8=some down.toNat)
    (index : BitVec.extractLsb' 0 8 s.regs.rdx.toBitVec=BitVec.ofNat 8 byteIndex)
    (bit : s.regs.rcx=.ofNat shift)
    (byteRead : s.dmem.loadInt (down+32+.ofNat 64 byteIndex) 1=some (byte : Int)) :
    (Placement.physical Add.r31d 0x31d s).All (fun t =>
      t.pc=Add.entry+0x338 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with
        rdi:=.ofBitVec down,rax:=.ofNat (selected byte shift),rdx:=.ofNat (selected byte shift),
        rcx:=.ofNat (selected byte shift+1)}) := by
  have ix : (BitVec.ofNat 8 byteIndex).setWidth 64=BitVec.ofNat 64 byteIndex :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  have byteAddr : down+BitVec.ofNat 64 byteIndex+32=down+32+BitVec.ofNat 64 byteIndex := by ac_rfl
  have downEq : BitVec.ofInt 64 ((down.toNat : Int).bmod 18446744073709551616)=down := by
    rw [←BitVec.toInt_eq_toNat_bmod]
    exact BitVec.ofInt_toInt
  simp at byteAddr byteRead downRead
  obtain ⟨b,rfl⟩ : ∃ b : Fin 256, byte=b.val := ⟨⟨byte,byteBound⟩,rfl⟩
  rcases (by omega : shift=0 ∨ shift=1 ∨ shift=2 ∨ shift=3 ∨ shift=4 ∨ shift=5 ∨
    shift=6 ∨ shift=7) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp [Placement.physical,Add.r31d,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.drop,BitVec.take,Effects.All,
    ConstExpr.interp,AddrExpr.interp,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_toInt,index,bit,ix,
    ]
  all_goals rw [downRead]
  all_goals simp [Effects.All,downEq,byteAddr,byteRead,CondCode.interp,Add.entry]
  all_goals simp [Effects.All,show (Width.W32==Width.W8)=false from by decide]
  all_goals clear byteRead byteBound
  all_goals revert b
  all_goals decide +kernel

end Binary.Pair.Allowedips.C1Internal
