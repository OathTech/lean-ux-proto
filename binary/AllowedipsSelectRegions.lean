import PairAllowedipsSelect
import AllowedipsPlacementChild

namespace Binary.Pair.Allowedips.Select
open AllowedipsMutationImage AllowedipsChild
local instance : Labels := Image.linkedLabels

private theorem selected_word (byte shift : Nat) (small : byte<256) :
    (UInt64.ofBitVec (((BitVec.ofNat 32 byte).sshiftRight shift).setWidth 64) &&& 1)=
      UInt64.ofNat (selected byte shift) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toBitVec_and,UInt64.toBitVec_ofNat,
    BitVec.toNat_and,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  change (((BitVec.ofNat 32 byte).sshiftRight shift).toNat%2^64 &&& 1)=selected byte shift%2^64
  rw [Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide : 2^32<2^64))]
  rw [show (1 : Nat)=2^1-1 from rfl,Nat.and_two_pow_sub_one_eq_mod,shift_mod byte shift small]
  exact (Nat.mod_eq_of_lt (by unfold selected; omega)).symm

theorem select_step (s : MachineData) (byteIndex shift byte : Nat) (base next : BitVec 64)
    (indexBound : byteIndex<16) (shiftBound : shift<8) (byteBound : byte<256)
    (old : Int) (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8=some old)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec+25) 1=some (byteIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec+26) 1=some (shift : Int))
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some base.toNat)
    (byteRead : s.dmem.loadInt (s.regs.r13.toBitVec+.ofNat 64 byteIndex) 1=some (byte : Int))
    (childRead : s.dmem.loadInt (s.regs.rbx.toBitVec+8+.ofNat 64 (8*selected byte shift)) 8=some next.toNat) :
    (Placement.physical (Add.r212++Add.r231) 0x212 s).All (fun t =>
      t.pc=(if next=0 then Add.entry+0x6e0 else Add.entry+0x241) ∧
      t.data.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 next.toInt ∧
      t.data.regs={s.regs with
        rax:=.ofNat (selected byte shift),rdx:=.ofNat (selected byte shift),
        rcx:=.ofBitVec next,r8:=.ofBitVec base}) := by
  have target : (label "L_ffffffff813a12a0" : Int64)=Add.entry+0x6e0 := by decide +kernel
  have signed : (next.toNat : Int).bmod 18446744073709551616=next.toInt :=
    (BitVec.toInt_eq_toNat_bmod next).symm
  simp at indexRead shiftRead baseRead byteRead childRead mapped
  have ix := extend8 byteIndex (by omega)
  have sh := extend8 shift (by omega)
  have by8 := extend8 byte byteBound
  change (BitVec.ofNat 8 byteIndex).setWidth 64=BitVec.ofNat 64 byteIndex at ix
  change (BitVec.ofNat 8 shift).setWidth 64=BitVec.ofNat 64 shift at sh
  change (BitVec.ofNat 8 byte).setWidth 64=BitVec.ofNat 64 byte at by8
  have shiftMask : shift%256 &&& 31=shift := by
    rw [Nat.mod_eq_of_lt (by omega),show (31 : Nat)=2^5-1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (by omega)]
  simp [Placement.physical,Add.r212,Add.r231,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,BitVec.drop,BitVec.take,
    Effects.All,ConstExpr.interp,AddrExpr.interp,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_mul,BitVec.ofInt_toInt,ix,sh,by8,extract32,low32,
    BitVec.ofInt_natCast,shiftMask,indexRead,shiftRead,baseRead,byteRead,mapped,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,StatusFlags.from_result]
  have childAddr : s.regs.rbx.toBitVec+BitVec.ofNat 64 (selected byte shift)*8+8=
      s.regs.rbx.toBitVec+8+BitVec.ofNat 64 (8*selected byte shift) := by
    rw [BitVec.ofNat_mul]
    rw [BitVec.mul_comm (BitVec.ofNat 64 (selected byte shift)) 8]
    ac_rfl
  simp at childAddr
  by_cases zero : shift=0
  all_goals try simp only [zero] at childRead childAddr
  all_goals simp [-UInt64.ofBitVec_and,Effects.All,ofInt_bmod64,zero]
  all_goals simp only [castmod64,shift_mod byte shift byteBound]
  · have eq0 : byte%2=selected byte 0 := by simp [selected]
    simp only [eq0,childAddr,childRead]
    have mask := selected_word byte 0 byteBound
    simp only [BitVec.sshiftRight_zero] at mask
    simp [Effects.All,CondCode.interp,mask,target,signed]
    split <;> simp_all [Effects.All,Add.entry]
  · simp only [childAddr,childRead]
    simp [CondCode.interp,selected_word byte shift byteBound,target,signed]
    by_cases one : shift=1 <;> simp only [one,ite_true,ite_false,Effects.All]
    all_goals repeat intro _
    all_goals by_cases empty : next=0#64 <;> simp only [empty,ite_true,ite_false,Effects.All]
    all_goals simp only [and_true]
    all_goals rfl

#print axioms select_step
end Binary.Pair.Allowedips.Select
