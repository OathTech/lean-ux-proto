import AllowedipsRootEffect
import PairAllowedipsReturn

namespace Binary.Pair.Allowedips.Return
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem addPrefix (s : MachineData) (bx bp r12 r13 r14 r15 : UInt64)
    (h0 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8=some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+56) 8=some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+64) 8=some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+72) 8=some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+80) 8=some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+88) 8=some r15.toNat) :
    (Placement.physical Add.r54e 0x54e s).All (fun t =>
      t.data.regs={s.regs with
        rax:=.ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rbx:=bx,rbp:=bp,r12,r13,r14,r15,rsp:=s.regs.rsp+96} ∧
      t.data.dmem=s.dmem ∧ t.pc=Add.entry+0x55e) := by
  have add48 (x : BitVec 64) : 48+x=x+48 := BitVec.add_comm _ _
  have add48u (x : UInt64) : 48+x=x+48 := UInt64.add_comm _ _
  simp [Placement.physical,Add.r54e,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,
    ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.signed,
    Effects.All,Add.entry,UInt64.toBitVec_add,UInt64.ofBitVec_add,
    BitVec.add_assoc,add48u]
  simp_all [Effects.All]
  decide

/-- One return instruction, reusable at all three actual image sites. -/
theorem ret (s : MachineData) (pc : Int64) (ra : UInt64)
    (read : s.dmem.loadInt s.regs.rsp.toBitVec 8=some ra.toNat) :
    (Directives.interp Add.r55e s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs={s.regs with rsp:=s.regs.rsp+8} ∧ t.data.dmem=s.dmem ∧
      t.pc=.ofBitVec ra.toBitVec) := by
  simp [Add.r55e,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    MachineData.load,Reg64s.get64,Reg64s.set64,Effects.All,read]

def wrapperCode (v4 : Bool) := if v4 then Insert4.r42 else Insert6.r4f

theorem wrapper_adjust (v4 : Bool) (s : MachineData) (pc : Int64) :
    (Directives.interp ((wrapperCode v4).take 1) s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs={s.regs with rsp:=s.regs.rsp+.ofNat (if v4 then 8 else 16)} ∧
      t.data.dmem=s.dmem ∧ t.pc=pc+4) := by
  cases v4 <;>
    simp [wrapperCode,Insert4.r42,Insert6.r4f,Directives.interp,Directive.interp,
      Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
      MachineData.set,MachineData.setReg,ConstExpr.interp,
      Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
      BitVec.take,BitVec.drop,Effects.All,UInt64.add_comm]

/-- The common four-pop suffix of both public wrappers. -/
theorem wrapper_pop (s : MachineData) (pc : Int64) (bx bp r12 r13 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8=some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8=some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8=some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some r13.toNat) :
    (Directives.interp (Insert4.r42.drop 1 |>.take 4) s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs={s.regs with rbx:=bx,rbp:=bp,r12,r13,rsp:=s.regs.rsp+32} ∧
      t.data.dmem=s.dmem ∧ t.pc=pc+6) := by
  simp [Insert4.r42,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    MachineData.load,MachineData.set,MachineData.setReg,Reg64s.set,Reg64s.get64,Reg64s.set64,Effects.All,
    UInt64.toBitVec_add,BitVec.add_assoc,h0,Int64.add_assoc]
  simp_all [Effects.All]
  decide

#print axioms addPrefix
#print axioms ret
#print axioms wrapper_adjust
#print axioms wrapper_pop
end Binary.Pair.Allowedips.Return
