import PairInsertWalkRegions

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

def compareCode (other : Reg64) (target : Label) : List (Kraken.Sized Directive) :=
  [⟨.instr (.regular .W64 .W32 (.cmp (.reg (.low .r13 .W32)) (.regOrMem (.reg (.low other .W32))))),3⟩,
   ⟨.instr (.regular .W64 .W64 (.jcc .z target)),2⟩]

private theorem compare_nat (a b : BitVec 32) : (a-b==0#32)=(a.toNat==b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add,BitVec.toNat_inj]

theorem compare_generic (other : Reg64) (target : Label) (pc : Int64) (s : MachineData) :
    (Directives.interp (compareCode other target) s pc (fun pc data => .done ⟨data,pc⟩)).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if (s.regs.get (.low .r13 .W32)).toNat==(s.regs.get (.low other .W32)).toNat
        then label target else pc+5)) := by
  simp [compareCode,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Effects.All,StatusFlags.from_result,CondCode.interp,
    compare_nat,Int64.add_assoc]
  split <;> simp_all [Effects.All]

theorem first_compare (s : MachineData) :
    (run IndexInsertImage.Insert.rb4 0xb4 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if (s.regs.get (.low .r13 .W32)).toNat==(s.regs.get (.low .r14 .W32)).toNat
        then codeEntry+0x6f else codeEntry+0xb9)) := by
  change (Directives.interp (compareCode .r14 "L_ffffffff813a020f") s (codeEntry+0xb4)
    (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a020f"=codeEntry+0x6f := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0xb4 : Int64)+5=0xb9 by decide +kernel]
    using compare_generic .r14 "L_ffffffff813a020f" (codeEntry+0xb4) s

theorem second_compare (s : MachineData) :
    (run IndexInsertImage.Insert.r119 0x119 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if (s.regs.get (.low .r13 .W32)).toNat==(s.regs.get (.low .r15 .W32)).toNat
        then codeEntry+0x18f else codeEntry+0x11e)) := by
  change (Directives.interp (compareCode .r15 "L_ffffffff813a032f") s (codeEntry+0x119)
    (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a032f"=codeEntry+0x18f := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0x119 : Int64)+5=0x11e by decide +kernel]
    using compare_generic .r15 "L_ffffffff813a032f" (codeEntry+0x119) s

#print axioms first_compare
#print axioms second_compare
end Binary.Pair.Insert
