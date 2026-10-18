import PairInsertRegions

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

/-- Both walks have this identical pointer-adjustment/CALL segment.
The correspondence point is after the callback; the subtraction alone
need not reestablish the data relation. -/
theorem cursor_call (offset : Nat) (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (run IndexInsertImage.Insert.r92 offset s).All (fun t =>
      t.data.regs={s.regs with rbx := s.regs.rbx-8,rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (codeEntry+.ofNat offset+9).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810f3100) := by
  simp [run,IndexInsertImage.Insert.r92,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.store,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,RelRegOrMem.interp,ConstExpr.interp,
    Effects.All,Width.bytesv,Int64.add_assoc] at mapped ⊢
  rw [mapped]
  simp only [Effects.All]
  refine ⟨trivial,trivial,?_⟩
  rw [← Int64.add_assoc, ← Int64.add_assoc, Int64.add_comm]
  simp only [Int64.add_assoc, Int64.sub_add_cancel]
  decide +kernel

theorem locked_cursor_same : IndexInsertImage.Insert.rf7=IndexInsertImage.Insert.r92 := rfl

def testCode (target : Label) : List (Kraken.Sized Directive) :=
  [⟨.instr (.regular .W64 .W64 (.test (.reg (.low .rbx .W64)) (.regOrMem (.reg (.low .rbx .W64))))),3⟩,
   ⟨.instr (.regular .W64 .W64 (.jcc .z target)),2⟩]
theorem guard_generic (target : Label) (pc : Int64) (s : MachineData) :
    (Directives.interp (testCode target) s pc (fun pc data => .done ⟨data,pc⟩)).All
      (fun t => t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
        t.pc=(if s.regs.rbx.toBitVec=0 then label target else pc+5)) := by
  simp [testCode,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.drop,BitVec.take,Effects.All,StatusFlags.from_result,CondCode.interp,Int64.add_assoc]
  split <;> simp_all [Effects.All]

theorem first_node_guard (s : MachineData) :
    (run IndexInsertImage.Insert.r9b 0x9b s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if s.regs.rbx.toBitVec=0 then codeEntry+0xcc else codeEntry+0xa0)) := by
  change (Directives.interp (testCode "L_ffffffff813a026c") s (codeEntry+0x9b) (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a026c"=codeEntry+0xcc := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0x9b : Int64)+5=0xa0 by decide +kernel] using guard_generic "L_ffffffff813a026c" (codeEntry+0x9b) s

theorem second_node_guard (s : MachineData) :
    (run IndexInsertImage.Insert.r100 0x100 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if s.regs.rbx.toBitVec=0 then codeEntry+0x131 else codeEntry+0x105)) := by
  change (Directives.interp (testCode "L_ffffffff813a02d1") s (codeEntry+0x100) (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a02d1"=codeEntry+0x131 := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0x100 : Int64)+5=0x105 by decide +kernel] using guard_generic "L_ffffffff813a02d1" (codeEntry+0x100) s

def advanceCode (target : Label) : List (Kraken.Sized Directive) :=
  IndexInsertImage.Insert.rbe.take 2 ++ [⟨.instr (.regular .W64 .W64 (.jcc .nz target)),2⟩]

theorem advance_generic (target : Label) (pc : Int64) (s : MachineData) (next : BitVec 64)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat) :
    (Directives.interp (advanceCode target) s pc (fun pc data => .done ⟨data,pc⟩)).All (fun t =>
      t.data.regs={s.regs with rbx := .ofBitVec next} ∧ t.data.dmem=s.dmem ∧
      t.pc=(if next=0 then pc+9 else label target)) := by
  simp [advanceCode,IndexInsertImage.Insert.rbe,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Reg64s.set,Reg64s.set64,
    BitVec.drop,BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,StatusFlags.from_result,CondCode.interp,
    Int64.add_assoc] at read ⊢
  rw [read]
  simp only [Effects.All,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  split <;> simp_all [Effects.All]

theorem first_advance (s : MachineData) (next : BitVec 64)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat) :
    (run IndexInsertImage.Insert.rbe 0xbe s).All (fun t =>
      t.data.regs={s.regs with rbx := .ofBitVec next} ∧ t.data.dmem=s.dmem ∧
      t.pc=(if next=0 then codeEntry+0xc7 else codeEntry+0x8d)) := by
  change (Directives.interp (advanceCode "L_ffffffff813a022d") s (codeEntry+0xbe) (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a022d"=codeEntry+0x8d := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0xbe : Int64)+9=0xc7 by decide +kernel] using advance_generic "L_ffffffff813a022d" (codeEntry+0xbe) s next read

theorem second_advance (s : MachineData) (next : BitVec 64)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some next.toNat) :
    (run IndexInsertImage.Insert.r123 0x123 s).All (fun t =>
      t.data.regs={s.regs with rbx := .ofBitVec next} ∧ t.data.dmem=s.dmem ∧
      t.pc=(if next=0 then codeEntry+0x12c else codeEntry+0xf2)) := by
  change (Directives.interp (advanceCode "L_ffffffff813a0292") s (codeEntry+0x123) (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a0292"=codeEntry+0xf2 := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0x123 : Int64)+9=0x12c by decide +kernel] using advance_generic "L_ffffffff813a0292" (codeEntry+0x123) s next read

#print axioms cursor_call
#print axioms first_node_guard
#print axioms second_node_guard
#print axioms first_advance
#print axioms second_advance
end Binary.Pair.Insert
