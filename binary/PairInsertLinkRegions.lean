import PairInsertRegions

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

def linkStoreCode (address value : Reg64) : List (Kraken.Sized Directive) :=
  [⟨.instr (.regular .W64 .W64 (.mov
    (.mem {base := some (.reg address),idx := none,disp := (8 : Int64)})
    (.regOrMem (.reg (.low value .W64))))),4⟩]

theorem link_store_generic (address value : Reg64) (pc : Int64) (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.get64 address+8) 8=some old) :
    (Directives.interp (linkStoreCode address value) s pc (fun pc data => .done ⟨data,pc⟩)).All
      (fun t => t.data.regs=s.regs ∧
        t.data.dmem=s.dmem.storeInt (s.regs.get64 address+8) 8 (s.regs.get64 value).toInt ∧ t.pc=pc+4) := by
  simp [linkStoreCode,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at mapped ⊢
  rw [mapped]
  simp [Effects.All]

theorem unlink_successor (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.r13.toBitVec+8) 8=some old) :
    (run IndexInsertImage.Insert.r3e 0x3e s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem.storeInt (s.regs.r13.toBitVec+8) 8 s.regs.rbx.toBitVec.toInt ∧
      t.pc=codeEntry+0x42) := by
  change (Directives.interp (linkStoreCode .r13 .rbx) s (codeEntry+0x3e)
    (fun pc data => .done ⟨data,pc⟩)).All _
  simpa only [Reg64s.get64,Int64.add_assoc,show (0x3e : Int64)+4=0x42 by decide +kernel]
    using link_store_generic .r13 .rbx (codeEntry+0x3e) s old mapped

theorem prepend_successor (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some old) :
    (run IndexInsertImage.Insert.r157 0x157 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+8) 8 s.regs.r13.toBitVec.toInt ∧
      t.pc=codeEntry+0x15b) := by
  change (Directives.interp (linkStoreCode .rbx .r13) s (codeEntry+0x157)
    (fun pc data => .done ⟨data,pc⟩)).All _
  simpa only [Reg64s.get64,Int64.add_assoc,show (0x157 : Int64)+4=0x15b by decide +kernel]
    using link_store_generic .rbx .r13 (codeEntry+0x157) s old mapped

#print axioms unlink_successor
#print axioms prepend_successor
end Binary.Pair.Insert
