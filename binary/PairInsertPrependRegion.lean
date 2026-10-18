import PairInsertNestedRegion

namespace Binary.Pair.Insert
local instance : Labels := Image.linkedLabels

def prependSetup := IndexInsertImage.Insert.r136.take 3
def prependBack := (IndexInsertImage.Insert.r136.drop 3).take 1
def prependNext := (IndexInsertImage.Insert.r136.drop 4).take 1
def prependRoot := (IndexInsertImage.Insert.r136.drop 5).take 1
def prependTest := IndexInsertImage.Insert.r136.drop 6

set_option maxRecDepth 2048 in
theorem prepend_setup_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0x136) prependSetup := by binary_layout
set_option maxRecDepth 2048 in
theorem prepend_back_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0x142) prependBack := by binary_layout
set_option maxRecDepth 2048 in
theorem prepend_next_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0x146) prependNext := by binary_layout
set_option maxRecDepth 2048 in
theorem prepend_root_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0x14a) prependRoot := by binary_layout
set_option maxRecDepth 2048 in
theorem prepend_test_layout : LaidOut IndexInsertImage.Insert.fetch (codeEntry+0x14d) prependTest := by binary_layout

def prependRootAddress (s : MachineData) : BitVec 64 := s.regs.r12.toBitVec+s.regs.r14.toBitVec*8

theorem prepend_setup (s : MachineData) (head : UInt64)
    (read : s.dmem.loadInt (prependRootAddress s) 8=some head.toNat) :
    (run prependSetup 0x136 s).All (fun t =>
      t.data.regs={s.regs with
        rbx := head,rax := .ofBitVec (prependRootAddress s),r13 := s.regs.rbp+8} ∧
      t.data.dmem=s.dmem ∧ t.pc=codeEntry+0x142) := by
  simp [run,prependSetup,IndexInsertImage.Insert.r136,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,AddrExpr.interp,
    Reg64s.get64,Reg64s.set,Reg64s.set64,BitVec.take,
    ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_add,BitVec.ofInt_mul,
    BitVec.ofInt_toInt,BitVec.ofInt_ofNat,Effects.All,prependRootAddress,
    codeEntry,IndexInsertImage.Insert.entry] at read ⊢
  rw [read]
  simp [Effects.All]

def pointerStoreCode (base value : Reg64) (displacement : Int64) (size : Nat) : List (Kraken.Sized Directive) :=
  [⟨.instr (.regular .W64 .W64 (.mov
    (.mem {base := some (.reg base),idx := none,disp := displacement})
    (.regOrMem (.reg (.low value .W64))))),size⟩]

theorem pointer_store (base value : Reg64) (displacement pc : Int64) (size : Nat)
    (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.get64 base+displacement.toBitVec) 8=some old) :
    (Directives.interp (pointerStoreCode base value displacement size) s pc (fun pc data => .done ⟨data,pc⟩)).All
      (fun t => t.data.regs=s.regs ∧
        t.data.dmem=s.dmem.storeInt (s.regs.get64 base+displacement.toBitVec) 8 (s.regs.get64 value).toInt ∧
        t.pc=pc+.ofNat size) := by
  simp [pointerStoreCode,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,Effects.All] at mapped ⊢
  rw [mapped]
  simp [Effects.All]

theorem prepend_back (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbp.toBitVec+16) 8=some old) :
    (run prependBack 0x142 s).All (fun t => t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rbp.toBitVec+16) 8 s.regs.rax.toBitVec.toInt ∧ t.pc=codeEntry+0x146) := by
  change (Directives.interp (pointerStoreCode .rbp .rax 16 4) s (codeEntry+0x142)
    (fun pc data => .done ⟨data,pc⟩)).All _
  simpa only [Reg64s.get64,show (16 : Int64).toBitVec=16 by decide +kernel,Int64.add_assoc,show (0x142 : Int64)+.ofNat 4=0x146 by decide +kernel]
    using pointer_store .rbp .rax 16 (codeEntry+0x142) 4 s old mapped

theorem prepend_next (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rbp.toBitVec+8) 8=some old) :
    (run prependNext 0x146 s).All (fun t => t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rbp.toBitVec+8) 8 s.regs.rbx.toBitVec.toInt ∧ t.pc=codeEntry+0x14a) := by
  change (Directives.interp (pointerStoreCode .rbp .rbx 8 4) s (codeEntry+0x146)
    (fun pc data => .done ⟨data,pc⟩)).All _
  simpa only [Reg64s.get64,show (8 : Int64).toBitVec=8 by decide +kernel,Int64.add_assoc,show (0x146 : Int64)+.ofNat 4=0x14a by decide +kernel]
    using pointer_store .rbp .rbx 8 (codeEntry+0x146) 4 s old mapped

theorem prepend_root (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt s.regs.rax.toBitVec 8=some old) :
    (run prependRoot 0x14a s).All (fun t => t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt s.regs.rax.toBitVec 8 s.regs.r13.toBitVec.toInt ∧ t.pc=codeEntry+0x14d) := by
  simp [run,prependRoot,IndexInsertImage.Insert.r136,Directives.interp,Directive.interp,
    Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
    ConstExpr.interp,BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_toInt,Effects.All,
    codeEntry,IndexInsertImage.Insert.entry,mapped]

theorem prepend_test (s : MachineData) :
    (run prependTest 0x14d s).All (fun t => t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if s.regs.rbx.toBitVec=0 then codeEntry+0x15b else codeEntry+0x152)) := by
  change (Directives.interp (testCode "L_ffffffff813a02fb") s (codeEntry+0x14d)
    (fun pc data => .done ⟨data,pc⟩)).All _
  have target : label "L_ffffffff813a02fb"=codeEntry+0x15b := by decide +kernel
  simpa only [target,Int64.add_assoc,show (0x14d : Int64)+5=0x152 by decide +kernel]
    using guard_generic "L_ffffffff813a02fb" (codeEntry+0x14d) s

#print axioms prepend_setup
#print axioms pointer_store
#print axioms prepend_back
#print axioms prepend_next
#print axioms prepend_root
#print axioms prepend_test
end Binary.Pair.Insert
