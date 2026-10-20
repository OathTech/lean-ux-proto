import AllowedipsRootFinish

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def headerLow (width cidr : Nat) : Nat :=
  cidr+(((width/8-1)%8) ^^^ (cidr/8))*256

private theorem prepared_finite : ∀ family : Bool, ∀ value : Fin 129,
    let width := if family then 32 else 128
    let cidr := value.val
    (UInt64.ofBitVec ((BitVec.extractLsb' 0 8 (UInt64.ofNat (width/8)).toBitVec).setWidth 64)=
      UInt64.ofNat (width/8)) ∧
    ((~~~BitVec.extractLsb' 0 32 ((BitVec.extractLsb' 0 32 (UInt64.ofNat cidr).toBitVec).setWidth 64)).setWidth 64=
      (~~~BitVec.ofNat 32 cidr).setWidth 64) ∧
    (UInt64.ofBitVec ((UInt64.ofNat cidr).toBitVec.replaceLow
      ((BitVec.extractLsb' 0 8
        (((BitVec.extractLsb' 0 32
          (((BitVec.extractLsb' 0 32 (UInt64.ofNat (width/8-1)).toBitVec).setWidth 64) &&& 7)).setWidth 64) ^^^
            (BitVec.extractLsb' 0 32 (UInt64.ofNat (cidr/8)).toBitVec).setWidth 64)) ++
        BitVec.extractLsb' 0 8 (UInt64.ofNat cidr).toBitVec))=UInt64.ofNat (headerLow width cidr)) ∧
    (UInt64.ofBitVec ((BitVec.extractLsb' 0 32
      ((BitVec.extractLsb' 0 32 (UInt64.ofNat width).toBitVec).setWidth 64) <<< 24).setWidth 64)=
      UInt64.ofNat width*16777216) := by
  decide +kernel

theorem header_prepare (s : MachineData) (width cidr : Nat)
    (family : width=32 ∨ width=128) (bound : cidr≤width)
    (bits : s.regs.rbp=.ofNat width) (requested : s.regs.rdi=.ofNat cidr)
    (shifted : s.regs.rsi=.ofNat (cidr/8)) (index : s.regs.rcx=.ofNat (width/8-1))
    (original : s.regs.rdx=.ofNat cidr) (bytes : s.regs.rax=.ofNat (width/8)) :
    (Placement.physical Add.r481 0x481 s).All (fun t =>
      t.pc=Add.entry+0x494 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with
        rax:=.ofNat (width/8),rdx:=.ofNat (headerLow width cidr),
        rsi:=.ofNat (width*16777216),rcx:=.ofBitVec ((~~~(BitVec.ofNat 32 cidr)).setWidth 64)}) := by
  simp [Placement.physical,Add.r481,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
    ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,
    Effects.All,ShiftCountExpr.interpMasked,ShiftCountExpr.interp,
    bits,requested,shifted,index,original,bytes,Add.entry]
  rcases family with rfl|rfl
  · exact prepared_finite true ⟨cidr,by omega⟩
  · exact prepared_finite false ⟨cidr,by omega⟩

private theorem pack_finite : ∀ family : Bool, ∀ value : Fin 129,
    let width := if family then 32 else 128
    let cidr := value.val
    let shift := (BitVec.extractLsb' 0 32
      (((BitVec.extractLsb' 0 32 ((~~~BitVec.ofNat 32 cidr).setWidth 64)).setWidth 64) &&& 7) <<< 16).setWidth 64
    (UInt64.ofBitVec shift=UInt64.ofNat (7-cidr%8)*65536) ∧
    (UInt64.ofBitVec ((BitVec.extractLsb' 0 32
      ((BitVec.extractLsb' 0 32
        ((BitVec.extractLsb' 0 16 (UInt64.ofNat (headerLow width cidr)).toBitVec).setWidth 64)).setWidth 64 |||
          (BitVec.extractLsb' 0 32 shift).setWidth 64)).setWidth 64) |||
      UInt64.ofBitVec ((BitVec.extractLsb' 0 32 ((UInt64.ofNat width).toBitVec*16777216)).setWidth 64)=
        UInt64.ofNat (headerWord width cidr)) := by
  decide +kernel

theorem header_pack (s : MachineData) (width cidr : Nat)
    (family : width=32 ∨ width=128) (bound : cidr≤width)
    (low : s.regs.rdx=.ofNat (headerLow width cidr))
    (high : s.regs.rsi=.ofNat (width*16777216))
    (shift : s.regs.rcx=.ofBitVec ((~~~(BitVec.ofNat 32 cidr)).setWidth 64)) :
    (Placement.physical (Add.r494.take 5) 0x494 s).All (fun t =>
      t.pc=Add.entry+0x4a1 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with
        rdx:=.ofNat (headerWord width cidr),rcx:=.ofNat ((7-cidr%8)*65536)}) := by
  simp [Placement.physical,Add.r494,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
    ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,Effects.All,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,low,high,shift,Add.entry]
  rcases family with rfl|rfl
  · exact pack_finite true ⟨cidr,by omega⟩
  · exact pack_finite false ⟨cidr,by omega⟩

/-- Keep the memory store separate from header arithmetic so symbolic
execution does not duplicate the expanded packed value through load cases. -/
theorem header_finish (s : MachineData) (word : BitVec 32) (width : Nat)
    (family : width=32 ∨ width=128) (bytes : s.regs.rax=.ofNat (width/8))
    (value : s.regs.rdx=.ofBitVec (word.setWidth 64))
    (mapped : (s.dmem.loadInt (s.regs.rbx.toBitVec+24) 4).isSome=true) :
    (Placement.physical (Add.r494.drop 5) 0x4a1 s).All (fun t =>
      t.pc=Add.entry+0x4ab ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rbx.toBitVec+24) 4 word.toInt ∧
      t.data.regs={s.regs with rsi:=.ofBitVec (s.regs.rbx.toBitVec+32)} ∧
      t.data.status.cf=(width==32)) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r494,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    bytes,value] at read ⊢
  rw [read]
  have mod64 : (word.toNat : Int)%18446744073709551616=word.toNat :=
    Int.emod_eq_of_lt (by omega) (by have := word.isLt; omega)
  rcases family with rfl|rfl <;>
    simp [Effects.All,Add.entry,StatusFlags.from_result,BitVec.unsigned,mod64,BitVec.toInt_eq_toNat_bmod]
  all_goals rfl

theorem copy_branch (s : MachineData) :
    (Placement.physical Add.r4ab 0x4ab s).All (fun t =>
      t.data=s ∧ t.pc=(if s.status.cf then Add.entry+0x51f else Add.entry+0x4ad)) := by
  cases flag : s.status.cf <;>
    simp [Placement.physical,Add.r4ab,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    CondCode.interp,Effects.All,Add.entry,flag]
  all_goals rfl

theorem copy4_branch (s : MachineData) (size : s.regs.rax=4) :
    (Placement.physical Add.r51f 0x51f s).All (fun t =>
      t.data.dmem=s.dmem ∧ t.data.regs=s.regs ∧ t.pc=Add.entry+0x757) := by
  simp [Placement.physical,Add.r51f,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,ConstExpr.interp,CondCode.interp,Effects.All,StatusFlags.from_result,size,Add.entry]
  rfl

#print axioms header_finish
#print axioms copy_branch
#print axioms copy4_branch
#print axioms header_pack
#print axioms header_prepare
end Binary.Pair.Allowedips.Root
