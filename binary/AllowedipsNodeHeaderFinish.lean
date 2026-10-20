import AllowedipsNodeHeaderRegions

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

private theorem packed_registers : ∀ family : Bool, ∀ value : Fin 129,
    let width := if family then 32 else 128
    let cidr := value.val
    let low := (BitVec.extractLsb' 0 16 (UInt64.ofNat (headerLow width cidr)).toBitVec).setWidth 64
    let shifted := (BitVec.extractLsb' 0 32 ((UInt64.ofNat (7-cidr%8)).toBitVec*65536)).setWidth 64
    let high := (BitVec.extractLsb' 0 32
      ((BitVec.extractLsb' 0 32 (UInt64.ofNat width).toBitVec).setWidth 64) <<< 24).setWidth 64
    (UInt64.ofBitVec ((BitVec.extractLsb' 0 32
      ((BitVec.extractLsb' 0 32 low).setWidth 64 ||| shifted)).setWidth 64) |||
      UInt64.ofBitVec ((BitVec.extractLsb' 0 32 high).setWidth 64)=UInt64.ofNat (headerWord width cidr)) ∧
    UInt64.ofBitVec high=UInt64.ofNat width*16777216 := by
  decide +kernel

theorem header_pack (s : MachineData) (width cidr : Nat)
    (family : width=32 ∨ width=128) (bound : cidr≤width)
    (low : s.regs.rax=.ofNat (headerLow width cidr))
    (shift : s.regs.rdx=.ofNat ((7-cidr%8)*65536)) (bits : s.regs.r15=.ofNat width) :
    (Placement.physical (Add.r1c4.take 5) 0x1c4 s).All (fun t =>
      t.pc=Add.entry+0x1d1 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with rax:=.ofNat (headerWord width cidr),rcx:=.ofNat (width*16777216)}) := by
  simp [Placement.physical,Add.r1c4,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
    ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,ShiftCountExpr.interpMasked,ShiftCountExpr.interp,
    low,shift,bits,Add.entry]
  rcases family with rfl|rfl
  · exact packed_registers true ⟨cidr,by omega⟩
  · exact packed_registers false ⟨cidr,by omega⟩

theorem header_finish (s : MachineData) (value : BitVec 32) (width : Nat)
    (family : width=32 ∨ width=128) (bytes : s.regs.rbp=.ofNat (width/8))
    (packed : s.regs.rax=.ofBitVec (value.setWidth 64))
    (mapped : (s.dmem.loadInt (s.regs.r8.toBitVec+24) 4).isSome=true) :
    (Placement.physical (Add.r1c4.drop 5) 0x1d1 s).All (fun t =>
      t.pc=(if width=32 then Add.entry+0x1de else Add.entry+0x4ed) ∧
      t.data.dmem=s.dmem.storeInt (s.regs.r8.toBitVec+24) 4 value.toInt ∧ t.data.regs=s.regs) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r1c4,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,AddrExpr.interp,ConstExpr.interp,
    Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_add,BitVec.ofInt_toInt,BitVec.ofInt_ofNat,
    Effects.All,StatusFlags.from_result,CondCode.interp,packed,bytes,AllowedipsChild.extract32] at read ⊢
  rw [read]
  rcases family with rfl|rfl <;> simp [Effects.All,Add.entry,BitVec.unsigned]
  all_goals rfl

#print axioms header_pack
#print axioms header_finish
end Binary.Pair.Allowedips.NodeInit
