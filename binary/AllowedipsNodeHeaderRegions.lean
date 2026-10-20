import AllowedipsNodeAttachChecked

namespace Binary.Pair.Allowedips.NodeInit
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

def selector (width cidr : Nat) : Nat := (cidr/8) ^^^ ((width/8-1)%8)

private theorem selector_registers : ∀ family : Bool, ∀ value : Fin 129,
    let cidr := value.val
    let mask : BitVec 64 := if family then 3 else 7
    let original := (BitVec.extractLsb' 0 32 (UInt64.ofNat cidr).toBitVec).setWidth 64
    let shifted := (BitVec.extractLsb' 0 32
      (original.replaceLow (BitVec.extractLsb' 0 8 original >>> 3))).setWidth 64
    (UInt64.ofBitVec shifted=UInt64.ofNat (cidr/8)) ∧
    (UInt64.ofBitVec ((BitVec.extractLsb' 0 32 (shifted ^^^ mask)).setWidth 64)=
      UInt64.ofNat (cidr/8) ^^^ UInt64.ofBitVec mask) ∧
    (~~~BitVec.extractLsb' 0 32 original).setWidth 64=(~~~BitVec.ofNat 32 cidr).setWidth 64 := by
  decide +kernel

theorem header_first (s : MachineData) (width cidr : Nat)
    (family : width=32 ∨ width=128) (bound : cidr≤width)
    (mask : s.regs.rax=.ofNat ((width/8-1)%8)) (requested : s.regs.rdi=.ofNat cidr)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+36) 1).isSome=true) :
    (Placement.physical Add.r198 0x198 s).All (fun t =>
      t.pc=Add.entry+0x1ab ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec+36) 1 (BitVec.ofNat 8 ((width/8-1)%8)).toInt ∧
      t.data.regs={s.regs with
        rax:=.ofNat (selector width cidr),rcx:=.ofNat (selector width cidr),
        rdx:=.ofBitVec ((~~~BitVec.ofNat 32 cidr).setWidth 64)}) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r198,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,mask,requested] at read ⊢
  rw [read]
  rcases family with rfl|rfl <;> simp [Effects.All,Add.entry,selector]
  · exact selector_registers true ⟨cidr,by omega⟩
  · exact selector_registers false ⟨cidr,by omega⟩

def selectorMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt (s.regs.rsp.toBitVec+43) 1 (s.regs.get (.low .rax .W8)).toInt

private theorem header_registers : ∀ family : Bool, ∀ value : Fin 129,
    let cidr := value.val
    let mask : UInt64 := if family then 3 else 7
    let low := (BitVec.extractLsb' 0 8 (UInt64.ofNat cidr).toBitVec).setWidth 64
    (((((4294967295-cidr%4294967296)%4294967296%18446744073709551616 &&& 7) : Nat) : Int).bmod 256=
      (BitVec.ofNat 8 (7-cidr%8)).toInt) ∧
    (UInt64.ofBitVec (low.replaceLow
      (BitVec.extractLsb' 0 8 ((UInt64.ofNat (cidr/8)).toBitVec ^^^ mask.toBitVec) ++
        BitVec.extractLsb' 0 8 low))=
      UInt64.ofNat cidr+(mask ^^^ UInt64.ofNat (cidr/8))*256) ∧
    (UInt64.ofBitVec ((BitVec.extractLsb' 0 32
      ((BitVec.extractLsb' 0 32 ((~~~BitVec.ofNat 32 cidr).setWidth 64)).setWidth 64 &&& 7) <<< 16).setWidth 64)=
      UInt64.ofNat (7-cidr%8)*65536) := by
  decide +kernel

theorem header_second (s : MachineData) (width cidr : Nat)
    (family : width=32 ∨ width=128) (bound : cidr≤width)
    (index : s.regs.rax=.ofNat (selector width cidr))
    (copy : s.regs.rcx=.ofNat (selector width cidr))
    (shift : s.regs.rdx=.ofBitVec ((~~~BitVec.ofNat 32 cidr).setWidth 64))
    (requested : s.regs.r12=.ofNat cidr)
    (firstMapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+43) 1).isSome=true)
    (secondMapped : ((selectorMemory s).loadInt (s.regs.rsp.toBitVec+44) 1).isSome=true) :
    (Placement.physical Add.r1ab 0x1ab s).All (fun t =>
      t.pc=Add.entry+0x1c4 ∧
      t.data.dmem=(selectorMemory s).storeInt (s.regs.rsp.toBitVec+44) 1
        (BitVec.ofNat 8 (7-cidr%8)).toInt ∧
      t.data.regs={s.regs with
        rax:=.ofNat (headerLow width cidr),rdx:=.ofNat ((7-cidr%8)*65536)}) := by
  obtain ⟨firstOld,firstRead⟩ := Option.isSome_iff_exists.mp firstMapped
  obtain ⟨secondOld,secondRead⟩ := Option.isSome_iff_exists.mp secondMapped
  simp [Placement.physical,Add.r1ab,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,index,copy,shift,requested,selectorMemory]
    at firstRead secondRead ⊢
  rw [firstRead]
  simp only [Effects.All]
  rw [secondRead]
  rcases family with rfl|rfl <;> simp [Effects.All,Add.entry,selector,headerLow]
  · have facts := header_registers true ⟨cidr,by omega⟩
    refine ⟨?_,facts.2⟩
    rw [facts.1]
  · have facts := header_registers false ⟨cidr,by omega⟩
    refine ⟨?_,facts.2⟩
    rw [facts.1]

#print axioms header_first
#print axioms header_second
end Binary.Pair.Allowedips.NodeInit
