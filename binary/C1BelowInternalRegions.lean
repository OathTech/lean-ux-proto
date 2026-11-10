import AllowedipsNodeCopyChecked
import AllowedipsRootRecord
import PairServiceCall
import AllowedipsStackReady
import C1BelowInternalBits

/-! Result C1, work package 3: the internal node's initialization on the
split path of `add` (`add+0x292` to `add+0x31d`), region by region. Each
lemma is the execution of one decoded region of the image from facts about
its entry state. -/
namespace Binary.Pair.Allowedips.C1Internal
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

/-- `+0x292`: reload the first node, keep the second allocation in `r12`,
and fall through when it is not NULL. -/
theorem entry_region (s : MachineData) (base : BitVec 64)
    (nonzero : s.regs.rax≠0)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some base.toNat) :
    (Placement.physical Add.r292 0x292 s).All (fun t =>
      t.pc=Add.entry+0x2a3 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with r8:=.ofBitVec base,r12:=s.regs.rax}) := by
  simp [Placement.physical,Add.r292,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp] at baseRead ⊢
  rw [baseRead]
  have nz : ¬s.regs.rax.toBitVec=0#64 := fun h => nonzero (UInt64.eq_of_toBitVec_eq h)
  simp [Effects.All,Add.entry,nz]

/-- `+0x2a3`: the first node's pointer goes back to its stack word. -/
theorem save_region (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8).isSome=true) :
    (Placement.physical (Add.r2a3.take 1) 0x2a3 s).All (fun t =>
      t.pc=Add.entry+0x2a8 ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec+24) 8 s.regs.r8.toBitVec.toInt ∧
      t.data.regs=s.regs) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r2a3,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at oldRead ⊢
  rw [oldRead]
  simp [Effects.All,Add.entry]

def listMemory (s : MachineData) : DataMem :=
  (s.dmem.storeInt (s.regs.r12.toBitVec+56) 8 (s.regs.r12.toBitVec+56).toInt).storeInt
    (s.regs.r12.toBitVec+64) 8 (s.regs.r12.toBitVec+56).toInt

theorem list_region (s : MachineData) (cidr common : Nat) (base : BitVec 64)
    (cidrBound : cidr≤128) (commonBound : common≤128)
    (commonLow : BitVec.extractLsb' 0 8 s.regs.r13.toBitVec=BitVec.ofNat 8 common)
    (cidrRead : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 1=some (cidr : Int))
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8=some base.toNat)
    (nextMapped : (s.dmem.loadInt (s.regs.r12.toBitVec+56) 8).isSome=true)
    (prevMapped : ((s.dmem.storeInt (s.regs.r12.toBitVec+56) 8 (s.regs.r12.toBitVec+56).toInt).loadInt
      (s.regs.r12.toBitVec+64) 8).isSome=true) :
    (Placement.physical Add.r2ad 0x2ad s).All (fun t =>
      t.pc=Add.entry+0x2cf ∧ t.data.dmem=listMemory s ∧
      ∃ x : BitVec 32, x.setWidth 8=BitVec.ofNat 8 (min cidr common) ∧
        t.data.regs={s.regs with
          rax:=.ofBitVec (s.regs.r12.toBitVec+56),r8:=.ofBitVec base,
          rdi:=.ofBitVec (x.setWidth 64),rdx:=.ofBitVec (x.setWidth 64)}) := by
  obtain ⟨old,oldRead⟩ := Option.isSome_iff_exists.mp nextMapped
  obtain ⟨old2,oldRead2⟩ := Option.isSome_iff_exists.mp prevMapped
  simp [Placement.physical,Add.r2ad,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp,listMemory,commonLow] at cidrRead baseRead oldRead oldRead2 ⊢
  rw [cidrRead]
  simp only [Effects.All]
  rw [baseRead]
  simp only [Effects.All]
  rw [oldRead]
  simp only [Effects.All]
  rw [oldRead2]
  simp only [Effects.All]
  simp [Add.entry,low_byte_byte,low32_wide]
  refine ⟨_,?_,rfl⟩
  have taken := below_finite ⟨cidr,by omega⟩ ⟨common,by omega⟩
  simp only at taken
  by_cases least : common≤cidr
  · rw [ite_eq_left (taken.mpr least),low_byte_word,commonLow,Nat.min_eq_right least]
  · rw [ite_eq_right (fun h => least (taken.mp h)),low_byte_word_byte,Nat.min_eq_left (by omega)]

private theorem pack_first_finite : ∀ family : Bool, ∀ v : Fin 129,
    ((⟨BitVec.setWidth 64 (BitVec.ofNat 8 v.val)⟩ : UInt64)=UInt64.ofNat v.val) ∧
    (BitVec.ofNat 8 v.val >>> 3 ^^^ (if family then 3#8 else 7#8))=
      BitVec.ofNat 8 (NodeInit.selector (if family then 32 else 128) v.val) := by
  decide +kernel

theorem pack_first (s : MachineData) (x : BitVec 32) (width l : Nat)
    (family : width=32 ∨ width=128) (bound : l≤width)
    (low : x.setWidth 8=BitVec.ofNat 8 l)
    (least : s.regs.rdi=.ofBitVec (x.setWidth 64)) (copy : s.regs.rdx=.ofBitVec (x.setWidth 64))
    (bits : s.regs.r15=.ofNat width)
    (maskRead : s.dmem.loadInt (s.regs.rsp.toBitVec+36) 1=some (((width/8-1)%8 : Nat) : Int)) :
    (Placement.physical Add.r2cf 0x2cf s).All (fun t =>
      t.pc=Add.entry+0x2e6 ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with
        rax:=.ofNat l,rcx:=.ofBitVec ((~~~x).setWidth 64),rsi:=.ofBitVec ((~~~x).setWidth 64),
        rdi:=.ofNat (width*16777216),
        rdx:=.ofBitVec ((x.setWidth 64).replaceLow (BitVec.ofNat 8 (NodeInit.selector width l)))}) := by
  simp [Placement.physical,Add.r2cf,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    ShiftCountExpr.interpMasked,ShiftCountExpr.interp,
    StatusFlags.from_result,least,copy,bits] at maskRead ⊢
  rw [maskRead]
  rcases family with rfl|rfl
  · simp [Add.entry,Effects.All,low_byte_wide,low32_wide,replace_replace,low_byte_replace,low]
    have finite := pack_first_finite true ⟨l,by omega⟩
    exact ⟨finite.1,congrArg (BitVec.replaceLow _) finite.2⟩
  · simp [Add.entry,Effects.All,low_byte_wide,low32_wide,replace_replace,low_byte_replace,low]
    have finite := pack_first_finite false ⟨l,by omega⟩
    exact ⟨finite.1,congrArg (BitVec.replaceLow _) finite.2⟩

private theorem pack_second_finite : ∀ family : Bool, ∀ v : Fin 129,
    let width := if family then 32 else 128
    let l := v.val
    ((⟨BitVec.setWidth 64
        (BitVec.extractLsb' 0 32
          (BitVec.setWidth 64
              (BitVec.extractLsb' 0 32
                (BitVec.setWidth 64
                  (BitVec.extractLsb' 0 16
                    ((UInt64.ofNat l).toBitVec.replaceLow
                      (BitVec.ofNat 8 (NodeInit.selector width l) ++
                        BitVec.extractLsb' 0 8 (UInt64.ofNat l).toBitVec))))) |||
            BitVec.setWidth 64 (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 (7-l%8)) <<< 16)))⟩ : UInt64) |||
        UInt64.ofNat (width*16777216)=UInt64.ofNat (headerWord width l)) ∧
    ((⟨BitVec.setWidth 64 (BitVec.extractLsb' 0 32 (BitVec.ofNat 64 (7-l%8)) <<< 16)⟩ : UInt64)=
      UInt64.ofNat (7-l%8)*65536) := by
  decide +kernel

theorem pack_second (s : MachineData) (x : BitVec 32) (y : BitVec 64) (width l : Nat)
    (family : width=32 ∨ width=128) (bound : l≤width)
    (low : x.setWidth 8=BitVec.ofNat 8 l)
    (prefixLength : s.regs.rax=.ofNat l)
    (index : s.regs.rdx=.ofBitVec (y.replaceLow (BitVec.ofNat 8 (NodeInit.selector width l))))
    (shift : s.regs.rsi=.ofBitVec ((~~~x).setWidth 64)) (copy : s.regs.rcx=.ofBitVec ((~~~x).setWidth 64))
    (high : s.regs.rdi=.ofNat (width*16777216)) (bytes : s.regs.rbp=.ofNat (width/8)) :
    (Placement.physical Add.r2e6 0x2e6 s).All (fun t =>
      t.pc=Add.entry+0x2fb ∧ t.data.dmem=s.dmem ∧ t.data.status.cf=decide (width=32) ∧
      t.data.regs={s.regs with
        rax:=.ofNat (headerWord width l),rcx:=.ofNat (7-l%8),rsi:=.ofNat ((7-l%8)*65536)}) := by
  rcases family with rfl|rfl
  · simp [Placement.physical,Add.r2e6,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
      RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
      ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
      BitVec.take,BitVec.drop,BitVec.signed,
      Effects.All,
      ShiftCountExpr.interpMasked,ShiftCountExpr.interp,
      StatusFlags.from_result,prefixLength,index,shift,copy,high,bytes,Add.entry,
      low_byte_replace,low32_wide,not_low3 x l low (by omega)]
    have finite := pack_second_finite true ⟨l,by omega⟩
    exact ⟨by decide,finite.1,rfl,finite.2⟩
  · simp [Placement.physical,Add.r2e6,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
      RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
      ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
      BitVec.take,BitVec.drop,BitVec.signed,
      Effects.All,
      ShiftCountExpr.interpMasked,ShiftCountExpr.interp,
      StatusFlags.from_result,prefixLength,index,shift,copy,high,bytes,Add.entry,
      low_byte_replace,low32_wide,not_low3 x l low (by omega)]
    have finite := pack_second_finite false ⟨l,by omega⟩
    exact ⟨by decide,finite.1,rfl,finite.2⟩

end Binary.Pair.Allowedips.C1Internal
