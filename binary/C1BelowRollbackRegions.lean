import C1Interfaces
import AllowedipsMutationCodeLayout
import RegionExecution

/-! Result C1, work package 3, rollback path: the straight-line instruction
regions between the second allocation's NULL return (`add+0x292`) and the
common exit, executed symbolically. Nothing here is assumed of an execution:
each lemma takes facts about the state it starts from. -/
namespace Binary.Statements.C1.Proof.Rollback
open Binary.AllowedipsMutationImage Binary.TrustBase
local instance : Labels := Image.linkedLabels

/-- `add+0x292 .. +0x2a3` with `rax = 0`: reload the first node, branch to the rollback. -/
theorem region292 (s : MachineData) (base : Nat)
    (rax : s.regs.rax = 0)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some (base : Int)) :
    (Directives.interp Add.r292 s (Add.entry + 0x292) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x651 ∧ t.data.dmem = s.dmem ∧
      t.data.regs = {s.regs with r8 := .ofNat base, r12 := 0}) := by
  simp [Add.r292,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,rax] at baseRead ⊢
  rw [baseRead]
  simp [Effects.All,CondCode.interp,StatusFlags.from_result]
  exact ⟨rfl,rfl⟩

/-- `add+0x651`: save the first node across the coverage call. -/
theorem region651 (s : MachineData)
    (mapped : (s.dmem.loadInt s.regs.rsp.toBitVec 8).isSome = true) :
    (Directives.interp (Add.r651.take 1) s (Add.entry + 0x651) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x655 ∧ t.data.dmem = s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.r8.toBitVec.toInt ∧
      t.data.regs = s.regs) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp mapped
  simp [Add.r651,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,Effects.All] at oldRead ⊢
  rw [oldRead]
  simp [Effects.All]
  rfl

/-- The memory after `list_del(&node->peer_list)`'s two unlinking stores. -/
def unlinked (m : DataMem) (next prev : Nat) : DataMem :=
  (m.storeInt (.ofNat 64 next + 8) 8 (BitVec.ofNat 64 prev).toInt).storeInt
    (.ofNat 64 prev) 8 (BitVec.ofNat 64 next).toInt

/-- `add+0x65a .. +0x681`: reload the node, load `node_cache`, unlink the node from its peer's list. -/
theorem region65a (s : MachineData) (base cache next prev : Nat)
    (baseRead : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (base : Int))
    (cacheRead : s.dmem.loadInt (.ofNat 64 Statements.C1.cacheWord) 8 = some (cache : Int))
    (prevRead : s.dmem.loadInt (.ofNat 64 base + 64) 8 = some (prev : Int))
    (nextRead : s.dmem.loadInt (.ofNat 64 base + 56) 8 = some (next : Int))
    (firstMapped : (s.dmem.loadInt (.ofNat 64 next + 8) 8).isSome = true)
    (secondMapped : ((s.dmem.storeInt (.ofNat 64 next + 8) 8 (BitVec.ofNat 64 prev).toInt).loadInt
      (.ofNat 64 prev) 8).isSome = true) :
    (Directives.interp Add.r65a s (Add.entry + 0x65a) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x681 ∧ t.data.dmem = unlinked s.dmem next prev ∧
      t.data.regs = {s.regs with r8 := .ofNat base, rdi := .ofNat cache, rsi := .ofNat base, rdx := .ofNat next, rax := 0xdead000000000100}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp firstMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp secondMapped
  simp [Add.r65a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,unlinked] at baseRead cacheRead prevRead nextRead oldRead oldRead2 ⊢
  rw [baseRead]
  simp only [Effects.All]
  have cacheAddress : BitVec.ofInt 64 ((Add.entry.toInt + 1626 + 4 + 7).bmod 18446744073709551616) + 12823611#64 =
      BitVec.ofNat 64 Statements.C1.cacheWord := by rfl
  rw [cacheAddress,cacheRead]
  have word (n : Nat) : BitVec.ofInt 64 ((n : Int).bmod 18446744073709551616) = BitVec.ofNat 64 n := by
    rw [Binary.AllowedipsChild.ofInt_bmod64,BitVec.ofInt_natCast]
  have value (n : Nat) : (n : Int).bmod 18446744073709551616 = (BitVec.ofNat 64 n).toInt := by
    rw [BitVec.toInt_ofNat']
  simp only [Effects.All,word]
  rw [prevRead]
  simp only [Effects.All,word]
  rw [nextRead]
  simp only [Effects.All,word]
  simp only [value]
  rw [oldRead]
  simp only [Effects.All]
  rw [oldRead2]
  simp [Effects.All]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- `add+0x681 .. +0x68d`: poison the unlinked node's list words. -/
theorem region681 (s : MachineData)
    (rax : s.regs.rax = 0xdead000000000100)
    (firstMapped : (s.dmem.loadInt (s.regs.r8.toBitVec + 56) 8).isSome = true)
    (secondMapped : ((s.dmem.storeInt (s.regs.r8.toBitVec + 56) 8 (0xdead000000000100#64).toInt).loadInt
      (s.regs.r8.toBitVec + 64) 8).isSome = true) :
    (Directives.interp (Add.r681.take 3) s (Add.entry + 0x681) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x68d ∧
      t.data.dmem = (s.dmem.storeInt (s.regs.r8.toBitVec + 56) 8 (0xdead000000000100#64).toInt).storeInt
        (s.regs.r8.toBitVec + 64) 8 (0xdead000000000122#64).toInt ∧
      t.data.regs = {s.regs with rax := 0xdead000000000122}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp firstMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp secondMapped
  simp [Add.r681,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,rax] at oldRead oldRead2 ⊢
  rw [oldRead]
  simp only [Effects.All]
  rw [oldRead2]
  simp [Effects.All]
  rfl

/-- `add+0x692`: `-ENOMEM` and the jump to the common exit. -/
theorem region692 (s : MachineData) :
    (Directives.interp Add.r692 s (Add.entry + 0x692) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.dmem = s.dmem ∧
      t.data.regs = {s.regs with rbx := 0xfffffff4}) := by
  simp [Add.r692,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    Operand.interp,MachineData.set,MachineData.setReg,
    ConstExpr.interp,Reg64s.set,Reg64s.set64,
    
    Effects.All,RelRegOrMem.interp]
  rfl

end Binary.Statements.C1.Proof.Rollback
