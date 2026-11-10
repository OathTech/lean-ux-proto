import C1BelowSplitMachine

/- Origin: trial source binary-trials/t5/T5MachineRoot.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 3 (third piece): the image's root publication of the internal
node, `rcu_assign_pointer(*trie, node)` with `connect_node`'s parent word,
`Add.entry+0x6c5 .. +0x6e0` (region `Add.r6c5`; 7 instructions ending in the jump to
the common exit). The KCOV call at `+0x6c0` before it is not executed here. -/
namespace Binary.SplitStage3.RootExit
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3
local instance : Labels := Image.linkedLabels

theorem r6c5_layout {fetch : Int64 → Option Decoded} (mutation : AllowedipsMutationDecoderAgreement fetch) :
    LaidOut fetch (Add.entry + 0x6c5) Add.r6c5 := Add_r6c5_layout.agreement mutation.add

theorem toInt_emod_toNat (x : BitVec 64) : (x.toInt % 18446744073709551616).toNat = x.toNat := by
  have bound := x.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem ofInt_toInt_bmod64 (x : BitVec 64) :
    BitVec.ofInt 64 (x.toInt.bmod 18446744073709551616) = x := by
  rw [AllowedipsChild.ofInt_bmod64, BitVec.ofInt_toInt]

def memRoot (s : MachineData) (trieSlot : BitVec 64) : DataMem :=
  (s.dmem.storeInt (s.regs.r12.toBitVec + 48) 8 (trieSlot ||| 2).toInt).storeInt
      trieSlot 8 s.regs.r12.toBitVec.toInt

theorem regionF (s : MachineData) (trieSlot : BitVec 64)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some trieSlot.toInt)
    (nodeMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : ((s.dmem.storeInt (s.regs.r12.toBitVec + 48) 8 (trieSlot ||| 2).toInt).loadInt
        trieSlot 8).isSome = true) :
    (Directives.interp Add.r6c5 s (Add.entry + 0x6c5) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x549 ∧
      t.data.dmem = memRoot s trieSlot ∧
      t.data.regs = {s.regs with rax := UInt64.ofBitVec (trieSlot ||| 2), rbx := 0, rdx := UInt64.ofBitVec trieSlot}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp nodeMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp rootMapped
  simp [Add.r6c5,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    memRoot] at slotRead oldRead oldRead2 ⊢
  rw [slotRead]
  simp [Effects.All,BitVec.ofInt_toInt,toInt_emod_toNat,ofInt_toInt_bmod64]
  rw [oldRead]
  simp only [Effects.All]
  intro v
  rw [oldRead2]
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  rfl

#print axioms regionF

/-- From `Add.entry+0x6c5` (after the KCOV call) to the common exit: the root slot
pointer saved at `8(%rsp)` receives the internal node, whose parent word is the
tagged slot address. -/
theorem root_exit (fetch : Int64 → Option Decoded) (agree : AllowedipsMutationDecoderAgreement fetch)
    (s : MachineData) (trieSlot : BitVec 64)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some trieSlot.toInt)
    (nodeMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : (s.dmem.loadInt trieSlot 8).isSome = true) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.dmem = memRoot s trieSlot ∧
      t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbp = s.regs.rbp ∧
      t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧ t.data.regs.r14 = s.regs.r14 ∧
      t.data.regs.r15 = s.regs.r15) ⟨s, Add.entry + 0x6c5⟩ := by
  have run := regionF s trieSlot slotRead nodeMapped (storeInt_defined _ _ _ _ _ _ rootMapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (r6c5_layout agree) s _ run)
  rintro t ⟨pcT, memT, regsT⟩
  simp only [pcT, memT, regsT]
  simp only [and_self]

#print axioms root_exit

end Binary.SplitStage3.RootExit

namespace Binary.Pair.Allowedips.C1Split
open Binary.SplitStage3

/-- The root publication's machine memory in stage 1's terms. -/
theorem memRoot_connectMemory (m : DataMem) (node slot : Nat) :
    (m.storeInt (BitVec.ofNat 64 node + 48) 8 (BitVec.ofNat 64 slot ||| 2).toInt).storeInt
        (BitVec.ofNat 64 slot) 8 (BitVec.ofNat 64 node).toInt=
      connectMemory m node slot (slot ||| 2) := by
  have tagged : BitVec.ofNat 64 (slot ||| 2)=BitVec.ofNat 64 slot ||| 2 := by
    rw [BitVec.ofNat_or]
    rfl
  simp only [connectMemory,write64,field_ofNat,tagged]

#print axioms memRoot_connectMemory
end Binary.Pair.Allowedips.C1Split
