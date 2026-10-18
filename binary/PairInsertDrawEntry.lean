import PairInsertAddress
import PairInsertDrawData

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

/-- Consume the machine's actual returned word, store it through the owner,
and load its bucket. Agreement with a recorded draw is a separate boundary. -/
theorem draw_entry (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s d owner base} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (ready : RetryData n o shadow d owner base)
    (storage : storageCheck n o=true) (table : initial.data.regs.rdi.toNat=n.table)
    (argument : initial.data.regs.rsi.toNat=base) :
    ∃ focus : InsertFocus n o (ready.entry.afterDraw (drawWord s).toNat),
      focus.fresh.owner=owner ∧ focus.fresh.base=base ∧ focus.index=(drawWord s).toNat ∧
      RetryData n o (ready.entry.afterDraw (drawWord s).toNat) d owner base ∧
      Eventually (instructionStep fetch) (fun t => t.pc=walkStart false focus.nodes ∧
        Core n o c initial ra .outer (ready.entry.afterDraw (drawWord s).toNat) t.data ∧
        WalkRegisters false focus.index t.data ∧
        t.data.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head focus.nodes)) ⟨s,codeEntry+0x79⟩ := by
  have layout := (validate_basic (reconstruct_components ready.related).1).1
  let value := (drawWord s).toNat
  have small : value<2^32 := (drawWord s).isLt
  have sameWord : BitVec.ofNat 32 value=drawWord s := by simp only [value,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  obtain ⟨focus,ownerEq,baseEq,indexEq⟩ := ready.entry.draw_focus value ready.related storage small ready.resident.kind
  refine ⟨focus,ownerEq,baseEq,indexEq,ready.draw value small storage,?_⟩
  have slot : DataSlot n o (base+28) 4 := .entry owner base 28 4 ready.resident.named (.inr (.inr rfl))
  have address : s.regs.rbp.toBitVec+28=BitVec.ofNat 64 (base+28) := by
    rw [core.owner_address argument,BitVec.ofNat_add]
    rfl
  have memory : drawMemory s=write32 s.dmem (base+28) value := by
    rw [drawMemory,address]
    simp only [write32,sameWord]
  have stored : Core n o c initial ra .outer (ready.entry.afterDraw value)
      {s with dmem := drawMemory s} := by
    rw [memory]
    exact core.store32 facts layout slot value
  have mapped : (s.dmem.loadInt (s.regs.rbp.toBitVec+28) 4).isSome=true := by
    obtain ⟨old,read⟩ := ready.resident.index
    have actual := word_loadInt _ _ _ _ _ read
    rw [layout.index] at actual
    rw [address,←core.frame.loadInt _ _ (slot.heap layout),actual]
    rfl
  have bucketAddress : drawBucketAddress s=BitVec.ofNat 64 (tableHead n o (focus.index%8192)) := by
    rw [indexEq]
    have same := core.bucket_address (index := value) layout table
    rw [sameWord] at same
    exact same
  have headBound : Index.head focus.nodes<2^64 := word_bound focus.headRead
  have headValue : (UInt64.ofNat (Index.head focus.nodes)).toNat=Index.head focus.nodes := by
    change Index.head focus.nodes%2^64=Index.head focus.nodes
    exact Nat.mod_eq_of_lt headBound
  have read : (drawMemory s).loadInt (drawBucketAddress s) 8=
      some (UInt64.ofNat (Index.head focus.nodes)).toNat := by
    rw [bucketAddress,headValue,
      ←stored.frame.loadInt _ _ ((LinkSlot.table _ (Nat.mod_lt _ (by decide))).heap layout)]
    exact word_loadInt _ _ _ _ _ focus.headRead
  have physical := draw_and_head s (.ofNat (Index.head focus.nodes)) mapped read
  have run := region_eventually (IndexInsertImage.Insert_r79_layout.agreement decoder) s _ physical
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨regs,heap,pc⟩
  refine ⟨?_,⟨by rw [regs]; exact core.stack,by rw [regs]; exact core.table,
    by rw [regs]; exact core.owner,heap ▸ stored.memory,heap ▸ stored.frame⟩,?_,?_⟩
  · have zero : UInt64.ofNat (Index.head focus.nodes)=0 ↔ BitVec.ofNat 64 (Index.head focus.nodes)=0 :=
      UInt64.toBitVec_inj.symm
    simpa only [zero,walkStart,walkPC,Bool.false_eq_true,↓reduceIte,Int64.add_zero,
      show Int64.ofNat 199=199 by decide,show Int64.ofNat 141=141 by decide] using pc
  · constructor
    · rw [regs,indexEq]
      simp only [UInt64.toNat_ofBitVec,BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (drawWord s).isLt; omega)
    · intro impossible; cases impossible
  · rw [regs]
    rfl

#print axioms draw_entry
end Binary.Pair.Insert
