import LookupBucketHistory
import ScanFrame

namespace Binary.LookupHistory
open TrustBase

/-- Updating the physical BH count changes that component of KCOV state.
    Metadata and active-buffer preservation are derived from byte separation;
    the new count is read back from the actual four-byte store. -/
theorem bh_state (s : MachineData) (count : BitVec 32) (coverage : KcovLayout)
    (state : KcovState coverage count s.dmem)
    (metadataApart : ∀ a, KcovMetadataBytes coverage a → ¬InRange preemptCountAddress 4 a)
    (storageApart : coverage.mode = 2 ∨ coverage.mode = 3 →
      ∀ a, KcovStorageBytes coverage a → ¬InRange preemptCountAddress 4 a) :
    KcovState coverage (512+count) (bhDisabled s count).dmem := by
  have frame := bh_disabled_frame s count
  have field (base : BitVec 64) (width : Nat)
      (part : ∀ a, InRange base width a → KcovMetadataBytes coverage a) :
      s.dmem.loadInt base width = (bhDisabled s count).dmem.loadInt base width := by
    apply frame.loadInt
    intro byte bound
    exact metadataApart _ (part _ ⟨byte, bound, rfl⟩)
  have task := field currentTaskAddress 8 (fun _ h => .inl h)
  have mode := field (coverage.task+0x6e0) 4 (fun _ h => .inr (.inl h))
  have capacity := field (coverage.task+0x6e4) 4 (fun _ h => .inr (.inr (.inl h)))
  have area := field (coverage.task+0x6e8) 8 (fun _ h => .inr (.inr (.inr (.inl h))))
  have softirq := field (coverage.task+0x704) 4 (fun _ h => .inr (.inr (.inr (.inr h))))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [KcovMetadata, load32, load64, ← task, ← mode, ← capacity, ← area, ← softirq]
      using state.1
  · simp only [load32, bh_disabled_count, Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    congr 1
  · intro active
    exact Kcov.buffer_frame coverage _ _ (state.2.2 active) _ frame (storageApart active)

theorem bh_ready (s : MachineData) (count : BitVec 32) (coverage : KcovLayout)
    (ready : PeerGet.CallsReady coverage count s)
    (metadataApart : ∀ a, KcovMetadataBytes coverage a → ¬InRange preemptCountAddress 4 a)
    (storageApart : coverage.mode = 2 ∨ coverage.mode = 3 →
      ∀ a, KcovStorageBytes coverage a → ¬InRange preemptCountAddress 4 a) :
    PeerGet.CallsReady coverage (512+count) (bhDisabled s count) := by
  exact {
    state := bh_state s count coverage ready.state metadataApart storageApart
    aligned := ready.aligned
    mapped := storeInt_defined _ _ _ _ _ _ ready.mapped
    pushSeparate := ready.pushSeparate
    returnSeparate := ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

/-- Header temporaries do not alter the saved query/type/output registers
    or the already established callback state. -/
theorem header_ready (s : MachineData) (count : BitVec 32) (coverage : KcovLayout)
    (head : BitVec 64) (af : Bool)
    (ready : PeerGet.CallsReady coverage (512+count) (bhDisabled s count)) :
    PeerGet.CallsReady coverage (512+count)
      (headLoaded (bucketMasked (queryCopied (bhDisabled s count)) af) head) := by
  apply ready.congr (after := headLoaded (bucketMasked (queryCopied (bhDisabled s count)) af) head) rfl
  simp [headLoaded, bucketMasked, queryCopied, bhDisabled, MachineData.setReg,
    Reg64s.set, Reg64s.set64]

theorem header_registers (s : MachineData) (count : BitVec 32) (head : BitVec 64) (af : Bool) :
    (headLoaded (bucketMasked (queryCopied (bhDisabled s count)) af) head).regs =
      {s.regs with rbx := .ofBitVec head, rax := .ofBitVec ((Lookup.bucketWord s).setWidth 64)} := by
  simp [headLoaded, bucketMasked, queryCopied, bhDisabled, Lookup.bucketWord, MachineData.setReg,
    Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

/-- The incoming bucket shape survives the BH write whenever its actual
    read footprint is separate. This does not require distinct peer words. -/
theorem header_bucket (s : MachineData) (count : BitVec 32) (head : BitVec 64) (af : Bool)
    (es : List (Address × Leanux.WG.IndexEntry))
    (bucket : BucketShape s.dmem head es)
    (separate : ∀ cell ∈ es, ∀ a, BucketShapeReads cell.1 a → ¬InRange preemptCountAddress 4 a) :
    BucketShape (headLoaded (bucketMasked (queryCopied (bhDisabled s count)) af) head).dmem head es :=
  BucketShape.frame_reads (bh_disabled_frame s count) es separate head bucket

#print axioms bh_state
#print axioms bh_ready
#print axioms header_ready
#print axioms header_registers
#print axioms header_bucket
end Binary.LookupHistory
