import LookupBucketHistory
import ScanFrame

namespace Binary.LookupHistory
open TrustBase

/-- Updating the physical BH count changes that component of KCOV state.
    Metadata and active-buffer preservation are derived from byte separation;
    the new count is read back from the actual four-byte store. -/
theorem bh_state (s : MachineData) (count : BitVec 32) (coverage : LookupCoverage.Context)
    (state : LookupCoverage.Context.At coverage count s.dmem)
    (metadataApart : ∀ a, LookupCoverage.Context.metadataBytes coverage a → ¬InRange preemptCountAddress 4 a)
    (storageApart : LookupBufferNeeded coverage.coverage coverage.entryPreempt coverage.entryView →
      ∀ a, KcovStorageBytes coverage.coverage a → ¬InRange preemptCountAddress 4 a) :
    LookupCoverage.Context.At coverage (512+count) (bhDisabled s count).dmem := by
  have frame := bh_disabled_frame s count
  refine ⟨LookupCoverage.coverage_metadata_frame coverage _ _ state.1 _ frame metadataApart ?_, ?_⟩
  · intro needed
    exact Kcov.buffer_frame coverage.coverage _ _ (state.1.2.2.2 needed).2.2 _ frame (storageApart needed)
  · simp only [load32, bh_disabled_count, Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    congr 1

theorem bh_ready (s : MachineData) (count : BitVec 32) (coverage : LookupCoverage.Context)
    (ready : LookupCoverage.CallsReady coverage count s)
    (entryCount : count = coverage.entryPreempt)
    (metadataApart : ∀ a, LookupCoverage.Context.metadataBytes coverage a → ¬InRange preemptCountAddress 4 a)
    (storageApart : LookupBufferNeeded coverage.coverage coverage.entryPreempt coverage.entryView →
      ∀ a, KcovStorageBytes coverage.coverage a → ¬InRange preemptCountAddress 4 a) :
    LookupCoverage.CallsReady coverage (512+count) (bhDisabled s count) := by
  exact {
    state := bh_state s count coverage ready.state metadataApart storageApart
    phase := .inr (by rw [entryCount])
    aligned := ready.aligned
    mapped := storeInt_defined _ _ _ _ _ _ ready.mapped
    pushSeparate := ready.pushSeparate
    returnSeparate := ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

/-- Header temporaries do not alter the saved query/type/output registers
    or the already established callback state. -/
theorem header_ready (s : MachineData) (count : BitVec 32) (coverage : LookupCoverage.Context)
    (head : BitVec 64) (af : Bool)
    (ready : LookupCoverage.CallsReady coverage (512+count) (bhDisabled s count)) :
    LookupCoverage.CallsReady coverage (512+count)
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
