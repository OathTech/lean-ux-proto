import PairSpan
import CommonBitsCoverage

namespace Binary.Pair.Trie
open TrustBase CommonBitsCoverage

instance (c : Context) : Decidable c.Needed := by
  unfold Context.Needed LookupModeRead
  infer_instance

instance (p : BitVec 32) : Decidable (LookupSoftRead p) := by
  unfold LookupSoftRead
  infer_instance

instance (c : KcovLayout) (p : BitVec 32) : Decidable (LookupModeRead c p) := by
  unfold LookupModeRead
  infer_instance

def metadataSpans (c : Context) : List Span :=
  [(currentTaskAddress.toNat,8)] ++
  (if LookupSoftRead c.preempt then [((c.coverage.task+0x704).toNat,4)] else []) ++
  (if LookupModeRead c.coverage c.preempt then [((c.coverage.task+0x6e0).toNat,4)] else []) ++
  (if c.Needed then [((c.coverage.task+0x6e4).toNat,4),((c.coverage.task+0x6e8).toNat,8)] else [])

def writeSpans (c : Context) : List Span :=
  if c.Needed then [(c.coverage.area.toNat,8*c.coverage.capacity.toNat)] else []

def readSpans (c : Context) : List Span := metadataSpans c ++ [(preemptCountAddress.toNat,4)] ++
  (if c.Needed then [(c.coverage.area.toNat,8)] ++ writeSpans c else [])

/-- Inspect callback inputs and the buffer's mapped words, including its
current header. The check follows the callback's conditional read footprint. -/
def coverageCheck (c : Context) (m : DataMem) : Bool :=
  (load64 m currentTaskAddress == some c.coverage.task) &&
  (load32 m preemptCountAddress == some c.preempt) &&
  (if LookupSoftRead c.preempt then load32 m (c.coverage.task+0x704) == some c.coverage.softirqEnabled else true) &&
  (if LookupModeRead c.coverage c.preempt then load32 m (c.coverage.task+0x6e0) == some c.coverage.mode else true) &&
  (if c.Needed then
    (load32 m (c.coverage.task+0x6e4) == some c.coverage.capacity) &&
    (load64 m (c.coverage.task+0x6e8) == some c.coverage.area) &&
    (List.range c.coverage.capacity.toNat).all (fun word =>
      (m.loadInt (c.coverage.area+.ofNat 64 (8*word)) 8).isSome) &&
    (match load64 m c.coverage.area with
      | none => false
      | some count => count.toNat ≤ c.coverage.capacity.toNat)
   else true)

/-- The extra initial-header assertion exposed by the proof: the runner had
checked final coverage contents but had not checked callback readiness. -/
def frameCheck (c : Context) (s : MachineData) : Bool :=
  coverageCheck c s.dmem && s.regs.rsp.toNat % 8 == 0 &&
  (List.range 6).all (fun n => (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome) &&
  spansApart (readSpans c) [((s.regs.rsp.toBitVec-48).toNat,48)] &&
  spansApart (writeSpans c) (metadataSpans c ++ [(preemptCountAddress.toNat,4)])

end Binary.Pair.Trie
