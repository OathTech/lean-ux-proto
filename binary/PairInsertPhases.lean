import PairInsertCallFacts

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage

inductive Phase where | enabled | outer | inner
  deriving DecidableEq

def Phase.disabled : Phase → Bool
  | .enabled => false
  | .outer | .inner => true

def Phase.context (p : Phase) (c : Context) : Context :=
  ⟨c.coverage, match p with
    | .enabled => c.preempt
    | .outer => c.preempt+512
    | .inner => c.preempt+1024⟩

theorem Phase.coverage {n o c s ra} (facts : FrameFacts n o c s ra)
    (p : Phase) (m : DataMem) :
    (p.context c).CoverageAt m=(Index.phase c p.disabled).CoverageAt m := by
  cases p with
  | enabled => rfl
  | outer => rfl
  | inner => exact nested_coverage c facts.hardirq facts.nestedHardirq m

theorem Phase.bytes {n o c s ra} (facts : FrameFacts n o c s ra)
    (p : Phase) (a : BitVec 64) :
    (p.context c).bytes a=(Index.phase c p.disabled).bytes a := by
  cases p with
  | enabled => rfl
  | outer => rfl
  | inner => exact nested_bytes c facts.hardirq facts.nestedHardirq a

theorem Phase.needed {n o c s ra} (facts : FrameFacts n o c s ra) (p : Phase) :
    (p.context c).Needed=(Index.phase c p.disabled).Needed := by
  cases p with
  | enabled => rfl
  | outer => rfl
  | inner =>
    have add : c.preempt+512+512=c.preempt+1024 := by rw [BitVec.add_assoc]; rfl
    have gates := nested_gate c.coverage (c.preempt+512) facts.hardirq (by rw [add]; exact facts.nestedHardirq)
    rw [add] at gates
    simp only [context,disabled,Index.phase,↓reduceIte,Context.Needed,gates.2]

theorem Phase.writes {n o c s ra} (facts : FrameFacts n o c s ra)
    (p : Phase) (a : BitVec 64) :
    (p.context c).writes a=(Index.phase c p.disabled).writes a := by
  unfold Context.writes
  rw [p.needed facts]
  rfl

theorem Phase.metadata {n o c s ra} (facts : FrameFacts n o c s ra)
    (p : Phase) (a : BitVec 64) :
    (p.context c).metadataBytes a=(Index.phase c p.disabled).metadataBytes a := by
  cases p with
  | enabled => rfl
  | outer => rfl
  | inner =>
    have add : c.preempt+512+512=c.preempt+1024 := by rw [BitVec.add_assoc]; rfl
    have gates := nested_gate c.coverage (c.preempt+512) facts.hardirq (by rw [add]; exact facts.nestedHardirq)
    rw [add] at gates
    simp only [context,disabled,Index.phase,↓reduceIte,Context.metadataBytes,Context.Needed,gates.1,gates.2]

theorem FrameFacts.pending_frame {n o c s ra before after writes}
    (facts : FrameFacts n o c s ra)
    (pending : ∀ b, LookupPendingRead (Index.phase c b).preempt → before.loadInt softirqPendingAddress 2=some 0)
    (frame : EqualOutside writes before after)
    (footprint : ∀ a, writes a → Index.HeapBytes n o a ∨ Index.StackBytes s 7 a ∨
      AllowedipsCoverageWrites c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a) :
    ∀ b, LookupPendingRead (Index.phase c b).preempt → after.loadInt softirqPendingAddress 2=some 0 := by
  intro b needed
  have same := frame.loadInt softirqPendingAddress 2 (by
    intro byte hb written
    have inside : InRange softirqPendingAddress 2 (softirqPendingAddress+.ofNat 64 byte) := ⟨byte,hb,rfl⟩
    cases b with
    | true => exact facts.pending_disjoint needed _ inside (footprint _ written)
    | false =>
      have metadata : AllowedipsMetadata c.coverage c.preempt (softirqPendingAddress+.ofNat 64 byte) :=
        .inr (.inr (.inr (.inr ⟨needed,inside⟩)))
      have g := facts.toCallFacts.geometry
      rcases footprint _ written with heap | stack | buffer | count
      · exact g.heapService _ heap (.inl (.inl metadata))
      · exact g.serviceStack _ (.inl (.inl metadata)) stack
      · exact g.bufferMetadata _ buffer metadata
      · exact g.preemptMetadata _ metadata count)
  exact same.symm.trans (pending b needed)

#print axioms Phase.coverage
#print axioms Phase.bytes
#print axioms Phase.writes
#print axioms FrameFacts.pending_frame
end Binary.Pair.Insert
