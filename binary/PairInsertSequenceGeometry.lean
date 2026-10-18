import PairInsertSequenceFacts
import PairSequenceFrame

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index

/-- Private provider state is framed by every pre-existing subsystem call,
including its caller setup and optional lookup output store. -/
theorem InitialFacts.private_existing {n o c base w ra config}
    (facts : InitialFacts n o c base w ra config) :
    ∀ a, RandomProvider.PrivateBytes config a → ¬Sequence.Writes n o c base a := by
  intro a privateByte written
  rcases written with heap | stack | buffer | preempt | output
  · exact facts.provider.private_heap a privateByte heap
  · exact facts.provider.private_live a privateByte
      (Stack.reserve_mono _ 13 135 8 (by decide) a stack)
  · exact facts.provider.private_services a privateByte (.inl (.inr ⟨buffer.1,.inr buffer.2⟩))
  · exact facts.provider.private_services a privateByte (.inr preempt)
  · exact spansApart_disjoint facts.outputApart (fun _ h => h) (Covers.range _ _) a privateByte output

theorem InitialFacts.private_frame {n o c base w ra config before after}
    (facts : InitialFacts n o c base w ra config)
    (frame : EqualOutside (Sequence.Writes n o c base) before after) :
    ∀ a, RandomProvider.PrivateBytes config a → before.get? a=after.get? a :=
  fun a privateByte => frame a (facts.private_existing a privateByte)

/-- Union of the four anchors and explicit caller installation. Geometry is
kept outside reconstruction and justified by the executable initial check. -/
def Writes (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (config : RandomProvider.Config) (a : BitVec 64) : Prop :=
  HeapBytes n o a ∨ LiveStack base 135 a ∨ AllowedipsCoverageWrites c.coverage c.preempt a ∨
    InRange preemptCountAddress 4 a ∨ RandomProvider.PrivateBytes config a ∨
    InRange base.data.regs.rcx.toBitVec 8 a

theorem pending_cover (n o c base config) :
    Covers (pendingProtected n o c base config) (Writes n o c base config) := by
  intro a written
  rcases written with heap | stack | buffer | preempt | privateByte | output
  · exact (show Covers (storageSpans n o) (HeapBytes n o) from fun _ h => h).append_left.append_left.append_left.append_left.append_left a heap
  · exact (live_cover base 135).append_right.append_left.append_left.append_left.append_left a stack
  · exact (Trie.callBuffers_cover c).append_right.append_left.append_left.append_left a buffer
  · exact (Covers.range preemptCountAddress 4).append_right.append_left.append_left a preempt
  · exact (show Covers config.blocks (RandomProvider.PrivateBytes config) from fun _ h => h).append_right.append_left a privateByte
  · exact (Covers.range base.data.regs.rcx.toBitVec 8).append_right a output

theorem InitialFacts.pending_frame {n o c base w ra config before after}
    (facts : InitialFacts n o c base w ra config)
    (frame : EqualOutside (Writes n o c base config) before after)
    (needed : LookupPendingRead (c.preempt+512)) :
    before.loadInt softirqPendingAddress 2=after.loadInt softirqPendingAddress 2 := by
  apply frame.loadInt
  intro i hi
  exact spansApart_disjoint (facts.pendingApart needed) (Covers.range _ _) (pending_cover n o c base config)
    _ ⟨i,hi,rfl⟩

theorem existing_writes {n o c base config a} (written : Sequence.Writes n o c base a) :
    Writes n o c base config a := by
  rcases written with heap | stack | buffer | preempt | output
  · exact .inl heap
  · exact .inr (.inl (Stack.reserve_mono _ 13 135 8 (by decide) a stack))
  · exact .inr (.inr (.inl buffer))
  · exact .inr (.inr (.inr (.inl preempt)))
  · exact .inr (.inr (.inr (.inr (.inr output))))

/-- The nested insertion callback's smaller reservation follows from the
mixed-call footprint check; it adds no new separation premise. -/
theorem InitialFacts.nested_apart {n o c base w ra config}
    (facts : InitialFacts n o c base w ra config)
    (needed : LookupPendingRead (c.preempt+512)) :
    spansApart [(softirqPendingAddress.toNat,2)]
      (storageSpans n o ++ callStack base 7 false ++ Trie.callBuffers c ++
        [(preemptCountAddress.toNat,4)])=true := by
  have checked := facts.pendingApart needed
  let left : Span := (softirqPendingAddress.toNat,2)
  have original := List.all_eq_true.mp checked left (by simp [left])
  apply List.all_eq_true.mpr
  intro l member
  have equal : l=left := by simpa [left] using member
  subst l
  apply List.all_eq_true.mpr
  intro small member
  have narrow (large : Span) (inLarge : large ∈ pendingProtected n o c base config)
      (lower : large.1≤small.1) (upper : small.1+small.2≤large.1+large.2) :
      (left.1+left.2≤2^64 && small.1+small.2≤2^64 &&
        disjointRanges left.1 left.2 small.1 small.2)=true := by
    have old := List.all_eq_true.mp original large inLarge
    simp only [Bool.and_eq_true,decide_eq_true_eq,disjointRanges,Bool.or_eq_true] at old ⊢
    rcases old with ⟨⟨lbound,rbound⟩,before|after⟩ <;> omega
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact narrow small (by simp [pendingProtected,member]) (by omega) (by omega)
      · have smallAt : small=((base.data.regs.rsp.toBitVec-56).toNat,56) := by
          simpa [callStack] using member
        subst small
        let large : Span := ((base.data.regs.rsp.toBitVec-1080).toNat,1088)
        have largeAt : large ∈ pendingProtected n o c base config := by
          simp [pendingProtected,callStack,large]
        have bound := List.all_eq_true.mp original large largeAt
        have bound : (base.data.regs.rsp.toBitVec-1080).toNat+1088≤2^64 := by
          simp only [Bool.and_eq_true,decide_eq_true_eq] at bound
          exact bound.1.2
        have spBound := base.data.regs.rsp.toBitVec.isLt
        have starts : (base.data.regs.rsp.toBitVec-1080).toNat≤
            (base.data.regs.rsp.toBitVec-56).toNat ∧
            (base.data.regs.rsp.toBitVec-56).toNat+56≤
              (base.data.regs.rsp.toBitVec-1080).toNat+1088 := by
          simp only [BitVec.toNat_sub] at bound ⊢
          change (2^64-1080+base.data.regs.rsp.toBitVec.toNat)%2^64+1088≤2^64 at bound
          change (2^64-1080+base.data.regs.rsp.toBitVec.toNat)%2^64≤
            (2^64-56+base.data.regs.rsp.toBitVec.toNat)%2^64 ∧
            (2^64-56+base.data.regs.rsp.toBitVec.toNat)%2^64+56≤
              (2^64-1080+base.data.regs.rsp.toBitVec.toNat)%2^64+1088
          omega
        exact narrow large largeAt starts.1 starts.2
    · exact narrow small (by simp [pendingProtected,member]) (by omega) (by omega)
  · have equal := List.mem_singleton.mp member
    subst small
    exact narrow (preemptCountAddress.toNat,4) (by simp [pendingProtected]) (by omega) (by omega)

#print axioms InitialFacts.private_frame
#print axioms InitialFacts.pending_frame
#print axioms InitialFacts.nested_apart
end Binary.Pair.InsertSequence
