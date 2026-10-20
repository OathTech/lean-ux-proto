import PairInsertRandomFrame

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Instrumentation

theorem Core.random_coverage {n o c initial ra config shadow s inputAt value rest t}
    (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64)
    (old : MemoryReady c initial ra (savedWords initial.data) .outer (calledState s returnPC target).data.dmem)
    (post : RandomService.Post config c.coverage (c.preempt+512) inputAt
      (calledState s returnPC target) returnPC.toUInt64 value rest t) (b : Bool) :
    (Index.phase c b).CoverageAt t.data.dmem := by
  apply coverage_metadata_frame (Index.phase c b) _ _ (old.covered b) _ post.frame
    (core.random_metadata_apart provider returnPC target b)
  intro needed
  by_cases active : AllowedipsCoverageNeeded c.coverage (c.preempt+512)
  · exact (post.coverageState.2.2.2 active).2.2
  · apply Kcov.buffer_frame c.coverage _ _ ((old.covered b).2.2.2 needed).2.2 _ post.frame
    intro a inside written
    have needed : AllowedipsCoverageNeeded c.coverage c.preempt ∨
        AllowedipsCoverageNeeded c.coverage (c.preempt+512) := by
      cases b with
      | false =>
        apply Or.inl
        simpa only [Index.phase,Bool.false_eq_true,ite_false,Context.Needed,AllowedipsCoverageNeeded] using needed
      | true =>
        apply Or.inr
        simpa only [Index.phase,ite_true,Context.Needed,AllowedipsCoverageNeeded] using needed
    have service : AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a :=
      .inl (.inr ⟨needed,inside⟩)
    rcases written with privateByte | stack | buffer
    · exact provider.private_services a privateByte service
    · unfold RandomStack at stack
      rw [core.random_base] at stack
      obtain ⟨i,hi,eq⟩ := stack
      exact provider.wide.geometry.serviceStack a service ⟨i,by omega,eq⟩
    · exact active buffer.1

theorem ProviderFacts.private_pending {n o c initial ra config}
    (provider : ProviderFacts n o c initial ra config) (b : Bool)
    (needed : LookupPendingRead (Index.phase c b).preempt) :
    ∀ a, RandomProvider.PrivateBytes config a → ¬InRange softirqPendingAddress 2 a := by
  intro a privateByte pending
  cases b with
  | false =>
    exact provider.private_services a privateByte
      (.inl (.inl (.inr (.inr (.inr (.inr ⟨needed,pending⟩))))))
  | true =>
    apply spansApart_disjoint provider.privateApart (fun _ h => h) (Q := InRange softirqPendingAddress 2) _ a privateByte pending
    intro address inside
    refine ⟨(softirqPendingAddress.toNat,2),?_,by simpa [Span.contains] using inside⟩
    apply List.mem_append_right
    change _ ∈ providerPending c
    rw [providerPending,ite_eq_left (show LookupPendingRead (c.preempt+512) from needed)]
    simp

theorem Core.random_pending {n o c initial ra config shadow s}
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64) (b : Bool)
    (needed : LookupPendingRead (Index.phase c b).preempt) :
    ∀ a, InRange softirqPendingAddress 2 a →
      ¬RandomWrites config c.coverage (c.preempt+512) (calledState s returnPC target) a := by
  intro a pending written
  rcases written with privateByte | stack | buffer
  · exact provider.private_pending b needed a privateByte pending
  · unfold RandomStack at stack
    rw [core.random_base] at stack
    obtain ⟨i,hi,eq⟩ := stack
    have inside : Index.StackBytes initial 135 a := ⟨i,by omega,eq⟩
    cases b with
    | false =>
      exact provider.wide.geometry.serviceStack a
        (.inl (.inl (.inr (.inr (.inr (.inr ⟨needed,pending⟩)))))) inside
    | true =>
      have cover : Covers (providerPending c) (InRange softirqPendingAddress 2) := by
        simpa only [providerPending,show LookupPendingRead (c.preempt+512) from needed,ite_true] using
          Covers.range softirqPendingAddress 2
      exact spansApart_disjoint provider.pendingApart (Index.stack_cover initial 135) cover a inside pending
  · cases b with
    | false =>
      exact provider.wide.geometry.bufferMetadata a ⟨.inr buffer.1,buffer.2⟩
        (.inr (.inr (.inr (.inr ⟨needed,pending⟩))))
    | true => exact facts.pending_disjoint needed a pending (.inr (.inr (.inl ⟨.inr buffer.1,buffer.2⟩)))

theorem Core.random_memory {n o c initial ra config shadow s inputAt value rest t}
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64)
    (old : MemoryReady c initial ra (savedWords initial.data) .outer (calledState s returnPC target).data.dmem)
    (post : RandomService.Post config c.coverage (c.preempt+512) inputAt
      (calledState s returnPC target) returnPC.toUInt64 value rest t) :
    MemoryReady c initial ra (savedWords initial.data) .outer t.data.dmem := by
  have slot (i : Nat) (bound : i≤7) :
      (calledState s returnPC target).data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
        t.data.dmem.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply post.frame.loadInt
    intro byte hb written
    exact core.random_slot provider returnPC target i bound _ written ⟨byte,hb,rfl⟩
  refine ⟨?_,?_,?_,core.random_coverage provider returnPC target old post,post.preemptState,?_⟩
  · intro i hi
    rw [←slot (i+1) (by omega)]
    exact old.saved i hi
  · have same := slot 0 (by omega)
    simp only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] at same
    exact same.symm.trans old.returnWord
  · intro i hi
    exact post.mapped _ _ (old.mapped i hi)
  · intro b needed
    have same := post.frame.loadInt softirqPendingAddress 2 (fun byte hb =>
      core.random_pending facts provider returnPC target b needed _ ⟨byte,hb,rfl⟩)
    exact same.symm.trans (old.pending b needed)

#print axioms Core.random_memory
end Binary.Pair.Insert
