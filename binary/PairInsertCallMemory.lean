import PairInsertPhases

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage

/-- The saved frame and callback resources persist across every collision
retry. Both pending-read conditions are retained, even in the middle phase. -/
structure MemoryReady (c : Context) (initial : MachineState) (ra : UInt64)
    (values : List UInt64) (p : Phase) (m : DataMem) : Prop where
  saved : ∀ i, i<6 → m.loadInt (Stack.slot initial.data.regs.rsp.toBitVec (i+1)) 8=some (values[i]?.getD 0).toNat
  returnWord : m.loadInt initial.data.regs.rsp.toBitVec 8=some ra.toNat
  mapped : ∀ i<7, (m.loadInt (Stack.slot initial.data.regs.rsp.toBitVec (i+1)) 8).isSome=true
  covered : ∀ b, (Index.phase c b).CoverageAt m
  preempt : load32 m preemptCountAddress=some (p.context c).preempt
  pending : ∀ b, LookupPendingRead (Index.phase c b).preempt → m.loadInt softirqPendingAddress 2=some 0

theorem MemoryReady.state {n o c initial ra values p m} (facts : FrameFacts n o c initial ra)
    (ready : MemoryReady c initial ra values p m) : (p.context c).At m := by
  exact ⟨by rw [p.coverage facts]; exact ready.covered _,ready.preempt⟩

theorem MemoryReady.initial {n o c initial ra} (facts : FrameFacts n o c initial ra)
    (values : List UInt64) : MemoryReady c initial ra values .enabled
      (Stack.save initial.data.dmem initial.data.regs.rsp.toBitVec values 7) := by
  have old := Index.MemoryReady.initial facts.toCallFacts (by decide) values
  refine ⟨fun i hi => old.saved i (by omega),old.returnWord,old.mapped,old.covered,old.preempt,?_⟩
  apply facts.pending_frame
    (before := initial.data.dmem)
    (frame := Stack.frame initial.data.dmem initial.data.regs.rsp.toBitVec values 7 7 (by decide))
  · intro b needed
    cases b with
    | false => exact facts.pending needed
    | true => exact facts.nestedPending needed
  · intro a written
    exact .inr (.inl written)

theorem MemoryReady.frame {n o c initial ra values p before after writes}
    (facts : FrameFacts n o c initial ra) (ready : MemoryReady c initial ra values p before)
    (frame : EqualOutside writes before after) (footprint : ∀ a, writes a → Index.HeapBytes n o a) :
    MemoryReady c initial ra values p after := by
  have g := facts.toCallFacts.geometry
  have slot (i : Nat) (bound : i≤7) : before.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
      after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply frame.loadInt
    intro byte hb written
    exact g.heapLive _ (footprint _ written) (Stack.inside _ 7 i bound _ ⟨byte,hb,rfl⟩)
  have state := state_frame (p.context c) before after (ready.state facts) _ frame (by
    intro a read written
    rw [p.bytes facts] at read
    exact g.heapService a (footprint a written) (Index.phase_bytes c p.disabled a read))
  refine ⟨?_,?_,?_,?_,state.2,?_⟩
  · intro i hi
    rw [←slot (i+1) (by omega)]
    exact ready.saved i hi
  · have same := slot 0 (by omega)
    simp only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] at same
    exact same.symm.trans ready.returnWord
  · intro i hi
    rw [←slot (i+1) (by omega)]
    exact ready.mapped i hi
  · intro b
    apply coverage_frame (Index.phase c b) before after (ready.covered b) _ frame
    intro a read written
    exact g.heapService a (footprint a written) (Index.phase_bytes c b a read)
  · exact facts.pending_frame ready.pending frame (fun a h => .inl (footprint a h))

theorem MemoryReady.callback {n o c initial ra values p before after}
    (facts : FrameFacts n o c initial ra) (ready : MemoryReady c initial ra values p before)
    (state : (p.context c).At after)
    (mapped : (after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec 7) 8).isSome=true)
    (frame : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 a ∨
      (p.context c).writes a) before after) : MemoryReady c initial ra values p after := by
  have g := facts.toCallFacts.geometry
  have written (a : BitVec 64) (h : (p.context c).writes a) : AllowedipsCoverageWrites c.coverage c.preempt a := by
    rw [p.writes facts] at h
    exact Index.phase_writes c p.disabled a h
  have slot (i : Nat) (bound : i<7) : before.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
      after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply frame.loadInt
    intro byte hb changed
    rcases changed with stack | buffer
    · exact Stack.separate _ 7 i 7 (by decide) (by omega) (by decide) (by omega) _ ⟨byte,hb,rfl⟩ stack
    · exact g.bufferLive _ (written _ buffer) (Stack.inside _ 7 i (by omega) _ ⟨byte,hb,rfl⟩)
  refine ⟨?_,?_,?_,?_,state.2,?_⟩
  · intro i hi
    rw [←slot (i+1) (by omega)]
    exact ready.saved i hi
  · have same := slot 0 (by omega)
    simp only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] at same
    exact same.symm.trans ready.returnWord
  · intro i hi
    by_cases last : i+1=7
    · simpa only [last] using mapped
    · rw [←slot (i+1) (by omega)]
      exact ready.mapped i hi
  · intro b
    apply Index.callback_coverage g (by decide) p.disabled b (ready.covered b)
    · rw [←p.coverage facts]
      exact state.1
    · simpa only [p.writes facts] using frame
  · apply facts.pending_frame ready.pending frame
    intro a changed
    rcases changed with stack | buffer
    · exact .inr (.inl (Stack.scratch _ 7 7 (by decide) (by decide) a stack))
    · exact .inr (.inr (.inl (written a buffer)))

theorem MemoryReady.preempt_transition {n o c initial ra values p q before after}
    (facts : FrameFacts n o c initial ra) (ready : MemoryReady c initial ra values p before)
    (frame : EqualOutside (InRange preemptCountAddress 4) before after)
    (count : load32 after preemptCountAddress=some (q.context c).preempt) :
    MemoryReady c initial ra values q after := by
  have g := facts.toCallFacts.geometry
  have slot (i : Nat) (bound : i≤7) : before.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
      after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply frame.loadInt
    intro byte hb
    exact g.preemptLive _ (Stack.inside _ 7 i bound _ ⟨byte,hb,rfl⟩)
  refine ⟨?_,?_,?_,?_,count,?_⟩
  · intro i hi
    rw [←slot (i+1) (by omega)]
    exact ready.saved i hi
  · have same := slot 0 (by omega)
    simp only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] at same
    exact same.symm.trans ready.returnWord
  · intro i hi
    rw [←slot (i+1) (by omega)]
    exact ready.mapped i hi
  · intro b
    apply coverage_metadata_frame (Index.phase c b) before after (ready.covered b) _ frame
    · intro a metadata
      exact g.preemptMetadata a (Index.phase_metadata c b a metadata)
    · intro needed
      apply Kcov.buffer_frame _ before after ((ready.covered b).2.2.2 needed).2.2 _ frame
      intro a member
      have either : c.Needed ∨ (Context.mk c.coverage (c.preempt+512)).Needed := by
        cases b with
        | false => exact .inl needed
        | true => exact .inr needed
      rcases member with header | buffer
      · exact g.preemptHeader a either header
      · exact g.bufferPreempt a ⟨either,buffer⟩
  · exact facts.pending_frame ready.pending frame (fun _ h => .inr (.inr (.inr h)))

theorem MemoryReady.calls_ready {n o c initial ra values p s}
    (facts : FrameFacts n o c initial ra) (ready : MemoryReady c initial ra values p s.dmem)
    (aligned : s.regs.rsp.toNat%8=0)
    (callSlot : s.regs.rsp.toBitVec-8=Stack.slot initial.data.regs.rsp.toBitVec 7) :
    CallsReady (p.context c) s := by
  have g := facts.toCallFacts.geometry
  have written (a : BitVec 64) (h : (p.context c).writes a) : AllowedipsCoverageWrites c.coverage c.preempt a := by
    rw [p.writes facts] at h
    exact Index.phase_writes c p.disabled a h
  refine ⟨ready.state facts,aligned,?_,?_,?_,?_,?_⟩
  · rw [callSlot]
    exact ready.mapped 6 (by decide)
  · intro a read changed
    rw [callSlot] at changed
    rw [p.bytes facts] at read
    exact g.serviceStack a (Index.phase_bytes c p.disabled a read) (Stack.scratch _ 7 7 (by decide) (by decide) a changed)
  · intro a changed inside
    rw [callSlot] at inside
    exact g.bufferLive a (written a changed) (Stack.inside _ 7 7 (by decide) a inside)
  · intro a changed metadata
    rw [p.metadata facts] at metadata
    exact g.bufferMetadata a (written a changed) (Index.phase_metadata c p.disabled a metadata)
  · intro a changed count
    exact g.bufferPreempt a (written a changed) count

theorem MemoryReady.call_store {n o c initial ra values p m}
    (facts : FrameFacts n o c initial ra) (ready : MemoryReady c initial ra values p m)
    (value : BitVec 64) : MemoryReady c initial ra values p
      (m.storeInt (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 value.toInt) := by
  have frame := storeInt_frame m (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 value.toInt
  have state := state_frame (p.context c) _ _ (ready.state facts) _ frame (by
    intro a read written
    rw [p.bytes facts] at read
    exact facts.toCallFacts.geometry.serviceStack a (Index.phase_bytes c p.disabled a read)
      (Stack.scratch _ 7 7 (by decide) (by decide) a written))
  apply ready.callback facts state
  · rw [load64_store]
    rfl
  · intro a outside
    exact frame a (fun inside => outside (.inl inside))

#print axioms MemoryReady.initial
#print axioms MemoryReady.frame
#print axioms MemoryReady.callback
#print axioms MemoryReady.preempt_transition
#print axioms MemoryReady.calls_ready
#print axioms MemoryReady.call_store
end Binary.Pair.Insert
