import PairIndexGeometry
import PairServiceCall

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage
set_option maxRecDepth 2048

def phase (c : Context) (disabled : Bool) : Context :=
  ⟨c.coverage,if disabled then c.preempt+512 else c.preempt⟩

theorem phase_metadata (c : Context) (disabled : Bool) (a : BitVec 64)
    (member : (phase c disabled).metadataBytes a) : AllowedipsMetadata c.coverage c.preempt a := by
  cases disabled with
  | false => exact AllowedipsCoverage.metadata_before _ _ _ member
  | true => exact AllowedipsCoverage.metadata_during _ _ _ member
theorem phase_bytes (c : Context) (disabled : Bool) (a : BitVec 64)
    (member : (phase c disabled).bytes a) : AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a := by
  cases disabled with
  | false => exact AllowedipsCoverage.bytes_before _ _ _ member
  | true => exact AllowedipsCoverage.bytes_during _ _ _ member
theorem phase_writes (c : Context) (disabled : Bool) (a : BitVec 64)
    (member : (phase c disabled).writes a) : AllowedipsCoverageWrites c.coverage c.preempt a := by
  cases disabled with
  | false => exact ⟨.inl member.1,member.2⟩
  | true => exact ⟨.inr member.1,member.2⟩

/-- The real saved words, callback buffer and BH state carried through a
mutator. The final scratch word is the shared instrumentation CALL slot. -/
structure MemoryReady (c : Context) (initial : MachineState) (ra : UInt64)
    (words : Nat) (values : List UInt64) (disabled : Bool) (m : DataMem) : Prop where
  saved : ∀ i, i+1<words → m.loadInt (Stack.slot initial.data.regs.rsp.toBitVec (i+1)) 8=some (values[i]?.getD 0).toNat
  returnWord : m.loadInt initial.data.regs.rsp.toBitVec 8=some ra.toNat
  mapped : ∀ i<words, (m.loadInt (Stack.slot initial.data.regs.rsp.toBitVec (i+1)) 8).isSome=true
  covered : ∀ b, (phase c b).CoverageAt m
  preempt : load32 m preemptCountAddress=some (phase c disabled).preempt
  pending : LookupPendingRead c.preempt → m.loadInt softirqPendingAddress 2=some 0

theorem MemoryReady.frame {n o c initial ra words values disabled before after writes}
    (g : Geometry n o c initial words)
    (ready : MemoryReady c initial ra words values disabled before)
    (frame : EqualOutside writes before after)
    (footprint : ∀ a, writes a → HeapBytes n o a) :
    MemoryReady c initial ra words values disabled after := by
  have slot (i : Nat) (bound : i≤words) : before.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
      after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply frame.loadInt
    intro byte hb written
    exact g.heapLive _ (footprint _ written) (Stack.inside _ words i bound _ ⟨byte,hb,rfl⟩)
  have state := state_frame (phase c disabled) before after ⟨ready.covered _,ready.preempt⟩ _ frame (by
    intro a read written
    exact g.heapService a (footprint a written) (phase_bytes c disabled a read))
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
    apply coverage_frame (phase c b) before after (ready.covered b) _ frame
    intro a read written
    exact g.heapService a (footprint a written) (phase_bytes c b a read)
  · intro needed
    have same := frame.loadInt softirqPendingAddress 2 (by
      intro byte hb written
      exact g.heapService _ (footprint _ written) (.inl (.inl (.inr (.inr (.inr (.inr ⟨needed,byte,hb,rfl⟩)))))))
    exact same.symm.trans (ready.pending needed)

theorem MemoryReady.initial {n o c initial ra words} (facts : CallFacts n o c initial ra words)
    (size : words<2^60) (values : List UInt64) :
    MemoryReady c initial ra words values false
      (Stack.save initial.data.dmem initial.data.regs.rsp.toBitVec values words) := by
  have g := facts.geometry
  have frame := Stack.frame initial.data.dmem initial.data.regs.rsp.toBitVec values words words (by omega)
  have oldState : (phase c false).At initial.data.dmem := facts.coverage
  have before := state_frame (phase c false) _ _ oldState _ frame (by
    intro a read written
    exact g.serviceStack a (phase_bytes c false a read) written)
  refine ⟨?_,?_,?_,?_,before.2,?_⟩
  · intro i hi
    exact Stack.read _ _ _ words i size (by omega)
  · rw [Stack.return_read _ _ _ words size]
    exact facts.entry.2
  · intro i hi
    exact Stack.mapped _ _ _ _ _ _ (by simpa [Stack.slot,Nat.mul_comm] using facts.stack i hi)
  · intro b
    apply coverage_frame (phase c b) _ _ (by cases b; exact facts.coverage.1; exact facts.during) _ frame
    intro a read written
    exact g.serviceStack a (phase_bytes c b a read) written
  · intro needed
    have same := frame.loadInt softirqPendingAddress 2 (by
      intro byte hb written
      exact g.serviceStack _ (.inl (.inl (.inr (.inr (.inr (.inr ⟨needed,byte,hb,rfl⟩)))))) written)
    exact same.symm.trans (facts.pending needed)

theorem callback_coverage {n o c initial words before after}
    (g : Geometry n o c initial words) (positive : 0<words) (active target : Bool)
    (old : (phase c target).CoverageAt before) (next : (phase c active).CoverageAt after)
    (frame : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec words) 8 a ∨
      (phase c active).writes a) before after) : (phase c target).CoverageAt after := by
  apply coverage_metadata_frame (phase c target) before after old _ frame
  · intro a read written
    rcases written with stack | buffer
    · exact g.serviceStack a (.inl (.inl (phase_metadata c target a read)))
        (Stack.scratch _ words words positive (by omega) a stack)
    · exact g.bufferMetadata a (phase_writes c active a buffer) (phase_metadata c target a read)
  · intro needed
    by_cases enabled : (phase c active).Needed
    · exact (next.2.2.2 enabled).2.2
    · apply Kcov.buffer_frame _ before after (old.2.2.2 needed).2.2 _ frame
      intro a read written
      rcases written with stack | buffer
      · exact g.serviceStack a (phase_bytes c target a (.inr (.inr ⟨needed,read⟩)))
          (Stack.scratch _ words words positive (by omega) a stack)
      · exact enabled buffer.1

theorem MemoryReady.callback {n o c initial ra words values disabled before after}
    (g : Geometry n o c initial words) (size : words<2^60) (positive : 0<words)
    (ready : MemoryReady c initial ra words values disabled before)
    (state : (phase c disabled).At after)
    (mapped : (after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec words) 8).isSome=true)
    (frame : EqualOutside (fun a => InRange (Stack.slot initial.data.regs.rsp.toBitVec words) 8 a ∨
      (phase c disabled).writes a) before after) : MemoryReady c initial ra words values disabled after := by
  have slot (i : Nat) (bound : i≤words) (different : i≠words) :
      before.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
      after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply frame.loadInt
    intro byte hb written
    rcases written with stack | buffer
    · exact Stack.separate _ words i words size bound (by omega) different _ ⟨byte,hb,rfl⟩ stack
    · exact g.bufferLive _ (phase_writes c disabled _ buffer) (Stack.inside _ words i bound _ ⟨byte,hb,rfl⟩)
  refine ⟨?_,?_,?_,?_,state.2,?_⟩
  · intro i hi
    rw [←slot (i+1) (by omega) (by omega)]
    exact ready.saved i hi
  · have same := slot 0 (by omega) (by omega)
    simp only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] at same
    exact same.symm.trans ready.returnWord
  · intro i hi
    by_cases same : i+1=words
    · simpa only [same] using mapped
    · rw [←slot (i+1) (by omega) same]
      exact ready.mapped i hi
  · intro b
    exact callback_coverage g positive disabled b (ready.covered b) state.1 frame
  · intro needed
    have same := frame.loadInt softirqPendingAddress 2 (by
      intro byte hb written
      have metadata : AllowedipsMetadata c.coverage c.preempt (softirqPendingAddress+.ofNat 64 byte) :=
        .inr (.inr (.inr (.inr ⟨needed,byte,hb,rfl⟩)))
      rcases written with stack | buffer
      · exact g.serviceStack _ (.inl (.inl metadata)) (Stack.scratch _ words words positive (by omega) _ stack)
      · exact g.bufferMetadata _ (phase_writes c disabled _ buffer) metadata)
    exact same.symm.trans (ready.pending needed)

theorem MemoryReady.preempt_transition {n o c initial ra words values first second before after}
    (g : Geometry n o c initial words)
    (ready : MemoryReady c initial ra words values first before)
    (frame : EqualOutside (InRange preemptCountAddress 4) before after)
    (count : load32 after preemptCountAddress=some (phase c second).preempt) :
    MemoryReady c initial ra words values second after := by
  have slot (i : Nat) (bound : i≤words) : before.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8=
      after.loadInt (Stack.slot initial.data.regs.rsp.toBitVec i) 8 := by
    apply frame.loadInt
    intro byte hb
    exact g.preemptLive _ (Stack.inside _ words i bound _ ⟨byte,hb,rfl⟩)
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
    apply coverage_metadata_frame (phase c b) before after (ready.covered b) _ frame
    · intro a metadata
      exact g.preemptMetadata a (phase_metadata c b a metadata)
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
  · intro needed
    have same := frame.loadInt softirqPendingAddress 2 (by
      intro byte hb
      exact g.preemptMetadata _ (.inr (.inr (.inr (.inr ⟨needed,byte,hb,rfl⟩)))))
    exact same.symm.trans (ready.pending needed)

theorem MemoryReady.calls_ready {n o c initial ra words values disabled}
    (g : Geometry n o c initial words) (positive : 0<words) (s : MachineData)
    (ready : MemoryReady c initial ra words values disabled s.dmem)
    (aligned : s.regs.rsp.toNat%8=0)
    (callSlot : s.regs.rsp.toBitVec-8=Stack.slot initial.data.regs.rsp.toBitVec words) :
    CallsReady (phase c disabled) s := by
  refine ⟨⟨ready.covered _,ready.preempt⟩,aligned,?_,?_,?_,?_,?_⟩
  · rw [callSlot]
    have mapped := ready.mapped (words-1) (by omega)
    simpa only [show words-1+1=words by omega] using mapped
  · intro a read written
    rw [callSlot] at written
    exact g.serviceStack a (phase_bytes c disabled a read) (Stack.scratch _ words words positive (by omega) a written)
  · intro a written inside
    rw [callSlot] at inside
    exact g.bufferLive a (phase_writes c disabled a written) (Stack.inside _ words words (by omega) a inside)
  · intro a written metadata
    exact g.bufferMetadata a (phase_writes c disabled a written) (phase_metadata c disabled a metadata)
  · intro a written preempt
    exact g.bufferPreempt a (phase_writes c disabled a written) preempt

#print axioms MemoryReady.initial
#print axioms MemoryReady.frame
#print axioms MemoryReady.callback
#print axioms MemoryReady.preempt_transition
#print axioms MemoryReady.calls_ready
end Binary.Pair.Index
