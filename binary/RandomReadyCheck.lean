import RandomStateFrame
import PairFrameProof

namespace Binary.RandomProvider
open TrustBase CommonBitsCoverage Pair

def metadataSpans (c : Context) : List Span :=
  Trie.metadataSpans c ++ [(preemptCountAddress.toNat,4)]

def bufferSpans (c : Context) : List Span :=
  if c.Needed then [(c.coverage.area.toNat,8),(c.coverage.area.toNat,8*c.coverage.capacity.toNat)] else []

def liveStackSpans (s : MachineState) : List Span :=
  [((s.data.regs.rsp.toBitVec-1024).toNat,1032)]

/-- Executable physical service entry assertion, kept separate from input
agreement. Its proposition is exactly the declared service's readiness. -/
def readyCheck (config : Config) (c : Context) (s : MachineState) : Except String Unit := do
  unless Trie.coverageCheck c s.data.dmem do throw "random.ready.coverage"
  unless (!decide c.Needed || c.coverage.capacity.toNat>0) do throw "random.ready.capacity"
  check config c.coverage.task.toNat (RandomRecordingActive c.coverage c.preempt) s.data.dmem
  unless s.data.system.cpl==0 do throw "random.ready.privilege"
  unless !s.data.system.bits[10] do throw "random.ready.direction"
  unless (List.range 1024).all (fun i =>
      (s.data.dmem.get? (s.data.regs.rsp.toBitVec-1024+.ofNat 64 i)).isSome) do
    throw "random.ready.stack"
  unless spansApart config.blocks (liveStackSpans s ++ metadataSpans c ++ bufferSpans c) do
    throw "random.ready.private-alias"
  unless spansApart (liveStackSpans s) (metadataSpans c ++ bufferSpans c) do
    throw "random.ready.stack-alias"
  unless spansApart (bufferSpans c) (metadataSpans c) do throw "random.ready.buffer-alias"

theorem metadata_cover (c : Context) : Covers (metadataSpans c) (RandomMetadata c.coverage c.preempt) := by
  intro a read
  rcases read with current | count | soft | mode | capacity
  · exact (Trie.metadataSpans_cover (.inl current) |> fun h =>
      ⟨h.choose,List.mem_append_left _ h.choose_spec.1,h.choose_spec.2⟩)
  · exact (Covers.range preemptCountAddress 4).append_right a count
  · exact (Trie.metadataSpans_cover (c := c) (.inr (.inl soft)) |> fun h =>
      ⟨h.choose,List.mem_append_left _ h.choose_spec.1,h.choose_spec.2⟩)
  · exact (Trie.metadataSpans_cover (c := c) (.inr (.inr (.inl mode))) |> fun h =>
      ⟨h.choose,List.mem_append_left _ h.choose_spec.1,h.choose_spec.2⟩)
  · exact (Trie.metadataSpans_cover (c := c) (.inr (.inr (.inr capacity))) |> fun h =>
      ⟨h.choose,List.mem_append_left _ h.choose_spec.1,h.choose_spec.2⟩)

theorem buffer_cover (c : Context) : Covers (bufferSpans c) (RandomBuffer c.coverage c.preempt) := by
  rintro a ⟨needed,header | buffer⟩
  · exact ⟨(c.coverage.area.toNat,8),by simp [bufferSpans,show c.Needed from needed],
      by simpa [Span.contains] using header⟩
  · exact ⟨(c.coverage.area.toNat,8*c.coverage.capacity.toNat),by simp [bufferSpans,show c.Needed from needed],
      by simpa [Span.contains,KcovBufferBytes] using buffer⟩

theorem readyCheck_sound {config : Config} {c : Context} {s : MachineState}
    (checked : readyCheck config c s=.ok ()) : RandomReady config c.coverage c.preempt s := by
  unfold readyCheck at checked
  obtain ⟨coverage,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨capacity,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨u,privateCheck,checked⟩ := bind_ok checked
  cases u
  obtain ⟨privilege,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨direction,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨stack,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨privateApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨stackApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨bufferApart,_⟩ := check_ok _ _ _ _ checked
  have coverPrivate : Covers config.blocks (PrivateBytes config) := fun _ h => h
  have coverStack : Covers (liveStackSpans s) (RandomLiveStack s) := Covers.range _ _
  have protectedCover : Covers (liveStackSpans s ++ metadataSpans c ++ bufferSpans c)
      (fun a => RandomLiveStack s a ∨ RandomMetadata c.coverage c.preempt a ∨ RandomBuffer c.coverage c.preempt a) := by
    intro a read
    rcases read with stack | metadata | buffer
    · exact coverStack.append_left.append_left a stack
    · exact (metadata_cover c).append_right.append_left a metadata
    · exact (buffer_cover c).append_right a buffer
  have services : Covers (metadataSpans c ++ bufferSpans c)
      (fun a => RandomMetadata c.coverage c.preempt a ∨ RandomBuffer c.coverage c.preempt a) := by
    intro a read
    rcases read with metadata | buffer
    · exact (metadata_cover c).append_left a metadata
    · exact (buffer_cover c).append_right a buffer
  exact ⟨(Trie.coverageCheck_sound coverage).1,(Trie.coverageCheck_sound coverage).2,
    by intro needed; simpa [show c.Needed from needed] using capacity,
    privateCheck,eq_of_beq privilege,by simpa using direction,
    fun i hi => List.all_eq_true.mp stack i (List.mem_range.mpr hi),
    spansApart_disjoint privateApart coverPrivate protectedCover,
    spansApart_disjoint stackApart coverStack services,
    spansApart_disjoint bufferApart (buffer_cover c) (metadata_cover c)⟩

#print axioms readyCheck_sound
end Binary.RandomProvider
