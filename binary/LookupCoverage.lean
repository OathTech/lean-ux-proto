import KcovInvariant

namespace Binary.LookupCoverage
open TrustBase Kcov
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

/-- Fixed lookup context: the entry bucket and preempt count determine the
    union of callback reads. The current count changes at BH-disable. -/
structure Context where
  coverage : KcovLayout
  entryPreempt : BitVec 32
  entryView : LookupRelation.View

def Context.At (c : Context) (current : BitVec 32) (memory : Mem 64) : Prop :=
  LookupCoverageAt c.coverage c.entryPreempt c.entryView memory ∧
  load32 memory preemptCountAddress = some current

def Context.writes (c : Context) := LookupCoverageWrites c.coverage c.entryPreempt c.entryView

def Context.bytes (c : Context) := LookupServiceBytes c.coverage c.entryPreempt c.entryView

/-- Derived from actual call sites; this is not a new entry assumption. -/
def Context.Allowed (c : Context) (current : BitVec 32) (kind : KcovKind) : Prop :=
  (kind = .pc ∧ (current = c.entryPreempt ∨ current = 512+c.entryPreempt)) ∨
  (kind ≠ .pc ∧ current = 512+c.entryPreempt ∧ c.entryView.bucket ≠ [])

theorem allowed_context {c : Context} {current kind} (allowed : c.Allowed current kind) :
    current = c.entryPreempt ∨ current = 512+c.entryPreempt := by
  rcases allowed with ⟨_, contexts⟩ | ⟨_, context, _⟩
  · exact contexts
  · exact .inr context

theorem context_soft {c : Context} {current kind} (allowed : c.Allowed current kind)
    (read : LookupSoftRead current) :
    LookupSoftRead c.entryPreempt ∨ LookupSoftRead (512+c.entryPreempt) := by
  rcases allowed_context allowed with rfl | rfl
  · exact .inl read
  · exact .inr read

theorem context_mode {c : Context} {current kind} (allowed : c.Allowed current kind)
    (read : LookupModeRead c.coverage current) :
    LookupModeRead c.coverage c.entryPreempt ∨ LookupModeRead c.coverage (512+c.entryPreempt) := by
  rcases allowed_context allowed with rfl | rfl
  · exact .inl read
  · exact .inr read

theorem buffer_needed {c : Context} {current kind} (allowed : c.Allowed current kind)
    (mode : c.coverage.mode = (if kind = .pc then 2 else 3))
    (gate : LookupModeRead c.coverage current) :
    LookupBufferNeeded c.coverage c.entryPreempt c.entryView := by
  rcases allowed with ⟨rfl, contexts⟩ | ⟨different, rfl, nonempty⟩
  · exact .inl ⟨mode, context_mode (.inl ⟨rfl, contexts⟩) gate⟩
  · exact .inr ⟨by simpa [different] using mode, nonempty, gate⟩

theorem enabled_iff (kind : KcovKind) (layout : KcovLayout) (preempt : BitVec 32) :
    Kcov.enabled kind layout preempt = true ↔
      LookupModeRead layout preempt ∧ layout.mode = (if kind = .pc then 2 else 3) := by
  by_cases h0 : preempt &&& 0xff0100#32 = 0#32
  all_goals by_cases h1 : preempt &&& 0x100#32 = 0#32
  all_goals by_cases h2 : preempt &&& 0xff0000#32 = 0#32
  all_goals simp [Kcov.enabled, LookupModeRead, h0, h1, h2]

/-- Early returns do not require metadata from a later branch. -/
theorem inactive_plan (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (task : load64 s.data.dmem currentTaskAddress = some layout.task)
    (softirq : LookupSoftRead preempt → load32 s.data.dmem (layout.task+0x704) = some layout.softirqEnabled)
    (mode : LookupModeRead layout preempt → load32 s.data.dmem (layout.task+0x6e0) = some layout.mode)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (inactive : Kcov.enabled kind layout preempt = false) :
    KcovPlan kind s = some [] := by
  by_cases h0 : preempt &&& 0xff0100#32 = 0#32
  all_goals by_cases h1 : preempt &&& 0x100#32 = 0#32
  all_goals by_cases h2 : preempt &&& 0xff0000#32 = 0#32
  all_goals by_cases h3 : layout.softirqEnabled = 0#32
  all_goals simp [LookupSoftRead, LookupModeRead] at softirq mode
  all_goals simp [h0, h1, h2, h3] at softirq mode
  all_goals simp [Kcov.enabled, h0, h1, h2, h3] at inactive
  all_goals simp [KcovPlan, preemptRead, returnRead, task, mode, softirq,
    h0, h1, h2, h3, inactive]

theorem active_plan (c : Context) (kind : KcovKind) (current : BitVec 32)
    (s : MachineState) (returnPC : BitVec 64)
    (state : c.At current s.data.dmem) (allowed : c.Allowed current kind)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (active : Kcov.enabled kind c.coverage current = true) :
    LookupBufferNeeded c.coverage c.entryPreempt c.entryView ∧
    KcovBuffer c.coverage s.data.dmem ∧ ∃ count : Nat,
      count ≤ c.coverage.capacity.toNat ∧
      load64 s.data.dmem c.coverage.area = some (.ofNat 64 count) ∧
      KcovPlan kind s = some (bufferPlan kind c.coverage count returnPC
        (argument kind s .rdi) (argument kind s .rsi)) := by
  obtain ⟨gate, matching⟩ := (enabled_iff kind c.coverage current).mp active
  have needed := buffer_needed allowed matching gate
  obtain ⟨capacity, area, buffer⟩ := state.1.2.2.2 needed
  obtain ⟨count, bound, header⟩ := buffer.2
  have plan := Kcov.plan_normal_form_of_reads kind c.coverage s current returnPC count
    state.1.1 (fun read => state.1.2.1 (context_soft allowed read))
    (fun read => state.1.2.2.1 (context_mode allowed read)) capacity area state.2 returnRead header bound
  exact ⟨needed, buffer, count, bound, header, by simpa only [active, ite_true] using plan⟩

theorem ready (c : Context) (kind : KcovKind) (current : BitVec 32)
    (s : MachineState) (returnPC : BitVec 64)
    (state : c.At current s.data.dmem) (allowed : c.Allowed current kind)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (stack : ∀ a, c.writes a → ¬InRange s.data.regs.rsp.toBitVec 8 a) : KcovReady kind s := by
  cases active : Kcov.enabled kind c.coverage current with
  | false =>
    exact Kcov.inactive_ready kind s (inactive_plan kind c.coverage s current returnPC
      state.1.1 (fun read => state.1.2.1 (context_soft allowed read))
      (fun read => state.1.2.2.1 (context_mode allowed read)) state.2 returnRead active)
  | true =>
    obtain ⟨needed, buffer, count, bound, header, plan⟩ := active_plan c kind current s returnPC
      state allowed returnRead active
    refine ⟨_, plan, ?_⟩
    intro write member
    obtain ⟨word, bound, atWord⟩ := bufferPlan_addresses kind c.coverage count returnPC
      (argument kind s .rdi) (argument kind s .rsi) write member
    constructor
    · rw [atWord]; exact buffer.1 word bound
    · intro address inside
      rw [atWord] at inside
      exact stack address ⟨needed, word_in_buffer c.coverage word bound address inside⟩

/-- Preserve only the metadata actually reached in either callback context.
    The buffer premise is discharged separately by framing or actual stores. -/
theorem coverage_metadata_frame (c : Context) (before after : Mem 64)
    (state : LookupCoverageAt c.coverage c.entryPreempt c.entryView before)
    (writes : BitVec 64 → Prop) (frame : EqualOutside writes before after)
    (apart : ∀ a, LookupMetadataBytes c.coverage c.entryPreempt c.entryView a → ¬writes a)
    (buffer : LookupBufferNeeded c.coverage c.entryPreempt c.entryView → KcovBuffer c.coverage after) :
    LookupCoverageAt c.coverage c.entryPreempt c.entryView after := by
  have field (base : BitVec 64) (width : Nat)
      (part : ∀ a, InRange base width a → LookupMetadataBytes c.coverage c.entryPreempt c.entryView a) :
      before.loadInt base width = after.loadInt base width :=
    frame.loadInt base width (fun i hi => apart _ (part _ ⟨i, hi, rfl⟩))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have same := field currentTaskAddress 8 (fun _ h => .inl h)
    simpa only [load64, ← same] using state.1
  · intro needed
    have same := field (c.coverage.task+0x704) 4 (fun _ h => .inr (.inl ⟨needed, h⟩))
    simpa only [load32, ← same] using state.2.1 needed
  · intro needed
    have same := field (c.coverage.task+0x6e0) 4 (fun _ h => .inr (.inr (.inl ⟨needed, h⟩)))
    simpa only [load32, ← same] using state.2.2.1 needed
  · intro needed
    obtain ⟨capacity, area, _⟩ := state.2.2.2 needed
    have sameCapacity := field (c.coverage.task+0x6e4) 4
      (fun _ h => .inr (.inr (.inr ⟨needed, .inl h⟩)))
    have sameArea := field (c.coverage.task+0x6e8) 8
      (fun _ h => .inr (.inr (.inr ⟨needed, .inr h⟩)))
    exact ⟨by simpa only [load32, ← sameCapacity] using capacity,
      by simpa only [load64, ← sameArea] using area, buffer needed⟩

theorem coverage_frame (c : Context) (before after : Mem 64)
    (state : LookupCoverageAt c.coverage c.entryPreempt c.entryView before)
    (writes : BitVec 64 → Prop) (frame : EqualOutside writes before after)
    (apart : ∀ a, c.bytes a → ¬writes a) :
    LookupCoverageAt c.coverage c.entryPreempt c.entryView after := by
  apply coverage_metadata_frame c before after state writes frame (fun a h => apart a (.inl h))
  intro needed
  exact Kcov.buffer_frame c.coverage before after (state.2.2.2 needed).2.2 writes frame
    (fun a h => apart a (.inr (.inr ⟨needed, h⟩)))

theorem state_frame (c : Context) (current : BitVec 32) (before after : Mem 64)
    (state : c.At current before) (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes before after) (apart : ∀ a, c.bytes a → ¬writes a) :
    c.At current after := by
  refine ⟨coverage_frame c before after state.1 writes frame apart, ?_⟩
  have same := frame.loadInt preemptCountAddress 4
    (fun i hi => apart _ (.inr (.inl ⟨i, hi, rfl⟩)))
  simpa only [load32, ← same] using state.2

theorem state_preserved (c : Context) (kind : KcovKind) (current : BitVec 32)
    (s t : MachineState) (returnPC : BitVec 64)
    (state : c.At current s.data.dmem) (allowed : c.Allowed current kind)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (metadataApart : ∀ a, c.writes a → ¬LookupMetadataBytes c.coverage c.entryPreempt c.entryView a)
    (preemptApart : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a)
    (effect : KcovEffect kind s t)
    (serviceFrame : EqualOutside (KcovWrites kind s) s.data.dmem t.data.dmem) :
    c.At current t.data.dmem ∧ EqualOutside c.writes s.data.dmem t.data.dmem := by
  cases active : Kcov.enabled kind c.coverage current with
  | false =>
    have plan := inactive_plan kind c.coverage s current returnPC state.1.1
      (fun read => state.1.2.1 (context_soft allowed read))
      (fun read => state.1.2.2.1 (context_mode allowed read)) state.2 returnRead active
    have same := Kcov.inactive_effect kind s t plan effect
    rw [same]
    exact ⟨state, fun _ _ => rfl⟩
  | true =>
    obtain ⟨needed, buffer, count, bound, header, plan⟩ := active_plan c kind current s returnPC
      state allowed returnRead active
    have inside : ∀ a, KcovWrites kind s a → c.writes a := by
      rintro a ⟨stores, computed, write, member, atByte⟩
      rw [plan] at computed
      cases Option.some.inj computed
      obtain ⟨word, wordBound, atWord⟩ := bufferPlan_addresses kind c.coverage count returnPC
        (argument kind s .rdi) (argument kind s .rsi) write member
      exact ⟨needed, word_in_buffer c.coverage word wordBound a (by simpa only [atWord] using atByte)⟩
    have frame : EqualOutside c.writes s.data.dmem t.data.dmem := by
      intro a outside
      exact serviceFrame a (fun h => outside (inside a h))
    have newBuffer : KcovBuffer c.coverage t.data.dmem := by
      obtain ⟨stores, computed, memory⟩ := effect
      rw [plan] at computed
      cases Option.some.inj computed
      rw [memory]
      exact bufferPlan_preserves kind c.coverage count returnPC (argument kind s .rdi)
        (argument kind s .rsi) s.data.dmem buffer header bound
    refine ⟨⟨coverage_metadata_frame c _ _ state.1 c.writes frame
      (fun a h written => metadataApart a written h) (fun _ => newBuffer), ?_⟩, frame⟩
    have same := frame.loadInt preemptCountAddress 4
      (fun i hi written => preemptApart _ written ⟨i, hi, rfl⟩)
    simpa only [load32, ← same] using state.2

#print axioms coverage_metadata_frame
#print axioms coverage_frame
#print axioms state_frame
#print axioms state_preserved

#print axioms ready
#print axioms active_plan
#print axioms inactive_plan
#print axioms enabled_iff
#print axioms buffer_needed
end Binary.LookupCoverage
