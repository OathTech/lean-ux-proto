import LookupCoverage

namespace Binary.CommonBitsCoverage
open TrustBase Kcov
local instance : Labels := Image.linkedLabels

/-- common_bits leaves preempt_count unchanged and always calls both PC and
    comparison instrumentation. Metadata below is required only when read. -/
structure Context where
  coverage : KcovLayout
  preempt : BitVec 32

def Context.Needed (c : Context) : Prop :=
  LookupModeRead c.coverage c.preempt ∧ (c.coverage.mode = 2 ∨ c.coverage.mode = 3)

def Context.CoverageAt (c : Context) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some c.coverage.task ∧
  (LookupSoftRead c.preempt → load32 memory (c.coverage.task+0x704) = some c.coverage.softirqEnabled) ∧
  (LookupModeRead c.coverage c.preempt → load32 memory (c.coverage.task+0x6e0) = some c.coverage.mode) ∧
  (c.Needed → load32 memory (c.coverage.task+0x6e4) = some c.coverage.capacity ∧
    load64 memory (c.coverage.task+0x6e8) = some c.coverage.area ∧ KcovBuffer c.coverage memory)

def Context.At (c : Context) (memory : Mem 64) : Prop :=
  c.CoverageAt memory ∧ load32 memory preemptCountAddress = some c.preempt

def Context.metadataBytes (c : Context) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  (LookupSoftRead c.preempt ∧ InRange (c.coverage.task+0x704) 4 a) ∨
  (LookupModeRead c.coverage c.preempt ∧ InRange (c.coverage.task+0x6e0) 4 a) ∨
  (c.Needed ∧ (InRange (c.coverage.task+0x6e4) 4 a ∨ InRange (c.coverage.task+0x6e8) 8 a))

def Context.writes (c : Context) (a : BitVec 64) : Prop := c.Needed ∧ KcovBufferBytes c.coverage a

def Context.bytes (c : Context) (a : BitVec 64) : Prop :=
  c.metadataBytes a ∨ InRange preemptCountAddress 4 a ∨ (c.Needed ∧ KcovStorageBytes c.coverage a)

private theorem buffer_needed {c : Context} {kind : KcovKind}
    (mode : c.coverage.mode = (if kind = .pc then 2 else 3))
    (gate : LookupModeRead c.coverage c.preempt) : c.Needed := by
  refine ⟨gate, ?_⟩
  by_cases pc : kind = .pc
  · exact .inl (by simpa [pc] using mode)
  · exact .inr (by simpa [pc] using mode)

theorem active_plan (c : Context) (kind : KcovKind)
    (s : MachineState) (returnPC : BitVec 64)
    (state : c.At s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (active : Kcov.enabled kind c.coverage c.preempt = true) :
    c.Needed ∧
    KcovBuffer c.coverage s.data.dmem ∧ ∃ count : Nat,
      count ≤ c.coverage.capacity.toNat ∧
      load64 s.data.dmem c.coverage.area = some (.ofNat 64 count) ∧
      KcovPlan kind s = some (bufferPlan kind c.coverage count returnPC
        (argument kind s .rdi) (argument kind s .rsi)) := by
  obtain ⟨gate, matching⟩ := (LookupCoverage.enabled_iff kind c.coverage c.preempt).mp active
  have needed := buffer_needed matching gate
  obtain ⟨capacity, area, buffer⟩ := state.1.2.2.2 needed
  obtain ⟨count, bound, header⟩ := buffer.2
  have plan := Kcov.plan_normal_form_of_reads kind c.coverage s c.preempt returnPC count
    state.1.1 (fun read => state.1.2.1 read)
    (fun read => state.1.2.2.1 read) capacity area state.2 returnRead header bound
  exact ⟨needed, buffer, count, bound, header, by simpa only [active, ite_true] using plan⟩

theorem ready (c : Context) (kind : KcovKind)
    (s : MachineState) (returnPC : BitVec 64)
    (state : c.At s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (stack : ∀ a, c.writes a → ¬InRange s.data.regs.rsp.toBitVec 8 a) : KcovReady kind s := by
  cases active : Kcov.enabled kind c.coverage c.preempt with
  | false =>
    exact Kcov.inactive_ready kind s (LookupCoverage.inactive_plan kind c.coverage s c.preempt returnPC
      state.1.1 (fun read => state.1.2.1 read)
      (fun read => state.1.2.2.1 read) state.2 returnRead active)
  | true =>
    obtain ⟨needed, buffer, count, bound, header, plan⟩ := active_plan c kind s returnPC
      state returnRead active
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
    (state : c.CoverageAt before)
    (writes : BitVec 64 → Prop) (frame : EqualOutside writes before after)
    (apart : ∀ a, c.metadataBytes a → ¬writes a)
    (buffer : c.Needed → KcovBuffer c.coverage after) :
    c.CoverageAt after := by
  have field (base : BitVec 64) (width : Nat)
      (part : ∀ a, InRange base width a → c.metadataBytes a) :
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
    (state : c.CoverageAt before)
    (writes : BitVec 64 → Prop) (frame : EqualOutside writes before after)
    (apart : ∀ a, c.bytes a → ¬writes a) :
    c.CoverageAt after := by
  apply coverage_metadata_frame c before after state writes frame (fun a h => apart a (.inl h))
  intro needed
  exact Kcov.buffer_frame c.coverage before after (state.2.2.2 needed).2.2 writes frame
    (fun a h => apart a (.inr (.inr ⟨needed, h⟩)))

theorem state_frame (c : Context) (before after : Mem 64)
    (state : c.At before) (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes before after) (apart : ∀ a, c.bytes a → ¬writes a) :
    c.At after := by
  refine ⟨coverage_frame c before after state.1 writes frame apart, ?_⟩
  have same := frame.loadInt preemptCountAddress 4
    (fun i hi => apart _ (.inr (.inl ⟨i, hi, rfl⟩)))
  simpa only [load32, ← same] using state.2

theorem state_preserved (c : Context) (kind : KcovKind)
    (s t : MachineState) (returnPC : BitVec 64)
    (state : c.At s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (metadataApart : ∀ a, c.writes a → ¬c.metadataBytes a)
    (preemptApart : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a)
    (effect : KcovEffect kind s t)
    (serviceFrame : EqualOutside (KcovWrites kind s) s.data.dmem t.data.dmem) :
    c.At t.data.dmem ∧ EqualOutside c.writes s.data.dmem t.data.dmem := by
  cases active : Kcov.enabled kind c.coverage c.preempt with
  | false =>
    have plan := LookupCoverage.inactive_plan kind c.coverage s c.preempt returnPC state.1.1
      (fun read => state.1.2.1 read)
      (fun read => state.1.2.2.1 read) state.2 returnRead active
    have same := Kcov.inactive_effect kind s t plan effect
    rw [same]
    exact ⟨state, fun _ _ => rfl⟩
  | true =>
    obtain ⟨needed, buffer, count, bound, header, plan⟩ := active_plan c kind s returnPC
      state returnRead active
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

/-- Instantiate the named scoped callback contract and derive reusable physical
    readiness from its concrete stores and frame. No callee preservation axiom. -/
theorem callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (c : Context) (s : MachineState) (returnAddress : UInt64)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : c.At s.data.dmem)
    (stack : ∀ a, c.writes a → ¬InRange s.data.regs.rsp.toBitVec 8 a)
    (metadata : ∀ a, c.writes a → ¬c.metadataBytes a)
    (preemptFrame : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a) :
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        c.At t.machine.data.dmem ∧
        EqualOutside c.writes s.data.dmem t.machine.data.dmem ∧
        NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history) ⟨s, [s]⟩ := by
  have returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnAddress.toBitVec := by
    simp only [load64, entry.2, Option.map_some, BitVec.ofInt_natCast]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp
  have run := contract s returnAddress atEntry
    (ready c kind s returnAddress.toBitVec state returnRead stack) entry
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨returned, frame, effect, noReentry, noAllowedips⟩
  have preserved := state_preserved c kind s t.machine returnAddress.toBitVec
    state returnRead metadata preemptFrame effect frame
  exact ⟨returned, preserved.1, preserved.2, noReentry, noAllowedips⟩

end Binary.CommonBitsCoverage
