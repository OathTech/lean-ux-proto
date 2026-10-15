import PeerLoadHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

theorem nonnull_guard_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body) (nonnull : body.regs.rbx ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x12⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbx .W64) body af, Image.PeerGet.entry+0x1b⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x12⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_null_guard fetch agree body history)
  rintro t ⟨af, machine, recorded⟩
  have nonzero : body.regs.get (.low .rbx .W64) ≠ (0 : BitVec 64) := by
    intro h
    apply nonnull
    apply UInt64.toBitVec_inj.mp
    simpa [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take] using h
  simp only [beq_iff_eq, nonzero, ite_false] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbx .W64) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame


/-- Actual nonnull prefix to the zero-count test. The memory word determines
    EBP; no positivity premise excludes dead peers. -/
theorem nonnull_prefix_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (body : MachineData) (nonnull : body.regs.rbx ≠ 0) (count : UInt32)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (fieldSeparate : ∀ a, InRange (body.regs.rbx.toBitVec+0x420) 4 a → ¬scanWrites body coverage a)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x12⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = Image.PeerGet.entry+0x3b ∧
      t.machine.data.regs.rsp = body.regs.rsp ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧
      t.machine.data.regs.rbp = count.toUInt64 ∧
      t.machine.data.regs.r13 = body.regs.rbx+0x420 ∧
      LookupCoverage.CallsReady coverage preempt t.machine.data ∧
      EqualOutside (scanWrites body coverage) body.dmem t.machine.data.dmem ∧
      t.history.getLast? = some t.machine ∧
      PeerCountPhase.StableExtension history t.history ∧
      ∃ af, observeHistory (LookupObservation.edge rxSection) t.history =
        .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false
          ⟨tested (.low .rbx .W64) body af, Image.PeerGet.entry+0x1b⟩]) ∧
        ∃ tail, t.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x12⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (nonnull_guard_history fetch agree body body coverage preempt (ScanFrame.initial body coverage preempt ready)
      nonnull rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, machine₁, trace₁⟩
  have pc₁ : guarded.machine.pc = Image.PeerGet.entry+0x1b := congrArg MachineState.pc machine₁
  let event := LookupObservation.decision rxSection .peerGetMaybeZeroNull false guarded.machine
  have call := scan_call_cursor fetch "L_ffffffff810f3100" guarded
    (by rw [pc₁]; exact agree _ _ (by rfl)) .pc tracePc body coverage preempt trace₁.frame (trace₁.frame).ready.pc_allowed
    rxSection (events ++ [event]) trace₁.observed trace₁.last (by
      simp [LookupObservation.edge, pc₁, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro afterCall ⟨pc₂, bx₂, _, trace₂⟩
  have pc₂ : afterCall.machine.pc = Image.PeerGet.entry+0x20 := by rw [pc₂, pc₁]; rfl
  have bx₂ : afterCall.machine.data.regs.rbx = body.regs.rbx := by
    simpa only [machine₁, tested] using bx₂
  have field₂ : afterCall.machine.data.dmem.loadInt (afterCall.machine.data.regs.rbx.toBitVec+0x420) 4 = some count.toNat := by
    rw [bx₂, ← trace₂.frame.memory.loadInt (body.regs.rbx.toBitVec+0x420) 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact field
  have load := load_body_history fetch agree tracePc traceCmp afterCall.machine.data count field₂
    coverage preempt trace₂.frame.ready comparison rxSection afterCall.history (events ++ [event])
    trace₂.observed (by rw [← pc₂]; exact trace₂.last)
  have cursor : (⟨⟨afterCall.machine.data, Image.PeerGet.entry+0x20⟩, afterCall.history⟩ : Executed) = afterCall := by rw [← pc₂]
  rw [cursor] at load
  apply eventually_weaken (historyStep fetch) _ _ _ _ load
  rintro final ⟨pc₃, bx₃, bp₃, trace₃⟩
  have writesEq : scanWrites (loaded afterCall.machine.data count) coverage = scanWrites body coverage := by
    funext a
    simp only [scanWrites, loaded, trace₂.frame.stack]
  have combine : ∀ m, EqualOutside (scanWrites (loaded afterCall.machine.data count) coverage)
      afterCall.machine.data.dmem m → EqualOutside (scanWrites body coverage) body.dmem m := by
    intro m framed a outside
    rw [writesEq] at framed
    exact (trace₂.frame.memory a outside).trans (framed a outside)
  obtain ⟨earlier, recorded₁, cuts₁⟩ := (trace₁.trans trace₂).extension
  obtain ⟨later, recorded₂, cuts₂⟩ := trace₃.extension
  refine ⟨pc₃, trace₃.frame.stack.trans trace₂.frame.stack, bx₃.trans bx₂, bp₃,
    by simpa only [loaded, bx₂] using trace₃.frame.output,
    trace₃.frame.ready, combine _ trace₃.frame.memory, trace₃.last, (trace₁.stable.trans trace₂.stable).trans trace₃.stable, af, ?_, earlier ++ later, ?_, ?_⟩
  · simpa only [event, machine₁] using trace₃.observed
  · rw [recorded₂, recorded₁, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact (cuts₁ q h cut).memory
    · exact combine _ (cuts₂ q h cut).memory

#print axioms nonnull_guard_history
#print axioms nonnull_prefix_history
end Binary.PeerGet
