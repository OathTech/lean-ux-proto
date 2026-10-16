import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import AllowedipsPeerFinishHistory
import AllowedipsPeerClearHistory

namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory AllowedipsPeerHistory
open TrustBase LookupHistory AllowedipsPeerHistory
local instance : Labels := Image.linkedLabels

/-- The accepted null edge emits its real machine state, with the actual
    undefined TEST flag and a physical frame at both appended cuts. -/
theorem null_guard_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body) (null : body.regs.rbx = 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x12⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbx .W64) body af, Image.PeerGet.entry+0xdd⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull true t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x12⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_null_guard fetch agree body history)
  rintro t ⟨af, machine, recorded⟩
  have isZero : body.regs.get (.low .rbx .W64) = 0#64 := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, null]
  simp only [isZero, BEq.rfl, ite_true] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbx .W64) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, AllowedipsPeerObservation.edge, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

/-- Clearing the helper's return pointer changes only RBX and flags; it
    preserves the physical scan-style frame and emits no source decision. -/
theorem clear_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xdd⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = Image.PeerGet.entry+0x9d ∧ t.machine.data.regs.rbx = 0 ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0xdd⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (clear_history fetch agree body history)
  rintro t ⟨af, machine, recorded⟩
  have fields := zeroed_shape body af
  have nextFrame : ScanFrame base coverage preempt (zeroed body (.low .rbx .W32) af) := by
    apply frame.congr fields.2
    all_goals rw [fields.1]
  refine ⟨congrArg MachineState.pc machine, ?_,
    StableTrace.of_suffix observed last _ recorded ?_ ?_ (clear_observed rxSection body af) ?_⟩
  · rw [machine, fields.1]
  · simpa only [machine] using nextFrame
  · simp [machine]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

/-- Complete null-pointer suffix, including the callback and real RET.
    The emitted null decision is tied to its actual successor, and the
    returned event to the final state; no expected World is supplied. -/
theorem null_suffix_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (null : body.regs.rbx = 0) (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (ready : AllowedipsPeerCoverage.CallsReady coverage preempt body)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ AllowedipsPeerHistory.scanWrites body coverage address))
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x12⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧ final.machine.data.regs.rax = 0 ∧
      AllowedipsPeerCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ af, observeHistory (AllowedipsPeerObservation.edge rxSection) final.history =
        .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull true
            ⟨tested (.low .rbx .W64) body af, Image.PeerGet.entry+0xdd⟩,
          LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints) →
            EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x12⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (null_guard_history fetch agree body body coverage preempt (ScanFrame.initial body coverage preempt ready)
      null rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, guardMachine, guardTrace⟩
  let nullEvent := LookupObservation.decision rxSection .peerGetMaybeZeroNull true guarded.machine
  have pc₁ : guarded.machine.pc = Image.PeerGet.entry+0xdd := congrArg MachineState.pc guardMachine
  have clear := historySteps_eventually fetch 2 _ _
    (clear_trace fetch agree body guarded.machine.data coverage preempt guardTrace.frame
      rxSection guarded.history (events ++ [nullEvent]) guardTrace.observed
      (by rw [← pc₁]; exact guardTrace.last))
  have cursor₁ : (⟨⟨guarded.machine.data, Image.PeerGet.entry+0xdd⟩, guarded.history⟩ : Executed) = guarded := by rw [← pc₁]
  rw [cursor₁] at clear
  apply eventually_trans (historyStep fetch) _ _ _ clear
  rintro cleared ⟨pc₂, bx₂, clearTrace⟩
  have writeEq : AllowedipsPeerHistory.scanWrites cleared.machine.data coverage = AllowedipsPeerHistory.scanWrites body coverage := by
    funext a
    simp only [AllowedipsPeerHistory.scanWrites, clearTrace.frame.stack]
  have finish := finish_9d_history fetch agree contract initial cleared.machine.data returnAddress
    entry (clearTrace.frame.stack.trans sp) coverage preempt clearTrace.frame.ready
    _ (frame.trans clearTrace.frame.memory) (by
      intro address inside
      have h := savedSeparate address inside
      rw [writeEq]
      exact fun written => h (by
        rcases written with (old | earlier) | later
        · exact .inl old
        · exact .inr earlier
        · exact .inr later))
    rxSection cleared.history (events ++ [nullEvent]) clearTrace.observed
    (by rw [← pc₂]; exact clearTrace.last)
  have cursor₂ : (⟨⟨cleared.machine.data, Image.PeerGet.entry+0x9d⟩, cleared.history⟩ : Executed) = cleared := by rw [← pc₂]
  rw [cursor₂] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, _scratch, result, state, endFrame, seen, last, returning, tail, recorded, cuts⟩
  have before := guardTrace.trans clearTrace
  have wholeFrame : EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem final.machine.data.dmem := by
    rw [writeEq] at endFrame
    intro a outside
    exact (clearTrace.frame.memory a outside).trans (endFrame a outside)
  obtain ⟨earlier, earlierRecorded, earlierCuts⟩ := before.extension
  refine ⟨returned, result.trans bx₂, state, wholeFrame, last, before.stable.returning returning, af, ?_, earlier ++ tail, ?_, ?_⟩
  · simpa only [nullEvent, guardMachine, List.append_assoc, List.singleton_append] using seen
  · rw [recorded, earlierRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact (earlierCuts q h cut).memory
    · have eq := cuts q h cut
      rw [writeEq] at eq
      intro a outside
      exact (clearTrace.frame.memory a outside).trans (eq a outside)

#print axioms null_guard_history
#print axioms clear_trace
#print axioms null_suffix_history
end Binary.AllowedipsPeerGet
