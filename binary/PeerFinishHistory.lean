import PeerSavedHistory
import PeerPhaseExceptions
import ScanFrame

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- The common return suffix for null, dead and live peers. Its callback,
    six POPs and RET all remain in the executed history. The frame holds at
    every appended anchored cut, including the real caller return state. -/
theorem finish_9d_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt body)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ scanWrites body coverage address))
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x9d⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧
      final.machine.data.regs.rax = body.regs.rbx ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem final.machine.data.dmem ∧
      observeHistory (LookupObservation.edge rxSection) final.history =
        .ok (events ++ [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ tail, final.history = history ++ tail ∧
        ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
          EqualOutside (scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x9d⟩, history⟩ := by
  have call := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨body, Image.PeerGet.entry+0x9d⟩, history⟩ (agree _ _ (by rfl)) .pc contract
    body coverage preempt (ScanFrame.initial body coverage preempt ready) ((ScanFrame.initial body coverage preempt ready)).ready.pc_allowed
    rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro afterCall ⟨pc, bx, _, trace⟩
  change afterCall.machine.pc = Image.PeerGet.entry+0xa2 at pc
  have finish := historySteps_eventually fetch 8 _ _
    (return_from_saved_history fetch agree initial afterCall.machine.data returnAddress
      afterCall.history entry (trace.frame.stack.trans sp) _
      (frame.trans trace.frame.memory) savedSeparate)
  have cursor : (⟨⟨afterCall.machine.data, Image.PeerGet.entry+0xa2⟩, afterCall.history⟩ : Executed) =
      afterCall := by rw [← pc]
  rw [cursor] at finish
  have finish := history_last fetch _ _ trace.last finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨⟨returned, result, memory, recorded⟩, finalLast⟩
  let epilogue := restoreStates afterCall.machine.data initial.data.regs.rbx initial.data.regs.rbp
    initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 returnAddress
  have finalMachine : final.machine =
      ⟨restoreData afterCall.machine.data initial.data.regs.rbx initial.data.regs.rbp
        initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 7,
        .ofBitVec returnAddress.toBitVec⟩ := by
    rw [recorded] at finalLast
    simp only [List.getLast?_append, restoreStates, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.some_or] at finalLast
    exact (Option.some.inj finalLast).symm
  have restored := history_restore trace.last
  have seen := observeHistory_splice (LookupObservation.edge rxSection)
    afterCall.history.dropLast afterCall.machine epilogue
  have suffix : observeHistory (LookupObservation.edge rxSection) (afterCall.machine :: epilogue) =
      .ok [LookupObservation.returned "wg_peer_get_maybe_zero" final.machine] := by
    rw [finalMachine]
    have atEpilogue : afterCall.machine = ⟨afterCall.machine.data, Image.PeerGet.entry+0xa2⟩ := by
      rw [← pc]
    rw [atEpilogue]
    exact epilogue_observed rxSection afterCall.machine.data
      initial.data.regs.rbx initial.data.regs.rbp initial.data.regs.r12 initial.data.regs.r13
      initial.data.regs.r14 initial.data.regs.r15 returnAddress
  rw [restored, trace.observed, suffix] at seen
  obtain ⟨earlier, earlierRecorded, cuts⟩ := trace.extension
  have returning : PeerCountPhase.ReturningExtension history final.history := by
    apply trace.stable.returning
    rw [recorded]
    exact PeerCountPhase.returning_history afterCall.history afterCall.machine.data
      initial.data.regs.rbx initial.data.regs.rbp initial.data.regs.r12 initial.data.regs.r13
      initial.data.regs.r14 initial.data.regs.r15 returnAddress
      (by rw [← pc]; exact trace.last)
  refine ⟨returned, result.trans bx, memory ▸ trace.frame.ready.state,
    memory ▸ trace.frame.memory, ?_, ?_, returning, earlier ++ epilogue, ?_, ?_⟩
  · rw [recorded, ← restored, List.append_assoc]
    exact seen
  · exact finalLast
  · rw [recorded, earlierRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact (cuts q h cut).memory
    · have eq := restoreStates_memory afterCall.machine.data initial.data.regs.rbx initial.data.regs.rbp
        initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15
        returnAddress q h
      rw [eq]
      exact trace.frame.memory

#print axioms finish_9d_history
end Binary.PeerGet
