import CallbackLeafHistory
import ServiceObservation
import LookupCoverageCalls

namespace Binary.LookupCoverage.First
open TrustBase LookupObservation Callback
local instance : Labels := Image.linkedLabels

/-- History-aware callback application in the caller's actual prefix.
    Interior cuts/observations are excluded by the named service contract,
    while physical readiness and preservation are proved from memory. -/
theorem observed_callback (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : LeafService fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (layout : Context) (preempt : BitVec 32) (s : MachineState) (returnAddress : UInt64)
    (outer : UInt64) (outside : s.data.regs.rsp≠outer+8)
    (atEntry : s.pc = address) (entry : EntryFrame s returnAddress)
    (state : Context.At layout preempt s.data.dmem)
    (allowed : layout.Allowed preempt kind)
    (stack : Context.Separated layout (InRange s.data.regs.rsp.toBitVec 8))
    (metadata : Context.Separated layout (Context.metadataBytes layout))
    (preemptFrame : Context.Separated layout (InRange preemptCountAddress 4))
    (rxSection : Nat) (front : List MachineState) (events : List Point)
    (observed : observeHistory (edge rxSection) (front ++ [s]) = .ok events) :
    Eventually (guardedHistoryStep fetch (StackGuard outer))
      (fun t => Returned s t.machine returnAddress ∧
        Context.At layout preempt t.machine.data.dmem ∧
        EqualOutside (Context.writes layout) s.data.dmem t.machine.data.dmem ∧
        observeHistory (edge rxSection) t.history = .ok events ∧
        t.history.getLast? = some t.machine ∧
        ∃ tail, t.history = front ++ s :: tail ∧
          (s :: tail).getLast? = some t.machine ∧
          (∀ q ∈ (s :: tail).dropLast, q.pc ∉ Image.cutPoints) ∧
          NoAnchoredReentry (s :: tail))
      ⟨s, front ++ [s]⟩ := by
  have returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec=some returnAddress.toBitVec := by
    simp only [load64,entry.2,Option.map_some,BitVec.ofInt_natCast]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    simp
  have raw := contract s returnAddress atEntry
    (ready layout kind preempt s returnAddress.toBitVec state allowed returnRead stack) entry
  have run : Eventually (historyStep fetch) (fun t => Returned s t.machine returnAddress ∧
      Context.At layout preempt t.machine.data.dmem ∧
      EqualOutside (Context.writes layout) s.data.dmem t.machine.data.dmem ∧
      ∀ q∈t.history.dropLast,leafGuard s.data.regs.rsp q) ⟨s,[s]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ raw
    rintro t ⟨returned,frame,effect,interior⟩
    have preserved := state_preserved layout kind preempt s t.machine returnAddress.toBitVec
      state allowed returnRead metadata preemptFrame effect frame
    exact ⟨returned,preserved.1,preserved.2,interior⟩
  have withLast := history_last fetch _ ⟨s, [s]⟩ rfl run
  let Q (t : Executed) : Prop := Returned s t.machine returnAddress ∧
    Context.At layout preempt t.machine.data.dmem ∧
    EqualOutside (Context.writes layout) s.data.dmem t.machine.data.dmem ∧
    t.history.getLast? = some t.machine ∧
    ∀ q∈t.history.dropLast,leafGuard s.data.regs.rsp q
  have localRun : Eventually (historyStep fetch) (fun t => Q t ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ withLast
    rintro t ⟨⟨returned, state, frame, noReentry⟩, last⟩
    exact ⟨⟨returned, state, frame, last,noReentry⟩,fun q hq => (noReentry q hq).2⟩
  have joined := silent_service fetch rxSection Q s localRun front events observed
  have guarded := history_guard_suffix joined (by simp) (by
    rintro t ⟨localState,tail,⟨_,_,_,_,safe⟩,_,localHistory,recorded,_⟩
    refine ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using recorded,?_⟩
    intro q member
    have inside := safe q (by simpa only [localHistory] using member)
    exact fun equal => outside (inside.1.symm.trans equal))
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨localState, tail, ⟨returned, state, frame, last,_⟩, machine,
    localHistory, history, observed, noReentry⟩
  rw [localHistory, ← machine] at last
  refine ⟨machine ▸ returned, machine ▸ state, machine ▸ frame, observed, ?_,
    tail, history, last, ?_, ?_⟩
  · rw [history, List.getLast?_append, last]
    rfl
  · intro q present
    exact no_reentry_cuts localState.history noReentry q (by simpa only [localHistory] using present)

  · simpa only [localHistory] using noReentry

#print axioms observed_callback
end Binary.LookupCoverage.First
