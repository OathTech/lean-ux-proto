import ScanFrame
import LookupFirstCall
namespace Binary.LookupHistory.First
open TrustBase Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

def CallStackSafe (outer base : UInt64) : Prop := base≠outer+8 ∧ base-8≠outer+8

/-- Execute a real instrumentation call. Both its caller-state frame and
    every newly reached anchored cut preserve the physical scan invariant.
    Service interiors are retained in history and excluded only by the
    named no-anchored-reentry service contract. -/
theorem scan_call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨Instrumentation.callInstruction target, 5⟩) (kind : KcovKind)
    (contract : LeafService fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (base s : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt s)
    (allowed : coverage.Allowed preempt kind)
    (rxSection : Nat) (front : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) (front ++ [⟨s, pc⟩]) = .ok events)
    (silent : LookupObservation.edge rxSection ⟨s, pc⟩
      (Instrumentation.calledState s (pc+5) (label target)) = .ok [])
    (ordinary : PeerCountPhase.Ordinary ⟨s, pc⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine.pc = pc+5 ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧ t.machine.data.regs.rbp = s.regs.rbp ∧
      ScanFrame base coverage preempt t.machine.data ∧
      observeHistory (LookupObservation.edge rxSection) t.history = .ok events ∧
      t.history.getLast? = some t.machine ∧
      ∃ tail, t.history = (front ++ [⟨s, pc⟩]) ++ tail ∧
        ScanCuts base coverage preempt tail ∧
        PeerCountPhase.StableExtension (front ++ [⟨s, pc⟩]) t.history)
      ⟨⟨s, pc⟩, front ++ [⟨s, pc⟩]⟩ := by
  have call := LookupInstrumentation.First.observed_call fetch pc target here kind contract s outer (by rw [frame.stack]; exact safe.1)
    (by rw [frame.stack]; exact safe.2) coverage preempt
    frame.ready allowed rxSection front events [] observed silent
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ call
  rintro t ⟨ret, ready, memory, observations, last, tail, recorded, localLast, noCuts, noReentry⟩
  obtain ⟨finalPC, sp, bx, bp, r12, r13, r14, r15⟩ :=
    Instrumentation.returned_caller s (pc+5) (label target) t.machine ret
  have preserved : ScanFrame base coverage preempt t.machine.data := {
    ready := ready
    stack := sp.trans frame.stack
    query := r12.trans frame.query
    output := r13.trans frame.output
    kinds := r14.trans frame.kinds
    saved := r15.trans frame.saved
    memory := by
      rw [frame.stack] at memory
      intro a outside
      exact (frame.memory a outside).trans (memory a outside) }
  have stable : PeerCountPhase.StableExtension (front ++ [⟨s, pc⟩]) t.history := by
    rw [recorded, List.append_assoc, List.singleton_append]
    exact PeerCountPhase.StableExtension.call front ⟨s, pc⟩ _ tail ordinary noReentry
  refine ⟨finalPC, bx, bp, preserved, by simpa only [List.append_nil] using observations, last,
    Instrumentation.calledState s (pc+5) (label target) :: tail, recorded, ?_, stable⟩
  let localHistory := Instrumentation.calledState s (pc+5) (label target) :: tail
  change localHistory.getLast? = some t.machine at localLast
  have restored := Binary.history_restore localLast
  intro q member cut
  change q ∈ localHistory at member
  rw [← restored] at member
  rcases List.mem_append.mp member with interior | final
  · exact False.elim (noCuts q interior cut)
  · have equal : q = t.machine := List.mem_singleton.mp final
    simpa only [equal] using preserved

/-- Convenient form at an existing actual history cursor. -/
theorem scan_call_cursor (fetch : Int64 → Option Decoded) (target : Label)
    (s : Executed) (here : fetch s.machine.pc = some ⟨Instrumentation.callInstruction target, 5⟩)
    (kind : KcovKind)
    (contract : LeafService fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (base : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt s.machine.data)
    (allowed : coverage.Allowed preempt kind)
    (rxSection : Nat) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) s.history = .ok events)
    (last : s.history.getLast? = some s.machine)
    (silent : LookupObservation.edge rxSection s.machine
      (Instrumentation.calledState s.machine.data (s.machine.pc+5) (label target)) = .ok [])
    (ordinary : PeerCountPhase.Ordinary s.machine := by
      constructor <;> simp_all [Image.PeerGet.entry, Image.Lookup.entry]) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine.pc = s.machine.pc+5 ∧
      t.machine.data.regs.rbx = s.machine.data.regs.rbx ∧
      t.machine.data.regs.rbp = s.machine.data.regs.rbp ∧
      StableTrace base coverage preempt rxSection s.history events t) s := by
  have restored := history_restore last
  have call := scan_call fetch s.machine.pc target here kind contract base s.machine.data
    coverage preempt safe frame allowed rxSection s.history.dropLast events
    (by simpa only [restored] using observed) silent ordinary
  have initial : (⟨⟨s.machine.data, s.machine.pc⟩, s.history.dropLast ++ [⟨s.machine.data, s.machine.pc⟩]⟩ : Executed) = s := by
    cases s with
    | mk machine history => cases machine; simp_all
  rw [initial] at call
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ call
  rintro t ⟨pc, bx, bp, frame, seen, last, tail, recorded, cuts, stable⟩
  exact ⟨pc, bx, bp, ⟨frame, seen, last, tail, by simpa only [restored] using recorded, cuts⟩,
    by simpa only [restored] using stable⟩

#print axioms scan_call
#print axioms scan_call_cursor
end Binary.LookupHistory.First
