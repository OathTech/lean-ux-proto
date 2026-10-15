import CallHistory
import LookupType

namespace Binary.LookupHistory
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Physical component of the bucket-loop invariant. RBX is the moving
    node/entry cursor and RBP is the loaded index; neither is fixed here.
    This is not the whole-World relation. -/
def scanWrites (base : MachineData) (coverage : KcovLayout) (a : Address) : Prop :=
  InRange (base.regs.rsp.toBitVec-8) 8 a ∨ KcovBufferBytes coverage a

structure ScanFrame (base : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (current : MachineData) : Prop where
  ready : PeerGet.CallsReady coverage preempt current
  stack : current.regs.rsp = base.regs.rsp
  query : current.regs.r12 = base.regs.r12
  output : current.regs.r13 = base.regs.r13
  kinds : current.regs.r14 = base.regs.r14
  saved : current.regs.r15 = base.regs.r15
  memory : EqualOutside (scanWrites base coverage) base.dmem current.dmem

theorem ScanFrame.initial (base : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : PeerGet.CallsReady coverage preempt base) : ScanFrame base coverage preempt base :=
  ⟨ready, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem ScanFrame.congr {base current next : MachineData} {coverage preempt}
    (frame : ScanFrame base coverage preempt current)
    (memory : next.dmem = current.dmem) (stack : next.regs.rsp = current.regs.rsp)
    (query : next.regs.r12 = current.regs.r12) (output : next.regs.r13 = current.regs.r13)
    (kinds : next.regs.r14 = current.regs.r14) (saved : next.regs.r15 = current.regs.r15) :
    ScanFrame base coverage preempt next :=
  ⟨frame.ready.congr memory stack, stack.trans frame.stack, query.trans frame.query,
    output.trans frame.output, kinds.trans frame.kinds, saved.trans frame.saved,
    by rw [memory]; exact frame.memory⟩

theorem ScanFrame.bucket {base current : MachineData} {coverage preempt}
    (frame : ScanFrame base coverage preempt current)
    (head : Address) (es : List (Address × Leanux.WG.IndexEntry))
    (represented : BucketShape base.dmem head es)
    (separate : ∀ cell ∈ es, ∀ address, BucketShapeReads cell.1 address →
      ¬scanWrites base coverage address) :
    BucketShape current.dmem head es :=
  BucketShape.frame_reads frame.memory es separate head represented

def ScanCuts (base : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history, s.pc ∈ Image.cutPoints → ScanFrame base coverage preempt s.data

theorem ScanCuts.append {base coverage preempt first second}
    (a : ScanCuts base coverage preempt first) (b : ScanCuts base coverage preempt second) :
    ScanCuts base coverage preempt (first ++ second) := by
  intro s member cut
  rcases List.mem_append.mp member with h | h
  · exact a s h cut
  · exact b s h cut

/-- Actual suffix of a scan execution, retaining its observations and the
    physical frame at every appended cut. -/
structure ScanTrace (base : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (rxSection : Nat) (initialHistory : List MachineState)
    (events : List LookupObservation.Point) (current : Executed) : Prop where
  frame : ScanFrame base coverage preempt current.machine.data
  observed : observeHistory (LookupObservation.edge rxSection) current.history = .ok events
  last : current.history.getLast? = some current.machine
  extension : ∃ tail, current.history = initialHistory ++ tail ∧ ScanCuts base coverage preempt tail

theorem ScanTrace.trans {base coverage preempt rxSection history events current next}
    (first : ScanTrace base coverage preempt rxSection history events current)
    (second : ScanTrace base coverage preempt rxSection current.history events next) :
    ScanTrace base coverage preempt rxSection history events next := by
  obtain ⟨a, ha, ca⟩ := first.extension
  obtain ⟨b, hb, cb⟩ := second.extension
  exact ⟨second.frame, second.observed, second.last, a++b,
    by rw [hb, ha, List.append_assoc], ca.append cb⟩

theorem history_restore {history : List MachineState} {s : MachineState}
    (last : history.getLast? = some s) : history.dropLast ++ [s] = history := by
  have nonempty : history ≠ [] := by intro empty; rw [empty] at last; cases last
  have lastEq : history.getLast nonempty = s := by
    simpa only [List.getLast?_eq_some_getLast nonempty, Option.some.injEq] using last
  rw [← lastEq]
  exact List.dropLast_concat_getLast nonempty

/-- Append a concrete instruction suffix after its symbolic execution has
    supplied every successor and its cut facts. -/
theorem ScanTrace.of_suffix {base coverage preempt rxSection history events current next}
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some current)
    (tail : List MachineState) (recorded : next.history = history ++ tail)
    (frame : ScanFrame base coverage preempt next.machine.data)
    (lastNext : (current :: tail).getLast? = some next.machine)
    (silent : observeHistory (LookupObservation.edge rxSection) (current :: tail) = .ok [])
    (cuts : ScanCuts base coverage preempt tail) :
    ScanTrace base coverage preempt rxSection history events next := by
  have restored := history_restore last
  have combined := observeHistory_splice (LookupObservation.edge rxSection)
    history.dropLast current tail
  rw [restored, observed, silent] at combined
  change observeHistory (LookupObservation.edge rxSection) (history.dropLast ++ current :: tail) =
    .ok (events ++ []) at combined
  refine ⟨frame, ?_, ?_, tail, recorded, cuts⟩
  · rw [recorded, ← restored, List.append_assoc]
    simpa only [List.singleton_append, List.append_nil] using combined
  · rw [recorded, ← restored, List.append_assoc]
    simp only [List.singleton_append]
    simp only [List.getLast?_append, lastNext, Option.some_or]

/-- Execute a real instrumentation call. Both its caller-state frame and
    every newly reached anchored cut preserve the physical scan invariant.
    Service interiors are retained in history and excluded only by the
    named no-anchored-reentry service contract. -/
theorem scan_call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨Instrumentation.callInstruction target, 5⟩) (kind : KcovKind)
    (contract : ServiceReturns fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (base s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s)
    (rxSection : Nat) (front : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) (front ++ [⟨s, pc⟩]) = .ok events)
    (silent : LookupObservation.edge rxSection ⟨s, pc⟩
      (Instrumentation.calledState s (pc+5) (label target)) = .ok []) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = pc+5 ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧ t.machine.data.regs.rbp = s.regs.rbp ∧
      ScanFrame base coverage preempt t.machine.data ∧
      observeHistory (LookupObservation.edge rxSection) t.history = .ok events ∧
      t.history.getLast? = some t.machine ∧
      ∃ tail, t.history = (front ++ [⟨s, pc⟩]) ++ tail ∧
        ScanCuts base coverage preempt tail)
      ⟨⟨s, pc⟩, front ++ [⟨s, pc⟩]⟩ := by
  have call := Instrumentation.observed_call fetch pc target here kind contract s coverage preempt
    frame.ready rxSection front events [] observed silent
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro t ⟨ret, ready, memory, observations, last, tail, recorded, localLast, noCuts⟩
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
  refine ⟨finalPC, bx, bp, preserved, by simpa only [List.append_nil] using observations, last,
    Instrumentation.calledState s (pc+5) (label target) :: tail, recorded, ?_⟩
  let localHistory := Instrumentation.calledState s (pc+5) (label target) :: tail
  have nonempty : localHistory ≠ [] := by simp [localHistory]
  change localHistory.getLast? = some t.machine at localLast
  have lastEq : localHistory.getLast nonempty = t.machine := by
    simpa only [List.getLast?_eq_some_getLast nonempty, Option.some.injEq] using localLast
  have restored : localHistory.dropLast ++ [t.machine] = localHistory := by
    rw [← lastEq]
    exact List.dropLast_concat_getLast nonempty
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
    (contract : ServiceReturns fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (base : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt s.machine.data)
    (rxSection : Nat) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) s.history = .ok events)
    (last : s.history.getLast? = some s.machine)
    (silent : LookupObservation.edge rxSection s.machine
      (Instrumentation.calledState s.machine.data (s.machine.pc+5) (label target)) = .ok []) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = s.machine.pc+5 ∧
      t.machine.data.regs.rbx = s.machine.data.regs.rbx ∧
      t.machine.data.regs.rbp = s.machine.data.regs.rbp ∧
      ScanTrace base coverage preempt rxSection s.history events t) s := by
  have restored := history_restore last
  have call := scan_call fetch s.machine.pc target here kind contract base s.machine.data
    coverage preempt frame rxSection s.history.dropLast events
    (by simpa only [restored] using observed) silent
  have initial : (⟨⟨s.machine.data, s.machine.pc⟩, s.history.dropLast ++ [⟨s.machine.data, s.machine.pc⟩]⟩ : Executed) = s := by
    cases s with
    | mk machine history => cases machine; simp_all
  rw [initial] at call
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro t ⟨pc, bx, bp, frame, seen, last, tail, recorded, cuts⟩
  exact ⟨pc, bx, bp, frame, seen, last, tail, by simpa only [restored] using recorded, cuts⟩

#print axioms ScanTrace.of_suffix
#print axioms ScanTrace.trans
#print axioms scan_call_cursor

#print axioms ScanFrame.initial
#print axioms ScanFrame.congr
#print axioms ScanFrame.bucket
#print axioms ScanCuts.append
#print axioms scan_call
end Binary.LookupHistory
