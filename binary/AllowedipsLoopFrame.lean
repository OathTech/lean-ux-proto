import AllowedipsLoopRegion
import CommonBitsCalls
import AllowedipsPeerObservation
import PeerPhaseHistory

namespace Binary.AllowedipsLoop
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Lookup's common_bits CALL, four saved words and its callback return word.
The node walk itself writes no trie field. -/
def writes (stack : UInt64) (coverage : CommonBitsCoverage.Context) (a : BitVec 64) : Prop :=
  InRange (stack.toBitVec-48) 48 a ∨ coverage.writes a

structure Frame (base : MachineData) (coverage : CommonBitsCoverage.Context)
    (current : MachineData) : Prop where
  ready : CommonBitsCoverage.CallsReady coverage current
  stack : current.regs.rsp = base.regs.rsp
  width : current.regs.r12 = base.regs.r12
  family : current.regs.r13 = base.regs.r13
  memory : EqualOutside (writes base.regs.rsp coverage) base.dmem current.dmem
  mapped : ∀ n < 6, (current.dmem.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true
  coverageSeparate : ∀ a, coverage.bytes a → ¬InRange (base.regs.rsp.toBitVec-48) 48 a

theorem Frame.initial (base : MachineData) (coverage : CommonBitsCoverage.Context)
    (ready : CommonBitsCoverage.CallsReady coverage base)
    (mapped : ∀ n < 6, (base.dmem.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true)
    (coverageSeparate : ∀ a, coverage.bytes a → ¬InRange (base.regs.rsp.toBitVec-48) 48 a) :
    Frame base coverage base :=
  ⟨ready,rfl,rfl,rfl,(fun _ _ => rfl),mapped,coverageSeparate⟩

theorem Frame.congr {base current next : MachineData} {coverage}
    (frame : Frame base coverage current)
    (memory : next.dmem = current.dmem) (stack : next.regs.rsp = current.regs.rsp)
    (width : next.regs.r12 = current.regs.r12) (family : next.regs.r13 = current.regs.r13) :
    Frame base coverage next :=
  ⟨frame.ready.congr memory stack,stack.trans frame.stack,width.trans frame.width,
    family.trans frame.family,(by rw [memory]; exact frame.memory),
    (by rw [memory]; exact frame.mapped),frame.coverageSeparate⟩

theorem stack_slot_window (stack : UInt64) (n : Nat) (bound : n < 6) :
    stack.toBitVec-.ofNat 64 ((n+1)*8) = stack.toBitVec-48+.ofNat 64 (8*(5-n)) := by
  have number : 48 = (n+1)*8+8*(5-n) := by omega
  rw [show (48 : BitVec 64) = .ofNat 64 48 from rfl,number,BitVec.ofNat_add,
    ←BitVec.sub_sub,BitVec.sub_add_cancel]

/-- Each required scratch word is inside the single concrete scratch region. -/
theorem stack_slot_inside (stack : UInt64) (n : Nat) (bound : n < 6) (a : BitVec 64)
    (inside : InRange (stack.toBitVec-.ofNat 64 ((n+1)*8)) 8 a) :
    InRange (stack.toBitVec-48) 48 a := by
  obtain ⟨byte,byteBound,address⟩ := inside
  refine ⟨8*(5-n)+byte,by omega,?_⟩
  simpa only [stack_slot_window stack n bound,BitVec.ofNat_add,BitVec.add_assoc] using address

def Cuts (base : MachineData) (coverage : CommonBitsCoverage.Context)
    (history : List MachineState) : Prop :=
  ∀ q ∈ history, (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints) →
    EqualOutside (writes base.regs.rsp coverage) base.dmem q.data.dmem

theorem Cuts.append {base coverage first second}
    (a : Cuts base coverage first) (b : Cuts base coverage second) :
    Cuts base coverage (first ++ second) := by
  intro q member cut
  rcases List.mem_append.mp member with h | h
  · exact a q h cut
  · exact b q h cut

/-- A loop segment retains its real history and physical frames at every
M2 cut. Count phase stability covers every actual prefix, including callbacks. -/
structure Trace (base : MachineData) (coverage : CommonBitsCoverage.Context)
    (rxSection : Nat) (initialHistory : List MachineState)
    (events : List LookupObservation.Point) (current : Executed) : Prop where
  frame : Frame base coverage current.machine.data
  observed : observeHistory (AllowedipsObservation.edge rxSection) current.history = .ok events
  last : current.history.getLast? = some current.machine
  extension : ∃ tail, current.history = initialHistory ++ tail ∧ Cuts base coverage tail
  stable : PeerCountPhase.StableExtension initialHistory current.history

theorem Trace.trans {base coverage rxSection history events nextEvents current next}
    (first : Trace base coverage rxSection history events current)
    (second : Trace base coverage rxSection current.history nextEvents next) :
    Trace base coverage rxSection history nextEvents next := by
  obtain ⟨a,ha,ca⟩ := first.extension
  obtain ⟨b,hb,cb⟩ := second.extension
  exact ⟨second.frame,second.observed,second.last,⟨a++b,
    by rw [hb,ha,List.append_assoc],ca.append cb⟩,first.stable.trans second.stable⟩

theorem history_restore {history : List MachineState} {s : MachineState}
    (last : history.getLast? = some s) : history.dropLast ++ [s] = history := by
  exact Binary.history_restore last

/-- Join a concrete local path to the incoming real history. All source
observations are computed from edges, and scanner stability follows from
proved exclusion of the two peer mutation/return PCs. -/
theorem Trace.of_path {base coverage rxSection history events current next}
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some current)
    (path : List MachineState) (head : path.head? = some current)
    (recorded : next.history = history.dropLast ++ path)
    (lastNext : path.getLast? = some next.machine)
    (frame : Frame base coverage next.machine.data)
    (delta : List LookupObservation.Point)
    (localObserved : observeHistory (AllowedipsObservation.edge rxSection) path = .ok delta)
    (cuts : Cuts base coverage path)
    (ordinary : ∀ q ∈ path.dropLast, PeerCountPhase.Ordinary q) :
    Trace base coverage rxSection history (events ++ delta) next := by
  cases path with
  | nil => cases head
  | cons first tail =>
    have eq : first = current := Option.some.inj head
    subst first
    have restore := history_restore last
    have full : next.history = history ++ tail := by
      calc next.history = history.dropLast ++ current :: tail := recorded
           _ = (history.dropLast ++ [current]) ++ tail := by simp
           _ = history ++ tail := by rw [restore]
    refine ⟨frame,?_,?_,⟨tail,full,?_⟩,?_⟩
    · rw [recorded,observeHistory_splice,restore,observed,localObserved]
      rfl
    · rw [recorded,List.getLast?_append,lastNext]
      rfl
    · intro q member atCut
      exact cuts q (.tail _ member) atCut
    · have stable := PeerCountPhase.StableExtension.of_ordinary history.dropLast current tail ordinary
      simpa only [restore, ← recorded] using stable

/-- Concrete scalar-region bridge used below. Its three static PC premises
are discharged on the actual decoded list, not exported by the function Pre. -/
theorem quiet_trace {fetch pc code}
    (layout : LaidOut fetch pc code) (base s : MachineData)
    (coverage : CommonBitsCoverage.Context) (P : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All
      (fun t => P t ∧ Frame base coverage t.data))
    (initial : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,pc⟩)
    (silent : ∀ address ∈ regionPCs pc code, ∀ before after,
      before.pc = address → AllowedipsObservation.edge rxSection before after = .ok [])
    (noInterior : ∀ address ∈ (regionPCs pc code).tail, ¬(address ∈ AllowedipsImage.cutPoints ∨ address ∈ Image.cutPoints))
    (ordinary : ∀ address ∈ regionPCs pc code,
      address ≠ Image.PeerGet.entry+0xaf ∧ address ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧
      Trace base coverage rxSection history events t)
      ⟨⟨s,pc⟩,history⟩ := by
  have lifted := region_history layout s _ run history.dropLast
  have initialHistory := history_restore last
  rw [initialHistory] at lifted
  apply eventually_weaken (historyStep fetch) _ _ _ _ lifted
  rintro t ⟨⟨post,frame⟩,path,head,lastNext,recorded,inside⟩
  have delta : observeHistory (AllowedipsObservation.edge rxSection) path = .ok [] := by
    apply observe_silent
    intro before member after
    exact silent before.pc (inside before member).1 before after rfl
  have cutFrames : Cuts base coverage path := by
    intro q member cut
    have restore := history_restore lastNext
    rw [← restore] at member
    rcases List.mem_append.mp member with prior | endpoint
    · rcases (inside q prior).2 with eq | interior
      · simpa only [eq] using initial.memory
      · exact False.elim (noInterior q.pc interior cut)
    · simpa only [List.mem_singleton.mp endpoint] using frame.memory
  have neutral : ∀ q ∈ path.dropLast, PeerCountPhase.Ordinary q := by
    intro q member
    exact ordinary q.pc (inside q member).1
  have trace := Trace.of_path observed last path head recorded lastNext frame [] delta cutFrames neutral
  exact ⟨post, by simpa only [List.append_nil] using trace⟩

/-- Existing helper callback non-reentry facts also prove silence for the
global M2 observer; the empty list cannot contain an unchecked helper RET. -/
theorem service_observation (rxSection : Nat) (path : List MachineState)
    (old : NoAnchoredReentry path) (new : NoAllowedipsReentry path) :
    observeHistory (AllowedipsObservation.edge rxSection) path = .ok [] :=
  AllowedipsPeerObservation.global_history rxSection path []
    (AllowedipsPeerObservation.no_reentry_observations rxSection path old new)
    (by intro p member; cases member)

#print axioms Frame.congr
#print axioms Trace.trans
#print axioms Trace.of_path
#print axioms service_observation
end Binary.AllowedipsLoop
