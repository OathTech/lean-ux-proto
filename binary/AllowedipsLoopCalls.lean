import AllowedipsLoopFrame
import AllowedipsLoopObservation
import CommonBitsCallbackTrace

namespace Binary.AllowedipsLoop
open TrustBase Instrumentation
local instance : Labels := Image.linkedLabels

theorem callback_subset (stack : UInt64) (coverage : CommonBitsCoverage.Context) (a : BitVec 64)
    (small : InRange (stack.toBitVec-8) 8 a ∨ coverage.writes a) : writes stack coverage a := by
  rcases small with small | covered
  · left
    obtain ⟨byte,bound,atByte⟩ := small
    refine ⟨40+byte,by omega,?_⟩
    have shift : stack.toBitVec-48+40 = stack.toBitVec-8 := by
      rw [show (48 : BitVec 64) = 8+40 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc,
      show BitVec.ofNat 64 40 = (40 : BitVec 64) from rfl, shift]
    exact atByte
  · exact .inr covered

/-- Actual instrumentation call, silent in the source observer, preserving
all loop cursor registers and frames. No ready-on-future-states premise. -/
theorem call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target,5⟩) (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target)
      (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,pc⟩)
    (quiet : Quiet pc)
    (ordinary : pc ≠ Image.PeerGet.entry+0xaf ∧ pc ≠ Image.PeerGet.entry+0x4a) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = pc+5 ∧ t.machine.data.regs.rbx = s.regs.rbx ∧
      t.machine.data.regs.rbp = s.regs.rbp ∧ t.machine.data.regs.r14 = s.regs.r14 ∧
      t.machine.data.regs.r15 = s.regs.r15 ∧ Trace base coverage rxSection history events t)
      ⟨⟨s,pc⟩,history⟩ := by
  have called := CommonBits.callback_trace fetch pc target here kind contract coverage s frame.ready
    rxSection (fun after => quiet_edge rxSection ⟨s,pc⟩ after quiet) ordinary
  have joined := history_prepend fetch _ _ called history.dropLast
  rw [history_restore last] at joined
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro final ⟨localState,⟨⟨returned,ready⟩,trace⟩,machine,recorded⟩
  obtain ⟨pcEq,sp,bx,bp,r12,r13,r14,r15⟩ := returned_caller s (pc+5) (label target) localState.machine returned
  have widen {memory : Mem 64}
      (small : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ coverage.writes a) s.dmem memory) :
      EqualOutside (writes base.regs.rsp coverage) base.dmem memory := by
    intro a outside
    apply (frame.memory a outside).trans
    exact small a (fun h => outside (by rw [← frame.stack]; exact callback_subset _ _ _ h))
  have nextFrame : Frame base coverage final.machine.data := by
    rw [machine]
    refine ⟨ready,sp.trans frame.stack,r12.trans frame.width,r13.trans frame.family,
      widen trace.frame,?_,frame.coverageSeparate⟩
    intro n bound
    by_cases first : n = 0
    · subst n
      change (localState.machine.data.dmem.loadInt (base.regs.rsp.toBitVec-8) 8).isSome = true
      rw [←frame.stack,←sp]
      exact ready.mapped
    · have unchanged := trace.frame.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8 (by
        intro byte byteBound written
        rcases written with pushed | covered
        · rw [frame.stack] at pushed
          have a := stack_slot_window base.regs.rsp n bound
          have b := stack_slot_window base.regs.rsp 0 (by decide)
          change base.regs.rsp.toBitVec-8 = _ at b
          rw [a,b] at pushed
          exact stack_slots_disjoint (base.regs.rsp.toBitVec-48) (5-n) 5
            (by omega) (by omega) (by omega) _ ⟨byte,byteBound,rfl⟩ pushed
        · exact frame.coverageSeparate _ (.inr (.inr ⟨covered.1,.inr covered.2⟩))
            (stack_slot_inside base.regs.rsp n bound _ ⟨byte,byteBound,rfl⟩))
      rw [←unchanged]
      exact frame.mapped n bound
  obtain ⟨points,localObserved,signature⟩ := trace.observed
  have empty : points = [] := List.map_eq_nil_iff.mp signature
  subst points
  have localTrace := Trace.of_path observed last localState.history trace.head recorded
    (by rw [machine]; exact trace.last) nextFrame [] localObserved
    (fun q member cut => widen (trace.cuts q member cut)) trace.ordinary
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa only [machine] using pcEq
  · simpa only [machine] using bx
  · simpa only [machine] using bp
  · simpa only [machine] using r14
  · simpa only [machine] using r15
  · simpa only [List.append_nil] using localTrace

#print axioms callback_subset
#print axioms call
end Binary.AllowedipsLoop
