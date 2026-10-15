import LookupCallHistory
import AllowedipsServices
import AllowedipsLoopObservation
import ScanFrame
set_option linter.unusedSimpArgs false

namespace Binary.AllowedipsBh
open TrustBase
local instance : Labels := Image.linkedLabels

def countArgument (s : MachineData) : MachineData :=
  s.setReg (.low .rsi .W32) 512

def returnArgument (s : MachineData) : MachineData :=
  (countArgument s).setReg (.low .rdi .W64) (AllowedipsImage.Lookup.entry+0x137).toBitVec

def called (s : MachineData) : MachineState :=
  Instrumentation.calledState (returnArgument s) (AllowedipsImage.Lookup.entry+0x13c)
    (.ofNat 0xffffffff810732c0)

theorem count_argument (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, AllowedipsImage.Lookup.entry+0x12b⟩, history⟩ := by
  refine instruction_history fetch _ history
    (fun t => t = ⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩) ?_
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x12b) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Operand.interp, ConstExpr.interp,
    MachineData.set, Effects.All, countArgument]
  rfl

theorem return_argument (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩, history⟩ := by
  refine instruction_history fetch _ history
    (fun t => t = ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩) ?_
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x130) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, AddrExpr.interp, ConstExpr.interp,
    Effects.All, returnArgument, AllowedipsImage.Lookup.entry, BitVec.toAddressSize,
    BitVec.signed, BitVec.ofInt_toInt, BitVec.take]

def argumentStates (s : MachineData) : List MachineState :=
  [⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩,
   ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩, called s]

theorem arguments_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (history : List MachineState) :
    historySteps fetch 3 (fun t => t.machine = called s ∧ t.history = history ++ argumentStates s)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x12b⟩, history⟩ := by
  rw [show 3 = 1+2 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (count_argument fetch agree s history)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩,
      history ++ [⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩]⟩ := by cases t; simp_all
  rw [cursor, show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (return_argument fetch agree s _)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩,
      history ++ [⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩,
        ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  have mapped' : ((returnArgument s).dmem.loadInt ((returnArgument s).regs.rsp.toBitVec-8) 8).isSome = true := by
    simpa [returnArgument, countArgument, MachineData.setReg, Reg64s.set, Reg64s.set64] using mapped
  have call := Instrumentation.call_instruction fetch (AllowedipsImage.Lookup.entry+0x137)
    "L_ffffffff810732c0" (agree _ _ (by rfl)) (returnArgument s)
    (history ++ [⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩,
      ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩]) mapped'
  apply historySteps_mono fetch 1 _ _ _ _ call
  rintro t ⟨machine, recorded⟩
  have final : t.machine = called s := machine
  refine ⟨final, ?_⟩
  simpa only [final, argumentStates, List.append_assoc, List.cons_append, List.nil_append] using recorded

theorem arguments_observed (rxSection : Nat) (s : MachineData) :
    observeHistory (AllowedipsObservation.edge rxSection)
      (⟨s, AllowedipsImage.Lookup.entry+0x12b⟩ :: argumentStates s) = .ok [] := by
  have first := AllowedipsLoop.quiet_edge rxSection ⟨s, AllowedipsImage.Lookup.entry+0x12b⟩
    ⟨countArgument s,AllowedipsImage.Lookup.entry+0x130⟩ (by dsimp only; unfold AllowedipsLoop.Quiet; decide)
  have second := AllowedipsLoop.quiet_edge rxSection ⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩
    ⟨returnArgument s,AllowedipsImage.Lookup.entry+0x137⟩ (by dsimp only; unfold AllowedipsLoop.Quiet; decide)
  have third := AllowedipsLoop.quiet_edge rxSection ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩
    (called s) (by dsimp only; unfold AllowedipsLoop.Quiet; decide)
  simp [observeHistory,argumentStates,first,second,third]
  rfl

theorem called_shape (s : MachineData) :
    (called s).data.regs = {s.regs with
      rsp := s.regs.rsp-8
      rsi := 512
      rdi := (AllowedipsImage.Lookup.entry+0x137).toUInt64} ∧
    (called s).data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8
      (AllowedipsImage.Lookup.entry+0x13c).toBitVec.toInt := by
  simp [called, Instrumentation.calledState, returnArgument, countArgument,
    MachineData.setReg, Reg64s.set, Reg64s.set64]
  rfl

theorem called_entry (s : MachineData) (aligned : s.regs.rsp.toNat % 8 = 0) :
    EntryFrame (called s) (AllowedipsImage.Lookup.entry+0x13c).toUInt64 := by
  constructor
  · rw [(called_shape s).1]
    change (s.regs.rsp-8).toNat % 8 = 0
    simp only [UInt64.toNat_sub, show (8 : UInt64).toNat = 8 from rfl]
    have bound := s.regs.rsp.toNat_lt_size
    omega
  · rw [(called_shape s).1, (called_shape s).2]
    simp only [UInt64.toBitVec_sub, show (8 : UInt64).toBitVec = 8#64 from rfl]
    exact load64_store _ _ _

/-- Readiness is derived after the CALL push. The no-work condition is
    checked on the actual updated count, including nested disable counts. -/
theorem called_ready (s : MachineData) (count : BitVec 32)
    (preempt : s.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int))
    (hardirq : count &&& 0x000f0000 = 0)
    (pending : (count+1-512) &&& 0x00ffff00 = 0 → s.dmem.loadInt softirqPendingAddress 2 = some 0)
    (preemptApart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (pendingApart : (count+1-512) &&& 0x00ffff00 = 0 →
      ∀ a, InRange softirqPendingAddress 2 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a) :
    BhEnableReady (called s) := by
  have frame := storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (AllowedipsImage.Lookup.entry+0x13c).toBitVec.toInt
  have countRead := frame.loadInt preemptCountAddress 4 (by
    intro byte bound; exact preemptApart _ ⟨byte, bound, rfl⟩)
  have sp : (called s).data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-8 := by simp [(called_shape s).1]
  have amount : (called s).data.regs.get (.low .rsi .W32) = 512#32 := by
    simp [(called_shape s).1, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  refine ⟨count, ?_, hardirq, ?_, ?_⟩
  · rw [(called_shape s).2, ← countRead]
    exact preempt
  · rw [amount]
    intro need
    have read := frame.loadInt softirqPendingAddress 2 (by
      intro byte bound; exact pendingApart need _ ⟨byte, bound, rfl⟩)
    rw [(called_shape s).2, ← read]
    exact pending need
  · simpa only [sp] using preemptApart

#print axioms arguments_history
#print axioms arguments_observed
#print axioms called_shape
#print axioms called_entry
#print axioms called_ready

/-- Apply the named physical BH service contract to the executed CALL.
    Service states remain in history; no anchored event/cut is discarded. -/
theorem enable_history (fetch : Int64 → Option Decoded)
    (agree : AllowedipsDecoderAgreement fetch) (contract : AllowedipsBhEnableContract fetch)
    (s : MachineData) (count : BitVec 32)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (preempt : s.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int))
    (hardirq : count &&& 0x000f0000 = 0)
    (pending : (count+1-512) &&& 0x00ffff00 = 0 → s.dmem.loadInt softirqPendingAddress 2 = some 0)
    (preemptApart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (pendingApart : (count+1-512) &&& 0x00ffff00 = 0 →
      ∀ a, InRange softirqPendingAddress 2 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, AllowedipsImage.Lookup.entry+0x12b⟩) :
    Eventually (historyStep fetch) (fun t =>
      Returned (called s) t.machine (AllowedipsImage.Lookup.entry+0x13c).toUInt64 ∧
      t.machine.data.dmem.loadInt preemptCountAddress 4 = some ((count-512).toNat : Int) ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨
        InRange preemptCountAddress 4 a) s.dmem t.machine.data.dmem ∧
      observeHistory (AllowedipsObservation.edge rxSection) t.history = .ok events ∧
      t.history.getLast? = some t.machine ∧
      ∃ tail, t.history = history ++ argumentStates s ++ tail ∧
        (called s :: tail).getLast? = some t.machine ∧
        (NoAnchoredReentry (called s :: tail) ∧ NoAllowedipsReentry (called s :: tail)))
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x12b⟩, history⟩ := by
  have args := historySteps_eventually fetch 3 _ _ (arguments_history fetch agree s mapped history)
  apply eventually_trans (historyStep fetch) _ _ _ args
  rintro callee ⟨machine, recorded⟩
  let front := history ++ [⟨countArgument s, AllowedipsImage.Lookup.entry+0x130⟩,
    ⟨returnArgument s, AllowedipsImage.Lookup.entry+0x137⟩]
  have cursor : callee = ⟨called s, front ++ [called s]⟩ := by
    cases callee; simp_all [front, argumentStates, List.append_assoc]
  rw [cursor]
  have restored := LookupHistory.history_restore last
  have seen := observeHistory_splice (AllowedipsObservation.edge rxSection)
    history.dropLast ⟨s, AllowedipsImage.Lookup.entry+0x12b⟩ (argumentStates s)
  rw [restored, observed, arguments_observed] at seen
  have calleeObserved : observeHistory (AllowedipsObservation.edge rxSection)
      (front ++ [called s]) = .ok events := by
    change observeHistory (AllowedipsObservation.edge rxSection)
      (history.dropLast ++ ⟨s, AllowedipsImage.Lookup.entry+0x12b⟩ :: argumentStates s) = .ok (events ++ []) at seen
    have joined : front ++ [called s] = history ++ argumentStates s := by
      simp [front, argumentStates, List.append_assoc]
    rw [joined, ← restored, List.append_assoc]
    simpa only [List.singleton_append, List.append_nil] using seen
  have run := contract (called s) (AllowedipsImage.Lookup.entry+0x13c).toUInt64 rfl
    (called_ready s count preempt hardirq pending preemptApart pendingApart) (called_entry s aligned)
  have runLast := history_last fetch _ ⟨called s, [called s]⟩ (by simp) run
  let Q : Executed → Prop := fun t =>
    Returned (called s) t.machine (AllowedipsImage.Lookup.entry+0x13c).toUInt64 ∧
    EqualOutside (InRange preemptCountAddress 4) (called s).data.dmem t.machine.data.dmem ∧
    (∀ old : BitVec 32, (called s).data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      t.machine.data.dmem.loadInt preemptCountAddress 4 =
        some ((old-(called s).data.regs.get (.low .rsi .W32)).toNat : Int)) ∧
    t.history.getLast? = some t.machine
  have regrouped : Eventually (historyStep fetch) (fun t => Q t ∧ (NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history))
      ⟨called s, [called s]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ runLast
    intro t h
    exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2⟩, h.1.2.2.2⟩
  have service := AllowedipsObservation.silent_service fetch rxSection _ (called s)
    regrouped front events calleeObserved
  apply eventually_weaken (historyStep fetch) _ _ _ _ service
  rintro t ⟨localState, tail, ⟨returned, frame, effect, localLast⟩,
    final, localHistory, recorded, seen, noReentry⟩
  have pushed := storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (AllowedipsImage.Lookup.entry+0x13c).toBitVec.toInt
  have countRead : (called s).data.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int) := by
    rw [(called_shape s).2]
    have read := pushed.loadInt preemptCountAddress 4 (by
      intro byte bound; exact preemptApart _ ⟨byte, bound, rfl⟩)
    exact read.symm.trans preempt
  have amount : (called s).data.regs.get (.low .rsi .W32) = 512#32 := by
    simp [(called_shape s).1, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  have countFinal := effect count countRead
  rw [amount] at countFinal
  have lastLocal : (called s :: tail).getLast? = some t.machine := by
    rw [← localHistory, final]
    exact localLast
  refine ⟨by rw [final]; exact returned, by rw [final]; exact countFinal, ?_, seen, ?_,
    tail, ?_, lastLocal, by rw [← localHistory]; exact noReentry⟩
  · rw [(called_shape s).2] at frame
    rw [final]
    exact pushed.trans frame
  · simp [recorded, List.getLast?_append, lastLocal]
  · simpa only [front, argumentStates, List.append_assoc, List.cons_append, List.nil_append] using recorded

#print axioms enable_history
end Binary.AllowedipsBh
