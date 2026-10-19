import LookupBhHistory
import CallbackLeafHistory
import FirstScanFrame
namespace Binary.LookupBh.First
open TrustBase Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}
/-- Apply the named physical BH service contract to the executed CALL.
    Service states remain in history; no anchored event/cut is discarded. -/
theorem enable_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    (s : MachineData) (safe : CallStackSafe outer s.regs.rsp) (count : BitVec 32)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (preempt : s.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int))
    (hardirq : count &&& 0x000f0000 = 0)
    (pending : (count+1-512) &&& 0x00ffff00 = 0 → s.dmem.loadInt softirqPendingAddress 2 = some 0)
    (preemptApart : ∀ a, InRange preemptCountAddress 4 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (pendingApart : (count+1-512) &&& 0x00ffff00 = 0 →
      ∀ a, InRange softirqPendingAddress 2 a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.Lookup.entry+0x78⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      Returned (called s) t.machine (Image.Lookup.entry+0x89).toUInt64 ∧
      t.machine.data.dmem.loadInt preemptCountAddress 4 = some ((count-512).toNat : Int) ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨
        InRange preemptCountAddress 4 a) s.dmem t.machine.data.dmem ∧
      observeHistory (LookupObservation.edge rxSection) t.history = .ok events ∧
      t.history.getLast? = some t.machine ∧
      ∃ tail, t.history = history ++ argumentStates s ++ tail ∧
        (called s :: tail).getLast? = some t.machine ∧
        NoAnchoredReentry (called s :: tail))
      ⟨⟨s, Image.Lookup.entry+0x78⟩, history⟩ := by
  have args := historySteps_eventually fetch 3 _ _ (arguments_history fetch agree s mapped history)
  have args := history_guard_suffix (guard := StackGuard outer) args last (by
    rintro t ⟨machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [argumentStates,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals exact safe.1)
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ args
  rintro callee ⟨machine, recorded⟩
  let front := history ++ [⟨countArgument s, Image.Lookup.entry+0x7d⟩,
    ⟨returnArgument s, Image.Lookup.entry+0x84⟩]
  have cursor : callee = ⟨called s, front ++ [called s]⟩ := by
    cases callee; simp_all [front, argumentStates, List.append_assoc]
  rw [cursor]
  have restored := LookupHistory.history_restore last
  have seen := observeHistory_splice (LookupObservation.edge rxSection)
    history.dropLast ⟨s, Image.Lookup.entry+0x78⟩ (argumentStates s)
  rw [restored, observed, arguments_observed] at seen
  have calleeObserved : observeHistory (LookupObservation.edge rxSection)
      (front ++ [called s]) = .ok events := by
    change observeHistory (LookupObservation.edge rxSection)
      (history.dropLast ++ ⟨s, Image.Lookup.entry+0x78⟩ :: argumentStates s) = .ok (events ++ []) at seen
    have joined : front ++ [called s] = history ++ argumentStates s := by
      simp [front, argumentStates, List.append_assoc]
    rw [joined, ← restored, List.append_assoc]
    simpa only [List.singleton_append, List.append_nil] using seen
  have run := contract (called s) (Image.Lookup.entry+0x89).toUInt64 rfl
    (called_ready s count preempt hardirq pending preemptApart pendingApart) (called_entry s aligned)
  have runLast := history_last fetch _ ⟨called s, [called s]⟩ (by simp) run
  let Q : Executed → Prop := fun t =>
    Returned (called s) t.machine (Image.Lookup.entry+0x89).toUInt64 ∧
    EqualOutside (InRange preemptCountAddress 4) (called s).data.dmem t.machine.data.dmem ∧
    (∀ old : BitVec 32, (called s).data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      t.machine.data.dmem.loadInt preemptCountAddress 4 =
        some ((old-(called s).data.regs.get (.low .rsi .W32)).toNat : Int)) ∧
    t.history.getLast? = some t.machine ∧
    ∀ q∈t.history.dropLast,leafGuard (called s).data.regs.rsp q
  have regrouped : Eventually (historyStep fetch) (fun t => Q t ∧ NoAnchoredReentry t.history)
      ⟨called s, [called s]⟩ := by
    apply eventually_weaken (historyStep fetch) _ _ _ _ runLast
    intro t h
    exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.2, h.1.2.2.2⟩, fun q hq => (h.1.2.2.2 q hq).2⟩
  have service := LookupObservation.silent_service fetch rxSection _ (called s)
    regrouped front events calleeObserved
  have service := history_guard_suffix (guard := StackGuard outer) service (by simp) (by
    rintro t ⟨localState,tail,⟨_,_,_,_,interior⟩,_,localHistory,recorded,_⟩
    refine ⟨tail,by simpa only [List.append_assoc,List.singleton_append] using recorded,?_⟩
    intro q member
    have inside := interior q (by simpa only [localHistory] using member)
    have stack : (called s).data.regs.rsp=s.regs.rsp-8 := by rw [(called_shape s).1]
    exact fun equal => safe.2 (stack.symm.trans (inside.1.symm.trans equal)))
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ service
  rintro t ⟨localState, tail, ⟨returned, frame, effect, localLast,_⟩,
    final, localHistory, recorded, seen, noReentry⟩
  have pushed := storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (Image.Lookup.entry+0x89).toBitVec.toInt
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
end Binary.LookupBh.First
