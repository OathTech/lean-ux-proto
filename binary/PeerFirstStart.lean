import PeerStartHistory
import LookupFirstCoverage
import PeerFirstStack
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem start_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (s : MachineData) (safe : StackSlots outer s.regs.rsp) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (state : LookupCoverage.Context.At coverage preempt s.dmem)
    (phase : preempt = coverage.entryPreempt ∨ preempt = 512+coverage.entryPreempt)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, LookupCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (returnSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 8))
    (metadataSeparate : LookupCoverage.Context.Separated coverage (LookupCoverage.Context.metadataBytes coverage))
    (preemptSeparate : LookupCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.PeerGet.entry⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine.pc = Image.PeerGet.entry+0x12 ∧
      t.machine.data.regs.rsp = s.regs.rsp-48 ∧ t.machine.data.regs.rbx = s.regs.rdi ∧
      LookupCoverage.CallsReady coverage preempt t.machine.data ∧
      EqualOutside (LookupCoverage.Context.writes coverage) (saveMemory s 7) t.machine.data.dmem ∧
      observeHistory (LookupObservation.edge rxSection) t.history = .ok events ∧
      t.history.getLast? = some t.machine ∧
      PeerCountPhase.StableExtension history t.history ∧
      ∃ tail, t.history = history ++ tail ∧
        ∀ q ∈ tail, q.pc ∈ Image.cutPoints → EqualOutside (entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have start := historySteps_eventually fetch 8 _ _ (prologue_history fetch agree s history mapped)
  have start := history_guard_suffix (guard := StackGuard outer) start last (by
    rintro t ⟨_,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [prologueStates,List.cons_append,List.nil_append,List.dropLast_cons_cons,
      List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change _ ≠ outer+8
    all_goals simp only [pushedData,copiedData]
    all_goals slots_guard safe)
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ start
  rintro callee ⟨machine, recorded⟩
  have cursor : callee = ⟨prologueCalled s, (history ++ prologueStates s) ++ [prologueCalled s]⟩ := by
    cases callee; simp_all [List.append_assoc]
  rw [cursor]
  have stack : (prologueCalled s).data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-56 := by
    simp only [prologueCalled, Instrumentation.calledState, copiedData, pushedData,
      UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  have entry : EntryFrame (prologueCalled s) (Image.PeerGet.entry+0x12).toUInt64 := by
    constructor
    · change ((s.regs.rsp-48)-8).toNat % 8 = 0
      exact aligned_sub _ 8 (aligned_sub _ 48 aligned (by decide)) (by decide)
    · rw [stack, prologue_called_memory]
      simpa [slot, savedWords] using saveMemory_read s 7 6 (by decide) (by decide)
  have calleeState : LookupCoverage.Context.At coverage preempt (prologueCalled s).data.dmem := by
    rw [prologue_called_memory]
    exact LookupCoverage.state_frame coverage preempt _ _ state _ (saveMemory_frame s 7 (by decide)) pushSeparate
  have restored := history_restore last
  have seen := observeHistory_splice (LookupObservation.edge rxSection)
    history.dropLast ⟨s, Image.PeerGet.entry⟩ (prologueStates s ++ [prologueCalled s])
  rw [restored, observed, prologue_observed] at seen
  change observeHistory (LookupObservation.edge rxSection)
    (history.dropLast ++ ⟨s, Image.PeerGet.entry⟩ :: (prologueStates s ++ [prologueCalled s])) =
      .ok (events ++ []) at seen
  have calleeObserved : observeHistory (LookupObservation.edge rxSection)
      ((history ++ prologueStates s) ++ [prologueCalled s]) = .ok events := by
    rw [List.append_assoc, ← restored, List.append_assoc]
    simpa only [List.singleton_append, List.append_nil] using seen
  have call := LookupCoverage.First.observed_callback fetch (.ofNat 0xffffffff810f31f0) .pc contract
    coverage preempt (prologueCalled s) (Image.PeerGet.entry+0x12).toUInt64 outer (by
      change (s.regs.rsp-48)-8≠outer+8
      slots_guard safe) rfl entry calleeState (.inl ⟨rfl, phase⟩)
    (by simpa only [stack] using returnSeparate) metadataSeparate preemptSeparate rxSection
    (history ++ prologueStates s) events calleeObserved
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ call
  rintro t ⟨returned, state, frame, seen, last, serviceTail, serviceRecorded, serviceLast, noCuts, noReentry⟩
  have sp : t.machine.data.regs.rsp = s.regs.rsp-48 := by
    rw [returned.2.1]
    change ((s.regs.rsp-48)-8)+8 = s.regs.rsp-48
    apply UInt64.toBitVec_inj.mp
    exact BitVec.sub_add_cancel _ _
  have bodySlot : t.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-56 := by
    simp only [sp, UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  have memory : EqualOutside (LookupCoverage.Context.writes coverage) (saveMemory s 7) t.machine.data.dmem := by
    simpa only [prologue_called_memory] using frame
  have ready : LookupCoverage.CallsReady coverage preempt t.machine.data := {
    state := state
    phase := phase
    aligned := by
      rw [sp]
      exact aligned_sub _ 48 aligned (by decide)
    mapped := by
      rw [bodySlot]
      have read := memory.loadInt (s.regs.rsp.toBitVec-56) 8 (by
        intro byte bound written
        exact returnSeparate _ written ⟨byte, bound, rfl⟩)
      rw [← read]
      simpa [slot] using congrArg Option.isSome (saveMemory_read s 7 6 (by decide) (by decide))
    pushSeparate := by
      intro address kept inside
      rw [bodySlot] at inside
      obtain ⟨byte, bound, eq⟩ := inside
      exact pushSeparate address kept ⟨byte, by omega, eq⟩
    returnSeparate := by simpa only [bodySlot, LookupCoverage.Context.Separated] using returnSeparate
    metadataSeparate := metadataSeparate
    preemptSeparate := preemptSeparate }
  have prologueStable : PeerCountPhase.StableExtension history
      ((history ++ prologueStates s) ++ [prologueCalled s]) := by
    rw [← restored, List.append_assoc, List.append_assoc, List.singleton_append]
    apply PeerCountPhase.StableExtension.of_ordinary
    intro q member
    simp only [prologueStates, List.cons_append, List.nil_append,
      List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      constructor <;> simp [Image.PeerGet.entry, Image.PeerGet.entry]
  have serviceStable := PeerCountPhase.StableExtension.service
    (history ++ prologueStates s) (prologueCalled s) serviceTail noReentry
  have stable : PeerCountPhase.StableExtension history t.history := by
    rw [serviceRecorded]
    exact prologueStable.trans serviceStable
  refine ⟨returned.1, sp, returned.2.2.1, ready, memory, seen, last, stable,
    prologueStates s ++ prologueCalled s :: serviceTail, ?_, ?_⟩
  · simpa only [List.append_assoc] using serviceRecorded
  · intro q member cut
    rcases List.mem_append.mp member with saves | service
    · have framed := prologue_frames s q (List.mem_append.mpr (.inl saves))
      exact fun address outside => framed address (fun h => outside (.inl h))
    · have serviceRestored := history_restore serviceLast
      rw [← serviceRestored] at service
      rcases List.mem_append.mp service with interior | final
      · exact False.elim (noCuts q interior cut)
      · have eq := List.mem_singleton.mp final
        rw [eq]
        exact (saveMemory_frame s 7 (by decide)).trans memory

#print axioms prologue_frames
#print axioms start_history
end Binary.PeerGet.First
