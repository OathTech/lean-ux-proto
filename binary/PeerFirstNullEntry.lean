import PeerNullEntryHistory
import PeerFirstNull
import PeerFirstStart
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem null_entry_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (s : MachineData) (safe : StackSlots outer s.regs.rsp) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (null : s.regs.rdi = 0)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (state : LookupCoverage.Context.At coverage preempt s.dmem)
    (phase : preempt = coverage.entryPreempt ∨ preempt = 512+coverage.entryPreempt)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, LookupCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : LookupCoverage.Context.Separated coverage (LookupCoverage.Context.metadataBytes coverage))
    (preemptSeparate : LookupCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.PeerGet.entry⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = 0 ∧ LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (entryWrites s coverage) s.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ guard : MachineState, guard.pc = Image.PeerGet.entry+0xdd ∧
        EqualOutside (entryWrites s coverage) s.dmem guard.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull true guard,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have headerSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 8) := by
    intro address buffer inside
    obtain ⟨byte, bound, eq⟩ := inside
    exact coverageSeparate address buffer ⟨byte, by omega, eq⟩
  have start := start_history fetch agree contract s safe coverage preempt state phase entry.1 mapped
    pushSeparate headerSeparate metadataSeparate preemptSeparate rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ start
  rintro body ⟨pc, sp, bx, ready, memory, seen, last, startStable, startTail, startRecorded, startCuts⟩
  have bodyBase : body.machine.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-48 := by simp [sp]
  have callbackSlot : body.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-56 := by
    rw [bodyBase, BitVec.sub_sub]
    rfl
  have savedBase : s.regs.rsp.toBitVec-48 = (s.regs.rsp.toBitVec-56)+8 := by
    rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have savedSeparate : ∀ address, InRange (s.regs.rsp.toBitVec-48) 56 address →
      ¬(LookupCoverage.Context.writes coverage address ∨ scanWrites body.machine.data coverage address) := by
    intro address inside written
    rw [savedBase] at inside
    have outside : ¬LookupCoverage.Context.writes coverage address := fun inBuffer =>
      coverageSeparate address inBuffer (stack_tail_inside _ _ inside)
    rcases written with h | h | h
    · exact outside h
    · rw [callbackSlot] at h
      exact stack_tail_disjoint_header _ _ inside h
    · exact outside h
  have finish := null_suffix_history fetch agree contract ⟨s, Image.PeerGet.entry⟩ safe
    body.machine.data returnAddress entry sp (bx.trans null) coverage preempt ready
    (LookupCoverage.Context.writes coverage) memory savedSeparate rxSection body.history events seen
    (by rw [← pc]; exact last)
  have cursor : (⟨⟨body.machine.data, Image.PeerGet.entry+0x12⟩, body.history⟩ : Executed) = body := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ finish
  rintro final ⟨returned, result, state, suffixFrame, last, returning, af, seen, tail, recorded, cuts⟩
  have initialFrame : EqualOutside (entryWrites s coverage) s.dmem body.machine.data.dmem :=
    (saveMemory_frame s 7 (by decide)).trans memory
  have subset : ∀ address, scanWrites body.machine.data coverage address → entryWrites s coverage address := by
    intro address written
    rcases written with stack | buffer
    · rw [callbackSlot] at stack
      obtain ⟨byte, bound, eq⟩ := stack
      exact .inl ⟨byte, by omega, eq⟩
    · exact .inr buffer
  have transfer {after : Mem 64}
      (frame : EqualOutside (scanWrites body.machine.data coverage) body.machine.data.dmem after) :
      EqualOutside (entryWrites s coverage) s.dmem after := by
    intro address outside
    exact (initialFrame address outside).trans (frame address (fun written => outside (subset address written)))
  refine ⟨returned, result, state, transfer suffixFrame, last, startStable.returning returning,
    ⟨tested (.low .rbx .W64) body.machine.data af, Image.PeerGet.entry+0xdd⟩,
    rfl, initialFrame, seen, startTail ++ tail, ?_, ?_⟩
  · rw [recorded, startRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact startCuts q h cut
    · exact transfer (cuts q h cut)

#print axioms null_entry_history
end Binary.PeerGet.First
