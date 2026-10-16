import SequentialExecution
import PeerLiveEntryHistory
import PeerDeadEntryHistory
import PeerNullEntryHistory
import MirrorPeer

namespace Binary.Sequential
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- Endpoint-only peer-get composition, with the original conditional
coverage domain. The arithmetic bound follows from mirror acceptance.
No intermediate source World or pending-count relation is supplied. -/
theorem peer_nonnull (world : World) (device : Device) (pid : PeerId) (peer : Peer)
    (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch) (traceByte : TraceConstCmp1Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (answer : Option PeerId) (worldFinal : World)
    (accepted : (peerGetMaybeZero (some pid)).run world = .ok (answer, worldFinal))
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some (peer.refcount : Int))
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
    (countSeparate : peer.refcount ≠ 0 → ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 64 a ∨ LookupCoverage.Context.writes coverage a))
    (comparison : coverage.CompareAllowed preempt)
    (hasDevice : world.k.wg = some device) (hasPeer : device.peers.get? pid = some peer) :
    Eventually (instructionStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final returnAddress ∧
      (answer.isSome = true → PeerGet.ScratchMapped s final.data.dmem) ∧
      final.data.regs.rax = (if answer.isSome then s.regs.rdi else 0) ∧
      LookupCoverage.Context.At coverage preempt final.data.dmem ∧
      final.data.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 =
        some (((if peer.refcount = 0 then 0 else peer.refcount+1) : Nat) : Int) ∧
      EqualOutside (fun a => (peer.refcount ≠ 0 ∧ InRange (s.regs.rdi.toBitVec+0x420) 4 a) ∨
        PeerGet.entryWrites s coverage a) s.dmem final.data.dmem)
      ⟨s, Image.PeerGet.entry⟩ := by
  have bound := PeerMirror.accepted_peer_bound pid world worldFinal answer device peer hasDevice hasPeer accepted
  have result := (PeerMirror.accepted_peer_result pid world worldFinal answer device peer hasDevice hasPeer accepted).1
  by_cases zero : peer.refcount = 0
  · have run := PeerGet.dead_entry_history fetch agree contract traceCmp s returnAddress entry nonnull
      (by simpa only [zero, Int.natCast_zero] using field) coverage preempt state phase mapped pushSeparate
      coverageSeparate metadataSeparate preemptSeparate (by
        intro a inside written
        apply fieldSeparate a inside
        rcases written with stack | buffer
        · obtain ⟨i, hi, eq⟩ := stack
          exact .inl ⟨i, by omega, eq⟩
        · exact .inr buffer)
      comparison 0 [⟨s, Image.PeerGet.entry⟩] [] rfl rfl
    apply forget run
    rintro final ⟨ret, value, ready, frame, _⟩
    refine ⟨ret, ?_, ?_, ready, ?_, ?_⟩
    · simp [result, zero]
    · simpa only [result, zero, ite_true, Option.isSome_none, Bool.false_eq_true, ite_false] using value
    · rw [← frame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
        intro i hi written
        apply fieldSeparate _ ⟨i, hi, rfl⟩
        rcases written with stack | buffer
        · obtain ⟨j, hj, eq⟩ := stack
          exact .inl ⟨j, by omega, eq⟩
        · exact .inr buffer)]
      simpa [zero] using field
    · intro a outside
      exact frame a (fun written => outside (.inr written))
  · let count := UInt32.ofNat peer.refcount
    have countNat : count.toNat = peer.refcount := by
      simp only [count, UInt32.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have countNonzero : count ≠ 0 := by
      intro equal
      have h := congrArg UInt32.toNat equal
      rw [countNat] at h
      exact zero h
    have run := PeerGet.live_entry_history fetch agree contract traceCmp traceByte s returnAddress entry nonnull
      count countNonzero (by simpa only [countNat] using bound)
      (by
        change s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some (count.toNat : Int)
        simpa only [countNat] using field) coverage preempt state phase mapped pushSeparate
      coverageSeparate metadataSeparate preemptSeparate (countSeparate zero) fieldSeparate comparison
      0 [⟨s, Image.PeerGet.entry⟩] [] rfl rfl
    apply forget run
    rintro final ⟨ret, mapped, value, ready, finalCount, frame, _⟩
    refine ⟨ret, fun _ => mapped, ?_, ready, ?_, ?_⟩
    · simpa only [result, ite_eq_right zero, Option.isSome_some, ite_true] using value
    · simpa only [ite_eq_right zero, BitVec.toNat_add, UInt32.toNat_toBitVec, countNat,
        show (1 : BitVec 32).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (show peer.refcount+1 < 2^32 by omega)] using finalCount
    · intro a outside
      apply frame a
      rintro (count | scratch)
      · exact outside (.inl ⟨zero, count⟩)
      · exact outside (.inr scratch)

#print axioms peer_nonnull
end Binary.Sequential
