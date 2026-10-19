import SourceAdapter
import PeerDeadEntry
import PeerLiveEntry
import MirrorPeer

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Both nonnull physical paths under acceptance of the actual mirror.
    The arithmetic bound is derived from acceptance, never a separate entry
    restriction. This is an endpoint theorem, not per-cut adequacy. -/
theorem accepted_nonnull_to_return (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch)
    (pid : Leanux.WG.PeerId) (w w' : Leanux.World) (answer : Option Leanux.WG.PeerId)
    (device : Leanux.WG.Device) (peer : Leanux.WG.Peer)
    (hasDevice : w.wg.dev = some device) (hasPeer : device.peers.get? pid = some peer)
    (accepted : (Source.peerGetMaybeZero (some pid)).run w = .ok (answer, w'))
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some (peer.refcount : Int))
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4))
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 64 a ∨ KcovBufferBytes coverage a)) :
    Eventually (instructionStep fetch)
      (fun final => Returned ⟨s, Image.PeerGet.entry⟩ final returnAddress ∧
        final.data.regs.rax = (if answer.isSome then s.regs.rdi else 0) ∧
        KcovState coverage preempt final.data.dmem ∧
        final.data.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 =
          some ((peer.refcount + if answer.isSome then 1 else 0 : Nat) : Int) ∧
        EqualOutside (fun a => (answer.isSome = true ∧ InRange (s.regs.rdi.toBitVec+0x420) 4 a) ∨
          InRange (s.regs.rsp.toBitVec-56) 56 a ∨ KcovBufferBytes coverage a)
          s.dmem final.data.dmem)
      ⟨s, Image.PeerGet.entry⟩ := by
  have bound := PeerMirror.accepted_peer_bound pid w w' answer device peer hasDevice hasPeer accepted
  have result := (PeerMirror.accepted_peer_result pid w w' answer device peer hasDevice hasPeer accepted).1
  by_cases zero : peer.refcount = 0
  · have answerNone : answer = none := by simpa only [zero, ite_true] using result
    have run := dead_entry_to_return fetch agree tracePc traceCmp s returnAddress entry nonnull
      (by simpa [zero] using field) coverage preempt state mapped pushSeparate coverageSeparate
      metadataSeparate preemptSeparate (by
        intro a inside written
        apply fieldSeparate a inside
        rcases written with h | h
        · obtain ⟨i, hi, eq⟩ := h
          exact .inl ⟨i, by omega, eq⟩
        · exact .inr h)
    apply eventually_weaken (instructionStep fetch) _ _ _ _ run
    rintro final ⟨ret, value, state, frame⟩
    refine ⟨ret, by simpa only [answerNone, Option.isSome_none, Bool.false_eq_true, ite_false] using value,
      state, ?_, ?_⟩
    · rw [← frame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
        intro byte hb written
        apply fieldSeparate _ ⟨byte, hb, rfl⟩
        rcases written with h | h
        · obtain ⟨i, hi, eq⟩ := h
          exact .inl ⟨i, by omega, eq⟩
        · exact .inr h)]
      simpa only [answerNone, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] using field
    · intro a outside
      exact frame a (fun h => outside (.inr h))
  · have answerSome : answer = some pid := by simpa only [ite_eq_right zero] using result
    let count := UInt32.ofNat peer.refcount
    have countNat : count.toNat = peer.refcount := by
      simp only [count]
      exact Nat.mod_eq_of_lt (by omega)
    have countNonzero : count ≠ 0 := by
      intro h
      have eq := congrArg UInt32.toNat h
      rw [countNat] at eq
      exact zero eq
    have run := live_entry_to_return fetch agree tracePc traceCmp traceByte s returnAddress entry nonnull
      count countNonzero (by simpa only [countNat] using bound)
      (by simpa [countNat] using field) coverage preempt state mapped pushSeparate coverageSeparate
      metadataSeparate preemptSeparate countSeparate fieldSeparate
    apply eventually_weaken (instructionStep fetch) _ _ _ _ run
    rintro final ⟨ret, value, state, finalCount, frame⟩
    refine ⟨ret, by simpa only [answerSome, Option.isSome_some, ite_true] using value,
      state, ?_, ?_⟩
    · have incrementNat : (count.toBitVec+1).toNat = peer.refcount+1 := by
        simp only [BitVec.toNat_add, UInt32.toNat_toBitVec, countNat, show (1 : BitVec 32).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      simpa only [answerSome, Option.isSome_some, ite_true, incrementNat] using finalCount
    · intro a outside
      apply frame a
      rintro (h | h)
      · exact outside (.inl ⟨by simp [answerSome], h⟩)
      · exact outside (.inr h)

#print axioms accepted_nonnull_to_return
end Binary.PeerGet
