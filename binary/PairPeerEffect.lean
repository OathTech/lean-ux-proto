import AllowedipsCallerExecution
import AllowedipsCallerPre
import PairCallSearch

namespace Binary.Pair.Trie
open TrustBase AllowedipsCaller CommonBitsCoverage
local instance : Labels := Image.linkedLabels

def peerWrites (caller : MachineData) (peer : BitVec 64) (coverage : Context) (a : BitVec 64) : Prop :=
  InRange (peer+0x420) 4 a ∨ Scratch caller a ∨ coverage.writes a

theorem callWord_scratch (caller : MachineData) {a : BitVec 64}
    (inside : InRange (caller.regs.rsp.toBitVec-8) 8 a) : Scratch caller a := by
  have base : caller.regs.rsp.toBitVec-8=caller.regs.rsp.toBitVec-64+56 := by
    change _=caller.regs.rsp.toBitVec-(8+56)+56
    rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
  rw [base] at inside
  exact range_shift_inside _ 56 8 64 (by decide) inside

/-- Endpoint summary of the executed peer helper, including its caller's
CALL and result guard. No diagnostic history escapes this segment. -/
theorem peer_effect (fetch : Int64 → Option Decoded)
    (lookupAgree : AllowedipsDecoderAgreement fetch) (agree : AnchoredDecoderAgreement fetch)
    (pc : AllowedipsTracePcContract fetch) (cmp4 : AllowedipsTraceConstCmp4Contract fetch)
    (cmp1 : AllowedipsTraceConstCmp1Contract fetch)
    (caller : MachineData) (peer : BitVec 64) (coverage : Context)
    (ready : Ready coverage caller) (nonnull : peer≠0)
    (nodePeer : caller.dmem.loadInt caller.regs.rbp.toBitVec 8 = some peer.toNat)
    (count : UInt32) (nonzero : count≠0) (bound : count.toNat+1<2^31)
    (field : caller.dmem.loadInt (peer+0x420) 4 = some count.toNat)
    (countStack : ∀ a, InRange (peer+0x420) 4 a → ¬Scratch caller a)
    (countServices : ∀ a, coverage.bytes a → ¬InRange (peer+0x420) 4 a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=AllowedipsImage.Lookup.entry+0x122 ∧ t.data.regs.rsp=caller.regs.rsp ∧
      t.data.regs.rax.toBitVec=peer ∧ coverage.At t.data.dmem ∧
      t.data.dmem.loadInt (peer+0x420) 4=some ((count.toNat+1 : Nat) : Int) ∧
      EqualOutside (peerWrites caller peer coverage) caller.dmem t.data.dmem ∧
      (t.data.dmem.loadInt (t.data.regs.rsp.toBitVec-8) 8).isSome=true)
      ⟨caller,AllowedipsImage.Lookup.entry+0x110⟩ := by
  have run := live_result fetch lookupAgree agree pc cmp4 cmp1 caller peer coverage ready nonnull
    nodePeer count nonzero bound field countStack countServices 0 [⟨caller,AllowedipsImage.Lookup.entry+0x110⟩]
  apply Sequential.forget run
  rintro final ⟨helper,guard,post,_,position,regs,memory,machine,_⟩
  have returned := post.1
  have result := post.2.2.1
  have active := post.2.2.2.1
  have changed := post.2.2.2.2.1
  have frame := post.2.2.2.2.2.1
  have stack : helper.machine.data.regs.rsp=caller.regs.rsp := by
    rw [returned.2.1,(pushed_shape caller peer).1,UInt64.sub_add_cancel]
  have answer : helper.machine.data.regs.rax.toBitVec=peer := by
    rw [result,(pushed_shape caller peer).1]
  have countEq : (count.toBitVec+1).toNat=count.toNat+1 := by
    simp only [BitVec.toNat_add,UInt32.toNat_toBitVec]
    change (count.toNat+1)%2^32=count.toNat+1
    exact Nat.mod_eq_of_lt (by omega)
  have changed' : helper.machine.data.dmem.loadInt (peer+0x420) 4=some ((count.toNat+1 : Nat) : Int) := by
    simpa only [(pushed_shape caller peer).1,UInt64.toBitVec_ofBitVec,countEq] using changed
  have initialFrame := peer_call_frame caller peer
  have total : EqualOutside (peerWrites caller peer coverage) caller.dmem helper.machine.data.dmem := by
    intro a outside
    apply (initialFrame a (fun inside => outside (.inr (.inl (callWord_scratch caller inside))))).trans
    apply frame a
    rintro (count | scratch | buffer)
    · apply outside (.inl ?_)
      simpa only [(pushed_shape caller peer).1,UInt64.toBitVec_ofBitVec] using count
    · rw [scratch_base] at scratch
      obtain ⟨i,hi,equal⟩ := scratch
      exact outside (.inr (.inl ⟨i,by omega,equal⟩))
    · exact outside (.inr (.inr buffer))
  have callMapped : (helper.machine.data.dmem.loadInt (caller.regs.rsp.toBitVec-8) 8).isSome=true := by
    have read := frame.loadInt (caller.regs.rsp.toBitVec-8) 8 (by
      intro i hi written
      have inside : InRange (caller.regs.rsp.toBitVec-8) 8
          (caller.regs.rsp.toBitVec-8+.ofNat 64 i) := ⟨i,hi,rfl⟩
      rcases written with count | scratch | buffer
      · apply countStack _ _ (callWord_scratch caller inside)
        simpa only [(pushed_shape caller peer).1,UInt64.toBitVec_ofBitVec] using count
      · have base : caller.regs.rsp.toBitVec-8=caller.regs.rsp.toBitVec-64+56 := by
          change _=caller.regs.rsp.toBitVec-(8+56)+56
          rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
        rw [scratch_base] at scratch
        rw [base] at inside
        exact InRange.offset_disjoint (caller.regs.rsp.toBitVec-64) 56 8 0 56
          (by decide) (by decide) (by decide) _ inside (by simpa only [base,BitVec.add_zero] using scratch)
      · exact ready.separate _ (.inr (.inr ⟨buffer.1,.inr buffer.2⟩)) (callWord_scratch caller inside))
    rw [←read]
    have entry := (ready.entry peer).1.2
    rw [(pushed_shape caller peer).1] at entry
    change (peerCalled caller peer).data.dmem.loadInt (caller.regs.rsp.toBitVec-8) 8=some _ at entry
    rw [entry]; rfl
  rw [machine]
  exact ⟨position,regs ▸ stack,by rw [regs]; exact answer,by rw [memory]; exact active,
    by rw [memory]; exact changed',by rw [memory]; exact total,by rw [regs,stack,memory]; exact callMapped⟩

#print axioms peer_effect
end Binary.Pair.Trie
