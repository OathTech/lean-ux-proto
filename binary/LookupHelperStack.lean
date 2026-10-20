import LookupHelperFromBucket

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory

private theorem deep_slot (sp : BitVec 64) (i : Nat) (bound : i < 7) :
    sp - .ofNat 64 ((i+7)*8) = (sp-104) + .ofNat 64 (8*(6-i)) := by
  have n : 104 = (i+7)*8 + 8*(6-i) := by omega
  rw [show (104 : BitVec 64) = .ofNat 64 104 from rfl, n, BitVec.ofNat_add,
    ← BitVec.sub_sub, BitVec.sub_add_cancel]

/-- The seven helper scratch words are the entry's mapped words 6..12.
    Saved-register stores preserve mapping, and all intervening callback
    and BH writes are framed using the original entry allocation clauses. -/
theorem helper_stack_mapped (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket : Executed) (afterBucket : AfterBucket c world s coverage preempt v bucket)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (callback : Executed) (raw : List LookupObservation.Point)
    (traced : StableTrace bucket.machine.data ⟨coverage, preempt, v⟩ (512+preempt)
      c.rxSection bucket.history raw callback) (peer : Address) :
    ∀ n < 7,
      ((peerCalled callback.machine.data peer).data.dmem.loadInt
        ((peerCalled callback.machine.data peer).data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true := by
  obtain ⟨head, atHead, _, _, bucketFrame, _⟩ := afterBucket
  have baseMemory : (bucketExitBase head.machine.data c.query (cells c v)).dmem = head.machine.data.dmem := by
    unfold bucketExitBase
    split <;> rfl
  have baseStack : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp = head.machine.data.regs.rsp := by
    unfold bucketExitBase
    split <;> simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64]
  have bucketSP := bucketFrame.stack.trans (baseStack.trans atHead.stack)
  have callbackSP := traced.frame.stack.trans bucketSP
  have words : LookupStackWords c = 13 := by simp [LookupStackWords, focused]
  intro n hn
  let address := s.regs.rsp.toBitVec - .ofNat 64 ((n+7)*8)
  have inLive : ∀ a, InRange address 8 a → LookupLiveStack c ⟨s, Image.Lookup.entry⟩ a := by
    intro a inside
    unfold LookupLiveStack
    rw [words]
    apply backwards_range s.regs.rsp.toBitVec ((n+7)*8) 104 8 (by omega) a
    obtain ⟨j, hj, eq⟩ := inside
    exact ⟨j, by omega, eq⟩
  have slotSeparate : ∀ a, InRange address 8 a → ¬InRange (s.regs.rsp.toBitVec-48) 8 a := by
    intro a inside
    have oldSlot : s.regs.rsp.toBitVec-48 = (s.regs.rsp.toBitVec-104)+.ofNat 64 (8*7) := by
      rw [show (104 : BitVec 64) = 48+56 from rfl, ← BitVec.sub_sub]
      change s.regs.rsp.toBitVec-48 = (s.regs.rsp.toBitVec-48)-56+56
      rw [BitVec.sub_add_cancel]
    rw [oldSlot]
    exact stack_slots_disjoint (s.regs.rsp.toBitVec-104) (6-n) 7 (by omega) (by decide) (by omega) a
      (by simpa only [address, deep_slot _ n hn] using inside)
  have headRead := atHead.memory.loadInt address 8 (by
    intro j hj written
    have inside : InRange address 8 (address + .ofNat 64 j) := ⟨j, hj, rfl⟩
    rcases written with buffer | bh
    · exact entry.coverageStack _ buffer (inLive _ inside)
    · exact entry.bhStack _ bh (inLive _ inside))
  have bucketRead := bucketFrame.memory.loadInt address 8 (by
    intro j hj written
    have inside : InRange address 8 (address + .ofNat 64 j) := ⟨j, hj, rfl⟩
    rcases written with stack | buffer
    · have stackBase : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp.toBitVec-8 =
          s.regs.rsp.toBitVec-48 := by
        rw [baseStack, atHead.stack, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      exact slotSeparate _ inside (by simpa only [stackBase] using stack)
    · exact entry.coverageStack _ buffer (inLive _ inside))
  have callbackRead := traced.frame.memory.loadInt address 8 (by
    intro j hj written
    have inside : InRange address 8 (address + .ofNat 64 j) := ⟨j, hj, rfl⟩
    rcases written with stack | buffer
    · have stackBase : bucket.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [bucketSP, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      exact slotSeparate _ inside (by simpa only [stackBase] using stack)
    · exact entry.coverageStack _ buffer (inLive _ inside))
  have mapped := Lookup.saves_preserve_mapped s 6 address (by
    have h := entry.stackMapped (n+6) (by rw [words]; omega)
    simpa only [address, Nat.add_assoc] using h)
  rw [headRead] at mapped
  rw [baseMemory] at bucketRead
  rw [bucketRead, callbackRead] at mapped
  have stackAddr : (peerCalled callback.machine.data peer).data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8) = address := by
    simp only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg,
      Reg64s.set, Reg64s.set64, UInt64.toBitVec_sub, callbackSP]
    change (s.regs.rsp.toBitVec-40)-8-.ofNat 64 ((n+1)*8) = address
    rw [BitVec.sub_sub, BitVec.sub_sub]
    congr 1
    rw [← BitVec.add_assoc]
    change (40 : BitVec 64)+8+.ofNat 64 ((n+1)*8) = .ofNat 64 ((n+7)*8)
    rw [show (40 : BitVec 64)+8 = .ofNat 64 48 from rfl, ← BitVec.ofNat_add]
    congr 1
    omega
  rw [stackAddr]
  exact storeInt_defined _ _ _ _ _ _ mapped

#print axioms helper_stack_mapped
end Binary.LookupRelation
