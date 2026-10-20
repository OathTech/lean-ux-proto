import LookupOuterSaved
import LookupResultPrepared

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

theorem outer_live (c : Config) (s : MachineData) (a : Address)
    (inside : InRange (s.regs.rsp.toBitVec-40) 48 a) : LookupLiveStack c ⟨s, Image.Lookup.entry⟩ a := by
  have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
  exact backwards_range s.regs.rsp.toBitVec 40 (8*LookupStackWords c) 8 (by omega) a inside

theorem outer_callback_apart (s : MachineData) (a : Address)
    (inside : InRange (s.regs.rsp.toBitVec-40) 48 a) : ¬InRange (s.regs.rsp.toBitVec-48) 8 a := by
  have base : s.regs.rsp.toBitVec-40 = (s.regs.rsp.toBitVec-48)+8 := by
    rw [show (48 : BitVec 64) = 40+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [base] at inside
  simpa only [BitVec.add_zero] using InRange.offset_disjoint (s.regs.rsp.toBitVec-48) 8 48 0 8 (by decide) (by decide) (.inr (by decide)) a inside

theorem outer_deep_apart (s : MachineData) (a : Address)
    (inside : InRange (s.regs.rsp.toBitVec-40) 48 a) : ¬InRange (s.regs.rsp.toBitVec-104) 56 a := by
  have base : s.regs.rsp.toBitVec-40 = (s.regs.rsp.toBitVec-104)+64 := by
    rw [show (104 : BitVec 64) = 40+64 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [base] at inside
  simpa only [BitVec.add_zero] using InRange.offset_disjoint (s.regs.rsp.toBitVec-104) 64 48 0 56 (by decide) (by decide) (.inr (by decide)) a inside

/-- Owner and count bytes already belong to the read projection. Its entry
    separation protects saved words; the original return word is explicit. -/
theorem outer_data_apart (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (a : Address) (inside : InRange (s.regs.rsp.toBitVec-40) 48 a) : ¬LookupDataWrites c v a := by
  intro written
  obtain ⟨i, hi, eq⟩ := inside
  by_cases low : i < 40
  · have stack : LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a := by
      have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
      exact backwards_range s.regs.rsp.toBitVec 40 (8*LookupStackWords c) 0 (by omega) a ⟨i, low, eq⟩
    have read : Reads c v a := by
      rcases written with owner | ⟨_, count⟩
      · exact .inr (.inr (.inl owner))
      · exact .inr (.inr (.inr count))
    exact entry.readsScratch a read (.inl stack)
  · apply entry.dataReturn a _ written
    refine ⟨i-40, by omega, ?_⟩
    have number : i = 40+(i-40) := by omega
    rw [eq]
    calc
      _ = s.regs.rsp.toBitVec-40+(.ofNat 64 40+.ofNat 64 (i-40)) := by
        rw [← BitVec.ofNat_add, ← number]
      _ = s.regs.rsp.toBitVec+.ofNat 64 (i-40) := by
        change s.regs.rsp.toBitVec-40+(40+.ofNat 64 (i-40)) = s.regs.rsp.toBitVec+.ofNat 64 (i-40)
        rw [← BitVec.add_assoc, BitVec.sub_add_cancel]


/-- The bucket theorem preserves the original five saved registers and
    return word, including through any number of collision callbacks. -/
theorem outer_saved_bucket (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket : Executed) (after : AfterBucket c world s coverage preempt v bucket) :
    OuterSaved s bucket.machine.data := by
  obtain ⟨head, atHead, _, _, frame, _⟩ := after
  have baseMemory : (bucketExitBase head.machine.data c.query (cells c v)).dmem = head.machine.data.dmem := by
    unfold bucketExitBase; split <;> rfl
  have baseStack : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp = head.machine.data.regs.rsp := by
    unfold bucketExitBase; split <;> simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64]
  have baseSaved : (bucketExitBase head.machine.data c.query (cells c v)).regs.r15 = head.machine.data.regs.r15 := by
    unfold bucketExitBase; split <;> simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64]
  refine ⟨frame.stack.trans (baseStack.trans atHead.stack), frame.saved.trans (baseSaved.trans atHead.saved), ?_⟩
  intro a inside
  have headEq := atHead.memory a (by
    rintro (covered | bh)
    · exact entry.coverageStack a covered (outer_live c s a inside)
    · exact entry.bhStack a bh (outer_live c s a inside))
  have bucketEq := frame.memory a (by
    rintro (stack | covered)
    · apply outer_callback_apart s a inside
      have loc : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [baseStack, atHead.stack, UInt64.toBitVec_sub, BitVec.sub_sub]; rfl
      simpa only [loc] using stack
    · exact entry.coverageStack a covered (outer_live c s a inside))
  rw [baseMemory] at bucketEq
  exact headEq.trans bucketEq

/-- Selected helper execution preserves the outer stack despite using its
    own seven scratch words and conditionally incrementing the peer count. -/
theorem outer_saved_helper (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner)
    (afterBucket : AfterBucket c world s coverage preempt v bucket)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current) :
    OuterSaved s current.machine.data := by
  have bucketSaved := outer_saved_bucket c coverage preempt ra s world v entry bucket afterBucket
  obtain ⟨callback, _, cbPC, cbStack, cbOwner, traced, machine, _⟩ := before
  obtain ⟨ret, _, _, _, _, _, _, _, frame, _⟩ := after
  have callbackSaved := bucketSaved.frame traced.frame.stack traced.frame.saved _ traced.frame.memory (by
    intro a inside written
    rcases written with stack | covered
    · apply outer_callback_apart s a inside
      simpa only [bucketSaved.stack, UInt64.toBitVec_sub, BitVec.sub_sub, show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
    · exact entry.coverageStack a covered (outer_live c s a inside))
  have helperSP : helper.machine.data.regs.rsp = s.regs.rsp-48 := by
    rw [machine]
    simp only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64, cbStack]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [ret.2.1, helperSP]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
    change s.regs.rsp.toBitVec-48+8 = s.regs.rsp.toBitVec-40
    rw [show (48 : BitVec 64) = 40+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  · rw [ret.2.2.2.2.2.2.2, machine]
    exact callbackSaved.saved
  · intro a inside
    have callEq : callback.machine.data.dmem.get? a = helper.machine.data.dmem.get? a := by
      rw [machine]
      apply storeInt_frame
      intro written
      apply outer_callback_apart s a inside
      simpa only [peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64, cbStack,
        UInt64.toBitVec_sub, BitVec.sub_sub, show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using written
    have helperEq := frame a (by
      rintro (data | stack | covered)
      · exact outer_data_apart c coverage preempt ra s world v entry a inside data
      · apply outer_deep_apart s a inside
        simpa only [helperSP, UInt64.toBitVec_sub, BitVec.sub_sub, show (48 : UInt64).toBitVec+56 = (104 : BitVec 64) from rfl] using stack
      · exact entry.coverageStack a covered (outer_live c s a inside))
    exact (callbackSaved.memory a inside).trans (callEq.trans helperEq)

#print axioms outer_live
#print axioms outer_callback_apart
#print axioms outer_deep_apart
#print axioms outer_data_apart
#print axioms outer_saved_bucket
#print axioms outer_saved_helper
end Binary.LookupRelation
