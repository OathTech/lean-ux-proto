import LookupWriteFrame

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Reconstruct callback readiness at the restored outer SP. The mapped
    callback word is retained from the actual helper CALL/return, not assumed. -/
theorem ready_at_outer (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s t : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (stack : t.regs.rsp = s.regs.rsp-40)
    (state : LookupCoverage.Context.At ⟨coverage, preempt, v⟩ (512+preempt) t.dmem)
    (mapped : (t.dmem.loadInt (t.regs.rsp.toBitVec-8) 8).isSome = true) :
    LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) t := by
  refine ⟨state, .inr rfl, ?_, mapped, ?_, ?_, entry.coverageMetadata, entry.coveragePreempt⟩
  · rw [stack, UInt64.toNat_sub]
    simp only [show (40 : UInt64).toNat = 40 from rfl]
    have align := entry.frame.1
    change s.regs.rsp.toNat % 8 = 0 at align
    have bound := s.regs.rsp.toNat_lt_size
    omega
  · intro a service written
    exact entry.serviceStack a service (callback_stack_in c s t stack a written)
  · intro a covered inside
    have slot := callback_stack_in c s t stack a inside
    obtain ⟨i, hi, eq⟩ := slot
    exact entry.coverageStack a covered ⟨i, by omega, eq⟩

/-- The helper preserves its real CALL return word. It is reused as the
    lookup's next callback slot after the helper returns. -/
theorem helper_return_word_mapped (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current) :
    (current.machine.data.dmem.loadInt helper.machine.data.regs.rsp.toBitVec 8).isSome = true := by
  obtain ⟨callback, _, _, cbStack, _, _, machine, _, abi, _⟩ := before
  obtain ⟨_, _, _, _, _, _, _, _, frame, _⟩ := after
  have helperSP : helper.machine.data.regs.rsp = s.regs.rsp-48 := by
    rw [machine]
    simp only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64, cbStack]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  have read := frame.loadInt helper.machine.data.regs.rsp.toBitVec 8 (by
    intro i hi written
    have slot : InRange (helper.machine.data.regs.rsp.toBitVec) 8
        (helper.machine.data.regs.rsp.toBitVec+.ofNat 64 i) := ⟨i, hi, rfl⟩
    have stack : LookupStackWrites c ⟨s, Image.Lookup.entry⟩ (helper.machine.data.regs.rsp.toBitVec+.ofNat 64 i) := by
      apply callback_stack_in c s callback.machine.data cbStack
      simpa only [machine, peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg,
        Reg64s.set, Reg64s.set64, UInt64.toBitVec_sub, show (8 : UInt64).toBitVec = (8 : BitVec 64) from rfl] using slot
    rcases written with data | scratch | covered
    · have read : Reads c v (helper.machine.data.regs.rsp.toBitVec+.ofNat 64 i) := by
        rcases data with owner | ⟨_, count⟩
        · exact .inr (.inr (.inl owner))
        · exact .inr (.inr (.inr count))
      exact entry.readsScratch _ read (.inl stack)
    · have disjoint := InRange.offset_disjoint (helper.machine.data.regs.rsp.toBitVec-56) 56 8 0 56
        (by decide) (by decide) (.inr (by decide)) _ (by
          simpa only [show BitVec.ofNat 64 56 = (56 : BitVec 64) from rfl, BitVec.sub_add_cancel] using slot)
      apply disjoint
      simpa only [BitVec.add_zero] using scratch
    · obtain ⟨j, hj, eq⟩ := stack
      exact entry.coverageStack _ covered ⟨j, by omega, eq⟩)
  rw [← read, abi.2]
  rfl

#print axioms ready_at_outer
#print axioms helper_return_word_mapped
end Binary.LookupRelation
