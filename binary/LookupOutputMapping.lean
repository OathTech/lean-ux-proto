import LookupHelperStack
import PeerStartHistory
import PeerScratch

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory

/-- Before entering the helper the output remains mapped. Saved-register
    and CALL stores preserve mapping; callback and BH writes are disjoint. -/
theorem output_mapped_at_helper (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket current : Executed) (afterBucket : AfterBucket c world s coverage preempt v bucket)
    (owner : IndexOwner) (before : BeforeHelper c coverage preempt s world v bucket owner current)
    (needed : LookupOutputNeeded v) :
    (current.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true := by
  obtain ⟨head, atHead, _, _, bucketFrame, _⟩ := afterBucket
  obtain ⟨callback, delta, _, _, _, traced, machine, _⟩ := before
  have baseMemory : (bucketExitBase head.machine.data c.query (cells c v)).dmem = head.machine.data.dmem := by
    unfold bucketExitBase
    split <;> rfl
  have baseStack : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp = head.machine.data.regs.rsp := by
    unfold bucketExitBase
    split <;> simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64]
  have bucketSP := bucketFrame.stack.trans (baseStack.trans atHead.stack)
  have protect (i : Nat) (hi : i < 8) := entry.outputProtected
    (s.regs.rcx.toBitVec + .ofNat 64 i) ⟨needed, i, hi, rfl⟩
  have headRead := atHead.memory.loadInt s.regs.rcx.toBitVec 8 (by
    intro i hi written
    rcases written with buffer | bh
    · exact protect i hi (.inr (.inr (.inr buffer)))
    · exact protect i hi (.inr (.inl (.inr (.inl bh)))))
  have bucketRead := bucketFrame.memory.loadInt s.regs.rcx.toBitVec 8 (by
    intro i hi written
    rcases written with stack | buffer
    · have stackBase : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp.toBitVec-8 =
          s.regs.rsp.toBitVec-48 := by
        rw [baseStack, atHead.stack, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      rw [stackBase] at stack
      obtain ⟨j, hj, eq⟩ := stack
      exact protect i hi (.inr (.inr (.inl ⟨j, by omega, eq⟩)))
    · exact protect i hi (.inr (.inr (.inr buffer))))
  have callbackRead := traced.frame.memory.loadInt s.regs.rcx.toBitVec 8 (by
    intro i hi written
    rcases written with stack | buffer
    · have stackBase : bucket.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [bucketSP, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      rw [stackBase] at stack
      obtain ⟨j, hj, eq⟩ := stack
      exact protect i hi (.inr (.inr (.inl ⟨j, by omega, eq⟩)))
    · exact protect i hi (.inr (.inr (.inr buffer))))
  have mapped := Lookup.saves_preserve_mapped s 6 s.regs.rcx.toBitVec (entry.outputMapped needed)
  rw [headRead] at mapped
  rw [baseMemory] at bucketRead
  rw [bucketRead, callbackRead] at mapped
  rw [machine]
  exact storeInt_defined _ _ _ _ _ _ mapped

/-- Bytewise preservation admits output spans partly or wholly inside dead
    helper scratch. No output/scratch separation is added to the entry. -/
theorem output_mapped_after_helper (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (helper final : MachineData) (needed : LookupOutputNeeded v)
    (mapped : (helper.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true)
    (scratch : PeerGet.ScratchMapped helper final.dmem)
    (frame : EqualOutside (fun a => LookupDataWrites c v a ∨ PeerGet.entryWrites helper ⟨coverage, preempt, v⟩ a)
      helper.dmem final.dmem) :
    (final.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true := by
  classical
  rw [loadInt_defined] at mapped ⊢
  intro i hi
  let a := s.regs.rcx.toBitVec + .ofNat 64 i
  by_cases inside : InRange (helper.regs.rsp.toBitVec-56) 56 a
  · exact scratch a inside
  · have protect := entry.outputProtected a ⟨needed, i, hi, rfl⟩
    have outside : ¬(LookupDataWrites c v a ∨ PeerGet.entryWrites helper ⟨coverage, preempt, v⟩ a) := by
      rintro ((owner | ⟨_, count⟩) | stack | buffer)
      · exact protect (.inl (.inr (.inr (.inl owner))))
      · exact protect (.inl (.inr (.inr (.inr count))))
      · exact inside stack
      · exact protect (.inr (.inr (.inr buffer)))
    rw [← frame a outside]
    exact mapped i hi

#print axioms output_mapped_at_helper
#print axioms output_mapped_after_helper
end Binary.LookupRelation
