import LookupResultReady

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Compose the executed bucket, callback, CALL and complete helper frames
    into one footprint relative to the original entry memory. -/
theorem helper_write_frame (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (bucketAt : AfterBucket c world s coverage preempt v bucket)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current) :
    EqualOutside (LookupWrites c coverage preempt s v) s.dmem current.machine.data.dmem := by
  have bucketSaved := outer_saved_bucket c coverage preempt ra s world v entry bucket bucketAt
  have bucketFrame := bucket_write_frame c coverage preempt ra s world v entry bucket bucketAt
  obtain ⟨callback, _, _, cbStack, _, traced, machine, _⟩ := before
  obtain ⟨_, _, _, _, _, _, _, _, frame, _⟩ := after
  have cbFrame := lookup_frame_callback c coverage preempt s bucket.machine.data callback.machine.data v
    bucketSaved.stack bucketFrame traced.frame.memory
  have helperSP : helper.machine.data.regs.rsp = s.regs.rsp-48 := by
    rw [machine]
    simp only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64, cbStack]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  intro a outside
  have callEq : callback.machine.data.dmem.get? a = helper.machine.data.dmem.get? a := by
    rw [machine]
    apply storeInt_frame
    intro written
    apply outside (.inl (callback_stack_in c s callback.machine.data cbStack a _))
    simpa only [peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64] using written
  have helperEq := frame a (by
    rintro (data | scratch | covered)
    · exact outside (.inr (.inr (.inr (.inl data))))
    · apply outside (.inl _)
      have words : LookupStackWords c = 13 := by simp [LookupStackWords, focused]
      unfold LookupStackWrites
      rw [words]
      obtain ⟨i, hi, eq⟩ := scratch
      refine ⟨i, by omega, ?_⟩
      simpa only [helperSP, UInt64.toBitVec_sub, BitVec.sub_sub,
        show (48 : UInt64).toBitVec+56 = BitVec.ofNat 64 (8*13) from rfl] using eq
    · exact outside (.inr (.inl covered)))
  exact (cbFrame a outside).trans (callEq.trans helperEq)

/-- All physical finish premises at the committed result come from Pre
    and the actual selected execution, including NULL and zero-count peers. -/
theorem selected_result_ready (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current final : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (bucketAt : AfterBucket c world s coverage preempt v bucket)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal setWorld : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current)
    (result : AfterResult c coverage preempt s world v owner current answer helperFinal setWorld final) :
    OuterSaved s final.machine.data ∧
    EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem ∧
    LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) final.machine.data ∧
    final.machine.data.regs.r13 = s.regs.rcx ∧
    final.machine.data.regs.rbx.toBitVec = ownerAddress c owner ∧
    final.machine.data.regs.rbp.toBitVec = OwnerWord.pointer c.peers answer ∧
    final.machine.pc = (if answer.isSome then Image.Lookup.entry+0xc5 else Image.Lookup.entry+0x71) := by
  have saved := outer_saved_helper c coverage preempt ra s world v entry bucket helper current owner bucketAt before answer helperFinal after
  have initialFrame := helper_write_frame c coverage preempt ra s world v entry bucket helper current owner focused bucketAt before answer helperFinal after
  have word := helper_return_word_mapped c coverage preempt ra s world v entry bucket helper current owner before answer helperFinal after
  obtain ⟨af, _, _, _, _, _, _, machine, _, _, state, _, frame, _⟩ := result
  obtain ⟨ret, _, _, _, _, value, alive, _⟩ := after
  obtain ⟨callback, _, _, cbStack, cbOwner, traced, helperMachine, _⟩ := before
  have sameStack : final.machine.data.regs.rsp = current.machine.data.regs.rsp := by
    rw [machine]; simp [resultExit, resultSaved, OwnerWord.stored, tested, MachineData.setReg, Reg64s.set, Reg64s.set64]
  have finalSaved := saved.frame sameStack (by
    rw [machine]; simp [resultExit, resultSaved, OwnerWord.stored, tested, MachineData.setReg, Reg64s.set, Reg64s.set64]) _ frame (by
      intro a inside written
      exact outer_data_apart c coverage preempt ra s world v entry a inside (.inl ⟨owner, focused, written⟩))
  have finalFrame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem final.machine.data.dmem := by
    intro a outside
    exact (initialFrame a outside).trans (frame a (fun h => outside (.inr (.inr (.inr (.inl (.inl ⟨owner, focused, h⟩)))))))
  refine ⟨finalSaved, finalFrame, ready_at_outer c coverage preempt ra s final.machine.data world v entry finalSaved.stack state ?_, ?_, ?_, ?_, ?_⟩
  · have loc : final.machine.data.regs.rsp.toBitVec-8 = helper.machine.data.regs.rsp.toBitVec := by
      rw [sameStack, ret.2.1, UInt64.toBitVec_add]
      change helper.machine.data.regs.rsp.toBitVec+8-8 = helper.machine.data.regs.rsp.toBitVec
      rw [BitVec.add_sub_cancel]
    rw [loc, machine]
    exact storeInt_defined _ _ _ _ _ _ word
  · obtain ⟨head, atHead, _, _, bucketFrame, _⟩ := bucketAt
    have baseOut : (bucketExitBase head.machine.data c.query (cells c v)).regs.r13 = head.machine.data.regs.r13 := by
      unfold bucketExitBase; split <;> simp [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64]
    have cbOut := traced.frame.output.trans (bucketFrame.output.trans (baseOut.trans atHead.output))
    rw [machine]
    change current.machine.data.regs.r13 = s.regs.rcx
    rw [ret.2.2.2.2.2.1, helperMachine]
    exact cbOut
  · rw [machine]
    change current.machine.data.regs.rbx.toBitVec = ownerAddress c owner
    rw [ret.2.2.1, helperMachine]
    exact cbOwner
  · rw [machine]
    simpa only [resultExit, resultSaved, OwnerWord.stored, tested, MachineData.setReg, Reg64s.set, Reg64s.set64,
      UInt64.toBitVec_ofBitVec] using value
  · rw [machine]
    change (if current.machine.data.regs.rax = 0 then Image.Lookup.entry+0x71 else Image.Lookup.entry+0xc5) = _
    by_cases zero : current.machine.data.regs.rax = 0
    · simp only [zero, ne_eq, not_true_eq_false, decide_false] at alive
      simp [zero, ← alive]
    · have someAnswer : answer.isSome = true := by simpa only [zero, ne_eq, not_false_eq_true, decide_true] using alive.symm
      simp [zero, someAnswer]

#print axioms helper_write_frame
#print axioms selected_result_ready
end Binary.LookupRelation
