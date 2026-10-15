import LookupSelectedFrame
import CutFrames

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

private theorem entry_writes_subset (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (v : View) (a : Address)
    (written : Lookup.entryWrites s ⟨coverage, preempt, v⟩ a ∨ InRange preemptCountAddress 4 a) :
    LookupWrites c coverage preempt s v a := by
  rcases written with (stack | covered) | count
  · have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
    exact .inl (backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a stack)
  · exact .inr (.inl covered)
  · exact .inr (.inr (.inl count))

private theorem scan_writes_subset (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s base : MachineData) (v : View) (stack : base.regs.rsp = s.regs.rsp-40) (a : Address)
    (written : scanWrites base ⟨coverage, preempt, v⟩ a) : LookupWrites c coverage preempt s v a := by
  rcases written with slot | covered
  · exact .inl (callback_stack_in c s base stack a slot)
  · exact .inr (.inl covered)

/-- The loop invariant carries the original physical frame at every cut,
    including arbitrary collision prefixes and each stop outcome. -/
theorem bucket_cut_frames (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (world : World) (v : View)
    (bucket : Executed) (after : AfterBucket c world s coverage preempt v bucket) :
    CutFrames (LookupWrites c coverage preempt s v) s.dmem bucket.history := by
  obtain ⟨head, atHead, _, _, _, _, _, _, _, _, _, _, _, tail, recorded, frames⟩ := after
  have old := atHead.frames.mono (entry_writes_subset c coverage preempt s v)
  have endpoint : EqualOutside (LookupWrites c coverage preempt s v) s.dmem head.machine.data.dmem := by
    intro a outside
    have first := Lookup.saveMemory_frame s 6 (by decide) a (fun h => outside (entry_writes_subset c coverage preempt s v a (.inl (.inl h))))
    exact first.trans (atHead.memory a (by
      rintro (covered | count)
      · exact outside (.inr (.inl covered))
      · exact outside (.inr (.inr (.inl count)))))
  rw [recorded]
  exact old.append_after endpoint frames (scan_writes_subset c coverage preempt s head.machine.data v atHead.stack)

/-- The actual callback, CALL and every helper path carry the same original
    footprint. Dead helper scratch and zero-count entries are not excluded. -/
theorem helper_cut_frames (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (bucketAt : AfterBucket c world s coverage preempt v bucket)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current) :
    CutFrames (LookupWrites c coverage preempt s v) s.dmem current.history := by
  have saved := outer_saved_bucket c coverage preempt ra s world v entry bucket bucketAt
  have bucketFrame := bucket_write_frame c coverage preempt ra s world v entry bucket bucketAt
  have bucketCuts := bucket_cut_frames c coverage preempt s world v bucket bucketAt
  obtain ⟨callback, _, _, cbStack, _, traced, machine, recordedCall, _⟩ := before
  obtain ⟨callbackTail, callbackRecorded, callbackFrames⟩ := traced.extension
  have cbFrame := lookup_frame_callback c coverage preempt s bucket.machine.data callback.machine.data v saved.stack bucketFrame traced.frame.memory
  have cbCuts : CutFrames (LookupWrites c coverage preempt s v) s.dmem callback.history := by
    rw [callbackRecorded]
    exact bucketCuts.append_after bucketFrame
      (fun q member cut => (callbackFrames q member cut).memory)
      (scan_writes_subset c coverage preempt s bucket.machine.data v saved.stack)
  have callFrame : EqualOutside (scanWrites callback.machine.data ⟨coverage, preempt, v⟩)
      callback.machine.data.dmem helper.machine.data.dmem := by
    rw [machine]
    intro a outside
    exact storeInt_frame _ _ _ _ a (fun written => outside (.inl written))
  have callCuts : CutFrames (scanWrites callback.machine.data ⟨coverage, preempt, v⟩)
      callback.machine.data.dmem
      [⟨peerArgument callback.machine.data (OwnerWord.pointer c.peers c.focus.peer), Image.Lookup.entry+0xb5⟩, helper.machine] := by
    intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · intro _ _; rfl
    · exact callFrame
  have helperCuts : CutFrames (LookupWrites c coverage preempt s v) s.dmem helper.history := by
    rw [recordedCall]
    exact cbCuts.append_after cbFrame callCuts (scan_writes_subset c coverage preempt s callback.machine.data v cbStack)
  have helperFrame := lookup_frame_callback c coverage preempt s callback.machine.data helper.machine.data v cbStack cbFrame callFrame
  have helperSP : helper.machine.data.regs.rsp = s.regs.rsp-48 := by
    rw [machine]
    simp only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64, cbStack]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_sub, BitVec.sub_sub]
    rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, tail, recorded, frames⟩ := after
  rw [recorded]
  apply helperCuts.append_after helperFrame frames
  intro a written
  rcases written with data | scratch | covered
  · exact .inr (.inr (.inr (.inl data)))
  · apply Or.inl
    have words : LookupStackWords c = 13 := by simp [LookupStackWords, focused]
    unfold LookupStackWrites
    rw [words]
    obtain ⟨i, hi, eq⟩ := scratch
    refine ⟨i, by omega, ?_⟩
    simpa only [helperSP, UInt64.toBitVec_sub, BitVec.sub_sub,
      show (48 : UInt64).toBitVec+56 = BitVec.ofNat 64 (8*13) from rfl] using eq
  · exact .inr (.inl covered)

/-- The owner store, saved return value, test and branch retain frames at
    all four actual successor states, including the NULL-store branch. -/
theorem result_cut_frames (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current final : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (bucketAt : AfterBucket c world s coverage preempt v bucket)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal setWorld : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current)
    (result : AfterResult c coverage preempt s world v owner current answer helperFinal setWorld final) :
    CutFrames (LookupWrites c coverage preempt s v) s.dmem final.history := by
  have old := helper_cut_frames c coverage preempt ra s world v entry bucket helper current owner focused bucketAt before answer helperFinal after
  have endpoint := helper_write_frame c coverage preempt ra s world v entry bucket helper current owner focused bucketAt before answer helperFinal after
  obtain ⟨callback, _, _, _, cbOwner, _, machine, _⟩ := before
  obtain ⟨ret, _⟩ := after
  have location : current.machine.data.regs.rbx.toBitVec = ownerAddress c owner := by
    rw [ret.2.2.1, machine]
    exact cbOwner
  obtain ⟨af, _, _, _, _, _, _, _, recorded, _⟩ := result
  rw [recorded]
  apply old.append_after endpoint (localWrites := InRange (ownerAddress c owner) 8)
  · intro q member _
    rw [resultStates_memory _ _ _ member]
    simpa only [location] using OwnerWord.stored_frame current.machine.data
  · intro a written
    exact .inr (.inr (.inr (.inl (.inl ⟨owner, focused, written⟩))))

#print axioms bucket_cut_frames
#print axioms helper_cut_frames
#print axioms result_cut_frames
end Binary.LookupRelation
