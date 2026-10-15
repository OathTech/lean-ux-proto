import LookupCommonFinish

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Union of actual lookup/helper stores, including their disposable stack.
    Framing this footprint adds no relation clauses for untouched state. -/
def LookupWrites (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (v : View) (a : Address) : Prop :=
  LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a ∨ LookupCoverageWrites coverage preempt v a ∨
  InRange preemptCountAddress 4 a ∨ LookupDataWrites c v a ∨ LookupOutputWrites v ⟨s, Image.Lookup.entry⟩ a

theorem bucket_write_frame (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (bucket : Executed) (after : AfterBucket c world s coverage preempt v bucket) :
    EqualOutside (LookupWrites c coverage preempt s v) s.dmem bucket.machine.data.dmem := by
  obtain ⟨head, atHead, _, _, frame, _⟩ := after
  have baseMemory : (bucketExitBase head.machine.data c.query (cells c v)).dmem = head.machine.data.dmem := by
    unfold bucketExitBase; split <;> rfl
  have baseStack : (bucketExitBase head.machine.data c.query (cells c v)).regs.rsp = s.regs.rsp-40 := by
    unfold bucketExitBase; split <;> simpa [kindBase, MachineData.setReg, Reg64s.set, Reg64s.set64] using atHead.stack
  intro a outside
  have pushed := Lookup.saveMemory_frame s 6 (by decide) a (by
    intro inside
    have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
    exact outside (.inl (backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a inside)))
  have middle := atHead.memory a (by
    rintro (covered | count)
    · exact outside (.inr (.inl covered))
    · exact outside (.inr (.inr (.inl count))))
  have ending := frame.memory a (by
    rintro (stack | covered)
    · exact outside (.inl (callback_stack_in c s _ baseStack a stack))
    · exact outside (.inr (.inl covered)))
  rw [baseMemory] at ending
  exact pushed.trans (middle.trans ending)

/-- The entry's conditional no-pending-work word survives every store in
    the lookup footprint; the fixed preempt word is a distinct allocation. -/
theorem pending_from_frame (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (s t : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world v)
    (frame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem t.dmem) :
    LookupPendingRead preempt → t.dmem.loadInt softirqPendingAddress 2 = some 0 := by
  intro need
  have read := frame.loadInt softirqPendingAddress 2 (by
    intro i hi written
    rcases written with stack | covered | count | data | output
    · exact entry.pendingFrame need _ ⟨i, hi, rfl⟩ (.inl stack)
    · exact entry.pendingFrame need _ ⟨i, hi, rfl⟩ (.inr (.inl covered))
    · obtain ⟨j, hj, eq⟩ := count
      have same := congrArg BitVec.toNat eq
      simp only [softirqPendingAddress, preemptCountAddress, BitVec.toNat_add,
        BitVec.toNat_ofNat] at same
      omega
    · exact entry.pendingFrame need _ ⟨i, hi, rfl⟩ (.inr (.inr (.inl data)))
    · exact entry.pendingFrame need _ ⟨i, hi, rfl⟩ (.inr (.inr (.inr output))))
  rw [← read]
  exact entry.bhPending need

/-- Append a real callback footprint at the fixed outer stack position. -/
theorem lookup_frame_callback (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s before after : MachineData) (v : View)
    (stack : before.regs.rsp = s.regs.rsp-40)
    (initial : EqualOutside (LookupWrites c coverage preempt s v) s.dmem before.dmem)
    (frame : EqualOutside (scanWrites before ⟨coverage, preempt, v⟩) before.dmem after.dmem) :
    EqualOutside (LookupWrites c coverage preempt s v) s.dmem after.dmem := by
  intro a outside
  exact (initial a outside).trans (frame a (by
    rintro (slot | covered)
    · exact outside (.inl (callback_stack_in c s before stack a slot))
    · exact outside (.inr (.inl covered))))

#print axioms bucket_write_frame
#print axioms pending_from_frame
#print axioms lookup_frame_callback
end Binary.LookupRelation
