import RandomState

namespace Binary.RandomProvider

theorem snapshot_congr (blocks : List (Nat × Nat)) (before after : DataMem)
    (frame : ∀ span ∈ blocks, ∀ a, InRange (.ofNat 64 span.1) span.2 a →
      before.get? a=after.get? a) : snapshot blocks before=snapshot blocks after := by
  induction blocks with
  | nil => rfl
  | cons span rest ih =>
    have bytes : before.loadBytes (.ofNat 64 span.1) span.2=
        after.loadBytes (.ofNat 64 span.1) span.2 := by
      unfold Mem.loadBytes
      congr 1
      apply List.map_congr_left
      intro i member
      exact frame span (by simp) _ ⟨i,List.mem_range.mp member,rfl⟩
    simp only [snapshot,bytes,ih (fun item member => frame item (by simp [member]))]

/-- A frame on the declared physical allocations suffices for the entire
executable private-state check, including its pointer graph traversal. -/
theorem check_frame {c : Config} {before after : DataMem}
    (frame : ∀ a, PrivateBytes c a → before.get? a=after.get? a)
    (task : Nat) (active : Bool) : check c task active before=check c task active after := by
  have same := snapshot_congr c.blocks before after (fun span member a inside => frame a ⟨span,member,inside⟩)
  simp only [check,same]

#print axioms check_frame
end Binary.RandomProvider
