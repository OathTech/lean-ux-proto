import Leanux.Proofs.WG.TransmitSecurity.StagedObligationLedger

/-! One fixed ledger keeps every admitted ticket and its first terminal
outcome. These structural laws do not establish native execution coverage. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins

theorem Step.same_keys (step : Step before after) : keys after = keys before := by
  induction step with
  | nil => rfl
  | cons ticket change tail ih =>
    change ticket :: keys _ = ticket :: keys _
    exact congrArg (List.cons ticket) ih

theorem Step.valid (step : Step before after) (valid : Valid births before) : Valid births after :=
  ⟨step.same_keys.trans valid.1,valid.2⟩

theorem unique_status (unique : (keys ledger).Nodup)
    (first : (ticket,left) ∈ ledger) (second : (ticket,right) ∈ ledger) : left = right := by
  induction ledger with
  | nil => cases first
  | cons head tail ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with equal | firstTail
    · cases equal
      rcases List.mem_cons.mp second with equal | secondTail
      · cases equal; rfl
      · exact (fresh (List.mem_map.mpr ⟨(ticket,right),secondTail,rfl⟩)).elim
    · rcases List.mem_cons.mp second with equal | secondTail
      · cases equal
        exact (fresh (List.mem_map.mpr ⟨(ticket,left),firstTail,rfl⟩)).elim
      · exact ih rest firstTail secondTail

theorem Step.terminal (step : Step before after)
    (settled : (ticket,.terminal outcome) ∈ before) : (ticket,.terminal outcome) ∈ after := by
  induction step with
  | nil => cases settled
  | cons id change tail ih =>
    rcases List.mem_cons.mp settled with equal | later
    · cases equal
      cases change with
      | retain => exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih later)

/-- Later storage cleanup or ownership bookkeeping cannot replace a first
terminal result or turn that ticket into another pending obligation. -/
theorem Step.terminal_unchanged (step : Step before after) (valid : Valid births before)
    (settled : (ticket,.terminal outcome) ∈ before) (later : (ticket,status) ∈ after) :
    status = .terminal outcome :=
  unique_status (by rw [(step.valid valid).1]; exact valid.2) later (step.terminal settled)

/-- Every original birth has exactly one status after a legal transition.
The native transition proof, not this algebra, determines that status. -/
theorem Step.total_partition (step : Step before after) (valid : Valid births before)
    (born : ticket ∈ births) : ∃ status, (ticket,status) ∈ after ∧
      ∀ other, (ticket,other) ∈ after → other = status := by
  have kept := step.valid valid
  have member : ticket ∈ keys after := kept.1.symm ▸ born
  obtain ⟨⟨id,status⟩,inside,same⟩ := List.mem_map.mp member
  dsimp only at same
  subst id
  exact ⟨status,inside,fun other found => unique_status (kept.1.symm ▸ kept.2) found inside⟩

theorem Step.append (left : Step before after) (right : Step otherBefore otherAfter) :
    Step (before ++ otherBefore) (after ++ otherAfter) := by
  induction left with
  | nil => exact right
  | cons ticket change tail ih => exact .cons ticket change ih

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
