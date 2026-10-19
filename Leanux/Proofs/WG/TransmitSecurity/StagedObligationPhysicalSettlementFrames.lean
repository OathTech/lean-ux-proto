import Leanux.Proofs.WG.TransmitSecurity.StagedObligationPhysicalFrames

/-! A counted staged disposal cannot affect allocated pending tickets or their
cleanup debts. Distinctness comes from the same ledger's unique statuses. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins

/-- Settling a different pending location preserves exactly the allocated
entries and all old terminal outcomes. No inequality of packet bytes is used. -/
theorem settle_allocated_frame (valid : Valid domain ledger)
    (chosen : ∀ ticket ∈ selected, ticket ∈ pendingAt location ledger)
    (different : ∀ position ordinal, Pending.allocated position ordinal ≠ location)
    (outcome : Terminal) : AllocatedFrame ledger (settle selected outcome ledger) := by
  refine ⟨?_,fun _ _ member => (settle_pending (valid.1.symm ▸ valid.2) chosen).terminal member⟩
  intro ticket position ordinal
  rw [←mem_pendingAt,←mem_pendingAt,
    settle_other_location (valid.1.symm ▸ valid.2) chosen (different position ordinal)]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
