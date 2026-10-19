import Leanux.Proofs.WG.TransmitSecurity.StagedObligationBirthHistory
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationPhysicalFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelectionCut
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeMaterialFrames

/-! One fixed ledger joins the exact staged queues, selected positions and both
directions of allocated-cell accounting. Its domain is the complete canonical
birth history. This carrier is initialized here; transport through the full
native Runner, source terminal evidence and stopped frontiers remain separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects CausalJournal AllocatedObligation
open HandshakeSecurity.StagedConservation

structure Core (history : List Event) (ledger : Ledger) (debts : List CleanupDebt)
    (w : WGWorld) : Prop where
  valid : Valid (births history) ledger
  queues : QueueInv history ledger w
  selected : SelectedRecorded history ledger
  physical : Physical history ledger debts w

theorem core_initial (net bare : Bool) : Core [] [] [] (Runner.initialWG net bare) := by
  refine ⟨⟨rfl,List.nodup_nil⟩,queue_initial net bare,?_,physical_initial net bare⟩
  intro _ _ member
  cases member

/-- The canonical journal domain gives one status for every actual admission.
This is the carrier's consequence; native source transport must establish the
carrier at the execution cut before this theorem is a campaign claim. -/
theorem Core.total_partition (core : Core history ledger debts w)
    (born : ticket ∈ births history) :
    ∃ status, (ticket,status) ∈ ledger ∧ ∀ other, (ticket,other) ∈ ledger → other = status :=
  (Step.refl ledger).total_partition core.valid born

theorem Core.quiet_views (before : Core history ledger debts w)
    (suffix : List Event) (quiet : ∀ event ∈ suffix, birthPackets event = [])
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) :
    Core (history ++ suffix) ledger debts v := by
  refine ⟨?_,before.queues.views_append suffix epoch queues,before.selected.append suffix,
    (before.physical.views epoch cells).append suffix⟩
  rw [births_quiet_suffix _ _ quiet]
  exact before.valid

/-- The actual take transports all components of the same canonical ledger.
Its selected location is fresh by the earlier receipt positions, and every
existing allocated cell or terminal cleanup debt remains backed. -/
theorem core_take (r : Take.Receipt) (native : r.Valid)
    (before : Core history ledger debts r.run.before) :
    ∃ after, TakeAccounted (births history) ledger history r after ∧
      Core (history ++ [.stagingTaken r]) after debts r.run.after := by
  obtain ⟨after,accounted⟩ := take_accounted r native before.valid before.queues before.selected
  have frame : AllocatedFrame ledger after := by
    cases result : r.run.value with
    | none =>
      have same := accounted.exactTransfer
      rw [result] at same
      rw [same]
      exact AllocatedFrame.refl _
    | some peer =>
      have transfer := accounted.exactTransfer
      rw [result] at transfer
      obtain ⟨generation,_,same,_,_⟩ := transfer
      rw [same]
      exact take_allocated_frame _ _ _ _
  have views := take_material_views r native
  refine ⟨after,accounted,?_,accounted.queues,accounted.selected,
    ((before.physical.ledger_frame frame).views views.1 views.2).append _⟩
  rw [births_quiet _ rfl]
  exact accounted.valid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
