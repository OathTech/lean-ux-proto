import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixState
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontSource

/-! A routed front crosses at most one disposal checkpoint before its routed
receipt. The checkpoint keeps the same full accounted ledger, including
counted overflow and final release, at its native receipt snapshot. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier
open StagedAdmission.Front

theorem checkpoint_accounted (cut : Checkpoint entry history ledger snapshot)
    (canonical : entry.births = births entry.history)
    (before : Accounted entry.history entry.ledger debts locals entry.world)
    (material : PacketOrigins.snapshot snapshot = PacketOrigins.snapshot entry.world)
    (ownership : Ownership.view snapshot = Ownership.view entry.world) :
    Accounted history ledger debts locals snapshot := by
  have physical := CompleteFront.physical before.entry ownership
  exact ⟨⟨cut.core canonical before.entry.core material,
    StagedProvenance.checkpoint cut before.entry.justified,
    StagedProvenance.checkpoint_links cut before.entry.allocationLinks,
    checkpoint_no_selected cut before.entry.noSelected,physical.1,physical.2.1,physical.2.2⟩,
    CompleteFront.checkpoint cut before.entry.justified before.complete⟩

theorem normal_accounted (normal : Normal entry input r history ledger)
    (before : Accounted entry.history entry.ledger debts locals entry.world)
    (material : PacketOrigins.snapshot r.after = PacketOrigins.snapshot entry.world)
    (ownership : Ownership.view r.after = Ownership.view entry.world) :
    Accounted (history ++ [routedEvent input r]) ledger debts locals r.after := by
  have physical := CompleteFront.physical before.entry ownership
  exact ⟨⟨normal.core before.entry.core material,
    StagedProvenance.normal normal before.entry.justified,
    StagedProvenance.normal_links normal before.entry.allocationLinks,
    normal_no_selected normal before.entry.noSelected,physical.1,physical.2.1,physical.2.2⟩,
    CompleteFront.normal normal before.entry.justified before.complete⟩

theorem checkpoint_cuts {Safe : List Event → Prop} (cut : Checkpoint entry history ledger snapshot)
    (before : Safe entry.history) (after : Safe history) :
    ∃ suffix, history = entry.history ++ suffix ∧ Cuts Safe entry.history suffix := by
  cases cut with
  | initial => exact ⟨[],by simp,Cuts.nil before⟩
  | nonfinal => exact ⟨_,rfl,Cuts.singleton before after⟩
  | released => exact ⟨_,rfl,Cuts.singleton before after⟩
  | trimmed => exact ⟨_,rfl,Cuts.singleton before after⟩

private theorem stamped_head {Stamp : Event → Prop}
    (checked : ∃ added, (base ++ [event]) ++ tail = base ++ added ∧ ∀ e ∈ added, Stamp e) :
    Stamp event := by
  obtain ⟨added,equal,stamps⟩ := checked
  have same : event :: tail = added := List.append_cancel_left (by
    simpa only [List.append_assoc,List.singleton_append] using equal)
  exact stamps event (same ▸ List.mem_cons_self)

theorem material_checkpoint (cut : Checkpoint entry history ledger snapshot)
    (checked : Material.Checked entry.history entry.world (history ++ suffix)) :
    PacketOrigins.snapshot snapshot = PacketOrigins.snapshot entry.world := by
  cases cut with
  | initial => rfl
  | nonfinal => exact stamped_head checked
  | released => exact stamped_head checked
  | trimmed => exact stamped_head checked

theorem ownership_checkpoint (cut : Checkpoint entry history ledger snapshot)
    (checked : Ownership.Checked entry.history entry.world (history ++ suffix)) :
    Ownership.view snapshot = Ownership.view entry.world := by
  cases cut with
  | initial => rfl
  | nonfinal => exact stamped_head checked
  | released => exact stamped_head checked
  | trimmed => exact stamped_head checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Admission
