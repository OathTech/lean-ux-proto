import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceCreationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

/-! The original guarded device creation retains the old ticket ledger.
An absent device has no pending ticket; its fresh replacement invents none. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDeviceCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal StackOwnership

theorem entry (before : CompleteCarrier.Accounted h ledger [] [] w)
    (allocated : AllocationInv old w)
    (run : (wgCreate.run w).run a = .ok ((result,v),b)) :
    CompleteCarrier.Accounted h ledger [] [] v := by
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨absent,fresh⟩
  · exact before.same_view (link_frame same)
  · have gone : w.dev = none := by simpa [linkView,linkStore,wgStoreView] using absent
    have settled := Retired.no_pending before.entry (RetiredFrames.absent_staged gone)
      (RetiredFrames.absent_cells gone)
    have bounds := (show Allocated (freshDeviceWorld w) from ⟨old,allocated.freshDevice⟩).bounded
    have replacement : CompleteCarrier.Accounted h ledger [] [] (freshDeviceWorld w) :=
      ⟨Retired.empty_replacement before.entry settled fresh_staged fresh_cells bounds fresh_coverage fresh_inventory,
        before.complete⟩
    exact replacement.same_view (link_frame (fresh.trans (freshDevice_linkView w).symm))

/-- Native creation preserves every old terminal and admits no staged packet. -/
theorem checked : CompleteProduct.StateChecked (liftWGPrefix wgCreate) := by
  apply CompleteAllocated.native CompleteProduct.Safe CompleteProduct.account_safe
  intro h ledger
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨old,allocated⟩ := before.2
  exact ⟨entry before.1 allocated run,old,wgCreate_allocation_endpoint allocated run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDeviceCreation
