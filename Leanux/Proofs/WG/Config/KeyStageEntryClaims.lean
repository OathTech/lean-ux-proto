import Leanux.Proofs.WG.Config.KeyStageEntrySource
import Leanux.Proofs.WG.Config.KeyStageClaims

/-! All completed private-key-stage effects from the account at the actual request
entry. Later Stops retain prior receipts; a stopped stage emits no completion. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage

open Leanux Leanux.WG Queues Queues.RxCredits
open Leanux.Proofs.WG.Config.OwnerConfiguration RequestOrder

theorem matches_funded (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (same : Matches attrs initial result) (pre : ProjectedEntry cs loans initial) :
    FundedEntries cs loans result.receipts := by
  obtain ⟨g,a,rfl,rfl⟩ := same
  exact inspection_funded cs loans attrs g a ((entry_snapshot cs loans g a).mp pre)

theorem certificate_initial_effects (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result) (pre : ProjectedEntry cs loans initial) :
    RequestEffects cs loans attrs result := by
  have entries := matches_funded cs loans attrs initial result certificate.1.1 pre
  intro r member kind
  have beforeEntry := entries r member kind
  obtain ⟨before,device,_⟩ := beforeEntry.2
  obtain ⟨code,afterEntry,after,afterDevice,effect⟩ :=
    certificate_effect cs loans attrs initial result certificate r member kind before beforeEntry device
  exact ⟨beforeEntry,code,afterEntry,before,after,device,afterDevice,effect⟩

theorem original_request_effects (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (ProjectedEntry cs loans)
      (fun initial outcome=>∃ result : Inspection,
        result.outcome=outcome ∧ Certificate attrs initial result ∧ RequestEffects cs loans attrs result) := by
  intro g a pre
  have certificate := inspection_certificate attrs g a
  exact ⟨inspection attrs g a,inspection_outcome attrs g a,certificate,
    certificate_initial_effects cs loans attrs _ _ certificate pre⟩

end Leanux.Proofs.WG.Config.KeyStage
