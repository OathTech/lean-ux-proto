import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseAdmissionNeutral

/-! The enriched acceptance consumers project to the exact old focused
HandshakeWorker observers without constraining the incoming journal. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

/-- The original initiation admission event is retained at its pre-write cut;
nested release events alone disappear under the old-journal projection,
including when a later continuation stops. -/
theorem initiation_focused_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none)
    (record : HandshakeAdmission → E) (target : HandshakeCausal.Event → F)
    (targetDecode : F → Option HandshakeCausal.Event)
    (same : ∀ e, ρ (record e) = some (target (.admission e))) (mac : HandshakeMac) :
    StateProjectsPrefix ρ id (admitInitiationWith (observedOps release releaseDecode) record mac)
      (HandshakeWorker.old target targetDecode (HandshakeCausal.initiation mac)) := by
  rw [←initiation_focused]
  exact initiation_matching ρ (observedOps_projects release releaseDecode ρ quiet)
    record (target ∘ HandshakeCausal.Event.admission) same mac

/-- Response rejection repayments are observed in place, while the exact old
response admission observer and every stopped prefix remain unchanged. -/
theorem response_focused_old (release : StagedDisposal.Event → E)
    (releaseDecode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none)
    (record : HandshakeAdmission → E) (target : HandshakeCausal.Event → F)
    (targetDecode : F → Option HandshakeCausal.Event)
    (same : ∀ e, ρ (record e) = some (target (.admission e))) (mac : HandshakeMac) :
    StateProjectsPrefix ρ id (admitResponseWith (observedOps release releaseDecode) record mac)
      (HandshakeWorker.old target targetDecode (HandshakeCausal.response mac)) := by
  rw [←response_focused]
  exact response_matching ρ (observedOps_projects release releaseDecode ρ quiet)
    record (target ∘ HandshakeCausal.Event.admission) same mac

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
