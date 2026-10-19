import Leanux.Proofs.WG.Roaming.HandshakeOverlayInspectionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG

theorem step_facts :
    Campaign2.Product.Observes observeStep (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, Authenticated attempt) :=
  inspect_facts receiveStep receiveStep_valid

theorem step_original :
    (do let audit ← observeStep; pure audit.outcome) =
      Campaign2.Product.inspect (liftWG WG.receiveStep) :=
  inspect_original receiveStep _ receiveStep_erases

theorem schedule_facts (stack : Option Worker) :
    Campaign2.Product.Observes (observeSchedule stack) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, Authenticated attempt) := by
  apply inspect_facts
  simpa only [safe_transport] using HandshakeAttemptTransport.schedule_preserves receiver stack

theorem schedule_original (stack : Option Worker) :
    (do let audit ← observeSchedule stack; pure audit.outcome) =
      Campaign2.Product.inspect (Env.schedule stack) :=
  inspect_original _ _ (HandshakeAttemptTransport.schedule_erases receiver stack)

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
