import Leanux.Proofs.WG.Roaming.HandshakeOverlayRxSource
import Leanux.Proofs.WG.Roaming.HandshakeAttemptTransportSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem rxEvent_transport :
    HandshakeAttemptTransport.rxEvent (Attempt := Attempt) = rxEvent := by
  funext e
  cases e <;> rfl

theorem rxAttempt_transport :
    HandshakeAttemptTransport.attempt (Attempt := Attempt) = rxAttempt := by
  funext e
  cases e <;> rfl

theorem safe_transport :
    HandshakeAttemptTransport.Safe (fun h => ∀ r ∈ h, Authenticated r) = RxValid := by
  funext h
  unfold HandshakeAttemptTransport.Safe
  rw [rxAttempt_transport]
  rfl

/-- Concrete authenticated receive callback for the existing scheduler factories. -/
def receiver : HandshakeAttemptTransport.Receive Attempt
    (fun h => ∀ r ∈ h, Authenticated r) where
  step := receiveStep
  projects := by rw [rxEvent_transport]; exact receiveStep_projects
  appends := receiveStep_appends
  preserves := by rw [safe_transport]; exact receiveStep_valid

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
