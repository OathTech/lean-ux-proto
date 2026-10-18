import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationProjection
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationAuthorizedPoll

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The native slot projection required from H1's
`Noise.receivedWithKeypair_effect` and `ConfirmationEffect`: a normal result
promotes exactly when the received slot was pending. This premise concerns a
single source call; it supplies neither initialized uniqueness nor allocation
identity across separate calls. The campaign-2 branch is not imported. -/
def H1ConfirmationEdges : Prop :=
  ∀ (pid : PeerId) (kid : KeypairId) (w v : WGWorld) (a b : Ambient) (result : Bool),
    ((receivedWithKeypair pid kid).run w).run a = .ok ((result, v), b) →
      ∃ before after,
        Confirmation.slotsAt w pid = some before ∧ Confirmation.slotsAt v pid = some after ∧
        (result = true ↔ before.next = some kid) ∧ after.identity = before.identity ∧
        (result = true → after.current = some kid ∧ after.next = none ∧
          after.previous = before.current) ∧
        (result = false → after = before)

namespace Confirmation.Authorization

theorem receipt_slots (H1 : H1ConfirmationEdges) (r : Receipt) (valid : r.Valid) :
    ∃ before after,
      slotsAt r.confirmation.execution.before r.confirmation.peer = some before ∧
      slotsAt r.confirmation.execution.after r.confirmation.peer = some after ∧
      (r.confirmation.execution.value = true ↔ before.next = some r.confirmation.packet.keypair) ∧
      after.identity = before.identity ∧
      (r.confirmation.execution.value = true →
        after.current = some r.confirmation.packet.keypair ∧ after.next = none ∧
        after.previous = before.current) ∧
      (r.confirmation.execution.value = false → after = before) :=
  H1 r.confirmation.peer r.confirmation.packet.keypair r.confirmation.execution.before
    r.confirmation.execution.after r.confirmation.execution.ambientBefore
    r.confirmation.execution.ambientAfter r.confirmation.execution.value valid.2.2.2

end Confirmation.Authorization
end Leanux.Proofs.WG.HandshakeSecurity
