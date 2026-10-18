import Leanux.Proofs.WG.Roaming.RemoteConfigurationModel
import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteModel
import Leanux.Proofs.WG.Roaming.ConsumptionDestinationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

namespace RemoteProvenance
/-- Public projected explanations for a destination. Actual occurrence in the
single executed history is supplied separately by the source relation. -/
inductive Origin where
  | configuration (receipt : RemoteConfiguration.EndpointReceipt)
  | handshake (observation : ReceiveStepRemote.Observation)
  | data (record : ConfirmationOrder.Record) (authentication : ConsumptionAuthentication)

def Origin.Facts (origin : Origin) (pid : PeerId) (remote : Nat × Nat × Nat × Nat) : Prop :=
  match origin with
  | .configuration r =>
    r.peer = pid ∧ destination r.endpoint = remote ∧
    (r.endpoint.family = AF_INET ∨ r.endpoint.family = AF_INET6) ∧ r.Effect
  | .handshake q => q.Facts ∧ q.Cause pid remote
  | .data q e =>
    q.observation.peer = pid ∧ destination q.observation.endpoint = remote ∧
    e.Facts q ∧ ConsumptionFinalRemotes q

end RemoteProvenance
end Leanux.Proofs.WG.Roaming
