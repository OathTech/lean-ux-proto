import Leanux.Proofs.WG.Roaming.RemoteRetentionModel
import Leanux.Proofs.WG.Roaming.ConsumptionAuthenticationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise
open Noise.ConfirmationOrder Noise.ConsumeConfirmation

/-- Every final destination in this completed consume comes from the entry
map with the consumed packet's remote source installed at the actual peer.
This says nothing about survival of a peer or an endpoint. -/
def ConsumptionFinalRemotes (q : Record) : Prop :=
  RemoteRetained (updateRemote (remoteMap q.observation.entry) q.observation.peer
    (destination (sourceEndpoint q.observation.packet.source)))
    (remoteMap q.observation.finish)


end Leanux.Proofs.WG.Roaming
