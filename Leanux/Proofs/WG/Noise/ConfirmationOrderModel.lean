import Leanux.Proofs.WG.Noise.ConsumeConfirmationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConfirmationOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes ConsumeConfirmation

structure Record where
  position : Nat
  occurrence : Nat
  skb : SkbId
  packetStamp : PacketStamp
  observation : ConfirmationObservation
  internalId : Nat

def successful (qs : List Record) : List Nat :=
  qs.filterMap fun q => if q.observation.confirmed then some q.internalId else none

end Leanux.Proofs.WG.Noise.ConfirmationOrder
