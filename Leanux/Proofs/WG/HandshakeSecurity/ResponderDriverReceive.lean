import Leanux.Proofs.WG.TransmitSecurity.DriverNestedNeutral
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverRxFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem receive_tail (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Preserves (Driver.receiveTailObserved hooks pid pkt confirmed) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold Driver.receiveTailObserved
  simp only [Driver.nested_prepare_lift hooks rfl rfl,Driver.rxFinish_lift hooks rfl]
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | (nonce_source_head timersHandshakeComplete; exact lift _ (carrier_complete _ _))
    | (nonce_source_head RxCredits.prepareRest; exact lift _ (carrier_prepare _ _))
    | (nonce_source_head Packets.rxFinish; exact lift _ (carrier_finish _ _))
    | (nonce_source_head branch; exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | split
    | (with_reducible intro x; try dsimp only)

/-- Native confirmation is observed and adds authorization before this same
consumer invokes staging. Its checked prefix persists even when the consumer
stops after promotion, before returning an outer completed-consumer receipt. -/
theorem consume (H1 : H1ResponderCurrentEdges) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Preserves (Driver.consumeObserved hooks pid pkt ep) := by
  unfold Driver.consumeObserved
  dsimp only [hooks]
  apply StatePrefixEnsures.bind (lift _ (carrier_endpoint pid ep))
  intro _
  apply StatePrefixEnsures.bind (confirmation_preserves H1 pid pkt.keypair)
  intro confirmed
  exact receive_tail pid pkt confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
