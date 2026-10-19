import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceKeepalive

/-! The actual authenticated receive continuation preserves positivity through
confirmation, pending-packet staging and source routing. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem receive_tail (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Observed (E := E) (Driver.receiveTailObserved EntrySource.hooks (E := E) pid pkt confirmed) := by
  change StatePrefixPreserves (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) _
  unfold Driver.receiveTailObserved
  simp only [Driver.prepare_lift EntrySource.hooks (E := E) rfl]
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | (nonce_source_head timersHandshakeComplete; exact lift _ (complete _ _))
    | (nonce_source_head RxCredits.prepareRest; exact lift _ (prepare_rx _ _))
    | (nonce_source_head Packets.rxFinish; exact lift _ (finish_rx _ _))
    | (nonce_source_head branch; exact ambient _)
    | (nonce_source_head Pure.pure; exact pure _)
    | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
    | split
    | (with_reducible intro x; try dsimp only)

theorem consume_data (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Observed (E := E) (Driver.consumeObserved EntrySource.hooks (E := E) pid pkt ep) := by
  unfold Driver.consumeObserved
  dsimp only [EntrySource.hooks]
  apply StatePrefixEnsures.bind (lift _ (endpoint pid ep))
  intro _
  apply StatePrefixEnsures.bind (lift _ (confirm pid pkt.keypair))
  intro confirmed
  exact receive_tail pid pkt confirmed

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
