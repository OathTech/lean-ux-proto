import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveReceiveFrames

/-! The common native consumer retains timestamp history through endpoint
updates, confirmation, receive-triggered staging and decrypted-packet routing. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem receive_tail (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Preserves (Driver.receiveTailObserved TimestampDriver.hooks pid pkt confirmed) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold Driver.receiveTailObserved
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
    Preserves (Driver.consumeObserved TimestampDriver.hooks pid pkt ep) := by
  unfold Driver.consumeObserved
  dsimp only [TimestampDriver.hooks]
  apply StatePrefixEnsures.bind (lift _ (endpoint pid ep))
  intro _
  apply StatePrefixEnsures.bind (lift _ (confirm pid pkt.keypair))
  intro confirmed
  exact receive_tail pid pkt confirmed

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
