import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTransmitFrames

/-! Full native outgoing transmission retains historical encryption exclusion
through route selection, staging and final nullable peer payment. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Ready past active) (wgXmit family addr packets mtu) := by
  rw [Packets.wgXmit_front_factor]
  apply preserves_bind (ready_front family addr packets mtu)
  intro result
  cases result with
  | error err => exact preserves_pure err
  | ok pid =>
    unfold Packets.txTail
    exact preserves_bind (send pid) (fun _ => preserves_bind
      (ready_frame (LiveFrontier.peer_put (some pid)) (peer_put (some pid)))
      (fun _ => preserves_pure 0))

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
