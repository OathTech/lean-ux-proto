import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDevice
import Leanux.Proofs.WG.Queues.TxLivePeerConfiguration

/-! Peer-configuration leaf frames retain allocation epochs and pending packet
aliases while allowed-IP tables and peer metadata change. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.PeerConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxDisposition Keys Socket Maintenance Removal Handshake

theorem aip_ready (action : AipM α) : Preserves (Ready past active) (liftAip action) := by
  apply hoare_liftAip
  intro w d table before device
  simpa only [Ready,LiveFrontier.Ready,LiveFrontier.Inv,LiveFrontier.Physical,
    view,device,Option.map_some,Option.some.injEq,forall_eq'] using before

theorem list_add (pid : PeerId) (node : NodeId) : Preserves (Ready past active) (listAddTail pid node) := by
  unfold listAddTail
  repeat' encryption_past_handshake_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.PeerConfiguration
