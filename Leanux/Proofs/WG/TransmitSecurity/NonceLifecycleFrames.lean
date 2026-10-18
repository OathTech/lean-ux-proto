import Leanux.Proofs.WG.TransmitSecurity.NonceCreation
import Leanux.Proofs.WG.TransmitSecurity.NonceQueueFrames
import Leanux.Proofs.WG.RetirementSecurity.Rotation
import Leanux.Proofs.WG.RetirementSecurity.Confirmation

/-! Publication changes move references, never resetting a surviving sending
nonce frontier. These frames do not imply any reference holder must survive. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

private theorem modify_peer (pid : PeerId) (f : Peer → Peer) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (RetirementSecurity.updatePeer pid f) :=
  native_frame h ((peer_read pid).bind fun p => peer_write pid (f p))

theorem rotate (pid : PeerId) (newKey : KeypairId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (addNewKeypair pid newKey) := by
  rw [RetirementSecurity.rotation_source]
  unfold RetirementSecurity.rotationBody RetirementSecurity.rotationStart RetirementSecurity.updatePeer
  simp only [branch]
  repeat' nonce_preserves_step h

theorem clear (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (keypairsClear pid) := by
  rw [RetirementSecurity.clear_source]
  unfold RetirementSecurity.clearSlot RetirementSecurity.updateSlot
  repeat' nonce_preserves_step h

theorem confirm (pid : PeerId) (received : KeypairId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (receivedWithKeypair pid received) := by
  unfold receivedWithKeypair
  simp only [branch]
  repeat' first
    | (rx_retention_head modifyPeer; exact modify_peer _ _ h)
    | nonce_preserves_step h
  all_goals exact modify_peer _ _ h

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
