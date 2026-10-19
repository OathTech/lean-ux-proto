import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveRemoval

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

macro "archive_aip_step " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip _ $confirmed)
  | (rx_retention_head liftAip; exact aip _ $confirmed)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | archive_traffic_step $confirmed)

theorem list_add (pid : PeerId) (id : NodeId) (confirmed : List TimestampReceipt) :
    Framing.Preserves (StateInv confirmed) (listAddTail pid id) := by
  unfold listAddTail
  exact update_peer pid (fun p => {p with allowedipsList := p.allowedipsList ++ [id]}) (fun _ => ⟨rfl,rfl⟩) confirmed

theorem add_ip (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) (confirmed : List TimestampReceipt) :
    Framing.Preserves (StateInv confirmed) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch, branchCmp, invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact list_add _ _ confirmed)
    | (rx_retention_head listDel; exact list_del _ confirmed)
    | archive_aip_step confirmed

theorem insert_ip (family addr cidr : Nat) (pid : PeerId) (confirmed : List TimestampReceipt) :
    Framing.Preserves (StateInv confirmed) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact add_ip _ _ _ _ _ confirmed)
    | archive_aip_step confirmed

theorem allowed_ip (pid : PeerId) (ip : AllowedIpAttrs) (confirmed : List TimestampReceipt) :
    Framing.Preserves (StateInv confirmed) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact insert_ip _ _ _ _ confirmed)
    | archive_aip_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
