import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceRemoval

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

macro "peer_reference_aip_step" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip _)
  | (rx_retention_head liftAip; exact aip _)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | peer_reference_traffic_step)

theorem list_add (pid : PeerId) (id : NodeId) :
    Framing.Preserves Inv (listAddTail pid id) := by
  unfold listAddTail
  exact update_peer pid (fun p => {p with allowedipsList := p.allowedipsList ++ [id]}) (fun _ positive => positive)

theorem add_ip (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Framing.Preserves Inv (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch, branchCmp, invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact list_add _ _)
    | (rx_retention_head listDel; exact list_del _)
    | peer_reference_aip_step

theorem insert_ip (family addr cidr : Nat) (pid : PeerId) :
    Framing.Preserves Inv (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact add_ip _ _ _ _ _)
    | peer_reference_aip_step

theorem allowed_ip (pid : PeerId) (ip : AllowedIpAttrs) :
    Framing.Preserves Inv (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact insert_ip _ _ _ _)
    | peer_reference_aip_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
