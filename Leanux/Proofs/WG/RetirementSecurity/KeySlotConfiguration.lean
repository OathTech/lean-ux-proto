import Leanux.Proofs.WG.RetirementSecurity.KeySlotTransmit
import Leanux.Proofs.WG.RetirementSecurity.KeySlotCreation
import Leanux.Proofs.WG.RetirementSecurity.KeySlotBulkRemoval
import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationFrames
import Leanux.Proofs.WG.Origins.ConfiguredCommand

/-! Native peer configuration preserves slot liveness through cached keepalive
writes, staging, removal, allocation, and early-error payment. Recreating a
peer uses the actual empty-slot creation theorem, not numeric-slot persistence. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Configuration

theorem endpoint (pid : PeerId) (e : Endpoint) : Preserves (InvExcept pending) (setPeerEndpoint pid e) :=
  combined_frame (ConfiguredReceiveLeaves.setPeerEndpoint_view pid e) (endpoint_ownership pid e)

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (InvExcept pending) (setAllowedip pid ip) :=
  combined_frame (CurrentConfiguration.setAllowedip_view pid ip)
    ((HolderConfiguration.allowedip_fields pid ip).factor Prod.fst)

theorem config_finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves (InvExcept pending) (peerTailFinishSource attrs peer pid ret) := by
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head sendStagedPackets; exact staged _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | key_slot_tx_step

theorem config_tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves (InvExcept pending) (peerConfigTailSource attrs peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta:=false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact allowedip _ _)
    | (rx_retention_head peerTailFinishSource; exact config_finish _ _ _ _)
    | key_slot_tx_step

theorem config_update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Preserves (InvExcept pending) (peerConfigUpdateSource attrs peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact remove_peer _)
    | (rx_retention_head setPeerEndpoint; exact endpoint _ _)
    | (rx_retention_head removeByPeer; exact remove_routes _)
    | (rx_retention_head peerConfigTailSource; exact config_tail _ _ _)
    | key_slot_tx_step

theorem config_command (attrs : PeerAttrs) : Preserves (InvExcept pending) (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact create _ _)
    | (rx_retention_head peerConfigUpdateSource; exact config_update _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey _)
    | key_slot_tx_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
