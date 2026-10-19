import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastPeerFrames

/-! Actual peer configuration preserves historical encryption exclusion through
fresh allocation, allowed-IP changes, removal and guarded staged sends. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.PeerConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxDisposition Keys Socket Maintenance Removal Handshake
open Leanux.Proofs.WG.Configuration
set_option maxHeartbeats 600000

macro "encryption_past_aip_step" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip_ready _)
  | (rx_retention_head liftAip; exact aip_ready _)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | encryption_past_handshake_step)

theorem allowedip_add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves (Ready past active) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact list_add _ _)
    | (rx_retention_head listDel
       exact list_delete _)
    | encryption_past_aip_step

theorem allowedip_insert (family addr cidr : Nat) (pid : PeerId) : Preserves (Ready past active) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact allowedip_add _ _ _ _ _)
    | encryption_past_aip_step

theorem allowedip_set (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Ready past active) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact allowedip_insert _ _ _ _)
    | encryption_past_aip_step

theorem precompute (pid : PeerId) : Preserves (Ready past active) (precomputeStaticStatic pid) := by
  unfold precomputeStaticStatic requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_handshake_step

private theorem handshake_init (pid : PeerId) (psk : Option Key) : Preserves (Ready past active) (handshakeInit pid psk) := by
  unfold handshakeInit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact ready_owner_word _ _)
    | (rx_retention_head precomputeStaticStatic; exact precompute _)
    | encryption_past_handshake_step

theorem peer_create (key : Key) (psk : Option Key) : Preserves (Ready past active) (peerCreate key psk) := by
  unfold peerCreate resetLastSentHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,hiddenClock64]
  repeat' first
    | (rx_retention_head dstCacheReset
       exact ready_cache _)
    | (rx_retention_head handshakeInit; exact handshake_init _ _)
    | encryption_past_handshake_step

theorem peer_finish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves (Ready past active) (peerTailFinishSource a peer pid ret) := by
  unfold peerTailFinishSource WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendStagedPackets; exact send _)
    | encryption_past_handshake_step

theorem peer_tail (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves (Ready past active) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact allowedip_set _ _)
    | (rx_retention_head peerTailFinishSource; exact peer_finish _ _ _ _)
    | encryption_past_handshake_step

theorem peer_update (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves (Ready past active) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact remove_peer _)
    | (rx_retention_head setPeerEndpoint
       exact ready_endpoint _ _)
    | (rx_retention_head removeByPeer; exact remove_allowedips _)
    | (rx_retention_head peerConfigTailSource; exact peer_tail _ _ _)
    | encryption_past_handshake_step

theorem set_peer (attrs : PeerAttrs) : Preserves (Ready past active) (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact peer_create _ _)
    | (rx_retention_head peerConfigUpdateSource; exact peer_update _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey_lookup _)
    | encryption_past_handshake_step

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.PeerConfiguration
