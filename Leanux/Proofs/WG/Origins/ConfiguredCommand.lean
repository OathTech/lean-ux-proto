import Leanux.Proofs.WG.Origins.ConfiguredTraffic
import Leanux.Proofs.WG.Origins.CurrentConfiguration
import Leanux.Proofs.WG.Queues.SetPeerBoundary

/-! Standalone configured identity across the original peer command. This
supplies the predicate required by the next command in a device peer list. -/
namespace Leanux.Proofs.WG.ConfiguredCommand
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration ConfiguredTraffic ConfiguredRemoval

theorem finish (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int)  :
    Preserves (ConfiguredIdentity.Inv) (peerTailFinishSource a peer pid ret) := by
  have ending (running : Bool) : Preserves (ConfiguredIdentity.Inv) (do
      if ← (branch .peerRunning running : WG.M Bool) then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact ConfiguredTraffic.staged _)
      | configured_traffic_step
  have read : Preserves (ConfiguredIdentity.Inv) getDev := by configured_removal_step
  unfold peerTailFinishSource
  apply preserves_bind read
  intro d
  apply preserves_bind (hoare_liftAmbient
    (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) (ConfiguredIdentity.Inv))
  intro hasKeepalive
  cases hasKeepalive with
  | false => exact ending d.running
  | true =>
    dsimp only
    apply hoare_bind _ _ (ConfiguredTraffic.readPeer pid)
    intro p
    let P := fun w => ConfiguredIdentity.Inv w ∧
      (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p)
    have decide : Preserves P (WG.andM
        (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
        (WG.andM (branch .peerKeepaliveNonzero (a.keepalive.getD 0 != 0))
          (branch .peerKeepaliveRunning d.running))) := by
      unfold WG.andM
      simp (config := {zeta := false}) only [branch]
      repeat' first
        | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
        | rx_retention_step
    apply hoare_bind _ _ decide
    intro send
    apply hoare_bind _ _ (ConfiguredTraffic.writePeer pid
      {p with persistentKeepaliveInterval := a.keepalive.getD 0})
    intro _
    change Preserves (ConfiguredIdentity.Inv) _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) (ConfiguredIdentity.Inv))
    intro sendNow
    cases sendNow with
    | false => exact ending d.running
    | true => exact preserves_bind (ConfiguredTraffic.keepalive pid) (fun _ => ending d.running)

theorem tail (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId)  :
    Preserves (ConfiguredIdentity.Inv) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact ConfiguredRemoval.frame (CurrentConfiguration.setAllowedip_view _ _))
    | (rx_retention_head peerTailFinishSource; exact finish _ _ _ _)
    | configured_traffic_step

theorem update (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId)  :
    Preserves (ConfiguredIdentity.Inv) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact ConfiguredRemoval.remove _)
    | (rx_retention_head setPeerEndpoint
       exact ConfiguredRemoval.frame (ConfiguredReceiveLeaves.setPeerEndpoint_view _ _))
    | (rx_retention_head removeByPeer
       exact ConfiguredRemoval.frame (ConfiguredIdentity.removeByPeer_view _))
    | (rx_retention_head peerConfigTailSource; exact tail _ _ _)
    | (env_bind_head getPeer
       apply hoare_bind _ _ (ConfiguredTraffic.readPeer _)
       intro p
       apply hoare_bind _ _ (ConfiguredTraffic.writePeer _ _)
       intro _
       change Preserves (ConfiguredIdentity.Inv) _)
    | configured_traffic_step


/-- Every normal command result retains configured identity, including errors,
creation and deleting releases. No key-support history is required. -/
theorem command (attrs : PeerAttrs) : Preserves ConfiguredIdentity.Inv (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate
       exact hoare_consequence (ConfiguredIdentity.peerCreate_spec _ _)
         (fun _ h => h) (fun _ _ h => h.1))
    | (rx_retention_head peerConfigUpdateSource; exact update _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact frame (ConfiguredReceive.pubkeyLookup_view _))
    | configured_traffic_step

end Leanux.Proofs.WG.ConfiguredCommand
