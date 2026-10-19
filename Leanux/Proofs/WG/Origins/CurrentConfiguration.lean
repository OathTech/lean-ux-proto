import Leanux.Proofs.WG.Origins.CurrentTraffic
import Leanux.Proofs.WG.Origins.ConfiguredReceiveLeaves
import Leanux.Proofs.WG.Origins.RetainingConfiguration

/-! Normal configured/current identity preservation at the concrete peer-update
stages. All attribute values, nullable peers and native endpoints are unrestricted;
failed records and source guards remain Stops, and release may erase residents. -/
namespace Leanux.Proofs.WG.CurrentConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration ConfiguredHandshake CurrentLifecycle CurrentTraffic

macro "configuration_view_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from AipM
     apply hoare_liftAip
     intro w d store hi hd
     simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi)
  | (rx_retention_head liftAip
     apply hoare_liftAip
     intro w d store hi hd
     simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi)
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | configured_step $initial)

private theorem listAddTail_view (pid : PeerId) (id : NodeId) :
    SameView ConfiguredIdentity.view (listAddTail pid id) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold listAddTail
  repeat' configured_step initial

private theorem add_view (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView ConfiguredIdentity.view (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact (listAddTail_view _ _).wp (fun s => s = initial))
    | (rx_retention_head listDel; exact (ConfiguredIdentity.listDel_view _).wp (fun s => s = initial))
    | configuration_view_step initial

private theorem insert_view (family addr cidr : Nat) (pid : PeerId) :
    SameView ConfiguredIdentity.view (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (add_view _ _ _ _ _).wp (fun s => s = initial))
    | configuration_view_step initial

theorem setAllowedip_view (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView ConfiguredIdentity.view (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (insert_view _ _ _ _).wp (fun s => s = initial))
    | configuration_view_step initial

theorem setAllowedip_preserves (pid : PeerId) (ip : AllowedIpAttrs)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (setAllowedip pid ip) :=
  current_preserves _ (setAllowedip_view pid ip)
    (Origins.Retaining.of_view (Origins.Retaining.setAllowedip_material pid ip)) history

theorem peerTailFinish_preserves (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerTailFinishSource a peer pid ret) := by
  have ending (running : Bool) : Preserves (Inv history) (do
      if ← (branch .peerRunning running : WG.M Bool) then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _ history)
      | current_traffic_step history
  have read : Preserves (Inv history) getDev := by current_lifecycle_step history
  unfold peerTailFinishSource
  apply preserves_bind read
  intro d
  apply preserves_bind (hoare_liftAmbient
    (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) (Inv history))
  intro hasKeepalive
  cases hasKeepalive with
  | false => exact ending d.running
  | true =>
    dsimp only
    apply hoare_bind _ _ (readPeer_spec history pid)
    intro p
    let P := fun w => Inv history w ∧
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
    apply hoare_bind _ _ (writePeer_spec history pid
      {p with persistentKeepaliveInterval := a.keepalive.getD 0})
    intro _
    change Preserves (Inv history) _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) (Inv history))
    intro sendNow
    cases sendNow with
    | false => exact ending d.running
    | true => exact preserves_bind (sendKeepalive_preserves pid history) (fun _ => ending d.running)

theorem peerConfigTail_preserves (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact setAllowedip_preserves _ _ history)
    | (rx_retention_head peerTailFinishSource; exact peerTailFinish_preserves _ _ _ _ history)
    | current_traffic_step history

theorem peerConfigUpdate_preserves (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact peerRemove_preserves _ history)
    | (rx_retention_head setPeerEndpoint
       exact current_preserves _ (ConfiguredReceiveLeaves.setPeerEndpoint_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.setPeerEndpoint_material _ _)) history)
    | (rx_retention_head removeByPeer
       exact current_preserves _ (ConfiguredIdentity.removeByPeer_view _)
         (Origins.Retaining.of_view (Origins.Retaining.removeByPeer_material _)) history)
    | (rx_retention_head peerConfigTailSource; exact peerConfigTail_preserves _ _ _ history)
    | (env_bind_head getPeer
       apply hoare_bind _ _ (readPeer_spec history _)
       intro p
       apply hoare_bind _ _ (writePeer_spec history _ _)
       intro _
       change Preserves (Inv history) _)
    | current_traffic_step history

end Leanux.Proofs.WG.CurrentConfiguration
