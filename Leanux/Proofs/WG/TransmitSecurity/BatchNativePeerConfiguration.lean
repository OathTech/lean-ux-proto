import Leanux.Proofs.WG.TransmitSecurity.BatchNativeConfigurationLeaves

/-! Native peer configuration retains batch alignment through its actual
saved-peer writes, routing updates, creation/removal and staged sends. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Configuration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native Leanux.Proofs.WG.Configuration

theorem pubkey (key : Key) : Preserves (Coherent locals active) (pubkeyLookup key) :=
  coherent_join (OccurrenceConfiguration.pubkey key)
    (contents_wire (OccurrenceHandshake.pubkey_lookup_contents key) (OccurrenceHandshake.pubkey_lookup_wire key))

theorem precompute (pid : PeerId) : Preserves (Coherent locals active) (precomputeStaticStatic pid) :=
  coherent_join (OccurrenceConfiguration.precompute pid)
    (contents_wire (OccurrenceCreation.precompute_contents pid) (OccurrenceCreation.precompute_wire pid))

private theorem read_peer (pid : PeerId) :
    Hoare (getPeer pid) (Coherent locals active)
      (fun p w => Coherent locals active w ∧ peerAt w pid = some p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨rfl,rfl,d,device,stored⟩ := Origins.getPeer_return pid w v p a b run
  exact ⟨before,by simp [peerAt,device,stored]⟩

private theorem write_peer (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (queue : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Hoare (setPeer pid (f p)) (fun w => Coherent locals active w ∧ peerAt w pid = some p)
      (fun _ w => Coherent locals active w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp before.2
  have read : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer,getDev,device,stored]
  apply (hoare_iff_run_ambient _ _ _).mp (peer_update pid f stamp queue) w a result v b before.1
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,read,run⟩

macro "batch_config_step" : tactic => `(tactic| first
  | (rx_retention_head peerPut; exact Poll.peer_put _)
  | (rx_retention_head peerGet; exact peer_get_coherent _)
  | (rx_retention_head sendKeepalive; exact keepalive _)
  | batch_coherent_step)

theorem peer_finish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves (Coherent locals active) (peerTailFinishSource a peer pid ret) := by
  have ending (running : Bool) : Preserves (Coherent locals active) (do
      if ← (branch .peerRunning running : WG.M Bool) then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact send_coherent _)
      | batch_config_step
  unfold peerTailFinishSource
  apply preserves_bind (coherent_store getDev_sameWGStore)
  intro d
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) _)
  intro hasKeepalive
  cases hasKeepalive with
  | false => exact ending d.running
  | true =>
    dsimp only
    apply hoare_bind _ _ (read_peer pid)
    intro p
    let P := fun w => Coherent locals active w ∧ peerAt w pid = some p
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
    apply hoare_bind _ _ (write_peer pid p
      (fun q => {q with persistentKeepaliveInterval := a.keepalive.getD 0}) (fun _=>rfl) (fun _=>rfl))
    intro _
    change Preserves (Coherent locals active) _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
    intro sendNow
    cases sendNow with
    | false => exact ending d.running
    | true => exact preserves_bind (keepalive pid) (fun _ => ending d.running)

theorem peer_tail (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves (Coherent locals active) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | (rx_retention_head setAllowedip; exact allowedip_set _ _)
    | (rx_retention_head peerTailFinishSource; exact peer_finish _ _ _ _)
    | batch_config_step

theorem peer_update_source (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves (Coherent locals active) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (env_bind_head getPeer
       apply hoare_bind _ _ (read_peer pid)
       intro p
       apply hoare_bind _ _ (write_peer pid p (fun q => {q with presharedKey := psk.getD []}) (fun _=>rfl) (fun _=>rfl))
       intro _
       change Preserves (Coherent locals active) _)
    | (rx_retention_head peerRemove; exact Removal.remove _)
    | (rx_retention_head setPeerEndpoint; exact maintenance_coherent (.endpoint _ _))
    | (rx_retention_head removeByPeer; exact Removal.allowedips _)
    | (rx_retention_head peerConfigTailSource; exact peer_tail _ _ _)
    | (rx_retention_head peerPut; exact Poll.peer_put _)
    | rxstack_preserves_join
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem set_peer (attrs : PeerAttrs) : Preserves (Coherent locals active) (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact create _ _)
    | (rx_retention_head peerConfigUpdateSource; exact peer_update_source _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey _)
    | batch_config_step

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Configuration
