import Leanux.Proofs.WG.RetirementSecurity.TxWorkConfigurationLeaves

/-! Native peer configuration transports TX service through actual saved-peer
writes, routing updates, creation/removal and staged sends. The matching
get/set proof keeps queue contents and allocation stamps explicit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.Configuration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Leanux.Proofs.WG.Configuration

private theorem read_peer (pid : PeerId) :
    Hoare (getPeer pid) (Serving locals crypt tx)
      (fun p w => Serving locals crypt tx w ∧ peerAt w pid = some p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨rfl,rfl,d,device,stored⟩ := Origins.getPeer_return pid w v p a b run
  exact ⟨before,by simp [peerAt,device,stored]⟩

private theorem write_peer (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (queue : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Hoare (setPeer pid (f p)) (fun w => Serving locals crypt tx w ∧ peerAt w pid = some p)
      (fun _ w => Serving locals crypt tx w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp before.2
  have read : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer,getDev,device,stored]
  apply (hoare_iff_run_ambient _ _ _).mp (serving_peer_update pid f stamp queue) w a result v b before.1
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,read,run⟩

macro "serving_config_step" : tactic => `(tactic| first
  | (rx_retention_head peerPut; exact serving_peer_put _)
  | (rx_retention_head peerGet; exact serving_peer_get _)
  | (rx_retention_head sendKeepalive; exact serving_keepalive _)
  | serving_metadata_step)

theorem peer_finish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Preserves (Serving locals crypt tx) (peerTailFinishSource a peer pid ret) := by
  have ending (running : Bool) : Preserves (Serving locals crypt tx) (do
      if ← (branch .peerRunning running : WG.M Bool) then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact serving_staged _)
      | serving_config_step
  unfold peerTailFinishSource
  apply preserves_bind (serving_store getDev_sameWGStore)
  intro d
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) _)
  intro hasKeepalive
  cases hasKeepalive with
  | false => exact ending d.running
  | true =>
    dsimp only
    apply hoare_bind _ _ (read_peer pid)
    intro p
    let P := fun w => Serving locals crypt tx w ∧ peerAt w pid = some p
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
    change Preserves (Serving locals crypt tx) _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
    intro sendNow
    cases sendNow with
    | false => exact ending d.running
    | true => exact preserves_bind (serving_keepalive pid) (fun _ => ending d.running)

theorem peer_tail (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Preserves (Serving locals crypt tx) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Serving locals crypt tx)
       intro x b
       change Preserves (Serving locals crypt tx) _)
    | (rx_retention_head setAllowedip; exact serving_aip_set _ _)
    | (rx_retention_head peerTailFinishSource; exact peer_finish _ _ _ _)
    | serving_config_step

theorem peer_update_source (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Preserves (Serving locals crypt tx) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (env_bind_head getPeer
       apply hoare_bind _ _ (read_peer pid)
       intro p
       apply hoare_bind _ _ (write_peer pid p (fun q => {q with presharedKey := psk.getD []}) (fun _=>rfl) (fun _=>rfl))
       intro _
       change Preserves (Serving locals crypt tx) _)
    | (rx_retention_head peerRemove; exact serving_remove _)
    | (rx_retention_head setPeerEndpoint; exact serving_maintenance (.endpoint _ _))
    | (rx_retention_head removeByPeer; exact serving_aip_remove _)
    | (rx_retention_head peerConfigTailSource; exact peer_tail _ _ _)
    | (rx_retention_head peerPut; exact serving_peer_put _)
    | rxstack_preserves_join
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem set_peer (attrs : PeerAttrs) : Preserves (Serving locals crypt tx) (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact serving_peer_create _ _)
    | (rx_retention_head peerConfigUpdateSource; exact peer_update_source _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact serving_pubkey _)
    | serving_config_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork.Configuration
