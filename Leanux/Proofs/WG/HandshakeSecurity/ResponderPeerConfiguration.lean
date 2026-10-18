import Leanux.Proofs.WG.HandshakeSecurity.ResponderAllowedIps

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining Configuration

def SavedNativePeer (pid : PeerId) (p : Peer) (w : WGWorld) : Prop :=
  ∃ d, w.dev = some d ∧ d.peers[pid]? = some p

theorem read_saved_native (pid : PeerId) (confirmed : List Nat) :
    Hoare (getPeer pid) (History.Native confirmed)
      (fun p w => History.Native confirmed w ∧ SavedNativePeer pid p w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  obtain ⟨same, time, d, hd, hp⟩ := getPeer_normal pid w v p a b run
  subst v b
  exact ⟨hi,d,hd,hp⟩

theorem write_saved_native (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p) (confirmed : List Nat) :
    Hoare (setPeer pid (f p))
      (fun w => History.Native confirmed w ∧ SavedNativePeer pid p w)
      (fun _ => History.Native confirmed) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨d, hd, hp⟩ := hi.2
  have getter : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer, getDev, hd, hp]
  apply (hoare_iff_run_ambient _ _ _).mp (peerUpdate_native pid f same confirmed)
    w a result v b hi.1
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,getter,run⟩

theorem peerFinish_native (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerTailFinishSource a peer pid ret) := by
  have ending (running : Bool) : Preserves (History.Native confirmed) (do
      if ← (branch .peerRunning running : WG.M Bool) then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact staged_native _ confirmed)
      | responder_handshake_step confirmed
  unfold peerTailFinishSource
  apply preserves_bind (native_store getDev_sameWGStore confirmed)
  intro d
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) _)
  intro hasKeepalive
  cases hasKeepalive with
  | false => exact ending d.running
  | true =>
    dsimp only
    apply hoare_bind _ _ (read_saved_native pid confirmed)
    intro p
    let P := fun w => History.Native confirmed w ∧ SavedNativePeer pid p w
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
    apply hoare_bind _ _ (write_saved_native pid p
      (fun p => {p with persistentKeepaliveInterval := a.keepalive.getD 0}) (fun _ => rfl) confirmed)
    intro _
    change Preserves (History.Native confirmed) _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) _)
    intro sendNow
    cases sendNow with
    | false => exact ending d.running
    | true => exact preserves_bind (keepalive_native pid confirmed) (fun _ => ending d.running)

macro "responder_config_step " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (History.Native $confirmed)
     intro x b
     change Preserves (History.Native $confirmed) _)
  | (rx_retention_head peerGet; exact peerGet_native _ $confirmed)
  | responder_handshake_step $confirmed)

theorem peerTail_native (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self, branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact allowedip_native _ _ confirmed)
    | (rx_retention_head peerTailFinishSource; exact peerFinish_native _ _ _ _ confirmed)
    | responder_config_step confirmed

theorem peerUpdateConfig_native (H1 : H1ResponderCurrentEdges) (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact remove_native H1 _ confirmed)
    | (rx_retention_head setPeerEndpoint
       exact native_fields (pool_of_material (setPeerEndpoint_material _ _))
         ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) _ _) confirmed)
    | (rx_retention_head removeByPeer; exact removeByPeer_native _ confirmed)
    | (rx_retention_head peerConfigTailSource; exact peerTail_native _ _ _ confirmed)
    | responder_config_step confirmed

theorem setPeer_native (H1 : H1ResponderCurrentEdges) (a : PeerAttrs) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (setPeerCmd a) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' first
    | (rx_retention_head peerCreate; exact peerCreate_native _ _ confirmed)
    | (rx_retention_head peerConfigUpdateSource; exact peerUpdateConfig_native H1 _ _ _ _ _ confirmed)
    | responder_config_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
