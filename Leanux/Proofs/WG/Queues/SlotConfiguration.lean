import Leanux.Proofs.WG.Queues.SlotRemoval

/-! Three-slot compatibility through the original peer configuration command.
All source error results and deleting releases retain their native scope. -/
namespace Leanux.Proofs.WG.CurrentSlots.Configuration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Leanux.Proofs.WG.Configuration

private theorem listAddTail_preserves (pid : PeerId) (id : NodeId) : Preserves Inv (listAddTail pid id) := by
  unfold listAddTail
  repeat' slot_traffic_step

private theorem aip_preserves (action : AipM α) : Preserves Inv (liftAip action) := by
  apply hoare_liftAip
  intro w d table hi hd
  apply fields_transport hi
  unfold fields RxCredits.keyWords
  simp only [hd,Option.map_some,Option.bind_some]

macro "slot_aip_step" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip_preserves _)
  | (rx_retention_head liftAip; exact aip_preserves _)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | slot_remove_step)

theorem add_preserves (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves Inv (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact listAddTail_preserves _ _)
    | (rx_retention_head listDel; exact fields_preserves (project := id) (Removal.listDel_fields _))
    | slot_aip_step

theorem insert_preserves (family addr cidr : Nat) (pid : PeerId) :
    Preserves Inv (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact add_preserves _ _ _ _ _)
    | slot_aip_step

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) : Preserves Inv (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact insert_preserves _ _ _ _)
    | slot_aip_step

private theorem readPeer (pid : PeerId) :
    Hoare (getPeer pid) Inv (fun p w => Inv w ∧ Affiliation.peerAt w pid=some (Affiliation.peerCell p)) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.readPeer_spec) pid

private theorem writePeer (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p) (fun w => Inv w ∧ Affiliation.peerAt w pid=some (Affiliation.peerCell p)) (fun _ => Inv) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.writePeer_spec) pid p

private theorem maybeZero_view (peer : Option PeerId) : SameView Affiliation.view (peerGetMaybeZero peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := ((hoare_iff_run_ambient _ _ _).mp (PeerBorrow.acquire_spec peer (wgStoreView w))
    w a result v b rfl run).2
  change (wgStoreView v).dev.map Affiliation.state=(wgStoreView w).dev.map Affiliation.state
  cases result with
  | none => change wgStoreView v=wgStoreView w at borrowed; rw [borrowed]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    simp only [hv,hd,Option.map_some]
    exact congrArg some (Affiliation.state_peer_same d pid p {p with refcount:=p.refcount+1} hp rfl)

theorem pubkey_preserves (key : Key) : Preserves Inv (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact view_preserves (project := id) (maybeZero_view _))
    | slot_remove_step

theorem finish (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int)  :
    Preserves Inv (peerTailFinishSource a peer pid ret) := by
  have ending (running : Bool) : Preserves Inv (do
      if ← (branch .peerRunning running : WG.M Bool) then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) := by
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _)
      | slot_remove_step
  have read : Preserves Inv getDev := by repeat' slot_remove_step
  unfold peerTailFinishSource
  apply preserves_bind read
  intro d
  apply preserves_bind (hoare_liftAmbient
    (AmbientM.branch .peerHasKeepalive a.keepalive.isSome) Inv)
  intro hasKeepalive
  cases hasKeepalive with
  | false => exact ending d.running
  | true =>
    dsimp only
    apply hoare_bind _ _ (readPeer pid)
    intro p
    let P := fun w => Inv w ∧
      Affiliation.peerAt w pid=some (Affiliation.peerCell p)
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
    apply hoare_bind _ _ (writePeer pid
      {p with persistentKeepaliveInterval := a.keepalive.getD 0})
    intro _
    change Preserves Inv _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch .peerSendKeepalive send) Inv)
    intro sendNow
    cases sendNow with
    | false => exact ending d.running
    | true => exact preserves_bind (((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) pid)) (fun _ => ending d.running)

theorem tail (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId)  :
    Preserves Inv (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp (config := {zeta := false}) only [monadLift_self,branch]
  repeat' first
    | (rx_retention_head setAllowedip; exact allowedip _ _)
    | (rx_retention_head peerTailFinishSource; exact finish _ _ _ _)
    | slot_remove_step

theorem update (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId)  :
    Preserves Inv (peerConfigUpdateSource a peer flags psk pid) := by
  unfold peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerRemove; exact Removal.remove _)
    | (rx_retention_head setPeerEndpoint
       exact fields_preserves (project := id) ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) _ _))
    | (rx_retention_head removeByPeer
       exact Removal.removeByPeer_preserves _)
    | (rx_retention_head peerConfigTailSource; exact tail _ _ _)
    | (env_bind_head getPeer
       apply hoare_bind _ _ (readPeer _)
       intro p
       apply hoare_bind _ _ (writePeer _ _)
       intro _
       change Preserves Inv _)
    | slot_remove_step


/-- Every normal command result retains three-slot compatibility, including errors,
creation and deleting releases. No historical current-key support is required. -/
theorem command (attrs : PeerAttrs) : Preserves Inv (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  unfold setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerCreate
       exact peerCreate_preserves _ _)
    | (rx_retention_head peerConfigUpdateSource; exact update _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey_preserves _)
    | slot_remove_step

end Leanux.Proofs.WG.CurrentSlots.Configuration
