import Leanux.Proofs.WG.Packets.PublicationReceive
import Leanux.Proofs.WG.Origins.OwnerRemoval

/-! Allowed-IP deletion and the actual dead mark retain stored packet
certificates. This covers the pre-drain part of peer removal; work-flush
callbacks and their observed removal suffix are separate obligations. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion

private theorem listDel_geometry (id : NodeId) :
    SameView OwnerCompletion.geometry (listDel id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hr
  cases hd : w.dev with
  | none => simp [listDel,getDev,hd,invariant,AmbientM.invariant] at hr; cases hr
  | some d =>
    obtain ⟨x,u,b,actual,_,state⟩ := (total_iff_run_ambient _ _ _).mp
      (AllowedIps.listDel_wp w d hd id) w ambient rfl
    cases actual.symm.trans hr
    simpa only [OwnerCompletion.geometry,RxCredits.rxView,AllowedIps.unlisted,hd,
      Option.map_some,Option.bind_some] using congrArg OwnerCompletion.geometry state

theorem removeByPeer_geometry (pid : PeerId) :
    SameView OwnerCompletion.geometry (removeByPeer pid) := by
  have node (id : NodeId) : SameView OwnerCompletion.geometry (AllowedIps.removeNodeBody id) :=
    (removeNodeBody_sameNode id).of_factor
      (fun s : WGStoreView => OwnerCompletion.geometry {dev := s.dev}) _ (fun w => by
        simp only [OwnerCompletion.geometry,RxCredits.rxView,nodeView,wgStoreView,nodeDevice,
          Option.map_map,Option.bind_map,Function.comp_def])
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head listDel; exact (listDel_geometry _).wp (fun s => s = initial))
    | (allocation_release_head AllowedIps.removeNodeBody; exact (node _).wp (fun s => s = initial))
    | completion_step initial

theorem removeByPeer_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (removeByPeer pid) :=
  preserves_of_geometry _ (removeByPeer_geometry pid)
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
      (ConfiguredIdentity.removeByPeer_view pid)) history

theorem peerMakeDead_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerMakeDead pid) := by
  apply preserves_of_geometry
  · intro initial
    change Preserves (fun w => OwnerCompletion.geometry w = initial) _
    unfold peerMakeDead
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (allocation_release_head removeByPeer
         exact (removeByPeer_geometry _).wp (fun s => s = initial))
      | completion_step initial
  · intro initial
    unfold peerMakeDead
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (rx_retention_head removeByPeer
         exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
           (ConfiguredIdentity.removeByPeer_view _) initial)
      | publication_peer_step initial

/-- The actual pre-removal observer keeps all lifetime events, including
those preceding a Stop, and appends to the arbitrary input history. -/
theorem removeByPeer_checked (pid : PeerId) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (removeByPeerPrefix pid))) := by
  apply observed_native _ _
    (RxHistory.mixed_erases (liftWGObserver_erases (removeByPeerPrefix_erases pid)))
  · apply OwnerChecks.native_mixed _ _ (removeByPeerPrefix_erases pid)
      (removeByPeerPrefix_preserves allocationAmbient allocationAllowedIps.nodes pid)
      (Origins.Retaining.of_view (Origins.Retaining.removeByPeer_material pid))
    · intro history
      exact ConfiguredHandshake.current_preserves _ (ConfiguredIdentity.removeByPeer_view pid)
        (Origins.Retaining.of_view (Origins.Retaining.removeByPeer_material pid)) history
    · intro history
      exact hoare_consequence (OwnerAllowedIps.removeByPeer_preserves pid)
        (fun _ hi => hi.2) (fun _ _ hi => hi)
  · exact removeByPeer_preserves pid

theorem peerMakeDead_checked (pid : PeerId) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (peerMakeDeadPrefix pid))) := by
  apply observed_native _ _
    (RxHistory.mixed_erases (liftWGObserver_erases (peerMakeDeadPrefix_erases pid)))
  · apply OwnerChecks.native_mixed _ _ (peerMakeDeadPrefix_erases pid)
      (peerMakeDeadPrefix_preserves allocationAmbient allocationAllowedIps pid)
      (Origins.Retaining.of_view (Origins.Retaining.peerMakeDead_material pid))
      (CurrentLifecycle.markDead_preserves pid)
    intro history
    exact hoare_consequence (OwnerRemoval.peerMakeDead_preserves pid)
      (fun _ hi => hi.2) (fun _ _ hi => hi)
  · exact peerMakeDead_preserves pid

end Leanux.Proofs.WG.PublicationFrontier
