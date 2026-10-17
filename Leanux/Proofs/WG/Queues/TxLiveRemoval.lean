import Leanux.Proofs.WG.Queues.TxLiveMaintenance
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint
import Leanux.Proofs.Framing.WGAllowedIps

/-! Native peer removal and device shutdown retain the encryption-ring live
bound. Peer deletion and original crypt-work rejection remain possible; this
does not assert termination or discharge any native guard. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem ready_fields (hi : Ready w)
    (same : v.dev.map (fun d => (d.nextSkb,d.encryptQueue)) =
      w.dev.map (fun d => (d.nextSkb,d.encryptQueue))) : Ready v := by
  have each (e : Device) (endpoint : v.dev=some e) :
      ∃d,w.dev=some d ∧ e.nextSkb=d.nextSkb ∧ e.encryptQueue=d.encryptQueue := by
    cases hd:w.dev with
    | none => simp [hd,endpoint] at same
    | some d =>
      have pair : (e.nextSkb,e.encryptQueue)=(d.nextSkb,d.encryptQueue) := by
        simpa only [hd,endpoint,Option.map_some,Option.some.injEq] using same
      exact ⟨d,rfl,congrArg Prod.fst pair,congrArg Prod.snd pair⟩
  constructor
  · intro e endpoint
    obtain ⟨d,device,frontier,ring⟩ := each e endpoint
    rw [frontier,ring]
    exact hi.1 d device
  · intro e endpoint
    obtain ⟨d,device,_,ring⟩ := each e endpoint
    rw [ring]
    exact hi.2 d device

theorem fields_ready {action : WG.M α}
    (same : SameView (fun w : WGWorld => w.dev.map (fun d => (d.nextSkb,d.encryptQueue))) action) :
    Preserves Ready action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ready_fields hi ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

private theorem list_delete (id : NodeId) : Preserves Ready (listDel id) :=
  fields_ready ((AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => s.1.dev.map fun d => (d.nextSkb,d.encryptQueue))
    _ (fun w => by simp only [AllowedIps.clearListView,Option.map_map,Function.comp_def]))

private theorem node_remove (id : NodeId) : Preserves Ready (AllowedIps.removeNodeBody id) :=
  fields_ready ((removeNodeBody_sameNode id).of_factor
    (fun s : WGStoreView => s.dev.map fun d => (d.nextSkb,d.encryptQueue))
    _ (fun w => by simp only [nodeView,nodeDevice,wgStoreView,Option.map_map,Function.comp_def]))

theorem remove_allowedips (pid : PeerId) : Preserves Ready (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head listDel; exact list_delete _)
    | (allocation_release_head AllowedIps.removeNodeBody; exact node_remove _)
    | live_socket_step

theorem free_allowedips : Preserves Ready WG.free := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  apply ready_fields hi
  have fields := congrArg
    (fun s : WGStoreView × (PeerId → Option Peer) => s.1.dev.map fun d => (d.nextSkb,d.encryptQueue)) kept
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
    wgStoreView,Option.map_map,Function.comp_def] using fields

theorem make_dead (pid : PeerId) : Preserves Ready (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head removeByPeer; exact remove_allowedips _)
    | live_socket_step

theorem remove_peer (peer : Option PeerId) : Preserves Ready (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head peerMakeDead; exact make_dead _)
    | (allocation_release_head peerRemoveAfterDead; exact remove_after_dead _)
    | live_socket_step

theorem remove_all : Preserves Ready peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head WG.free; exact free_allowedips)
    | (allocation_release_head peerMakeDead; exact make_dead _)
    | (allocation_release_head peerRemoveAfterDead; exact remove_after_dead _)
    | live_socket_step

theorem socket_reinit (new4 new6 : Option Nat) : Preserves Ready (socketReinit new4 new6) := by
  unfold socketReinit sockFree iputReport
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' live_socket_step

theorem stop : Preserves Ready wgStop := by
  unfold wgStop requireNotPending resetLastSentHandshake
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head purgeStagedPackets; exact purge_staged _)
    | (allocation_release_head timersStop; exact timers_stop _)
    | (allocation_release_head handshakeClear; exact handshake_clear _)
    | (allocation_release_head keypairsClear; exact keys_clear _)
    | (allocation_release_head socketReinit; exact socket_reinit _ _)
    | live_socket_step

theorem down : Preserves Ready wgDown :=
  preserves_bind (modify_live _ (fun _=>rfl) (fun _=>rfl)) (fun _=>stop)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
