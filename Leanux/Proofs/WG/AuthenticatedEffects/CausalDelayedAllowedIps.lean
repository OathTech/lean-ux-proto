import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedDeferred
import Leanux.Proofs.WG.Packets.PublicationAllowedIps
import Leanux.Proofs.WG.Packets.PublicationRemoval

/-! Trie mutation retains the actual timer and send-work observations. Saved
peer-list writes use the existing exact list-deletion source theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem node_native (action : WG.M α) (same : SameNode action) : StateSafe (liftWGPrefix action) := by
  apply state_framed
  · intro initial
    apply retained_exact
    apply same.of_factor (fun s pid t => (s.dev.bind fun d => d.peers[pid]?).map
      (fun p => (p.internalId,p.timer t,p.wheel t))) TimerSlots.view
    intro w
    funext pid t
    simp only [nodeView,nodeDevice,wgStoreView,TimerSlots.view,Option.bind_map,Function.comp_def]
  · apply same.of_factor (fun s => (s.dev.map Device.sendWorkQueue).getD []) QueuedOccurrences.queue
    intro w
    simp only [nodeView,nodeDevice,wgStoreView,QueuedOccurrences.queue,Option.map_map,Function.comp_def]

theorem list_delete (id : NodeId) : StateSafe (liftWGPrefix (listDel id)) := by
  apply state_native
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  cases hd : w.dev with
  | none => simp [listDel,getDev,hd,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    obtain ⟨x,u,c,actual,_,state⟩ := (total_iff_run_ambient _ _ _).mp
      (AllowedIps.listDel_wp w d hd id) w a rfl
    cases actual.symm.trans run
    rw [state]
    apply hi.retained
    · intro pid t token pending
      cases t <;> simpa only [TimerSlots.view,Option.bind_some,AllowedIps.unlisted_get,Option.map_map,
        Function.comp_def,AllowedIps.unlist,Peer.timer,Peer.wheel,hd] using pending
    · simp only [QueuedOccurrences.queue,AllowedIps.unlisted,hd,Option.map_some]

theorem remove_allowed (pid : PeerId) : StateSafe (liftWGPrefix (removeByPeer pid)) := by
  apply state_native
  intro h
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact native_contract _ (list_delete _) h)
    | (rx_retention_head AllowedIps.removeNodeBody
       exact native_contract _ (node_native _ (removeNodeBody_sameNode _)) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head getPeer; exact native_contract _ (by causal_delayed_native) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn; apply list_view_spec id (Inv h); intro x state; change Preserves (Inv h) _)
    | rx_retention_step

theorem free_allowed : StateSafe (liftWGPrefix WG.free) := by
  apply state_native
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  have fields := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView w)) w a value v b rfl run
  apply hi.retained
  · have peers := congrArg Prod.snd fields
    intro pid t token pending
    have projected := congrArg (fun f : PeerId → Option Peer =>
      (f pid).map (fun p => (p.internalId,p.timer t,p.wheel t))) peers
    have same : TimerSlots.view v pid t = TimerSlots.view w pid t := by
      cases t <;> simpa only [TimerSlots.view,Peer.timer,Peer.wheel,AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,wgStoreView,
      AllowedIps.resetAllowedips,Option.bind_map,Option.map_bind,Option.map_map,
      Function.comp_def] using projected
    exact same ▸ pending
  · have queues := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
      (s.1.dev.map Device.sendWorkQueue).getD []) fields
    simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,wgStoreView,
      AllowedIps.resetAllowedips,Option.map_map,Function.comp_def,QueuedOccurrences.queue] using queues

theorem dead (pid : PeerId) : StateSafe (liftWGPrefix (peerMakeDead pid)) := by
  apply state_native
  intro h
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact native_contract _ (remove_allowed _) h)
    | (env_bind_head getPeer; exact native_contract _
        (native_peer_update _ _ (by intro p t; rfl)) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
