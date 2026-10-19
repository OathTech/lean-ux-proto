import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedRemoval
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedPeerCreation
import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfigurationFrames

/-! Native configuration leaves retain delayed-effect occurrences. The native
trie lift only changes its own extracted store; socket and identity masks leave
resident timer slots and send-work order visible. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem socket_native (action : WG.M α) (same : SameSocket action) : StateSafe (liftWGPrefix action) := by
  apply state_framed
  · intro initial
    apply retained_exact
    apply same.of_factor (fun s pid t => (s.dev.bind fun d => d.peers[pid]?).map
      (fun p => (p.internalId,p.timer t,p.wheel t))) TimerSlots.view
    intro w
    funext pid t
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,TimerSlots.view,Option.bind_map,Function.comp_def]
  · apply same.of_factor (fun s => (s.dev.map Device.sendWorkQueue).getD []) QueuedOccurrences.queue
    intro w
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,QueuedOccurrences.queue,Option.map_map,Function.comp_def]

theorem configuration_native (action : WG.M α) (same : SameConfiguration action) : StateSafe (liftWGPrefix action) := by
  apply state_framed
  · intro initial
    apply retained_exact
    apply same.of_factor (fun s pid t => (s.dev.bind fun d => d.peers[pid]?).map
      (fun p => (p.internalId,p.timer t,p.wheel t))) TimerSlots.view
    intro w
    funext pid t
    simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,TimerSlots.view,Option.bind_map,Function.comp_def]
  · apply same.of_factor (fun s => (s.dev.map Device.sendWorkQueue).getD []) QueuedOccurrences.queue
    intro w
    simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,QueuedOccurrences.queue,Option.map_map,Function.comp_def]

theorem aip_native (action : AipM α) : StateSafe (liftWGPrefix (monadLift action : WG.M α)) := by
  apply state_framed
  · intro initial
    apply hoare_liftAip
    intro w d table hi hd pid t token found
    exact hi pid t token (by simpa only [TimerSlots.view,Option.bind_some,hd] using found)
  · intro initial
    apply hoare_liftAip
    intro w d table hi hd
    simpa only [QueuedOccurrences.queue,hd,Option.map_some] using hi

macro "causal_delayed_aip_native " h:term : tactic => `(tactic| first
  | (first | allocation_release_lift_from AipM | rx_retention_head liftAip
     exact native_contract _ (aip_native _) $h)
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) $h)
  | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) $h)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

private theorem add_allowed (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    StateSafe (liftWGPrefix (add root bits key cidr peer)) := by
  apply state_native
  intro h
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listDel; exact native_contract _ (list_delete _) h)
    | (rx_retention_head listAddTail; exact native_contract _
        (native_peer_update _ _ (by intro p t; rfl)) h)
    | causal_delayed_aip_native h

private theorem insert_allowed (family addr cidr : Nat) (pid : PeerId) :
    StateSafe (liftWGPrefix (WG.insert family addr cidr pid)) := by
  apply state_native
  intro h
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact native_contract _ (add_allowed _ _ _ _ _) h)
    | causal_delayed_aip_native h

theorem allowedip (pid : PeerId) (ip : AllowedIpAttrs) : StateSafe (liftWGPrefix (setAllowedip pid ip)) := by
  apply state_native
  intro h
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact native_contract _ (insert_allowed _ _ _ _) h)
    | causal_delayed_aip_native h

theorem pubkey (key : Key) : StateSafe (liftWGPrefix (pubkeyLookup key)) := by
  apply state_framed _ (pubkeyLookup_retained key)
  intro initial
  change Preserves (fun w => SendWorkCauses.queue w = initial) _
  unfold pubkeyLookup peerGetMaybeZero
  simp only [branch,branchCmp,refcountIncNotZero,invariant,unsupported,requireNotPending]
  repeat' queue_callback_step initial

theorem expire_keys (pid : PeerId) : StateSafe (liftWGPrefix (expireCurrentPeerKeypairs pid)) := by
  apply state_framed
  · intro initial
    unfold expireCurrentPeerKeypairs handshakeClear handshakeZero resetLastSentHandshake
    simp only [requireNotPending,branch,invariant,hiddenClock64]
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold expireCurrentPeerKeypairs handshakeClear handshakeZero resetLastSentHandshake
    simp only [requireNotPending,branch,invariant,hiddenClock64]
    repeat' send_work_frame_step initial

theorem clear_endpoint (pid : PeerId) : StateSafe (liftWGPrefix (clearPeerEndpointSrc pid)) := by
  apply state_framed
  · intro initial
    unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' timer_data_step initial
  · intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
    simp only [getAmbient,hiddenJiffies]
    repeat' queue_callback_step initial

theorem port (value : Nat) : StateSafe (liftWGPrefix (setPort value)) := by
  apply state_native
  intro h
  unfold setPort
  simp only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact native_contract _ (clear_endpoint _) h)
    | (rx_retention_head socketInit; exact native_contract _ (socket_native _ (socketInit_sameSocket _)) h)
    | (rx_retention_head ForIn.forIn; apply list_view_spec id (Inv h); intro x state; change Preserves (Inv h) _)
    | causal_delayed_aip_native h

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
