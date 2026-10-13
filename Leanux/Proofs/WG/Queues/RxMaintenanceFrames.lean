import Leanux.Proofs.WG.Queues.RxQueuePrimitives

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Original endpoint and timer maintenance frames. Hidden-input validation
and failures remain in the original operations; no time or ownership premise
is added to the successful-endpoint queue contracts. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem dstCacheReset_rxQueues (pid : PeerId) : SameView rxQueues (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have ht := (rxQueues_kernel (hiddenJiffies_sameKernel .dstCacheResetTs)).wp (fun t => t = s)
  mvcgen [dstCacheReset, hg, hs, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem setPeerEndpoint_rxQueues (pid : PeerId) (e : Endpoint) : SameView rxQueues (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hn := (requireNotPending_rxQueues pid "changing the endpoint").wp (fun t => t = s)
  have he := fun old => (rxQueues_kernel (endpointEq_sameKernel e old)).wp (fun t => t = s)
  have hc := (dstCacheReset_rxQueues pid).wp (fun t => t = s)
  mvcgen [setPeerEndpoint, hg, hs, hn, he, hc, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem armTimer_rxQueues (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView rxQueues (armTimer pid timer delay) := by
  rw [armTimer_source]
  apply SameView.bind (rxQueues_kernel (timerArmExpiry_sameKernel pid timer delay))
  intro expiry
  exact modifyPeer_rxQueues pid (fun p => p.setTimer timer (some expiry))
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem delTimer_rxQueues (pid : PeerId) (timer : PeerTimer) : SameView rxQueues (delTimer pid timer) :=
  modifyPeer_rxQueues pid (fun p => p.setTimer timer none)
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_rxQueues (pid : PeerId) : SameView rxQueues (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_rxQueues pid).wp (fun t => t = s)
  mvcgen [modPeerTimerGuard, getDev, getK, hg, WG.andM, branch, invariant]

theorem modPeerTimer_rxQueues (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView rxQueues (modPeerTimer pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_rxQueues pid).wp (fun t => t = s)
  have ha := (armTimer_rxQueues pid timer delay).wp (fun t => t = s)
  mvcgen [modPeerTimer, hg, ha]

theorem timersHandshakeComplete_rxQueues (pid : PeerId) (site : HiddenSite) :
    SameView rxQueues (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hd := (delTimer_rxQueues pid .retransmitHandshake).wp (fun t => t = s)
  have hh := (rxQueues_kernel (hidden_sameKernel site)).wp (fun t => t = s)
  mvcgen [timersHandshakeComplete, hg, hs, hd, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem timersAnyAuthenticatedPacketReceived_rxQueues (pid : PeerId) :
    SameView rxQueues (timersAnyAuthenticatedPacketReceived pid) := delTimer_rxQueues pid .newHandshake

theorem timersDataReceived_rxQueues (pid : PeerId) : SameView rxQueues (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have ht := (modPeerTimer_rxQueues pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec rxQueues (fun t => t = s) _ ht
  mvcgen [timersDataReceived, hg, hs, ht, hd, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem timersTraversal_rxQueues (pid : PeerId) : SameView rxQueues (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_rxQueues pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_rxQueues pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec rxQueues (fun t => t = s) _ (ht delay)
  mvcgen [timersTraversal, hg, ht, hd, branchCmp]

/-- Queueing a handshake can release the extra peer reference. Retention
allows the original release semantics instead of requiring ownership. -/
theorem sendQueuedHandshakeInitiation_rxQueues (pid : PeerId) (retry : Bool) :
    RetainsRx (sendQueuedHandshakeInitiation pid retry) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := getPeer_rx_spec P pid
  have hs := fun p => setPeer_rx_spec P pid p
  have hn := (requireNotPending_rxQueues pid "queueing a handshake").wp P
  have hc := fun date => (rxQueues_kernel (branchExpired_sameKernel .queuedNotExpired date REKEY_TIMEOUT (!·))).wp P
  have hget := (peerGet_rxQueues pid).wp P
  have hput := (peerPut_rxQueues (some pid)).wp s
  have hrec := (rxQueues_kernel (recordQueued_sameKernel .sendWorker pid)).wp P
  have hqueue := (modifyDev_rxQueues (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl)).wp P
  mvcgen [sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hrec, hqueue, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx])
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem keepKeyFreshRx_rxQueues (pid : PeerId) : RetainsRx (keepKeyFreshRx pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := getPeer_rx_spec P pid
  have hs := fun p => setPeer_rx_spec P pid p
  have hk := fun id => (getKeypair_rxQueues id).wp P
  have ht := fun date delay => (rxQueues_kernel (branchExpired_sameKernel .rxFreshExpired date delay)).wp P
  have hq := (sendQueuedHandshakeInitiation_rxQueues pid false).wp s
  mvcgen [keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx])
  all_goals subst s
  all_goals exact rx_retained_refl _

end Leanux.Proofs.WG.Queues
