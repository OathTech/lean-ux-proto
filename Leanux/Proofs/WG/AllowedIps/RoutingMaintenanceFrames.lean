import Leanux.Proofs.WG.AllowedIps.RoutingNapiFrames
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceLifecycleFrames
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks

/-! Concrete timer and device-control routing frames. Timer callbacks and staged
sends may delete a peer; later original getters either establish a fresh setter
witness or Stop. Saved peer lists, successful drains and reference credits are
not premises. Device absence is retained by these normal-endpoint contracts. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem expiredRetransmitHandshake_routing (pid : PeerId) :
    RetainsRoutingCall (expiredRetransmitHandshake pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hd := (delTimer_routing pid .sendKeepalive).wp P
  have hp := (purgeStagedPackets_routing pid).wp P
  have hm := (modPeerTimer_routing .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).wp P
  have he := (clearPeerEndpointSrc_routing pid).wp P
  have hq := (sendQueuedHandshakeInitiation_routing pid true).wp s
  have hx (α : Type) := discard_view_spec routingView (α := α) P
  mvcgen [expiredRetransmitHandshake, hg, hs, hd, hp, hm, he, hq, hx, branch, branchCmp]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem expiredSendKeepalive_routing (pid : PeerId) :
    RetainsRoutingCall (expiredSendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := (sendKeepalive_routing pid).wp s
  have hm := (modPeerTimer_routing .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp P
  have hx (α : Type) := discard_view_spec routingView (α := α) P
  mvcgen [expiredSendKeepalive, hg, hs, hk, hm, hx, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem expiredNewHandshake_routing (pid : PeerId) :
    RetainsRoutingCall (expiredNewHandshake pid) := by
  apply ProjectedAction.of_wp
  intro s
  have he := (clearPeerEndpointSrc_routing pid).wp (RetainsRouting s)
  have hq := (sendQueuedHandshakeInitiation_routing pid false).wp s
  mvcgen [expiredNewHandshake, he, hq]
  subst s
  exact RetainsRouting.refl _

theorem expiredZeroKeyMaterial_routing (pid : PeerId) :
    RetainsRoutingCall (expiredZeroKeyMaterial pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := (getPeer_routing pid).wp P
  have hget := (peerGet_routing pid).wp P
  have hput := (peerPut_retainsRouting (some pid)).wp s
  have hrec := (routing_kernel _ (recordQueued_sameKernel .clearPeerWorker pid)).wp P
  have hm := (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) (fun _ => rfl)).wp P
  mvcgen [expiredZeroKeyMaterial, hg, hget, hput, hrec, hm, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem expiredSendPersistentKeepalive_routing (pid : PeerId) :
    RetainsRoutingCall (expiredSendPersistentKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (RetainsRouting s)
  have hk := (sendKeepalive_routing pid).wp s
  mvcgen [expiredSendPersistentKeepalive, hg, hk, branch]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem timerCallback_routing (pid : PeerId) (timer : PeerTimer) :
    RetainsRoutingCall (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshake_routing pid
  | sendKeepalive => exact expiredSendKeepalive_routing pid
  | newHandshake => exact expiredNewHandshake_routing pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterial_routing pid
  | persistentKeepalive => exact expiredSendPersistentKeepalive_routing pid

theorem wgOpen_routing : RetainsRoutingCall wgOpen := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hs := fun port => (socketControl_routing _ (socketInit_sameSocketKernel port)).wp P
  have hsend := fun pid => (sendStagedPackets_routing pid).wp s
  have hk := fun pid => (sendKeepalive_routing pid).wp s
  have hg := fun pid => (getPeer_routing pid).wp P
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    wgOpen, hs, hsend, hk, hg, getDev, getK, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem wgUp_routing : RetainsRoutingCall wgUp := by
  apply ProjectedAction.of_wp
  intro s
  have hm := fun running => (modifyDev_routing (fun d => {d with running}) (fun _ => rfl)).wp (RetainsRouting s)
  have ho := wgOpen_routing.wp s
  mvcgen [wgUp, hm, ho]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem netnsPreExit_routing : SameView routingView netnsPreExit := by
  apply SameView.of_wp
  intro s
  have hs := (socketControl_routing _ (socketReinit_sameSocketKernel none none)).wp (fun t => t = s)
  have he := fun pid => (clearPeerEndpointSrc_routing pid).wp (fun t => t = s)
  have hm := (modifyDev_routing (fun d => {d with carrier := false, creatingNet := false}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    netnsPreExit, hs, he, hm, getDev, getK, branch, invariant]

end Leanux.Proofs.WG.AllowedIps
