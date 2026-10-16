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
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hd := (delTimer_routing pid .sendKeepalive).wp P
  have hp := (purgeStagedPackets_routing pid).wp P
  have hm := (modPeerTimer_routing .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).wp P
  have he := (clearPeerEndpointSrc_routing pid).wp P
  have hq := RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid true) s
  have hx (α : Type) := discard_view_spec routingView (m := AmbientM) (α := α) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, expiredRetransmitHandshake, hg, hs, hd, hp, hm, he, hq, hx, branch, branchCmp]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem expiredSendKeepalive_routing (pid : PeerId) :
    RetainsRoutingCall (expiredSendKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have hm := (modPeerTimer_routing .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp P
  have hx (α : Type) := discard_view_spec routingView (m := AmbientM) (α := α) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, expiredSendKeepalive, hg, hs, hk, hm, hx, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem expiredNewHandshake_routing (pid : PeerId) :
    RetainsRoutingCall (expiredNewHandshake pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  have he := (clearPeerEndpointSrc_routing pid).wp (RetainsRouting s)
  have hq := RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, expiredNewHandshake, he, hq]
  subst s
  exact RetainsRouting.refl _

theorem expiredZeroKeyMaterial_routing (pid : PeerId) :
    RetainsRoutingCall (expiredZeroKeyMaterial pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hg := (getPeer_routing pid).wp P
  have hget := (peerGet_routing pid).wp P
  have hput := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  have hm := (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) (fun _ => rfl)).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, expiredZeroKeyMaterial, hg, hget, hput, hm, getDev, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem expiredSendPersistentKeepalive_routing (pid : PeerId) :
    RetainsRoutingCall (expiredSendPersistentKeepalive pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  have hg := (getPeer_routing pid).wp (RetainsRouting s)
  have hk := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, expiredSendPersistentKeepalive, hg, hk, branch]
  all_goals try simp_all
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
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hs := fun port => (socketControl_routing_native _ (socketInit_sameSocket port)).wp P
  have hsend := fun pid => RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have hk := fun pid => RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have hg := fun pid => (getPeer_routing pid).wp P
  have hl (α β : Type) := list_view_spec routingView (m := AmbientM) (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    wgOpen, hs, hsend, hk, hg, getDev, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem wgUp_routing : RetainsRoutingCall wgUp := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  have hm := fun running => (modifyDev_routing (fun d => {d with running}) (fun _ => rfl)).wp (RetainsRouting s)
  have ho := RetainsRoutingCall.wp wgOpen_routing s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, wgUp, hm, ho]
  all_goals try simp_all
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem netnsPreExit_routing : SameView routingView netnsPreExit := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  have hs := (socketControl_routing_native _ (socketReinit_sameSocket none none)).wp (fun t => t = s)
  have he := fun pid => (clearPeerEndpointSrc_routing pid).wp (fun t => t = s)
  have hm := (modifyDev_routing (fun d => {d with carrier := false, creatingNet := false}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec routingView (m := AmbientM) (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, branch, branchCmp,
    AmbientM.branch, AmbientM.branchCmp, invariant, AmbientM.invariant,
    getAmbient, peekQueuedUnit, recordQueued, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    netnsPreExit, hs, he, hm, getDev, branch, invariant]
  all_goals simp_all

end Leanux.Proofs.WG.AllowedIps
