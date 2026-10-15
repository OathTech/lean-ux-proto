import Leanux.Proofs.WG.AllowedIps.RoutingFlushFrames
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGSocketLifecycle

/-! Concrete routing frames for device configuration. Strong existing masks
project to the routing view; peer/key helpers retain their original getters and
Stops. These normal-endpoint frames assert neither progress nor residency. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem configuration_routing (a : M α) (ha : SameConfiguration a) : SameView routingView a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map routingState) routingView
  intro w
  simp [routingView, configurationView, configurationKernel, configurationDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem socketControl_routing (a : M α) (ha : SameSocketKernel a) : SameView routingView a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map routingState) routingView
  intro w
  simp [routingView, socketKernelView, socketKernel, socketDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem dstCacheResetNow_routing (pid : PeerId) : SameView routingView (dstCacheResetNow pid) := by
  apply (dstCacheReset_routing pid).bind
  intro _
  exact modifyPeer_routing pid (fun p => {p with dstCache := {p.dstCache with slot := none}}) (fun _ => rfl)

theorem clearPeerEndpointSrc_routing (pid : PeerId) : SameView routingView (clearPeerEndpointSrc pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hr := (dstCacheResetNow_routing pid).wp (fun t => t = s)
  mvcgen [clearPeerEndpointSrc, hg, hs, hr]
  all_goals simp_all

theorem setPort_routing (port : Nat) : SameView routingView (setPort port) := by
  apply SameView.of_wp
  intro s
  have hc := fun pid => (clearPeerEndpointSrc_routing pid).wp (fun t => t = s)
  have hs := (socketControl_routing _ (socketInit_sameSocketKernel port)).wp (fun t => t = s)
  have hm := (modifyDev_routing (fun d => {d with incomingPort := port}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, setPort, hc, hs, hm, getDev, getK, branch, invariant]

theorem expireCurrentPeerKeypairs_routing (pid : PeerId) :
    SameView routingView (expireCurrentPeerKeypairs pid) := by
  apply SameView.of_wp
  intro s
  have hn := (requireNotPending_routing pid "clearing the handshake").wp (fun t => t = s)
  have hi := (indexRemove_routing (.handshake pid)).wp (fun t => t = s)
  have hh := (handshakeZero_routing pid).wp (fun t => t = s)
  have hr := (resetLastSentHandshake_routing pid).wp (fun t => t = s)
  have hp := (getPeer_routing pid).wp (fun t => t = s)
  have hg := fun kp => (getKeypair_routing kp).wp (fun t => t = s)
  have hs := fun kp k => (setKeypair_routing kp k).wp (fun t => t = s)
  have hclear := (handshakeClear_routing pid).wp (fun t => t = s)
  mvcgen [expireCurrentPeerKeypairs, hclear, hn, hi, hh, hr, hp, hg, hs, branch, invariant]

end Leanux.Proofs.WG.AllowedIps
