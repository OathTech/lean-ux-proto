import Leanux.Proofs.WG.AllowedIps.RoutingFlushFrames
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.Proofs.Framing.Product

/-! Concrete routing frames for device configuration. Strong existing masks
project to the routing view; peer/key helpers retain their original getters and
Stops. These normal-endpoint frames assert neither progress nor residency. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-- The original product observation masks only the configuration fields of
the device; the remaining store observations retain their original scope. -/
def configurationProductView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    {wgStoreView w.wg with dev := w.wg.dev.map configurationDevice})

/-- The socket mask has the same original product observation domain. -/
def socketControlProductView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    {wgStoreView w.wg with dev := w.wg.dev.map socketDevice})

theorem configuration_routing (a : Leanux.M α)
    (ha : SameView configurationProductView a) :
    SameView (fun w => routingView w.wg) a := by
  apply ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w => routingView w.wg)
  intro w
  simp [routingView, configurationProductView, configurationDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem socketControl_routing (a : Leanux.M α)
    (ha : SameView socketControlProductView a) :
    SameView (fun w => routingView w.wg) a := by
  apply ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w => routingView w.wg)
  intro w
  simp [routingView, socketControlProductView, socketDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem configuration_routing_native (a : WG.M α) (ha : SameConfiguration a) :
    SameView routingView a := by
  apply ha.of_factor (fun k : WGOwnedView => k.dev.map routingState) routingView
  intro w
  simp [routingView, configurationView, configurationDevice,
    routingState, Option.map_map, Function.comp_def]
  rfl

theorem socketControl_routing_native (a : WG.M α) (ha : SameSocket a) :
    SameView routingView a := by
  apply ha.of_factor (fun k : WGOwnedView => k.dev.map routingState) routingView
  intro w
  simp [routingView, socketView, socketDevice,
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
  have hs := (socketControl_routing_native _ (socketInit_sameSocket port)).wp (fun t => t = s)
  have hm := (modifyDev_routing (fun d => {d with incomingPort := port}) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec routingView (m := AmbientM)
    (α := α) (β := β) (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s)
        (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, -Std.Do.Spec.forIn_list,
    -Std.Do.Spec.forIn'_list, hl, setPort, hc, hs, hm, getDev, branch,
    AmbientM.branch, invariant, AmbientM.invariant]

theorem expireCurrentPeerKeypairs_routing (pid : PeerId) :
    SameView routingView (expireCurrentPeerKeypairs pid) := by
  apply SameView.of_wp
  intro s
  have hn := (requireNotPending_routing pid "clearing the handshake").wp (fun t => t = s)
  have hr := (resetLastSentHandshake_routing pid).wp (fun t => t = s)
  have hp := (getPeer_routing pid).wp (fun t => t = s)
  have hg := fun kp => (getKeypair_routing kp).wp (fun t => t = s)
  have hs := fun kp k => (setKeypair_routing kp k).wp (fun t => t = s)
  have hclear := (handshakeClear_routing pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s)
        (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, expireCurrentPeerKeypairs,
    hclear, hn, hr, hp, hg, hs, branch, AmbientM.branch, invariant, AmbientM.invariant]

end Leanux.Proofs.WG.AllowedIps
