import Leanux.Proofs.WG.AllowedIps.RoutingSendFrames
import Leanux.Proofs.WG.Queues.RxStackFrames
import Leanux.Proofs.WG.Lifetimes.SocketSend4

/-! Original socket-send routing frames. Existing socket source factors retain
all route, hidden-input and loopback branches; no successful-send premise is used. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem dstCacheGet_routing (pid : PeerId) (gen : Nat) : SameView routingView (dstCacheGet pid gen) := by
  apply SameView.of_wp
  intro s
  have hp := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have ambient {α : Type} (a : AmbientM α) (P : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) P (fun _ => P) := hoare_liftAmbient a P
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, dstCacheGet, getAmbient, hiddenJiffies,
    hp, hs, ambient, branch, branchCmp]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView]
  all_goals try assumption

theorem dstCacheSet_routing (pid : PeerId) (src gen dev : Nat) : SameView routingView (dstCacheSet pid src gen dev) := by
  apply SameView.of_wp
  intro s
  have hp := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [dstCacheSet, hp, hs, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem tunnelXmit_routing (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView routingView ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  apply SameView.of_wp
  intro s
  have hl := fun sites force => (routing_kernel _ (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites force)).wp (fun t => t = s)
  have hp := fun fam => (routing_kernel _ (socketPort_sameStore fam)).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, tunnelXmitSource, hl, hp, ambient,
    modifyDev, skipCut, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4ClearSrc_routing cache : SameView routingView (send4ClearSrcSource cache) := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => routing_getPeer (fun t => t = s) pid
  have hs := fun pid p => routing_setPeer (fun t => t = s) pid p
  mvcgen [send4ClearSrcSource, hp, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4Finish_routing e bytes ds exactRx route : SameView routingView (send4FinishSource e bytes ds exactRx route) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    routing a
  unfold Hoare at routing route
  have ht := fun r => (tunnelXmit_routing e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4FinishSource, ht, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4RouteDone_routing e cache bytes ds exactRx gen fallback rt :
    SameView routingView (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  apply SameView.of_wp
  intro s
  have hs := fun pid src gen dev => (dstCacheSet_routing pid src gen dev).wp (fun t => t = s)
  have hf := fun r => (send4Finish_routing e bytes ds exactRx r).wp (fun t => t = s)
  mvcgen [send4RouteDoneSource, hs, hf, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4Retry_routing e cache bytes ds exactRx gen fallback srcIf rt :
    SameView routingView (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    routing a
  unfold Hoare at routing route
  have hc := (send4ClearSrc_routing cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_routing pid).wp (fun t => t = s)
  have hd := fun rt => (send4RouteDone_routing e cache bytes ds exactRx gen fallback rt).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4RetrySource, hc, hr, hd, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4Miss_routing e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView routingView (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    routing a
  unfold Hoare at routing route
  have hc := (send4ClearSrc_routing cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_routing pid).wp (fun t => t = s)
  have hn := fun srcIf rt => (send4Retry_routing e cache bytes ds exactRx gen fallback srcIf rt).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4MissSource, hc, hr, hn, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4AfterCache_routing e cache bytes ds exactRx gen saddr srcIf route :
    SameView routingView (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  apply SameView.of_wp
  intro s
  have hm := (send4Miss_routing e cache bytes ds exactRx gen route saddr srcIf).wp (fun t => t = s)
  have hf := (send4Finish_routing e bytes ds exactRx route).wp (fun t => t = s)
  mvcgen [send4AfterCacheSource, hm, hf, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send4_routing e cache bytes ds exactRx : SameView routingView (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    routing a
  unfold Hoare at routing route
  have hg := fun pid gen => (dstCacheGet_routing pid gen).wp (fun t => t = s)
  have ha := fun gen src srcIf route => (send4AfterCache_routing e cache bytes ds exactRx gen src srcIf route).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4Source, hg, ha, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem send6_routing e cache bytes ds exactRx : SameView routingView (send6 e cache bytes ds exactRx) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    routing a
  unfold Hoare at routing route
  have hg := fun pid gen => (dstCacheGet_routing pid gen).wp (fun t => t = s)
  have hp := fun pid => routing_getPeer (fun t => t = s) pid
  have hs := fun pid p => routing_setPeer (fun t => t = s) pid p
  have hr := fun pid => (dstCacheReset_routing pid).wp (fun t => t = s)
  have hc := fun pid src gen dev => (dstCacheSet_routing pid src gen dev).wp (fun t => t = s)
  have ht := fun r => (tunnelXmit_routing e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send6, hg, hp, hs, hr, hc, ht, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]

  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

end Leanux.Proofs.WG.AllowedIps
