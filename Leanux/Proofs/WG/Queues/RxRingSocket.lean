import Leanux.Proofs.WG.Queues.RxRingEncrypt
import Leanux.Proofs.WG.Lifetimes.SocketSend4

/-! Concrete socket sends retain the full decrypt-ring cell, including
loopback sections and ordinary route errors. The original socket-port Stops
remain in scope, but a Stop has no returned World or cell-frame conclusion. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem dstCacheGet_cell (pid : PeerId) (gen : Nat) : SameView nativeCell (dstCacheGet pid gen) := by
  apply SameView.of_wp
  intro s
  have hp := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  have ambient {α : Type} (a : AmbientM α) (P : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) P (fun _ => P) := hoare_liftAmbient a P
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, dstCacheGet, getAmbient, hiddenJiffies,
    hp, hs, ambient, branch, branchCmp]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem dstCacheSet_cell (pid : PeerId) (src gen dev : Nat) : SameView nativeCell (dstCacheSet pid src gen dev) := by
  apply SameView.of_wp
  intro s
  have hp := getPeer_cell_spec (fun t => t = s) pid
  have hs := fun p => setPeer_cell_spec (fun t => t = s) pid p
  mvcgen [dstCacheSet, hp, hs, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem tunnelXmit_cell (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView nativeCell ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  apply SameView.of_wp
  intro s
  have hl := fun sites force => (kernel (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites force)).wp (fun t => t = s)
  have hp := fun fam => (kernel (socketPort_sameStore fam)).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, tunnelXmitSource, hl, hp, ambient,
    modifyDev, skipCut, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [nativeCell, Option.map_map, Function.comp_def]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4ClearSrc_cell cache : SameView nativeCell (send4ClearSrcSource cache) := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => getPeer_cell_spec (fun t => t = s) pid
  have hs := fun pid p => setPeer_cell_spec (fun t => t = s) pid p
  mvcgen [send4ClearSrcSource, hp, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4Finish_cell e bytes ds exactRx route : SameView nativeCell (send4FinishSource e bytes ds exactRx route) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    routing a
  unfold Hoare at routing route
  have ht := fun r => (tunnelXmit_cell e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4FinishSource, ht, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4RouteDone_cell e cache bytes ds exactRx gen fallback rt :
    SameView nativeCell (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  apply SameView.of_wp
  intro s
  have hs := fun pid src gen dev => (dstCacheSet_cell pid src gen dev).wp (fun t => t = s)
  have hf := fun r => (send4Finish_cell e bytes ds exactRx r).wp (fun t => t = s)
  mvcgen [send4RouteDoneSource, hs, hf, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4Retry_cell e cache bytes ds exactRx gen fallback srcIf rt :
    SameView nativeCell (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    routing a
  unfold Hoare at routing route
  have hc := (send4ClearSrc_cell cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_cell pid).wp (fun t => t = s)
  have hd := fun rt => (send4RouteDone_cell e cache bytes ds exactRx gen fallback rt).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4RetrySource, hc, hr, hd, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4Miss_cell e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView nativeCell (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    routing a
  unfold Hoare at routing route
  have hc := (send4ClearSrc_cell cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_cell pid).wp (fun t => t = s)
  have hn := fun srcIf rt => (send4Retry_cell e cache bytes ds exactRx gen fallback srcIf rt).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4MissSource, hc, hr, hn, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4AfterCache_cell e cache bytes ds exactRx gen saddr srcIf route :
    SameView nativeCell (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  apply SameView.of_wp
  intro s
  have hm := (send4Miss_cell e cache bytes ds exactRx gen route saddr srcIf).wp (fun t => t = s)
  have hf := (send4Finish_cell e bytes ds exactRx route).wp (fun t => t = s)
  mvcgen [send4AfterCacheSource, hm, hf, branch, AmbientM.branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send4_cell e cache bytes ds exactRx : SameView nativeCell (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    routing a
  unfold Hoare at routing route
  have hg := fun pid gen => (dstCacheGet_cell pid gen).wp (fun t => t = s)
  have ha := fun gen src srcIf route => (send4AfterCache_cell e cache bytes ds exactRx gen src srcIf route).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send4Source, hg, ha, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption

theorem send6_cell e cache bytes ds exactRx : SameView nativeCell (send6 e cache bytes ds exactRx) := by
  apply SameView.of_wp
  intro s
  have routing {α : Type} (a : Net.M α) :
      Hoare (liftRouting a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    hoare_liftRouting a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) :=
    routing a
  unfold Hoare at routing route
  have hg := fun pid gen => (dstCacheGet_cell pid gen).wp (fun t => t = s)
  have hp := fun pid => getPeer_cell_spec (fun t => t = s) pid
  have hs := fun pid p => setPeer_cell_spec (fun t => t = s) pid p
  have hr := fun pid => (dstCacheReset_cell pid).wp (fun t => t = s)
  have hc := fun pid src gen dev => (dstCacheSet_cell pid src gen dev).wp (fun t => t = s)
  have ht := fun r => (tunnelXmit_cell e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [routing, route, getRouting, liftM, send6, hg, hp, hs, hr, hc, ht, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]

  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [nativeCell]
  all_goals try assumption


end Leanux.Proofs.WG.Queues.RxRing
