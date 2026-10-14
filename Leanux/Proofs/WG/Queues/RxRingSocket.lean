import Leanux.Proofs.WG.Queues.RxRingEncrypt

/-! Concrete socket sends retain the full decrypt-ring cell, including
loopback sections and ordinary route errors. The original socket-port Stops
remain in scope, but a Stop has no returned World or cell-frame conclusion. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem dstCacheGet_cell (pid : PeerId) (gen : Nat) : SameView cell (dstCacheGet pid gen) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have ht := fun site => (kernel (hiddenJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [dstCacheGet, hp, hs, ht, branch, branchCmp]

theorem dstCacheSet_cell (pid : PeerId) (src gen dev : Nat) : SameView cell (dstCacheSet pid src gen dev) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have ht := fun site => (kernel (hiddenJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [dstCacheSet, hp, hs, ht, branch]

theorem tunnelXmit_cell (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView cell ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  apply SameView.of_wp
  intro s
  have hl := fun sites force => (kernel (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites force)).wp (fun t => t = s)
  have hc := fun sites => (kernel (skipCut_sameKernel sites)).wp (fun t => t = s)
  have hp := fun fam => (kernel (socketPort_sameKernel fam)).wp (fun t => t = s)
  mvcgen [tunnelXmitSource, hl, hc, hp, modifyDev, modifyK, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell, Option.map_map, Function.comp_def]

theorem send4ClearSrc_cell cache : SameView cell (send4ClearSrcSource cache) := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  mvcgen [send4ClearSrcSource, hp, hs]

theorem send4Finish_cell e bytes ds exactRx route : SameView cell (send4FinishSource e bytes ds exactRx route) := by
  apply SameView.of_wp
  intro s
  have ht := fun r => (tunnelXmit_cell e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [send4FinishSource, ht, invariant]

theorem send4RouteDone_cell e cache bytes ds exactRx gen fallback rt :
    SameView cell (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  apply SameView.of_wp
  intro s
  have hs := fun pid src gen dev => (dstCacheSet_cell pid src gen dev).wp (fun t => t = s)
  have hf := fun r => (send4Finish_cell e bytes ds exactRx r).wp (fun t => t = s)
  mvcgen [send4RouteDoneSource, hs, hf, branch]

theorem send4Retry_cell e cache bytes ds exactRx gen fallback srcIf rt :
    SameView cell (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  apply SameView.of_wp
  intro s
  have hc := (send4ClearSrc_cell cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_cell pid).wp (fun t => t = s)
  have hl := fun fam src dst => (kernel (routeLookup_sameKernel fam src dst)).wp (fun t => t = s)
  have hd := fun rt => (send4RouteDone_cell e cache bytes ds exactRx gen fallback rt).wp (fun t => t = s)
  mvcgen [send4RetrySource, hc, hr, hl, hd, branch]

theorem send4Miss_cell e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView cell (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  apply SameView.of_wp
  intro s
  have hc := (send4ClearSrc_cell cache).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_cell pid).wp (fun t => t = s)
  have hl := fun fam src dst => (kernel (routeLookup_sameKernel fam src dst)).wp (fun t => t = s)
  have hn := fun srcIf rt => (send4Retry_cell e cache bytes ds exactRx gen fallback srcIf rt).wp (fun t => t = s)
  mvcgen [send4MissSource, hc, hr, hl, hn, branch]

theorem send4AfterCache_cell e cache bytes ds exactRx gen saddr srcIf route :
    SameView cell (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  apply SameView.of_wp
  intro s
  have hm := (send4Miss_cell e cache bytes ds exactRx gen route saddr srcIf).wp (fun t => t = s)
  have hf := (send4Finish_cell e bytes ds exactRx route).wp (fun t => t = s)
  mvcgen [send4AfterCacheSource, hm, hf, branch]

theorem send4_cell e cache bytes ds exactRx : SameView cell (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  apply SameView.of_wp
  intro s
  have hg := fun pid gen => (dstCacheGet_cell pid gen).wp (fun t => t = s)
  have ha := fun gen src srcIf route => (send4AfterCache_cell e cache bytes ds exactRx gen src srcIf route).wp (fun t => t = s)
  mvcgen [send4Source, hg, ha, getDev, getK, branch, invariant]

theorem send6_cell e cache bytes ds exactRx : SameView cell (send6 e cache bytes ds exactRx) := by
  apply SameView.of_wp
  intro s
  have hg := fun pid gen => (dstCacheGet_cell pid gen).wp (fun t => t = s)
  have hp := fun pid => (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun pid p => (setPeer_frame pid p).wp (fun t => t = s)
  have hr := fun pid => (dstCacheReset_cell pid).wp (fun t => t = s)
  have hl := fun fam src dst => (kernel (routeLookup_sameKernel fam src dst)).wp (fun t => t = s)
  have hc := fun pid src gen dev => (dstCacheSet_cell pid src gen dev).wp (fun t => t = s)
  have ht := fun r => (tunnelXmit_cell e bytes ds r exactRx).wp (fun t => t = s)
  mvcgen [send6, hg, hp, hs, hr, hl, hc, ht, getDev, getK, branch, invariant]

end Leanux.Proofs.WG.Queues.RxRing
