import Leanux.Proofs.WG.RetirementSecurity.TxWorkTimerFrames

/-! Native completion frames for the pending TX actor queue. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

private theorem dstCacheReset_work (pid : PeerId) : SameView queued (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' tx_work_step initial

private theorem dstCacheGet_work (pid : PeerId) (gen : Nat) : SameView queued (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' tx_work_step initial

private theorem dstCacheSet_work (pid : PeerId) (src gen dev : Nat) : SameView queued (dstCacheSet pid src gen dev) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold dstCacheSet
  repeat' tx_work_step initial



private theorem tunnelXmit_work (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView queued ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (store (Queues.loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (store (socketPort_sameStore _)).wp (fun s => s = initial))
    | tx_work_step initial

private theorem send4ClearSrc_work cache : SameView queued (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => queued w = initial) _
  repeat' first
    | tx_work_step initial

private theorem send4Finish_work e bytes ds exactRx route : SameView queued (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => queued w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_work _ _ _ _ _).wp (fun t => t = initial))
    | tx_work_step initial

private theorem send4RouteDone_work e cache bytes ds exactRx gen fallback rt :
    SameView queued (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => queued w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_work _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_work _ _ _ _ _).wp (fun t => t = initial))
    | tx_work_step initial

private theorem send4Retry_work e cache bytes ds exactRx gen fallback srcIf rt :
    SameView queued (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => queued w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_work _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_work _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_work _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | tx_work_step initial

private theorem send4Miss_work e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView queued (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => queued w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_work _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_work _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_work _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | tx_work_step initial

private theorem send4AfterCache_work e cache bytes ds exactRx gen saddr srcIf route :
    SameView queued (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => queued w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_work _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_work _ _ _ _ _).wp (fun t => t = initial))
    | tx_work_step initial

private theorem send4_work e cache bytes ds exactRx : SameView queued (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => queued w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_work _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_work _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | tx_work_step initial

private theorem send6_work (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView queued (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_work _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_work _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_work _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_work _ _ _ _ _).wp (fun s => s = initial))
    | tx_work_step initial

theorem sendSkbToPeer_work (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView queued (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4_work _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_work _ _ _ _ _).wp (fun s => s = initial))
    | tx_work_step initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
