import Leanux.Proofs.WG.RetirementSecurity.OwnershipSourceFrames

/-! The original IPv4/IPv6 socket paths retain the physical key-reference
projection while updating endpoint caches and transmission bookkeeping. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

private theorem dstCacheReset_ownership (pid : PeerId) : SameView ownershipPointView (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' ownership_source_step initial

private theorem dstCacheGet_ownership (pid : PeerId) (gen : Nat) : SameView ownershipPointView (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' ownership_source_step initial

private theorem dstCacheSet_ownership (pid : PeerId) (src gen dev : Nat) : SameView ownershipPointView (dstCacheSet pid src gen dev) := by
  intro initial
  unfold dstCacheSet
  apply hoare_bind _ _ (ownership_getPeer (fun s => s = initial) pid)
  intro p
  exact ownership_setPeer (fun s => s = initial) pid _



private theorem tunnelXmit_ownership (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView ownershipPointView ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (ownershipPoints_kernel _ (Queues.loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (ownershipPoints_kernel _ (socketPort_sameStore _)).wp (fun s => s = initial))
    | ownership_source_step initial

private theorem send4ClearSrc_ownership cache : SameView ownershipPointView (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => ownershipPointView w = initial) _
  repeat' first
    | ownership_source_step initial

private theorem send4Finish_ownership e bytes ds exactRx route : SameView ownershipPointView (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => ownershipPointView w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_ownership _ _ _ _ _).wp (fun t => t = initial))
    | ownership_source_step initial

private theorem send4RouteDone_ownership e cache bytes ds exactRx gen fallback rt :
    SameView ownershipPointView (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => ownershipPointView w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_ownership _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_ownership _ _ _ _ _).wp (fun t => t = initial))
    | ownership_source_step initial

private theorem send4Retry_ownership e cache bytes ds exactRx gen fallback srcIf rt :
    SameView ownershipPointView (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => ownershipPointView w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_ownership _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_ownership _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_ownership _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | ownership_source_step initial

private theorem send4Miss_ownership e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView ownershipPointView (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => ownershipPointView w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_ownership _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_ownership _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_ownership _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | ownership_source_step initial

private theorem send4AfterCache_ownership e cache bytes ds exactRx gen saddr srcIf route :
    SameView ownershipPointView (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => ownershipPointView w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_ownership _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_ownership _ _ _ _ _).wp (fun t => t = initial))
    | ownership_source_step initial

private theorem send4_ownership e cache bytes ds exactRx : SameView ownershipPointView (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => ownershipPointView w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_ownership _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_ownership _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | ownership_source_step initial

private theorem send6_ownership (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView ownershipPointView (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_ownership _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_ownership _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_ownership _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_ownership _ _ _ _ _).wp (fun s => s = initial))
    | ownership_source_step initial

theorem sendSkbToPeer_ownership (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView ownershipPointView (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4_ownership _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_ownership _ _ _ _ _).wp (fun s => s = initial))
    | ownership_source_step initial

end Leanux.Proofs.WG.RetirementSecurity
