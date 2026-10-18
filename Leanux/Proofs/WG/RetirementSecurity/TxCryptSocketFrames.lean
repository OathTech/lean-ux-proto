import Leanux.Proofs.WG.RetirementSecurity.TxCryptTimerFrames

/-! Native routing and socket completion preserves the encryption ring and TX packet cells. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

private theorem dstCacheReset_cryptWire (pid : PeerId) : SameView txCryptWire (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' crypt_wire_step initial

private theorem dstCacheGet_cryptWire (pid : PeerId) (gen : Nat) : SameView txCryptWire (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' crypt_wire_step initial

private theorem dstCacheSet_cryptWire (pid : PeerId) (src gen dev : Nat) : SameView txCryptWire (dstCacheSet pid src gen dev) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold dstCacheSet
  repeat' crypt_wire_step initial



private theorem tunnelXmit_cryptWire (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView txCryptWire ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (cryptWire_store (Queues.loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (cryptWire_store (socketPort_sameStore _)).wp (fun s => s = initial))
    | crypt_wire_step initial

private theorem send4ClearSrc_cryptWire cache : SameView txCryptWire (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => txCryptWire w = initial) _
  repeat' first
    | crypt_wire_step initial

private theorem send4Finish_cryptWire e bytes ds exactRx route : SameView txCryptWire (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => txCryptWire w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_cryptWire _ _ _ _ _).wp (fun t => t = initial))
    | crypt_wire_step initial

private theorem send4RouteDone_cryptWire e cache bytes ds exactRx gen fallback rt :
    SameView txCryptWire (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => txCryptWire w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_cryptWire _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_cryptWire _ _ _ _ _).wp (fun t => t = initial))
    | crypt_wire_step initial

private theorem send4Retry_cryptWire e cache bytes ds exactRx gen fallback srcIf rt :
    SameView txCryptWire (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => txCryptWire w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_cryptWire _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_cryptWire _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_cryptWire _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | crypt_wire_step initial

private theorem send4Miss_cryptWire e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView txCryptWire (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => txCryptWire w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_cryptWire _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_cryptWire _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_cryptWire _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | crypt_wire_step initial

private theorem send4AfterCache_cryptWire e cache bytes ds exactRx gen saddr srcIf route :
    SameView txCryptWire (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => txCryptWire w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_cryptWire _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_cryptWire _ _ _ _ _).wp (fun t => t = initial))
    | crypt_wire_step initial

private theorem send4_cryptWire e cache bytes ds exactRx : SameView txCryptWire (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => txCryptWire w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_cryptWire _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_cryptWire _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | crypt_wire_step initial

private theorem send6_cryptWire (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView txCryptWire (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_cryptWire _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_cryptWire _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_cryptWire _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_cryptWire _ _ _ _ _).wp (fun s => s = initial))
    | crypt_wire_step initial

theorem sendSkbToPeer_cryptWire (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView txCryptWire (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4_cryptWire _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_cryptWire _ _ _ _ _).wp (fun s => s = initial))
    | crypt_wire_step initial

end Leanux.Proofs.WG.RetirementSecurity
