import Leanux.Proofs.WG.Queues.RxRingEncrypt
import Leanux.Proofs.WG.Lifetimes.SocketSend4
import Leanux.Proofs.WG.AllowedIps.RoutingSocketFrames

-- Elaborate the common socket source once before generating its ring frames.

/-! Concrete socket sends retain the full decrypt-ring cell, including
loopback sections and ordinary route errors. The original socket-port Stops
remain in scope, but a Stop has no returned World or cell-frame conclusion. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem dstCacheGet_cell (pid : PeerId) (gen : Nat) : SameView nativeCell (dstCacheGet pid gen) := by
  ring_cell_source [dstCacheGet] using []

theorem dstCacheSet_cell (pid : PeerId) (src gen dev : Nat) : SameView nativeCell (dstCacheSet pid src gen dev) := by
  ring_cell_source [dstCacheSet] using []

theorem tunnelXmit_cell (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView nativeCell ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  have loopback := fun sites raised => kernel (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites raised)
  have port := fun fam => kernel (socketPort_sameStore fam)
  ring_cell_source [tunnelXmitSource] using [loopback, port]

theorem send4ClearSrc_cell cache : SameView nativeCell (send4ClearSrcSource cache) := by
  ring_cell_source [send4ClearSrcSource] using []

theorem send4Finish_cell e bytes ds exactRx route : SameView nativeCell (send4FinishSource e bytes ds exactRx route) := by
  have routing {α : Type} (a : Net.M α) : SameView nativeCell (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => nativeCell w = initial) (fun _ _ h => h)
  ring_cell_source [send4FinishSource] using [routing, tunnelXmit_cell]

theorem send4RouteDone_cell e cache bytes ds exactRx gen fallback rt :
    SameView nativeCell (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  ring_cell_source [send4RouteDoneSource] using [dstCacheSet_cell, send4Finish_cell]

theorem send4Retry_cell e cache bytes ds exactRx gen fallback srcIf rt :
    SameView nativeCell (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  have routing {α : Type} (a : Net.M α) : SameView nativeCell (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => nativeCell w = initial) (fun _ _ h => h)
  ring_cell_source [send4RetrySource] using [routing, send4ClearSrc_cell, dstCacheReset_cell, send4RouteDone_cell]

theorem send4Miss_cell e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView nativeCell (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  have routing {α : Type} (a : Net.M α) : SameView nativeCell (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => nativeCell w = initial) (fun _ _ h => h)
  ring_cell_source [send4MissSource] using [routing, send4ClearSrc_cell, dstCacheReset_cell, send4Retry_cell]

theorem send4AfterCache_cell e cache bytes ds exactRx gen saddr srcIf route :
    SameView nativeCell (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  ring_cell_source [send4AfterCacheSource] using [send4Miss_cell, send4Finish_cell]

theorem send4_cell e cache bytes ds exactRx : SameView nativeCell (send4 e cache bytes ds exactRx) := by
  have routing {α : Type} (a : Net.M α) : SameView nativeCell (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => nativeCell w = initial) (fun _ _ h => h)
  rw [← send4Source_eq]
  ring_cell_source [send4Source] using [routing, dstCacheGet_cell, send4AfterCache_cell]

theorem send6_cell e cache bytes ds exactRx : SameView nativeCell (send6 e cache bytes ds exactRx) := by
  have routing {α : Type} (a : Net.M α) : SameView nativeCell (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => nativeCell w = initial) (fun _ _ h => h)
  ring_cell_source [send6] using [routing, dstCacheGet_cell, dstCacheReset_cell, dstCacheSet_cell, tunnelXmit_cell]

end Leanux.Proofs.WG.Queues.RxRing
