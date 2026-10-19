import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCallbacks
import Leanux.Proofs.WG.Queues.RxRingSocket

/-! Native socket sends retain the handshake ring through route lookup,
loopback and ordinary route errors. Stops remain original source outcomes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem dstCacheGet_cell (pid : PeerId) (gen : Nat) : SameView view (dstCacheGet pid gen) := by
  handshake_cell_source [dstCacheGet] using []

theorem dstCacheSet_cell (pid : PeerId) (src gen dev : Nat) : SameView view (dstCacheSet pid src gen dev) := by
  handshake_cell_source [dstCacheSet] using []

theorem tunnelXmit_cell (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView view ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  have loopback := fun sites raised => kernel (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites raised)
  have port := fun fam => kernel (socketPort_sameStore fam)
  handshake_cell_source [tunnelXmitSource] using [loopback, port]

theorem send4ClearSrc_cell cache : SameView view (send4ClearSrcSource cache) := by
  handshake_cell_source [send4ClearSrcSource] using []

theorem send4Finish_cell e bytes ds exactRx route : SameView view (send4FinishSource e bytes ds exactRx route) := by
  have routing {α : Type} (a : Net.M α) : SameView view (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => view w = initial) (fun _ _ h => h)
  handshake_cell_source [send4FinishSource] using [routing, tunnelXmit_cell]

theorem send4RouteDone_cell e cache bytes ds exactRx gen fallback rt :
    SameView view (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  handshake_cell_source [send4RouteDoneSource] using [dstCacheSet_cell, send4Finish_cell]

theorem send4Retry_cell e cache bytes ds exactRx gen fallback srcIf rt :
    SameView view (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  have routing {α : Type} (a : Net.M α) : SameView view (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => view w = initial) (fun _ _ h => h)
  handshake_cell_source [send4RetrySource] using [routing, send4ClearSrc_cell, dstCacheReset_cell, send4RouteDone_cell]

theorem send4Miss_cell e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView view (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  have routing {α : Type} (a : Net.M α) : SameView view (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => view w = initial) (fun _ _ h => h)
  handshake_cell_source [send4MissSource] using [routing, send4ClearSrc_cell, dstCacheReset_cell, send4Retry_cell]

theorem send4AfterCache_cell e cache bytes ds exactRx gen saddr srcIf route :
    SameView view (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  handshake_cell_source [send4AfterCacheSource] using [send4Miss_cell, send4Finish_cell]

theorem send4_cell e cache bytes ds exactRx : SameView view (send4 e cache bytes ds exactRx) := by
  have routing {α : Type} (a : Net.M α) : SameView view (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => view w = initial) (fun _ _ h => h)
  rw [← send4Source_eq]
  handshake_cell_source [send4Source] using [routing, dstCacheGet_cell, send4AfterCache_cell]

theorem send6_cell e cache bytes ds exactRx : SameView view (send6 e cache bytes ds exactRx) := by
  have routing {α : Type} (a : Net.M α) : SameView view (liftRouting a) :=
    fun initial => hoare_liftRouting a (fun w => view w = initial) (fun _ _ h => h)
  handshake_cell_source [send6] using [routing, dstCacheGet_cell, dstCacheReset_cell, dstCacheSet_cell, tunnelXmit_cell]

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
