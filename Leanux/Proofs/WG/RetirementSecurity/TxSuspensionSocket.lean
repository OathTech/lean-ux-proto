import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionRouting

/-! Original socket completion, including the nested loopback record section,
retains suspended TX actors. Route and endpoint mutations remain observable. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem cache_reset (pid : PeerId) : Keeps (dstCacheReset pid) := by
  suspension_source [dstCacheReset] using [ambient_get, jiffies, peer, set_peer]

theorem cache_get (pid gen : Nat) : Keeps (dstCacheGet pid gen) := by
  suspension_source [dstCacheGet] using [ambient_get, jiffies, peer, set_peer]

theorem cache_set (pid src gen dev : Nat) : Keeps (dstCacheSet pid src gen dev) := by
  suspension_source [dstCacheSet] using [peer, set_peer]

theorem loopback (sites : List HiddenSite) (raised : Bool) : Keeps (loopbackSend sites raised) := by
  suspension_source [loopbackSend,raiseLoopbackRx,loopbackSoftirq] using [cuts, invariant, unsupported, device, ambient_get, peek_site, hidden]

theorem port (family : Nat) : Keeps (socketPort family) := by
  suspension_source [socketPort] using [device, unsupported]

theorem tunnel_source (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    Keeps (tunnelXmitSource e bytes ds r exactRx) := by
  suspension_source [tunnelXmitSource] using [unsupported, loopback, cuts, modify_device, port]

theorem tunnel (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    Keeps ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  exact tunnel_source e bytes ds r exactRx

theorem send4_clear cache : Keeps (send4ClearSrcSource cache) := by
  suspension_source [send4ClearSrcSource] using [peer, set_peer]

theorem send4_finish e bytes ds exactRx route : Keeps (send4FinishSource e bytes ds exactRx route) := by
  suspension_source [send4FinishSource] using [invariant, routing_lift, socket_namespace, neighbour, tunnel]

theorem send4_done e cache bytes ds exactRx gen fallback rt : Keeps (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  suspension_source [send4RouteDoneSource] using [branch, cache_set, send4_finish]

theorem send4_retry e cache bytes ds exactRx gen fallback srcIf rt : Keeps (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  suspension_source [send4RetrySource] using [branch, send4_clear, cache_reset, routing_lift, socket_namespace, route, send4_done]

theorem send4_miss e cache bytes ds exactRx gen fallback saddr srcIf : Keeps (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  suspension_source [send4MissSource] using [routing_get, branch, send4_clear, cache_reset, routing_lift, socket_namespace, route, send4_retry]

theorem send4_after e cache bytes ds exactRx gen saddr srcIf route : Keeps (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  suspension_source [send4AfterCacheSource] using [branch, send4_miss, send4_finish]

theorem send4_source e cache bytes ds exactRx : Keeps (send4Source e cache bytes ds exactRx) := by
  suspension_source [send4Source] using [device, branch, routing_lift, socket_namespace, table, invariant, cache_get, send4_after]

theorem send4_call e cache bytes ds exactRx : Keeps (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  exact send4_source e cache bytes ds exactRx

theorem send6_call e cache bytes ds exactRx : Keeps (send6 e cache bytes ds exactRx) := by
  suspension_source [send6] using [device, branch, routing_get, routing_lift, routing_call, route, invariant, cache_get, peer, set_peer, cache_reset, cache_set, tunnel]

theorem send_packet (pid : PeerId) (bytes : List UInt8) (ds : Nat) : Keeps (sendSkbToPeer pid bytes ds) := by
  suspension_source [sendSkbToPeer] using [peer, branch, send4_call, send6_call, set_peer]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
