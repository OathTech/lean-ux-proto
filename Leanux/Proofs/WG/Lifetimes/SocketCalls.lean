import Leanux.Proofs.WG.Lifetimes.SocketSend

/-! Named complete calls in the cache, endpoint and socket transmission family.
Results are retained; per-call safety composes through the shared bind rules.
IPv4 send, socket setup/reinitialization and the outer scheduler remain separate
callers. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

inductive SocketCall where
  | reset (pid : PeerId)
  | resetNow (pid : PeerId)
  | clear (pid : PeerId)
  | endpoint (pid : PeerId) (e : Endpoint)
  | cacheGet (pid : PeerId) (gen : Nat)
  | cacheSet (pid : PeerId) (src gen dev : Nat)
  | softirq
  | loopback (sites : List HiddenSite) (raised : Bool)
  | tunnel (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool)
  | send6 (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool)

namespace SocketCall

def Result : SocketCall → Type
  | .cacheGet _ _ => Option DstSlot
  | .send6 .. => Int
  | _ => Unit

def original (call : SocketCall) : M call.Result := match call with
  | .reset pid => dstCacheReset pid
  | .resetNow pid => dstCacheResetNow pid
  | .clear pid => clearPeerEndpointSrc pid
  | .endpoint pid e => setPeerEndpoint pid e
  | .cacheGet pid gen => dstCacheGet pid gen
  | .cacheSet pid src gen dev => dstCacheSet pid src gen dev
  | .softirq => loopbackSoftirq
  | .loopback sites raised => loopbackSend sites raised
  | .tunnel e bytes ds r exactRx => (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
  | .send6 e cache bytes ds exactRx => WG.send6 e cache bytes ds exactRx

def observed (call : SocketCall) : MixedM call.Result := match call with
  | .reset pid => dstCacheResetMixed pid
  | .resetNow pid => dstCacheResetNowPrefix pid
  | .clear pid => clearPeerEndpointSrcPrefix pid
  | .endpoint pid e => setPeerEndpointPrefix pid e
  | .cacheGet pid gen => dstCacheGetPrefix pid gen
  | .cacheSet pid src gen dev => dstCacheSetPrefix pid src gen dev
  | .softirq => loopbackSoftirqPrefix
  | .loopback sites raised => loopbackSendPrefix sites raised
  | .tunnel e bytes ds r exactRx => tunnelXmitPrefix e bytes ds r exactRx
  | .send6 e cache bytes ds exactRx => send6Prefix e cache bytes ds exactRx

theorem erases (call : SocketCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | reset pid => exact dstCacheResetMixed_erases pid
  | resetNow pid => exact dstCacheResetNowPrefix_erases pid
  | clear pid => exact clearPeerEndpointSrcPrefix_erases pid
  | endpoint pid e => exact setPeerEndpointPrefix_erases pid e
  | cacheGet pid gen => exact dstCacheGetPrefix_erases pid gen
  | cacheSet pid src gen dev => exact dstCacheSetPrefix_erases pid src gen dev
  | softirq => exact loopbackSoftirqPrefix_erases
  | loopback sites raised => exact loopbackSendPrefix_erases sites raised
  | tunnel e bytes ds r exactRx => exact tunnelXmitPrefix_erases e bytes ds r exactRx
  | send6 e cache bytes ds exactRx => exact send6Prefix_erases e cache bytes ds exactRx

theorem spec (c : AmbientContracts I) (sc : SocketContracts I) (P : IdentityView → Prop)
    (call : SocketCall) : AmbientSpec I P call.observed (fun _ => P) := by
  cases call with
  | reset pid => exact dstCacheResetMixed_spec c P pid
  | resetNow pid => exact dstCacheResetNowPrefix_spec c P pid
  | clear pid => exact clearPeerEndpointSrcPrefix_spec c P pid
  | endpoint pid e => exact setPeerEndpointPrefix_spec c P pid e
  | cacheGet pid gen => exact dstCacheGetPrefix_spec c P pid gen
  | cacheSet pid src gen dev => exact dstCacheSetPrefix_spec c P pid src gen dev
  | softirq => exact loopbackSoftirqPrefix_spec c P
  | loopback sites raised => exact loopbackSendPrefix_spec c P sites raised
  | tunnel e bytes ds r exactRx => exact tunnelXmitPrefix_spec c sc P e bytes ds r exactRx
  | send6 e cache bytes ds exactRx => exact send6Prefix_spec c sc P e cache bytes ds exactRx

theorem allocation (call : SocketCall) : PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  AmbientContracts.drop (call.spec allocationAmbient allocationSocket (fun _ => True))

end SocketCall

/-- A cache miss reads its peer before requesting the refresh clock. This
conditional equation uses original getter/clock executions, not log premises. -/
theorem dstCacheGetPrefix_clock_failure (pid gen : Nat) (w : World) (p : Peer)
    (h : List LifetimeEvent) (e : Stop)
    (ha : w.armRecords = true) (hc : w.dstCacheRecords = true)
    (hp : (getPeer pid).run w = .ok (p, w)) (hs : p.dstCache.slot = none)
    (hf : (hiddenJiffies .dstCacheRefreshTs).run w = .error e) :
    runPrefix (dstCacheGetPrefix pid gen) w h =
      (.error e, h ++ [.peer (.read pid p.internalId)]) := by
  simp [dstCacheGetPrefix, runPrefix_bind, getPeerMixed_run, hp, hs, ha, hc, hf]

end Leanux.Proofs.WG.Lifetimes
