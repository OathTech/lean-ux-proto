import Leanux.Proofs.WG.Progress.SocketRulesSource
import Leanux.Proofs.WG.Progress.RoutingIPv4SuffixSource
import Leanux.Proofs.WG.Progress.LoopbackSuffixSource

/-! Concrete normal-result suffix transport through both original socket families
and their packet, handshake-buffer and cookie-reply callers. Every routing and
loopback leaf is instantiated; no worker-completion or termination claim is made. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Noise Lifetimes

theorem socketTable_retains (records : List HiddenRecord) :
    NativeKeeps records (liftRouting (Net.Fib.inSocketNs Net.Fib.getTable)) :=
  native_liftRouting records _ (net_inSocketNs records _ (net_getTable records))

theorem socketNeighbor_retains (records : List HiddenRecord) (dev : Nat) :
    NativeKeeps records (liftRouting (Net.Fib.inSocketNs (Net.neighbourClassify dev))) :=
  native_liftRouting records _ (net_inSocketNs records _ (net_neighbourClassify records dev))

theorem socketRoute6_retains (records : List HiddenRecord) (src dst : Nat) :
    NativeKeeps records (liftRouting (Net.routeLookup 6 src dst)) :=
  native_liftRouting records _ (net_routeLookup6 records src dst)

theorem tunnelXmit_retains (records : List HiddenRecord)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    NativeKeeps records ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit)
      e bytes ds r exactRx) :=
  tunnelXmit_rule records (loopbackSend_retains records) e bytes ds r exactRx

theorem send6_retains (records : List HiddenRecord)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    NativeKeeps records (send6 e cache bytes ds exactRx) :=
  send6_rule records (socketRoute6_retains records) (loopbackSend_retains records)
    e cache bytes ds exactRx

/-- IPv4-dependent socket sends require this exact original route-lookup leaf only.
This is a dependency-parametric source rule, not a closed whole-send progress result. -/
theorem send4_of_route4 (records : List HiddenRecord)
    (route4 : ∀ src dst,NativeKeeps records
      (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 src dst))))
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    NativeKeeps records (send4 e cache bytes ds exactRx) :=
  send4_rule records (socketTable_retains records) route4 (socketNeighbor_retains records)
    (loopbackSend_retains records) e cache bytes ds exactRx

theorem sendSkbToPeer_of_route4 (records : List HiddenRecord)
    (route4 : ∀ src dst,NativeKeeps records
      (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 src dst))))
    (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    NativeKeeps records (sendSkbToPeer pid bytes ds) :=
  sendSkbToPeer_rule records (socketTable_retains records) route4 (socketNeighbor_retains records)
    (socketRoute6_retains records) (loopbackSend_retains records) pid bytes ds

theorem sendBufferToPeer_of_route4 (records : List HiddenRecord)
    (route4 : ∀ src dst,NativeKeeps records
      (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 src dst))))
    (pid : PeerId) (bytes : List UInt8) :
    NativeKeeps records (sendBufferToPeer pid bytes) :=
  sendBufferToPeer_rule records (socketTable_retains records) route4 (socketNeighbor_retains records)
    (socketRoute6_retains records) (loopbackSend_retains records) pid bytes

theorem sendBufferAsReplyToSkb_of_route4 (records : List HiddenRecord)
    (route4 : ∀ src dst,NativeKeeps records
      (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 src dst))))
    (src : SkbSource) (bytes : List UInt8) :
    NativeKeeps records (sendBufferAsReplyToSkb src bytes) :=
  sendBufferAsReplyToSkb_rule records (socketTable_retains records) route4 (socketNeighbor_retains records)
    (socketRoute6_retains records) (loopbackSend_retains records) src bytes


theorem socketRoute4_retains (records : List HiddenRecord) (src dst : Nat) :
    NativeKeeps records (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 src dst))) :=
  native_liftRouting records _ (net_inSocketNs records _ (net_routeLookup4 records src dst))

theorem send4_retains (records : List HiddenRecord)
    (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    NativeKeeps records (send4 e cache bytes ds exactRx) :=
  send4_of_route4 records (socketRoute4_retains records) e cache bytes ds exactRx

theorem sendSkbToPeer_retains (records : List HiddenRecord)
    (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    NativeKeeps records (sendSkbToPeer pid bytes ds) :=
  sendSkbToPeer_of_route4 records (socketRoute4_retains records) pid bytes ds

theorem sendBufferToPeer_retains (records : List HiddenRecord)
    (pid : PeerId) (bytes : List UInt8) :
    NativeKeeps records (sendBufferToPeer pid bytes) :=
  sendBufferToPeer_of_route4 records (socketRoute4_retains records) pid bytes

theorem sendBufferAsReplyToSkb_retains (records : List HiddenRecord)
    (src : SkbSource) (bytes : List UInt8) :
    NativeKeeps records (sendBufferAsReplyToSkb src bytes) :=
  sendBufferAsReplyToSkb_of_route4 records (socketRoute4_retains records) src bytes

end Leanux.Proofs.WG.Progress.RecordSuffix
