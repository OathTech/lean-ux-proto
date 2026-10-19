import Leanux.Proofs.WG.Progress.SocketPrimitiveSuffixSource
import Leanux.Proofs.WG.Lifetimes.SocketSend4
import Leanux.Proofs.WG.Lifetimes.HandshakeSend

/-! Suffix rules for exact original socket sends. The IPv4 proof consumes the
existing native source stages. The IPv6 proof unfolds its original body once.
Routing and loopback premises here name only the concrete source leaves. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Noise Lifetimes

theorem send4ClearSrc_retains (records : List HiddenRecord) (cache : Option PeerId) :
    NativeKeeps records (send4ClearSrcSource cache) := by
  unfold send4ClearSrcSource

  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

section
variable (records : List HiddenRecord)
variable (table : NativeKeeps records (liftRouting (Net.Fib.inSocketNs Net.Fib.getTable)))
variable (route4 : ∀ src dst,NativeKeeps records (liftRouting (Net.Fib.inSocketNs (Net.routeLookup 4 src dst))))
variable (neighbor : ∀ dev,NativeKeeps records (liftRouting (Net.Fib.inSocketNs (Net.neighbourClassify dev))))
variable (route6 : ∀ src dst,NativeKeeps records (liftRouting (Net.routeLookup 6 src dst)))
variable (loopback : ∀ sites raised,NativeKeeps records (loopbackSend sites raised))
include neighbor loopback in
theorem send4Finish_rule (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    NativeKeeps records (send4FinishSource e bytes ds exactRx route) := by
  unfold send4FinishSource
  simp (config := {zeta := false}) only [tunnelXmitSource_eq]

  repeat' first
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head liftRouting; exact neighbor _)
    | (native_suffix_head tunnelXmitSource; exact tunnelXmit_rule records loopback _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include neighbor loopback in
theorem send4RouteDone_rule (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route) (rt : Except Int Route) :
    NativeKeeps records (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDoneSource

  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head dstCacheSet; exact dstCacheSet_retains records _ _ _ _)
    | (native_suffix_head send4FinishSource; exact send4Finish_rule records neighbor loopback _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include route4 neighbor loopback in
theorem send4Retry_rule (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route) (srcIf : Nat) (rt : Except Int Route) :
    NativeKeeps records (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetrySource

  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head send4ClearSrcSource; exact send4ClearSrc_retains records _)
    | (native_suffix_head dstCacheReset; exact dstCacheReset_retains records _)
    | (native_suffix_head liftRouting; exact route4 _ _)
    | (native_suffix_head send4RouteDoneSource; exact send4RouteDone_rule records neighbor loopback _ _ _ _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include route4 neighbor loopback in
theorem send4Miss_rule (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr srcIf : Nat) :
    NativeKeeps records (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissSource

  repeat' first
    | (native_suffix_head getRouting; exact native_getRouting records)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head send4ClearSrcSource; exact send4ClearSrc_retains records _)
    | (native_suffix_head dstCacheReset; exact dstCacheReset_retains records _)
    | (native_suffix_head liftRouting; exact route4 _ _)
    | (native_suffix_head send4RetrySource; exact send4Retry_rule records route4 neighbor loopback _ _ _ _ _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include route4 neighbor loopback in
theorem send4AfterCache_rule (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen saddr srcIf : Nat) (route : Option Route) :
    NativeKeeps records (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  unfold send4AfterCacheSource

  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head send4MissSource; exact send4Miss_rule records route4 neighbor loopback _ _ _ _ _ _ _ _ _)
    | (native_suffix_head send4FinishSource; exact send4Finish_rule records neighbor loopback _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include table route4 neighbor loopback in
theorem send4_rule (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    NativeKeeps records (send4 e cache bytes ds exactRx) := by
  rw [←send4Source_eq]
  unfold send4Source

  repeat' first
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head liftRouting; exact table)
    | (native_suffix_head dstCacheGet; exact dstCacheGet_retains records _ _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head send4AfterCacheSource; exact send4AfterCache_rule records route4 neighbor loopback _ _ _ _ _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include route6 loopback in
theorem send6_rule (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    NativeKeeps records (send6 e cache bytes ds exactRx) := by
  unfold send6
  simp (config := {zeta := false}) only [tunnelXmitSource_eq]

  repeat' first
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head getRouting; exact native_getRouting records)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head dstCacheGet; exact dstCacheGet_retains records _ _)
    | (native_suffix_head dstCacheSet; exact dstCacheSet_retains records _ _ _ _)
    | (native_suffix_head dstCacheReset; exact dstCacheReset_retains records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head liftM; exact route6 _ _)
    | (native_suffix_head tunnelXmitSource; exact tunnelXmit_rule records loopback _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include table route4 neighbor route6 loopback in
theorem sendSkbToPeer_rule (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    NativeKeeps records (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer

  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head send4; exact send4_rule records table route4 neighbor loopback _ _ _ _ _)
    | (native_suffix_head send6; exact send6_rule records route6 loopback _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include table route4 neighbor route6 loopback in
theorem sendBufferToPeer_rule (pid : PeerId) (bytes : List UInt8) :
    NativeKeeps records (sendBufferToPeer pid bytes) := by
  rw [sendBufferToPeer_eq]
  simp only [Functor.discard,map_const,Function.comp_apply]

  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head hiddenAlloc; exact native_alloc records _)
    | (native_suffix_head sendSkbToPeer; exact sendSkbToPeer_rule records table route4 neighbor route6 loopback _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

include table route4 neighbor route6 loopback in
theorem sendBufferAsReplyToSkb_rule (src : SkbSource) (bytes : List UInt8) :
    NativeKeeps records (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb

  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head hiddenAlloc; exact native_alloc records _)
    | (native_suffix_head endpointFromSkb; exact endpointFromSkb_retains records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head send4; exact send4_rule records table route4 neighbor loopback _ _ _ _ _)
    | (native_suffix_head send6; exact send6_rule records route6 loopback _ _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step


end
end Leanux.Proofs.WG.Progress.RecordSuffix
