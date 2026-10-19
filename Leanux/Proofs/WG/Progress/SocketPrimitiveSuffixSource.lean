import Leanux.Proofs.WG.Progress.EndpointSuffixSource
import Leanux.Proofs.WG.Lifetimes.SocketSend
/-! Concrete cache and port suffix leaves, and the exact tunnel source rule.
Only the actual loopback call is a premise of the tunnel rule; SocketSuffixSource
instantiates it with the original loopback proof. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Noise Lifetimes

theorem native_getRouting (records : List HiddenRecord) :
    NativeKeeps records (getRouting : WG.M Net.Routing) := fun _ => preserves_pure _

theorem socketPort_retains (records : List HiddenRecord) (family : Nat) :
    NativeKeeps records (socketPort family) := by
  unfold socketPort
  repeat' first
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | native_suffix_step

theorem dstCacheGet_retains (records : List HiddenRecord) (pid gen : Nat) :
    NativeKeeps records (dstCacheGet pid gen) := by
  unfold dstCacheGet
  repeat' first
    | (native_suffix_head getAmbient; exact native_getAmbient records)
    | (native_suffix_head get; exact native_get records)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head hiddenJiffies; exact native_jiffies records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem dstCacheSet_retains (records : List HiddenRecord) (pid src gen dev : Nat) :
    NativeKeeps records (dstCacheSet pid src gen dev) := by
  unfold dstCacheSet
  exact native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records pid _)

theorem tunnelXmit_rule (records : List HiddenRecord)
    (loopback : ∀ sites raised,NativeKeeps records (loopbackSend sites raised))
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    NativeKeeps records ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit)
      e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  unfold tunnelXmitSource
  repeat' first
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | (native_suffix_head loopbackSend; exact loopback _ _)
    | (native_suffix_head skipCut; exact native_skipCut records _)
    | (native_suffix_head modifyDev; exact native_modifyDev records _)
    | (native_suffix_head socketPort; exact socketPort_retains records _)
    | (native_suffix_head modify; exact native_modify records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step


end Leanux.Proofs.WG.Progress.RecordSuffix
