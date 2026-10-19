import Leanux.Proofs.WG.Progress.TimerSuffixSource
import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource

/-! Normal ambient record-suffix transport through the actual endpoint comparison, cache reset and setter. All failure branches remain the original operations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Noise

theorem endpointEq_retains (records : List HiddenRecord) (a : Endpoint) (b : Option Endpoint) :
    NativeKeeps records (endpointEq a b) := by
  unfold endpointEq
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head WG.andM; apply native_and records)
    | native_suffix_step

theorem dstCacheReset_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (dstCacheReset pid) := by
  unfold dstCacheReset
  repeat' first
    | (native_suffix_head getAmbient; exact native_getAmbient records)
    | (native_suffix_head get; exact native_get records)
    | (native_suffix_head hiddenJiffies; exact native_jiffies records _)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | native_suffix_step

theorem setPeerEndpoint_retains (records : List HiddenRecord) (pid : PeerId) (ep : Endpoint) :
    NativeKeeps records (setPeerEndpoint pid ep) := by
  unfold setPeerEndpoint requireNotPending
  repeat' first
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head endpointEq; exact endpointEq_retains records _ _)
    | (native_suffix_head dstCacheReset; exact dstCacheReset_retains records _)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | native_suffix_step

end Leanux.Proofs.WG.Progress.RecordSuffix
