import Leanux.Proofs.WG.Progress.TimerSuffixSource
import Leanux.Proofs.WG.Lifetimes.LoopbackAccess
/-! Concrete suffix transport through loopback NET_RX sections, including their original pending-poll refusals and exact start/stop record reads. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

theorem raiseLoopbackRx_retains (records : List HiddenRecord) :
    NativeKeeps records raiseLoopbackRx := by
  unfold raiseLoopbackRx
  repeat' first
    | (native_suffix_head get; exact native_get records)
    | (native_suffix_head modify; exact native_modify records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem loopbackFinish_retains (records : List HiddenRecord) :
    NativeKeeps records loopbackFinish := by
  unfold loopbackFinish
  repeat' first
    | (native_suffix_head modify; exact native_modify records _)
    | (native_suffix_head getAmbient; exact native_getAmbient records)
    | (native_suffix_head peekHiddenSite; exact native_peek records)
    | (native_suffix_head hidden; exact native_hidden records _)
    | (native_suffix_head skipCut; exact native_skipCut records _)
    | (native_suffix_head throw; exact native_stop records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem loopbackSoftirq_retains (records : List HiddenRecord) :
    NativeKeeps records loopbackSoftirq := by
  rw [loopbackSoftirq_source]
  repeat' first
    | (native_suffix_head get; exact native_get records)
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | (native_suffix_head loopbackFinish; exact loopbackFinish_retains records)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem loopbackSend_retains (records : List HiddenRecord)
    (sites : List HiddenSite) (raised : Bool) :
    NativeKeeps records (loopbackSend sites raised) := by
  unfold loopbackSend
  exact native_bind records _ _ (native_skipCut records sites) (fun _=>by
    split
    · exact native_bind records _ _ (raiseLoopbackRx_retains records)
        (fun _=>loopbackSoftirq_retains records)
    · exact native_pure records _)
end Leanux.Proofs.WG.Progress.RecordSuffix
