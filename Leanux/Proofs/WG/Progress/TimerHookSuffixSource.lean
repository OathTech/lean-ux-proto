import Leanux.Proofs.WG.Progress.TimerSuffixSource
import Leanux.Proofs.WG.Progress.ReceiveCompletionSuffixSource

/-! Concrete normal-return record-suffix contracts for the original timer hooks. Error paths are unchanged, and no successful-execution premise is supplied. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Noise

theorem timersAnySent_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersAnyAuthenticatedPacketSent pid) :=
  delTimer_retains records pid .sendKeepalive

theorem timersAnyReceived_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersAnyAuthenticatedPacketReceived pid) :=
  delTimer_retains records pid .newHandshake

theorem timersComplete_retains (records : List HiddenRecord) (pid : PeerId) (site : HiddenSite) :
    NativeKeeps records (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  repeat' first
    | (native_suffix_head delTimer; exact delTimer_retains records _ _)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head hidden; exact native_hidden records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem timersDerived_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersSessionDerived pid) := by
  unfold timersSessionDerived
  simp only [discard,map_const,Function.comp_def]
  exact native_map records _ _ (modPeerTimer_retains records _ pid _ _)

theorem timersTraversal_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersTraversal pid) := by
  unfold timersTraversal
  simp only [discard,map_const,Function.comp_def]
  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head branchCmp; exact native_branchCmp records _ _ _ _)
    | (native_suffix_head modPeerTimer; exact modPeerTimer_retains records _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem timersInitiated_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  repeat' first
    | (native_suffix_head callerJiffies; exact callerJiffies_retains records _)
    | (native_suffix_head jitterBelowRekeyTimeout; exact native_jitter records .retransmit)
    | (native_suffix_head modPeerTimerGuard; exact modPeerTimerGuard_retains records _)
    | (native_suffix_head armTimer; exact armTimer_retains records _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem timersDataSent_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersDataSent pid) := by
  unfold timersDataSent
  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | (native_suffix_head callerJiffies; exact callerJiffies_retains records _)
    | (native_suffix_head jitterBelowRekeyTimeout; exact native_jitter records .newHandshake)
    | (native_suffix_head modPeerTimerGuard; exact modPeerTimerGuard_retains records _)
    | (native_suffix_head armTimer; exact armTimer_retains records _ _ _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem timersDataReceived_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (timersDataReceived pid) :=
  Completion.data_retains records pid (modPeerTimer_retains records _ pid _ _)


end Leanux.Proofs.WG.Progress.RecordSuffix
