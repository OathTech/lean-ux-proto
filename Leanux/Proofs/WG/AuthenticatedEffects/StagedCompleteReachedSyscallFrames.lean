import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSyscallSource

/-! The original syscall resets and seccomp guard retain the stronger
native entry. The literal journal is unchanged by these native-only leaves. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SyscallSource
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal
open CompletePrefix CompletePrefix.Runner.Delete

theorem enter_checked (call : Syscall) : Keeps (enter call) := by
  unfold enter
  apply Ensures.bind (Q:=fun _=>NativeEntry)
  · apply edit; intro w; rfl
  intro _
  apply Ensures.bind (Q:=fun _=>NativeEntry)
  · change Keeps (liftPrefix (modify _ : Leanux.M Unit))
    apply edit; intro w; rfl
  intro _
  apply Ensures.bind (Q:=fun _=>NativeEntry)
  · change Keeps (liftPrefix (modify _ : Leanux.M Unit))
    apply edit; intro w; rfl
  intro _
  split
  · exact seccomp _
  · apply Ensures.bind current_read
    intro task
    apply PrefixEnsures.ite
    · intro _; exact ambient (AmbientM.unsupported _)
    · intro _; exact Ensures.pure () (fun _ _ before=>before)

theorem enter_history (call : Syscall) (w : World) (h : List Event) :
    (runPrefix (enter call) w h).2=h := by
  have quiet : HistoryFrame some (enter call) := by
    unfold enter
    repeat' first
      | exact HistoryFrame.lift _ _
      | exact HistoryFrame.pure _ _
      | apply HistoryFrame.bind
      | (intro)
      | (split)
      | simp only [runPrefix_lift,runPrefix_pure]
  simpa only [List.filterMap_some] using quiet w h

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SyscallSource
