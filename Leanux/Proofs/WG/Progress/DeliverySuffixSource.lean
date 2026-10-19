import Leanux.Proofs.WG.Progress.StackSuffixFrames
import Leanux.Proofs.WG.Progress.SocketPrimitiveSuffixSource
import Leanux.Proofs.WG.Progress.SchedulerRecordSource
import Leanux.Proofs.Framing.Tools

/-! Original fixture delivery and crypt-worker scheduling retain a supplied
record suffix on normal return. Actual routing reads, mailbox updates,
unsupported delivery branches and the scheduler remain unchanged. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem deliverSent_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.deliverSent := by
  have routing : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (getRouting : Leanux.M Net.Routing) := native_product records _ (native_getRouting records)
  have fail {α : Type} (why : String) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (unsupported why : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  unfold Env.deliverSent
  apply preserves_bind (stack_getWG_retains records)
  intro initial
  apply preserves_bind
  · apply list_view_spec (fun w : World=>w.ambient.hidden) (Tail records)
    intro dg accumulator
    apply preserves_bind routing
    intro route
    dsimp only
    split
    · exact preserves_bind (stack_modifyEnv_retains records _) (fun _=>preserves_pure _)
    · split
      · exact preserves_bind (stack_modifyEnv_retains records _) (fun _=>preserves_pure _)
      · exact preserves_bind (stack_modifyEnv_retains records _) (fun _=>preserves_pure _)
      · split
        · exact preserves_bind (fail _) (fun _=>preserves_pure _)
        · exact preserves_pure _
  intro _
  exact native_product records _ (native_modify records (fun g=>{g with sent:=[]}))

theorem runCryptWorkers_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.runCryptWorkers :=
  preserves_bind (schedule_retains records none) (fun _=>deliverSent_retains records)

end Leanux.Proofs.WG.Progress.RecordSuffix
