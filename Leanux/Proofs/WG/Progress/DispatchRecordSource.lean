import Leanux.Proofs.WG.Progress.SchedulerRecordFrames
import Leanux.Proofs.WG.Progress.ClearWorkerRecordSource
import Leanux.Proofs.WG.Progress.NapiSuffixConcreteSource
import Leanux.Proofs.WG.Progress.HandshakeWorkerRecordSource
import Leanux.Proofs.WG.Progress.TransmitRecordSource

/-! Concrete record effects of every actual activation and dispatch. The existing dispatch source factor keeps its original selection, section start and failures; normal true dispatch strictly consumes supplied records. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem dispatchPrefix_retains (records : List HiddenRecord) (worker : Worker) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (dispatchPrefix worker) := by
  have dev : Preserves (fun w : World=>Tail records w.ambient.hidden) (monadLift getDev : Leanux.M Device) :=
    native_product records getDev (native_getDev records)
  have work (f : Device→Device) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (monadLift (modifyDev f) : Leanux.M Unit) :=
    native_product records (modifyDev f) (native_modifyDev records f)
  unfold dispatchPrefix
  repeat' first
    | with_reducible exact dev
    | with_reducible exact work _
    | with_reducible exact pendingDevice_retains records _ _
    | with_reducible exact peekUnit_retains records _
    | with_reducible exact resolveUnit_retains records _ _ _
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem dispatch_record_effect_of_activation
    (activation : ∀ a records,Preserves (fun w : World=>Tail records w.ambient.hidden)
      (Activation.run a))
    (worker : Worker) (records : List HiddenRecord) :
    Hoare (Env.dispatch worker) (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧ (result=true→StrictTail records w.ambient.hidden)) := by
  rw [dispatch_source]
  apply hoare_bind _ _ (dispatchPrefix_retains records worker)
  intro selected
  cases selected with
  | none =>
    apply hoare_consequence (hoare_pure false (fun w : World=>Tail records w.ambient.hidden))
      (fun _ hi=>hi)
    intro value final post
    exact ⟨post.2,by intro yes; rw [post.1] at yes; contradiction⟩
  | some pid =>
    unfold dispatchAfterPrefix dispatchAfterPrefixWith
    apply hoare_bind _ _ (hidden_after_product_tail (.sectionStart worker) records)
    intro _
    apply hoare_bind _ _ (retain_strict (Activation.run {worker,pid}) (activation _) records)
    intro _
    apply hoare_consequence (hoare_pure true (fun w : World=>StrictTail records w.ambient.hidden))
      (fun _ hi=>hi)
    intro value final post
    exact ⟨strict_tail post.2,fun _=>post.2⟩

theorem activation_all_strict (a : Activation) (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>w.ambient.hidden=some records)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  cases hw : a.worker
  all_goals first
    | exact encryptActivation_strict a hw records
    | exact decryptActivation_strict a hw records
    | exact txActivation_strict a hw records
    | exact receive_activation_strict a hw records
    | skip
  all_goals
    apply activation_strict_of_iterations _ ?_ a hw
    intro current same remaining
    simp only [Activation.iter,same]
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run

theorem activation_retains (a : Activation) (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Activation.run a) :=
  retain_tail (fun w : World=>w.ambient.hidden) _ (fun remaining=>
    hoare_consequence (activation_all_strict a remaining) (fun _ hi=>hi)
      (fun _ _ hi=>strict_tail hi)) records

theorem dispatch_record_effect (worker : Worker) (records : List HiddenRecord) :
    Hoare (Env.dispatch worker) (fun w=>Tail records w.ambient.hidden)
      (fun result w=>Tail records w.ambient.hidden ∧ (result=true→StrictTail records w.ambient.hidden)) :=
  dispatch_record_effect_of_activation activation_retains worker records

theorem dispatch_retains (worker : Worker) (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.dispatch worker) :=
  hoare_consequence (dispatch_record_effect worker records) (fun _ hi=>hi) (fun _ _ hi=>hi.1)

theorem activation_after_tail_strict (a : Activation) (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w=>Tail records w.ambient.hidden)
      (fun _ w=>StrictTail records w.ambient.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  obtain ⟨middle,present,prior⟩:=pre
  exact strict_extend prior ((hoare_iff_run _ _ _).mp (activation_all_strict a middle)
    before value after present run)

end Leanux.Proofs.WG.Progress.RecordSuffix
