import Leanux.Proofs.WG.Progress.RecordSuffixSource
import Leanux.Proofs.WG.Progress.StackFrames

/-! Physical hidden-record frames for actual scheduler reads and copied consistency probes, plus strict-suffix predicate transport. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem hasWork_retains (records : List HiddenRecord) (a : Activation) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Activation.hasWork a) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  have same := hasWork_world a before before value after rfl run
  simpa only [same] using pre

theorem consistentFilter_retains (records : List HiddenRecord) (xs : List Activation) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (xs.filterM Activation.consistent) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  have same := (filter_consistent_result xs before after value run).1
  simpa only [same] using pre

theorem recordBudget_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (recordBudget : Leanux.M Nat) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run
  exact pre

theorem retain_strict {α : Type} (action : Leanux.M α)
    (keep : ∀ records,Preserves (fun w : World=>Tail records w.ambient.hidden) action)
    (records : List HiddenRecord) :
    Preserves (fun w : World=>StrictTail records w.ambient.hidden) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  obtain ⟨middle,stored,suffix,shorter⟩ := pre
  exact tail_after_strict suffix shorter ((hoare_iff_run _ _ _).mp (keep middle)
    before value after (stored ▸ tail_self middle) run)

end Leanux.Proofs.WG.Progress.RecordSuffix
