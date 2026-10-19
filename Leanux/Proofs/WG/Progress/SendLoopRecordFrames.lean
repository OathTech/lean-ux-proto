import Leanux.Proofs.WG.Progress.DeliverySuffixSource

/-! The original crypt-work refusal guard retains the actual hidden-record field. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem requireNoCryptWork_hidden (records : Option (List HiddenRecord)) :
    Hoare Env.requireNoCryptWork (fun w=>w.ambient.hidden=records)
      (fun _ w=>w.ambient.hidden=records) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  unfold Env.requireNoCryptWork at run
  rw [StateT.run_bind] at run
  change ((Except.ok (before.wg,before) : Except Stop _) >>= _) = _ at run
  dsimp only [Bind.bind,Except.bind] at run
  cases device : before.wg.dev with
  | none=>rw [device] at run; cases run; exact pre
  | some d=>
    rw [device] at run
    dsimp only at run
    by_cases crypt : (!d.encryptQueue.empty || !d.txWorkQueue.isEmpty)=true
    · simp only [crypt,ite_true] at run; cases run
    · simp only [crypt] at run; cases run; exact pre

theorem requireNoCryptWork_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.requireNoCryptWork := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  have same:=(hoare_iff_run _ _ _).mp (requireNoCryptWork_hidden before.ambient.hidden)
    before value after rfl run
  simpa only [same] using pre

end Leanux.Proofs.WG.Progress.RecordSuffix
