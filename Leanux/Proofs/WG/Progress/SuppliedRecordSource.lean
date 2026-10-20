import Leanux.Proofs.WG.Progress.DeferredOuterSuffixSource

/-! Convert concrete normal record-suffix contracts to supplied-mode
preservation. This does not assert the missing whole-syscall contract. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing

theorem preserves_supplied_of_tail {σ α : Type}
    (read : σ → Option (List HiddenRecord)) (action : StateT σ (Except Stop) α)
    (keeps : ∀ records, Preserves (fun state => Tail records (read state)) action) :
    Preserves (fun state => (read state).isSome = true) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases present : read before with
  | none => simp only [present,Option.isSome_none,Bool.false_eq_true] at pre
  | some records =>
    have beforeTail : Tail records (read before) := by
      rw [present]
      exact tail_self records
    obtain ⟨rest,remaining,_⟩ := (hoare_iff_run _ _ _).mp (keeps records)
      before value after beforeTail run
    simp only [remaining,Option.isSome_some]

end Leanux.Proofs.WG.Progress.RecordSuffix
