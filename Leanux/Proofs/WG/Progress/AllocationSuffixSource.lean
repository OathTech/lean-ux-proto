import Leanux.Proofs.WG.Progress.RecordSuffixSource
import Leanux.Proofs.WG.Progress.AllocationProgressSource

/-! Normal-return suffix preservation through the original finite allocation source. Placeholder, unarmed and cut behavior stays as the original defines it. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing Leanux.Proofs.WG.Noise

theorem ambient_stop {α : Type} (P : Ambient → Prop) (e : Stop) :
    Preserves P (throw e : AmbientM α) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run

theorem allocationEval_retains (records : List HiddenRecord) (fuel k : Nat)
    (encounter : AmbientM Bool)
    (keep : Preserves (fun a => Tail records a.hidden) encounter) :
    Preserves (fun a => Tail records a.hidden) (allocationEval fuel encounter k) := by
  induction fuel generalizing k with
  | zero => exact preserves_pure _
  | succ fuel ih =>
    unfold allocationEval
    apply preserves_bind keep
    intro result
    cases result with
    | false => exact preserves_pure _
    | true => exact ih (k+1)

theorem allocation_record_retains (site : AllocSite) (records : List HiddenRecord) :
    Preserves (fun a => Tail records a.hidden)
      ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) site) := by
  rw [(allocation_encounter_sources site).1]
  apply preserves_bind (hoare_consequence (hidden_after_tail (.alloc site) records)
    (fun _ h=>h) (fun _ _ h=>strict_tail h))
  intro bytes
  split
  · exact preserves_pure true
  · exact preserves_pure false
  · exact ambient_stop _ _

theorem allocation_placeholder_retains (site : AllocSite) (records : List HiddenRecord) :
    Preserves (fun a => Tail records a.hidden)
      ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) site) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  rw [(allocation_encounter_sources site).2] at run
  simp only [StateT.run_bind,StateT.run_get,pure_bind] at run
  cases found : before.steerValues.findIdx? (·.1 == site.info.label) with
  | none =>
    simp only [found] at run
    split at run
    · cases run
    · cases run; exact pre
  | some k =>
    simp only [found] at run
    simp only [StateT.run_bind,StateT.run_set,pure_bind] at run
    cases choice : before.steerValues[k]!.2 with
    | none =>
      simp only [choice] at run
      cases run; exact pre
    | some bytes =>
      simp only [choice] at run
      split at run
      · cases run
      · cases run; exact pre

theorem hiddenAlloc_retains (site : AllocSite) (records : List HiddenRecord) :
    Preserves (fun a => Tail records a.hidden) (AmbientM.hiddenAlloc site) := by
  rw [hiddenAlloc_finite_source]
  unfold hiddenAllocFinite
  dsimp only
  cases count : site.info.count with
  | laxZero => exact preserves_pure true
  | unrecorded => exact preserves_pure true
  | cut => exact ambient_stop _ _
  | exact n =>
    apply preserves_bind (hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    intro entry
    split
    · exact preserves_pure true
    · apply preserves_bind (allocationEval_retains records n 0 _ ?_)
      · intro out; cases out.1 <;> exact preserves_pure _
      · split
        · exact allocation_placeholder_retains site records
        · exact allocation_record_retains site records

end Leanux.Proofs.WG.Progress.RecordSuffix
