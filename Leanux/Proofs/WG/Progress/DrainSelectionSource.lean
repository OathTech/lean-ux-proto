import Leanux.Proofs.WG.Progress.DrainOperations
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Noise Std.Do

/-- Actual guarded resolver; Ambient-only execution retains the device. -/
theorem resolveUnit_selected (worker : Worker) (unit : Nat) (queue : List Nat)
    (d : Device) :
    ⦃fun g => ⌜g.dev = some d⌝⦄ (resolveUnit worker unit queue : WG.M Nat)
      ⦃⇓? pid g => ⌜g.dev = some d ∧ pid ∈ queue⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change ((AmbientM.resolveUnit worker unit queue).run ambient >>= fun (pid, next) =>
    Except.ok ((pid, g), next)) = .ok ((result, final), after) at run
  cases resolved : (AmbientM.resolveUnit worker unit queue).run ambient with
  | error e => rw [resolved] at run; cases run
  | ok out =>
    rcases out with ⟨pid, next⟩
    rw [resolved] at run
    cases run
    refine ⟨pre, ?_⟩
    simp only [AmbientM.resolveUnit, StateT.run_bind, StateT.run_get, pure_bind] at resolved
    split at resolved
    · rename_i found who peer entry
      split at resolved
      · cases resolved
      · rename_i member
        cases resolved
        simpa using member
    · cases resolved

theorem drainSelect_selected (d : Device) :
    Ensures drainSelect (fun g => g.dev = some d)
      (fun selected g => g.dev = some d ∧ DrainSelected d selected) := by
  let P : WGWorld → Prop := fun g => g.dev = some d
  have hpure (selected : DrainSelection) (valid : DrainSelected d selected) :
      Ensures (pure selected : WG.M DrainSelection) P
        (fun chosen g => P g ∧ DrainSelected d chosen) := by
    intro g ambient result final after pre run
    cases run
    exact ⟨pre, valid⟩
  have hresolve (worker : Worker) (unit : Nat) (queue : List Nat)
      (choose : PeerId → DrainSelection) (valid : ∀ pid ∈ queue, DrainSelected d (choose pid)) :
      Ensures (do return choose (← resolveUnit worker unit queue)) P
        (fun chosen g => P g ∧ DrainSelected d chosen) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (resolveUnit_selected worker unit queue d)) ?_
    intro pid g ambient result final after pre run
    cases run
    exact ⟨pre.1, valid pid pre.2⟩
  have hpeek (worker : Worker) : Ensures (peekUnit worker : WG.M (Option Nat)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.peekUnit worker) P)
  unfold drainSelect
  refine ensures_bind (Q := fun read g => g.dev = some d ∧ read = d) _ _ ?_ ?_
  · intro g ambient result final after pre run
    simp [getDev, pre] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨pre, rfl⟩
  · intro captured g ambient result final after pre run
    obtain ⟨pre, same⟩ := pre
    subst captured
    revert g ambient result final after
    change Ensures _ P (fun chosen g => P g ∧ DrainSelected d chosen)
    split
    · rename_i empty
      apply hpure .drained
      simpa [DrainSelected] using empty
    · refine ensures_bind _ _ (hpeek .sendWorker) ?_
      intro send
      cases send with
      | some unit => exact hresolve .sendWorker unit d.sendWorkQueue .send (fun _ member => member)
      | none =>
        refine ensures_bind _ _ (hpeek .clearPeerWorker) ?_
        intro clear
        cases clear with
        | some unit => exact hresolve .clearPeerWorker unit d.clearWorkQueue .clear (fun _ member => member)
        | none =>
          refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
          · intro g ambient value final after pre run
            cases run
            exact pre
          · intro observed
            by_cases recording : observed.hidden.isSome = true
            · simp only [recording, ite_true]
              intro g ambient value final after pre run
              cases run
            · simp only [recording]
              cases hs : d.sendWorkQueue.head? with
              | some pid => exact hpure (.send pid) (List.mem_of_head? hs)
              | none =>
                cases hc : d.clearWorkQueue.head? with
                | some pid => exact hpure (.clear pid) (List.mem_of_head? hc)
                | none =>
                  apply hpure .drained
                  simp only [DrainSelected]
                  exact ⟨List.head?_eq_none_iff.mp hs, List.head?_eq_none_iff.mp hc⟩
end Leanux.Proofs.WG.Progress
