import Leanux.Proofs.WG.Progress.Scheduler

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def probeAccepted (a : Activation) (w : World) : Bool :=
  match (Activation.run a).run w with
  | .ok _ => true
  | .error _ => false

theorem consistent_result (a : Activation) (initial final : World) (result : Bool)
    (run : (Activation.consistent a).run initial = .ok (result, final)) :
    final = initial ∧ result = probeAccepted a initial := by
  rw [consistent_exact] at run
  unfold probeAccepted
  cases ha : (Activation.run a).run initial with
  | ok out => simpa [ha, probeResult, eq_comm, and_comm] using run
  | error err => cases err <;> simp_all [probeResult, eq_comm]

theorem filterAux_consistent_result (candidates acc : List Activation) (initial final : World)
    (result : List Activation)
    (run : (List.filterAuxM Activation.consistent candidates acc).run initial = .ok (result, final)) :
    final = initial ∧ result = (candidates.filter (probeAccepted · initial)).reverse ++ acc := by
  induction candidates generalizing initial final result acc with
  | nil =>
    change Except.ok (acc, initial) = Except.ok (result, final) at run
    simpa [eq_comm, and_comm] using run
  | cons a rest ih =>
    simp only [List.filterAuxM, StateT.run_bind] at run
    cases hp : (Activation.consistent a).run initial with
    | error err => rw [hp] at run; cases run
    | ok pair =>
      obtain ⟨accepted, afterProbe⟩ := pair
      obtain ⟨same, value⟩ := consistent_result a initial afterProbe accepted hp
      subst afterProbe
      rw [hp] at run
      have effect := ih (cond accepted (a :: acc) acc) initial final result run
      cases accepted <;> simp_all [List.reverse_cons, List.append_assoc]

theorem filter_consistent_result (candidates : List Activation) (initial final : World)
    (result : List Activation)
    (run : (candidates.filterM Activation.consistent).run initial = .ok (result, final)) :
    final = initial ∧ result = candidates.filter (probeAccepted · initial) := by
  simp only [List.filterM, StateT.run_bind] at run
  cases hf : (List.filterAuxM Activation.consistent candidates []).run initial with
  | error err => rw [hf] at run; cases run
  | ok pair =>
    obtain ⟨reversed, afterProbe⟩ := pair
    obtain ⟨same, values⟩ := filterAux_consistent_result candidates [] initial afterProbe reversed hf
    subst afterProbe
    rw [hf] at run
    change Except.ok (reversed.reverse, initial) = Except.ok (result, final) at run
    obtain ⟨rfl, rfl⟩ := Except.ok.inj run
    exact ⟨rfl, by simp [values]⟩

end Leanux.Proofs.WG.Progress
