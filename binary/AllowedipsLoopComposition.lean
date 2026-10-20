import AllowedipsSource
import History

namespace Binary.AllowedipsSource
open Leanux MirrorHistory

/-- Compose the actual bounded source loop through one invariant. The local
    premise is discharged by the instruction-region proof, never exported
    as a lookup hypothesis. In particular the source's fuel exhaustion is
    not treated as a successful binary return. -/
theorem loop_simulation [Labels] (fetch : Int64 → Option Decoded)
    (bits key : Nat)
    (Inv : Acc → List Point → World → Executed → Prop)
    (region : ∀ acc history world step points final machine,
      ((iteration bits key acc).run history).run world = .ok ((step,points),final) →
      Inv acc history world machine →
      Eventually (historyStep fetch)
        (Inv (match step with | .done a => a | .yield a => a) points final) machine)
    (fuel : Nat) (acc result : Acc) (history points : List Point)
    (world final : World) (machine : Executed)
    (accepted : ((loop bits key fuel acc).run history).run world =
      .ok ((result,points),final))
    (initial : Inv acc history world machine) :
    Eventually (historyStep fetch) (Inv result points final) machine := by
  induction fuel generalizing acc history world machine with
  | zero =>
    change Except.ok ((acc,history),world) = Except.ok ((result,points),final) at accepted
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj accepted)
    exact .done _ initial
  | succ fuel ih =>
    obtain ⟨step,middle,intermediate,first,rest⟩ :=
      loop_succ_accepted bits key fuel acc result history points world final accepted
    have body := region acc history world step middle intermediate machine first initial
    cases step with
    | done answer =>
      obtain ⟨rfl,rfl,rfl⟩ := rest
      exact body
    | yield next =>
      apply eventually_trans (historyStep fetch) _ _ _ body
      intro state invariant
      exact ih next middle intermediate state rest invariant

#print axioms loop_simulation
end Binary.AllowedipsSource
