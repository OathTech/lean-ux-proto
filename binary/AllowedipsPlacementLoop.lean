import AllowedipsPlacementSourceStep
import SequentialForIn

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG

/-- The composition obligation is isolated from physical instruction work.
The supplied step theorem must establish R on every accepted source iteration;
this lemma then executes the whole actual source loop, including early exits.
It is not a physical placement theorem until that step premise is discharged. -/
theorem compose_loop [Labels] (fetch : Int64 → Option Decoded)
    (root : Option NodeId) (key cidr bits : Nat)
    (R : Acc → AipStore → Ambient → MachineState → Prop)
    (step : ∀ acc store ambient next nextStore nextAmbient machine,
      ((iteration key cidr bits acc).run store).run ambient=.ok ((next,nextStore),nextAmbient) →
      acc.1=none → R acc store ambient machine →
      Eventually (instructionStep fetch)
        (R (match next with | .done a => a | .yield a => a) nextStore nextAmbient) machine)
    (store finalStore : AipStore) (ambient finalAmbient : Ambient)
    (result : Option NodeId × Bool) (machine : MachineState)
    (accepted : ((WG.nodePlacement root key cidr bits).run store).run ambient =
      .ok ((result,finalStore),finalAmbient))
    (initial : R (none,root,none) store ambient machine) :
    Eventually (instructionStep fetch) (fun t =>
      ∃ acc, acc.1=some result ∧ R acc finalStore finalAmbient t) machine := by
  rw [←run_eq_source] at accepted
  unfold run at accepted
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at accepted
  simp only [StateT.run_bind] at accepted
  let body := fun (_ : Nat) => iteration key cidr bits
  let items := List.range' 0 130
  change (do
    let ((acc,entries),state) ← ((forIn items (none,root,none) body).run store).run ambient
    ((match acc.1 with
      | some result => pure result
      | none => invariant "node_placement deeper than MAX_ALLOWEDIPS_DEPTH" : AipM (Option NodeId × Bool)).run entries).run state) = _ at accepted
  cases first : ((forIn items (none,root,none) body).run store).run ambient with
  | error error => simp only [first] at accepted; cases accepted
  | ok out =>
    rcases out with ⟨⟨acc,entries⟩,state⟩
    simp only [first] at accepted
    dsimp only [Bind.bind,Except.bind] at accepted
    cases resultEq : acc.1 with
    | none => rw [resultEq] at accepted; cases accepted
    | some answer =>
      rw [resultEq] at accepted
      change Except.ok ((answer,entries),state)=.ok ((result,finalStore),finalAmbient) at accepted
      cases accepted
      have loop := Sequential.forIn_execution fetch body R (fun acc => acc.1=none)
        (by intro _ acc store ambient next nextStore nextAmbient accepted
            exact yield_open (iteration_accepted accepted).1)
        (by intro _ acc store ambient next nextStore nextAmbient machine accepted openLoop related
            cases next <;> exact step acc store ambient _ nextStore nextAmbient machine accepted openLoop related) items _ _ _ _ _ _ machine first rfl initial
      apply eventually_weaken (instructionStep fetch) _ _ _ _ loop
      intro t related
      exact ⟨acc,resultEq,related⟩

#print axioms compose_loop
end Binary.Pair.Allowedips.Placement
