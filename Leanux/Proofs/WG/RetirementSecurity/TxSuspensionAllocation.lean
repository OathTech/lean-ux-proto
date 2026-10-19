import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionCompletion
import Leanux.Proofs.Framing.Allocation
import Init.Internal.Order.While

/-! Allocation outcomes consume their actual bounded encounter loop while
retaining suspended actors, including placeholder steering and failed draws. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def encounterLoop (encounter : AmbientM Bool) (limit start : Nat) : AmbientM (Option Bool × Nat) :=
  forIn ({} : Lean.Loop) (none,start) fun _ state=>
    if state.2 < limit then do
      let ok←encounter
      if !ok then Pure.pure (.done (some false,state.2))
      else Pure.pure (.yield (none,state.2+1))
    else Pure.pure (.done (none,state.2))

theorem encounter_loop (encounter : AmbientM Bool) (frame : SameView Ambient.suspended encounter)
    (limit start : Nat) : SameView Ambient.suspended (encounterLoop encounter limit start) := by
  induction remaining : limit-start generalizing start with
  | zero=>
    have ended : ¬start<limit := by omega
    unfold encounterLoop
    change SameView Ambient.suspended (Lean.Loop.forIn ({} : Lean.Loop) (none,start) _)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [ended,ite_false,pure_bind]
    exact SameView.pure _ _
  | succ remaining ih=>
    have pending : start<limit := by omega
    unfold encounterLoop
    change SameView Ambient.suspended (Lean.Loop.forIn ({} : Lean.Loop) (none,start) _)
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [pending,ite_true,bind_assoc]
    apply frame.bind
    intro ok
    cases ok
    · simp only [Bool.not_false,ite_true,pure_bind]
      exact SameView.pure _ _
    · simp only [Bool.not_true,Bool.false_eq_true,ite_false,pure_bind]
      exact ih (start+1) (by omega)

theorem record_outcome (site : AllocSite) : SameView Ambient.suspended (Allocation.recordOutcome site) := by
  unfold Allocation.recordOutcome
  apply (TxActorFrames.hidden (.alloc site)).bind
  intro bytes
  split
  · exact SameView.pure _ _
  · exact SameView.pure _ _
  · intro initial
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run

theorem placeholder_outcome (site : AllocSite) :
    SameView Ambient.suspended (Allocation.placeholderOutcome site) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  unfold Allocation.placeholderOutcome at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  repeat' first
    | (change Except.error _ = Except.ok _ at tail; cases tail)
    | split at tail
    | (rw [MaterialOrigin.bind_ok] at tail; obtain ⟨x,y,step,tail⟩:=tail; cases step)
    | (cases tail; rfl)

theorem allocation_outcome (site : AllocSite) : SameView Ambient.suspended (AmbientM.hiddenAlloc site) := by
  rw [←Allocation.allocationOutcome_eq]
  intro initial
  let P := fun w : Ambient=>w.suspended=initial
  have read : Preserves P (MonadState.get : AmbientM Ambient) :=
    hoare_consequence (hoare_get P) (fun _ h=>h) (fun _ _ h=>h.2)
  have stop {α : Type} (message : String) : Preserves P (Leanux.invariant message : AmbientM α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  have loop (encounter : AmbientM Bool) (limit start : Nat)
      (frame : SameView Ambient.suspended encounter) : Preserves P (encounterLoop encounter limit start) :=
    encounter_loop encounter frame limit start initial
  change Preserves P _
  unfold Allocation.allocationOutcome
  repeat' first
    | env_operation_fact read
    | env_operation_fact stop
    | (rx_retention_head ForIn.forIn
       change Preserves P (encounterLoop _ _ _)
       apply loop
       first | exact placeholder_outcome site | exact record_outcome site
             | (split <;> first | exact placeholder_outcome site | exact record_outcome site))
    | routing_tx_step

theorem allocation (site : AllocSite) : Keeps (hiddenAlloc site : StateT S AmbientM Bool) :=
  ambient (allocation_outcome site)

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
