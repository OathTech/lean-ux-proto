import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalAllModeModel
import Leanux.Proofs.WG.TimerDiscipline.ArmingLifecycleClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- A normal actual hook derives residency rather than requiring it. Missing
peer/device and clock/wheel refusals remain original Stops. -/
theorem timersTraversal_resident_all_modes (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersTraversal pid) (fun s => s = entry)
      (fun _ final => TraversalAllModeEffect pid entry final) := by
  intro g ambient result final after pre run
  subst entry
  cases device : g.dev with
  | none =>
    simp [timersTraversal, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [timersTraversal, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      refine ⟨d,p,device,resident,?_⟩
      exact timersTraversal_effect pid d p resident (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl,device⟩ run

/-- Strengthen the existing capture without replacing its recorded clock
facts or inspecting a manufactured state. The operation still executes once. -/
theorem dataDoneTraversal_all_modes (pid : PeerId) :
    Noise.Product.Ensures (dataDoneCapture (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal))
      (fun _ => True) (fun cut _ => DataDoneTraversalFacts pid cut ∧
        TraversalAllModeEffect pid cut.before.toSnapshot cut.after.toSnapshot) := by
  intro initial cut final pre run
  refine ⟨dataDoneTraversal_facts pid initial cut final pre run, ?_⟩
  have contract (entry : Product.Snapshot) :
      Product.Ensures (observed (liftWG (timersTraversal pid))
        (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal))
        (fun s => s = entry)
        (fun _ after => TraversalAllModeEffect pid entry.toSnapshot after.toSnapshot) := by
    apply observed_effect
    intro before value after equal execution
    subst entry
    change (((timersTraversal pid).run before.wg).run before.ambient >>= _) = _ at execution
    cases native : ((timersTraversal pid).run before.wg).run before.ambient with
    | error stop => rw [native] at execution; cases execution
    | ok out =>
      obtain ⟨⟨result,current⟩,inputs⟩ := out
      rw [native] at execution
      cases execution
      exact timersTraversal_resident_all_modes pid (Campaign2.snapshot before.wg before.ambient)
        before.wg before.ambient _ _ _ rfl native
  have facts := dataDoneCapture_facts _ _ _ _ (contract cut.before)
    initial cut final pre run
  exact facts.2 rfl

/-- The original authenticated receive tail retains the same immediate hook
cut, even though peer release executes afterward. No final timer claim follows. -/
theorem observedReceiveTraversalCommon_all_modes (msg : List UInt8) (pid : PeerId) :
    Noise.Product.Ensures (observedReceiveTraversalCommon msg pid) (fun _ => True)
      (fun hook _ => DataDoneTraversalFacts pid hook ∧
        TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) := by
  unfold observedReceiveTraversalCommon
  refine Noise.Product.ensures_bind _ _ (fun _ _ _ h _ => h) ?_
  intro ignored
  refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_all_modes pid) ?_
  intro hook
  refine Noise.Product.ensures_bind (Q := fun _ _ => DataDoneTraversalFacts pid hook ∧
      TraversalAllModeEffect pid hook.before.toSnapshot hook.after.toSnapshot) _ _
    (fun _ _ _ h _ => h) ?_
  intro ignored initial out final facts run
  cases run
  exact facts

end Leanux.Proofs.WG.TimerDiscipline
