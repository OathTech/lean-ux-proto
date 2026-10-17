import Leanux.Proofs.WG.TimerDiscipline.ResponseTraversalSource
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem traversalCapture_entry (pid : PeerId) (before : Campaign2.Product.Snapshot) :
    Noise.Product.Ensures (dataDoneCapture (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal))
      (fun w => Campaign2.Product.snapshot w = before)
      (fun cut _ => cut.before = before ∧ DataDoneTraversalFacts pid cut) := by
  intro entry cut final pre run
  have facts := dataDoneTraversal_facts pid entry cut final trivial run
  refine ⟨?_, facts⟩
  change ((observed (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)).run entry >>= fun out =>
    Except.ok (DataDoneTimerCut.mk (Campaign2.Product.snapshot entry) out.1.1
      (Campaign2.Product.snapshot out.2), out.2)) = .ok (cut, final) at run
  cases h : (observed (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)).run entry with
  | error err => rw [h] at run; cases run
  | ok pair =>
    rw [h] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact pre

theorem responseTraversalPrefix_facts (pid : PeerId) :
    Noise.Product.Ensures (responseTraversalPrefix pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut) := by
  unfold responseTraversalPrefix
  refine Noise.Product.ensures_bind _ _ (outgoingResponseSessionPrefix_facts pid) ?_
  intro response
  refine Noise.Product.ensures_bind
    (Q := fun before w => Campaign2.Product.snapshot w = before ∧
      ∀ cut, response = some cut → ResponseSessionFacts pid cut.session ∧
        responseSessionEnd cut.session = before) _ _ ?_ ?_
  · intro entry before final facts run
    cases run
    exact ⟨rfl, facts⟩
  · intro before
    cases chosen : (response.map (·.session.begun)).getD false with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      intro entry cut final facts run
      cases run
      refine ⟨facts.2, ?_, ?_⟩
      · exact chosen.symm
      · intro hook impossible
        cases impossible
    | true =>
      simp only [↓reduceIte, pure_bind]
      refine Noise.Product.ensures_bind
        (Q := fun hook _ =>
          (∀ cut, response = some cut → ResponseSessionFacts pid cut.session ∧
            responseSessionEnd cut.session = before) ∧
          hook.before = before ∧ DataDoneTraversalFacts pid hook) _ _ ?_ ?_
      · intro entry hook final facts run
        exact ⟨facts.2, traversalCapture_entry pid before entry hook final facts.1 run⟩
      · intro hook entry cut final facts run
        cases run
        refine ⟨facts.1, ?_, ?_⟩
        · exact chosen.symm
        · intro other same
          cases same
          exact facts.2

theorem observedResponseTraversal_facts (pid : PeerId) :
    Campaign2.Product.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut) := by
  change Noise.Product.Ensures _ _ _
  unfold observedResponseTraversal
  refine Noise.Product.ensures_bind _ _ (responseTraversalPrefix_facts pid) ?_
  intro cut
  refine Noise.Product.ensures_bind (Q := fun _ _ => ResponseTraversalFacts pid cut) _ _ ?_ ?_
  · intro entry returned final facts run
    exact facts
  · intro ignored entry out final facts run
    cases run
    exact facts

end Leanux.Proofs.WG.TimerDiscipline
