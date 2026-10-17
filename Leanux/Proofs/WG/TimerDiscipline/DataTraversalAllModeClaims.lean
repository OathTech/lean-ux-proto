import Leanux.Proofs.WG.TimerDiscipline.ReceiveTraversalAllModeSource
import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The actual encrypted-item completion invokes traversal before its packet
loop, even for an empty list. Ordered send observations and data-sent gating
are retained; the all-mode effect concerns this single immediate traversal. -/
theorem observedDataDone_all_modes (pid : PeerId) (items : List SkbId) :
    Campaign2.Product.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => DataDoneFacts pid items cut ∧
        TraversalAllModeEffect pid cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
  intro entry cut final pre run
  refine ⟨observedDataDone_facts pid items entry cut final pre run, ?_⟩
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  have prefixFacts : Noise.Product.Ensures (dataDonePrefix pid items) (fun _ => True)
      (fun cut _ => TraversalAllModeEffect pid
        cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
    unfold dataDonePrefix
    refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_all_modes pid) ?_
    intro traversal
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro pair
    obtain ⟨sent, observations⟩ := pair
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro selected
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro beforeSent
    cases selected with
    | false =>
      simp only [Bool.false_eq_true, ite_false, pure_bind]
      intro initial cut final facts run
      cases run
      exact facts.2
    | true =>
      simp only [ite_true, pure_bind]
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro dataHook initial cut final facts run
      cases run
      exact facts.2
  have carried : Noise.Product.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => TraversalAllModeEffect pid
        cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
    unfold observedDataDone
    refine Noise.Product.ensures_bind _ _ prefixFacts ?_
    intro cut
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored initial out final facts run
    cases run
    exact facts
  exact carried entry cut final pre run

/-- Raw consumeDataDone invocation: its actual endpoint/confirmation/keep-fresh
prefix precedes traversal, and the inner-packet validation/routing suffix follows.
No upstream authentication or packet acceptance is inferred. The original return,
receipt gating and both timer-cut observations are retained. -/
theorem observedRxDataTimers_all_modes (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Campaign2.Product.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => RxDataTimersFacts pid pkt result.1 ∧
        TraversalAllModeEffect pid result.1.traversal.before.toSnapshot result.1.traversal.after.toSnapshot) := by
  intro entry result final pre run
  refine ⟨observedRxDataTimers_facts pid pkt e entry result final pre run, ?_⟩
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  have prefixFacts : Noise.Product.Ensures (rxDataTimersObservedPrefix pid pkt e) (fun _ => True)
      (fun cut _ => TraversalAllModeEffect pid
        cut.traversal.before.toSnapshot cut.traversal.after.toSnapshot) := by
    unfold rxDataTimersObservedPrefix
    refine Noise.Product.ensures_bind _ _ (keep _ True) ?_
    intro ignored
    refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_all_modes pid) ?_
    intro traversal
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro keepalive
    cases keepalive with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro receipt initial cut final facts run
      cases run
      exact facts.2
    | true =>
      simp only [ite_true]
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro ignored initial cut final facts run
      cases run
      exact facts.2
  have carried : Noise.Product.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => TraversalAllModeEffect pid
        result.1.traversal.before.toSnapshot result.1.traversal.after.toSnapshot) := by
    unfold observedRxDataTimers
    refine Noise.Product.ensures_bind _ _ prefixFacts ?_
    intro cut
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro ignored initial out final facts run
    cases run
    exact facts
  exact carried entry result final pre run

end Leanux.Proofs.WG.TimerDiscipline
