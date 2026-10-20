import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationReadFrames

/-! Frames for actual product read points, including the full allocation
companion. Trial results are values; they never substitute a committed world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

theorem Shape.frame (source : Shape action) : SameView World.wg action := by
  induction source with
  | pure value => exact SameView.pure _ _
  | read =>
      intro initial
      exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2)
  | ambient body => exact fun _ => productAmbient_spec body _ (fun _ _ h=>h)
  | wg source => exact sameView_liftWG World.wg (fun w=>w) _ source.frame (fun _ _ _ h=>h)
  | packet skb =>
      apply sameView_liftWG World.wg (fun w=>w) _ ?_ (fun _ _ _ h=>h)
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro w a value v b performed
      exact (Packets.getTxSkb_current _ _ _ _ _ _ performed).1
  | bind head tail ihHead ihTail => exact SameView.bind ihHead ihTail

theorem Point.world (point : Point source w v) : v.wg=w.wg := by
  induction point with
  | entry source => rfl
  | returned source performed => exact (ProjectedAction.iff_run _ _ _).mp source.frame _ _ _ performed
  | wg point => exact point.world
  | packet point => exact Iteration.Reads.packet_world point
  | left tail point ih => exact ih
  | right head tail leading point ih =>
      exact ih.trans ((ProjectedAction.iff_run _ _ _).mp head.frame _ _ _ leading)

theorem Point.carrier (point : Point source w v) (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h v := by
  change CompleteAllocated.Carrier [] [] h v.wg v.ambient
  rw [point.world]
  exact before

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked (liftPrefix action) := by
  apply PrefixEnsures.lift
  · exact CompleteProduct.carrier_safe
  · intro h w value v before performed
    exact (Point.returned source performed).carrier before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
