import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointFramed

/-! Ordinary open prefixes retain the allocation companion needed by staging.
This auxiliary certificate is discharged for their literal source atoms; it
is not an incoming lifecycle or conservation hypothesis. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

def Strong : {α : Type} → {action : PrefixM Event α} → Shape action → Prop
  | _,_,.pure _ => True
  | _,_,.native (.quiet body _) => CompleteProduct.Checked (liftPrefix body)
  | _,_,.native _ => False
  | _,body,.child token => CompleteProduct.Checked body ∧ ∀ h w,CompleteProduct.Carrier h w → token.Entry h w
  | _,_,.bind head tail => Strong head ∧ ∀value,Strong (tail value)
  | _,_,.marked _ body => Strong body

theorem Strong.checked {shape : Shape action} (strong : Strong shape) : CompleteProduct.Checked action := by
  induction shape with
  | pure value => exact CompleteProduct.pure_checked value
  | native token => cases token <;> first | exact strong | exact False.elim strong
  | child => exact strong.1
  | bind head tail ihHead ihTail => exact CompleteProduct.bind_checked (ihHead strong.1) (fun x=>ihTail x (strong.2 x))
  | marked _ body ih => exact ih strong

theorem Strong.normal {shape : Shape action} (strong : Strong shape) (before : CompleteProduct.Carrier h w)
    (run : runPrefix action w h=(.ok (value,v),last)) : CompleteProduct.Carrier last v := by
  obtain ⟨_,_,_,post⟩ := strong.checked w h before
  simpa only [run] using post

theorem Strong.framed (strong : Strong shape) (before : CompleteProduct.Carrier h w) : Framed shape w h := by
  induction shape generalizing w h with
  | pure => exact before.1
  | native token => cases token <;> first | exact before.1 | exact False.elim strong
  | child => exact strong.2 h w before
  | bind head tail ihHead ihTail => exact ⟨ihHead strong.1 before,fun value u middle run=>
      ihTail value (strong.2 value) (Strong.normal strong.1 before run)⟩
  | marked _ body ih => exact ih strong before

theorem Strong.source_mpr {left right : PrefixM Event α} (same : left=right)
    {shape : Shape right} (strong : Strong shape) : Strong ((congrArg Shape same).mpr shape) := by
  cases same
  exact strong

theorem socket_checked (action : WG.M α) (frame : SameSocket action) :
    CompleteProduct.Checked (liftPrefix (liftWG action)) := by
  apply CompleteProduct.wg
  apply CompleteProduct.pair (CompletePassive.native CompleteProduct.Safe CompleteProduct.account_safe action (ControlFrames.socket frame))
    (erasesStatePrefix_lift action)
  exact AllocatedFrames.observed (erasesStatePrefix_lift action)
    (socketControlLift_preserves allocationAmbient allocationSocketControlStable action
      (frame.of_factor WGOwnedView.toWGStoreView _ (fun _=>rfl)))

theorem branch_checked (site : Decision) (value : Bool) :
    CompleteProduct.Checked (liftPrefix (liftWG (branch site value : WG.M Bool))) := by
  apply CompleteProduct.wg
  apply CompleteProduct.state_store
  intro initial
  exact hoare_liftAmbient (AmbientM.branch site value) (fun w=>wgStoreView w=initial)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
