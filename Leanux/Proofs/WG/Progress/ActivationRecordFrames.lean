import Leanux.Proofs.WG.Progress.RecordSuffixSource
import Leanux.Proofs.WG.Progress.ActivationExitSource
import Leanux.Proofs.WG.Roaming.HandshakeOverlayStepSource
import Leanux.Proofs.Framing.Batch
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing
/-- Ambient-sensitive variant of the shared occupancy store frame. The
actual getters are read-only; an arbitrary Ambient action would not suffice. -/
theorem activationOccupancy_sameKernel_hidden (a : Activation) :
    SameView (fun w : World => w.ambient.hidden) (Activation.occupancy a) := by
  have dev : SameView (fun w : World => w.ambient.hidden) (liftWG getDev) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro before value after run
    rw [Roaming.HandshakeOverlay.getDev_run] at run
    cases hd : before.wg.dev <;> simp only [hd] at run <;> cases run
    rfl
  have peer (pid : PeerId) :
      SameView (fun w : World => w.ambient.hidden) (liftWG (getPeer pid)) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro before value after run
    rw [liftWG_run] at run
    cases native : ((getPeer pid).run before.wg).run before.ambient with
    | error error => rw [native] at run; cases run
    | ok pair =>
      obtain ⟨⟨p,g⟩,ambient⟩ := pair
      obtain ⟨_,ambientEq,_⟩ := Peers.getPeer_current pid before.wg g p
        before.ambient ambient native
      rw [native] at run
      cases run
      exact congrArg Ambient.hidden ambientEq
  have fail {α : Type} (message : String) :
      SameView (fun w : World => w.ambient.hidden)
        (invariant message : Leanux.M α) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro before value after run
    cases run
  unfold Activation.occupancy
  apply SameView.bind dev
  intro d
  cases a.worker <;> dsimp only <;> first
    | exact SameView.pure _ _
    | exact fail _
    | skip
  split
  · exact SameView.bind (peer _) (fun _ => SameView.pure _ _)
  · exact fail _
end Leanux.Proofs.WG.Progress.RecordSuffix
