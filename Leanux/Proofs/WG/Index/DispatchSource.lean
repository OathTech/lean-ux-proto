import Leanux.Proofs.WG.Index.DispatchFrames
import Leanux.Proofs.WG.Index.SendSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Original selection, dequeue and section wrapper compose around the checked body. -/
theorem runOneSendWorker_tables : Noise.Product.Ensures Env.runOneSendWorker
    (fun w => TablesSafeWG w.wg) (fun _ w => TablesSafeWG w.wg) := by
  let P : World → Prop := fun w => TablesSafeWG w.wg
  change Noise.Product.Ensures _ P (fun _ => P)
  have lifted {α : Type} (action : WG.M α)
      (contract : Ensures action TablesSafeWG (fun _ => TablesSafeWG)) :
      Noise.Product.Ensures (liftWG action) P (fun _ => P) := by
    intro w result final pre run
    change (((action.run w.wg).run w.ambient) >>= fun ((value, current), inputs) =>
      .ok (value, {w with wg := current, ambient := inputs})) = _ at run
    cases executed : (action.run w.wg).run w.ambient with
    | error stop => rw [executed] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, current⟩, inputs⟩ := pair
      rw [executed] at run
      cases run
      exact contract w.wg w.ambient _ current inputs pre executed
  have ambient {α : Type} (action : AmbientM α) :
      Noise.Product.Ensures (liftAmbient action) P (fun _ => P) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (value, inputs) =>
      .ok (value, {w with ambient := inputs})) = _ at run
    cases executed : action.run w.ambient with
    | error stop => rw [executed] at run; cases run
    | ok pair =>
      obtain ⟨value, inputs⟩ := pair
      rw [executed] at run
      cases run
      exact pre
  have pureValue {α : Type} (value : α) :
      Noise.Product.Ensures (pure value : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  rw [TimerDiscipline.runOneSendWorker_source]
  refine Noise.Product.ensures_bind _ _
    ((Noise.Product.ensures_iff _ _ _).mpr sendWorkerSelection_tables) ?_
  intro selected
  refine Noise.Product.ensures_bind _ _
    ((Noise.Product.ensures_iff _ _ _).mpr (sendWorkerDequeue_tables selected.2)) ?_
  intro _
  unfold Env.runWorker
  refine Noise.Product.ensures_bind _ _
    (ambient (AmbientM.hidden (.sectionStart .sendWorker))) ?_
  intro _
  refine Noise.Product.ensures_bind _ _
    (lifted _ (handshakeSendWorker_tables selected.2)) ?_
  intro _
  refine Noise.Product.ensures_bind _ _
    (ambient (AmbientM.hidden (.sectionStop .sendWorker))) ?_
  intro _
  exact pureValue ()

end Leanux.Proofs.WG.Index
