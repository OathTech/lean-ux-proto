import Leanux.Proofs.WG.Roaming.NapiPublicationSource
import Leanux.Proofs.WG.Roaming.PollEndpointFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Env Noise

/-- NAPI guards and section entry do not change the native WireGuard world. -/
theorem napiIrqPublicationFront_preserves (initial : WGWorld) :
    Noise.Product.Ensures napiIrqPublicationFront (fun w => w.wg = initial)
      (fun _ w => w.wg = initial) := by
  let P : World → Prop := fun w => w.wg = initial
  have ambient {α : Type} (action : AmbientM α) :
      Noise.Product.Ensures (monadLift action : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (x,a) => Except.ok (x,{w with ambient := a})) = _ at run
    cases hr : action.run w.ambient with
    | error stop => rw [hr] at run; cases run
    | ok out => obtain ⟨x,a⟩ := out; rw [hr] at run; cases run; exact pre
  have dev : Noise.Product.Ensures (liftWG getDev) P (fun _ => P) := by
    intro w result final pre run
    change (((getDev.run w.wg).run w.ambient) >>= fun ((x,g),a) =>
      Except.ok (x,{w with wg := g, ambient := a})) = _ at run
    dsimp only [getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
      StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure] at run
    cases hd : w.wg.dev with
    | none => rw [hd] at run; change Except.error _ = Except.ok _ at run; cases run
    | some d => rw [hd] at run; change Except.ok (d,w) = Except.ok (result,final) at run; cases run; exact pre
  have env : Noise.Product.Ensures getEnv P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have changeEnv (f : EnvWorld → EnvWorld) :
      Noise.Product.Ensures (modifyEnv f) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have pureFrame {α : Type} (x : α) : Noise.Product.Ensures (pure x : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have soft : Noise.Product.Ensures napiPublicationFront P (fun _ => P) := by
    unfold napiPublicationFront
    refine Noise.Product.ensures_bind _ _ dev ?_
    intro d
    dsimp only
    split
    · exact pureFrame _
    refine Noise.Product.ensures_bind _ _ (ambient (get : AmbientM Ambient)) ?_
    intro a
    refine Noise.Product.ensures_bind _ _ (ambient AmbientM.peekHiddenSite) ?_
    intro site
    split
    · exact pureFrame _
    split
    · refine Noise.Product.ensures_bind _ _ (ambient (AmbientM.unsupported _)) ?_
      intro _
      refine Noise.Product.ensures_bind _ _ (ambient (AmbientM.hidden _)) ?_
      intro _
      refine Noise.Product.ensures_bind _ _ (ambient (modify _)) ?_
      intro _
      exact pureFrame _
    · refine Noise.Product.ensures_bind _ _ (ambient (AmbientM.hidden _)) ?_
      intro _
      refine Noise.Product.ensures_bind _ _ (ambient (modify _)) ?_
      intro _
      exact pureFrame _
  unfold napiIrqPublicationFront
  refine Noise.Product.ensures_bind _ _ (ambient (get : AmbientM Ambient)) ?_
  intro a
  split
  · exact pureFrame _
  refine Noise.Product.ensures_bind _ _ dev ?_
  intro d
  split
  · exact pureFrame _
  refine Noise.Product.ensures_bind _ _ (ambient AmbientM.peekHiddenSite) ?_
  intro site
  split
  · exact pureFrame _
  refine Noise.Product.ensures_bind _ _ env ?_
  intro fixture
  refine Noise.Product.ensures_bind _ _ (changeEnv _) ?_
  intro _
  split
  · exact soft
  · exact pureFrame _


end Leanux.Proofs.WG.Roaming
