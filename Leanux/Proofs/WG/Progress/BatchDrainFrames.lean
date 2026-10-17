import Leanux.Env
import Leanux.Proofs.WG.Noise.Execution

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Device-only local variant of C1 `Framing.deliverSent_sameKernel` in `Framing/EnvLeaves.lean`.
Actual deliveries may change fixture outputs and `sent`; their normal runs
preserve the full optional Device. -/
theorem deliverSent_sameKernel_device_variant (initial : Option Device) :
    Noise.Product.Ensures deliverSent (fun w => w.wg.dev = initial)
      (fun _ w => w.wg.dev = initial) := by
  let P := fun w : World => w.wg.dev = initial
  have hpure {α : Type} (x : α) : Noise.Product.Ensures (pure x : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have hget : Noise.Product.Ensures (getWG : Leanux.M WGWorld) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have hroute : Noise.Product.Ensures (getRouting : Leanux.M Net.Routing) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have hedit (f : EnvWorld → EnvWorld) : Noise.Product.Ensures (modifyEnv f) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have hstop (why : String) : Noise.Product.Ensures (unsupported why : Leanux.M Unit) P (fun _ => P) := by
    intro w result final pre run
    change Except.error _ = Except.ok _ at run
    cases run
  have hlist {α β : Type} (xs : List α) (initial : β)
      (body : α → β → Leanux.M (ForInStep β))
      (step : ∀ a b, Noise.Product.Ensures (body a b) P (fun _ => P)) :
      Noise.Product.Ensures (forIn xs initial body) P (fun _ => P) := by
    induction xs generalizing initial with
    | nil => simpa only [List.forIn_nil] using hpure initial
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine Noise.Product.ensures_bind _ _ (step x initial) ?_
      intro result
      cases result with
      | done final => exact hpure final
      | yield next => exact ih next
  unfold deliverSent
  refine Noise.Product.ensures_bind _ _ hget ?_
  intro g
  refine Noise.Product.ensures_bind _ _ (hlist _ _ _ ?_) ?_
  · intro dg accumulator
    refine Noise.Product.ensures_bind _ _ hroute ?_
    intro routing
    dsimp only
    split
    · exact Noise.Product.ensures_bind _ _ (hedit _) (fun _ => hpure _)
    · split
      · exact Noise.Product.ensures_bind _ _ (hedit _) (fun _ => hpure _)
      · exact Noise.Product.ensures_bind _ _ (hedit _) (fun _ => hpure _)
      · split
        · exact Noise.Product.ensures_bind _ _ (hstop _) (fun _ => hpure _)
        · exact hpure _
  · intro _ w result final pre run
    cases run
    exact pre

end Leanux.Proofs.WG.Progress
