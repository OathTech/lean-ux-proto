import Leanux.Proofs.Logged.WGPrefix

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RemainingLoop
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem forIn_remaining {Event α β : Type} (xs : List α) (b : β)
    (body : α → β → WGPrefix Event (ForInStep β))
    (I : List α → β → List Event → WGWorld → Ambient → Prop)
    (S : List Event → Prop) (Q : β → List Event → WGWorld → Ambient → Prop)
    (safe : ∀ b h w a, Q b h w a → S h)
    (done : ∀ b h w a, I [] b h w a → S h ∧ Q b h w a)
    (step : ∀ x rest b, StatePrefixEnsures (I (x :: rest) b) S (body x b)
      (fun out => match out with | .done b => Q b | .yield b => I rest b)) :
    StatePrefixEnsures (I xs b) S (forIn xs b body) Q := by
  induction xs generalizing b with
  | nil =>
    exact StatePrefixEnsures.pure b
      (fun h w a hi=>(done b h w a hi).1) (fun h w a hi=>(done b h w a hi).2)
  | cons x rest ih =>
    rw [List.forIn_cons]
    apply StatePrefixEnsures.bind (step x rest b)
    intro out
    cases out with
    | done b => exact StatePrefixEnsures.pure b (safe b) (fun _ _ _ hi=>hi)
    | yield b => exact ih b

end Leanux.Proofs.WG.Config.RemainingLoop
