import Leanux.Proofs.WG.AuthenticatedEffects.CausalScope

/-! Source-preserving contracts for lexical scope markers. A preserved history
predicate must explicitly accept the markers; authorization is not inferred
from entering a scope. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

variable {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}

theorem withToken_preserves (record : Event Cause → E) (cause : Cause)
    (body : Token Cause → WGPrefix E α)
    (safe : ∀ h w a, P h w a → S h)
    (markers : ∀ event h w a, P h w a → P (h ++ [record event]) w a)
    (preserves : ∀ token, StatePrefixPreserves P S (body token)) :
    StatePrefixPreserves P S (withToken record cause body) := by
  intro w a h hi
  let token : Token Cause := ⟨h.length,cause⟩
  have emit (event : Event Cause) : StatePrefixPreserves P S (emitStatePrefix (record event)) :=
    StatePrefixEnsures.emit _
      (fun history world ambient input => safe _ _ _ (markers event history world ambient input))
      (fun history world ambient input => markers event history world ambient input)
  have composed : StatePrefixPreserves P S (do
      emitStatePrefix (record (.entered token))
      let result ← body token
      emitStatePrefix (record (.exited token.position))
      pure result) :=
    StatePrefixEnsures.bind (emit (.entered token)) (fun _ =>
      StatePrefixEnsures.bind (preserves token) (fun result =>
        StatePrefixEnsures.bind (emit (.exited token.position)) (fun _ =>
          StatePrefixEnsures.pure result safe (fun _ _ _ input => input))))
  exact composed w a h hi

theorem scope_preserves (record : Event Cause → E) (cause : Cause)
    (body : WGPrefix E α)
    (safe : ∀ h w a, P h w a → S h)
    (markers : ∀ event h w a, P h w a → P (h ++ [record event]) w a)
    (preserves : StatePrefixPreserves P S body) :
    StatePrefixPreserves P S (scope record cause body) :=
  withToken_preserves record cause (fun _ => body) safe markers (fun _ => preserves)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
