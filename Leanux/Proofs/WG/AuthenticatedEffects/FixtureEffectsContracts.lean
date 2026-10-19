import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsSource

/-! Marker contracts do not grant authorization. Both the live-state invariant
and the retained stopped-history predicate must be preserved by the actual
entry, body and exit callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
open Leanux Leanux.Proofs.Logged

theorem run_preserves {P : List E → WGWorld → Ambient → Prop} {S : List E → Prop}
    (hooks : Hooks E) (trigger : Trigger) (body : WGPrefix E α)
    (safe : ∀ h w a, P h w a → S h)
    (enter : StatePrefixPreserves P S (hooks.enter trigger))
    (leave : ∀ token, StatePrefixPreserves P S (hooks.leave token))
    (preserves : StatePrefixPreserves P S body) :
    StatePrefixPreserves P S (runWith hooks trigger body) :=
  StatePrefixEnsures.bind enter (fun token =>
    StatePrefixEnsures.bind preserves (fun value =>
      StatePrefixEnsures.bind (leave token) (fun _ =>
        StatePrefixEnsures.pure value safe (fun _ _ _ input => input))))

end Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
