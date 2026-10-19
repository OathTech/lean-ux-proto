import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedBase

/-! Saved peer updates are justified by their actual preceding getter. The
invariant never assumes that an arbitrary peer value can be written without
creating timer occurrences. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

theorem state_read_write (pid : PeerId) (f : Peer → Peer) (next : Peer → WGPrefix Event α)
    (timers : ∀ p timer, ((f p).internalId,(f p).timer timer,(f p).wheel timer) =
      (p.internalId,p.timer timer,p.wheel timer))
    (tail : ∀ p, StateSafe (next p)) :
    StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))
      next p) := by
  let observed : WGPrefix Event Peer := do
    let p ← liftWGPrefix (getPeer pid)
    liftWGPrefix (setPeer pid (f p))
    pure p
  let original : WG.M Peer := do
    let p ← getPeer pid
    setPeer pid (f p)
    pure p
  have native : StateSafe observed := by
    apply state_observed observed original
    · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun p =>
        erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure p))
    · exact (StateAppends.lift _).bind (fun p => (StateAppends.lift _).bind (fun _ => StateAppends.pure p))
    · apply DelayedEffects.native_retained
      · intro initial
        apply TimerSlots.retained_read initial pid
        intro p known
        exact preserves_bind (TimerSlots.retained_write initial pid (f p) (by
          intro timer
          rw [timers]
          exact known timer)) (fun _ => preserves_pure p)
      · change SameView SendWorkCauses.queue original
        exact (SendWorkCauses.peer_read_frame pid).bind (fun p =>
          (SendWorkCauses.peer_write_frame pid (f p)).bind (fun _ => SameView.pure _ _))
  simpa only [observed,bind_assoc,pure_bind,effects,CausalEffects.ops,TimerEffects.observed] using state_bind native tail

theorem state_read_modify (pid : PeerId) (f : Peer → Peer)
    (timers : ∀ p timer, ((f p).internalId,(f p).timer timer,(f p).wheel timer) =
      (p.internalId,p.timer timer,p.wheel timer)) :
    StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))) := by
  have unit_pure : (fun (_ : Unit) => (pure () : WGPrefix Event Unit)) = pure := by
    funext value
    cases value
    rfl
  simpa only [unit_pure,bind_pure] using state_read_write pid f (fun _ => pure ()) timers (fun _ => state_pure ())

open Lean Meta Elab Tactic in
elab "causal_delayed_native_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a delayed state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``TimerEffects.Ops.step || action.isAppOf ``liftWGPrefix do throwError "not a native leaf"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different native head"

open Lean Meta Elab Tactic in
elab "causal_delayed_read_write_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a delayed state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a read continuation"
  let args := action.getAppArgs
  let read := args[args.size - 2]!.consumeMData.headBeta
  unless read.isAppOf ``TimerEffects.Ops.step || read.isAppOf ``liftWGPrefix do throwError "not a source read"
  unless read.getAppArgs.back!.isAppOf ``getPeer do throwError "not a peer read"
  let .lam _ _ body _ := args.back!.consumeMData | throwError "not a continuation lambda"
  let body := body.consumeMData.headBeta
  let write := if body.isAppOf ``Bind.bind then body.getAppArgs[body.getAppArgs.size - 2]! else body
  unless write.isAppOf ``TimerEffects.Ops.step || write.isAppOf ``liftWGPrefix do throwError "not an immediate source write"
  unless write.getAppArgs.back!.isAppOf ``setPeer do throwError "not a peer write"

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
