import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityHandshakeAdapters
import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableSavedPeer

/-! Observed peer writes retain the exact getter that justifies their saved
staged queue; arbitrary peer setters are not accepted as frames. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem state_read_write (pid : PeerId) (f : Peer → Peer) (next : Peer → WGPrefix Event α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (tail : ∀ p, StateSafe (next p)) :
    StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))
      next p) := by
  let observed : WGPrefix Event Peer := do
    let p ← liftWGPrefix (getPeer pid)
    liftWGPrefix (setPeer pid (f p))
    pure p
  have native : StateSafe observed := by
    apply state_history
    · exact Driver.History.state_bind (Driver.History.state_lift _) (fun p =>
        Driver.History.state_bind (Driver.History.state_lift _) (fun _ => Driver.History.state_pure p))
    · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun p =>
        erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure p))
    · intro h
      exact Native.update_return pid f same
    · exact StateHistoryFrame.bind (fun _ _ _ => rfl) (fun _ =>
        StateHistoryFrame.bind (fun _ _ _ => rfl) (fun _ _ _ _ => rfl))
  simpa only [observed,bind_assoc,pure_bind,effects,CausalEffects.ops,TimerEffects.observed] using state_bind native tail

theorem state_read_modify (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    StateSafe (do
      let p ← effects.step (getPeer pid)
      effects.step (setPeer pid (f p))) := by
  have unit_pure : (fun (_ : Unit) => (pure () : WGPrefix Event Unit)) = pure := by
    funext value
    cases value
    rfl
  simpa only [unit_pure,bind_pure] using state_read_write pid f (fun _ => pure ()) same (fun _ => state_pure ())

open Lean Meta Elab Tactic in
elab "available_effect_native_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a staged-origin state contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``TimerEffects.Ops.step || action.isAppOf ``liftWGPrefix do throwError "not a native leaf"
  let some native := action.getAppArgs.back? | throwError "missing native action"
  let native := native.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different native head"

open Lean Meta Elab Tactic in
elab "available_effect_update_head" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a staged-origin state contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a read continuation"
  let args := action.getAppArgs
  let some read := args[args.size - 2]? | throwError "missing read"
  let read := read.consumeMData.headBeta
  unless read.isAppOf ``TimerEffects.Ops.step || read.isAppOf ``liftWGPrefix do throwError "not a source read"
  let some nativeRead := read.getAppArgs.back? | throwError "missing read source"
  unless nativeRead.isAppOf ``getPeer do throwError "not a peer read"
  let some continuation := args.back? | throwError "missing continuation"
  let .lam _ _ body _ := continuation.consumeMData | throwError "not a continuation lambda"
  let body := body.consumeMData.headBeta
  let write ← if body.isAppOf ``Bind.bind then
      match body.getAppArgs[body.getAppArgs.size - 2]? with
      | some write => pure write
      | none => throwError "missing write"
    else pure body
  unless write.isAppOf ``TimerEffects.Ops.step || write.isAppOf ``liftWGPrefix do throwError "not an immediate source write"
  let some nativeWrite := write.getAppArgs.back? | throwError "missing write source"
  unless nativeWrite.isAppOf ``setPeer do throwError "not a peer write"


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
