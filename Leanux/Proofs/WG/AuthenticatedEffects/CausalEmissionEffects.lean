import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProduct
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionNativeFrames

/-! Timer and queued-work bookkeeping preserves ordered socket accounting;
its own causal receipts are quiet in the independent emission projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateSafe (effects.arm pid timer delay caller) :=
  state_current _ (fun _ => state_receipt _
    (state_native _ (EmissionFrames.arm pid timer delay caller)) _ (fun _ => rfl))

theorem queue (pid : PeerId) : StateSafe (effects.append pid) :=
  state_current _ (fun _ => state_receipt _
    (state_native _ (by sent_frame [] using [])) _ (fun _ => rfl))

open Lean Meta Elab Tactic in
elab "emission_native_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not an emission state contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGPrefix do throwError "not a native state lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native source"

macro "emission_effect_native" : tactic => `(tactic| first
  | (emission_native_head modPeerTimerGuard; exact state_native _ (EmissionFrames.guard _))
  | (emission_native_head callerJiffies; exact state_native _ ((callerJiffies_sameWGWorld _).factor WGWorld.sent))
  | (emission_native_head jitterBelowRekeyTimeout; exact state_native _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor WGWorld.sent))
  | (emission_native_head branchExpired; exact state_native _ ((branchExpired_sameWGWorld _ _ _ _).factor WGWorld.sent))
  | (emission_native_head peerGet; exact state_native _ (peerGet_sent _))
  | (emission_native_head peerPut; exact state_native _ (peerPut_sent _))
  | (emission_native_head delTimer; exact state_native _ (EmissionFrames.delete _ _))
  | (emission_native_head peekQueuedUnit; apply state_native; sent_frame [peekQueuedUnit] using [])
  | (emission_native_head recordQueued; apply state_native; sent_frame [recordQueued] using [])
  | emission_native)

macro "emission_effect_step" : tactic => `(tactic| first
  | (emission_head TimerEffects.Ops.step; change StateSafe (liftWGPrefix _); emission_effect_native)
  | (emission_head TimerEffects.Ops.arm; exact arm _ _ _ _)
  | (emission_head TimerEffects.Ops.append; exact queue _)
  | emission_effect_native
  | emission_step)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateSafe (TimerEffects.modifyWith effects site pid timer delay) := by
  unfold TimerEffects.modifyWith
  repeat' emission_effect_step

theorem traversal (pid : PeerId) : StateSafe (TimerEffects.traversalWith effects pid) := by
  unfold TimerEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | emission_effect_step

theorem derived (pid : PeerId) : StateSafe (TimerEffects.derivedWith effects pid) := by
  unfold TimerEffects.derivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact state_bind (modify_timer _ _ _ _) (fun _ => state_pure _)

theorem data_sent (pid : PeerId) : StateSafe (TimerEffects.dataSentWith effects pid) := by
  unfold TimerEffects.dataSentWith
  repeat' emission_effect_step

theorem data_received (pid : PeerId) : StateSafe (TimerEffects.dataReceivedWith effects pid) := by
  unfold TimerEffects.dataReceivedWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_head TimerEffects.modifyWith; exact modify_timer _ _ _ _)
    | emission_effect_step

theorem initiated (pid : PeerId) : StateSafe (TimerEffects.initiatedWith effects pid) := by
  unfold TimerEffects.initiatedWith
  repeat' emission_effect_step

theorem queued (pid : PeerId) (retry : Bool) : StateSafe (TimerEffects.queuedWith effects pid retry) := by
  unfold TimerEffects.queuedWith
  repeat' emission_effect_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
