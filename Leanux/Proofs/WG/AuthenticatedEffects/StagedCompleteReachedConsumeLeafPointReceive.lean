import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointTimer

/-! Original receive timer callback source. The arm callback remains an explicit
finite child until its cached-peer installation and later checks are refined. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

elab "consume_leaf_observer_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different observer head"

theorem observer_if (test : Prop) [Decidable test] (yes no : WGPrefix Event α) :
    liftWGObserver (if test then yes else no) =
      (if test then liftWGObserver yes else liftWGObserver no) := by split <;> rfl


theorem effect_step (body : WG.M α) : effects.step body = liftWGPrefix body := rfl

noncomputable def callerShape (site : HiddenSite) : Shape (wg (callerJiffies site)) := by
  unfold callerJiffies
  rw [wg_bind]
  apply Shape.bind (.native (.base (.ambient _)))
  intro ambient
  rw [wg_if]
  apply conditionalShape
  · intro yes
    change Shape (wg (hiddenJiffies site >>= fun value => pure (some value)))
    exact wgBindShape _ _ (.native (.base (.ambient _))) (fun value => .pure (some value))
  · intro no
    exact .pure none

noncomputable def guardShape (pid : PeerId) : Shape (wg (modPeerTimerGuard pid)) := by
  unfold modPeerTimerGuard WG.andM
  repeat' consume_leaf_shape

noncomputable def discardShape (body : WGPrefix Event α) (shape : Shape (liftWGObserver body)) :
    Shape (liftWGObserver (Functor.mapConst () body)) := by
  change Shape (liftWGObserver (body >>= fun _ => pure ()))
  rw [liftWGObserver_bind]
  exact .bind shape (fun _ => .pure ())

macro "consume_leaf_observed" : tactic => `(tactic| first
  | (consume_leaf_wg_head callerJiffies; exact callerShape _)
  | (consume_leaf_wg_head modPeerTimerGuard; exact guardShape _)
  | (consume_leaf_observer_head TimerEffects.Ops.arm; exact .child (.arm _ _ _ _))
  | (consume_leaf_observer_head Functor.mapConst; apply discardShape)
  | (consume_leaf_observer_head Bind.bind; rw [liftWGObserver_bind]; apply Shape.bind)
  | (consume_leaf_observer_head Pure.pure; exact .pure _)
  | (consume_leaf_observer_head ite; rw [observer_if]; apply conditionalShape)
  | consume_leaf_shape)

noncomputable def modifyShape (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Shape (liftWGObserver (TimerEffects.modifyWith effects site pid timer delay)) := by
  unfold TimerEffects.modifyWith
  simp only [effect_step]
  repeat' consume_leaf_observed

noncomputable def traversalShape (pid : PeerId) : Shape (liftWGObserver (TimerEffects.traversalWith effects pid)) := by
  apply Shape.marked (.traversal pid)
  unfold TimerEffects.traversalWith
  simp only [effect_step,discard]
  repeat' first
    | (consume_leaf_observer_head TimerEffects.modifyWith; exact modifyShape _ _ _ _)
    | consume_leaf_observed

noncomputable def receivedWriteShape (pid : PeerId) : Shape (liftWGObserver (do
    let p ← liftWGPrefix (getPeer pid)
    liftWGPrefix (setPeer pid {p with timerNeedAnotherKeepalive := true}))) := by
  rw [← Queued.lift_bind]
  exact .native (.metadata _ (PeerMetadata.updateShape pid (fun p => {p with timerNeedAnotherKeepalive := true})
    (fun _ => ⟨rfl,rfl,rfl⟩)))

noncomputable def receivedShape (pid : PeerId) : Shape (liftWGObserver (TimerEffects.dataReceivedWith effects pid)) := by
  apply Shape.marked (.received pid)
  unfold TimerEffects.dataReceivedWith
  simp only [effect_step,discard]
  rw [liftWGObserver_bind]
  refine .bind (.native (.metadata _ PeerMetadata.deviceReadShape)) ?_
  intro device
  rw [liftWGObserver_bind]
  refine .bind (.native (.base (.basic (.branch .timersDataReceivedRunning device.running)))) ?_
  intro running
  rw [observer_if]
  apply conditionalShape
  · intro yes
    rw [liftWGObserver_bind]
    refine .bind (.native (.metadata _ (PeerMetadata.peerReadShape pid))) ?_
    intro peer
    rw [liftWGObserver_bind]
    refine .bind (.native (.base (.basic (.branch .timersDataReceivedNotPending !(peer.timerPending .sendKeepalive))))) ?_
    intro pending
    rw [observer_if]
    apply conditionalShape
    · intro absent
      exact discardShape _ (modifyShape .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)
    · intro present
      exact receivedWriteShape pid
  · intro no
    exact .pure ()

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
