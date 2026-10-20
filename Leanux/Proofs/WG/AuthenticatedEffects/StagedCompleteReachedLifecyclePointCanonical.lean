import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointFrames

/-! Canonical witnesses expand the original lifecycle binds and saved peer
traversals. The five children are only the actual staging/keepalive, drain,
purge and release callbacks. Newlink has a dedicated source-point relation. Other native atoms, including
the destructor check, keep their finer coverage boundary explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

elab "lifecycle_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "lifecycle_native_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftPrefix do Lean.throwError "not a native lift"
  let some native := action.getAppArgs.back? | Lean.throwError "missing native action"
  let native := native.consumeMData
  let native ← if native.isAppOf ``liftWG then
      match native.getAppArgs.back? with
      | some action => pure action.consumeMData
      | none => Lean.throwError "missing WG action"
    else pure native
  let .const actual _ := native.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"


elab "lifecycle_observer_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftWGObserver do Lean.throwError "not an observer"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const actual _ := body.consumeMData.getAppFn | Lean.throwError "not a named body"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different observer body"

elab "lifecycle_wg_atom" : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftPrefix do Lean.throwError "not native"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  unless body.consumeMData.isAppOf ``liftWG do Lean.throwError "not WG"

theorem observer_list (xs : List ι) (initial : σ) (body : ι → σ → WGPrefix Event (ForInStep σ)) :
    liftWGObserver (forIn xs initial body) =
      forIn xs initial (fun value acc => liftWGObserver (body value acc)) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.forIn_cons,liftWGObserver_bind]
    congr 1
    funext decision
    cases decision <;> simp only [liftWGObserver_pure,ih]

macro "lifecycle_shape_step" : tactic => `(tactic| first
  | (lifecycle_shape_head Pure.pure; exact .pure _)
  | (lifecycle_shape_head Bind.bind; apply Shape.bind)
  | (lifecycle_shape_head ForIn.forIn; apply listShape)
  | (simp +failIfUnchanged only [liftWGObserver_bind,liftWGObserver_pure,liftWGObserver_lift,
      observer_list,liftWG_bind,liftWG_pure,Service.Points.lift_bind,Service.Points.lift_pure])
  | (lifecycle_native_head wgSetup; exact .native .setup)
  | (lifecycle_native_head wgNewlink; exact .native .newlink)
  | (lifecycle_native_head TxWork.Destruct.check; exact .native .check)
  | (lifecycle_native_head modify; exact .native .erase)
  | (lifecycle_wg_atom; solve | (refine .native (.quiet _ (wg_frame _ ?_)); solve | entry_lifecycle_native))
  | (lifecycle_wg_atom; solve | exact .native (.quiet _ (wg_frame _ RetiredFrames.settle)))
  | (lifecycle_wg_atom; solve | exact .native (.quiet _ (wg_frame _ (TimerFrames.store retireDeviceUnits_sameWGStore))))
  | (lifecycle_shape_head liftPrefix; solve | exact .native (.quiet _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w value v run
      cases run
      rfl)))

  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

def createBody : PrefixM Event Int := do
  let saved ← liftPrefix (liftWG (get : WG.M WGWorld))
  if saved.dev.isSome then return -EEXIST
  liftPrefix (liftWG wgSetup)
  let ret ← liftPrefix (liftWG wgNewlink)
  if ret < 0 then liftPrefix (liftWG (_root_.modify fun w : WGWorld=>{w with dev:=none}))
  pure ret

theorem create_factor : liftPrefix (liftWG wgCreate)=createBody := by
  unfold wgCreate createBody
  simp only [liftWG_bind,liftWG_pure,Service.Points.lift_bind,Service.Points.lift_pure,apply_ite]

noncomputable def createBodyShape : Shape createBody := by
  unfold createBody
  apply Shape.bind (.native (.quiet _ (wg_frame _ (by entry_lifecycle_native))))
  intro saved
  split
  · exact .pure _
  · apply Shape.bind (.native .setup)
    intro _
    apply Shape.bind (.native .newlink)
    intro ret
    split
    · exact .bind (.native .erase) (fun _=>.pure ret)
    · exact .bind (.pure ()) (fun _=>.pure ret)

noncomputable def createShape : Shape (liftPrefix (liftWG wgCreate)) :=
  .marked .create ((congrArg Shape create_factor).mpr createBodyShape)

noncomputable def openedShape : Shape (liftWGObserver (openObserved hooks)) := by
  apply Shape.marked .opened
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  simp only [liftWGObserver_bind,liftWGObserver_lift]
  apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.store getDev_sameWGStore))))
  intro dev
  apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.branch_frame _ _))))
  intro _
  apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.branch_frame _ _))))
  intro _
  apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.store getDev_sameWGStore))))
  intro d
  apply Shape.bind (.native (.quiet _ (wg_frame _ (ControlFrames.socket (socketInit_sameSocket _)))))
  intro ret
  apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.branch_frame _ _))))
  intro failed
  split
  · exact .pure ret
  · simp only [liftWGObserver_bind,liftWGObserver_pure,liftWGObserver_lift,observer_list]
    apply Shape.bind
    · apply listShape
      intro pid acc
      apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.branch_frame _ _))))
      intro _
      apply Shape.bind (.child (.family (.staging pid)))
      intro _
      apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.store (CompleteProduct.peer_read_store pid)))))
      intro peer
      apply Shape.bind (.native (.quiet _ (wg_frame _ (TimerFrames.branch_frame _ _))))
      intro kept
      split
      · simp only [liftWGObserver_bind,liftWGObserver_pure]
        exact .bind (.child (.family (.keepalive pid))) (fun _=>.pure (ForInStep.yield acc))
      · simpa only [liftWGObserver_pure] using (Shape.pure (ForInStep.yield acc))
    · intro _
      exact .bind (.native (.quiet _ (wg_frame _ (TimerFrames.branch_frame _ _)))) (fun _=>.pure 0)

noncomputable def upShape : Shape (liftWGObserver (upObserved hooks)) := by
  apply Shape.marked .up
  unfold upObserved
  repeat' first | (lifecycle_observer_head openObserved; exact openedShape) | lifecycle_shape_step

noncomputable def timersShape (pid : PeerId) :
    Shape (liftWGObserver (SendExchange.timersStopWith liftWGPrefix (sendDrainObserved hooks) pid)) := by
  apply Shape.marked (.timers pid)
  unfold SendExchange.timersStopWith
  repeat' first | (lifecycle_observer_head sendDrainObserved; exact .child (.family (.drain _))) | lifecycle_shape_step

noncomputable def afterDeadShape (pid : PeerId) :
    Shape (liftWGObserver (StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix
      (sendDrainObserved hooks) hooks.peerRelease pid)) := by
  apply Shape.marked (.peer pid)
  unfold StagedDisposal.Lifecycle.afterDeadWith
  repeat' first
    | (lifecycle_observer_head SendExchange.timersStopWith; exact timersShape _)
    | (lifecycle_observer_head sendDrainObserved; exact .child (.family (.drain _)))
    | (lifecycle_observer_head Hooks.peerRelease; exact .child (.family (.release _)))
    | lifecycle_shape_step

noncomputable def removeAllShape : Shape (liftWGObserver (removeAllObserved hooks)) := by
  apply Shape.marked .removeAll
  unfold removeAllObserved StagedDisposal.Lifecycle.removeAllWith Configuration.peerRemoveAllWith
  repeat' first | (lifecycle_observer_head StagedDisposal.Lifecycle.afterDeadWith; exact afterDeadShape _) | lifecycle_shape_step

noncomputable def downShape : Shape (liftWGObserver (downObserved hooks)) := by
  apply Shape.marked .down
  unfold downObserved StagedDisposal.Lifecycle.downWith StagedDisposal.Lifecycle.stopWith
  repeat' first
    | (lifecycle_observer_head SendExchange.timersStopWith; exact timersShape _)
    | (lifecycle_observer_head Hooks.stagedPurge; exact .child (.family (.purge _)))
    | lifecycle_shape_step

noncomputable def prepareShape : Shape (liftWGObserver RetiredPeer.Lifecycle.Packet.prepareObserved) := by
  apply Shape.marked .prepare
  unfold RetiredPeer.Lifecycle.Packet.prepareObserved
  repeat' first | (lifecycle_observer_head removeAllObserved; exact removeAllShape) | lifecycle_shape_step

noncomputable def tailShape : Shape (liftPrefix (liftWG CompleteRetired.tail)) := by
  apply Shape.marked .reset
  unfold CompleteRetired.tail RetiredFrames.reset
  repeat' lifecycle_shape_step

noncomputable def destructShape : Shape (liftWGObserver (destructObserved hooks)) := by
  apply Shape.marked .destruct
  rw [RetiredPeer.Lifecycle.Packet.source_factor,liftWGObserver_bind]
  exact .bind prepareShape (fun _=>by simpa only [liftWGObserver_lift] using tailShape)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
