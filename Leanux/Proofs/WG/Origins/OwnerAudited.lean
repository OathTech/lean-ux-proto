import Leanux.Proofs.Logged.FocusedInvariant
import Leanux.Proofs.WG.Origins.OwnerTimers
import Leanux.Proofs.WG.Origins.OwnerWorkers

/-! Owner bounds and existing captured checks through audit-only deferred work.
The small invariant does not assume allocation safety for an arbitrary saved
peer scan. Full boundary contracts are joined separately on the same run. -/
namespace Leanux.Proofs.WG.OwnerAudited
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues OwnerBounds
open Origins.HistorySupport (sensitive)

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  Carrier w.wg ∧ OwnerChecks.Checks h

abbrev Audited (g : AuditM α) :=
  FocusedInvariant Inv OwnerChecks.Checks RxHistory.Event.audit RxHistory.auditEvent g

private theorem safe (h : List RxHistory.Event) (w : World) (hi : Inv h w) :
    OwnerChecks.Checks h := hi.2

theorem join (g : RxHistory.Obs α)
    (current : CurrentChecks.Preserves g)
    (boundary : PrefixPreserves RxHistory.BoundaryInv RxHistory.BoundarySafe g)
    (owner : PrefixPreserves Inv OwnerChecks.Checks g) : OwnerChecks.Preserves g := by
  apply OwnerChecks.combine g current boundary
  · intro w h hi x v hr
    have post := (owner w h ⟨hi.carrier,hi.checked⟩).choose_spec.2.2
    rw [hr] at post
    exact post.1
  · intro w h hi
    exact (owner w h ⟨hi.carrier,hi.checked⟩).choose_spec.2.1

theorem join_ensures (g : RxHistory.Obs α) (P : World → Prop) (Q : α → World → Prop)
    (current : CurrentChecks.Preserves g)
    (boundary : PrefixEnsures (fun h w => RxHistory.BoundaryInv h w ∧ P w)
      RxHistory.BoundarySafe g (fun x h w => RxHistory.BoundaryInv h w ∧ Q x w))
    (owner : PrefixPreserves Inv OwnerChecks.Checks g) :
    PrefixEnsures (fun h w => OwnerChecks.Inv h w ∧ P w) OwnerChecks.Safe g
      (fun x h w => OwnerChecks.Inv h w ∧ Q x w) := by
  intro w h hi
  obtain ⟨suffix,hs,cs,cp⟩ := current w h hi.1.current
  obtain ⟨_,_,bs,bp⟩ := boundary w h ⟨hi.1.boundary,hi.2⟩
  obtain ⟨_,_,os,op⟩ := owner w h ⟨hi.1.carrier,hi.1.checked⟩
  refine ⟨suffix,hs,⟨cs,bs,os⟩,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    rw [hr] at cp bp op
    exact ⟨⟨cp,bp.1,op.1,op.2⟩,bp.2⟩

private theorem store (a : Leanux.M α) (frame : SameProductStore a) :
    PrefixPreserves Inv OwnerChecks.Checks (liftPrefix a) := by
  apply viewLiftPrefix_preserves productStoreView safe
  · intro h w v eq hi
    exact ⟨(pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      hi.1 (congrArg (fun s : ProductStore43 => s.2.2.2.dev) eq),hi.2⟩
  · exact frame

private theorem native_audit (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hc : Preserves Carrier a) :
    Audited (auditFocus (liftWGObserver g)) := by
  refine ⟨Appends.focus _ _ _,?_⟩
  change PrefixPreserves Inv OwnerChecks.Checks (RxHistory.mixed (liftWGObserver g))
  intro w h hi
  have app : Appends (RxHistory.mixed (liftWGObserver g)) := Appends.focus _ _ _
  have quiet : HistoryFrame sensitive (RxHistory.mixed (liftWGObserver g)) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _
  have checks := OwnerChecks.Checks.of_unchanged (w := w) app quiet hi.2
  obtain ⟨suffix,hs⟩ := app w h
  refine ⟨suffix,hs,checks,?_⟩
  cases hr : (runPrefix (RxHistory.mixed (liftWGObserver g)) w h).1 with
  | error e => trivial
  | ok out =>
    have source := ((RxHistory.mixed_erases (liftWGObserver_erases he)) w h).symm.trans hr
    rw [liftWG_run] at source
    cases native : (a.run w.wg).run w.ambient with
    | error e => simp [native,Except.map] at source
    | ok endpoint =>
      rcases endpoint with ⟨⟨result,u⟩,ambient⟩
      simp only [native,Except.map,Except.ok.injEq] at source
      cases source
      exact ⟨(hoare_iff_run_ambient _ _ _).mp hc
        w.wg w.ambient result u ambient hi.1 native,checks⟩

private theorem focused_store (a : Leanux.M α) (frame : SameProductStore a) :
    Audited (liftPrefix a) :=
  FocusedInvariant.lift _ _ a (store a frame)

private theorem audit_bind (g : AuditM α) (f : α → AuditM β)
    (hg : Audited g) (hf : ∀ x, Audited (f x)) : Audited (g >>= f) :=
  hg.bind (fun _ => rfl) hf

private theorem audit_pure (x : α) : Audited (pure x) :=
  FocusedInvariant.pure _ _ safe x

private theorem focused_forIn {γ : Type} (xs : List γ) (init : β)
    (f : γ → β → AuditM (ForInStep β)) (hf : ∀ x z, Audited (f x z)) :
    Audited (forIn xs init f) :=
  FocusedInvariant.forIn RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) safe xs init f hf

private theorem focused_range (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → AuditM (ForInStep β)) (hf : ∀ x z, Audited (f x z)) :
    Audited (forIn r init f) :=
  FocusedInvariant.range RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) safe r init f hf
theorem sendOne : Audited runOneSendWorkerAudit := by
  unfold Audited runOneSendWorkerAudit
  apply audit_bind _ _ (focused_store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases d.sendWorkQueue.head? with
  | none =>
    dsimp only
    exact focused_store _ (fun initial => productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
  | some headPid =>
    dsimp only
    apply audit_bind _ _ (focused_store (peekUnit .sendWorker) (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    intro unit
    cases unit <;> dsimp only
    all_goals (apply audit_bind)
    · exact audit_pure _
    · intro pid
      exact native_audit _ _ (runFlushedSendWorkPrefix_erases _) (OwnerLifecycle.runFlushedSendWork_preserves _)
    · exact focused_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi))
    · intro pid
      exact native_audit _ _ (runFlushedSendWorkPrefix_erases _) (OwnerLifecycle.runFlushedSendWork_preserves _)

theorem clearOne : Audited runOneClearWorkerAudit := by
  unfold Audited runOneClearWorkerAudit
  apply audit_bind _ _ (focused_store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases d.clearWorkQueue.head? with
  | none =>
    dsimp only
    exact focused_store _ (fun initial => productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))
  | some headPid =>
    dsimp only
    apply audit_bind _ _ (focused_store (peekUnit .clearPeerWorker) (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    intro unit
    cases unit <;> dsimp only
    all_goals (apply audit_bind)
    · exact audit_pure _
    · intro pid
      exact native_audit _ _ (runFlushedClearWorkPrefix_erases _) (OwnerLifecycle.runFlushedClearWork_preserves _)
    · exact focused_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi))
    · intro pid
      exact native_audit _ _ (runFlushedClearWorkPrefix_erases _) (OwnerLifecycle.runFlushedClearWork_preserves _)

open Lean Meta Elab Tactic in
elab "owner_audit_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Audited do throwError "not audited"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let mut action := args.back!.consumeMData
  for wrapper in [``auditFocus,``liftWGObserver] do
    if action.isAppOf wrapper then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing focused action"
      action := fields.back!.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  if expected != ``liftPrefix && action.isAppOf ``liftPrefix then
    let fields := action.getAppArgs
    unless fields.size > 0 do throwError "missing lifted action"
    action := fields.back!.consumeMData
    if action.isAppOf ``liftWG then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing WG action"
      action := fields.back!.consumeMData
  unless action.getAppFn.constName? == some expected do throwError "different observer"

open Lean Meta Elab Tactic in
elab "owner_audit_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Audited do throwError "not audited"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData
  if let .letE _ _ value body _ := action then
    replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! (args.size-1) (body.instantiate1 value)))]
  else
    let next := action.headBeta
    if !Expr.equal action next then
      replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! (args.size-1) next))]
    else
      let some _ ← matchMatcherApp? action | throwError "not a reducible observer head"
      replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

theorem saved : Audited getDevSavedAudit :=
  native_audit _ _ (erasesStatePrefix_lift getDev) (OwnerControls.store _ getDev_sameWGStore)

macro "owner_audit_steps" : tactic => `(tactic| first
  | (owner_audit_at getDevSavedAudit; exact saved)
  | (owner_audit_at delTimerPrefix
     exact native_audit _ _ (delTimerPrefix_erases _ _) (OwnerLifecycle.delTimer_preserves _ _))
  | (owner_audit_at timerCallbackPrefix
     exact native_audit _ _ (timerCallbackPrefix_erases _ _) (OwnerTimers.timerCallback_preserves _ _))
  | (owner_audit_at Env.timerWorker; exact focused_store _ (timerWorker_sameKernel _))
  | (owner_audit_at getWG; exact focused_store _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (owner_audit_at modifyWG; exact focused_store _ (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (owner_audit_at throw; exact focused_store _ (Origins.HistorySupport.source_throw _ _))
  | (owner_audit_at Env.sectionAppearsLater
     exact focused_store _ (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (owner_audit_at liftPrefix
     apply focused_store
     simp only [hidden,peekUnit,peekHiddenSite,resolveUnit,modifyAmbient,invariant,unsupported]
     intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (owner_audit_at Pure.pure; exact audit_pure _)
  | (owner_audit_at Bind.bind; apply audit_bind)
  | (owner_audit_at ForIn.forIn; first | apply focused_range | apply focused_forIn)
  | (owner_audit_at ite; split)
  | owner_audit_reduce
  | support_intro)

theorem wheelDue (d : Device) (j : UInt64) : Audited (wheelDueAudit d j) := by
  unfold wheelDueAudit
  exact native_audit _ _ (savedPeerLookupFlatMap_erases _ _ _) (preserves_pure _)

theorem wheelNextDue (d : Device) (j : UInt64) : Audited (wheelNextDueAudit d j) := by
  unfold wheelNextDueAudit
  exact audit_bind _ _ (wheelDue d j) (fun _ =>
    audit_pure _)

theorem stepComplete (b : UInt64) : Audited (requireStepCompleteAudit b) := by
  unfold requireStepCompleteAudit
  repeat' first
    | (owner_audit_at wheelDueAudit; exact wheelDue _ _)
    | owner_audit_steps

theorem nothingDue (j : UInt64) : Audited (requireNothingDueAudit j) := by
  unfold requireNothingDueAudit
  repeat' first
    | (owner_audit_at wheelNextDueAudit; exact wheelNextDue _ _)
    | owner_audit_steps

theorem audited_worker (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact hb | owner_audit_steps

theorem timerSection (worker : Worker) (body : AuditM Unit) (hb : Audited body) :
    Audited (runTimerSectionAudit worker body) := by
  unfold runTimerSectionAudit
  repeat' first
    | (owner_audit_at runWorkerPrefix; exact audited_worker worker body hb)
    | owner_audit_steps

theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Audited (timerDispatchAudit worker pid timer we step) := by
  unfold timerDispatchAudit
  repeat' first
    | (owner_audit_at requireStepCompleteAudit; exact stepComplete _)
    | (owner_audit_at runTimerSectionAudit; apply timerSection)
    | owner_audit_steps

theorem placeholderPass (j : UInt64) : Audited (RxHistory.placeholderTimerPassAudit j) := by
  unfold RxHistory.placeholderTimerPassAudit
  repeat' first
    | (owner_audit_at wheelNextDueAudit; exact wheelNextDue _ _)
    | (owner_audit_at runTimerSectionAudit; apply timerSection)
    | owner_audit_steps


end Leanux.Proofs.WG.OwnerAudited
