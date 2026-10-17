import Leanux.Proofs.WG.Queues.RxEnvWorkersHistory
import Leanux.Proofs.WG.Lifetimes.EnvDeferredCalls

/-! Concrete timer callers retain every worker continuation and recorded wait
boundary. Poll-free wheel dispatches and the placeholder timer pass are focused;
each saved peer scan is justified by its actual getter. Reset/absence guards
and every crypt-worker continuation remain explicit. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- Focus a conditional audit contract while preserving existing poll metadata.
The lower contract receives the actual projected incoming history. -/
private theorem timer_audit_ensures (a : AuditM α) (P : World → Prop)
    (Q : α → World → Prop)
    (ha : PrefixEnsures (fun h w => AuditInv h w ∧ P w) AuditSafe a
      (fun x h w => AuditInv h w ∧ Q x w)) :
    PrefixEnsures (fun h w => BoundaryInv h w ∧ P w) BoundarySafe (audit a)
      (fun x h w => BoundaryInv h w ∧ Q x w) := by
  intro w h hi
  have hf := ha.focus Event.audit auditEvent (fun _ => rfl) w h ⟨hi.1.audit, hi.2⟩
  obtain ⟨suffix, hs, hsafe, hpost⟩ := hf
  change (runPrefix (audit a) w h).2 = h ++ suffix at hs
  have he : stamps (runPrefix (audit a) w h).2 = stamps h :=
    congrArg (List.map RxJoint.Entry.stamp) (audit_entries a w h)
  refine ⟨suffix, hs, ⟨hsafe, he ▸ hi.1.distinct⟩, ?_⟩
  cases hr : (runPrefix (audit a) w h).1 with
  | error e => trivial
  | ok out =>
    have ho : AuditInv (auditHistory (runPrefix (audit a) w h).2) out.2 ∧ Q out.1 out.2 := by
      have hr' : (runPrefix (focusPrefix Event.audit auditEvent a) w h).1 = .ok out := hr
      simpa only [hr', auditHistory, audit] using hpost
    refine ⟨⟨ho.1, he ▸ hi.1.distinct, ?_⟩, ho.2⟩
    intro stamp hm
    have old := hi.1.released stamp (he ▸ hm)
    rw [hs]
    exact (released_append h suffix stamp).mpr (Or.inl old)

/-- Exact product-state projection carries the first call's result-dependent
postcondition into its continuation, including every failure prefix. -/
private theorem timer_projects_bind {State E F α β : Type}
    {I : List F → State → Prop} {S : List F → Prop}
    {Q : α → List F → State → Prop} {ρ : E → Option F}
    {g : PrefixT E State α} {a : PrefixT F State α}
    {f : α → PrefixT E State β} {b : α → PrefixT F State β}
    (hg : ProjectsUnder I ρ g a) (ha : PrefixEnsures I S a Q)
    (hf : ∀ x, ProjectsUnder (Q x) ρ (f x) (b x)) :
    ProjectsUnder I ρ (g >>= f) (a >>= b) := by
  intro w h hi
  have he := hg w h hi
  obtain ⟨_, _, _, hp⟩ := ha w (h.filterMap ρ) hi
  rw [he] at hp
  rw [runPrefix_bind, runPrefix_bind, he]
  cases hr : runPrefix g w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨x, v⟩
      exact hf x v hist (by simpa only [hr] using hp)

/-- A pure return after a focused action has the lower action's exact outcome;
no hypothesis of independence from the incoming history is used. -/
private theorem timer_audit_suffix_erases (a : AuditM α) (f : α → β)
    (original : Leanux.M β)
    (ha : ErasesPrefix (a >>= fun x => pure (f x)) original) :
    ErasesPrefix (audit a >>= fun x => pure (f x)) original := by
  intro w h
  have he := ha w (h.filterMap auditEvent)
  rw [runPrefix_bind] at he ⊢
  cases hr : runPrefix a w (h.filterMap auditEvent) with
  | mk result hist =>
    have ra : runPrefix (audit a) w h =
        (result, h ++ (hist.drop (h.filterMap auditEvent).length).map Event.audit) := by
      change ((runPrefix a w (h.filterMap auditEvent)).1,
        h ++ ((runPrefix a w (h.filterMap auditEvent)).2.drop (h.filterMap auditEvent).length).map Event.audit) = _
      rw [hr]
    rw [ra]
    rw [hr] at he
    cases result with
    | error e => exact he
    | ok out => simpa only [runPrefix_pure] using he

/-- The current wheel's poll-free timer pass, before crypt/send processing. -/
def placeholderTimerPassSource (jHi : UInt64) : Leanux.M Unit := do
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDev
    let some (pid, t, _) := TimerWheel.nextDue d jHi | break
    delTimer pid t
    Env.runTimerSection (← Env.timerWorker t) (WG.timerCallback pid t)

/-- Same pass with the existing R2 saved-map accesses. Each iteration derives
its scan premise from its actual getter; no saved-map premise escapes this block. -/
def placeholderTimerPassAudit (jHi : UInt64) : AuditM Unit := do
  let pending := (← getDevSavedAudit).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDevSavedAudit
    let some (pid, t, _) ← wheelNextDueAudit d jHi | break
    auditFocus (liftWGObserver (delTimerPrefix pid t))
    runTimerSectionAudit (← liftPrefix (Env.timerWorker t)) (auditFocus (liftWGObserver (timerCallbackPrefix pid t)))

theorem placeholderTimerPass_erases (jHi : UInt64) :
    ErasesPrefix (placeholderTimerPassAudit jHi) (placeholderTimerPassSource jHi) := by
  unfold placeholderTimerPassAudit placeholderTimerPassSource
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (maintenance_head getDevSavedAudit; exact getDevSavedAudit_erases)
    | (timer_audit_bound wheelNextDueAudit; apply erasesPrefix_bind_pure (wheelNextDueAudit_erases _ _))
    | (timer_audit_focus_head delTimerPrefix; exact auditFocus_erases (liftWGObserver_erases (delTimerPrefix_erases _ _)))
    | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_erases (liftWGObserver_erases (timerCallbackPrefix_erases _ _)))
    | (maintenance_head runTimerSectionAudit; apply runTimerSectionAudit_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (maintenance_head ite; apply erasesPrefix_ite)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem placeholderTimerPass_preserves (jHi : UInt64) :
    PrefixPreserves AuditInv AuditSafe (placeholderTimerPassAudit jHi) := by
  apply PrefixEnsures.preserves
  unfold placeholderTimerPassAudit
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (timer_audit_bound getDevSavedAudit; first
        | apply PrefixEnsures.bind getDevSavedAudit_spec
        | (timer_audit_drop_saved; apply PrefixEnsures.bind getDevSavedAudit_spec))
    | (timer_audit_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheelNextDueAudit_spec _ _))
    | timer_audit_calls
    | (timer_audit_drop_saved; timer_audit_calls)
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | (timer_audit_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (timer_audit_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

/-- Strengthen only an entry condition of an exact projection. -/
private theorem timer_projects_weaken {State E F α : Type}
    {I J : List F → State → Prop} {ρ : E → Option F}
    {g : PrefixT E State α} {a : PrefixT F State α}
    (hi : ∀ h w, J h w → I h w) (hp : ProjectsUnder I ρ g a) :
    ProjectsUnder J ρ g a := fun w h hj => hp w h (hi _ _ hj)

/-- Syntactic dispatch avoids unfolding unrelated effectful actions during
proof-rule matching. Every selected rule still constructs a checked term. -/
elab "rx_timer_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  let isPreserve := ty.isAppOf ``PrefixPreserves
  unless isPreserve || ty.isAppOf ``PrefixEnsures || ty.isAppOf ``ErasesPrefix ||
      ty.isAppOf ``ProjectsUnder do Lean.throwError "not an observer contract"
  unless args.size ≥ 2 do Lean.throwError "missing observer"
  let mut a := (if isPreserve then args.back! else args[args.size - 2]!).consumeMData
  for _ in [:4] do
    if a.isAppOf ``audit || a.isAppOf ``auditFocus || a.isAppOf ``liftPrefix then
      unless a.getAppArgs.size > 0 do Lean.throwError "missing wrapped action"
      a := a.getAppArgs.back!.consumeMData
  let some head := a.getAppFn.constName? | Lean.throwError "not a named action"
  let wanted := name.getId.eraseMacroScopes.toString
  unless head.toString == wanted || head.toString.endsWith ("." ++ wanted) do
    Lean.throwError "different action"

elab "rx_timer_bound " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless ty.isAppOf ``PrefixEnsures || ty.isAppOf ``ErasesPrefix ||
      ty.isAppOf ``ProjectsUnder do Lean.throwError "not an observer contract"
  unless args.size ≥ 2 do Lean.throwError "missing observer"
  let a := args[args.size - 2]!.consumeMData
  unless a.isAppOf ``Bind.bind && a.getAppArgs.size ≥ 2 do Lean.throwError "not a bind"
  let mut first := a.getAppArgs[a.getAppArgs.size - 2]!.consumeMData
  for _ in [:4] do
    if first.isAppOf ``audit || first.isAppOf ``auditFocus || first.isAppOf ``liftPrefix then
      unless first.getAppArgs.size > 0 do Lean.throwError "missing wrapped action"
      first := first.getAppArgs.back!.consumeMData
  let some head := first.getAppFn.constName? | Lean.throwError "not a named action"
  let wanted := name.getId.eraseMacroScopes.toString
  unless head.toString == wanted || head.toString.endsWith ("." ++ wanted) do
    Lean.throwError "different action"

elab "rx_timer_projects_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProjectsUnder do Lean.throwError "not a projection"
  let .app (.app front observed) lower := target | Lean.throwError "missing paired observers"
  let rec head : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. => let next := e.headBeta; if Lean.Expr.equal e next then e else head n next
        | _ => e
  let reduce (a : Lean.Expr) : Lean.MetaM Lean.Expr := do
    let a := head 64 a
    if (← Lean.Meta.matchMatcherApp? a).isSome then
      if let .reduced next ← Lean.Meta.reduceMatcher? a then return next
    return a
  let observed' ← reduce observed
  let lower' ← reduce lower
  if Lean.Expr.equal observed observed' && Lean.Expr.equal lower lower' then
    Lean.throwError "unchanged paired heads"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp2 front observed' lower')]

elab "rx_timer_projects_saved_pre" : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless ty.isAppOf ``ProjectsUnder && args.size ≥ 4 do Lean.throwError "not a projection"
  let mut pre := args[args.size - 4]!.consumeMData
  for _ in [:2] do
    match pre with
    | .lam _ _ body _ => pre := body.consumeMData
    | _ => pure ()
  unless pre.isAppOf ``And do Lean.throwError "no saved receipt"

macro "rx_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence (P := BoundaryInv) (Q := fun _ => BoundaryInv) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "rx_timer_calls" : tactic => `(tactic|
  first
  | (rx_timer_head timerDispatchAudit; exact audit_preserves _ (timerDispatchAudit_preserves _ _ _ _ _))
  | (rx_timer_head requireStepCompleteAudit; exact audit_preserves _ (requireStepCompleteAudit_preserves _))
  | (rx_timer_head requireNothingDueAudit; exact audit_preserves _ (requireNothingDueAudit_preserves _))
  | (rx_timer_head placeholderTimerPassAudit; exact audit_preserves _ (placeholderTimerPass_preserves _))
  | (rx_timer_head runOneSendWorkerAudit; exact audit_preserves _ runOneSendWorkerAudit_preserves)
  | (rx_timer_head runOneClearWorkerAudit; exact audit_preserves _ runOneClearWorkerAudit_preserves)
  | (rx_timer_head runCryptWorkers; exact runCryptWorkers_preserves)
  | (rx_timer_head runSendWorkers; exact runSendWorkers_preserves)
  | (rx_timer_head getWG; exact boundaryLift_kernel _ (by
      intro initial; exact productGetWG_spec (fun s => s = initial)))
  | (rx_timer_head modifyWG; exact boundaryLift_kernel _ (by
      intro initial; exact productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_timer_head getEnv; exact boundaryLift_kernel _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (rx_timer_head Env.peekNextSite; exact boundaryLift_kernel _ peekNextSite_sameKernel)
  | (rx_timer_head Env.deliverSent; exact boundaryLift_kernel _ deliverSent_sameKernel)
  | (rx_timer_head throw; exact boundaryLift_kernel _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      cases hr))
  | (audit_contract_head liftPrefix; exact boundaryLift_kernel _ (by
      intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (rx_timer_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
  | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => BoundaryInv h w) (hs := fun _ _ _ hi => hi.safe)))

def runTimers (jPass : UInt64) : Obs Bool := do
  liftPrefix (modifyWG fun w => { w with queuedThisCall := [] })   -- the guest slept
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer
  -- exists; a timer section in the records stays unconsumed and mismatches
  if (← liftPrefix getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  -- record-driven (review item 7): every turn consumes a section or breaks
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← audit getDevSavedAudit
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          audit (requireStepCompleteAudit b)
          step := none
        if d.clearWorkQueue.isEmpty then break
        audit runOneClearWorkerAudit
      else
        let some (pid, t, we) ← audit (wheelNextDueAudit d jPass)
          | liftPrefix (throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}"))
        audit (timerDispatchAudit w pid t we step)
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        audit (requireStepCompleteAudit b)
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then audit runOneSendWorkerAudit
      else
        -- the crypt work a timer queued, as the records order it, and a crypt
        -- activation the records resume after a section (`schedule`)
        runCryptWorkers
        if (← liftPrefix Env.peekNextSite) == some site then break
  if let some b := step then audit (requireStepCompleteAudit b)
  if fired then
    liftPrefix Env.deliverSent
    let d ← audit getDevSavedAudit
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

theorem runTimers_erases (jHi : UInt64) : ErasesPrefix (runTimers jHi) (Env.runTimers jHi) := by
  rw [← Environment.runTimersSource_eq]
  unfold runTimers Environment.runTimersSource
  repeat' first
    | maintenance_intro
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound timerDispatchAudit; exact timer_audit_suffix_erases _ _ _
        (timerDispatchAudit_suffix_erases _ _ _ _ _ _))
    | (rx_timer_head getDevSavedAudit; exact audit_erases getDevSavedAudit_erases)
    | (rx_timer_bound wheelNextDueAudit; apply erasesPrefix_bind_pure (audit_erases (wheelNextDueAudit_erases _ _)))
    | (rx_timer_head requireStepCompleteAudit; exact audit_erases (requireStepCompleteAudit_erases _))
    | (rx_timer_head runOneClearWorkerAudit; exact audit_erases runOneClearWorkerAudit_erases)
    | (rx_timer_head runOneSendWorkerAudit; exact audit_erases runOneSendWorkerAudit_erases)
    | (rx_timer_head runCryptWorkers; exact runCryptWorkers_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (maintenance_head ite; apply erasesPrefix_ite)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | timer_audit_cases
    | (with_reducible split)

theorem runTimers_preserves (jHi : UInt64) : PrefixPreserves BoundaryInv BoundarySafe (runTimers jHi) := by
  have getSaved : PrefixEnsures BoundaryInv BoundarySafe (audit getDevSavedAudit)
      (fun d h w => BoundaryInv h w ∧ SavedPeers d.peers.toList (identityView w.wg)) :=
    (timer_audit_ensures _ (fun _ => True) (fun d w => SavedPeers d.peers.toList (identityView w.wg))
      (getDevSavedAudit_spec.consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi))).consequence
      (fun _ _ hi => ⟨hi, trivial⟩) (fun _ _ _ hi => hi)
  have wheel (d : Device) (j : UInt64) : PrefixEnsures
      (fun h w => BoundaryInv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
      BoundarySafe (audit (wheelNextDueAudit d j)) (fun _ => BoundaryInv) :=
    (timer_audit_ensures _ (fun w => SavedPeers d.peers.toList (identityView w.wg)) (fun _ _ => True)
      ((wheelNextDueAudit_spec d j).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi, trivial⟩))).consequence
      (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)
  apply PrefixEnsures.preserves
  unfold runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (rx_timer_drop_saved; apply PrefixEnsures.bind getSaved)
        | apply PrefixEnsures.bind getSaved)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel _ _))
    | (rx_timer_drop_saved; rx_timer_calls)
    | rx_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | (rx_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (rx_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimers_projects (jHi : UInt64) :
    ProjectsUnder AuditInv auditEvent (runTimers jHi) (runTimersAudit jHi) := by
  have getProjects : ProjectsUnder AuditInv auditEvent (audit getDevSavedAudit) getDevSavedAudit :=
    audit_projects (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1))
  have wheelProjects (d : Device) (j : UInt64) :
      ProjectsUnder (fun h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
        auditEvent (audit (wheelNextDueAudit d j)) (wheelNextDueAudit d j) :=
    projectsUnder_focus Event.audit auditEvent (fun _ => rfl) (fun w h hi =>
      let ⟨suffix, hs, _, _⟩ := wheelNextDueAudit_spec d j w h hi; ⟨suffix, hs⟩)
  unfold runTimers runTimersAudit
  repeat' first
    | rx_timer_projects_reduce
    | (audit_contract ProjectsUnder; first
        | (rx_timer_bound getDevSavedAudit; apply timer_projects_bind getProjects getDevSavedAudit_spec)
        | (rx_timer_bound wheelNextDueAudit; apply timer_projects_bind (wheelProjects _ _) (wheelNextDueAudit_spec _ _))
        | (rx_timer_projects_saved_pre
           first
           | rx_timer_head Bind.bind
           | rx_timer_head Pure.pure
           | rx_timer_head timerDispatchAudit
           | rx_timer_head requireStepCompleteAudit
           | rx_timer_head runOneClearWorkerAudit
           | rx_timer_head runOneSendWorkerAudit
           | rx_timer_head runCryptWorkers
           apply timer_projects_weaken (I := AuditInv) (fun _ _ hi => hi.1))
        | (rx_timer_head timerDispatchAudit; exact audit_projects (timerDispatchAudit_preserves _ _ _ _ _))
        | (rx_timer_head requireStepCompleteAudit; exact audit_projects (requireStepCompleteAudit_preserves _))
        | (rx_timer_head runOneClearWorkerAudit; exact audit_projects runOneClearWorkerAudit_preserves)
        | (rx_timer_head runOneSendWorkerAudit; exact audit_projects runOneSendWorkerAudit_preserves)
        | (rx_timer_head runCryptWorkers; exact runCryptWorkers_projects)
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (rx_timer_head Pure.pure; exact projectsUnder_pure _ _)
        | (rx_timer_head ForIn.forIn; apply projectsUnder_range)
        | (rx_timer_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; apply PrefixEnsures.preserves)
    | (audit_contract PrefixEnsures; first
        | contradiction
        | timer_audit_stopped
        | (timer_audit_bound getDevSavedAudit; first
            | apply PrefixEnsures.bind getDevSavedAudit_spec
            | (timer_audit_drop_saved; apply PrefixEnsures.bind getDevSavedAudit_spec))
        | (timer_audit_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheelNextDueAudit_spec _ _))
        | (audit_contract_head timerDispatchAudit; exact timerDispatchAudit_preserves _ _ _ _ _)
        | timer_audit_calls
        | (timer_audit_drop_saved; timer_audit_calls)
        | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
        | (timer_audit_drop_saved; maintenance_join_let)
        | maintenance_join_let
        | (timer_audit_drop_saved; maintenance_join_use)
        | maintenance_join_use)
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

def placeholderSourceWithPass (jHi : UInt64) : Leanux.M Unit := do
  modifyWG fun w => { w with queuedThisCall := [] }
  if (← getWG).dev.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  -- the filter's own loop (review item 7): one turn per pending timer at most
  placeholderTimerPassSource jHi
  Env.runCryptWorkers
  Env.runSendWorkers
  for _ in [0:(← getDev).clearWorkQueue.length + 1] do
    if (← getDev).clearWorkQueue.isEmpty then break
    Env.runOneClearWorker

def placeholderAuditWithPass (jHi : UInt64) : AuditM Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return
  placeholderTimerPassAudit jHi
  runCryptWorkersAudit
  runSendWorkersAudit
  for _ in [0:(← getDevSavedAudit).clearWorkQueue.length + 1] do
    if (← getDevSavedAudit).clearWorkQueue.isEmpty then break
    runOneClearWorkerAudit

theorem placeholderSource_eq (jHi : UInt64) :
    placeholderSourceWithPass jHi = Env.runTimersPlaceholder jHi := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  simp only [placeholderSourceWithPass, placeholderTimerPassSource,
    Environment.runTimersPlaceholderSource, bind_assoc, pure_bind]
  rfl

theorem placeholderAudit_eq (jHi : UInt64) :
    placeholderAuditWithPass jHi = runTimersPlaceholderAudit jHi := by
  simp only [placeholderAuditWithPass, placeholderTimerPassAudit,
    runTimersPlaceholderAudit, bind_assoc, pure_bind]
  rfl

/-- The reset and absent-device return precede the focused pass; its worker
suffix remains concrete and observes every poll it actually reaches. -/
def runTimersPlaceholder (jHi : UInt64) : Obs Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return
  audit (placeholderTimerPassAudit jHi)
  runCryptWorkers
  runSendWorkers
  for _ in [0:(← audit getDevSavedAudit).clearWorkQueue.length + 1] do
    if (← audit getDevSavedAudit).clearWorkQueue.isEmpty then break
    audit runOneClearWorkerAudit

theorem runTimersPlaceholder_erases (jHi : UInt64) :
    ErasesPrefix (runTimersPlaceholder jHi) (Env.runTimersPlaceholder jHi) := by
  rw [← placeholderSource_eq]
  unfold runTimersPlaceholder placeholderSourceWithPass
  repeat' first
    | (rx_timer_head runTimers; exact runTimers_erases _)
    | (rx_timer_head placeholderTimerPassAudit; exact audit_erases (placeholderTimerPass_erases _))
    | (rx_timer_head getDevSavedAudit; exact audit_erases getDevSavedAudit_erases)
    | (rx_timer_head requireNothingDueAudit; exact audit_erases (requireNothingDueAudit_erases _))
    | (rx_timer_head runCryptWorkers; exact runCryptWorkers_erases)
    | (rx_timer_head runSendWorkers; exact runSendWorkers_erases)
    | (rx_timer_head runOneClearWorkerAudit; exact audit_erases runOneClearWorkerAudit_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem runTimersPlaceholder_preserves (jHi : UInt64) :
    PrefixPreserves BoundaryInv BoundarySafe (runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold runTimersPlaceholder
  repeat' first
    | (rx_timer_head runTimers; exact runTimers_preserves _)
    | (rx_timer_head getDevSavedAudit; exact audit_preserves _
        (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)))
    | rx_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem runTimersPlaceholder_projects (jHi : UInt64) :
    ProjectsUnder AuditInv auditEvent (runTimersPlaceholder jHi) (runTimersPlaceholderAudit jHi) := by
  rw [← placeholderAudit_eq]
  unfold runTimersPlaceholder placeholderAuditWithPass
  repeat' first
    | rx_timer_projects_reduce
    | (audit_contract ProjectsUnder; first
        | (rx_timer_head runTimers; exact runTimers_projects _)
        | (rx_timer_head placeholderTimerPassAudit; exact audit_projects (placeholderTimerPass_preserves _))
        | (rx_timer_head getDevSavedAudit; exact audit_projects
            (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)))
        | (rx_timer_head requireNothingDueAudit; exact audit_projects (requireNothingDueAudit_preserves _))
        | (rx_timer_head runCryptWorkers; exact runCryptWorkers_projects)
        | (rx_timer_head runSendWorkers; exact runSendWorkers_projects)
        | (rx_timer_head runOneClearWorkerAudit; exact audit_projects runOneClearWorkerAudit_preserves)
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (rx_timer_head Pure.pure; exact projectsUnder_pure _ _)
        | (rx_timer_head ForIn.forIn; apply projectsUnder_range)
        | (rx_timer_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; apply PrefixEnsures.preserves)
    | (audit_contract PrefixEnsures; first
        | (rx_timer_head runTimersAudit; exact runTimersAudit_preserves _)
        | (rx_timer_head placeholderTimerPassAudit; exact placeholderTimerPass_preserves _)
        | (rx_timer_head getDevSavedAudit; exact getDevSavedAudit_spec.consequence
            (fun _ _ hi => hi) (fun _ _ _ hi => hi.1))
        | timer_audit_calls
        | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
        | maintenance_join_let
        | maintenance_join_use)
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

def idleTimers : Obs Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| runTimers jEnd
  audit (requireNothingDueAudit jEnd)
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => { w with jiffiesLast := some j })

theorem idleTimers_erases : ErasesPrefix idleTimers Env.idleTimers := by
  unfold idleTimers Env.idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (rx_timer_head runTimers; exact runTimers_erases _)
    | (rx_timer_head runTimersPlaceholder; exact runTimersPlaceholder_erases _)
    | (rx_timer_head placeholderTimerPassAudit; exact audit_erases (placeholderTimerPass_erases _))
    | (rx_timer_head getDevSavedAudit; exact audit_erases getDevSavedAudit_erases)
    | (rx_timer_head requireNothingDueAudit; exact audit_erases (requireNothingDueAudit_erases _))
    | (rx_timer_head runCryptWorkers; exact runCryptWorkers_erases)
    | (rx_timer_head runSendWorkers; exact runSendWorkers_erases)
    | (rx_timer_head runOneClearWorkerAudit; exact audit_erases runOneClearWorkerAudit_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem idleTimers_preserves : PrefixPreserves BoundaryInv BoundarySafe idleTimers := by
  apply PrefixEnsures.preserves
  unfold idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (rx_timer_head runTimers; exact runTimers_preserves _)
    | (rx_timer_head runTimersPlaceholder; exact runTimersPlaceholder_preserves _)
    | (rx_timer_head getDevSavedAudit; exact audit_preserves _
        (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)))
    | rx_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem idleTimers_projects : ProjectsUnder AuditInv auditEvent idleTimers idleTimersAudit := by
  unfold idleTimers idleTimersAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | rx_timer_projects_reduce
    | (audit_contract ProjectsUnder; first
        | (rx_timer_head runTimers; exact runTimers_projects _)
        | (rx_timer_head runTimersPlaceholder; exact runTimersPlaceholder_projects _)
        | (rx_timer_head placeholderTimerPassAudit; exact audit_projects (placeholderTimerPass_preserves _))
        | (rx_timer_head getDevSavedAudit; exact audit_projects
            (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)))
        | (rx_timer_head requireNothingDueAudit; exact audit_projects (requireNothingDueAudit_preserves _))
        | (rx_timer_head runCryptWorkers; exact runCryptWorkers_projects)
        | (rx_timer_head runSendWorkers; exact runSendWorkers_projects)
        | (rx_timer_head runOneClearWorkerAudit; exact audit_projects runOneClearWorkerAudit_preserves)
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (rx_timer_head Pure.pure; exact projectsUnder_pure _ _)
        | (rx_timer_head ForIn.forIn; apply projectsUnder_range)
        | (rx_timer_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; apply PrefixEnsures.preserves)
    | (audit_contract PrefixEnsures; first
        | (rx_timer_head runTimersAudit; exact runTimersAudit_preserves _)
        | (rx_timer_head runTimersPlaceholderAudit; exact runTimersPlaceholderAudit_preserves _)
        | (rx_timer_head placeholderTimerPassAudit; exact placeholderTimerPass_preserves _)
        | (rx_timer_head getDevSavedAudit; exact getDevSavedAudit_spec.consequence
            (fun _ _ hi => hi) (fun _ _ _ hi => hi.1))
        | timer_audit_calls
        | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
        | maintenance_join_let
        | maintenance_join_use)
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

def afterAdvance : Obs Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    -- the domain filter's prediction (no records): the fixture's wait
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
    return
  -- review item 7: the window ends at the recorded end of the advance's wait
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  let some (j0, j1) := (← liftPrefix getEnv).lastAdvance | liftPrefix (invariant "afterAdvance without an advance")
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| runTimers jPass
  audit (requireNothingDueAudit jPass)
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => { w with jiffiesLast := some j })

theorem afterAdvance_erases : ErasesPrefix afterAdvance Env.afterAdvance := by
  unfold afterAdvance Env.afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (rx_timer_head runTimers; exact runTimers_erases _)
    | (rx_timer_head runTimersPlaceholder; exact runTimersPlaceholder_erases _)
    | (rx_timer_head placeholderTimerPassAudit; exact audit_erases (placeholderTimerPass_erases _))
    | (rx_timer_head getDevSavedAudit; exact audit_erases getDevSavedAudit_erases)
    | (rx_timer_head requireNothingDueAudit; exact audit_erases (requireNothingDueAudit_erases _))
    | (rx_timer_head runCryptWorkers; exact runCryptWorkers_erases)
    | (rx_timer_head runSendWorkers; exact runSendWorkers_erases)
    | (rx_timer_head runOneClearWorkerAudit; exact audit_erases runOneClearWorkerAudit_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem afterAdvance_preserves : PrefixPreserves BoundaryInv BoundarySafe afterAdvance := by
  apply PrefixEnsures.preserves
  unfold afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (rx_timer_head runTimers; exact runTimers_preserves _)
    | (rx_timer_head runTimersPlaceholder; exact runTimersPlaceholder_preserves _)
    | (rx_timer_head getDevSavedAudit; exact audit_preserves _
        (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)))
    | rx_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem afterAdvance_projects : ProjectsUnder AuditInv auditEvent afterAdvance afterAdvanceAudit := by
  unfold afterAdvance afterAdvanceAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | rx_timer_projects_reduce
    | (audit_contract ProjectsUnder; first
        | (rx_timer_head runTimers; exact runTimers_projects _)
        | (rx_timer_head runTimersPlaceholder; exact runTimersPlaceholder_projects _)
        | (rx_timer_head placeholderTimerPassAudit; exact audit_projects (placeholderTimerPass_preserves _))
        | (rx_timer_head getDevSavedAudit; exact audit_projects
            (getDevSavedAudit_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)))
        | (rx_timer_head requireNothingDueAudit; exact audit_projects (requireNothingDueAudit_preserves _))
        | (rx_timer_head runCryptWorkers; exact runCryptWorkers_projects)
        | (rx_timer_head runSendWorkers; exact runSendWorkers_projects)
        | (rx_timer_head runOneClearWorkerAudit; exact audit_projects runOneClearWorkerAudit_preserves)
        | (audit_contract_head liftPrefix; exact projectsUnder_lift _ _)
        | (rx_timer_head Pure.pure; exact projectsUnder_pure _ _)
        | (rx_timer_head ForIn.forIn; apply projectsUnder_range)
        | (rx_timer_head Bind.bind; apply projectsUnder_bind))
    | (audit_contract PrefixPreserves; apply PrefixEnsures.preserves)
    | (audit_contract PrefixEnsures; first
        | (rx_timer_head runTimersAudit; exact runTimersAudit_preserves _)
        | (rx_timer_head runTimersPlaceholderAudit; exact runTimersPlaceholderAudit_preserves _)
        | (rx_timer_head placeholderTimerPassAudit; exact placeholderTimerPass_preserves _)
        | (rx_timer_head getDevSavedAudit; exact getDevSavedAudit_spec.consequence
            (fun _ _ hi => hi) (fun _ _ _ hi => hi.1))
        | timer_audit_calls
        | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
        | maintenance_join_let
        | maintenance_join_use)
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

/-- Every deferred-call constructor is explicit. Only inspected poll-free
cases focus their existing audit; worker/timer cases use concrete observers. -/
def deferred : (call : EnvDeferredCall) → Obs call.Result
  | .drained what queues => audit (EnvDeferredCall.observed (.drained what queues))
  | .idleDevice => audit (EnvDeferredCall.observed .idleDevice)
  | .noCrypt => audit (EnvDeferredCall.observed .noCrypt)
  | .crypt => runCryptWorkers
  | .sendOne => audit (EnvDeferredCall.observed .sendOne)
  | .clearOne => audit (EnvDeferredCall.observed .clearOne)
  | .sendAll => runSendWorkers
  | .afterXmit => afterXmit
  | .timerWorker timer => audit (EnvDeferredCall.observed (.timerWorker timer))
  | .timers jHi => runTimers jHi
  | .placeholder jHi => runTimersPlaceholder jHi
  | .idle => idleTimers
  | .advance ticks => audit (EnvDeferredCall.observed (.advance ticks))
  | .afterAdvance => afterAdvance

theorem deferred_erases (call : EnvDeferredCall) :
    ErasesPrefix (deferred call) call.original := by
  cases call with
  | drained what queues => exact audit_erases (EnvDeferredCall.erases (.drained what queues))
  | idleDevice => exact audit_erases (EnvDeferredCall.erases .idleDevice)
  | noCrypt => exact audit_erases (EnvDeferredCall.erases .noCrypt)
  | crypt => exact runCryptWorkers_erases
  | sendOne => exact audit_erases (EnvDeferredCall.erases .sendOne)
  | clearOne => exact audit_erases (EnvDeferredCall.erases .clearOne)
  | sendAll => exact runSendWorkers_erases
  | afterXmit => exact afterXmit_erases
  | timerWorker timer => exact audit_erases (EnvDeferredCall.erases (.timerWorker timer))
  | timers jHi => exact runTimers_erases jHi
  | placeholder jHi => exact runTimersPlaceholder_erases jHi
  | idle => exact idleTimers_erases
  | advance ticks => exact audit_erases (EnvDeferredCall.erases (.advance ticks))
  | afterAdvance => exact afterAdvance_erases

theorem deferred_projects (call : EnvDeferredCall) :
    ProjectsUnder AuditInv auditEvent (deferred call) call.observed := by
  cases call with
  | drained what queues => exact audit_projects (EnvDeferredCall.preserves (.drained what queues))
  | idleDevice => exact audit_projects (EnvDeferredCall.preserves .idleDevice)
  | noCrypt => exact audit_projects (EnvDeferredCall.preserves .noCrypt)
  | crypt => exact runCryptWorkers_projects
  | sendOne => exact audit_projects (EnvDeferredCall.preserves .sendOne)
  | clearOne => exact audit_projects (EnvDeferredCall.preserves .clearOne)
  | sendAll => exact runSendWorkers_projects
  | afterXmit => exact afterXmit_projects
  | timerWorker timer => exact audit_projects (EnvDeferredCall.preserves (.timerWorker timer))
  | timers jHi => exact runTimers_projects jHi
  | placeholder jHi => exact runTimersPlaceholder_projects jHi
  | idle => exact idleTimers_projects
  | advance ticks => exact audit_projects (EnvDeferredCall.preserves (.advance ticks))
  | afterAdvance => exact afterAdvance_projects

theorem deferred_preserves (call : EnvDeferredCall) :
    PrefixPreserves BoundaryInv BoundarySafe (deferred call) := by
  cases call with
  | drained what queues => exact audit_preserves _ (EnvDeferredCall.preserves (.drained what queues))
  | idleDevice => exact audit_preserves _ (EnvDeferredCall.preserves .idleDevice)
  | noCrypt => exact audit_preserves _ (EnvDeferredCall.preserves .noCrypt)
  | crypt => exact runCryptWorkers_preserves
  | sendOne => exact audit_preserves _ (EnvDeferredCall.preserves .sendOne)
  | clearOne => exact audit_preserves _ (EnvDeferredCall.preserves .clearOne)
  | sendAll => exact runSendWorkers_preserves
  | afterXmit => exact afterXmit_preserves
  | timerWorker timer => exact audit_preserves _ (EnvDeferredCall.preserves (.timerWorker timer))
  | timers jHi => exact runTimers_preserves jHi
  | placeholder jHi => exact runTimersPlaceholder_preserves jHi
  | idle => exact idleTimers_preserves
  | advance ticks => exact audit_preserves _ (EnvDeferredCall.preserves (.advance ticks))
  | afterAdvance => exact afterAdvance_preserves

end Leanux.Proofs.WG.Queues.RxHistory
