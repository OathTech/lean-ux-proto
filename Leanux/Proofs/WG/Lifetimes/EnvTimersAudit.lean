import Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks
import Leanux.Proofs.WG.Environment.TimerSource
import Leanux.Proofs.Logged.TimerPass

/-! Actual timer-wheel environment calls, including their saved-peer scans,
bucket ordering, dispatch records, step guards and end-of-wait guards.
The removed raw-expiry fire operation is not an alternative execution path. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

abbrev getDevSavedAudit : AuditM Device :=
  auditFocus (liftWGObserver (liftWGPrefix getDev))

theorem getDevSavedAudit_erases :
    ErasesPrefix getDevSavedAudit (liftWG getDev) :=
  auditFocus_erases (liftWGObserver_erases (erasesStatePrefix_lift _))

theorem getDevSavedAudit_spec : PrefixEnsures AuditInv AuditSafe getDevSavedAudit
    (fun d h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w.wg)) :=
  (auditFocus_ensures (getDev_saved_spec_product
    (ProductAmbientContracts.ofNative allocationAmbient) (fun _ => True))).consequence
    (fun _ _ hi => ⟨⟨hi.1, trivial⟩, hi.2⟩)
    (fun _ _ _ hi => ⟨⟨hi.1.1, hi.2⟩, hi.1.2.2⟩)

/-- The optional-device getter supplies a saved-map receipt without inserting
another getter or changing the missing-device return. -/
private theorem getWG_savedAudit_spec :
    PrefixEnsures AuditInv AuditSafe (liftPrefix getWG)
      (fun g h w => AuditInv h w ∧
        ∀ d, g.dev = some d → SavedPeers d.peers.toList (identityView w.wg)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w g v hi hr
  cases hr
  refine ⟨hi, ?_⟩
  intro d hd id p hp
  have entry := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
  simp [identityView, Peers.snapshot, hd, entry]

def wheelDueAudit (d : Device) (j : UInt64) : AuditM (List (PeerId × PeerTimer × WheelEntry)) :=
  auditFocus (liftWGObserver (savedPeerLookupFlatMap d.peers (fun pid p =>
    PeerTimer.all.filterMap fun t => (p.wheel t).bind fun we =>
      if timeBeforeEq we.bucketExpiry j then some (pid, t, we) else none) d.peerList))

theorem wheelDueAudit_erases (d : Device) (j : UInt64) :
    ErasesPrefix (wheelDueAudit d j) (pure (TimerWheel.due d j)) := by
  have he := auditFocus_erases (liftWGObserver_erases (savedPeerLookupFlatMap_erases d.peers
    (fun pid p => PeerTimer.all.filterMap fun t => (p.wheel t).bind fun we =>
      if timeBeforeEq we.bucketExpiry j then some (pid, t, we) else none) d.peerList))
  have eqs : d.peerList.flatMap (fun pid => (d.peers[pid]?).toList.flatMap (fun p =>
      PeerTimer.all.filterMap fun t => (p.wheel t).bind fun we =>
        if timeBeforeEq we.bucketExpiry j then some (pid, t, we) else none)) = TimerWheel.due d j := by
    unfold TimerWheel.due
    apply congrArg (fun f => d.peerList.flatMap f)
    funext pid
    cases hp : d.peers[pid]? <;> simp [Std.TreeMap.get?_eq_getElem?, hp]
  simpa only [wheelDueAudit, liftWG_pure, eqs] using he

theorem wheelDueAudit_spec (d : Device) (j : UInt64) :
    PrefixEnsures (fun h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
      AuditSafe (wheelDueAudit d j) (fun _ => AuditInv) :=
  (auditFocus_ensures (savedPeerLookupFlatMap_spec_product
    (ProductAmbientContracts.ofNative allocationAmbient) (fun _ => True) d.peers _ _)).consequence
    (fun _ _ hi => ⟨⟨hi.1.1, trivial, hi.2⟩, hi.1.2⟩)
    (fun _ _ _ hi => ⟨hi.1.1, hi.2⟩)

def wheelNextDueAudit (d : Device) (j : UInt64) : AuditM (Option (PeerId × PeerTimer × WheelEntry)) := do
  let due ← wheelDueAudit d j
  return due.foldl (fun acc c => match acc with
    | none => some c
    | some a => if TimerWheel.runsBefore c.2.2 a.2.2 then some c else some a) none

theorem wheelNextDueAudit_erases (d : Device) (j : UInt64) :
    ErasesPrefix (wheelNextDueAudit d j) (pure (TimerWheel.nextDue d j)) :=
  erasesPrefix_bind_pure (wheelDueAudit_erases d j) (erasesPrefix_pure _)

theorem wheelNextDueAudit_spec (d : Device) (j : UInt64) :
    PrefixEnsures (fun h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
      AuditSafe (wheelNextDueAudit d j) (fun _ => AuditInv) :=
  PrefixEnsures.bind (wheelDueAudit_spec d j) (fun _ =>
    PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))

/-- Apply the ordinary composition rule only to the actual leading action. -/
elab "timer_audit_bound " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless (ty.isAppOf ``PrefixEnsures || ty.isAppOf ``ErasesPrefix) && args.size ≥ 2 do
    Lean.throwError "not a prefix contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let bound := action.getAppArgs
  unless bound.size ≥ 2 do Lean.throwError "missing action"
  let .const actual _ := bound[bound.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a named bound action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different bound action"

elab "timer_audit_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
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
        | .lam .. => let e' := e.headBeta; if Lean.Expr.equal e e' then e else head n e'
        | _ => e
  let .app (.app front observed) post := target | Lean.throwError "missing observer"
  let observed' := head 64 observed
  let post' := if target.isAppOf ``ErasesPrefix then head 64 post else post
  if Lean.Expr.equal observed observed' && Lean.Expr.equal post post' then Lean.throwError "unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp2 front observed' post')]

elab "timer_audit_reduce_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let .app (.app f observed) last := target | Lean.throwError "missing action"
  let reduce (action : Lean.Expr) : Lean.MetaM Lean.Expr := do
    if (← Lean.Meta.matchMatcherApp? action).isSome then
      if let .reduced next ← Lean.Meta.reduceMatcher? action then return next
    return action
  let observed' ←
    if observed.isAppOf ``liftWGObserver then
      match observed with
      | .app outer inner => do pure (Lean.mkApp outer (← reduce inner))
      | _ => pure observed
    else reduce observed
  let last' ← if target.isAppOf ``ErasesPrefix then reduce last else pure last
  if Lean.Expr.equal observed observed' && Lean.Expr.equal last last' then
    Lean.throwError "no reducible head matcher"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (.app (.app f observed') last')]

elab "timer_audit_erases_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesPrefix do Lean.throwError "not an erasure"
  let .app (.app front observed) original := target | Lean.throwError "missing actions"
  let .letE oname oty oval obody _ := observed.consumeMData | Lean.throwError "not an observer let"
  let .letE rname rty rval rbody _ := original.consumeMData | Lean.throwError "not a source let"
  unless oname.toString.startsWith "__do_jp" && rname.toString.startsWith "__do_jp" do
    Lean.throwError "not paired joins"
  let property (g a : Lean.Expr) := Lean.mkApp2 front g a
  let valueContract ← Lean.Meta.forallTelescope oty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN oval args) (Lean.mkAppN rval args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD oname oty fun g => do
    Lean.Meta.withLocalDeclD rname rty fun a => do
      let contract ← Lean.Meta.forallTelescope oty fun args _ => do
        Lean.Meta.mkForallFVars args (property (Lean.mkAppN g args) (Lean.mkAppN a args))
      Lean.Meta.withLocalDeclD `timer_audit_erasure_join contract fun hg => do
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (property (obody.instantiate1 g) (rbody.instantiate1 a))
        let proof ← Lean.Meta.mkLambdaFVars #[g, a, hg] next
        pure (proof, next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[oval, rval, valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "timer_audit_erases_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesPrefix do Lean.throwError "not an erasure"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!.consumeMData
  let original := args.back!.consumeMData
  unless observed.getAppFn.isFVar && original.getAppFn.isFVar do
    Lean.throwError "not paired local continuations"
  for decl in ← Lean.getLCtx do
    if decl.userName == `timer_audit_erasure_join then
      let proof := Lean.mkAppN decl.toExpr observed.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no paired continuation contract"

elab "timer_audit_focus_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not a contract"
  let action := (if ty.isAppOf ``PrefixPreserves then args.back! else args[args.size - 2]!).consumeMData
  unless action.isAppOf ``auditFocus do Lean.throwError "not focused"
  let lifted := action.getAppArgs.back!.consumeMData
  unless lifted.isAppOf ``liftWGObserver do Lean.throwError "not a native observer"
  let .const actual _ := lifted.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a named native observer"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different native observer"

elab "timer_audit_stopped" : tactic => Lean.Elab.Tactic.withMainContext do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not a contract"
  let action := (if ty.isAppOf ``PrefixPreserves then args.back! else args[args.size - 2]!).consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let bound := action.getAppArgs
  unless bound.size ≥ 2 do Lean.throwError "missing first action"
  let lifted := bound[bound.size - 2]!.consumeMData
  unless lifted.isAppOf ``liftPrefix do Lean.throwError "not a lift"
  let .const name _ := lifted.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a named failing action"
  unless name.toString == "throw" || name.toString.endsWith ".throw" do
    Lean.throwError "not a throw"
  if ty.isAppOf ``ErasesPrefix then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro w h; rfl))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (intro w h hi
       refine ⟨[], (List.append_nil h).symm, ?_, True.intro⟩
       first | exact hi.safe | exact hi.1.safe)))

macro "timer_audit_store" : tactic => `(tactic|
  first
  | (audit_contract_head getWG; exact auditLift_store _ (by
      intro initial
      exact productGetWG_spec (fun store => store.2.2.2 = initial)))
  | (audit_contract_head getEnv; exact auditLift_store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      cases hr
      rfl))
  | (audit_contract_head modifyWG; exact auditLift_store _ (by
      intro initial
      exact productModifyWG_spec (fun store => store.2.2.2 = initial) _ (fun _ => rfl)))
  | (audit_contract_head Env.sectionAppearsLater; exact auditLift_store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      cases hr
      rfl))
  | (audit_contract_head Env.peekNextSite; exact auditLift_store _
      (peekNextSite_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
        (fun w => wgStoreView w.wg) (fun _ => rfl)))
  | (audit_contract_head Env.timerWorker; exact auditLift_store _
      ((timerWorker_sameKernel _).of_factor (fun s : ProductStore43 => s.2.2.2)
        (fun w => wgStoreView w.wg) (fun _ => rfl)))
  | (audit_contract_head Env.deliverSent; exact auditLift_store _
      (deliverSent_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
        (fun w => wgStoreView w.wg) (fun _ => rfl)))
  | (audit_contract_head liftPrefix; first
      | exact auditLift_store _ (by
          intro initial
          exact productAmbient_spec _ _ (fun _ _ hi => hi))
      | exact auditLift_store _ (by
          apply (ProjectedAction.iff_run _ _ _).mpr
          intro w x v hr
          cases hr)))

macro "timer_audit_basic" : tactic => `(tactic|
  first
  | timer_audit_store
  | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
  | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => AuditInv h w) (hs := fun _ _ _ hi => hi.safe))
  | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | (with_reducible split)
  | maintenance_intro)

def requireStepCompleteAudit (b : UInt64) : AuditM Unit := do
  let d ← getDevSavedAudit
  let due ← wheelDueAudit d b
  if let some (pid, t) := (due.find? (fun c => c.2.2.bucketExpiry == b)).map (fun c => (c.1, c.2.1)) then
    liftPrefix (throw (.hidden s!"a timer step split: peer {pid}'s {repr t} timer at bucket expiry {b} is still pending when the records leave the step"))

theorem requireStepCompleteAudit_erases (b : UInt64) :
    ErasesPrefix (requireStepCompleteAudit b) (Env.requireStepComplete b) := by
  unfold requireStepCompleteAudit Env.requireStepComplete TimerWheel.anotherAtStep
  apply erasesPrefix_bind getDevSavedAudit_erases
  intro d
  apply erasesPrefix_bind_pure (wheelDueAudit_erases d b)
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | exact erasesPrefix_pure _
    | (split; all_goals try simp_all only [])
    | (intro x; try dsimp only)

theorem requireStepCompleteAudit_preserves (b : UInt64) :
    PrefixPreserves AuditInv AuditSafe (requireStepCompleteAudit b) := by
  apply PrefixEnsures.preserves
  unfold requireStepCompleteAudit
  apply PrefixEnsures.bind getDevSavedAudit_spec
  intro d
  apply PrefixEnsures.bind (wheelDueAudit_spec d b)
  intro due
  repeat' timer_audit_basic

def requireNothingDueAudit (jPass : UInt64) : AuditM Unit := do
  let some d := (← liftPrefix getWG).dev | return
  let some (pid, t, we) ← wheelNextDueAudit d jPass | return
  let worker ← liftPrefix (Env.timerWorker t)
  let unit := (((← liftPrefix getWG).timerUnits.find? fun e => e.2.1 == pid && e.2.2 == t).map (·.1)).getD 0
  if ← liftPrefix (Env.sectionAppearsLater worker unit) then
    liftPrefix (unsupported s!"a due timer's softirq deferred past the end-of-wait read: peer {pid}'s {repr t} timer (bucket expiry {we.bucketExpiry}, the read {jPass}) fires later in the stream")
  liftPrefix (throw (.hidden s!"a due timer did not fire: peer {pid}'s {repr t} timer, bucket expiry {we.bucketExpiry}, pending at the end-of-wait read {jPass}"))

theorem requireNothingDueAudit_erases (jPass : UInt64) :
    ErasesPrefix (requireNothingDueAudit jPass) (Env.requireNothingDue jPass) := by
  unfold requireNothingDueAudit Env.requireNothingDue
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro g
  cases hd : g.dev with
  | none => exact erasesPrefix_pure _
  | some d =>
    apply erasesPrefix_bind_pure (wheelNextDueAudit_erases d jPass)
    dsimp only
    cases ht : TimerWheel.nextDue d jPass with
    | none => exact erasesPrefix_pure _
    | some entry =>
      rcases entry with ⟨pid, t, we⟩
      repeat' first
        | contradiction
        | timer_audit_stopped
        | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
        | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
        | (maintenance_head Bind.bind; apply erasesPrefix_bind)
        | timer_audit_erases_join
        | timer_audit_erases_join_use
        | timer_audit_reduce
        | timer_audit_reduce_match
        | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq]; all_goals try subst_vars)
        | maintenance_intro

theorem requireNothingDueAudit_preserves (jPass : UInt64) :
    PrefixPreserves AuditInv AuditSafe (requireNothingDueAudit jPass) := by
  apply PrefixEnsures.preserves
  unfold requireNothingDueAudit
  apply PrefixEnsures.bind getWG_savedAudit_spec
  intro g
  cases hd : g.dev with
  | none =>
    exact PrefixEnsures.pure (fun _ _ hi => hi.1.safe) (fun _ _ hi => hi.1)
  | some d =>
    apply PrefixEnsures.bind ((wheelNextDueAudit_spec d jPass).consequence
      (fun _ _ hi => ⟨hi.1, hi.2 d rfl⟩) (fun _ _ _ hi => hi))
    intro due
    repeat' timer_audit_basic

def runTimerSectionAudit (worker : Worker) (body : AuditM Unit) : AuditM Unit := do
  if worker.timer?.isNone then liftPrefix (invariant s!"{worker.symbol} is not a timer callback")
  liftPrefix (modifyAmbient fun s => {s with fired := s.fired.push worker.symbol})
  runWorkerPrefix worker body

theorem runTimerSectionAudit_erases (worker : Worker) (he : ErasesPrefix body originalBody) :
    ErasesPrefix (runTimerSectionAudit worker body) (Env.runTimerSection worker originalBody) := by
  unfold runTimerSectionAudit Env.runTimerSection
  repeat' first
    | contradiction
    | timer_audit_stopped
    | with_reducible exact runWorkerPrefix_erases worker he
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimerSectionAudit_preserves (worker : Worker) (hb : PrefixPreserves AuditInv AuditSafe body) :
    PrefixPreserves AuditInv AuditSafe (runTimerSectionAudit worker body) := by
  apply PrefixEnsures.preserves
  unfold runTimerSectionAudit
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (audit_contract_head runWorkerPrefix; exact runWorkerPrefix_preserves (fun _ _ hi => hi.safe)
        (fun _ _ _ he hi => hi.store (congrArg (fun s : ProductStore43 => s.2.2.2) he)) worker hb)
    | timer_audit_basic

private def timerDispatchAudit (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : AuditM Unit := do
  let expected ← liftPrefix (Env.timerWorker t)
  if w != expected then
    liftPrefix (throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}"))
  -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
  -- section names, by the address its arm record carried
  if let some u ← liftPrefix (peekUnit w) then
    match (← liftPrefix getWG).timerUnits.find? (·.1 == u) with
    | some (_, pid', t') =>
      if pid' != pid || t' != t then
        liftPrefix (throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}"))
    | none => liftPrefix (throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})"))
  if let some b := step then
    if b != we.bucketExpiry then requireStepCompleteAudit b
  auditFocus (liftWGObserver (delTimerPrefix pid t))
  liftPrefix (modifyWG fun s => { s with timerPassStep := some we.bucketExpiry })
  runTimerSectionAudit w (auditFocus (liftWGObserver (timerCallbackPrefix pid t)))
  liftPrefix (modifyWG fun s => { s with timerPassStep := none })

def runTimersAudit (jPass : UInt64) : AuditM Bool := do
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
    let d ← getDevSavedAudit
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          requireStepCompleteAudit b
          step := none
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorkerAudit
      else
        let some (pid, t, we) ← wheelNextDueAudit d jPass
          | liftPrefix (throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}"))
        timerDispatchAudit w pid t we step
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        requireStepCompleteAudit b
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorkerAudit
      else
        -- the crypt work a timer queued, as the records order it, and a crypt
        -- activation the records resume after a section (`schedule`)
        runCryptWorkersAudit
        if (← liftPrefix Env.peekNextSite) == some site then break
  if let some b := step then requireStepCompleteAudit b
  if fired then
    liftPrefix Env.deliverSent
    let d ← getDevSavedAudit
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

def runTimersPlaceholderAudit (jHi : UInt64) : AuditM Unit := do
  liftPrefix (modifyWG fun w => { w with queuedThisCall := [] })
  if (← liftPrefix getWG).dev.isNone then return   -- no device, no timers
  -- the filter's own loop (review item 7): one turn per pending timer at most
  let pending := (← getDevSavedAudit).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDevSavedAudit
    let some (pid, t, _) ← wheelNextDueAudit d jHi | break
    auditFocus (liftWGObserver (delTimerPrefix pid t))
    runTimerSectionAudit (← liftPrefix (Env.timerWorker t)) (auditFocus (liftWGObserver (timerCallbackPrefix pid t)))
  runCryptWorkersAudit
  runSendWorkersAudit
  for _ in [0:(← getDevSavedAudit).clearWorkQueue.length + 1] do
    if (← getDevSavedAudit).clearWorkQueue.isEmpty then break
    runOneClearWorkerAudit

def idleTimersAudit : AuditM Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholderAudit jHi else discard <| runTimersAudit jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| runTimersAudit jEnd
  requireNothingDueAudit jEnd
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => { w with jiffiesLast := some j })

abbrev advanceAudit (ticks : Nat) : AuditM Int := liftPrefix (Env.advance ticks)

def afterAdvanceAudit : AuditM Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    -- the domain filter's prediction (no records): the fixture's wait
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholderAudit jHi else discard <| runTimersAudit jHi
    return
  -- review item 7: the window ends at the recorded end of the advance's wait
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  let some (j0, j1) := (← liftPrefix getEnv).lastAdvance | liftPrefix (invariant "afterAdvance without an advance")
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| runTimersAudit jPass
  requireNothingDueAudit jPass
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => { w with jiffiesLast := some j })

elab "timer_audit_saved_pre" : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless ty.isAppOf ``PrefixEnsures && args.size ≥ 4 do Lean.throwError "not a prefix contract"
  let mut pre := args[args.size - 4]!.consumeMData
  for _ in [:2] do
    match pre with
    | .lam _ _ body _ => pre := body.consumeMData
    | _ => pure ()
  unless pre.isAppOf ``And do Lean.throwError "no saved receipt"

macro "timer_audit_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence (P := AuditInv) (Q := fun _ => AuditInv) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "timer_audit_calls" : tactic => `(tactic|
  first
  | (audit_contract_head requireStepCompleteAudit; exact requireStepCompleteAudit_preserves _)
  | (audit_contract_head requireNothingDueAudit; exact requireNothingDueAudit_preserves _)
  | (timer_audit_focus_head delTimerPrefix; exact auditFocus_preserves ((AmbientContracts.drop
      (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _)).liftWGObserver))
  | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_preserves ((timerCallbackPrefix_preserves allocationAmbient
      allocationTx allocationTimerQueue _ _).liftWGObserver))
  | (audit_contract_head runTimerSectionAudit; apply runTimerSectionAudit_preserves)
  | (audit_contract_head runCryptWorkersAudit; exact runCryptWorkersAudit_preserves)
  | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
  | (audit_contract_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
  | (audit_contract_head runOneClearWorkerAudit; exact runOneClearWorkerAudit_preserves)
  | timer_audit_store
  | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
  | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => AuditInv h w) (hs := fun _ _ _ hi => hi.safe)))

private theorem timerDispatchAudit_erases (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    ErasesPrefix (timerDispatchAudit w pid t we step) (timerDispatchUnit w pid t we step) := by
  unfold timerDispatchAudit timerDispatchUnit
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (maintenance_head requireStepCompleteAudit; exact requireStepCompleteAudit_erases _)
    | (timer_audit_focus_head delTimerPrefix; exact auditFocus_erases (liftWGObserver_erases (delTimerPrefix_erases _ _)))
    | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_erases (liftWGObserver_erases (timerCallbackPrefix_erases _ _)))
    | (maintenance_head runTimerSectionAudit; apply runTimerSectionAudit_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (maintenance_head ite; apply erasesPrefix_ite)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

private theorem timerDispatchAudit_preserves (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    PrefixPreserves AuditInv AuditSafe (timerDispatchAudit w pid t we step) := by
  apply PrefixEnsures.preserves
  unfold timerDispatchAudit
  repeat' first
    | contradiction
    | timer_audit_stopped
    | timer_audit_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | (timer_audit_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (timer_audit_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

private theorem timerDispatchAudit_suffix_erases {α : Type} (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (x : α) :
    ErasesPrefix (do timerDispatchAudit w pid t we step; pure x)
      (do
        let expected ← Env.timerWorker t
        if w != expected then
          throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
        -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
        -- section names, by the address its arm record carried
        if let some u ← peekUnit w then
          match (← getWG).timerUnits.find? (·.1 == u) with
          | some (_, pid', t') =>
            if pid' != pid || t' != t then
              throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
          | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
        if let some b := step then
          if b != we.bucketExpiry then Env.requireStepComplete b
        delTimer pid t
        modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
        Env.runTimerSection w (WG.timerCallback pid t)
        modifyWG fun s => { s with timerPassStep := none }
        pure x) := by
  have stopped {α β : Type} (e : Stop) (f : α → Leanux.M β) :
      ((throw e : Leanux.M α) >>= f) = throw e := rfl
  have h := erasesPrefix_bind (timerDispatchAudit_erases w pid t we step) (fun _ => erasesPrefix_pure x)
  refine Eq.mp ?_ h
  congr 1
  unfold timerDispatchUnit
  simp only [bind_assoc, stopped]
  apply bind_congr
  intro expected
  by_cases he : (w != expected) = true
  · simp only [he, ite_true, stopped]
  · simp only [he, Bool.false_eq_true, ite_false, bind_assoc]
    apply bind_congr
    intro unit
    cases unit with
    | none =>
      cases step <;> simp only [bind_assoc]
      all_goals first
        | (solve | simp only [bind_assoc])
        | (split <;> simp only [bind_assoc])
    | some u =>
      simp only [bind_assoc]
      apply bind_congr
      intro state
      cases hn : state.timerUnits.find? (·.1 == u) with
      | none => simp only [stopped]
      | some named =>
        rcases named with ⟨unused, pid', t'⟩
        simp only
        by_cases hd : (pid' != pid || t' != t) = true
        · simp only [hd, ite_true, stopped]
        · simp only [hd, Bool.false_eq_true, ite_false]
          cases step <;> simp only [bind_assoc]
          all_goals first
            | (solve | simp only [bind_assoc])
            | (split <;> simp only [bind_assoc])

elab "timer_audit_cases" : tactic => Lean.Elab.Tactic.withMainContext do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``ErasesPrefix do Lean.throwError "not an erasure"
  let args := ty.getAppArgs
  let some matched ← Lean.Meta.matchMatcherApp? args[args.size - 2]!
    | Lean.throwError "not a head match"
  unless matched.discrs.size == 1 do Lean.throwError "not a single selector"
  let selector ← Lean.PrettyPrinter.delab matched.discrs[0]!
  Lean.Elab.Tactic.evalTactic (← `(tactic| cases htimer : $selector))

theorem runTimersAudit_erases (jPass : UInt64) :
    ErasesPrefix (runTimersAudit jPass) (Env.runTimers jPass) := by
  rw [← Environment.runTimersSource_eq]
  unfold runTimersAudit Environment.runTimersSource
  repeat' first
    | maintenance_intro
    | contradiction
    | timer_audit_stopped
    | (timer_audit_bound timerDispatchAudit; exact timerDispatchAudit_suffix_erases _ _ _ _ _ _)
    | (maintenance_head getDevSavedAudit; exact getDevSavedAudit_erases)
    | (timer_audit_bound wheelNextDueAudit; apply erasesPrefix_bind_pure (wheelNextDueAudit_erases _ _))
    | (maintenance_head requireStepCompleteAudit; exact requireStepCompleteAudit_erases _)
    | (maintenance_head requireNothingDueAudit; exact requireNothingDueAudit_erases _)
    | (timer_audit_focus_head delTimerPrefix; exact auditFocus_erases (liftWGObserver_erases (delTimerPrefix_erases _ _)))
    | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_erases (liftWGObserver_erases (timerCallbackPrefix_erases _ _)))
    | (maintenance_head runTimerSectionAudit; apply runTimerSectionAudit_erases)
    | (maintenance_head runCryptWorkersAudit; exact runCryptWorkersAudit_erases)
    | (maintenance_head runSendWorkersAudit; exact runSendWorkersAudit_erases)
    | (maintenance_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_erases)
    | (maintenance_head runOneClearWorkerAudit; exact runOneClearWorkerAudit_erases)
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

theorem runTimersAudit_preserves (jPass : UInt64) :
    PrefixPreserves AuditInv AuditSafe (runTimersAudit jPass) := by
  apply PrefixEnsures.preserves
  unfold runTimersAudit
  repeat' first
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
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimersPlaceholderAudit_erases (jHi : UInt64) :
    ErasesPrefix (runTimersPlaceholderAudit jHi) (Env.runTimersPlaceholder jHi) := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  unfold runTimersPlaceholderAudit Environment.runTimersPlaceholderSource
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (maintenance_head runTimersAudit; exact runTimersAudit_erases _)
    | (maintenance_head getDevSavedAudit; exact getDevSavedAudit_erases)
    | (timer_audit_bound wheelNextDueAudit; apply erasesPrefix_bind_pure (wheelNextDueAudit_erases _ _))
    | (maintenance_head requireStepCompleteAudit; exact requireStepCompleteAudit_erases _)
    | (maintenance_head requireNothingDueAudit; exact requireNothingDueAudit_erases _)
    | (timer_audit_focus_head delTimerPrefix; exact auditFocus_erases (liftWGObserver_erases (delTimerPrefix_erases _ _)))
    | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_erases (liftWGObserver_erases (timerCallbackPrefix_erases _ _)))
    | (maintenance_head runTimerSectionAudit; apply runTimerSectionAudit_erases)
    | (maintenance_head runCryptWorkersAudit; exact runCryptWorkersAudit_erases)
    | (maintenance_head runSendWorkersAudit; exact runSendWorkersAudit_erases)
    | (maintenance_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_erases)
    | (maintenance_head runOneClearWorkerAudit; exact runOneClearWorkerAudit_erases)
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

theorem runTimersPlaceholderAudit_preserves (jHi : UInt64) :
    PrefixPreserves AuditInv AuditSafe (runTimersPlaceholderAudit jHi) := by
  apply PrefixEnsures.preserves
  unfold runTimersPlaceholderAudit
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (timer_audit_bound getDevSavedAudit; first
        | apply PrefixEnsures.bind getDevSavedAudit_spec
        | (timer_audit_drop_saved; apply PrefixEnsures.bind getDevSavedAudit_spec))
    | (timer_audit_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheelNextDueAudit_spec _ _))
    | (audit_contract_head runTimersAudit; exact runTimersAudit_preserves _)
    | (timer_audit_drop_saved; audit_contract_head runTimersAudit; exact runTimersAudit_preserves _)
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

theorem idleTimersAudit_erases  :
    ErasesPrefix (idleTimersAudit) (Env.idleTimers) := by
  unfold idleTimersAudit Env.idleTimers
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (maintenance_head runTimersPlaceholderAudit; exact runTimersPlaceholderAudit_erases _)
    | (maintenance_head runTimersAudit; exact runTimersAudit_erases _)
    | (maintenance_head getDevSavedAudit; exact getDevSavedAudit_erases)
    | (timer_audit_bound wheelNextDueAudit; apply erasesPrefix_bind_pure (wheelNextDueAudit_erases _ _))
    | (maintenance_head requireStepCompleteAudit; exact requireStepCompleteAudit_erases _)
    | (maintenance_head requireNothingDueAudit; exact requireNothingDueAudit_erases _)
    | (timer_audit_focus_head delTimerPrefix; exact auditFocus_erases (liftWGObserver_erases (delTimerPrefix_erases _ _)))
    | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_erases (liftWGObserver_erases (timerCallbackPrefix_erases _ _)))
    | (maintenance_head runTimerSectionAudit; apply runTimerSectionAudit_erases)
    | (maintenance_head runCryptWorkersAudit; exact runCryptWorkersAudit_erases)
    | (maintenance_head runSendWorkersAudit; exact runSendWorkersAudit_erases)
    | (maintenance_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_erases)
    | (maintenance_head runOneClearWorkerAudit; exact runOneClearWorkerAudit_erases)
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

theorem idleTimersAudit_preserves  :
    PrefixPreserves AuditInv AuditSafe (idleTimersAudit) := by
  apply PrefixEnsures.preserves
  unfold idleTimersAudit
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (timer_audit_bound getDevSavedAudit; first
        | apply PrefixEnsures.bind getDevSavedAudit_spec
        | (timer_audit_drop_saved; apply PrefixEnsures.bind getDevSavedAudit_spec))
    | (timer_audit_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheelNextDueAudit_spec _ _))
    | (audit_contract_head runTimersAudit; exact runTimersAudit_preserves _)
    | (timer_audit_drop_saved; audit_contract_head runTimersAudit; exact runTimersAudit_preserves _)
    | (audit_contract_head runTimersPlaceholderAudit; exact runTimersPlaceholderAudit_preserves _)
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

theorem afterAdvanceAudit_erases  :
    ErasesPrefix (afterAdvanceAudit) (Env.afterAdvance) := by
  unfold afterAdvanceAudit Env.afterAdvance
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (maintenance_head runTimersPlaceholderAudit; exact runTimersPlaceholderAudit_erases _)
    | (maintenance_head runTimersAudit; exact runTimersAudit_erases _)
    | (maintenance_head getDevSavedAudit; exact getDevSavedAudit_erases)
    | (timer_audit_bound wheelNextDueAudit; apply erasesPrefix_bind_pure (wheelNextDueAudit_erases _ _))
    | (maintenance_head requireStepCompleteAudit; exact requireStepCompleteAudit_erases _)
    | (maintenance_head requireNothingDueAudit; exact requireNothingDueAudit_erases _)
    | (timer_audit_focus_head delTimerPrefix; exact auditFocus_erases (liftWGObserver_erases (delTimerPrefix_erases _ _)))
    | (timer_audit_focus_head timerCallbackPrefix; exact auditFocus_erases (liftWGObserver_erases (timerCallbackPrefix_erases _ _)))
    | (maintenance_head runTimerSectionAudit; apply runTimerSectionAudit_erases)
    | (maintenance_head runCryptWorkersAudit; exact runCryptWorkersAudit_erases)
    | (maintenance_head runSendWorkersAudit; exact runSendWorkersAudit_erases)
    | (maintenance_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_erases)
    | (maintenance_head runOneClearWorkerAudit; exact runOneClearWorkerAudit_erases)
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

theorem afterAdvanceAudit_preserves  :
    PrefixPreserves AuditInv AuditSafe (afterAdvanceAudit) := by
  apply PrefixEnsures.preserves
  unfold afterAdvanceAudit
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (timer_audit_bound getDevSavedAudit; first
        | apply PrefixEnsures.bind getDevSavedAudit_spec
        | (timer_audit_drop_saved; apply PrefixEnsures.bind getDevSavedAudit_spec))
    | (timer_audit_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheelNextDueAudit_spec _ _))
    | (audit_contract_head runTimersAudit; exact runTimersAudit_preserves _)
    | (timer_audit_drop_saved; audit_contract_head runTimersAudit; exact runTimersAudit_preserves _)
    | (audit_contract_head runTimersPlaceholderAudit; exact runTimersPlaceholderAudit_preserves _)
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

theorem advanceAudit_erases (ticks : Nat) :
    ErasesPrefix (advanceAudit ticks) (Env.advance ticks) := erasesPrefix_lift _

theorem advanceAudit_preserves (ticks : Nat) :
    PrefixPreserves AuditInv AuditSafe (advanceAudit ticks) :=
  auditLift_store _ ((advance_sameKernel ticks).of_factor
    (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))

end Leanux.Proofs.WG.Lifetimes
