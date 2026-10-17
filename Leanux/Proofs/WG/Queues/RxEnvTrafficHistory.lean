import Leanux.Proofs.WG.Queues.RxEnvWorkersHistory
import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit

/-! Actual environment ingress and every exact flood producer retain nested receive-worker
reschedules. Poll-free ingress steps are focused; every reached reschedule uses
the committed stamped scheduler, with the same prior audit and probe history. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- The original worker callback is reached only after a handled receive item. -/
def handshakeReceiveWorker : Obs Unit :=
  workerLoopPrefix .receiveWorker none Origins.HistoryAdapters.receiveStep (nestedResched .receiveWorker)
    (MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain"

theorem handshakeReceiveWorker_erases : ErasesPrefix handshakeReceiveWorker
    (Leanux.WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoopPrefix_erases _ _ Origins.HistoryAdapters.receiveStep_erases
    (nestedResched_erases _) _ _

theorem handshakeReceiveWorker_preserves : PrefixPreserves BoundaryInv BoundarySafe handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    Origins.HistoryAdapters.receiveStep_preserves (nestedResched_preserves _) _ _

theorem handshakeReceiveWorker_projects : ProjectsUnder AuditInv auditEvent handshakeReceiveWorker
    (handshakeReceiveWorkerAudit (nestedReschedAudit .receiveWorker)) := by
  have hs : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg)
      LifetimeEvent.Safe (liftWGObserver receiveStepPrefix) :=
    (HandshakeReceiveCall.allocation .step).liftWGObserver
  have hp := Origins.HistoryAdapters.receiveStep_projects
  have ha := auditFocus_preserves hs
  unfold handshakeReceiveWorker handshakeReceiveWorkerAudit workerLoopPrefix workerIterPrefix
  repeat' first
    | exact hp
    | exact ha
    | with_reducible exact nestedResched_projects _
    | with_reducible exact nestedReschedAudit_preserves _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | exact auditLift_kernel _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_range (S := AuditSafe)
    | with_reducible apply projectsUnder_bind (S := AuditSafe)
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

def inject (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : Obs Int := do
  if (← liftPrefix getRouting).foreignCreator then
    if (← liftPrefix getEnv).netnsCHolders.isEmpty then liftPrefix (unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)")
    if dest == 1 then liftPrefix (unsupported "wg_inject to wg0's address from the creating namespace (unroutable)")
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a datagram to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a datagram to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "receiving while a handshake is queued"))
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family dest tos ll)
  if family == 4 then
    match ← liftPrefix (Net.Fib.inSocketNs (Net.routeOutput4 0 src.daddr)) with
    | .error _ => liftPrefix (invariant "wg_inject: the injector's datagram has no route")
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then
        liftPrefix (invariant "wg_inject: the route disagrees with the sender source")
      liftPrefix (Net.Fib.inSocketNs (Net.neighbourClassify LO_IFINDEX))
  runWorkerPrefix .netRx (mixed (liftWGObserver (wgReceivePrefix msg src)))
  runCryptWorkers
  let d ← liftPrefix (liftWG getDev)
  mixed (requireDrainedPrefix "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  return msg.length

elab "rx_env_traffic_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  let mut action ←
    if ty.isAppOf ``PrefixPreserves then
      if args.size > 0 then pure args.back! else Lean.throwError "missing observer"
    else if ty.isAppOf ``PrefixEnsures || ty.isAppOf ``ErasesPrefix || ty.isAppOf ``ProjectsUnder then
      if args.size ≥ 2 then pure args[args.size - 2]! else Lean.throwError "missing observer"
    else Lean.throwError "not a traffic contract"
  let expected := name.getId.eraseMacroScopes.toString
  action := action.consumeMData
  for wrapper in [``mixed, ``audit, ``auditFocus, ``liftWGObserver, ``liftPrefix, ``liftM,
      ``MonadLiftT.monadLift, ``MonadLift.monadLift, ``liftWG] do
    if action.isAppOf wrapper && expected != wrapper.toString &&
        !wrapper.toString.endsWith ("." ++ expected) then
      let lifted := action.getAppArgs
      unless lifted.size > 0 do Lean.throwError "missing lifted action"
      action := lifted.back!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant-headed action"
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different traffic action head"

macro "rx_env_traffic_erasure" : tactic => `(tactic|
  first
    | (rx_env_traffic_head wgReceivePrefix; exact mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases _ _)))
    | (rx_env_traffic_head requireDrainedPrefix; exact mixed_erases (requireDrainedPrefix_erases _ _))
    | (rx_env_traffic_head runCryptWorkers; exact runCryptWorkers_erases)
    | (rx_env_traffic_head runSendWorkers; exact runSendWorkers_erases)
    | (rx_env_traffic_head runOneSendWorkerAudit; exact audit_erases runOneSendWorkerAudit_erases)
    | (rx_env_traffic_head schedule; exact schedule_erases _)
    | (rx_env_traffic_head pollScheduledInline; exact pollScheduledInline_erases)
    | (rx_env_traffic_head runWorkerPrefix; apply runWorkerPrefix_erases)
    | (rx_env_traffic_head handshakeReceiveWorker; exact handshakeReceiveWorker_erases)
    | (rx_env_traffic_head liftPrefix; exact erasesPrefix_lift _)
    | (rx_env_traffic_head Pure.pure; exact erasesPrefix_pure _)
    | (rx_env_traffic_head ForIn.forIn; first | apply erasesPrefix_range | apply erasesPrefix_forIn)
    | (rx_env_traffic_head Bind.bind; apply erasesPrefix_bind)
    | traffic_erases_join
    | traffic_erases_join_use
    | traffic_erasure_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro)

macro "rx_env_traffic_preservation" : tactic => `(tactic|
  first
    | traffic_ensures
    | maintenance_join_let
    | maintenance_join_use
    | (rx_env_traffic_head wgReceivePrefix; exact mixed_preserves
        (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _).liftWGObserver)
    | (rx_env_traffic_head requireDrainedPrefix; exact mixed_preserves (requireDrainedPrefix_allocation _ _))
    | (rx_env_traffic_head runCryptWorkers; exact runCryptWorkers_preserves)
    | (rx_env_traffic_head runSendWorkers; exact runSendWorkers_preserves)
    | (rx_env_traffic_head runOneSendWorkerAudit; exact audit_preserves _ runOneSendWorkerAudit_preserves)
    | (rx_env_traffic_head schedule; exact schedule_preserves _)
    | (rx_env_traffic_head pollScheduledInline; exact pollScheduledInline_preserves)
    | (rx_env_traffic_head runWorkerPrefix; apply runWorkerPrefix_preserves
        (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.productStore he))
    | (rx_env_traffic_head handshakeReceiveWorker; exact handshakeReceiveWorker_preserves)
    | (rx_env_traffic_head senderSource; exact boundaryLift_kernel _ (senderSource_sameKernel _ _ _ _))
    | (rx_env_traffic_head deliverSent; exact boundaryLift_kernel _ deliverSent_sameKernel)
    | (rx_env_traffic_head getDev; exact boundaryLift_kernel _
        (liftWG_sameProductStore getDev getDev_sameWGStore))
    | (rx_env_traffic_head requireNotPending; apply boundaryLift_kernel _;
        change SameProductStore (liftWG (pure ())); rw [liftWG_pure];
        exact SameView.pure _ _)
    | (rx_env_traffic_head peekNextSite; exact boundaryLift_kernel _ peekNextSite_sameKernel)
    | (rx_env_traffic_head getWG; exact boundaryLift_kernel _ (by
        intro initial; exact productGetWG_spec (fun store => store = initial)))
    | (rx_env_traffic_head modifyWG; exact boundaryLift_kernel _ (by
        intro initial; exact productModifyWG_spec (fun store => store = initial) _ (fun _ => rfl)))
    | (rx_env_traffic_head getEnv; exact boundaryLift_kernel _ (by
        apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
    | ((first | rx_env_traffic_head inSocketNs | rx_env_traffic_head routeOutput4 |
          rx_env_traffic_head neighbourClassify | rx_env_traffic_head getRouting);
        exact boundaryLift_kernel _ (by intro initial; exact productRouting_spec _ (fun store => store = initial)))
    | ((first | rx_env_traffic_head unsupported | rx_env_traffic_head invariant | rx_env_traffic_head getAmbient |
          rx_env_traffic_head recordBudget | rx_env_traffic_head fixtureSend);
        exact boundaryLift_kernel _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (rx_env_traffic_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (rx_env_traffic_head ForIn.forIn; first
        | apply PrefixEnsures.rangeInvariant (State := World) (I := fun _ h w => BoundaryInv h w)
            (hs := fun _ _ _ hi => hi.safe)
        | apply PrefixEnsures.forInInvariant _ _ _ (fun _ h w => BoundaryInv h w) BoundarySafe
            (fun _ _ _ hi => hi.safe))
    | (rx_env_traffic_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => BoundaryInv h w))
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro)

elab "rx_traffic_projects_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProjectsUnder do Lean.throwError "not a projection"
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
      Lean.Meta.withLocalDeclD `rx_traffic_projection_join contract fun hg => do
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (property (obody.instantiate1 g) (rbody.instantiate1 a))
        let proof ← Lean.Meta.mkLambdaFVars #[g, a, hg] next
        pure (proof, next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[oval, rval, valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "rx_traffic_projects_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProjectsUnder do Lean.throwError "not a projection"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!.consumeMData
  let original := args.back!.consumeMData
  unless observed.getAppFn.isFVar && original.getAppFn.isFVar do
    Lean.throwError "not paired local continuations"
  for decl in ← Lean.getLCtx do
    if decl.userName == `rx_traffic_projection_join then
      let proof := Lean.mkAppN decl.toExpr observed.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no paired continuation contract"

elab "rx_traffic_projects_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
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


/-- Normalize only branch receipts. The observer programs are not traversed. -/
elab "rx_traffic_context" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut receipts : Array (Lean.TSyntax `ident) := #[]
  for decl in ← Lean.getLCtx do
    if !decl.isImplementationDetail then
      let ty := (← Lean.instantiateMVars decl.type).consumeMData
      if ty.isAppOf `Eq || ty.isAppOf `Not then
        receipts := receipts.push (Lean.mkIdent decl.userName)
  unless receipts.size > 0 do Lean.throwError "no branch receipts"
  let selected := #[receipts.back!]
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    simp only [*, Option.some.injEq, Except.ok.injEq, Except.error.injEq,
      Prod.mk.injEq, reduceCtorEq] at $[$selected]*))


/-- Close an impossible constructor arm from its recorded discriminant. -/
elab "rx_traffic_absurd_receipt" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ctx ← Lean.getLCtx
  for decl in ctx do
    let ty := (← Lean.instantiateMVars decl.type).consumeMData
    let .forallE _ valueType rest _ := ty | continue
    let .forallE _ premise result _ := rest.consumeMData | continue
    unless premise.isAppOf ``Eq && result.isConstOf ``False do continue
    for value in ctx do
      unless Lean.Expr.equal valueType value.type do continue
      let needed := premise.instantiate1 value.toExpr
      for receipt in ctx do
        if Lean.Expr.equal needed receipt.type then
          let impossible := Lean.mkAppN decl.toExpr #[value.toExpr, receipt.toExpr]
          goal.assign (← Lean.Meta.mkFalseElim (← goal.getType) impossible)
          Lean.Elab.Tactic.replaceMainGoal []
          return
  Lean.throwError "no impossible constructor receipt"

macro "rx_env_traffic_projection" : tactic => `(tactic|
  first
    | rx_traffic_absurd_receipt
    | rx_traffic_projects_join
    | rx_traffic_projects_join_use
    | rx_traffic_projects_reduce
    | (audit_contract ProjectsUnder; first
        | (rx_env_traffic_head wgReceivePrefix; exact mixed_projects
            (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _).liftWGObserver)
        | (rx_env_traffic_head requireDrainedPrefix; exact mixed_projects (requireDrainedPrefix_allocation _ _))
        | (rx_env_traffic_head runCryptWorkers; exact runCryptWorkers_projects)
        | (rx_env_traffic_head runSendWorkers; exact runSendWorkers_projects)
        | (rx_env_traffic_head runOneSendWorkerAudit; exact audit_projects runOneSendWorkerAudit_preserves)
        | (rx_env_traffic_head schedule; exact schedule_projects _)
        | (rx_env_traffic_head pollScheduledInline; exact pollScheduledInline_projects)
        | (rx_env_traffic_head runWorkerPrefix; apply runWorker_projects)
        | (rx_env_traffic_head handshakeReceiveWorker; exact handshakeReceiveWorker_projects)
        | (rx_env_traffic_head liftPrefix; exact projectsUnder_lift _ _)
        | (rx_env_traffic_head Pure.pure; exact projectsUnder_pure _ _)
        | (rx_env_traffic_head ForIn.forIn; first | apply projectsUnder_range (S := AuditSafe) | apply projectsUnder_forIn (S := AuditSafe))
        | (rx_env_traffic_head Bind.bind; apply projectsUnder_bind (S := AuditSafe)))
    | (audit_contract PrefixPreserves; first
        | (rx_env_traffic_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
        | (rx_env_traffic_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
        | (rx_env_traffic_head scheduleAudit; exact scheduleAudit_preserves _)
        | (rx_env_traffic_head pollScheduledInlineAudit; exact pollScheduledInlineAudit_preserves)
        | env_traffic_preservation)
    | (audit_contract PrefixEnsures; first
        | (rx_env_traffic_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
            (I := fun _ h w => AuditInv h w) (hs := fun _ _ _ hi => hi.safe))
        | (rx_env_traffic_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
        | (rx_env_traffic_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
        | (rx_env_traffic_head scheduleAudit; exact scheduleAudit_preserves _)
        | (rx_env_traffic_head pollScheduledInlineAudit; exact pollScheduledInlineAudit_preserves)
        | env_traffic_preservation)
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try rx_traffic_context; all_goals try subst_vars; all_goals try contradiction; all_goals try rx_traffic_absurd_receipt)
    | maintenance_intro)

theorem inject_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) := by
  unfold inject Env.inject
  repeat' rx_env_traffic_erasure

theorem inject_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves BoundaryInv BoundarySafe (inject family port msg tos ll dest) := by
  unfold inject
  repeat' rx_env_traffic_preservation

theorem inject_projects (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsUnder AuditInv auditEvent (inject family port msg tos ll dest) (injectAudit family port msg tos ll dest) := by
  unfold inject injectAudit
  repeat' rx_env_traffic_projection

def afterBatch : Obs Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getAmbient).hidden.isNone then
    runCryptWorkers
    runSendWorkers
    return
  for _ in [0:(← liftPrefix recordBudget)] do
    schedule
    if (← liftPrefix peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then
      audit runOneSendWorkerAudit
    else break
  let d ← liftPrefix (liftWG getDev)
  mixed (requireDrainedPrefix "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  liftPrefix deliverSent

theorem afterBatch_erases : ErasesPrefix afterBatch (Env.afterBatch) := by
  unfold afterBatch Env.afterBatch
  repeat' rx_env_traffic_erasure

theorem afterBatch_preserves : PrefixPreserves BoundaryInv BoundarySafe afterBatch := by
  unfold afterBatch
  repeat' rx_env_traffic_preservation

theorem afterBatch_projects : ProjectsUnder AuditInv auditEvent afterBatch afterBatchAudit := by
  unfold afterBatch afterBatchAudit
  repeat' rx_env_traffic_projection

def flood (count port family : Nat) (messages : List (List UInt8)) : Obs Int := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a flood to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a flood to a port other than wg0's")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a flood while a handshake is queued"))
  let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
  let src ← liftPrefix (senderSource family 0)
  for msg in messages ++ List.replicate count invalid do
    if family == 4 then
      match ← liftPrefix (Net.routeOutput4 0 src.daddr) with
      | .error _ => liftPrefix (invariant "wg_flood: the datagram to wg0's port has no route")
      | .ok r =>
        if r.dev != LO_IFINDEX || r.src != src.saddr then
          liftPrefix (invariant "wg_flood: the route disagrees with the sender source")
        liftPrefix (Net.neighbourClassify LO_IFINDEX)
    liftPrefix fixtureSend
    runWorkerPrefix .netRx do
      mixed (liftWGObserver (wgReceivePrefix msg src))
      pollScheduledInline
  afterBatch
  let d ← liftPrefix (liftWG getDev)
  mixed (requireDrainedPrefix "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  return 0

theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) := by
  unfold flood Env.flood
  repeat' first
    | (rx_env_traffic_head afterBatch; exact afterBatch_erases)
    | rx_env_traffic_erasure

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves BoundaryInv BoundarySafe (flood count port family messages) := by
  unfold flood
  repeat' first
    | (rx_env_traffic_head afterBatch; exact afterBatch_preserves)
    | rx_env_traffic_preservation

theorem flood_projects (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsUnder AuditInv auditEvent (flood count port family messages) (floodAudit count port family messages) := by
  unfold flood floodAudit
  repeat' first
    | (audit_contract ProjectsUnder; rx_env_traffic_head afterBatch; exact afterBatch_projects)
    | (audit_contract PrefixPreserves; rx_env_traffic_head afterBatchAudit; exact afterBatchAudit_preserves)
    | rx_env_traffic_projection

end Leanux.Proofs.WG.Queues.RxHistory
