import Lean
import Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit
import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Lifetimes.ReceiveIngress

/-! Exact environment ingress, multicast loopback and flood observations. Inline
polling records the complete demanded saved-map scan before effects. Every flood
producer, inline poll and deferred activation follows the original source,
including its partial history when a later record or drain guard fails. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

def xmitMulticastLoopAudit (family addr : Nat) : AuditM Unit := do
  if multicastLoops family addr then auditFocus (liftWGObserver (loopbackSendPrefix [] true))
  else if family == 6 && addr / 2 ^ 120 == 0xff then
    liftPrefix (unsupported "an IPv6 multicast destination (whether the IP output loops a copy back depends on wg0's groups)")

def pollScheduledInlinePrefix : PrefixM LifetimeEvent Unit := do
  let d ← liftWGObserver (liftWGPrefix getDev)
  let pending ← liftWGObserver (savedPeerFilterMap (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList)
  if pending.length > 1 then liftPrefix (unsupported "NAPI polls of several peers in one softirq")
  for pid in pending do
    discard <| rxPollStackPrefix pid NAPI_POLL_WEIGHT

theorem pollScheduledInlinePrefix_erases : ErasesPrefix pollScheduledInlinePrefix Env.pollScheduledInline := by
  unfold pollScheduledInlinePrefix Env.pollScheduledInline
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
  intro d
  apply erasesPrefix_bind_pure (liftWGObserver_erases (savedPeerFilterMap_erases _ _))
  dsimp only
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible exact rxPollStackPrefix_erases _ _
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem pollScheduledInlinePrefix_allocation :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe pollScheduledInlinePrefix := by
  let c := ProductAmbientContracts.ofNative allocationAmbient
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  unfold pollScheduledInlinePrefix
  apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
  intro d
  apply PrefixEnsures.bind (savedPeerFilterMap_spec_product c (fun _ => True) _ _)
  intro pending
  apply PrefixEnsures.consequence
    (show PrefixEnsures (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe _
      (fun _ h w => AllocationInv h w.wg) from ?_)
    (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
  change PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe _
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | exact (rxPollStackPrefix_preserves c (ProductTxContracts.ofNative allocationTx) ⟨fun len => (allocationRx.stats len).liftWGObserver, fun why => (allocationRx.dishonest why).liftWGObserver, fun id => (allocationRx.free id).liftWGObserver⟩ ⟨fun P => (allocationWgXmit.errors P).liftWGObserver⟩ _ _)
    | exact ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.unsupported _))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

abbrev pollScheduledInlineAudit : AuditM Unit := auditFocus pollScheduledInlinePrefix

theorem pollScheduledInlineAudit_erases : ErasesPrefix pollScheduledInlineAudit Env.pollScheduledInline :=
  auditFocus_erases pollScheduledInlinePrefix_erases

theorem pollScheduledInlineAudit_preserves : PrefixPreserves AuditInv AuditSafe pollScheduledInlineAudit :=
  auditFocus_preserves pollScheduledInlinePrefix_allocation

def injectAudit (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : AuditM Int := do
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
  runWorkerPrefix .netRx (auditFocus (liftWGObserver (wgReceivePrefix msg src)))
  runCryptWorkersAudit
  let d ← liftPrefix (liftWG getDev)
  auditFocus (requireDrainedPrefix "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  return msg.length

def afterBatchAudit : AuditM Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getAmbient).hidden.isNone then
    runCryptWorkersAudit
    runSendWorkersAudit
    return
  for _ in [0:(← liftPrefix recordBudget)] do
    scheduleAudit
    if (← liftPrefix peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then
      runOneSendWorkerAudit
    else break
  let d ← liftPrefix (liftWG getDev)
  auditFocus (requireDrainedPrefix "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  liftPrefix deliverSent

elab "traffic_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  let mut action ←
    if ty.isAppOf ``PrefixPreserves then
      if args.size > 0 then pure args.back! else Lean.throwError "missing observer"
    else if ty.isAppOf ``PrefixEnsures || ty.isAppOf ``ErasesPrefix then
      if args.size ≥ 2 then pure args[args.size - 2]! else Lean.throwError "missing observer"
    else Lean.throwError "not a traffic contract"
  let expected := name.getId.eraseMacroScopes.toString
  action := action.consumeMData
  for wrapper in [``auditFocus, ``liftWGObserver, ``liftPrefix, ``liftM,
      ``MonadLiftT.monadLift, ``MonadLift.monadLift, ``liftWG] do
    if action.isAppOf wrapper && expected != wrapper.toString &&
        !wrapper.toString.endsWith ("." ++ expected) then
      let lifted := action.getAppArgs
      unless lifted.size > 0 do Lean.throwError "missing lifted action"
      action := lifted.back!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant-headed action"
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different traffic action head"

/- The paired continuations below are proved once and applied at each source
branch. They share proof terms, not executions or state. -/
elab "traffic_erasure_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let keepJoins := true
  let rec reduceHead : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if keepJoins && name.toString.startsWith "__do_jp" then e
        else reduceHead n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if keepJoins && name.toString.startsWith "__do_jp" then e
          else reduceHead n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal e next then e else reduceHead n next
        | _ => e
  let .app (.app f observed) last := target | Lean.throwError "missing action"
  let observed' :=
    if observed.isAppOf ``liftWGObserver then
      match observed with
      | .app outer inner => Lean.mkApp outer (reduceHead 64 inner)
      | _ => observed
    else reduceHead 64 observed
  let last' := if target.isAppOf ``ErasesPrefix then reduceHead 64 last else last
  if Lean.Expr.equal observed observed' && Lean.Expr.equal last last' then
    Lean.throwError "heads unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (.app (.app f observed') last')]

elab "traffic_erases_join" : tactic => Lean.Elab.Tactic.withMainContext do
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
      Lean.Meta.withLocalDeclD `traffic_erasure_join contract fun hg => do
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (property (obody.instantiate1 g) (rbody.instantiate1 a))
        let proof ← Lean.Meta.mkLambdaFVars #[g, a, hg] next
        pure (proof, next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[oval, rval, valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "traffic_erases_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesPrefix do Lean.throwError "not an erasure"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!.consumeMData
  let original := args.back!.consumeMData
  unless observed.getAppFn.isFVar && original.getAppFn.isFVar do
    Lean.throwError "not paired local continuations"
  for decl in ← Lean.getLCtx do
    if decl.userName == `traffic_erasure_join then
      let proof := Lean.mkAppN decl.toExpr observed.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no paired continuation contract"

macro "env_traffic_erasure" : tactic => `(tactic|
  first
    | traffic_erases_join
    | traffic_erases_join_use
    | (traffic_head loopbackSendPrefix; exact auditFocus_erases (liftWGObserver_erases (loopbackSendPrefix_erases _ _)))
    | (traffic_head wgReceivePrefix; exact auditFocus_erases (liftWGObserver_erases (wgReceivePrefix_erases _ _)))
    | (traffic_head requireDrainedPrefix; exact auditFocus_erases (requireDrainedPrefix_erases _ _))
    | (traffic_head runCryptWorkersAudit; exact runCryptWorkersAudit_erases)
    | (traffic_head runWorkerPrefix; apply runWorkerPrefix_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | traffic_erasure_reduce
    | maintenance_intro)

elab "traffic_ensures" : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``PrefixPreserves do Lean.throwError "already result-dependent"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply PrefixEnsures.preserves))

macro "env_traffic_preservation" : tactic => `(tactic|
  first
    | traffic_ensures
    | maintenance_join_let
    | maintenance_join_use
    | (traffic_head loopbackSendPrefix; exact auditFocus_preserves
        ((AmbientContracts.drop (loopbackSendPrefix_spec allocationAmbient (fun _ => True) _ _)).liftWGObserver))
    | (traffic_head wgReceivePrefix; exact auditFocus_preserves
        (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _).liftWGObserver)
    | (traffic_head requireDrainedPrefix; exact auditFocus_preserves (requireDrainedPrefix_allocation _ _))
    | (traffic_head runCryptWorkersAudit; exact runCryptWorkersAudit_preserves)
    | (traffic_head runWorkerPrefix; apply runWorkerPrefix_preserves
        (fun _ _ hi => hi.safe)
        (fun _ _ _ he hi => hi.store (congrArg (fun s : ProductStore43 => s.2.2.2) he)))
    | (traffic_head senderSource; exact auditLift_store _
        ((senderSource_sameKernel _ _ _ _).of_factor (fun s : ProductStore43 => s.2.2.2)
          (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (traffic_head deliverSent; exact auditLift_store _
        (deliverSent_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
          (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (traffic_head getDev; exact auditLift_store _ (sameView_liftWG (fun w => wgStoreView w.wg)
        wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi)))
    | (traffic_head requireNotPending; apply auditLift_store
       simp only [requireNotPending, liftWG_pure]
       exact SameView.pure _ _)
    | (traffic_head peekNextSite; exact auditLift_store _
        (peekNextSite_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
          (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (traffic_head getWG; exact auditLift_store _ (by
        intro initial
        exact productGetWG_spec (fun store => store.2.2.2 = initial)))
    | (traffic_head modifyWG; exact auditLift_store _ (by
        intro initial
        exact productModifyWG_spec (fun store => store.2.2.2 = initial) _ (fun _ => rfl)))
    | (traffic_head getEnv; exact auditLift_store _ (by
        apply (ProjectedAction.iff_run _ _ _).mpr
        intro w x v hr
        cases hr
        rfl))
    | ((first | traffic_head inSocketNs | traffic_head routeOutput4 | traffic_head neighbourClassify | traffic_head getRouting);
        exact auditLift_store _ (by intro initial; exact productRouting_spec _ (fun store => store.2.2.2 = initial)))
    | ((first | traffic_head unsupported | traffic_head invariant | traffic_head getAmbient |
          traffic_head recordBudget | traffic_head fixtureSend);
        exact auditLift_store _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | (traffic_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (traffic_head ForIn.forIn; apply PrefixEnsures.forInInvariant _ _ _ (fun _ h w => AuditInv h w) AuditSafe (fun _ _ _ hi => hi.safe))
    | (traffic_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_reduce
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro)

theorem xmitMulticastLoopAudit_erases (family addr : Nat) :
    ErasesPrefix (xmitMulticastLoopAudit family addr) (Env.xmitMulticastLoop family addr) := by
  unfold xmitMulticastLoopAudit Env.xmitMulticastLoop
  repeat' env_traffic_erasure

theorem xmitMulticastLoopAudit_preserves (family addr : Nat) :
    PrefixPreserves AuditInv AuditSafe (xmitMulticastLoopAudit family addr) := by
  apply PrefixEnsures.preserves
  unfold xmitMulticastLoopAudit
  repeat' env_traffic_preservation

theorem injectAudit_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (injectAudit family port msg tos ll dest) (Env.inject family port msg tos ll dest) := by
  unfold injectAudit Env.inject
  repeat' env_traffic_erasure

theorem injectAudit_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves AuditInv AuditSafe (injectAudit family port msg tos ll dest) := by
  apply PrefixEnsures.preserves
  unfold injectAudit
  repeat' env_traffic_preservation
theorem afterBatchAudit_erases : ErasesPrefix afterBatchAudit Env.afterBatch := by
  unfold afterBatchAudit Env.afterBatch
  repeat' first
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact scheduleAudit_erases _
    | with_reducible apply erasesPrefix_range
    | env_traffic_erasure

theorem afterBatchAudit_preserves : PrefixPreserves AuditInv AuditSafe afterBatchAudit := by
  apply PrefixEnsures.preserves
  unfold afterBatchAudit
  repeat' first
    | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
    | (audit_contract_head runOneSendWorkerAudit; exact runOneSendWorkerAudit_preserves)
    | (audit_contract_head scheduleAudit; exact scheduleAudit_preserves _)
    | (audit_contract_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World) (I := fun _ h w => AuditInv h w) (hs := fun _ _ _ hi => hi.safe))
    | env_traffic_preservation

def floodAudit (count port family : Nat) (messages : List (List UInt8)) : AuditM Int := do
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
      auditFocus (liftWGObserver (wgReceivePrefix msg src))
      pollScheduledInlineAudit
  afterBatchAudit
  let d ← liftPrefix (liftWG getDev)
  auditFocus (requireDrainedPrefix "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  return 0

theorem floodAudit_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (floodAudit count port family messages) (Env.flood count port family messages) := by
  unfold floodAudit Env.flood
  repeat' first
    | with_reducible exact afterBatchAudit_erases
    | with_reducible exact pollScheduledInlineAudit_erases
    | env_traffic_erasure

theorem floodAudit_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves AuditInv AuditSafe (floodAudit count port family messages) := by
  apply PrefixEnsures.preserves
  unfold floodAudit
  repeat' first
    | (audit_contract_head afterBatchAudit; exact afterBatchAudit_preserves)
    | (audit_contract_head pollScheduledInlineAudit; exact pollScheduledInlineAudit_preserves)
    | env_traffic_preservation
end Leanux.Proofs.WG.Lifetimes
