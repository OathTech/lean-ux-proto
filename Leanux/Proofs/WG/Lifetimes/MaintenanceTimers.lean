import Lean
import Leanux.Proofs.WG.Lifetimes.ReceiveEntry

set_option maxHeartbeats 600000
set_option pp.structureInstances false

/-! Endpoint and receive-timer maintenance with explicit resolved-peer
accesses. The generic contracts use the existing immediate read/update helper.
Time records retain their original validation; these are lifetime contracts. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

elab "maintenance_erases_bind" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 && args[args.size - 2]!.consumeMData.isAppOf ``Bind.bind do
    Lean.throwError "not an observer bind"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply erasesStatePrefix_bind))

elab "maintenance_spec_bind" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 && args[args.size - 2]!.consumeMData.isAppOf ``Bind.bind do
    Lean.throwError "not an observer bind"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply StatePrefixEnsures.bind))

elab "maintenance_lift_head" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 && args[args.size - 2]!.consumeMData.isAppOf ``liftWGPrefix do
    Lean.throwError "not a native lift"

elab "maintenance_head " name:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn
    | Lean.throwError "not a constant-headed observer"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different observer head"

elab "maintenance_lift_action_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  unless action.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
  let .const actual _ := action.getAppArgs.back!.consumeMData.getAppFn
    | Lean.throwError "not a constant-headed native action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different native action head"

elab "maintenance_intro" : tactic => do
  let ty ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
  unless ty.isForall do Lean.throwError "not a continuation binder"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))


elab "maintenance_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
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
  let last' := if target.isAppOf ``ErasesStatePrefix then reduceHead 64 last else last
  if Lean.Expr.equal observed observed' && Lean.Expr.equal last last' then
    Lean.throwError "heads unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (.app (.app f observed') last')]

elab "maintenance_reduce_match" : tactic => Lean.Elab.Tactic.withMainContext do
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
  let last' ← if target.isAppOf ``ErasesStatePrefix then reduce last else pure last
  if Lean.Expr.equal observed observed' && Lean.Expr.equal last last' then
    Lean.throwError "no reducible head matcher"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (.app (.app f observed') last')]

elab "maintenance_erases_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesStatePrefix do Lean.throwError "not an erasure"
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
      Lean.Meta.withLocalDeclD `maintenance_erasure_join contract fun hg => do
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (property (obody.instantiate1 g) (rbody.instantiate1 a))
        let proof ← Lean.Meta.mkLambdaFVars #[g, a, hg] next
        pure (proof, next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[oval, rval, valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "maintenance_erases_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesStatePrefix do Lean.throwError "not an erasure"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!.consumeMData
  let original := args.back!.consumeMData
  unless observed.getAppFn.isFVar && original.getAppFn.isFVar do
    Lean.throwError "not paired local continuations"
  for decl in ← Lean.getLCtx do
    if decl.userName == `maintenance_erasure_join then
      let proof := Lean.mkAppN decl.toExpr observed.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no paired continuation contract"

/-- Share the actual compiler-generated continuation's checked contract. -/
elab "maintenance_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  if target.isAppOf ``ErasesStatePrefix then Lean.throwError "not a preservation contract"
  let .app (.app front observed) post := target | Lean.throwError "missing action"
  let isProduct := observed.isAppOf ``liftWGObserver
  let action := if isProduct then observed.getAppArgs.back! else observed
  let wrap (a : Lean.Expr) :=
    if isProduct then
      match observed with
      | .app outer _ => Lean.mkApp outer a
      | _ => a
    else a
  let .letE name ty value body _ := action.consumeMData | Lean.throwError "not a let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a join"
  let property (a : Lean.Expr) := Lean.mkApp2 front (wrap a) post
  let valueContract ← Lean.Meta.forallTelescope ty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD name ty fun fn => do
    let contract ← Lean.Meta.forallTelescope ty fun args _ => do
      Lean.Meta.mkForallFVars args (property (Lean.mkAppN fn args))
    Lean.Meta.withLocalDeclD `maintenance_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 fn))
      let proof ← Lean.Meta.mkLambdaFVars #[fn, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "maintenance_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let action := args[args.size - 2]!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back! else action
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `maintenance_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"

elab "maintenance_product_lift" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let observed := args[args.size - 2]!.consumeMData
  unless observed.isAppOf ``liftWGObserver do Lean.throwError "not a product lift"
  let action := observed.getAppArgs.back!.consumeMData
  if action.isAppOf ``Bind.bind then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [liftWGObserver_bind]))
  else if action.isAppOf ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [liftWGObserver_pure]))
  else if action.isAppOf ``ite then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [apply_ite]))
  else Lean.throwError "not a lift composition"

elab "maintenance_impossible_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← goal.getType
  for decl in ← Lean.getLCtx do
    let .forallE _ _ (.forallE _ _ final _) _ := decl.type.consumeMData | continue
    unless final.isConstOf ``False do continue
    for evidence in ← Lean.getLCtx do
      unless (← Lean.Meta.matchEq? evidence.type).isSome do continue
      let (args, _, _) ← Lean.Meta.forallMetaTelescope decl.type
      unless args.size == 2 do continue
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType args[1]!) evidence.type then
        args[1]!.mvarId!.assign evidence.toExpr
        let proof := Lean.mkAppN decl.toExpr args
        goal.assign (← Lean.Meta.mkFalseElim target proof)
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no impossible match branch"

elab "maintenance_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let observed := args[args.size - 2]!.consumeMData
  let observed := if observed.isAppOf ``liftWGObserver then observed.getAppArgs.back!.consumeMData else observed
  let actions := if target.isAppOf ``ErasesStatePrefix then [observed, args.back!.consumeMData] else [observed]
  for action in actions do
    if let some matcher ← Lean.Meta.matchMatcherApp? action then
      for discr in matcher.discrs do
        for decl in ← Lean.getLCtx do
          if let some (_, lhs, _) ← Lean.Meta.matchEq? decl.type then
            if Lean.Expr.eqv lhs discr then
              let rewritten ← goal.rewrite target decl.toExpr
              let next ← goal.replaceTargetEq rewritten.eNew rewritten.eqProof
              Lean.Elab.Tactic.replaceMainGoal (next :: rewritten.mvarIds)
              return
  for action in actions do
    if let some matcher ← Lean.Meta.matchMatcherApp? action then
      let discr := matcher.discrs[0]!
      let (vars, next) ← goal.generalize #[{ expr := discr, hName? := some `maintenance_discriminator }]
      let branches ← next.cases vars[0]!
      Lean.Elab.Tactic.replaceMainGoal (branches.toList.map (·.mvarId))
      return
  Lean.throwError "not a head matcher"

macro "maintenance_store" c:ident P:term : tactic => `(tactic| (
  maintenance_lift_head
  apply AmbientContracts.store $c $P
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => wgStoreView w = initial)
        (fun _ w => wgStoreView w = initial) :=
    hoare_liftAmbient a (fun w => wgStoreView w = initial)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, getAmbient, getDev, hidden, hiddenJiffies,
    peekHiddenSite, branch, branchCmp, unsupported, invariant, ha]
  all_goals first | assumption | rfl))

elab "maintenance_product_bind" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let ty := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 && args[args.size - 2]!.consumeMData.isAppOf ``Bind.bind do
    Lean.throwError "not a product observer bind"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply PrefixEnsures.bind))

macro "maintenance_product_store" c:ident P:term : tactic => `(tactic| (
  maintenance_head liftWGPrefix
  apply ProductAmbientContracts.nativeStore $c $P
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => wgStoreView w = initial)
        (fun _ w => wgStoreView w = initial) :=
    hoare_liftAmbient a (fun w => wgStoreView w = initial)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, getAmbient, getDev, hidden, hiddenJiffies,
    peekHiddenSite, branch, branchCmp, unsupported, invariant, ha]
  all_goals first | assumption | rfl))

theorem endpointEq_sameStore (a : Endpoint) (b : Option Endpoint) :
    SameWGStore (endpointEq a b) := by
  apply SameView.of_wp
  intro k
  mvcgen [endpointEq, WG.andM, branch, AmbientM.branch]

def dstCacheResetMixed (pid : PeerId) : MixedM Unit := do
  let a ← liftWGPrefix (getAmbient : WG.M Ambient)
  let w ← liftWGPrefix (get : WG.M WGWorld)
  if !(a.armRecords && w.dstCacheRecords) then return
  let ts ← liftWGPrefix (hiddenJiffies .dstCacheResetTs)
  modifyPeerKeysPrefix pid fun p => {p with dstCache := {p.dstCache with resetTs := ts}}

theorem dstCacheResetMixed_erases (pid : PeerId) :
    ErasesStatePrefix (dstCacheResetMixed pid) (dstCacheReset pid) := by
  unfold dstCacheResetMixed dstCacheReset
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro a
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro w
  split
  · exact erasesStatePrefix_pure _
  · exact erasesStatePrefix_bind (erasesStatePrefix_lift _)
      (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem dstCacheResetMixed_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (dstCacheResetMixed pid) (fun _ => P) := by
  unfold dstCacheResetMixed
  apply StatePrefixEnsures.bind (c.store P _ (fun initial => hoare_liftAmbient
    (get : AmbientM Ambient) (fun w => wgStoreView w = initial)))
  intro a
  apply StatePrefixEnsures.bind (c.store P (get : WG.M WGWorld) (by
    apply SameView.of_wp
    intro initial
    mvcgen))
  intro w
  split
  · exact c.pure P _
  · apply StatePrefixEnsures.bind (c.store P _ (fun initial => hoare_liftAmbient (AmbientM.hiddenJiffies _) (fun w => wgStoreView w = initial)))
    intro ts
    exact modifyPeerKeysPrefix_spec_ambient c P pid _ (fun _ => rfl)

def setPeerEndpointPrefix (pid : PeerId) (e : Endpoint) : MixedM Unit := do
  requireNotPendingMixed pid "changing the endpoint"
  if ← liftWGPrefix (branch .setEndpointEq (← liftWGPrefix (endpointEq e (← getPeerMixed pid).endpoint))) then return
  if ← liftWGPrefix (branch .setEndpointV4 (e.family == AF_INET)) then
    modifyPeerKeysPrefix pid fun p => {p with endpoint := some e}
    dstCacheResetMixed pid
  else if ← liftWGPrefix (branch .setEndpointV6 (e.family == AF_INET6)) then
    modifyPeerKeysPrefix pid fun p => {p with endpoint := some e}
    dstCacheResetMixed pid

theorem setPeerEndpointPrefix_erases (pid : PeerId) (e : Endpoint) :
    ErasesStatePrefix (setPeerEndpointPrefix pid e) (setPeerEndpoint pid e) := by
  have update : ErasesStatePrefix
      (do modifyPeerKeysPrefix pid (fun p => {p with endpoint := some e}); dstCacheResetMixed pid)
      (do setPeer pid {(← getPeer pid) with endpoint := some e}; dstCacheReset pid) := by
    simp only [modifyPeerKeysPrefix, bind_assoc]
    exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
      erasesStatePrefix_bind (setPeerMixed_erases _ _) (fun _ => dstCacheResetMixed_erases _))
  unfold setPeerEndpointPrefix setPeerEndpoint
  apply erasesStatePrefix_bind (requireNotPendingMixed_erases _ _)
  intro _
  apply erasesStatePrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro equal
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro yes
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro v4
    split
    · exact update
    · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro v6
      split
      · exact update
      · exact erasesStatePrefix_pure _

theorem setPeerEndpointPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (e : Endpoint) : AmbientSpec I P (setPeerEndpointPrefix pid e) (fun _ => P) := by
  unfold setPeerEndpointPrefix
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_spec c P _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | (maintenance_lift_action_head endpointEq; exact c.store P _ (endpointEq_sameStore _ _))
    | maintenance_store c P
    | maintenance_store c P
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec c P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

def placeOnWheelPrefix (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit? : Option Nat) : MixedM Unit := do
  let p ← getPeerMixed pid
  match TimerWheel.place p t expires clk with
  | .kept _ =>
    -- :1123-1130: the slot, the list position and the stored bucket expiry
    -- stay; only `expires` changes. The C writes no enqueue record here.
    setPeerMixed pid (p.setTimer t (some expires))
    if unit?.isSome then
      if (← liftWGPrefix (peekHiddenSite : WG.M (Option Nat))) == some HiddenSite.timerEnqueue.info.id then
        liftWGPrefix (throw (.hidden s!"Linux re-enqueued peer {pid}'s {repr t} timer, which the mirror keeps in its slot (expires {expires}, base clock {clk})"))
  | .enqueued slot bexp =>
    if let some u := unit? then
      let eb ← liftWGPrefix (hidden .timerEnqueue)
      let (ridx, rbexp, u3) := (recordWord eb 0, recordWord64 eb 1, recordWord eb 2)
      if u != 0 && u3 != u then
        liftWGPrefix (throw (.hidden s!"the enqueue record names timer {u3}, the arm record {u}"))
      if ridx != slot || rbexp != bexp then
        liftWGPrefix (throw (.hidden s!"wheel arithmetic differs from Linux for peer {pid}'s {repr t} timer: expires {expires}, base clock {clk}: the mirror puts it in slot {slot} at bucket expiry {bexp}, Linux in slot {ridx} at {rbexp}"))
    -- the bucket expiry is in (expires, expires + 8^level] (calc_index rounds up)
    let lvl := TimerWheel.levelOf slot
    if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
      liftWGPrefix (invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}")
    let stamp := (← liftWGPrefix (get : WG.M WGWorld)).timerEnqueues + 1
    liftWGPrefix (modify fun k => { k with timerEnqueues := stamp })
    setPeerMixed pid ((p.setTimer t (some expires)).setWheel t (some ⟨slot, bexp, stamp⟩))
  if let some what := TimerWheel.peerWheelProblem (← getPeerMixed pid) then
    liftWGPrefix (invariant s!"peer {pid}'s timers: {what}")

def armTimerPrefix (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc? : Option UInt64 := none) : MixedM Unit := do
  let w ← liftWGPrefix (get : WG.M WGWorld)
  if !(← liftWGPrefix (getAmbient : WG.M Ambient)).armRecords then
    -- the domain filter (no records): the nominal expiry and the wheel at
    -- the last known `jiffies`, with no record to check
    let j0 := w.jiffiesLast.getD 0
    placeOnWheelPrefix pid t (j0 + delay.toUInt64) j0 none
    return
  let bs ← liftWGPrefix (hidden .modTimerArm)
  let (jm, e) := (recordWord64 bs 0, recordWord64 bs 1)
  -- the caller's read is recorded (kind 311), never recovered from `e`
  let some jc := jc? | liftWGPrefix (invariant "a timer armed with arm records and no caller read (kind 311)")
  let expires := jc + delay.toUInt64       -- `expires = jiffies + delay`, the caller's arithmetic
  if expires != e then
    liftWGPrefix (throw (.hidden s!"timer expiry differs from Linux: the caller read jiffies {jc} and mod_timer published {e}; the mirror's delay {delay} gives {expires}"))
  let gap := (jm - jc).toInt64             -- `(long)(J_m - J_c)`
  if gap < 0 then
    liftWGPrefix (throw (.hidden s!"mod_timer's jiffies {jm} is behind the caller's read {jc} (delay {delay}, expires {e})"))
  if gap > 1 then
    liftWGPrefix (unsupported s!"a stall between a timer's two jiffies reads (the mirror's delay matches the published expiry): the caller's {jc}, mod_timer's {jm} (delay {delay}, expires {e})")
  liftWGPrefix (modify fun w => { w with jiffiesLast := some jm })
  -- dispatch order (docs/2026-10-11-dispatch-order.md): the record's
  -- third word is the timer's address, which its section names
  let u := recordWord bs 2
  if u != 0 then liftWGPrefix (modify fun w => { w with timerUnits := (u, pid, t) :: w.timerUnits.filter (·.1 != u) })
  -- __mod_timer :1085-1088: a pending timer re-armed with the same expires
  if (← getPeerMixed pid).timer t == some e then return
  -- the base locked and forwarded: kind 313, the base clock
  let cb ← liftWGPrefix (hidden .timerClk)
  let (clk, u2) := (recordWord64 cb 0, recordWord cb 1)
  if u != 0 && u2 != u then
    liftWGPrefix (throw (.hidden s!"the base-clock record names timer {u2}, the arm record {u}"))
  if timeAfter clk (jm + 1) then
    liftWGPrefix (throw (.hidden s!"the timer base's clock {clk} is more than one past mod_timer's read {jm}"))
  if let some prev := (← liftWGPrefix (get : WG.M WGWorld)).timerClk then
    if timeBefore clk prev then
      liftWGPrefix (throw (.hidden s!"the timer base's clock went back: {clk} after {prev}"))
  if let some b := TimerWheel.earliestDue (← liftWGPrefix getDev) jm then
    if timeAfter clk b then
      liftWGPrefix (throw (.hidden s!"the timer base's clock {clk} is past the overdue modeled bucket {b} (forward_timer_base stops at next_expiry)"))
  if let some step := w.timerPassStep then
    if !timeAfter clk step then
      liftWGPrefix (throw (.hidden s!"an arm inside a timer pass at step {step} with the base clock {clk} not past it"))
  liftWGPrefix (modify fun k => { k with timerClk := some clk })
  placeOnWheelPrefix pid t e clk (some u)

def delTimerPrefix (pid : PeerId) (t : PeerTimer) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => (p.setTimer t none).setWheel t none

macro "maintenance_erases" : tactic => `(tactic|
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl)

theorem placeOnWheelPrefix_erases (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit? : Option Nat) :
    ErasesStatePrefix (placeOnWheelPrefix pid t expires clk unit?) (placeOnWheel pid t expires clk unit?) := by
  unfold placeOnWheelPrefix placeOnWheel
  maintenance_erases

theorem armTimerPrefix_erases (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    ErasesStatePrefix (armTimerPrefix pid t delay jc) (armTimer pid t delay jc) := by
  unfold armTimerPrefix armTimer
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_erases_bind
    | (maintenance_head placeOnWheelPrefix; exact placeOnWheelPrefix_erases _ _ _ _ _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem delTimerPrefix_erases (pid : PeerId) (t : PeerTimer) :
    ErasesStatePrefix (delTimerPrefix pid t) (delTimer pid t) := modifyPeerKeysPrefix_erases _ _


theorem placeOnWheelPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit? : Option Nat) :
    AmbientSpec I P (placeOnWheelPrefix pid t expires clk unit?) (fun _ => P) := by
  unfold placeOnWheelPrefix
  apply StatePrefixEnsures.bind (c.getPeer P pid)
  intro p
  let Q := fun s : IdentityView => P s ∧ s.1.slots pid = some p.internalId
  change AmbientSpec I Q _ (fun _ => P)
  apply AmbientContracts.forget (P := Q) (Q := fun _ => Q) ?_ (fun _ _ hi => hi.1)
  have set (q : Peer) (hq : q.internalId = p.internalId) :
      AmbientSpec I Q (setPeerMixed pid q) (fun _ => Q) :=
    (c.setPeer Q pid q).consequence
      (fun _ _ _ hi => ⟨hi.1, hi.2, by simpa only [hq] using hi.2.2⟩)
      (fun _ _ _ _ hi => hi)
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_spec_bind
    | (maintenance_head setPeerMixed; exact set _ (by cases t <;> rfl))
    | (maintenance_head getPeerMixed; exact c.getPeer_frame Q _)
    | maintenance_store c Q
    | (maintenance_head Pure.pure; exact c.pure Q _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem armTimerPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    AmbientSpec I P (armTimerPrefix pid t delay jc) (fun _ => P) := by
  unfold armTimerPrefix
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_spec_bind
    | (maintenance_head placeOnWheelPrefix; exact placeOnWheelPrefix_spec c P _ _ _ _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | maintenance_store c P
    | (maintenance_head Pure.pure; exact c.pure P _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem delTimerPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) : AmbientSpec I P (delTimerPrefix pid t) (fun _ => P) :=
  modifyPeerKeysPrefix_spec_ambient c P pid _ (fun p => by cases t <;> rfl)

/-- The original nested arrow resolves the peer before evaluating andM.
Keeping that elaborated order is necessary even when running is false. -/
def modPeerTimerGuardPrefix (pid : PeerId) : MixedM Bool := do
  let running := (← liftWGPrefix getDev).running
  let alive := !(← getPeerMixed pid).isDead
  liftWGPrefix (WG.andM (branch .modTimerRunning running) (branch .modTimerAlive alive))

theorem modPeerTimerGuardPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (modPeerTimerGuardPrefix pid) (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuardPrefix modPeerTimerGuard
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => erasesStatePrefix_lift _))

theorem modPeerTimerGuardPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (modPeerTimerGuardPrefix pid) (fun _ => P) := by
  apply StatePrefixEnsures.bind (c.store P _ (by apply SameView.of_wp; intro initial; mvcgen [getDev, invariant, AmbientM.invariant]))
  intro d
  apply StatePrefixEnsures.bind (c.getPeer_frame P pid)
  intro p
  apply c.store P
  apply SameView.of_wp
  intro initial
  mvcgen [WG.andM, branch, AmbientM.branch]

def modPeerTimerPrefix (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) : MixedM Bool := do
  let jc ← liftWGPrefix (callerJiffies site)
  if ← modPeerTimerGuardPrefix pid then
    armTimerPrefix pid t delay jc
    return true
  return false

theorem modPeerTimerPrefix_erases (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    ErasesStatePrefix (modPeerTimerPrefix site pid t delay) (modPeerTimer site pid t delay) := by
  unfold modPeerTimerPrefix modPeerTimer
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro jc
  apply erasesStatePrefix_bind (modPeerTimerGuardPrefix_erases pid)
  intro b
  split
  · exact erasesStatePrefix_bind (armTimerPrefix_erases pid t delay jc) (fun _ => erasesStatePrefix_pure _)
  · exact erasesStatePrefix_pure _

theorem modPeerTimerPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    AmbientSpec I P (modPeerTimerPrefix site pid t delay) (fun _ => P) := by
  unfold modPeerTimerPrefix
  apply StatePrefixEnsures.bind (c.store P _ ((callerJiffies_sameWGWorld site).factor wgStoreView))
  intro jc
  apply StatePrefixEnsures.bind (modPeerTimerGuardPrefix_spec c P pid)
  intro b
  split
  · exact StatePrefixEnsures.bind (armTimerPrefix_spec c P pid t delay jc) (fun _ => c.pure P _)
  · exact c.pure P _

def timersHandshakeCompletePrefix (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) : MixedM Unit := do
  delTimerPrefix pid .retransmitHandshake
  modifyPeerKeysPrefix pid fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}
  let now ← liftWGPrefix (hidden site)
  modifyPeerKeysPrefix pid fun p => {p with walltimeLastHandshake := now}

def timersAnyAuthenticatedPacketReceivedPrefix (pid : PeerId) : MixedM Unit :=
  delTimerPrefix pid .newHandshake

def timersDataReceivedPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .timersDataReceivedRunning (← liftWGPrefix getDev).running) then
    if ← liftWGPrefix (branch .timersDataReceivedNotPending !((← getPeerMixed pid).timerPending .sendKeepalive)) then
      discard <| modPeerTimerPrefix .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
    else
      modifyPeerKeysPrefix pid fun p => {p with timerNeedAnotherKeepalive := true}

def timersTraversalPrefix (pid : PeerId) : MixedM Unit := do
  let interval := (← getPeerMixed pid).persistentKeepaliveInterval
  if ← liftWGPrefix (branchCmp .traversalKeepalive (interval != 0) interval 0) then
    discard <| modPeerTimerPrefix .timerJiffiesTraversal pid .persistentKeepalive (interval * HZ)

theorem timersHandshakeCompletePrefix_erases (pid : PeerId) (site : HiddenSite) :
    ErasesStatePrefix (timersHandshakeCompletePrefix pid site) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeCompletePrefix timersHandshakeComplete
  simp only [modifyPeerKeysPrefix, bind_assoc]
  exact erasesStatePrefix_bind (delTimerPrefix_erases _ _) (fun _ =>
    erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
      erasesStatePrefix_bind (setPeerMixed_erases _ _) (fun _ =>
        erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
          erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _)))))

theorem timersAnyAuthenticatedPacketReceivedPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersAnyAuthenticatedPacketReceivedPrefix pid) (timersAnyAuthenticatedPacketReceived pid) :=
  delTimerPrefix_erases _ _

theorem timersDataReceivedPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersDataReceivedPrefix pid) (timersDataReceived pid) := by
  unfold timersDataReceivedPrefix timersDataReceived
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modPeerTimerPrefix; exact modPeerTimerPrefix_erases _ _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem timersTraversalPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersTraversalPrefix pid) (timersTraversal pid) := by
  unfold timersTraversalPrefix timersTraversal
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modPeerTimerPrefix; exact modPeerTimerPrefix_erases _ _ _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | rfl

theorem timersHandshakeCompletePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (site : HiddenSite) : AmbientSpec I P (timersHandshakeCompletePrefix pid site) (fun _ => P) := by
  unfold timersHandshakeCompletePrefix
  apply StatePrefixEnsures.bind (delTimerPrefix_spec c P _ _)
  intro _
  apply StatePrefixEnsures.bind (modifyPeerKeysPrefix_spec_ambient c P pid
    (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}) (fun _ => rfl))
  intro _
  apply StatePrefixEnsures.bind (c.store P _ (fun initial => hoare_liftAmbient (AmbientM.hidden site) (fun w => wgStoreView w = initial)))
  intro now
  exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl)

theorem timersAnyAuthenticatedPacketReceivedPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (timersAnyAuthenticatedPacketReceivedPrefix pid) (fun _ => P) :=
  delTimerPrefix_spec c P _ _

theorem timersDataReceivedPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (timersDataReceivedPrefix pid) (fun _ => P) := by
  unfold timersDataReceivedPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_store c P
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | maintenance_store c P
    | maintenance_store c P
    | (maintenance_head modPeerTimerPrefix; exact modPeerTimerPrefix_spec c P _ _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem timersTraversalPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (timersTraversalPrefix pid) (fun _ => P) := by
  unfold timersTraversalPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | maintenance_store c P
    | maintenance_store c P
    | (maintenance_head modPeerTimerPrefix; exact modPeerTimerPrefix_spec c P _ _ _ _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

/-- Product caller contracts retain arbitrary invariants over the actual World. -/
theorem dstCacheResetMixed_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (dstCacheResetMixed pid)) (fun _ => P) := by
  simp only [dstCacheResetMixed, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.nativeStore P _ (fun initial => hoare_liftAmbient
    (get : AmbientM Ambient) (fun w => wgStoreView w = initial)))
  intro a
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.nativeStore P (get : WG.M WGWorld) (by
    apply SameView.of_wp
    intro initial
    mvcgen))
  intro w
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  split
  · exact c.pure P _
  · apply PrefixEnsures.bind (c.nativeStore P _ (fun initial => hoare_liftAmbient (AmbientM.hiddenJiffies _) (fun w => wgStoreView w = initial)))
    intro ts
    try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    exact modifyPeerKeysPrefix_spec_product c P pid _ (fun _ => rfl)

theorem setPeerEndpointPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (e : Endpoint) : ProductAmbientSpec I P (liftWGObserver (setPeerEndpointPrefix pid e)) (fun _ => P) := by
  simp only [setPeerEndpointPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | maintenance_product_lift
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head requireNotPendingMixed; exact requireNotPendingMixed_spec_product c P _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | (maintenance_lift_action_head endpointEq; exact c.nativeStore P _ (endpointEq_sameStore _ _))
    | maintenance_product_store c P
    | maintenance_product_store c P
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_head dstCacheResetMixed; exact dstCacheResetMixed_spec_product c P _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem placeOnWheelPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit? : Option Nat) :
    ProductAmbientSpec I P (liftWGObserver (placeOnWheelPrefix pid t expires clk unit?)) (fun _ => P) := by
  unfold placeOnWheelPrefix
  rw [liftWGObserver_bind]
  apply PrefixEnsures.bind (c.getPeer P pid)
  intro p
  let Q := fun s : IdentityView => P s ∧ s.1.slots pid = some p.internalId
  change ProductAmbientSpec I Q _ (fun _ => P)
  apply ProductAmbientContracts.forget (P := Q) (Q := fun _ => Q) ?_ (fun _ _ hi => hi.1)
  have set (q : Peer) (hq : q.internalId = p.internalId) :
      ProductAmbientSpec I Q (liftWGObserver (setPeerMixed pid q)) (fun _ => Q) :=
    (c.setPeer Q pid q).consequence
      (fun _ _ hi => ⟨hi.1, hi.2, by simpa only [hq] using hi.2.2⟩)
      (fun _ _ _ hi => hi)
  repeat' first
    | maintenance_product_lift
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_bind
    | (maintenance_head setPeerMixed; exact set _ (by cases t <;> rfl))
    | (maintenance_head getPeerMixed; exact c.getPeer_frame Q _)
    | maintenance_product_store c Q
    | (maintenance_head Pure.pure; exact c.pure Q _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem armTimerPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    ProductAmbientSpec I P (liftWGObserver (armTimerPrefix pid t delay jc)) (fun _ => P) := by
  unfold armTimerPrefix
  repeat' first
    | maintenance_product_lift
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_bind
    | (maintenance_head placeOnWheelPrefix; exact placeOnWheelPrefix_spec_product c P _ _ _ _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | maintenance_product_store c P
    | (maintenance_head Pure.pure; exact c.pure P _)
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem delTimerPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (t : PeerTimer) : ProductAmbientSpec I P (liftWGObserver (delTimerPrefix pid t)) (fun _ => P) := by
  simpa only [delTimerPrefix] using
  modifyPeerKeysPrefix_spec_product c P pid _ (fun p => by cases t <;> rfl)

theorem modPeerTimerGuardPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (modPeerTimerGuardPrefix pid)) (fun _ => P) := by
  simp only [modPeerTimerGuardPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.nativeStore P _ (by apply SameView.of_wp; intro initial; mvcgen [getDev, invariant, AmbientM.invariant]))
  intro d
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.getPeer_frame P pid)
  intro p
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply c.nativeStore P
  apply SameView.of_wp
  intro initial
  mvcgen [WG.andM, branch, AmbientM.branch]

theorem modPeerTimerPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    ProductAmbientSpec I P (liftWGObserver (modPeerTimerPrefix site pid t delay)) (fun _ => P) := by
  simp only [modPeerTimerPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.nativeStore P _ ((callerJiffies_sameWGWorld site).factor wgStoreView))
  intro jc
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (modPeerTimerGuardPrefix_spec_product c P pid)
  intro b
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  split
  · exact PrefixEnsures.bind (armTimerPrefix_spec_product c P pid t delay jc) (fun _ => c.pure P _)
  · exact c.pure P _

theorem timersHandshakeCompletePrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) (site : HiddenSite) : ProductAmbientSpec I P (liftWGObserver (timersHandshakeCompletePrefix pid site)) (fun _ => P) := by
  simp only [timersHandshakeCompletePrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (delTimerPrefix_spec_product c P _ _)
  intro _
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (modifyPeerKeysPrefix_spec_product c P pid
    (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}) (fun _ => rfl))
  intro _
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.nativeStore P _ (fun initial => hoare_liftAmbient (AmbientM.hidden site) (fun w => wgStoreView w = initial)))
  intro now
  try simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl)

theorem timersAnyAuthenticatedPacketReceivedPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : ProductAmbientSpec I P (liftWGObserver (timersAnyAuthenticatedPacketReceivedPrefix pid)) (fun _ => P) := by
  simpa only [timersAnyAuthenticatedPacketReceivedPrefix] using
  delTimerPrefix_spec_product c P _ _

theorem timersDataReceivedPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : ProductAmbientSpec I P (liftWGObserver (timersDataReceivedPrefix pid)) (fun _ => P) := by
  simp only [timersDataReceivedPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_product_lift
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_store c P
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | maintenance_product_store c P
    | maintenance_product_store c P
    | (maintenance_head modPeerTimerPrefix; exact modPeerTimerPrefix_spec_product c P _ _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

theorem timersTraversalPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : ProductAmbientSpec I P (liftWGObserver (timersTraversalPrefix pid)) (fun _ => P) := by
  simp only [timersTraversalPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_product_lift
    | contradiction
    | maintenance_impossible_match
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | maintenance_product_store c P
    | maintenance_product_store c P
    | (maintenance_head modPeerTimerPrefix; exact modPeerTimerPrefix_spec_product c P _ _ _ _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro

end Leanux.Proofs.WG.Lifetimes
