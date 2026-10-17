import Leanux.Proofs.WG.Queues.JointConfigurationUpdate
import Leanux.Proofs.WG.Configuration.PeerRemovalCompletion

/-! The actual removal observer only appends lifetime accesses, including
failed flush and timer prefixes. These are journal facts with no allocation,
affiliation, saved-reference, progress, or successful-return premise. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps Configuration

elab "joint_append_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``StateAppends do Lean.throwError "not StateAppends"
  let action := ty.getAppArgs.back!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

elab "joint_append_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateAppends do Lean.throwError "not StateAppends"
  let .app property action := target | Lean.throwError "missing action"
  let .letE name type value body _ := action.consumeMData | Lean.throwError "not an action let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a source join"
  let contract ← Lean.Meta.forallTelescope type fun args _ =>
    Lean.Meta.mkForallFVars args (Lean.mkApp property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar contract
  let (continuation,next) ← Lean.Meta.withLocalDeclD name type fun f => do
    let contract ← Lean.Meta.forallTelescope type fun args _ =>
      Lean.Meta.mkForallFVars args (Lean.mkApp property (Lean.mkAppN f args))
    Lean.Meta.withLocalDeclD `joint_append_contract contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (Lean.mkApp property (body.instantiate1 f))
      return (← Lean.Meta.mkLambdaFVars #[f,hf] next,next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[value,valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!,next]

elab "joint_append_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateAppends do Lean.throwError "not StateAppends"
  let action := target.getAppArgs.back!.consumeMData
  unless action.getAppFn.isFVar do Lean.throwError "not a source continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `joint_append_contract then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no matching source continuation contract"

elab "joint_append_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateAppends do Lean.throwError "not StateAppends"
  let .app property action := target | Lean.throwError "missing action"
  let rec reduce : Nat → Lean.Expr → Lean.Expr
    | 0,e => e
    | n+1,e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else reduce n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else reduce n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal e next then e else reduce n next
        | _ => e
  let next := reduce 64 action
  if Lean.Expr.equal next action then Lean.throwError "unchanged action head"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp property next)]

macro "joint_append_step" : tactic => do
  let pinned (name : String) := Lean.mkCIdent (normalizePinnedName name.toName)
  `(tactic| first
  | joint_append_join
  | joint_append_join_use
  | joint_append_reduce
  | (joint_append_head liftWGPrefix; exact StateAppends.lift _)
  | (joint_append_head Pure.pure; exact StateAppends.pure _)
  | (joint_append_head getPeerMixed; exact StateAppends.focus _ _ _)
  | (joint_append_head setPeerMixed; exact StateAppends.focus _ _ _)
  | (joint_append_head peerGetMixed; exact StateAppends.focus _ _ _)
  | (joint_append_head peerPutMixed; exact StateAppends.focus _ _ _)
  | (joint_append_head modifyPeerKeysPrefix; unfold modifyPeerKeysPrefix)
  | (joint_append_head requireNotPendingMixed; unfold requireNotPendingMixed)
  | (joint_append_head peerDerefPrefix
     exact $(pinned "_private.Leanux.Proofs.WG.Queues.JointConfigurationTail.0.Leanux.Proofs.WG.Queues.RoutingJoint.deref_appends") _)
  | (joint_append_head keypairPutPrefix
     exact $(pinned "_private.Leanux.Proofs.WG.Queues.JointConfigurationTail.0.Leanux.Proofs.WG.Queues.RoutingJoint.keyPut_appends") _ _)
  | (joint_append_head Bind.bind; apply StateAppends.bind)
  | (joint_append_head ForIn.forIn; apply stateAppends_forIn)
  | (joint_append_head ite
     apply $(pinned "_private.Leanux.Proofs.WG.Queues.JointConfigurationTail.0.Leanux.Proofs.WG.Queues.RoutingJoint.append_ite"))
  | maintenance_intro
  | split)

private theorem savedAny_appends (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    StateAppends (savedPeerAny test xs) := by
  intro w ambient h
  change ∃ s, (runStatePrefix (savedPeerAny test xs) w ambient h).2 = h ++ s
  rw [savedPeerAny_run]
  exact ⟨_,rfl⟩

private theorem loopback_appends (sites : List HiddenSite) (raised : Bool) :
    StateAppends (loopbackSendPrefix sites raised) := by
  unfold loopbackSendPrefix loopbackSoftirqPrefix
  repeat' first
    | (joint_append_head savedPeerAny; exact savedAny_appends _ _)
    | joint_append_step

private theorem tunnel_appends (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (r : Route) (exactRx : Bool) : StateAppends (tunnelXmitPrefix e bytes ds r exactRx) := by
  unfold tunnelXmitPrefix
  repeat' first
    | (joint_append_head loopbackSendPrefix; exact loopback_appends _ _)
    | joint_append_step

private theorem cacheGet_appends (pid : PeerId) (gen : Nat) : StateAppends (dstCacheGetPrefix pid gen) := by
  unfold dstCacheGetPrefix
  repeat' joint_append_step

private theorem cacheReset_appends (pid : PeerId) : StateAppends (dstCacheResetMixed pid) := by
  unfold dstCacheResetMixed
  repeat' joint_append_step

private theorem send4Finish_appends (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) :
    StateAppends (send4FinishPrefix e bytes ds exactRx route) := by
  unfold send4FinishPrefix
  repeat' first
    | (joint_append_head tunnelXmitPrefix; exact tunnel_appends _ _ _ _ _)
    | joint_append_step

private theorem send4RouteDone_appends (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route) (rt : Except Int Route) :
    StateAppends (send4RouteDonePrefix e cache bytes ds exactRx gen fallback rt) := by
  unfold send4RouteDonePrefix dstCacheSetPrefix
  repeat' first
    | (joint_append_head send4FinishPrefix; exact send4Finish_appends _ _ _ _ _)
    | joint_append_step

private theorem send4Retry_appends (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route) (srcIf : Nat) (rt : Except Int Route) :
    StateAppends (send4RetryPrefix e cache bytes ds exactRx gen fallback srcIf rt) := by
  unfold send4RetryPrefix send4ClearSrcPrefix
  repeat' first
    | (joint_append_head send4RouteDonePrefix; exact send4RouteDone_appends _ _ _ _ _ _ _ _)
    | (joint_append_head dstCacheResetMixed; exact cacheReset_appends _)
    | joint_append_step

private theorem send4Miss_appends (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (gen : Nat) (fallback : Option Route) (saddr srcIf : Nat) :
    StateAppends (send4MissPrefix e cache bytes ds exactRx gen fallback saddr srcIf) := by
  unfold send4MissPrefix send4ClearSrcPrefix
  repeat' first
    | (joint_append_head send4RetryPrefix; exact send4Retry_appends _ _ _ _ _ _ _ _ _)
    | (joint_append_head dstCacheResetMixed; exact cacheReset_appends _)
    | joint_append_step

private theorem send4_appends (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : StateAppends (send4Prefix e cache bytes ds exactRx) := by
  unfold send4Prefix send4AfterCachePrefix
  repeat' first
    | (joint_append_head send4FinishPrefix; exact send4Finish_appends _ _ _ _ _)
    | (joint_append_head send4MissPrefix; exact send4Miss_appends _ _ _ _ _ _ _ _ _)
    | (joint_append_head dstCacheGetPrefix; exact cacheGet_appends _ _)
    | joint_append_step

private theorem send6_appends (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) : StateAppends (send6Prefix e cache bytes ds exactRx) := by
  unfold send6Prefix dstCacheSetPrefix
  repeat' first
    | (joint_append_head tunnelXmitPrefix; exact tunnel_appends _ _ _ _ _)
    | (joint_append_head dstCacheGetPrefix; exact cacheGet_appends _ _)
    | (joint_append_head dstCacheResetMixed; exact cacheReset_appends _)
    | joint_append_step

private theorem sendBuffer_appends (pid : PeerId) (bytes : List UInt8) :
    StateAppends (sendBufferToPeerPrefix pid bytes) := by
  unfold sendBufferToPeerPrefix sendSkbToPeerPrefix
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (joint_append_head send4Prefix; exact send4_appends _ _ _ _ _)
    | (joint_append_head send6Prefix; exact send6_appends _ _ _ _ _)
    | joint_append_step

private theorem initiation_appends (pid : PeerId) : StateAppends (createInitiationPrefix pid) := by
  unfold createInitiationPrefix setChainPrefix
  repeat' joint_append_step

private theorem mac_appends (pid : PeerId) (msg : List UInt8) : StateAppends (addMacToPacketPrefix pid msg) := by
  unfold addMacToPacketPrefix andPrefix
  repeat' joint_append_step

private theorem place_appends (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
    StateAppends (placeOnWheelPrefix pid t expires clk unit) := by
  unfold placeOnWheelPrefix
  repeat' joint_append_step

private theorem arm_appends (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc : Option UInt64) :
    StateAppends (armTimerPrefix pid t delay jc) := by
  unfold armTimerPrefix
  repeat' first
    | (joint_append_head placeOnWheelPrefix; exact place_appends _ _ _ _ _)
    | joint_append_step

private theorem modTimer_appends (site : HiddenSite) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    StateAppends (modPeerTimerPrefix site pid t delay) := by
  unfold modPeerTimerPrefix modPeerTimerGuardPrefix
  repeat' first
    | (joint_append_head armTimerPrefix; exact arm_appends _ _ _ _)
    | joint_append_step

/-- The real worker includes handshake allocation refusals, socket errno returns
and every early Stop. Only actual lifetime events are appended. -/
theorem handshakeSendWorkerPrefix_appends (pid : PeerId) : StateAppends (handshakeSendWorkerPrefix pid) := by
  unfold handshakeSendWorkerPrefix sendHandshakeInitiationPrefix timersTraversalPrefix
    timersAnyAuthenticatedPacketSentPrefix timersHandshakeInitiatedPrefix delTimerPrefix modPeerTimerGuardPrefix
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (joint_append_head createInitiationPrefix; exact initiation_appends _)
    | (joint_append_head addMacToPacketPrefix; exact mac_appends _ _)
    | (joint_append_head sendBufferToPeerPrefix; exact sendBuffer_appends _ _)
    | (joint_append_head modPeerTimerPrefix; exact modTimer_appends _ _ _ _)
    | (joint_append_head armTimerPrefix; exact arm_appends _ _ _ _)
    | joint_append_step

private theorem clearKeys_appends (pid : PeerId) : StateAppends (keypairsClearPrefix pid) := by
  unfold keypairsClearPrefix
  repeat' joint_append_step

theorem queuedExpiredZeroKeyMaterialPrefix_appends (pid : PeerId) :
    StateAppends (queuedExpiredZeroKeyMaterialPrefix pid) := by
  unfold queuedExpiredZeroKeyMaterialPrefix handshakeClearPrefix handshakeZeroPrefix
  repeat' first
    | (joint_append_head keypairsClearPrefix; exact clearKeys_appends _)
    | joint_append_step

private theorem flushedSend_appends (pid : PeerId) : StateAppends (runFlushedSendWorkPrefix pid) := by
  unfold runFlushedSendWorkPrefix
  repeat' first
    | (joint_append_head handshakeSendWorkerPrefix; exact handshakeSendWorkerPrefix_appends _)
    | joint_append_step

private theorem flushedClear_appends (pid : PeerId) : StateAppends (runFlushedClearWorkPrefix pid) := by
  unfold runFlushedClearWorkPrefix
  repeat' first
    | (joint_append_head queuedExpiredZeroKeyMaterialPrefix; exact queuedExpiredZeroKeyMaterialPrefix_appends _)
    | joint_append_step

theorem drainHandshakeSendWqPrefix_appends (upTo : Option PeerId) :
    StateAppends (drainHandshakeSendWqPrefix upTo) := by
  unfold drainHandshakeSendWqPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (joint_append_head runFlushedSendWorkPrefix; exact flushedSend_appends _)
    | (joint_append_head runFlushedClearWorkPrefix; exact flushedClear_appends _)
    | joint_append_step

private theorem timersStop_appends (pid : PeerId) : StateAppends (timersStopPrefix pid) := by
  unfold timersStopPrefix delTimerPrefix
  repeat' first
    | (joint_append_head drainHandshakeSendWqPrefix; exact drainHandshakeSendWqPrefix_appends _)
    | joint_append_step

theorem peerRemoveAfterDeadPrefix_appends (pid : PeerId) : StateAppends (peerRemoveAfterDeadPrefix pid) := by
  unfold peerRemoveAfterDeadPrefix
  repeat' first
    | (joint_append_head keypairsClearPrefix; exact clearKeys_appends _)
    | (joint_append_head timersStopPrefix; exact timersStop_appends _)
    | (joint_append_head drainHandshakeSendWqPrefix; exact drainHandshakeSendWqPrefix_appends _)
    | joint_append_step

theorem peerMakeDeadPrefix_appends (pid : PeerId) : StateAppends (peerMakeDeadPrefix pid) := by
  unfold peerMakeDeadPrefix
  repeat' first
    | (joint_append_head removeByPeerPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationUpdate.«0».Leanux.Proofs.WG.Queues.RoutingJoint.replace_appends) _)
    | joint_append_step

theorem peerRemovePrefix_appends (peer : Option PeerId) : StateAppends (peerRemovePrefix peer) := by
  unfold peerRemovePrefix
  repeat' first
    | (joint_append_head peerMakeDeadPrefix; exact peerMakeDeadPrefix_appends _)
    | (joint_append_head peerRemoveAfterDeadPrefix; exact peerRemoveAfterDeadPrefix_appends _)
    | joint_append_step

end Leanux.Proofs.WG.Queues.RoutingJoint
