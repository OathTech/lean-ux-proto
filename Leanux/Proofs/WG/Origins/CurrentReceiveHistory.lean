import Leanux.Proofs.WG.Origins.CurrentFocus
import Leanux.Proofs.WG.Origins.SupportCallers
import Leanux.Proofs.WG.Origins.CurrentTraffic
import Leanux.Proofs.WG.Origins.ConfiguredReceiveLeaves

/-! Current configured identity through the existing receive observers. Session
receipts use their actual journal cut; other steps preserve the incoming session
history. No initialized-history or successful-execution premise is added. -/
namespace Leanux.Proofs.WG.CurrentReceiveHistory
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Origins ConfiguredHandshake ConfiguredReceiveLeaves
open CurrentHistory

private theorem store_preserves {α : Type} (a : WG.M α)
    (frame : SameView wgStoreView a) (history : List SessionOrigin.Receipt) :
    Framing.Preserves (CurrentLifecycle.Inv history) a :=
  current_preserves a (ConfiguredIdentity.sameWG (project := id) frame)
    (Retaining.of_view (Origins.sameView_of_sameWG (project := id) frame)) history

private theorem cookie_preserves {α : Type} (a : WG.M α)
    (frame : SameCookie a) (history : List SessionOrigin.Receipt) :
    Framing.Preserves (CurrentLifecycle.Inv history) a := by
  apply current_preserves a ?_
    (Retaining.of_view (Retaining.cookie_material_native a (frame.factor WGOwnedView.toWGStoreView))) history
  apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
    ConfiguredIdentity.view
  intro w
  simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
    ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

private theorem pay_preserves (peer : Option PeerId) (history : List SessionOrigin.Receipt) :
    Framing.Preserves (CurrentLifecycle.Inv history) (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.peerPut_preserves peer)
      w ambient result v ambient' hi.1 hr,
    hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
      (CurrentIdentity.peerPut_retains peer) w ambient result v ambient' hr)⟩

private theorem native_life (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a)
    (ha : ∀ history, Framing.Preserves (CurrentLifecycle.Inv history) a) :
    Focused HistoryAdapters.encode HistoryAdapters.decode
      (HistoryAdapters.life (liftWGObserver g)) :=
  ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases he) (native_product a ha)⟩

private theorem view_life (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hv : SameView ConfiguredIdentity.view a)
    (hm : SameView Origins.view a) :
    Focused HistoryAdapters.encode HistoryAdapters.decode
      (HistoryAdapters.life (liftWGObserver g)) :=
  native_life g a he (fun history => current_preserves a hv (Retaining.of_view hm) history)

open Lean Meta Elab Tactic in
elab "current_focused_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``CurrentHistory.Focused do throwError "not a focused current contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "no action"
  let mut action := args.back!.consumeMData
  for wrapper in [``HistoryAdapters.life, ``liftWGObserver] do
    if action.isAppOf wrapper then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing wrapped action"
      action := fields.back!.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless action.getAppFn.constName? == some expected do throwError "different focused action head"

open Lean Meta Elab Tactic in
/-- Prove each source join once; the generated application is kernel checked. -/
elab "current_focus_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``CurrentHistory.Focused && args.size > 0 do
    throwError "not a focused current contract"
  let i := args.size - 1
  let action := args[i]!.consumeMData
  let property := fun a => mkAppN target.getAppFn (args.set! i a)
  let beta := action.headBeta
  unless Expr.equal action beta do
    replaceMainGoal [← goal.replaceTargetDefEq (property beta)]
    return
  let .letE name ty value body _ := action | throwError "not a source let"
  unless name.toString.startsWith "__do_jp" do
    replaceMainGoal [← goal.replaceTargetDefEq (property (body.instantiate1 value))]
    return
  let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof,next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN f xs))
    withLocalDeclD `current_focused_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f,hf] next,next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!,next]

open Lean Meta Elab Tactic in
elab "current_focus_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``CurrentHistory.Focused && args.size > 0 do
    throwError "not a focused current contract"
  let action := args.back!.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `current_focused_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

macro "current_focus_native" : tactic => `(tactic| (
  apply focused_lift
  apply native_product
  intro history
  try simp (config := {zeta := false}) only [branch,hiddenClock64,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head Cookies.loadPhase
       exact store_preserves _ Cookies.loadPhase_sameStore history)
    | (rx_retention_head cookieValidatePacket
       exact cookie_preserves _ (cookieValidatePacket_sameCookie _ _ _) history)
    | current_lifecycle_step history))

macro "current_receive_focused" : tactic => `(tactic| first
  | current_focus_join
  | current_focus_join_use
  | (current_focused_at Origins.localSession
     exact ⟨(StateAppends.focus _ _ _).liftWGObserver,CurrentSessionPrefix.session _⟩)
  | (current_focused_at modifyPeerKeysPrefix
     apply view_life _ _ (modifyPeerKeysPrefix_erases _ _)
     · apply ConfiguredIdentity.modifyPeer_view; intro p; rfl
     exact Retaining.modifyPeer_material _ _)
  | (current_focused_at createResponsePrefix
     exact native_life _ _ (createResponsePrefix_erases _)
       (fun history => ConfiguredReceive.createResponse_preserves _ history))
  | (current_focused_at addMacToPacketPrefix
     exact view_life _ _ (addMacToPacketPrefix_erases _ _)
       (addMacToPacket_view _ _) (Retaining.addMacToPacket_material _ _))
  | (current_focused_at sendBufferToPeerPrefix
     exact view_life _ _ (sendBufferToPeerPrefix_erases _ _)
       (sendBufferToPeer_view _ _) (Retaining.sendBufferToPeer_material _ _))
  | (current_focused_at timersSessionDerivedPrefix
     exact view_life _ _ (timersSessionDerivedPrefix_erases _)
       (timersSessionDerived_view _) (Retaining.timersSessionDerived_material _))
  | (current_focused_at timersTraversalPrefix
     exact view_life _ _ (timersTraversalPrefix_erases _)
       (ConfiguredIdentity.timersTraversal_view _) (Retaining.timersTraversal_material _))
  | (current_focused_at timersAnyAuthenticatedPacketSentPrefix
     exact view_life _ _ (timersAnyAuthenticatedPacketSentPrefix_erases _)
       (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view _)
       (Retaining.timersAnyAuthenticatedPacketSent_material _))
  | (current_focused_at sendHandshakeCookiePrefix
     exact view_life _ _ (sendHandshakeCookiePrefix_erases _ _)
       (sendHandshakeCookie_view _ _) (Origins.HistorySupport.cookieSend_material _ _))
  | (current_focused_at consumeInitiationPrefix
     exact native_life _ _ (consumeInitiationPrefix_erases _)
       (fun history => ConfiguredReceive.consumeInitiation_preserves _ history))
  | (current_focused_at consumeResponsePrefix
     exact native_life _ _ (consumeResponsePrefix_erases _)
       (fun history => ConfiguredReceive.consumeResponse_preserves _ history))
  | (current_focused_at setPeerEndpointFromSkbPrefix
     exact view_life _ _ (setPeerEndpointFromSkbPrefix_erases _ _)
       (setPeerEndpointFromSkb_view _ _) (Origins.HistorySupport.endpoint_material _ _))
  | (current_focused_at timersHandshakeCompletePrefix
     exact view_life _ _ (timersHandshakeCompletePrefix_erases _ _)
       (timersHandshakeComplete_view _ _) (Retaining.timersHandshakeComplete_material _ _))
  | (current_focused_at sendKeepalivePrefix
     exact native_life _ _ (sendKeepalivePrefix_erases _)
       (fun history => CurrentTraffic.sendKeepalive_preserves _ history))
  | (current_focused_at timersAnyAuthenticatedPacketReceivedPrefix
     exact view_life _ _ (timersAnyAuthenticatedPacketReceivedPrefix_erases _)
       (timersAnyAuthenticatedPacketReceived_view _) (Retaining.timersAnyAuthenticatedPacketReceived_material _))
  | (current_focused_at peerPutMixed
     exact native_life _ _ (peerPutMixed_erases _) (pay_preserves _))
  | (current_focused_at cookieMessageConsumePrefix
     exact native_life _ _ (cookieMessageConsumePrefix_erases _)
       (fun history => CurrentTraffic.cookieMessageConsume_preserves _ history))
  | (current_focused_at liftPrefix; current_focus_native)
  | (current_focused_at Pure.pure; exact focused_pure _ _ _)
  | (current_focused_at Bind.bind; apply focused_bind _ _ HistoryAdapters.decode_encode)
  | (current_focused_at ite; apply focused_ite)
  | (run_tac do
      unless (← Lean.Elab.Tactic.getMainTarget).isForall do Lean.throwError "not a continuation"
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))
  | split)

private theorem response_focused (pid : PeerId) :
    Focused HistoryAdapters.encode HistoryAdapters.decode (HistoryAdapters.localResponse pid) := by
  unfold HistoryAdapters.localResponse HandshakeSources.responseWith
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' current_receive_focused

theorem response (pid : PeerId) :
    CurrentHistory.Preserves (HistoryAdapters.focus (HistoryAdapters.localResponse pid)) :=
  (response_focused pid).2

private theorem afterMac_focused (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Focused HistoryAdapters.encode HistoryAdapters.decode (HistoryAdapters.localAfterMac msg src loaded mac) := by
  unfold HistoryAdapters.localAfterMac HandshakeSources.afterMacWith
  simp (config := {zeta := false}) only [← HistoryAdapters.localResponse_eq]
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' first
    | (current_focused_at HistoryAdapters.localResponse; exact response_focused _)
    | current_receive_focused

theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    CurrentHistory.Preserves (HistoryAdapters.focus (HistoryAdapters.localAfterMac msg src loaded mac)) :=
  (afterMac_focused msg src loaded mac).2

private theorem reception_focused (msg : List UInt8) (src : SkbSource) :
    Focused HistoryAdapters.encode HistoryAdapters.decode (HistoryAdapters.localReception msg src) := by
  unfold HistoryAdapters.localReception HandshakeSources.receptionWith
  simp (config := {zeta := false}) only [← HistoryAdapters.localAfterMac_eq]
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' first
    | (current_focused_at HistoryAdapters.localAfterMac; exact afterMac_focused _ _ _ _)
    | current_receive_focused

theorem reception (msg : List UInt8) (src : SkbSource) :
    CurrentHistory.Preserves (HistoryAdapters.focus (HistoryAdapters.localReception msg src)) :=
  (reception_focused msg src).2

theorem receiveStep : CurrentHistory.Preserves HistoryAdapters.receiveStep := by
  have proof : Focused HistoryAdapters.encode HistoryAdapters.decode HistoryAdapters.localStep := by
    unfold HistoryAdapters.localStep HandshakeSources.stepWith
    simp (config := {zeta := false}) only [← HistoryAdapters.localReception_eq]
    dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
    repeat' first
      | (current_focused_at HistoryAdapters.localReception; exact reception_focused _ _)
      | current_receive_focused
  exact proof.2

end Leanux.Proofs.WG.CurrentReceiveHistory
