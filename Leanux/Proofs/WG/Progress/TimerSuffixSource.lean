import Lean
import Leanux.Proofs.WG.Progress.CutJitterSuffixSource
import Leanux.WG.Timers
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Noise

theorem native_map {α β : Type} (records : List HiddenRecord) (f : α → β)
    (action : WG.M α) (keep : NativeKeeps records action) :
    NativeKeeps records (f <$> action) := by
  rw [map_eq_pure_bind]
  exact native_bind records _ _ keep (fun _=>native_pure records _)

theorem native_getAmbient (records : List HiddenRecord) :
    NativeKeeps records (getAmbient : WG.M Ambient) :=
  native_ambient records _ ((hoare_iff_run _ _ _).mpr (by
    intro before value after pre run
    cases run
    exact pre))

theorem native_jiffies (records : List HiddenRecord) (site : HiddenSite) :
    NativeKeeps records (hiddenJiffies site) := by
  apply native_ambient
  unfold AmbientM.hiddenJiffies
  exact preserves_bind (hoare_consequence (hidden_after_tail site records)
    (fun _ h=>h) (fun _ _ h=>strict_tail h)) (fun _=>preserves_pure _)

theorem native_peek (records : List HiddenRecord) :
    NativeKeeps records (peekHiddenSite : WG.M (Option Nat)) := by
  apply native_ambient
  unfold AmbientM.peekHiddenSite
  apply preserves_bind (retain_tail Ambient.hidden _ skipAmbient_suffix records)
  intro _
  apply preserves_bind (hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
  intro _
  exact preserves_pure _

theorem callerJiffies_retains (records : List HiddenRecord) (site : HiddenSite) :
    NativeKeeps records (callerJiffies site) := by
  unfold callerJiffies
  apply native_bind records _ _ (native_getAmbient records)
  intro a
  split
  · exact native_map records _ _ (native_jiffies records site)
  · exact native_pure records _

open Lean Meta Elab Tactic in
elab "native_suffix_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``NativeKeeps do throwError "not a native suffix contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo n
  unless action.getAppFn.constName? == some expected do throwError "different native action head"

open Lean Meta Elab Tactic in
elab "native_suffix_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    evalTactic (← `(tactic| intro))
    return
  unless target.isAppOf ``NativeKeeps do throwError "not a native suffix contract"
  let args := target.getAppArgs
  let action := args.back!.consumeMData
  let replace (next : Expr) : TacticM Unit := do
    replaceMainGoal [← goal.replaceTargetDefEq
      (mkAppN target.getAppFn (args.set! (args.size - 1) next))]
  if let .letE name _ value body _ := action then
    if name.toString.startsWith "__do_jp" then throwError "shared continuation requires join rule"
    replace (body.instantiate1 value)
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replace reduced
    return
  let head := action.getAppFn.constName?
  if head == some ``Bind.bind then
    evalTactic (← `(tactic| refine native_bind _ _ _ ?_ ?_))
  else if head == some ``Pure.pure then
    evalTactic (← `(tactic| exact native_pure _ _))
  else if head == some ``Functor.map then
    evalTactic (← `(tactic| apply native_map))
  else if head == some ``ite || head == some ``dite then
    evalTactic (← `(tactic| split))
  else if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
  else
    throwError "unhandled native suffix action head {head}"

open Lean Meta Elab Tactic in
elab "native_suffix_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``NativeKeeps do throwError "not a native suffix contract"
  let action := target.getAppArgs.back!.consumeMData
  let .letE name ty value body _ := action | throwError "not a shared continuation"
  unless name.toString.startsWith "__do_jp" do throwError "not a shared continuation"
  let records := target.getAppArgs[0]!
  let property := fun a => mkAppM ``NativeKeeps #[records,a]
  let contract ← forallTelescope ty fun xs _ => do
    mkForallFVars xs (← property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof,next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => do
      mkForallFVars xs (← property (mkAppN f xs))
    withLocalDeclD `native_suffix_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (← property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f,hf] next,next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!,next]

open Lean Meta Elab Tactic in
elab "native_suffix_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``NativeKeeps do throwError "not a native suffix contract"
  let action := target.getAppArgs.back!.consumeMData
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `native_suffix_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

theorem placeOnWheel_retains (records : List HiddenRecord) (pid : PeerId)
    (timer : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
    NativeKeeps records (placeOnWheel pid timer expires clk unit) := by
  unfold placeOnWheel
  repeat' first
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head setPeer; exact native_setPeer records _ _)
    | (native_suffix_head peekHiddenSite; exact native_peek records)
    | (native_suffix_head hidden; exact native_hidden records _)
    | (native_suffix_head get; exact native_get records)
    | (native_suffix_head modify; exact native_modify records _)
    | (native_suffix_head throw; exact native_stop records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem armTimer_retains (records : List HiddenRecord) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    NativeKeeps records (armTimer pid timer delay caller) := by
  unfold armTimer
  repeat' first
    | (native_suffix_head placeOnWheel; exact placeOnWheel_retains records _ _ _ _ _)
    | (native_suffix_head getAmbient; exact native_getAmbient records)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head hidden; exact native_hidden records _)
    | (native_suffix_head get; exact native_get records)
    | (native_suffix_head modify; exact native_modify records _)
    | (native_suffix_head throw; exact native_stop records _)
    | (native_suffix_head invariant; exact native_invariant records _)
    | (native_suffix_head unsupported; exact native_unsupported records _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem delTimer_retains (records : List HiddenRecord) (pid : PeerId) (timer : PeerTimer) :
    NativeKeeps records (delTimer pid timer) := by
  unfold delTimer
  exact native_bind records _ _ (native_getPeer records pid) (fun _=>native_setPeer records pid _)

theorem modPeerTimerGuard_retains (records : List HiddenRecord) (pid : PeerId) :
    NativeKeeps records (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuard WG.andM
  repeat' first
    | (native_suffix_head getDev; exact native_getDev records)
    | (native_suffix_head getPeer; exact native_getPeer records _)
    | (native_suffix_head branch; exact native_branch records _ _)
    | native_suffix_join
    | native_suffix_join_use
    | native_suffix_step

theorem modPeerTimer_retains (records : List HiddenRecord) (site : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    NativeKeeps records (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  exact native_bind records _ _ (callerJiffies_retains records site) (fun caller=>
    native_bind records _ _ (modPeerTimerGuard_retains records pid) (fun guard=>by
      split
      · exact native_bind records _ _ (armTimer_retains records pid timer delay caller)
          (fun _=>native_pure records _)
      · exact native_pure records _))


end Leanux.Proofs.WG.Progress.RecordSuffix
