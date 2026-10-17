import Leanux.Proofs.WG.Origins.CurrentChecks
import Leanux.Proofs.WG.Origins.CurrentReceiveHistory

/-! The existing receive observers preserve positional current-identity checks.
Their actual lifetime and session suffixes contain no decrypt or copied-probe
events. The equalities below include failed prefixes and arbitrary old history. -/
namespace Leanux.Proofs.WG.CurrentReceiveChecks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins
open Origins.HistorySupport (sensitive)

private theorem focus_frame {E F G State α : Type}
    (enc : E → F) (dec : F → Option E) (projection : F → Option G)
    (g : PrefixT E State α) (appends : Appends g)
    (frame : HistoryFrame (fun e => projection (enc e)) g) :
    HistoryFrame projection (focusPrefix enc dec g) := by
  intro w h
  obtain ⟨suffix,hs⟩ := appends w (h.filterMap dec)
  have projected := frame w (h.filterMap dec)
  rw [hs,List.filterMap_append] at projected
  have empty : suffix.filterMap (fun e => projection (enc e)) = [] := by
    simpa using projected
  have hr : runPrefix g w (h.filterMap dec) =
      ((runPrefix g w (h.filterMap dec)).1,h.filterMap dec ++ suffix) := Prod.ext rfl hs
  rw [focusPrefix_suffix enc dec g w h _ suffix hr]
  simp only [List.filterMap_append,List.filterMap_map,Function.comp_def,empty,List.append_nil]

private theorem life_frame (g : PrefixM LifetimeEvent α) :
    HistoryFrame (fun e => sensitive (HistoryAdapters.encode e)) (HistoryAdapters.life g) :=
  focusPrefix_other _ _ _ (fun _ => rfl) g

private theorem session_frame (pid : PeerId) :
    HistoryFrame (fun e => sensitive (HistoryAdapters.encode e))
      (liftWGObserver (Origins.localSession pid)) := by
  apply StateHistoryFrame.liftWGObserver
  intro w ambient h
  exact focusPrefix_other _ _ _ (by intro e; cases e <;> rfl)
    ((SessionOrigin.observed pid).run w) ambient h

open Lean Meta Elab Tactic in
elab "receive_history_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``HistoryFrame do throwError "not a history frame"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let action := args.back!.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless action.getAppFn.constName? == some expected do throwError "different action head"

open Lean Meta Elab Tactic in
/-- Prove each source join once; the generated application is kernel checked. -/
elab "receive_history_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``HistoryFrame && args.size > 0 do
    throwError "not a history frame"
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
    withLocalDeclD `receive_history_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f,hf] next,next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!,next]

open Lean Meta Elab Tactic in
elab "receive_history_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``HistoryFrame && args.size > 0 do
    throwError "not a history frame"
  let action := args.back!.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `receive_history_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

private theorem frame_ite (projection : E → Option F) (p : Prop) [Decidable p]
    (a b : PrefixT E State α) (ha : p → HistoryFrame projection a)
    (hb : ¬p → HistoryFrame projection b) :
    HistoryFrame projection (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

macro "receive_history_step" : tactic => `(tactic| first
  | receive_history_join
  | receive_history_join_use
  | (receive_history_at HistoryAdapters.life; exact life_frame _)
  | (receive_history_at liftWGObserver; exact session_frame _)
  | (receive_history_at liftPrefix; exact HistoryFrame.lift _ _)
  | (receive_history_at Pure.pure; exact HistoryFrame.pure _ _)
  | (receive_history_at Bind.bind; apply HistoryFrame.bind)
  | (receive_history_at ite; apply frame_ite)
  | (run_tac do
      unless (← Lean.Elab.Tactic.getMainTarget).isForall do Lean.throwError "not a continuation"
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))
  | split)

private theorem response_frame (pid : PeerId) :
    HistoryFrame (fun e => sensitive (HistoryAdapters.encode e))
      (HistoryAdapters.localResponse pid) := by
  unfold HistoryAdapters.localResponse HandshakeSources.responseWith
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' receive_history_step

private theorem afterMac_frame (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    HistoryFrame (fun e => sensitive (HistoryAdapters.encode e))
      (HistoryAdapters.localAfterMac msg src loaded mac) := by
  unfold HistoryAdapters.localAfterMac HandshakeSources.afterMacWith
  simp (config := {zeta := false}) only [← HistoryAdapters.localResponse_eq]
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' first
    | (receive_history_at HistoryAdapters.localResponse; exact response_frame _)
    | receive_history_step

private theorem reception_frame (msg : List UInt8) (src : SkbSource) :
    HistoryFrame (fun e => sensitive (HistoryAdapters.encode e))
      (HistoryAdapters.localReception msg src) := by
  unfold HistoryAdapters.localReception HandshakeSources.receptionWith
  simp (config := {zeta := false}) only [← HistoryAdapters.localAfterMac_eq]
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' first
    | (receive_history_at HistoryAdapters.localAfterMac; exact afterMac_frame _ _ _ _)
    | receive_history_step

private theorem step_frame :
    HistoryFrame (fun e => sensitive (HistoryAdapters.encode e)) HistoryAdapters.localStep := by
  unfold HistoryAdapters.localStep HandshakeSources.stepWith
  simp (config := {zeta := false}) only [← HistoryAdapters.localReception_eq]
  dsimp (config := {zeta := false}) only [HistoryAdapters.ops]
  repeat' first
    | (receive_history_at HistoryAdapters.localReception; exact reception_frame _ _)
    | receive_history_step

theorem response (pid : PeerId) :
    CurrentChecks.Preserves (HistoryAdapters.focus (HistoryAdapters.localResponse pid)) :=
  CurrentChecks.quiet _ (Appends.focus _ _ _)
    (focus_frame _ _ sensitive _ (HistoryAdapters.localResponse_appends pid) (response_frame pid))
    (HistorySupport.response pid) (CurrentReceiveHistory.response pid)

theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    CurrentChecks.Preserves (HistoryAdapters.focus (HistoryAdapters.localAfterMac msg src loaded mac)) :=
  CurrentChecks.quiet _ (Appends.focus _ _ _)
    (focus_frame _ _ sensitive _ (HistoryAdapters.localAfterMac_appends msg src loaded mac)
      (afterMac_frame msg src loaded mac))
    (HistorySupport.afterMac msg src loaded mac) (CurrentReceiveHistory.afterMac msg src loaded mac)

theorem reception (msg : List UInt8) (src : SkbSource) :
    CurrentChecks.Preserves (HistoryAdapters.focus (HistoryAdapters.localReception msg src)) :=
  CurrentChecks.quiet _ (Appends.focus _ _ _)
    (focus_frame _ _ sensitive _ (HistoryAdapters.localReception_appends msg src) (reception_frame msg src))
    (HistorySupport.reception msg src) (CurrentReceiveHistory.reception msg src)

theorem receiveStep : CurrentChecks.Preserves HistoryAdapters.receiveStep :=
  CurrentChecks.quiet _ (Appends.focus _ _ _)
    (focus_frame _ _ sensitive _ HistoryAdapters.localStep_appends step_frame)
    HistorySupport.receiveStep CurrentReceiveHistory.receiveStep

private theorem reschedule :
    CurrentChecks.Preserves (liftPrefix (Env.condResched .receiveWorker)) := by
  apply CurrentChecks.quiet _ (Appends.lift _) (HistoryFrame.lift _ _)
    (HistorySupport.lift_kernel _ (condResched_sameKernel .receiveWorker))
  apply CurrentHistory.lift
  intro history
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi hr
  have store := (ProjectedAction.iff_run _ _ _).mp
    (condResched_sameKernel .receiveWorker) w value v hr
  have dev : v.wg.dev = w.wg.dev :=
    congrArg (fun s : ProductStore43 => s.2.2.2.dev) store
  constructor
  · intro state hs
    exact hi.1 state (by simpa only [ConfiguredIdentity.view,dev] using hs)
  · intro d hd slot key hk valid
    exact hi.2 d (dev.symm.trans hd) slot key hk valid

theorem receiveIteration : CurrentChecks.Preserves HistoryAdapters.receiveIteration :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => ⟨hi.1.1,hi.2.2⟩) receiveStep reschedule

end Leanux.Proofs.WG.CurrentReceiveChecks
