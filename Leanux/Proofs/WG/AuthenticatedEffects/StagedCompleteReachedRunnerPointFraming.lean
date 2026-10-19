import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointContract

/-! Native frame certificates retain the canonical shape through its exact
source equalities. Successful loop prefixes carry the original accumulator;
there is no invariant assigned to a fabricated failed World. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal

 theorem Framed.source_cast {left right : PrefixOuter Event α} (same : left=right)
    {shape : Shape left} (framed : Framed shape h) : Framed (same ▸ shape) h := by
  cases same; exact framed

theorem Framed.source_mpr {left right : PrefixOuter Event α} (same : left=right)
    {shape : Shape right} (framed : Framed shape h) :
    Framed ((congrArg Shape same).mpr shape) h := by
  cases same; exact framed

elab "runner_frame_uncast" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Framed do Lean.throwError "not a frame certificate"
  let args := target.getAppArgs
  if args.size < 2 then Lean.throwError "missing frame shape"
  let raw := args[args.size-2]!.consumeMData
  let shape := if raw.isAppOf ``id then raw.getAppArgs.back! else raw
  unless shape.isAppOf ``Eq.mpr do Lean.throwError "not a source cast"
  let parts := shape.getAppArgs
  if parts.size < 2 then Lean.throwError "missing cast proof"
  let rec expand (fuel : Nat) (proof : Lean.Expr) : Lean.MetaM Lean.Expr := do
    if proof.isAppOf ``congrArg then return proof
    match fuel with
    | 0 => return proof
    | n+1 =>
      match proof.getAppFn with
      | .const name levels =>
        let info ← Lean.getConstInfo name
        match info.value? true with
        | some value =>
          let unfolded := Lean.mkAppN (value.instantiateLevelParams info.levelParams levels) proof.getAppArgs
          expand n unfolded.consumeMData.headBeta
        | none => return proof
      | _ => return proof
  let proof ← expand 8 parts[parts.size-2]!.consumeMData
  unless proof.isAppOf ``congrArg do Lean.throwError m!"not a canonical source congruence: {proof.getAppFn} ({proof.getAppArgs.size} args), {proof}"
  let proofArgs := proof.getAppArgs
  if proofArgs.size < 4 then Lean.throwError "incomplete source congruence"
  let same := proofArgs.back!
  let function := proofArgs[proofArgs.size-2]!
  let functionType ← Lean.Meta.whnf (← Lean.Meta.inferType function)
  let .forallE _ domain _ _ := functionType | Lean.throwError "not a unary source congruence"
  Lean.Meta.withLocalDeclD `source domain fun source => do
    let shaped := (Lean.mkApp function source).headBeta.consumeMData
    unless shaped.isAppOf ``Shape do Lean.throwError "source congruence does not produce Shape"
    let some action := shaped.getAppArgs.back? | Lean.throwError "missing congruent source"
    let lifted ← Lean.Meta.mkLambdaFVars #[source] action
    let equation ← Lean.Meta.mkAppM ``congrArg #[lifted,same]
    let frameType ← Lean.Meta.mkAppM ``Framed #[parts.back!,args.back!]
    let frame ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar frameType
    let result ← Lean.Meta.mkAppM ``Framed.source_mpr #[equation,frame]
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let more ← goal.apply result
      return frame.mvarId! :: more

theorem list_framed (xs : List ι) (state : σ)
    (body : ι→σ→PrefixOuter Event (ForInStep σ)) (shapes : ∀i s,Shape (body i s))
    (I : σ→History→Prop)
    (frames : ∀i s h,I s h→Framed (shapes i s) h)
    (normal : ∀i s h decision last,I s h→runPrefixOuter (body i s) h=(.ok decision,last)→I decision.value last)
    (before : I state h) : Framed (listShape xs state body shapes) h := by
  induction xs generalizing state h with
  | nil => exact .pure _
  | cons i rest ih =>
    unfold listShape
    apply Framed.source_cast
    apply Framed.bind (frames i state h before)
    intro decision last performed
    cases decision with
    | done final => exact .pure _
    | yield next => exact ih next (normal i state h (.yield next) last before performed)

theorem array_pure_framed (xs : Array ι) (state : σ) (body : ι→σ→ForInStep σ) :
    Framed (arrayShape xs state (fun i s=>pure (body i s)) (fun i s=>.pure (body i s))) h := by
  unfold arrayShape
  runner_frame_uncast
  exact list_framed _ _ _ _ (fun _ _=>True) (fun _ _ _ _=>.pure _) (fun _ _ _ _ _ _ _=>True.intro) True.intro

theorem callback_framed (callback : Callback) (index : Nat) (w : World)
    (before : CompleteProduct.Carrier h w) : Framed (callbackShape callback index w) h := by
  cases callback <;> exact before

theorem callback_checked (callback : Callback) : CompletePrefix.Product.Checked callback.action := by
  cases callback with
  | sends => exact CompletePrefix.Product.Execution.sends
  | idle => exact CompletePrefix.Product.Execution.idle
  | afterXmit => exact CompletePrefix.Product.Execution.after_xmit
  | advance => exact CompletePrefix.Product.Execution.advance
  | route => exact CompletePrefix.Product.product_store _ Framing.routeIntoWg0_sameKernel
  | cleanup => exact CompletePrefix.Product.cleanup

theorem sequence_framed (call : Syscall) (actions : List Callback)
    (offset index : Nat) (w : World)
    (before : CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe h w) :
    Framed (sequenceShape call actions offset index w) h := by
  induction actions generalizing offset w h with
  | nil => simp only [sequenceShape]; repeat' runner_frame_uncast; exact .pure _
  | cons action rest ih =>
    simp only [sequenceShape]
    repeat' runner_frame_uncast
    apply Framed.bind (.marked _ _ before.1 (callback_framed action index w before.1))
    intro out last performed
    exact ih _ _ (checked_normal (callback_checked action) before performed)

theorem after_dispatch_framed (call : Syscall) (ret : Int) (index : Nat) (w : World)
    (before : CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe h w) :
    Framed (afterDispatchShape call ret index w) h := by
  unfold afterDispatchShape
  repeat' runner_frame_uncast
  apply Framed.bind (.native _ before.1)
  intro out middle preludeRun
  have next := checked_normal ReturnSource.prelude_checked before preludeRun
  runner_frame_uncast
  repeat' runner_frame_uncast
  apply Framed.bind (sequence_framed call _ 0 index out.2 next)
  intro after last sequenceRun
  have sequenceRun' := sequenceRun
  rw [callbacks_source] at sequenceRun'
  have final := checked_normal (ReturnSource.sequence_checked _ (fun action member=>ReturnSource.callback_checked call action member)) next sequenceRun'
  repeat' runner_frame_uncast
  apply Framed.bind (.native _ final.1)
  intro done ending routingRun
  repeat' runner_frame_uncast
  exact .pure _

theorem syscall_framed (call : Syscall) (index : Nat) (w : World)
    (before : CompletePrefix.Runner.Entry h w) : Framed (syscallShape call index w) h := by
  unfold syscallShape
  repeat' runner_frame_uncast
  apply Framed.bind (.native _ before.1.1)
  intro entered middle enterRun
  have entry : CompletePrefix.With CompleteRunner.DeleteFrames.Entry CompleteProduct.Safe h w :=
    ⟨⟨before.1.1,before.1.2.1,before.1.2.2.1⟩,before.2⟩
  have next := checked_normal (SyscallSource.enter_checked call) entry enterRun
  repeat' runner_frame_uncast
  apply Framed.bind (.child (.dispatch call) next)
  intro out last dispatchRun
  exact after_dispatch_framed call out.1 index out.2
    (checked_normal (RunnerSource.dispatch_checked call) next dispatchRun)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
