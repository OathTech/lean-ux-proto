import Leanux.Proofs.WG.Queues.RunnerSelectionData
import Leanux.Proofs.WG.Queues.RunnerAccount

/-! Queries specialize the existing runner certificate. At the actual syscall
leaf, selection retains its operation index and the inner traffic index. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerSelection
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open AdmissionSelection RunnerSelectionData

elab "runner_selection_head " name:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Selection do Lean.throwError "not runner selection"
  let args := target.getAppArgs
  unless args.size > 0 do Lean.throwError "missing outer rule"
  let rule := args.back!.consumeMData
  let checked ← match rule with
    | .proj _ _ checked=>pure checked
    | _=>
      let fields := rule.getAppArgs
      unless fields.size > 0 do Lean.throwError "missing checked projection"
      pure fields.back!
  let rec head : Nat→Lean.Expr→Lean.Expr
    | 0,e=>e
    | n+1,e=>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _=>head n (body.instantiate1 value)
      | _=>match e.getAppFn.consumeMData with
        | .letE _ _ value body _=>head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam ..=>let next := e.headBeta; if Lean.Expr.equal next e then e else head n next
        | .const ``id _=>if e.getAppArgs.isEmpty then e else head n e.getAppArgs.back!
        | _=>e
  let checked := head 64 checked
  let .const actual _ := checked.getAppFn | Lean.throwError "not a checked constructor"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("."++expected) do
    Lean.throwError "different checked constructor"

elab "runner_selection_intro" : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isForall do Lean.throwError "not a literal function contract"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

elab "runner_selection_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Selection do Lean.throwError "not runner selection"
  let args := target.getAppArgs
  unless args.size > 0 do Lean.throwError "missing outer rule"
  let rule := args.back!.consumeMData
  let (checked,rebuild) : Lean.Expr × (Lean.Expr→Lean.Expr) ← match rule with
    | .proj structName index checked=>pure (checked,fun changed=>.proj structName index changed)
    | _=>
      let fields := rule.getAppArgs
      unless fields.size > 0 do Lean.throwError "missing checked rule projection"
      pure (fields.back!,fun changed=>Lean.mkAppN rule.getAppFn (fields.pop.push changed))
  let rec head : Nat→Lean.Expr→Lean.Expr
    | 0,e=>e
    | n+1,e=>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _=>head n (body.instantiate1 value)
      | _=>match e.getAppFn.consumeMData with
        | .letE _ _ value body _=>head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam ..=>let next := e.headBeta; if Lean.Expr.equal next e then e else head n next
        | .const ``id _=>if e.getAppArgs.isEmpty then e else head n e.getAppArgs.back!
        | _=>e
  let reduced := head 64 checked
  let reduced ← if Lean.Expr.equal checked reduced then
      match ← Lean.Meta.reduceRecMatcher? reduced with
      | some result=>pure result
      | none=>
        match ← Lean.Meta.delta? reduced (fun name=>
          name.toString.endsWith ".splitter" || (name.toString.splitOn "_sparseCasesOn_").length > 1) with
        | some result=>pure result
        | none=>Lean.throwError "no checked-head reduction"
    else pure reduced
  if Lean.Expr.equal checked reduced then Lean.throwError "checked head unchanged"
  let next := Lean.mkAppN target.getAppFn (args.pop.push (rebuild reduced))
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq next]

/-- Generalize only a generated recursor's major/equality arguments. Its
source expression and motive stay fixed, avoiding invalid global rewrites. -/
elab "runner_selection_except" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Selection do Lean.throwError "not runner selection"
  let args := target.getAppArgs
  unless args.size > 0 do Lean.throwError "missing outer rule"
  let rule := args.back!.consumeMData
  let (checked,rebuild) : Lean.Expr × (Lean.Expr→Lean.Expr) ← match rule with
    | .proj structName index checked=>pure (checked,fun changed=>.proj structName index changed)
    | _=>
      let fields := rule.getAppArgs
      unless fields.size > 0 do Lean.throwError "missing checked rule projection"
      pure (fields.back!,fun changed=>Lean.mkAppN rule.getAppFn (fields.pop.push changed))
  unless checked.isAppOf ``Except.rec do Lean.throwError "not an exception recursor"
  let .recInfo info ← Lean.getConstInfo ``Except.rec | Lean.throwError "not a recursor"
  let majorIndex := info.getMajorIdx
  let fields := checked.getAppArgs
  unless fields.size == majorIndex+2 do Lean.throwError "not an equality-indexed recursor"
  let major := fields[majorIndex]!
  let equality := fields[majorIndex+1]!
  let type ← Lean.Meta.inferType major
  let next ← Lean.Meta.withLocalDeclD `sourceResult type fun result=>do
    let recursor :=  Lean.mkAppN checked.getAppFn ((fields.extract 0 majorIndex).push result)
    let partialType ← Lean.Meta.whnf (← Lean.Meta.inferType recursor)
    unless partialType.isForall do Lean.throwError "no recursor equality binder"
    Lean.Meta.withLocalDeclD `sourceEquality partialType.bindingDomain! fun equation=>do
      let changed := Lean.mkApp recursor equation
      let body := Lean.mkAppN target.getAppFn (args.pop.push (rebuild changed))
      let quantified ← Lean.Meta.mkForallFVars #[result,equation] body
      Lean.Meta.mkFreshExprMVar quantified
  goal.assign (Lean.mkAppN next #[major,equality])
  Lean.Elab.Tactic.replaceMainGoal [next.mvarId!]
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro sourceResult sourceEquality; cases sourceResult))

macro "runner_selection_steps" queries:ident chosen:ident effects:ident : tactic =>
  `(tactic|
    (repeat' first
    | (runner_selection_head pure; exact certified_pure _ _)
    | (runner_selection_head stopped; exact certified_stopped _)
    | (runner_selection_head bind; apply certified_bind)
    | (runner_selection_head array; apply certified_array)
    | (runner_selection_head forIn; apply certified_forIn)
    | (runner_selection_head branch; apply certified_branch)
    | (runner_selection_head mpr; apply certified_mpr (same:=by first | rfl | simp only [RoutingJoint.executeTraceWith, *, ↓reduceIte]))
    | (runner_selection_head runAt; first | exact RunnerSelectionData.runAt _ _ _ ($queries _) ($chosen _) ($effects _) | exact quietRunAt _ _ _ (ConservationEffects.lift _))
    | runner_selection_intro
    | runner_selection_reduce
    | dsimp (config := {failIfUnchanged := true}) only
    | split))


macro "runner_quiet_selection" : tactic =>
  `(tactic|
    (repeat' first
    | contradiction
    | (runner_selection_head pure; exact certified_pure _ _)
    | (runner_selection_head stopped; exact certified_stopped _)
    | (runner_selection_head bind; apply certified_bind)
    | (runner_selection_head array; apply certified_array)
    | (runner_selection_head forIn; apply certified_forIn)
    | (runner_selection_head branch; apply certified_branch)
    | (runner_selection_head mpr; apply certified_mpr (same:=by rfl))
    | (runner_selection_head runAt; exact quietRunAt _ _ _ (ConservationEffects.lift _))
    | runner_selection_intro
    | runner_selection_reduce
    | dsimp (config := {failIfUnchanged := true}) only
    | split))

-- The pending-work cases enlarge the generated computational certificate.
set_option maxHeartbeats 1600000 in
def afterCall (op : Operation) (state : RunnerOperation.State) (ret : Int) (w : World) :
    Selection (ConservationRunner.afterCallCertified op state ret w).rule := by
  unfold ConservationRunner.afterCallCertified
  runner_quiet_selection
  rename_i advanced
  rcases advanced with ⟨ignored,⟨ambient,tasks,seccomp,fs,wg,fixture⟩⟩
  rcases ambient with ⟨env,timing,envCalls,steps,extraOut,hidden,placeholders,
    placeholderCount,suspended,units,pending,sections,netSection,steer,arm,fired,armed,steered⟩
  cases hidden with
  | none=>cases suspended <;> cases pending <;> runner_quiet_selection
  | some records=>
    cases records with
    | nil=>cases suspended <;> cases pending <;> runner_quiet_selection
    | cons record rest=>cases suspended <;> cases pending <;> runner_quiet_selection

/-- Its first query is exactly the existing syscall query at this accumulator. -/
def operation (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀c,Nat→Query (rules c))
    (chosen : ∀c inner,Fates (queries c inner))
    (effects : ∀c,ConservationEffects.Conserves (rules c))
    (trace : Trace) (op : Operation) (state : RunnerOperation.State) :
    Selection (ConservationRunner.operationCertified call rules established trace op state).rule :=
  RunnerSelectionData.bind
    (RunnerSelectionData.runAt state.2.1.size (RunnerOperation.prepare trace state)
      (rules (toSyscall state.2.1 state.2.2.1 state.2.1.size op))
      (queries _) (chosen _) (effects _))
    (fun out=>afterCall op state out.1 out.2)

def finish (trace : Trace) (state : RunnerOperation.State) :
    Selection (ConservationRunner.finishCertified trace state).rule := by
  unfold ConservationRunner.finishCertified
  runner_quiet_selection

def loop (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀c,Nat→Query (rules c))
    (chosen : ∀c inner,Fates (queries c inner))
    (effects : ∀c,ConservationEffects.Conserves (rules c))
    (trace : Trace) (state : RunnerOperation.State) :
    Selection (ConservationRunner.loopCertified call rules established trace state).rule :=
  RunnerSelectionData.array trace.ops state (RunnerOperation.operation call trace)
    (fun op acc=>(ConservationRunner.operationCertified call rules established trace op acc).rule)
    (operation call rules established queries chosen effects trace)

/-- The actual runner tail, including returned-state decisions, carries every
selected syscall admission through its actual subsequent operations. -/
def tail (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (queries : ∀c,Nat→Query (rules c))
    (chosen : ∀c inner,Fates (queries c inner))
    (effects : ∀c,ConservationEffects.Conserves (rules c))
    (trace : Trace) (w : World) :
    Selection (ConservationRunner.tail call rules established trace w).rule :=
  let selected := RunnerSelectionData.bind
    (loop call rules established queries chosen effects trace (w,#[],#[],#[],#[],#[]))
    (finish trace)
  { query := selected.query, fates := selected.fates, effects := selected.effects }

end Leanux.Proofs.WG.Queues.RxCredits.RunnerSelection
