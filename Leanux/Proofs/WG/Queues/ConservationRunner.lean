import Leanux.Proofs.WG.Queues.ConservationCertified

/-! Build a concrete certificate for the existing runner body. Only proof
constructors are composed; the runner action and its accumulator are unchanged. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationRunner
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open ConservationCertified

private def entry (w : World) : Ledger→List RxHistory.Event→Prop :=
  fun cs h=>HolderEntry.Inv cs [] h w

private def resultAssertion (type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.withLocalDeclD `out type fun out => do
    let world? ←
      if ← Lean.Meta.isDefEq type (Lean.mkConst ``World) then pure (some out)
      else if type.isAppOf ``Prod && type.getAppArgs.size == 2 then
        let args := type.getAppArgs
        if ← Lean.Meta.isDefEq args[0]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 0 out))
        else if ← Lean.Meta.isDefEq args[1]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 1 out))
        else pure none
      else pure none
    let assertion ← match world? with
      | some w => Lean.Meta.mkAppM ``entry #[w]
      | none => pure pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "conservation_runner_head " name:ident : tactic => do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Certified do Lean.throwError "not a certified action"
  let action := target.getAppArgs[target.getAppArgs.size-3]!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("."++expected) do
    Lean.throwError "different action"

elab "conservation_runner_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Certified do Lean.throwError "not a certified action"
  let args := target.getAppArgs
  let action := args[args.size-3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let type ← Lean.Meta.inferType aa[aa.size-2]!
  let q ← resultAssertion type.getAppArgs.back! args[args.size-2]!
  let qs ← Lean.PrettyPrinter.delab q
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply ConservationCertified.bind (Q := $qs)))

elab "conservation_runner_loop" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
  unless target.isAppOf ``Certified do Lean.throwError "not a certified action"
  let args := target.getAppArgs
  let action := args[args.size-3]!.consumeMData
  unless action.isAppOf ``ForIn.forIn do Lean.throwError "not a source loop"
  let aa := action.getAppArgs
  let type ← Lean.Meta.inferType aa[aa.size-2]!
  let q ← resultAssertion type args[args.size-2]!
  let qs ← Lean.PrettyPrinter.delab q
  Lean.Elab.Tactic.evalTactic (← `(tactic| first
    | apply ConservationCertified.array (I := $qs)
    | apply ConservationCertified.forIn (I := $qs)))

elab "conservation_runner_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Certified do Lean.throwError "not a certified action"
  let .app (.app (.app front action) pre) post := target | Lean.throwError "missing action"
  let rec head : Nat→Lean.Expr→Lean.Expr
    | 0,e=>e
    | n+1,e=>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _=>head n (body.instantiate1 value)
      | _=>match e.getAppFn.consumeMData with
        | .letE _ _ value body _=>head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam ..=>let next := e.headBeta; if Lean.Expr.equal next e then e else head n next
        | _=>e
  let mut next := head 64 action
  if (← Lean.Meta.matchMatcherApp? next).isSome then
    if let .reduced reduced ← Lean.Meta.reduceMatcher? next then next := reduced
  if Lean.Expr.equal action next then Lean.throwError "head unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp3 front next pre post)]

elab "conservation_runner_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Certified do Lean.throwError "not a certified action"
  let action := target.getAppArgs[target.getAppArgs.size-3]!.consumeMData
  unless (← Lean.Meta.matchMatcherApp? action).isSome do Lean.throwError "not a head matcher"
  Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

def tail (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (w : World) :
    Certified (RoutingJoint.runnerTailWith call (fun j v=>(j,v)) trace w)
      (entry w) (fun out=>entry out.2) := by
  have syscall (index : Nat) (w : World) (c : Syscall)
      {P : Ledger→List RxHistory.Event→Prop} {Q : Int × World→Ledger→List RxHistory.Event→Prop} :=
    ConservationCertified.runAt (P:=P) (Q:=Q) index w (rules c) (established c)
  have ambient (index : Nat) (w : World)
      {P : Ledger→List RxHistory.Event→Prop} {Q : Unit × World→Ledger→List RxHistory.Event→Prop} :=
    ConservationCertified.runAt (P:=P) (Q:=Q) index w (HolderTrafficDispatch.lift (skipAmbient : Leanux.M Unit))
      (HolderTrafficDispatch.lift_established _
        (fun initial=>productAmbient_spec _ _ (fun _ _ hi=>hi)) (loans:=[]))
  unfold RoutingJoint.runnerTailWith
  repeat' first
    | (conservation_runner_head runAtPrefix; first | apply syscall | apply ambient)
    | (conservation_runner_head Pure.pure; apply ConservationCertified.pure)
    | (conservation_runner_head throw; exact ConservationCertified.stopped _)
    | conservation_runner_bind
    | conservation_runner_loop
    | conservation_runner_reduce
    | (conservation_runner_head ite; apply ConservationCertified.branch)
    | maintenance_intro
    | conservation_runner_match
  all_goals try dsimp only [entry] at *
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro cs h hi; exact HolderEntryDispatch.wg_store hi rfl)
  all_goals rename_i hi
  all_goals exact HolderEntryDispatch.wg_store hi rfl

private theorem boot_store (foreign : Bool) : SameView (fun w=>wgStoreView w.wg)
    (do Net.Fib.bootTables
        if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
  apply SameView.bind
  · intro initial
    exact productRouting_spec _ (fun s=>s.2.2.2=initial)
  · intro _
    split
    · intro initial
      exact productRouting_spec _ (fun s=>s.2.2.2=initial)
    · exact SameView.pure _ _

/-- Initialization uses the actual fixture, seccomp prefill and optional FIB
boot. Their failure arms have no normal certificate. -/
def initialized (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (placeholders : Bool) :
    Certified (RoutingJoint.executeTraceWith call (fun j v=>(j,v)) trace placeholders)
      (fun cs h=>cs=[] ∧ h=[]) (fun out=>entry out.2) := by
  have tail_spec (w : World) {P : Ledger→List RxHistory.Event→Prop}
      (pre : ∀cs h,P cs h→entry w cs h) :
      Certified (RoutingJoint.runnerTailWith call (fun j v=>(j,v)) trace w) P (fun out=>entry out.2) := by
    refine ⟨(tail call rules established trace w).rule,?_⟩
    intro cs h out k hi run
    exact (tail call rules established trace w).establishes (pre cs h hi) run
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w=.ok (x,v))
      (hi : wgStoreView w.wg=wgStoreView (initialWG trace.net trace.bare)) :
      wgStoreView v.wg=wgStoreView (initialWG trace.net trace.bare) :=
    ((Lifetimes.ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  unfold RoutingJoint.executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp,↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (conservation_runner_head RoutingJoint.runnerTailWith; apply tail_spec)
    | (conservation_runner_head throw; exact ConservationCertified.stopped _)
    | conservation_runner_reduce
    | (conservation_runner_head ite; apply ConservationCertified.branch)
    | conservation_runner_match
    | (conservation_runner_head Bind.bind; exact ConservationCertified.stopped _)
    | (intro)
  all_goals rename_i hi
  all_goals obtain ⟨rfl,rfl⟩ := hi
  all_goals apply HolderEntry.initialized trace.net trace.bare
  all_goals first
    | rfl
    | rename_i run
      have hb := boot_initial _ _ _ run (by rfl)
      exact hb

end Leanux.Proofs.WG.Queues.RxCredits.ConservationRunner
