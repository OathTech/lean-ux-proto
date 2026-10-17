import Leanux.Proofs.WG.Queues.ConservationCertified
import Leanux.Proofs.WG.Queues.RunnerOperation

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

/-- The post-call source has no admission callback. Its actual skipAmbient,
normal-exit guards and metadata loops retain the returned World entry. -/
def afterCallCertified (op : Operation) (state : RunnerOperation.State) (ret : Int) (w : World) :
    Certified (RunnerOperation.afterCall op state ret w) (entry w)
      (fun step=>entry (match step with | .done out=>out | .yield out=>out).1) := by
  have ambient (index : Nat) (w : World)
      {P : Ledger→List RxHistory.Event→Prop} {Q : Unit × World→Ledger→List RxHistory.Event→Prop} :=
    ConservationCertified.runAt (P:=P) (Q:=Q) index w (HolderTrafficDispatch.lift (skipAmbient : Leanux.M Unit))
      (HolderTrafficDispatch.lift_established _
        (fun initial=>productAmbient_spec _ _ (fun _ _ hi=>hi)) (loans:=[]))
  unfold RunnerOperation.afterCall
  repeat' first
    | (conservation_runner_head runAtPrefix; apply ambient)
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

/-- The original indexed syscall is the exposed first certificate. Its exact
converted call uses the current saved results and descriptor ends. -/
def operationCertified (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (op : Operation) (state : RunnerOperation.State) :
    Certified (RunnerOperation.operation call trace op state) (entry state.1)
      (fun step=>entry (match step with | .done out=>out | .yield out=>out).1) :=
  ConservationCertified.bind
    (ConservationCertified.runAt state.2.1.size (RunnerOperation.prepare trace state)
      (rules (toSyscall state.2.1 state.2.2.1 state.2.1.size op))
      (established _)
      (fun _ _ hi=>HolderEntryDispatch.wg_store hi rfl)
      (fun _ _ _ hi=>hi))
    (fun out=>afterCallCertified op state out.1 out.2)

/-- The unchanged final guards and JSON projection do not execute a syscall. -/
def finishCertified (trace : Trace) (state : RunnerOperation.State) :
    Certified (RunnerOperation.finishWith (fun j v=>(j,v)) trace state)
      (entry state.1) (fun out=>entry out.2) := by
  unfold RunnerOperation.finishWith
  repeat' first
    | (conservation_runner_head Pure.pure; apply ConservationCertified.pure)
    | (conservation_runner_head throw; exact ConservationCertified.stopped _)
    | conservation_runner_bind
    | conservation_runner_reduce
    | (conservation_runner_head ite; apply ConservationCertified.branch)
    | maintenance_intro
  all_goals intros; assumption

/-- The actual finite array loop uses the named operation certificate. -/
def loopCertified (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (state : RunnerOperation.State) :
    Certified (forIn trace.ops state (RunnerOperation.operation call trace))
      (entry state.1) (fun out=>entry out.1) :=
  ConservationCertified.array trace.ops state (RunnerOperation.operation call trace)
    (fun out=>entry out.1) (fun op state=>
      { rule := (operationCertified call rules established trace op state).rule
        establishes := by
          intro cs h out k hi run
          obtain ⟨next,certificate,post⟩ :=
            (operationCertified call rules established trace op state).establishes hi run
          refine ⟨next,certificate,?_⟩
          cases out <;> exact post })
    (fun _ _ hi=>hi) (fun _ _ _ hi=>hi)

def tail (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (w : World) :
    Certified (RoutingJoint.runnerTailWith call (fun j v=>(j,v)) trace w)
      (entry w) (fun out=>entry out.2) := by
  let checked := ConservationCertified.bind
    (loopCertified call rules established trace (w,#[],#[],#[],#[],#[]))
    (finishCertified trace)
  exact ⟨ConservationOuter.reindex (RunnerOperation.tail_factor call (fun j v=>(j,v)) trace w).symm checked.rule,
    ConservationOuter.reindex_ensures (RunnerOperation.tail_factor call (fun j v=>(j,v)) trace w).symm
      checked.rule checked.establishes⟩

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

/-- The literal initial World used by the existing runner. -/
def fixture (trace : Trace) (placeholders : Bool) : World :=
  { ambient :=
      { env := harnessEnv
        timing := Env.timing
        allocArmed := trace.allocArmed
        hiddenPlaceholders := placeholders && trace.hidden.isNone
        steerValues := if placeholders then trace.steer else []
        armRecords := trace.armRecords
        allocSteered := if placeholders then
          (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
          else [] }
    fs := initialFS trace.net trace.foreign trace.stepped trace.seccompChild
    tasks := initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild
    wg := { initialWG trace.net trace.bare with
      portBound := Env.portBound
      fixtureNetDevices := Env.fixtureNetDevices
      dstCacheRecords := trace.dstCacheRecords
      routing := { foreignCreator := trace.foreign } }
    fixture :=
      { netnsCHolders := if trace.foreign then [9,8,5,4] else []
        routes := trace.routes
        napiBeforePut := trace.napiBeforePut } }

/-- The actual prefill choice, with its following source left explicit. -/
def prefillWith (count : Nat) (w : World) (next : World → PrefixOuter E α) : PrefixOuter E α :=
  if count > 0 then
    match Env.seccompPrefill count w.seccomp w.tasks with
    | .ok (seccomp,tasks) => next { w with seccomp,tasks }
    | .error reason => throw (0,.invariant reason)
  else next w

/-- The actual optional boot, including the recorded-step reset on success. -/
def bootWith (net foreign : Bool) (w : World) (next : World → PrefixOuter E α) : PrefixOuter E α :=
  if net then
    match (do Net.Fib.bootTables
              if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w with
    | .ok (_,v) => next { v with ambient := { v.ambient with steps := #[], envCalls := [] } }
    | .error reason => throw (0,reason)
  else next w

/-- Exact factorization of the unchanged runner; failures retain their index. -/
theorem initialized_factor (call : Syscall → RxHistory.Obs Int)
    (trace : Trace) (placeholders : Bool) :
    RoutingJoint.executeTraceWith call (fun j v => (j,v)) trace placeholders =
      prefillWith trace.seccompPrefill (fixture trace placeholders) (fun w =>
        bootWith trace.net trace.foreign w (RoutingJoint.runnerTailWith call (fun j v => (j,v)) trace)) := by
  rfl

private def reindexCertified {action other : PrefixOuter RxHistory.Event α}
    (same : action = other) (checked : Certified action P Q) : Certified other P Q :=
  ⟨ConservationOuter.reindex same checked.rule,
    ConservationOuter.reindex_ensures same checked.rule checked.establishes⟩

/-- Prefill changes only the seccomp/task fixture fields. -/
def prefillCertified (count : Nat) (w : World) (next : World → PrefixOuter RxHistory.Event α)
    (checked : ∀v, wgStoreView v.wg = wgStoreView w.wg → Certified (next v) P Q) :
    Certified (prefillWith count w next) P Q :=
  if positive : count > 0 then
    match actual : Env.seccompPrefill count w.seccomp w.tasks with
    | .ok out => reindexCertified
        (by simp only [prefillWith, positive, ↓reduceIte, actual])
        (checked { w with seccomp := out.1, tasks := out.2 } rfl)
    | .error reason => reindexCertified
        (by simp only [prefillWith, positive, ↓reduceIte, actual])
        (ConservationCertified.stopped (0,.invariant reason))
  else reindexCertified (by simp only [prefillWith, positive, ↓reduceIte]) (checked w rfl)

/-- Boot retains the WG store while preserving its actual success/error result. -/
def bootCertified (net foreign : Bool) (w : World) (next : World → PrefixOuter RxHistory.Event α)
    (checked : ∀v, wgStoreView v.wg = wgStoreView w.wg → Certified (next v) P Q) :
    Certified (bootWith net foreign w next) P Q :=
  if enabled : net then
    match actual : (do
        Net.Fib.bootTables
        if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w with
    | .ok out => reindexCertified
        (by simp only [bootWith, enabled, ↓reduceIte, actual])
        (checked { out.2 with ambient := { out.2.ambient with steps := #[], envCalls := [] } }
          ((Lifetimes.ProjectedAction.iff_run _ _ _).mp (boot_store foreign) w out.1 out.2 actual))
    | .error reason => reindexCertified
        (by simp only [bootWith, enabled, ↓reduceIte, actual])
        (ConservationCertified.stopped (0,reason))
  else reindexCertified (by rw [bootWith, ite_eq_right enabled]) (checked w rfl)

/-- The existing tail certificate with the actual initialized entry assertion. -/
def initialTail (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (w : World)
    (store : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
    Certified (RoutingJoint.runnerTailWith call (fun j v=>(j,v)) trace w)
      (fun cs h=>cs=[] ∧ h=[]) (fun out=>entry out.2) := by
  refine ⟨(tail call rules established trace w).rule,?_⟩
  intro cs h out k hi run
  obtain ⟨rfl,rfl⟩ := hi
  exact (tail call rules established trace w).establishes
    (HolderEntry.initialized trace.net trace.bare w store) run

/-- Initialization uses the actual fixture, seccomp prefill and optional FIB
boot. Their failure arms have no normal certificate. -/
def initialized (call : Syscall→RxHistory.Obs Int)
    (rules : ∀c,ConservationSource.Rule (call c))
    (established : ∀c,HolderTrafficDispatch.Established (rules c) [])
    (trace : Trace) (placeholders : Bool) :
    Certified (RoutingJoint.executeTraceWith call (fun j v=>(j,v)) trace placeholders)
      (fun cs h=>cs=[] ∧ h=[]) (fun out=>entry out.2) := by
  let checked := prefillCertified trace.seccompPrefill (fixture trace placeholders) _ (fun w prefill =>
    bootCertified trace.net trace.foreign w _ (fun v boot =>
      initialTail call rules established trace v (boot.trans prefill)))
  exact ⟨ConservationOuter.reindex (initialized_factor call trace placeholders).symm checked.rule,
    ConservationOuter.reindex_ensures (initialized_factor call trace placeholders).symm checked.rule checked.establishes⟩

end Leanux.Proofs.WG.Queues.RxCredits.ConservationRunner
