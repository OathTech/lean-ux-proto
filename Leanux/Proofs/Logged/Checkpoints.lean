import Lean
import Leanux.Proofs.Logged.Outer
import Leanux.Runner

/-! Read-only observations at the original runner's committed checkpoints.
There is one explicit emit site after the syscall, ambient-record consumption
and every per-operation guard. The state projection is proof-side only.
Erasure preserves the original JSON and indexed failures; the emit equation
and the single source site additionally identify what each observation means. -/
namespace Leanux.Proofs.Logged
open Lean Leanux Leanux.Runner

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

-- Introduce callback parameters without unfolding the erasure contract.
elab "checkpoint_intro_forall" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro a))

elab "checkpoint_head " n:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``ErasesT do Lean.throwError "not an erasure contract"
  let args := t.getAppArgs
  unless args[args.size - 2]!.consumeMData.isAppOf n.getId do
    Lean.throwError "different observer head"

elab "checkpoint_emit_head" : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``ErasesT do Lean.throwError "not an erasure contract"
  let args := t.getAppArgs
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let binds := action.getAppArgs
  unless binds[binds.size - 2]!.consumeMData.isAppOf `Leanux.Proofs.Logged.emitCheckpoint do
    Lean.throwError "not a checkpoint emission"

elab "checkpoint_head_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let rec reduceHead : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _ => reduceHead n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE _ _ value body _ => reduceHead n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal e next then e else reduceHead n next
        | _ => e
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesT do Lean.throwError "not an erasure contract"
  let .app (.app f observed) original := target | Lean.throwError "missing actions"
  let observed' := reduceHead 64 observed
  let original' := reduceHead 64 original
  if Lean.Expr.equal observed observed' && Lean.Expr.equal original original' then
    Lean.throwError "heads unchanged"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (.app (.app f observed') original')]

-- Equal outcomes of one discriminator must use the same branch payload.
elab "checkpoint_alias" : tactic => Lean.Elab.Tactic.withMainContext do
  let rec collapse (fuel : Nat) (goal : Lean.MVarId) (eq : Lean.FVarId) :
      Lean.MetaM (Option Lean.MVarId) := goal.withContext do
    match fuel with
    | 0 => Lean.throwError "outcome equality nesting exceeded"
    | fuel + 1 =>
      let some (_, lhs, rhs) ← Lean.Meta.matchEq? (← eq.getType)
        | Lean.throwError "expected an outcome equality"
      if lhs.isFVar || rhs.isFVar then
        return some (← Lean.Meta.subst goal eq)
      match ← Lean.Meta.injection goal eq with
      | .solved => return none
      | .subgoal next eqs _ =>
        let mut current := some next
        for field in eqs do
          if let some g := current then
            current ← collapse fuel g field
        return current
  let goal ← Lean.Elab.Tactic.getMainGoal
  let decls := (← Lean.getLCtx).getFVarIds
  for i in [:decls.size] do
    let di ← decls[i]!.getDecl
    if let some (_, lhs, rhs) ← Lean.Meta.matchEq? di.type then
      for j in [i+1:decls.size] do
        let dj ← decls[j]!.getDecl
        if let some (_, lhs', rhs') ← Lean.Meta.matchEq? dj.type then
          if Lean.Expr.eqv lhs lhs' && !(Lean.Expr.eqv rhs rhs') then
            let proof ← Lean.Meta.mkEqTrans (← Lean.Meta.mkEqSymm di.toExpr) dj.toExpr
            let next ← goal.assert `checkpoint_outcome (← Lean.Meta.inferType proof) proof
            let (eq, next) ← next.intro1
            match ← collapse 4 next eq with
            | none => Lean.Elab.Tactic.replaceMainGoal []
            | some next => Lean.Elab.Tactic.replaceMainGoal [next]
            return
  Lean.throwError "no repeated discriminator equation"

elab "checkpoint_head_match" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ErasesT do Lean.throwError "not an erasure contract"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!.consumeMData
  -- Reuse the already selected discriminator before splitting its other
  -- occurrence. This keeps the same result variables on both sides.
  for action in [observed, args.back!.consumeMData] do
    if let some matcher ← Lean.Meta.matchMatcherApp? action then
      for discr in matcher.discrs do
        for decl in ← Lean.getLCtx do
          if let some (_, lhs, _) ← Lean.Meta.matchEq? decl.type then
            if Lean.Expr.eqv lhs discr then
              let rewritten ← goal.rewrite target decl.toExpr
              let next ← goal.replaceTargetEq rewritten.eNew rewritten.eqProof
              Lean.Elab.Tactic.replaceMainGoal (next :: rewritten.mvarIds)
              return
  if (← Lean.Meta.matchMatcherApp? observed).isSome then
    Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal observed)
  else
    let original := args.back!.consumeMData
    let some _ ← Lean.Meta.matchMatcherApp? original | Lean.throwError "not a head matcher"
    Lean.Elab.Tactic.replaceMainGoal (← Lean.Meta.Split.splitMatch goal original)

/-- Append exactly one projection of the committed World and operation index. -/
def emitCheckpoint (project : Nat → World → α) (index : Nat) (w : World) :
    StateT (List α) (Except (Nat × Stop)) Unit :=
  modify (· ++ [project index w])

/-- Exact observation content and multiplicity at the checkpoint boundary. -/
theorem emitCheckpoint_run (project : Nat → World → α) (index : Nat)
    (w : World) (observed : List α) :
    (emitCheckpoint project index w).run observed =
      .ok ((), observed ++ [project index w]) := rfl

theorem emitCheckpoint_erases (project : Nat → World → α) (index : Nat) (w : World) :
    ErasesT (emitCheckpoint project index w) (pure ()) := by
  intro observed
  rfl

theorem emitCheckpoint_then_erases (project : Nat → World → α)
    (index : Nat) (w : World)
    {g : StateT (List α) (Except (Nat × Stop)) β} {o : Except (Nat × Stop) β}
    (he : ErasesT g o) :
    ErasesT (do emitCheckpoint project index w; g) o := by
  simpa only [pure_bind] using
    erasesT_bind (emitCheckpoint_erases project index w) (fun _ => he)

/-- The original runner with one projected observation at each operation's
successful commit boundary. Final trace guards still control acceptance. -/
def executeTraceCheckpoints (project : Nat → World → α) (trace : Trace) (placeholders : Bool := false) : StateT (List α) (Except (Nat × Stop)) Json := do
  let ambient : Ambient := { env := harnessEnv, timing := Env.timing,
                             allocArmed := trace.allocArmed,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  let mut world : World := { ambient,
                             fs := initialFS trace.net trace.foreign trace.stepped trace.seccompChild,
                             tasks := initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild,
                             wg := { initialWG trace.net trace.bare with
                                     portBound := Env.portBound,
                                     fixtureNetDevices := Env.fixtureNetDevices,
                                     dstCacheRecords := trace.dstCacheRecords,
                                     routing := { foreignCreator := trace.foreign } },
                             fixture := { netnsCHolders := if trace.foreign then [9, 8, 5, 4] else [],
                                          routes := trace.routes,
                                          napiBeforePut := trace.napiBeforePut } }
  -- the seccomp prefill fixture (design 5): the chain the guest installed before the window
  if trace.seccompPrefill > 0 then
    match Env.seccompPrefill trace.seccompPrefill world.seccomp world.tasks with
    | .ok (seccomp, tasks) => world := { world with seccomp, tasks }
    | .error e => throw (0, .invariant e)
  -- lane C: the fixture namespaces' IPv4 tables at boot (`lo` up in each),
  -- built by the C's own sequence outside every window (the design note,
  -- 9.3); its steps are discarded with the first operation's reset
  if trace.net then
    let boot : M Unit := do
      Net.Fib.bootTables
      if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables
    match boot.run world with
    | .ok (_, w) => world := { w with ambient := { w.ambient with steps := #[], envCalls := [] } }
    | .error e => throw (0, e)
  let mut results : Array Int := #[]
  let mut ends : Array (Option (Nat × Nat)) := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList   -- B3, E2's lookahead
    world := { world with ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) },
                          fixture := { world.fixture with hiddenAhead := ahead }, wg := { world.wg with netRxRaised := false } }
    let (ret, w) ← (syscall (toSyscall results ends index op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
    if let i :: _ := w.ambient.pendingWork then
      let name := ((Worker.all.find? (·.index == i)).map (·.symbol)).getD s!"unit {i}"
      if w.ambient.hidden.isSome then
        throw (index, .hidden s!"{name} is pending at the end of the operation (the dispatch its requeue causes has no section in the records)")
      else
        throw (index, .invariant s!"{name} is pending at the end of the operation (the fixed order ran no dispatch for it)")
    if w.wg.netRxRaised then
      throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
    emitCheckpoint project index w
    world := w
    results := results.push ret
    ends := ends.push (if ret == 0 then w.fs.userFds else none)
    -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8);
    -- an epoll_wait's `ret` events of 12 bytes (epoll, the read channel)
    let bytes := match op, w.fs.userOut with
      | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
      | .epollWait .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min (ret.toNat * 12) READ_HEAD)) else ""
      | _, _ => ""
    -- pipe2: the pair copied to the caller, or null on failure; a read's
    -- digest; a write's sigpipe (P design section 6)
    let fds : List (String × Json) := match op with
      | .pipe2 _ => [("fds", match w.fs.userFds with
          | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
          | none => .null)]
      | .read .. => [("digest", readDigest w.fs.userOut ret)]
      | .epollWait .. => [("digest", readDigest w.fs.userOut (ret * 12))]
      | .write .. => [("sigpipe", writeSigpipe w.tasks)]
      | _ => []
    let device := w.ambient.extraOut
    observations := observations.push (Json.mkObj ([
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)] ++ fds ++ device))
    for s in w.ambient.steps do
      -- W7 stream H: the NET_RX section ordinal of a step inside one
      let fields := [("index", toJson index), ("label", toJson s.label)]
        ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
      branches := branches.push (Json.mkObj (match s.operands, s.excluded with
        | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
        | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
        | none, none => fields))
    for symbol in w.ambient.fired do
      fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
  -- a placement the check chose must have been met
  if world.fixture.napiBeforePut.any id then
    throw (results.size - 1, .invariant "napi_irq_before_put names more NAPI polls than the trace has")
  -- the domain filter: a schedule entry for an allocation site that the
  -- mirror never met would be left over in the kernel
  if world.ambient.hiddenPlaceholders && world.ambient.steerValues.any (fun e => world.ambient.allocSteered.contains e.1) then
    throw (trace.ops.size - 1, .outsideDomain "steer" "allocation schedule entries beyond the encounters")
  -- D3: the timer sections the environment ran (`fired:<symbol>`
  -- expectations), present only when one ran
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else []))

private abbrev CheckpointLoopState :=
  World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json

/-- The exact iterator callback, factored only as a proof obligation. Its
observer and original retain the syscall, ambient drain, guards and output
bookkeeping in their original order. -/
private theorem checkpointOperation_erases (project : Nat → World → α)
    (trace : Trace) (op : Operation) (state : CheckpointLoopState) :
    ErasesT
  (show StateT (List α) (Except (Nat × Stop)) (ForInStep CheckpointLoopState) from do
    let mut world := state.1
    let mut results := state.2.1
    let mut ends := state.2.2.1
    let mut observations := state.2.2.2.1
    let mut branches := state.2.2.2.2.1
    let mut fired := state.2.2.2.2.2
    let index := results.size
    let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList   -- B3, E2's lookahead
    world := { world with ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) },
                          fixture := { world.fixture with hiddenAhead := ahead }, wg := { world.wg with netRxRaised := false } }
    let (ret, w) ← (syscall (toSyscall results ends index op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
    if let i :: _ := w.ambient.pendingWork then
      let name := ((Worker.all.find? (·.index == i)).map (·.symbol)).getD s!"unit {i}"
      if w.ambient.hidden.isSome then
        throw (index, .hidden s!"{name} is pending at the end of the operation (the dispatch its requeue causes has no section in the records)")
      else
        throw (index, .invariant s!"{name} is pending at the end of the operation (the fixed order ran no dispatch for it)")
    if w.wg.netRxRaised then
      throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
    emitCheckpoint project index w
    world := w
    results := results.push ret
    ends := ends.push (if ret == 0 then w.fs.userFds else none)
    -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8);
    -- an epoll_wait's `ret` events of 12 bytes (epoll, the read channel)
    let bytes := match op, w.fs.userOut with
      | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
      | .epollWait .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min (ret.toNat * 12) READ_HEAD)) else ""
      | _, _ => ""
    -- pipe2: the pair copied to the caller, or null on failure; a read's
    -- digest; a write's sigpipe (P design section 6)
    let fds : List (String × Json) := match op with
      | .pipe2 _ => [("fds", match w.fs.userFds with
          | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
          | none => .null)]
      | .read .. => [("digest", readDigest w.fs.userOut ret)]
      | .epollWait .. => [("digest", readDigest w.fs.userOut (ret * 12))]
      | .write .. => [("sigpipe", writeSigpipe w.tasks)]
      | _ => []
    let device := w.ambient.extraOut
    observations := observations.push (Json.mkObj ([
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)] ++ fds ++ device))
    for s in w.ambient.steps do
      -- W7 stream H: the NET_RX section ordinal of a step inside one
      let fields := [("index", toJson index), ("label", toJson s.label)]
        ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
      branches := branches.push (Json.mkObj (match s.operands, s.excluded with
        | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
        | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
        | none, none => fields))
    for symbol in w.ambient.fired do
      fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
    pure (ForInStep.yield (world, results, ends, observations, branches, fired)))
  (show Except (Nat × Stop) (ForInStep CheckpointLoopState) from do
    let mut world := state.1
    let mut results := state.2.1
    let mut ends := state.2.2.1
    let mut observations := state.2.2.2.1
    let mut branches := state.2.2.2.2.1
    let mut fired := state.2.2.2.2.2
    let index := results.size
    let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList   -- B3, E2's lookahead
    world := { world with ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) },
                          fixture := { world.fixture with hiddenAhead := ahead }, wg := { world.wg with netRxRaised := false } }
    let (ret, w) ← (syscall (toSyscall results ends index op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
    if let i :: _ := w.ambient.pendingWork then
      let name := ((Worker.all.find? (·.index == i)).map (·.symbol)).getD s!"unit {i}"
      if w.ambient.hidden.isSome then
        throw (index, .hidden s!"{name} is pending at the end of the operation (the dispatch its requeue causes has no section in the records)")
      else
        throw (index, .invariant s!"{name} is pending at the end of the operation (the fixed order ran no dispatch for it)")
    if w.wg.netRxRaised then
      throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
    world := w
    results := results.push ret
    ends := ends.push (if ret == 0 then w.fs.userFds else none)
    -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8);
    -- an epoll_wait's `ret` events of 12 bytes (epoll, the read channel)
    let bytes := match op, w.fs.userOut with
      | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
      | .epollWait .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min (ret.toNat * 12) READ_HEAD)) else ""
      | _, _ => ""
    -- pipe2: the pair copied to the caller, or null on failure; a read's
    -- digest; a write's sigpipe (P design section 6)
    let fds : List (String × Json) := match op with
      | .pipe2 _ => [("fds", match w.fs.userFds with
          | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
          | none => .null)]
      | .read .. => [("digest", readDigest w.fs.userOut ret)]
      | .epollWait .. => [("digest", readDigest w.fs.userOut (ret * 12))]
      | .write .. => [("sigpipe", writeSigpipe w.tasks)]
      | _ => []
    let device := w.ambient.extraOut
    observations := observations.push (Json.mkObj ([
      ("index", toJson index), ("ret", toJson ret),
      ("errno", if ret < 0 then toJson (-ret) else .null),
      ("bytes", toJson bytes)] ++ fds ++ device))
    for s in w.ambient.steps do
      -- W7 stream H: the NET_RX section ordinal of a step inside one
      let fields := [("index", toJson index), ("label", toJson s.label)]
        ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
      branches := branches.push (Json.mkObj (match s.operands, s.excluded with
        | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
        | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
        | none, none => fields))
    for symbol in w.ambient.fired do
      fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
    pure (ForInStep.yield (world, results, ends, observations, branches, fired))) := by
  repeat' first
    | checkpoint_alias
    | contradiction
    | (checkpoint_emit_head; with_reducible apply emitCheckpoint_then_erases)
    | (checkpoint_head Pure.pure; with_reducible exact erasesT_pure _)
    | (checkpoint_head Pure.pure; simp_all only [ErasesT, StateT.run_pure, map_pure, reduceCtorEq])
    | (checkpoint_head liftM; with_reducible exact erasesT_liftM _)
    | (checkpoint_head StateT.lift; with_reducible exact erasesT_lift _)
    | (checkpoint_head MonadExcept.throw; with_reducible exact erasesT_throw _)
    | (checkpoint_head ite; with_reducible apply erasesT_ite)
    | (checkpoint_head Bind.bind; with_reducible apply erasesT_bind)
    | (checkpoint_head Functor.map; with_reducible apply erasesT_map)
    | (checkpoint_head ForIn.forIn; with_reducible apply erasesT_array)
    | (checkpoint_head ForIn.forIn; with_reducible apply erasesT_forIn)
    | checkpoint_intro_forall
    | checkpoint_head_reduce
    | (checkpoint_head_match <;> try simp_all only
        [])
    | rfl

/-- Forgetting only checkpoint observations recovers the full original
runner result, including JSON and every exact indexed failure. -/
theorem executeTraceCheckpoints_erases (project : Nat → World → α)
    (trace : Trace) (placeholders : Bool) :
    ErasesT (executeTraceCheckpoints project trace placeholders)
      (Runner.executeTrace trace placeholders) := by
  unfold executeTraceCheckpoints Runner.executeTrace
  repeat' first
    | checkpoint_alias
    | contradiction
    | (checkpoint_emit_head; with_reducible apply emitCheckpoint_then_erases)
    | (checkpoint_head Pure.pure; with_reducible exact erasesT_pure _)
    | (checkpoint_head liftM; with_reducible exact erasesT_liftM _)
    | (checkpoint_head StateT.lift; with_reducible exact erasesT_lift _)
    | (checkpoint_head MonadExcept.throw; with_reducible exact erasesT_throw _)
    | (checkpoint_head ite; with_reducible apply erasesT_ite)
    | (checkpoint_head Bind.bind; with_reducible apply erasesT_bind)
    | (checkpoint_head Functor.map; with_reducible apply erasesT_map)
    | checkpoint_intro_forall
    | checkpoint_head_reduce
    | checkpoint_head_match
    | rfl
  all_goals
    exact erasesT_array _ _ _ _ (checkpointOperation_erases project trace)

/-- Original accepted traces and successful checkpoint-observer executions
have exactly the same JSON; the observation content is fixed at the emit site. -/
theorem executeTraceCheckpoints_success_iff (project : Nat → World → α)
    (trace : Trace) (placeholders : Bool) (json : Json) (observed : List α) :
    Runner.executeTrace trace placeholders = .ok json ↔
      ∃ observed', (executeTraceCheckpoints project trace placeholders).run observed =
        .ok (json, observed') :=
  erasesT_success_iff (executeTraceCheckpoints_erases project trace placeholders) json observed

end Leanux.Proofs.Logged
