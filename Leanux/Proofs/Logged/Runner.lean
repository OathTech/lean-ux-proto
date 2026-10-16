import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.Logged.Syscalls
import Leanux.Runner

/-! The complete proof-side acceptance observer for the pinned runner.
Erasing history preserves JSON and exact indexed errors for every input. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.Logged
open Lean Leanux Leanux.Runner

def executeTraceLogged (trace : Trace) (placeholders : Bool := false) : StateT History (Except (Nat × Stop)) Json := do
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
    let (ret, w) ← runAtLogged index world (syscallLogged (toSyscall results ends index op))
    let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
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

private abbrev LoggedLoopState :=
  World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json

/-- The exact iterator callback, factored only as a proof obligation. Its
observer runs syscallLogged at the original syscall site; the ambient drain,
guards and output bookkeeping retain their original order. -/
private theorem loggedOperation_erases (trace : Trace) (op : Operation) (state : LoggedLoopState) :
    ErasesT
  (show StateT History (Except (Nat × Stop)) (ForInStep LoggedLoopState) from do
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
    let (ret, w) ← runAtLogged index world (syscallLogged (toSyscall results ends index op))
    let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
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
    pure (ForInStep.yield (world, results, ends, observations, branches, fired)))
  (show Except (Nat × Stop) (ForInStep LoggedLoopState) from do
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
    | (checkpoint_head Leanux.Proofs.Logged.runAtLogged;
       exact runAtLogged_erases _ _ _ _ (syscallLogged_erases _))
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
        [reduceCtorEq, Except.ok.injEq, Except.error.injEq, Option.some.injEq, Prod.mk.injEq])
    | rfl

/-- Exact erasure to the executable runner, including JSON and each indexed
failure. The history invariant remains a separate proof obligation. -/
theorem executeTraceLogged_erases (trace : Trace) (placeholders : Bool) :
    ErasesT (executeTraceLogged trace placeholders)
      (Runner.executeTrace trace placeholders) := by
  unfold executeTraceLogged Runner.executeTrace
  repeat' first
    | checkpoint_alias
    | contradiction
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
    exact erasesT_array _ _ _ _ (loggedOperation_erases trace)

/-- Accepted runner inputs have an observer history and unchanged JSON.
The history invariant is a separate proof obligation. -/
theorem executeTraceLogged_success_iff (trace : Trace) (placeholders : Bool)
    (json : Json) (history : History) :
    Runner.executeTrace trace placeholders = .ok json ↔
      ∃ history', (executeTraceLogged trace placeholders).run history = .ok (json, history') :=
  erasesT_success_iff (executeTraceLogged_erases trace placeholders) json history

end Leanux.Proofs.Logged
