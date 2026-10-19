import Leanux.Proofs.WG.Configuration.RunnerCompletion
import Leanux.Proofs.WG.Queues.RxRunnerHistory
import Leanux.Proofs.Logged.ProjectsOuter

/-! One literal typed runner body shared by the routing and RX observers.
Only the syscall observer and successful result projection are parameters. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Configuration

def runnerTailWith {E α : Type} (call : Syscall → PrefixM E Int)
    (finish : Json → World → α) (trace : Trace)
    (initialWorld : World) : PrefixOuter E α := do
  let mut world := initialWorld
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
    let (ret, w) ← runAtPrefix index world (call (toSyscall results ends index op))
    let (_, w) ← runAtPrefix index w (liftPrefix (skipAmbient : Leanux.M Unit))
    if let some (r :: _) := w.ambient.hidden then
      throw (index, .hidden s!"a record of site {r.site} was not consumed")
    if let a :: _ := w.ambient.suspended then
      throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
    if w.ambient.hidden.isSome then
      if let i :: _ := w.ambient.pendingWork then
        let name := ((Worker.all.find? (·.index == i)).map (·.symbol)).getD s!"unit {i}"
        throw (index, .hidden s!"{name} is pending at the end of the operation (the dispatch its requeue causes has no section in the records)")
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
  return finish (Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else []))) world

def executeTraceWith {E α : Type} (call : Syscall → PrefixM E Int)
    (finish : Json → World → α) (trace : Trace) (placeholders : Bool := false) : PrefixOuter E α := do
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
    let boot : Leanux.M Unit := do
      Net.Fib.bootTables
      if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables
    match boot.run world with
    | .ok (_, w) => world := { w with ambient := { w.ambient with steps := #[], envCalls := [] } }
    | .error e => throw (0, e)
  runnerTailWith call finish trace world

theorem runnerTail_routing_factor (trace : Trace) (w : World) :
    runnerTailObserved trace w =
      runnerTailWith syscallObserved (fun j v => (j,v)) trace w := rfl

theorem runnerTail_rx_factor {E : Type} (call : Syscall → PrefixM E Int)
    (trace : Trace) (w : World) :
    RxHistory.runnerTail call trace w = runnerTailWith call (fun j _ => j) trace w := rfl

theorem executeTrace_routing_factor (trace : Trace) (placeholders : Bool) :
    executeTraceObserved trace placeholders =
      executeTraceWith syscallObserved (fun j v => (j,v)) trace placeholders := rfl

theorem executeTrace_rx_factor {E : Type} (call : Syscall → PrefixM E Int)
    (trace : Trace) (placeholders : Bool) :
    RxHistory.executeTraceWith call trace placeholders =
      executeTraceWith call (fun j _ => j) trace placeholders := rfl

end Leanux.Proofs.WG.Queues.RoutingJoint
