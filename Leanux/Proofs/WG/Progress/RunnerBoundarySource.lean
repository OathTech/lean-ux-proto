import Leanux.Proofs.WG.Progress.RunnerBoundaryModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Lean Leanux Leanux.Runner Campaign2

/-- The original loop accumulator. Concrete execution state stays in this source connection. -/
abbrev RunnerAccumulator := World × Array Int × Array (Option (Nat × Nat)) ×
  Array Lean.Json × Array Lean.Json × Array Lean.Json

def runnerInitial (trace : Trace) (placeholders : Bool) : Except (Nat × Stop) World := do
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
  return world

def runnerStep (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    Except (Nat × Stop) (ForInStep RunnerAccumulator) := do
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
  return .yield (world, results, ends, observations, branches, fired)

/-- The actual syscall and ambient strip, followed by the four original
operation-completion checks, including supplied-mode pending work. A negative
syscall return still passes when these checks succeed. -/
def runnerOperation (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    Except (Nat × Stop) (Int × World) := do
  let world := state.1
  let results := state.2.1
  let ends := state.2.2.1
  let index := results.size
  let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList   -- B3, E2's lookahead
  let world := { world with
    ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) }
    fixture := { world.fixture with hiddenAhead := ahead }
    wg := { world.wg with netRxRaised := false } }
  let (ret, w) ← (syscall (toSyscall results ends index op)).run world
    |>.mapError fun e => (index, e)
  let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
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
  return (ret, w)

def runnerPresent (op : Operation) (state : RunnerAccumulator) (ret : Int) (w : World) :
    Except (Nat × Stop) (ForInStep RunnerAccumulator) := do
  let mut world := state.1
  let mut results := state.2.1
  let mut ends := state.2.2.1
  let mut observations := state.2.2.2.1
  let mut branches := state.2.2.2.2.1
  let mut fired := state.2.2.2.2.2
  let index := state.2.1.size
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
  return .yield (world, results, ends, observations, branches, fired)

theorem runnerStep_operation_source (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    runnerStep trace op state = (do
      let (ret, w) ← runnerOperation trace op state
      runnerPresent op state ret w) := by
  unfold runnerStep runnerOperation runnerPresent
  simp only [bind_assoc]
  congr 1
  funext pair
  obtain ⟨ret, middle⟩ := pair
  congr 1
  funext pair
  obtain ⟨u, after⟩ := pair
  cases u
  cases h : after.ambient.hidden with
  | none => cases hs : after.ambient.suspended <;> cases hb : after.wg.netRxRaised <;> rfl
  | some records =>
    cases records with
    | nil => cases hs : after.ambient.suspended <;>
      cases hp : after.ambient.pendingWork <;> cases hb : after.wg.netRxRaised <;> rfl
    | cons record rest => rfl

def runnerFinish (trace : Trace) (state : RunnerAccumulator) : Except (Nat × Stop) Lean.Json := do
  let world := state.1
  let results := state.2.1
  let observations := state.2.2.2.1
  let branches := state.2.2.2.2.1
  let fired := state.2.2.2.2.2
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

def runnerBoundarySource (trace : Trace) (placeholders : Bool) :
    Except (Nat × Stop) Lean.Json := do
  let initial ← runnerInitial trace placeholders
  let final ← forIn trace.ops ((initial, #[], #[], #[], #[], #[]) : RunnerAccumulator)
    (runnerStep trace)
  runnerFinish trace final

theorem executeTrace_boundary_source (trace : Trace) (placeholders : Bool) :
    runnerBoundarySource trace placeholders = executeTrace trace placeholders := by
  let ambient : Ambient := { env := harnessEnv, timing := Env.timing,
                             allocArmed := trace.allocArmed,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  let seed : World := { ambient,
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
  let boot : M Unit := do
    Net.Fib.bootTables
    if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables
  let finish : World → Except (Nat × Stop) Json := fun world => do
    let final ← forIn trace.ops ((world, #[], #[], #[], #[], #[]) : RunnerAccumulator)
      (runnerStep trace)
    runnerFinish trace final
  change ((do
      let mut world := seed
      if trace.seccompPrefill > 0 then
        match Env.seccompPrefill trace.seccompPrefill world.seccomp world.tasks with
        | .ok (seccomp, tasks) => world := {world with seccomp, tasks}
        | .error e => throw (0, .invariant e)
      if trace.net then
        match boot.run world with
        | .ok (_, w) => world := {w with ambient := {w.ambient with steps := #[], envCalls := []}}
        | .error e => throw (0, e)
      pure world) >>= finish) = (do
      let mut world := seed
      if trace.seccompPrefill > 0 then
        match Env.seccompPrefill trace.seccompPrefill world.seccomp world.tasks with
        | .ok (seccomp, tasks) => world := {world with seccomp, tasks}
        | .error e => throw (0, .invariant e)
      if trace.net then
        match boot.run world with
        | .ok (_, w) => world := {w with ambient := {w.ambient with steps := #[], envCalls := []}}
        | .error e => throw (0, e)
      finish world)
  have tail (world : World) : ((do
      let mut current := world
      if trace.net then
        match boot.run current with
        | .ok (_, w) => current := {w with ambient := {w.ambient with steps := #[], envCalls := []}}
        | .error e => throw (0, e)
      pure current) >>= finish) = (do
      let mut current := world
      if trace.net then
        match boot.run current with
        | .ok (_, w) => current := {w with ambient := {w.ambient with steps := #[], envCalls := []}}
        | .error e => throw (0, e)
      finish current) := by
    cases net : trace.net
    · simp only [Bool.false_eq_true, ite_false, pure_bind]
    · simp only [ite_true]
      cases executed : boot.run world <;> rfl
  by_cases prefill : trace.seccompPrefill > 0
  · simp only [prefill, ite_true]
    cases prepared : Env.seccompPrefill trace.seccompPrefill seed.seccomp seed.tasks with
    | error error => rfl
    | ok pair =>
      obtain ⟨seccomp, tasks⟩ := pair
      simpa only [prepared, pure_bind] using tail {seed with seccomp, tasks}
  · simpa only [prefill, ite_false] using tail seed

end Leanux.Proofs.WG.Progress
