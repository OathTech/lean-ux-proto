import Leanux.Proofs.WG.Configuration.SyscallCompletion
import Leanux.Proofs.Logged.PrefixOuter

/-! Literal initialized source Runner returning its actual final accumulator
World beside JSON. The completion observer erases to this entire result; the
source result projects to the original public JSON Runner. -/
namespace Leanux.Proofs.WG.Configuration
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.AllowedIps Std.Do
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

def runnerTailObserved (trace : Trace)
    (initialWorld : World) : PrefixOuter RoutingCompletion (Json × World) := do
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
    let (ret, w) ← runAtPrefix index world (syscallObserved (toSyscall results ends index op))
    let (_, w) ← runAtPrefix index w (liftPrefix (skipAmbient : Leanux.M Unit))
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
  return (Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else [])), world)

def sourceRunnerTail (trace : Trace)
    (initialWorld : World) : Except (Nat × Stop) (Json × World) := do
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
    let (ret, w) ← (syscall (toSyscall results ends index op)).run world
      |>.mapError fun e => (index, e)
    let (_, w) ← (skipAmbient : Leanux.M Unit).run w |>.mapError fun e => (index, e)
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
  return (Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else [])), world)

def executeTraceObserved (trace : Trace) (placeholders : Bool := false) : PrefixOuter RoutingCompletion (Json × World) := do
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
  runnerTailObserved trace world

def sourceRunner (trace : Trace) (placeholders : Bool := false) : Except (Nat × Stop) (Json × World) := do
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
  sourceRunnerTail trace world

macro "runner_erasure_step" : tactic => `(tactic|
  first
    | (maintenance_head syscallObserved; exact syscallObserved_erases _)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head runAtPrefix; apply runAtPrefix_erases)
    | (maintenance_head Pure.pure; exact erasesOuter_pure _)
    | (maintenance_head throw; exact erasesOuter_throw _)
    | (maintenance_head ite; apply erasesOuter_ite)
    | (maintenance_head Bind.bind; apply erasesOuter_bind)
    | (maintenance_head Functor.map; apply erasesOuter_map)
    | (maintenance_head ForIn.forIn; first | apply erasesOuter_array | apply erasesOuter_forIn)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split)

macro "runner_erasure" : tactic => `(tactic| repeat' runner_erasure_step)

theorem runnerTailObserved_erases (trace : Trace) (w : World) :
    ErasesOuter (runnerTailObserved trace w) (sourceRunnerTail trace w) := by
  unfold runnerTailObserved sourceRunnerTail
  runner_erasure

theorem executeTraceObserved_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (executeTraceObserved trace placeholders)
      (sourceRunner trace placeholders) := by
  unfold executeTraceObserved sourceRunner
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | (maintenance_head runnerTailObserved; exact runnerTailObserved_erases _ _)
    | runner_erasure_step

private theorem except_project_ite {ε α β : Type} (p : Prop) [Decidable p]
    (a b : Except ε α) (c d : Except ε β) (f : α → β)
    (ha : p → a.map f = c) (hb : ¬p → b.map f = d) :
    (if p then a else b).map f = (if p then c else d) := by
  by_cases h : p <;> simp_all

private theorem except_project_bind {ε α β γ : Type} (a : Except ε α)
    (f : α → Except ε β) (g : α → Except ε γ) (p : β → γ)
    (hf : ∀ x, (f x).map p = g x) :
    (a >>= f).map p = a >>= g := by
  cases a <;> simp_all [bind, Except.bind, Except.map]

/-- The extra World is the source accumulator, with no alteration of the
original JSON result or indexed Stop. -/
theorem sourceRunner_json (trace : Trace) (placeholders : Bool) :
    (sourceRunner trace placeholders).map Prod.fst =
      Runner.executeTrace trace placeholders := by
  unfold sourceRunner sourceRunnerTail Runner.executeTrace
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild)
  all_goals repeat' first
    | rfl
    | apply except_project_ite
    | apply except_project_bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | (split <;> try simp_all only)

end Leanux.Proofs.WG.Configuration
