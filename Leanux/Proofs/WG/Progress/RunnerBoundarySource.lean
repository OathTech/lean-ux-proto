import Leanux.Proofs.WG.Progress.RunnerBoundaryModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Lean Leanux Leanux.Runner Campaign2

/-- The original loop accumulator. Concrete execution state stays in this source connection. -/
abbrev RunnerAccumulator := World × Array Int × Array (Option (Nat × Nat)) ×
  Array Lean.Json × Array Lean.Json × Array Lean.Json

def runnerInitial (trace : Trace) (placeholders floodExact : Bool) : Except (Nat × Stop) World := do
  let mut world : World := { k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild, env := harnessEnv,
                             timing := Env.timing, portBound := Env.portBound,
                             fixtureNetDevices := Env.fixtureNetDevices,
                             foreignCreator := trace.foreign,
                             netnsCHolders := if trace.foreign then [9, 8, 5, 4] else [],
                             allocArmed := trace.allocArmed, routes := trace.routes,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             floodExact,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords, dstCacheRecords := trace.dstCacheRecords,
                             napiBeforePut := trace.napiBeforePut,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  -- the seccomp prefill fixture (design 5): the chain the guest installed before the window
  if trace.seccompPrefill > 0 then
    match Env.seccompPrefill trace.seccompPrefill world.k with
    | .ok k => world := { world with k }
    | .error e => throw (0, .invariant e)
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
  world := { world with hidden := trace.hidden.map (·[index]!), netRxRaised := false }
  let (ret, w) ← (syscall (toSyscall results ends index op)).run world
    |>.mapError fun e => (index, e)
  let (_, w) ← skipAmbient.run w |>.mapError fun e => (index, e)
  if let some (r :: _) := w.hidden then
    throw (index, .hidden s!"a record of site {r.site} was not consumed")
  if let a :: _ := w.suspended then
    throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
  if w.netRxRaised then
    throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
  world := w
  results := results.push ret
  ends := ends.push (if ret == 0 then w.userFds else none)
  -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8);
  -- an epoll_wait's `ret` events of 12 bytes (epoll, the read channel)
  let bytes := match op, w.userOut with
    | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
    | .epollWait .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min (ret.toNat * 12) READ_HEAD)) else ""
    | _, _ => ""
  -- pipe2: the pair copied to the caller, or null on failure; a read's
  -- digest; a write's sigpipe (P design section 6)
  let fds : List (String × Json) := match op with
    | .pipe2 _ => [("fds", match w.userFds with
        | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
        | none => .null)]
    | .read .. => [("digest", readDigest w.userOut ret)]
    | .epollWait .. => [("digest", readDigest w.userOut (ret * 12))]
    | .write .. => [("sigpipe", writeSigpipe w.k)]
    | _ => []
  let device := w.extraOut
  observations := observations.push (Json.mkObj ([
    ("index", toJson index), ("ret", toJson ret),
    ("errno", if ret < 0 then toJson (-ret) else .null),
    ("bytes", toJson bytes)] ++ fds ++ device))
  for s in w.steps do
    -- W7 stream H: the NET_RX section ordinal of a step inside one
    let fields := [("index", toJson index), ("label", toJson s.label)]
      ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
    branches := branches.push (Json.mkObj (match s.operands, s.excluded with
      | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
      | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
      | none, none => fields))
  for symbol in w.fired do
    fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
  return .yield (world, results, ends, observations, branches, fired)

/-- The actual syscall and ambient strip, followed by all three original
operation-completion checks. A negative syscall return still passes here. -/
def runnerOperation (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    Except (Nat × Stop) (Int × World) := do
  let index := state.2.1.size
  let world := { state.1 with hidden := trace.hidden.map (·[index]!), netRxRaised := false }
  let (ret, w) ← (syscall (toSyscall state.2.1 state.2.2.1 index op)).run world
    |>.mapError fun e => (index, e)
  let (_, w) ← skipAmbient.run w |>.mapError fun e => (index, e)
  if let some (r :: _) := w.hidden then
    throw (index, .hidden s!"a record of site {r.site} was not consumed")
  if let a :: _ := w.suspended then
    throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
  if w.netRxRaised then
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
  ends := ends.push (if ret == 0 then w.userFds else none)
  -- a read's first READ_HEAD bytes in the clear (eventfd reads: all 8);
  -- an epoll_wait's `ret` events of 12 bytes (epoll, the read channel)
  let bytes := match op, w.userOut with
    | .read .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min ret.toNat READ_HEAD)) else ""
    | .epollWait .., some v => if ret > 0 then hexBytesOf (v.extract 0 (min (ret.toNat * 12) READ_HEAD)) else ""
    | _, _ => ""
  -- pipe2: the pair copied to the caller, or null on failure; a read's
  -- digest; a write's sigpipe (P design section 6)
  let fds : List (String × Json) := match op with
    | .pipe2 _ => [("fds", match w.userFds with
        | some (r, wr) => if ret == 0 then toJson [r, wr] else .null
        | none => .null)]
    | .read .. => [("digest", readDigest w.userOut ret)]
    | .epollWait .. => [("digest", readDigest w.userOut (ret * 12))]
    | .write .. => [("sigpipe", writeSigpipe w.k)]
    | _ => []
  let device := w.extraOut
  observations := observations.push (Json.mkObj ([
    ("index", toJson index), ("ret", toJson ret),
    ("errno", if ret < 0 then toJson (-ret) else .null),
    ("bytes", toJson bytes)] ++ fds ++ device))
  for s in w.steps do
    -- W7 stream H: the NET_RX section ordinal of a step inside one
    let fields := [("index", toJson index), ("label", toJson s.label)]
      ++ (if s.netRx > 0 then [("section", toJson s.netRx)] else [])
    branches := branches.push (Json.mkObj (match s.operands, s.excluded with
      | some (a, b), _ => fields ++ [("operands", toJson [a, b])]
      | none, some x => fields ++ [("operands_excluded", toJson x.operand)]
      | none, none => fields))
  for symbol in w.fired do
    fired := fired.push (Json.mkObj [("index", toJson index), ("symbol", toJson symbol)])
  return .yield (world, results, ends, observations, branches, fired)

theorem runnerStep_operation_source (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    runnerStep trace op state = (do
      let (ret, w) ← runnerOperation trace op state
      runnerPresent op state ret w) := by
  unfold runnerStep runnerOperation runnerPresent
  simp only [bind_assoc, pure_bind]
  congr 1
  funext pair
  obtain ⟨ret, middle⟩ := pair
  congr 1
  funext pair
  obtain ⟨u, after⟩ := pair
  cases u
  cases h : after.hidden with
  | none => cases hs : after.suspended <;> cases hb : after.netRxRaised <;> rfl
  | some records =>
    cases records with
    | nil => cases hs : after.suspended <;> cases hb : after.netRxRaised <;> rfl
    | cons record rest => rfl


def runnerFinish (trace : Trace) (state : RunnerAccumulator) : Except (Nat × Stop) Lean.Json := do
  let world := state.1
  let results := state.2.1
  let ends := state.2.2.1
  let observations := state.2.2.2.1
  let branches := state.2.2.2.2.1
  let fired := state.2.2.2.2.2
  -- a placement the check chose must have been met
  if world.napiBeforePut.any id then
    throw (results.size - 1, .invariant "napi_irq_before_put names more NAPI polls than the trace has")
  -- the domain filter: a schedule entry for an allocation site that the
  -- mirror never met would be left over in the kernel
  if world.hiddenPlaceholders && world.steerValues.any (fun e => world.allocSteered.contains e.1) then
    throw (trace.ops.size - 1, .outsideDomain "steer" "allocation schedule entries beyond the encounters")
  -- D3: the timer sections the environment ran (`fired:<symbol>`
  -- expectations), present only when one ran
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.napiAmbiguous)] else []))


def runnerBoundarySource (trace : Trace) (placeholders floodExact : Bool) :
    Except (Nat × Stop) Lean.Json := do
  let initial ← runnerInitial trace placeholders floodExact
  let final ← forIn trace.ops ((initial, #[], #[], #[], #[], #[]) : RunnerAccumulator)
    (runnerStep trace)
  runnerFinish trace final

theorem executeTrace_boundary_source (trace : Trace) (placeholders floodExact : Bool) :
    runnerBoundarySource trace placeholders floodExact = executeTrace trace placeholders floodExact := by
  unfold runnerBoundarySource runnerInitial executeTrace
  simp only [bind_assoc, pure_bind]
  split
  · cases h : Env.seccompPrefill trace.seccompPrefill
      (initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild)
    all_goals simp only [h, bind_assoc, pure_bind]
    all_goals rfl
  · rfl

end Leanux.Proofs.WG.Progress
