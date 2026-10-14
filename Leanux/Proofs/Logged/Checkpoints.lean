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
def executeTraceCheckpoints (project : Nat → World → α) (trace : Trace) (placeholders : Bool := false) (floodExact : Bool := false) : StateT (List α) (Except (Nat × Stop)) Json := do
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
  if trace.seccompPrefill > 0 then
    match Env.seccompPrefill trace.seccompPrefill world.k with
    | .ok k => world := { world with k }
    | .error e => throw (0, .invariant e)
  let mut results : Array Int := #[]
  let mut ends : Array (Option (Nat × Nat)) := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
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
    emitCheckpoint project index w
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

/-- Forgetting only checkpoint observations recovers the full original
runner result, including JSON and every exact indexed failure. -/
theorem executeTraceCheckpoints_erases (project : Nat → World → α)
    (trace : Trace) (placeholders : Bool) {floodExact : Bool} :
    ErasesT (executeTraceCheckpoints project trace placeholders floodExact)
      (Runner.executeTrace trace placeholders floodExact) := by
  unfold executeTraceCheckpoints Runner.executeTrace
  repeat' first
    | contradiction
    | with_reducible apply emitCheckpoint_then_erases
    | with_reducible exact erasesT_pure _
    | with_reducible exact erasesT_liftM _
    | with_reducible exact erasesT_lift _
    | with_reducible exact erasesT_throw _
    | with_reducible apply erasesT_ite
    | with_reducible apply erasesT_bind
    | with_reducible apply erasesT_map
    | with_reducible apply erasesT_array
    | with_reducible apply erasesT_forIn
    | intro_forall
    | dsimp only
    | (split <;> try simp_all only [reduceCtorEq])

/-- Original accepted traces and successful checkpoint-observer executions
have exactly the same JSON; the observation content is fixed at the emit site. -/
theorem executeTraceCheckpoints_success_iff (project : Nat → World → α)
    (trace : Trace) (placeholders : Bool) {floodExact : Bool} (json : Json) (observed : List α) :
    Runner.executeTrace trace placeholders floodExact = .ok json ↔
      ∃ observed', (executeTraceCheckpoints project trace placeholders floodExact).run observed =
        .ok (json, observed') :=
  erasesT_success_iff (executeTraceCheckpoints_erases project trace placeholders) json observed

end Leanux.Proofs.Logged
