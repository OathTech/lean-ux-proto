import Leanux.Proofs.Logged.Outer
import Leanux.Proofs.Logged.Syscalls
import Leanux.Runner

/-! The complete proof-side acceptance observer for the pinned runner.
Erasing history preserves JSON and exact indexed errors for every input. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.Logged
open Lean Leanux Leanux.Runner

def executeTraceLogged (trace : Trace) (placeholders : Bool := false) : StateT History (Except (Nat × Stop)) Json := do
  let mut world : World := { k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped, env := harnessEnv,
                             timing := Env.timing, portBound := Env.portBound,
                             fixtureNetDevices := Env.fixtureNetDevices,
                             foreignCreator := trace.foreign,
                             netnsCHolders := if trace.foreign then [9, 8, 5, 4] else [],
                             allocArmed := trace.allocArmed, routes := trace.routes,
                             hiddenPlaceholders := placeholders && trace.hidden.isNone,
                             steerValues := if placeholders then trace.steer else [],
                             armRecords := trace.armRecords, dstCacheRecords := trace.dstCacheRecords,
                             napiBeforePut := trace.napiBeforePut,
                             allocSteered := if placeholders then
                               (trace.steer.map (·.1)).filter fun l => AllocSite.all.any (·.info.label == l)
                             else [] }
  let mut results : Array Int := #[]
  let mut ends : Array (Option (Nat × Nat)) := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    world := { world with hidden := trace.hidden.map (·[index]!), netRxRaised := false }
    let (ret, w) ← runAtLogged index world (syscallLogged (toSyscall results ends index op))
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

/-- Exact erasure all the way to the unchanged executable runner.
This is the observation bridge, not yet the no-duplicate invariant. -/
theorem executeTraceLogged_erases (trace : Trace) (placeholders : Bool) :
    ErasesT (executeTraceLogged trace placeholders) (Runner.executeTrace trace placeholders) := by
  unfold executeTraceLogged Runner.executeTrace
  repeat' first
    | contradiction
    | with_reducible exact syscallLogged_erases _
    | with_reducible apply runAtLogged_erases
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

/-- Accepted runner inputs have an observer history and unchanged JSON.
The history invariant is a separate proof obligation. -/
theorem executeTraceLogged_success_iff (trace : Trace) (placeholders : Bool)
    (json : Json) (history : History) :
    Runner.executeTrace trace placeholders = .ok json ↔
      ∃ history', (executeTraceLogged trace placeholders).run history = .ok (json, history') :=
  erasesT_success_iff (executeTraceLogged_erases trace placeholders) json history

end Leanux.Proofs.Logged
