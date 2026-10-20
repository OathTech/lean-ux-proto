import Leanux.Proofs.WG.Queues.JointRunnerSource

/-! Literal factors of the existing runner operation. The successful result
arrays, saved descriptor ends, exact syscall conversion and all guards retain
the original order. These factors introduce no new observer or journal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerOperation
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

abbrev State := World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json

def prepare (trace : Trace) (state : State) : World :=
  let world := state.1
  let index := state.2.1.size
  let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList
  { world with
    ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) }
    fixture := { world.fixture with hiddenAhead := ahead }
    wg := { world.wg with netRxRaised := false } }

def afterCall {E : Type} (op : Operation) (state : State) (ret : Int) (w : World) :
    PrefixOuter E (ForInStep State) := do
  let mut world := state.1
  let mut results := state.2.1
  let mut ends := state.2.2.1
  let mut observations := state.2.2.2.1
  let mut branches := state.2.2.2.2.1
  let mut fired := state.2.2.2.2.2
  let index := results.size
  let (_, w) ← runAtPrefix index w (liftPrefix (skipAmbient : Leanux.M Unit))
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
  return .yield (world,results,ends,observations,branches,fired)

def operation {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (op : Operation) (state : State) : PrefixOuter E (ForInStep State) := do
  let results := state.2.1
  let ends := state.2.2.1
  let index := results.size
  let (ret,w) ← runAtPrefix index (prepare trace state) (call (toSyscall results ends index op))
  afterCall op state ret w

def finishWith {E α : Type} (finish : Json → World → α) (trace : Trace) (state : State) : PrefixOuter E α := do
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
  return finish (Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else []))) world

theorem tail_factor {E α : Type} (call : Syscall → PrefixM E Int) (finish : Json → World → α)
    (trace : Trace) (w : World) :
    RoutingJoint.runnerTailWith call finish trace w = (do
      let state ← forIn trace.ops (w,#[],#[],#[],#[],#[]) (operation call trace)
      finishWith finish trace state) := by rfl

theorem bind_normal {E α β : Type} {front : PrefixOuter E α} {tail : α → PrefixOuter E β}
    {h k : List E} {result : β}
    (run : runPrefixOuter (front >>= tail) h = (.ok result,k)) :
    ∃ x j,runPrefixOuter front h = (.ok x,j) ∧ runPrefixOuter (tail x) j = (.ok result,k) := by
  rw [runPrefixOuter_bind] at run
  cases start : runPrefixOuter front h with
  | mk outcome j =>
    rw [start] at run
    cases outcome with
    | error reason => cases run
    | ok x => exact ⟨x,j,rfl,run⟩

/-- A normal operation exposes the actual syscall invocation, including
the saved descriptor/results-dependent conversion and its exact journal cut.
The operation's own normal run supplies its continuation. -/
theorem operation_cut {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (op : Operation) (state : State)
    {h k : List E} {result : ForInStep State}
    (run : runPrefixOuter (operation call trace op state) h = (.ok result,k)) :
    ∃ ret w j,
      runPrefix (call (toSyscall state.2.1 state.2.2.1 state.2.1.size op))
        (prepare trace state) h = (.ok (ret,w),j) ∧
      runPrefixOuter (afterCall op state ret w) j = (.ok result,k) := by
  obtain ⟨out,j,front,rest⟩ := bind_normal run
  rw [runAtPrefix_run] at front
  cases actual : runPrefix (call (toSyscall state.2.1 state.2.2.1 state.2.1.size op))
      (prepare trace state) h with
  | mk outcome history =>
    rw [actual] at front
    cases outcome with
    | error reason => cases front
    | ok value =>
      cases front
      exact ⟨out.1,out.2,history,rfl,rest⟩

/-- Successful metadata/guard processing always advances the result index
once; even a negative syscall result occupies its original operation slot. -/
theorem afterCall_index {E : Type} (op : Operation) (state : State) (ret : Int) (w : World)
    {h k : List E} {result : ForInStep State}
    (run : runPrefixOuter (afterCall (E:=E) op state ret w) h = (.ok result,k)) :
    ∃ out,result = .yield out ∧ out.2.1 = state.2.1.push ret := by
  unfold afterCall at run
  obtain ⟨returned,j,start,rest⟩ := bind_normal run
  rcases returned with ⟨ignored,world⟩
  cases hidden : world.ambient.hidden with
  | none =>
    cases suspended : world.ambient.suspended with
    | nil =>
      cases pending : world.ambient.pendingWork with
      | cons unit restUnits =>
        simp only [hidden,suspended,pending,Option.isSome_none,Bool.false_eq_true,↓reduceIte] at rest
        cases rest
      | nil =>
        cases raised : world.wg.netRxRaised <;>
          simp only [hidden,suspended,pending,raised,Bool.false_eq_true,↓reduceIte] at rest
        · obtain ⟨branches,l,branchRun,rest⟩ := bind_normal rest
          obtain ⟨fired,m,firedRun,rest⟩ := bind_normal rest
          cases rest
          exact ⟨_,rfl,rfl⟩
        · cases rest
    | cons head tail => simp only [hidden,suspended,runPrefixOuter_bind] at rest; cases rest
  | some records =>
    cases records with
    | nil =>
      cases suspended : world.ambient.suspended with
      | nil =>
        cases pending : world.ambient.pendingWork with
        | cons unit restUnits =>
          simp only [hidden,suspended,pending] at rest
          cases rest
        | nil =>
          cases raised : world.wg.netRxRaised <;>
            simp only [hidden,suspended,pending,raised,Bool.false_eq_true,↓reduceIte] at rest
          · obtain ⟨branches,l,branchRun,rest⟩ := bind_normal rest
            obtain ⟨fired,m,firedRun,rest⟩ := bind_normal rest
            cases rest
            exact ⟨_,rfl,rfl⟩
          · cases rest
      | cons head tail => simp only [hidden,suspended,runPrefixOuter_bind] at rest; cases rest
    | cons head tail => simp only [hidden,runPrefixOuter_bind] at rest; cases rest

theorem operation_index {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (op : Operation) (state : State) {h k : List E} {result : ForInStep State}
    (run : runPrefixOuter (operation call trace op state) h = (.ok result,k)) :
    ∃ out,result = .yield out ∧ out.2.1.size = state.2.1.size+1 := by
  obtain ⟨ret,w,j,front,rest⟩ := operation_cut call trace op state run
  obtain ⟨out,same,values⟩ := afterCall_index op state ret w rest
  exact ⟨out,same,by rw [values,Array.size_push]⟩

end Leanux.Proofs.WG.Queues.RxCredits.RunnerOperation
