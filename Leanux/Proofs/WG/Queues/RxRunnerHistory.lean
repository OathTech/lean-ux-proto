import Leanux.Proofs.WG.Queues.RxSyscallsHistory
import Leanux.Proofs.WG.Lifetimes.RunnerSafety

/-! Literal initialized Runner with committed stamped callback observations.
Outer composition transports the returned accumulator World. Indexed failures
retain their reached history; saved consistency trials remain isolated. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-- Direct full-audit projection under a predicate on the actual incoming
history. World predicates occur in P or in a result-dependent continuation. -/
def OuterProjects (P : List AuditEvent → Prop) (g : PrefixOuter Event α)
    (a : PrefixOuter AuditEvent α) : Prop :=
  ∀ h, P (auditHistory h) → runPrefixOuter a (auditHistory h) =
    ((runPrefixOuter g h).1, auditHistory (runPrefixOuter g h).2)

/-- Only successful returns supply a World to a continuation. Errors retain
history in the projection itself, and require no invented failed World. -/
def OuterEnsures (P : List AuditEvent → Prop) (a : PrefixOuter AuditEvent α)
    (Q : α → List AuditEvent → Prop) : Prop :=
  ∀ h, P h → match runPrefixOuter a h with
    | (.error _, _) => True
    | (.ok x, h') => Q x h'

theorem outerProjects_pure (x : α) : OuterProjects P (pure x) (pure x) :=
  fun _ _ => rfl

theorem outerProjects_throw (e : Nat × Stop) :
    OuterProjects P (throw e : PrefixOuter Event α) (throw e) := fun _ _ => rfl

/-- A reached Stop has no continuation; its retained history is exact. -/
theorem outerProjects_throw_bind (e : Nat × Stop)
    (f : α → PrefixOuter Event β) (b : α → PrefixOuter AuditEvent β) :
    OuterProjects P ((throw e : PrefixOuter Event α) >>= f) ((throw e : PrefixOuter AuditEvent α) >>= b) := by
  intro h _
  simp only [runPrefixOuter_bind, runPrefixOuter_throw]

theorem outerProjects_bind (hg : OuterProjects P g a) (ha : OuterEnsures P a Q)
    (hf : ∀ x, OuterProjects (Q x) (f x) (b x)) :
    OuterProjects P (g >>= f) (a >>= b) := by
  intro h hi
  have he := hg h hi
  have hp := ha (auditHistory h) hi
  rw [he] at hp
  rw [runPrefixOuter_bind, runPrefixOuter_bind, he]
  cases hr : runPrefixOuter g h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok x => exact hf x hist (by simpa only [hr] using hp)

theorem outerProjects_runAt (hg : ProjectsUnder AuditInv auditEvent g a)
    (index : Nat) (w : World) :
    OuterProjects (fun h => AuditInv h w) (runAtPrefix index w g) (runAtPrefix index w a) := by
  intro h hi
  have he := hg w h hi
  change runPrefix a w (auditHistory h) =
    ((runPrefix g w h).1, auditHistory (runPrefix g w h).2) at he
  simp only [runAtPrefix_run, he]

theorem outerEnsures_runAt (ha : PrefixPreserves AuditInv AuditSafe a)
    (index : Nat) (w : World) :
    OuterEnsures (fun h => AuditInv h w) (runAtPrefix index w a)
      (fun out h => AuditInv h out.2) := by
  intro h hi
  have hp := (ha w h hi).choose_spec.2.2
  rw [runAtPrefix_run]
  cases hr : runPrefix a w h with
  | mk result hist => cases result with
    | error _ => trivial
    | ok out => simpa only [hr, Except.mapError] using hp

theorem outerEnsures_pure (hq : ∀ h, P h → Q x h) :
    OuterEnsures P (pure x) Q := fun h hp => hq h hp

theorem outerEnsures_bind (ha : OuterEnsures P a Q)
    (hb : ∀ x, OuterEnsures (Q x) (b x) R) : OuterEnsures P (a >>= b) R := by
  intro h hi
  have hp := ha h hi
  rw [runPrefixOuter_bind]
  cases hr : runPrefixOuter a h with
  | mk result hist =>
    cases result with
    | error e => trivial
    | ok x => exact hb x hist (by simpa only [hr] using hp)

def outerStepValue : ForInStep α → α | .done x => x | .yield x => x

theorem outerEnsures_forIn {I : β → List AuditEvent → Prop} (xs : List γ) (init : β)
    (a : γ → β → PrefixOuter AuditEvent (ForInStep β))
    (ha : ∀ x b, OuterEnsures (I b) (a x b) (fun step => I (outerStepValue step))) :
    OuterEnsures (I init) (forIn xs init a) I := by
  induction xs generalizing init with
  | nil => simpa only [List.forIn_nil] using outerEnsures_pure (fun _ hi => hi)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply outerEnsures_bind (ha x init)
    intro step
    cases step with
    | done b => exact outerEnsures_pure (fun _ hi => hi)
    | yield b => exact ih b

theorem outerProjects_forIn {I : β → List AuditEvent → Prop} (xs : List γ) (init : β)
    (g : γ → β → PrefixOuter Event (ForInStep β))
    (a : γ → β → PrefixOuter AuditEvent (ForInStep β))
    (ha : ∀ x b, OuterEnsures (I b) (a x b) (fun step => I (outerStepValue step)))
    (hg : ∀ x b, OuterProjects (I b) (g x b) (a x b)) :
    OuterProjects (I init) (forIn xs init g) (forIn xs init a) := by
  induction xs generalizing init with
  | nil => exact outerProjects_pure init
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply outerProjects_bind (hg x init) (ha x init)
    intro step
    cases step with
    | done b => exact outerProjects_pure b
    | yield b => exact ih b

theorem outerProjects_array {I : β → List AuditEvent → Prop} (xs : Array γ) (init : β)
    (g : γ → β → PrefixOuter Event (ForInStep β))
    (a : γ → β → PrefixOuter AuditEvent (ForInStep β))
    (ha : ∀ x b, OuterEnsures (I b) (a x b) (fun step => I (outerStepValue step)))
    (hg : ∀ x b, OuterProjects (I b) (g x b) (a x b)) :
    OuterProjects (I init) (forIn xs init g) (forIn xs init a) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact outerProjects_forIn _ _ _ _ ha hg


theorem outerProjects_pre (hg : OuterProjects Q g a) (hp : ∀ h, P h → Q h) :
    OuterProjects P g a := fun h hi => hg h (hp _ hi)

theorem outerProjects_runAt_bind {α β : Type} {g : Obs α} {a : AuditM α}
    {f : α × World → PrefixOuter Event β} {b : α × World → PrefixOuter AuditEvent β}
    (hg : ProjectsUnder AuditInv auditEvent g a)
    (ha : PrefixPreserves AuditInv AuditSafe a) (index : Nat) (w : World)
    (hi : ∀ h, P h → AuditInv h w)
    (hf : ∀ out, OuterProjects (fun h => AuditInv h out.2) (f out) (b out)) :
    OuterProjects P (runAtPrefix index w g >>= f) (runAtPrefix index w a >>= b) :=
  outerProjects_pre (outerProjects_bind (outerProjects_runAt hg index w)
    (outerEnsures_runAt ha index w) hf) hi

theorem outerProjects_map (f : α → β) (hg : OuterProjects P g a) :
    OuterProjects P (f <$> g) (f <$> a) := by
  intro h hi
  have he := hg h hi
  simp only [map_eq_pure_bind, runPrefixOuter_bind, he]
  cases hr : runPrefixOuter g h with
  | mk result hist => cases result <;> rfl

theorem outerProjects_ite (p : Prop) [Decidable p]
    (ht : p → OuterProjects P gt at') (he : ¬p → OuterProjects P ge ae) :
    OuterProjects P (if p then gt else ge) (if p then at' else ae) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

theorem outerProjects_array_bind {I : β → List AuditEvent → Prop}
    (xs : Array γ) (init : β)
    (g : γ → β → PrefixOuter Event (ForInStep β))
    (a : γ → β → PrefixOuter AuditEvent (ForInStep β))
    (hi : ∀ h, P h → I init h)
    (ha : ∀ x b, OuterEnsures (I b) (a x b) (fun step => I (outerStepValue step)))
    (hg : ∀ x b, OuterProjects (I b) (g x b) (a x b))
    (hf : ∀ out, OuterProjects (I out) (f out) (b out)) :
    OuterProjects P (forIn xs init g >>= f) (forIn xs init a >>= b) := by
  apply outerProjects_pre (outerProjects_bind (outerProjects_array xs init g a ha hg) ?_ hf) hi
  rw [← Array.forIn_toList]
  exact outerEnsures_forIn _ _ _ ha

theorem outerEnsures_of_wp (ha :
    ⦃fun h => ⌜P h⌝⦄ a ⦃post⟨fun x h => ⌜Q x h⌝, fun _ _ => ⌜True⌝⟩⦄) :
    OuterEnsures P a Q := by
  intro h hi
  have hp := (prefixOuter_wp_iff _ _ _ _).mp ha h hi
  cases hr : runPrefixOuter a h with
  | mk result hist => cases result with
    | error _ => trivial
    | ok out => simpa only [hr] using hp


theorem outerProjects_array_from {I : β → List AuditEvent → Prop}
    (xs : Array γ) (init : β)
    (g : γ → β → PrefixOuter Event (ForInStep β))
    (a : γ → β → PrefixOuter AuditEvent (ForInStep β))
    (hi : ∀ h, P h → I init h)
    (ha : ∀ x b, OuterEnsures (I b) (a x b) (fun step => I (outerStepValue step)))
    (hg : ∀ x b, OuterProjects (I b) (g x b) (a x b)) :
    OuterProjects P (forIn xs init g) (forIn xs init a) :=
  outerProjects_pre (outerProjects_array xs init g a ha hg) hi

/-- Literal post-prefill runner body, parameterized only by its syscall
observer. JSON and indexed guards remain inside this source-shaped cut. -/
def runnerTail {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace) (initialWorld : World) : PrefixOuter E Json := do
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
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else []))


def executeTraceWith {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace) (placeholders : Bool := false) : PrefixOuter E Json := do
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
  runnerTail call trace world

def executeTraceHistory (trace : Trace) (placeholders : Bool) : PrefixOuter Event Json :=
  executeTraceWith syscall trace placeholders

theorem executeTraceAudit_eq (trace : Trace) (placeholders : Bool) :
    executeTraceAudit trace placeholders = executeTraceWith syscallAudit trace placeholders := by
  rfl

private def runnerHistorySourceTail (trace : Trace) (initialWorld : World) : Except (Nat × Stop) Json := do
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
    let (ret, w) ← (Leanux.syscall (toSyscall results ends index op)).run world |>.mapError fun e => (index, e)
    let (_, w) ← (skipAmbient : Leanux.M Unit).run w |>.mapError fun e => (index, e)
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
  return Json.mkObj ([("version", toJson (1 : Nat)), ("id", toJson trace.id),
    ("observations", .arr observations), ("branches", .arr branches)]
    ++ (if fired.isEmpty then [] else [("fired", .arr fired)])
    ++ (if world.fixture.napiAmbiguous > 0 then [("napi_irq_ambiguous", toJson world.fixture.napiAmbiguous)] else []))

private def runnerHistorySource (trace : Trace) (placeholders : Bool := false) : Except (Nat × Stop) Json := do
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
  runnerHistorySourceTail trace world


private theorem runnerHistoryTail_erases (trace : Trace) (w : World) :
    ErasesOuter (runnerTail syscall trace w) (runnerHistorySourceTail trace w) := by
  unfold runnerTail runnerHistorySourceTail
  repeat' first
    | (maintenance_head syscall; exact syscall_erases _)
    | audit_runner_erasure_step

theorem executeTraceHistory_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (executeTraceHistory trace placeholders)
      (Runner.executeTrace trace placeholders) := by
  change ErasesOuter (executeTraceHistory trace placeholders) (runnerHistorySource trace placeholders)
  unfold executeTraceHistory executeTraceWith runnerHistorySource
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases (Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild))
  all_goals repeat' first
    | (maintenance_head runnerTail; exact runnerHistoryTail_erases _ _)
    | audit_runner_erasure_step

theorem runAtBoundary_wp {g : Obs α} (hg : PrefixPreserves BoundaryInv BoundarySafe g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜BoundaryInv h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜BoundaryInv h out.2⌝, fun _ h => ⌜BoundarySafe h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures BoundaryInv BoundarySafe g (fun _ => BoundaryInv) from hg) index w

/-- Checked conditional composition at the existing observer stack. -/
private theorem rxRunnerTriple_ite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a b : m α) (ha : c → Triple a P Q) (hb : ¬c → Triple b P Q) :
    Triple (if c then a else b) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using ha h
  · simpa only [h, ↓reduceIte] using hb h

private theorem rxRunnerTriple_dite {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps]
    {α : Type u} {P : Assertion ps} {Q : PostCond α ps} (c : Prop) [Decidable c]
    (a : c → m α) (b : ¬c → m α)
    (ha : ∀ h, Triple (a h) P Q) (hb : ∀ h, Triple (b h) P Q) :
    Triple (if h : c then a h else b h) P Q := by
  by_cases h : c
  · simpa only [h, ↓reduceDIte] using ha h
  · simpa only [h, ↓reduceDIte] using hb h

private def boundaryRunnerWorldAssertion (w : World) : Assertion
    (.except (Nat × Stop) (.arg (List Event) .pure)) :=
  fun h => ⌜BoundaryInv h w⌝

private def boundaryRunnerResultAssertion (type pre : Lean.Expr) : Lean.MetaM Lean.Expr := do
  Lean.Meta.withLocalDeclD `out type fun out => do
    let world? ←
      if ← Lean.Meta.isDefEq type (Lean.mkConst ``World) then pure (some out)
      else if type.isAppOf ``Prod then
        let args := type.getAppArgs
        if ← Lean.Meta.isDefEq args[0]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 0 out))
        else if ← Lean.Meta.isDefEq args[1]! (Lean.mkConst ``World) then
          pure (some (Lean.mkProj ``Prod 1 out))
        else pure none
      else pure none
    let assertion ← match world? with
      | some w => Lean.Meta.mkAppM ``boundaryRunnerWorldAssertion #[w]
      | none => pure pre
    Lean.Meta.mkLambdaFVars #[out] assertion

elab "boundary_runner_wp_bind" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let aa := action.getAppArgs
  let x := aa[aa.size - 2]!
  let type ← Lean.Meta.inferType x
  let result := type.getAppArgs.back!
  let q ← boundaryRunnerResultAssertion result args[args.size - 2]!
  let mut proof ← Lean.Meta.mkConstWithFreshMVarLevels ``Triple.bind
  let mut type ← Lean.Meta.inferType proof
  let mut goals : List Lean.MVarId := []
  while let .forallE name domain body _ := type.consumeMData do
    let argument ←
      match name.toString with
      | "m" => pure args[0]!
      | "ps" => pure args[1]!
      | "α" => pure result
      | "β" => pure args[3]!
      | "P" => pure args[args.size - 2]!
      | "Q" => pure q
      | "R" => pure args.back!
      | "x" => pure x
      | "f" => pure aa.back!
      | "hx" | "hf" =>
        let hole ← Lean.Meta.mkFreshExprMVar domain
        goals := goals ++ [hole.mvarId!]
        pure hole
      | _ => Lean.Meta.synthInstance domain
    unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType argument) domain do
      Lean.throwError "canonical bind parameter {name} has the wrong type"
    proof := Lean.mkApp proof argument
    type := body.instantiate1 argument
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal goals

elab "boundary_runner_wp_array" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Triple do Lean.throwError "not a triple"
  let args := target.getAppArgs
  let action := args[args.size - 3]!.consumeMData
  unless action.isAppOf ``ForIn.forIn do Lean.throwError "not forIn"
  let aa := action.getAppArgs
  let init := aa[aa.size - 2]!
  let result ← Lean.Meta.inferType init
  let q ← boundaryRunnerResultAssertion result args[args.size - 2]!
  let qterm ← Lean.PrettyPrinter.delab q
  let qtype ← Lean.PrettyPrinter.delab (← Lean.Meta.inferType q)
  let qsyntax ← `(term| ($qterm : $qtype))
  let err ← Lean.Meta.whnf (Lean.mkProj ``Prod 1 args.back!)
  let esyntax ← Lean.PrettyPrinter.delab err
  let psyntax ← Lean.PrettyPrinter.delab args[1]!
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    apply Triple.entails_wp_of_pre_post (ps := $psyntax) (Q' := ($qsyntax, $esyntax))))
  let rest := (← Lean.Elab.Tactic.getGoals).tail
  Lean.Elab.Tactic.setGoals [(← Lean.Elab.Tactic.getMainGoal)]
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [← Array.forIn_toList]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply Spec.forIn_list_const_inv))
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro hd acc))
  Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getGoals) ++ rest)

private theorem runnerHistoryTail_safe_wp (trace : Trace) (w : World) :
    ⦃fun h => ⌜BoundaryInv h w⌝⦄ runnerTail syscall trace w
    ⦃post⟨fun _ h => ⌜BoundarySafe h⌝, fun _ h => ⌜BoundarySafe h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtBoundary_wp (syscall_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtBoundary_wp (boundaryLift_kernel skipAmbient (by
      intro initial
      exact productAmbient_spec _ _ (fun _ _ hi => hi))) index w
  unfold runnerTail
  repeat' first
    | (runner_wp_call syscall; apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | (runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter Event) (ps := .except (Nat × Stop) (.arg (List Event) .pure)))
    | (runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List Event)) (ps := .arg (List Event) .pure)))
    | runner_wp_throw_bind
    | boundary_runner_wp_bind
    | boundary_runner_wp_array
    | runner_wp_reduce
    | (runner_wp_head ite; apply rxRunnerTriple_ite)
    | (runner_wp_head dite; apply rxRunnerTriple_dite)
    | maintenance_intro
    | runner_wp_match
  all_goals try dsimp only [boundaryRunnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact BoundaryInv.productStore hi rfl)
  all_goals try (solve | intro history hi; exact BoundaryInv.safe hi)


theorem executeTraceHistory_safe_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜BoundarySafe h⌝, fun _ h => ⌜BoundarySafe h⌝⟩⦄ := by
  have tail_spec (w : World) := runnerHistoryTail_safe_wp trace w
  have boot_store (foreign : Bool) : SameView (fun w => wgStoreView w.wg)
      (do Net.Fib.bootTables
          if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
    apply SameView.bind
    · intro initial
      exact productRouting_spec _ (fun s => s.2.2.2 = initial)
    · intro _
      split
      · intro initial
        exact productRouting_spec _ (fun s => s.2.2.2 = initial)
      · exact SameView.pure _ _
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w = .ok (x, v))
      (hi : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
      wgStoreView v.wg = wgStoreView (initialWG trace.net trace.bare) :=
    ((ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  unfold executeTraceHistory executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases (Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild))
  all_goals repeat' first
    | (runner_wp_head runnerTail; apply Triple.entails_wp_of_pre_post (tail_spec _))
    | (runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter Event) (ps := .except (Nat × Stop) (.arg (List Event) .pure)))
    | (runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List Event)) (ps := .arg (List Event) .pure)))
    | runner_wp_throw_bind
    | boundary_runner_wp_bind
    | boundary_runner_wp_array
    | runner_wp_reduce
    | (runner_wp_head ite; apply rxRunnerTriple_ite)
    | (runner_wp_head dite; apply rxRunnerTriple_dite)
    | maintenance_intro
    | runner_wp_match
  all_goals try dsimp only [boundaryRunnerWorldAssertion] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact BoundaryInv.productStore hi rfl)
  all_goals try (solve | intro history hi; exact BoundaryInv.safe hi)
  all_goals
    intro history hi
    change history = [] at hi
    subst history
    first
    | change BoundarySafe []
      refine ⟨?_, ?_⟩
      · exact ⟨⟨AccessEvent.safe_nil, AccessEvent.safe_nil, AccessEvent.safe_nil⟩,
          by simp [AllProbeValid, probeEntries, auditHistory]⟩
      · simp [stamps, entries]
    | apply boundary_initial
      apply allocation_initial trace.net trace.bare
      first
      | rfl
      | rename_i hrun
        have hb := boot_initial _ _ _ hrun (by rfl)
        exact hb

/-- Safety is unconditional in the original result: Stops preserve their reached
committed history and saved filter-entry validity just as successful JSON does. -/
theorem executeTraceHistory_safe (trace : Trace) (placeholders : Bool) :
    BoundarySafe (runPrefixOuter (executeTraceHistory trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceHistory_safe_wp trace placeholders) [] rfl
  cases hr : runPrefixOuter (executeTraceHistory trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

/-- Select an outer observer head without unfolding a mismatched action. -/
elab "rx_outer_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``OuterProjects do Lean.throwError "not an outer projection"
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing outer observers"
  let .const actual _ := args[args.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a named outer action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different outer action"

elab "rx_runner_projects_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``OuterProjects do Lean.throwError "not a projection"
  let .app (.app front observed) original := target | Lean.throwError "missing actions"
  let .letE oname oty oval obody _ := observed.consumeMData | Lean.throwError "not an observer let"
  let .letE rname rty rval rbody _ := original.consumeMData | Lean.throwError "not a source let"
  unless oname.toString.startsWith "__do_jp" && rname.toString.startsWith "__do_jp" do
    Lean.throwError "not paired joins"
  let property (g a : Lean.Expr) := Lean.mkApp2 front g a
  let valueContract ← Lean.Meta.forallTelescope oty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN oval args) (Lean.mkAppN rval args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD oname oty fun g => do
    Lean.Meta.withLocalDeclD rname rty fun a => do
      let contract ← Lean.Meta.forallTelescope oty fun args _ => do
        Lean.Meta.mkForallFVars args (property (Lean.mkAppN g args) (Lean.mkAppN a args))
      Lean.Meta.withLocalDeclD `rx_runner_projection_join contract fun hg => do
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (property (obody.instantiate1 g) (rbody.instantiate1 a))
        let proof ← Lean.Meta.mkLambdaFVars #[g, a, hg] next
        pure (proof, next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[oval, rval, valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "rx_runner_projects_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``OuterProjects do Lean.throwError "not a projection"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!.consumeMData
  let original := args.back!.consumeMData
  unless observed.getAppFn.isFVar && original.getAppFn.isFVar do
    Lean.throwError "not paired local continuations"
  for decl in ← Lean.getLCtx do
    if decl.userName == `rx_runner_projection_join then
      let proof := Lean.mkAppN decl.toExpr observed.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no paired continuation contract"

elab "rx_runner_projects_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``OuterProjects do Lean.throwError "not a projection"
  let .app (.app front observed) lower := target | Lean.throwError "missing paired observers"
  let rec head : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. => let next := e.headBeta; if Lean.Expr.equal e next then e else head n next
        | _ => e
  let reduce (a : Lean.Expr) : Lean.MetaM Lean.Expr := do
    let a := head 64 a
    if (← Lean.Meta.matchMatcherApp? a).isSome then
      if let .reduced next ← Lean.Meta.reduceMatcher? a then return next
    return a
  let observed' ← reduce observed
  let lower' ← reduce lower
  if Lean.Expr.equal observed observed' && Lean.Expr.equal lower lower' then
    Lean.throwError "unchanged paired heads"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp2 front observed' lower')]


elab "rx_outer_bind_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``OuterProjects do Lean.throwError "not an outer projection"
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing outer observers"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``Bind.bind do Lean.throwError "not an outer bind"
  let bound := action.getAppArgs
  unless bound.size ≥ 2 do Lean.throwError "missing bound action"
  let .const actual _ := bound[bound.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a named bound action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different bound action"

macro "rx_runner_lower_wp " syscall_spec:ident ambient_spec:ident : tactic => `(tactic|
  (repeat' first
    | (runner_wp_call syscallAudit; apply Triple.entails_wp_of_pre_post ($syscall_spec _ _ _))
    | (runner_wp_call liftPrefix; apply Triple.entails_wp_of_pre_post ($ambient_spec _ _))
    | (runner_wp_head Pure.pure; apply Triple.pure
        (m := PrefixOuter AuditEvent) (ps := .except (Nat × Stop) (.arg (List AuditEvent) .pure)))
    | (runner_wp_head throw; apply Triple.entails_wp_of_pre
        (Spec.throw_ExceptT (m := StateM (List AuditEvent)) (ps := .arg (List AuditEvent) .pure)))
    | runner_wp_throw_bind
    | runner_wp_bind
    | (runner_wp_head ForIn.forIn; rw [← Array.forIn_toList]; apply Spec.forIn_list_const_inv)
    | runner_wp_array
    | runner_wp_reduce
    | (runner_wp_head ite; apply rxRunnerTriple_ite)
    | (runner_wp_head dite; apply rxRunnerTriple_dite)
    | maintenance_intro
    | runner_wp_match))

/-- Exact full-audit correspondence uses the returned World after each indexed
call and the actual prior history, including all reached filter probe payloads. -/
theorem runnerTail_projects (trace : Trace) (w : World) :
    OuterProjects (fun h => AuditInv h w) (runnerTail syscall trace w)
      (runnerTail syscallAudit trace w) := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtAudit_wp (syscallAudit_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtAudit_wp (auditLift_store skipAmbient (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))) index w
  unfold runnerTail
  repeat' first
    | contradiction
    | rx_runner_projects_join
    | rx_runner_projects_join_use
    | rx_runner_projects_reduce
    | (audit_contract OuterEnsures; apply outerEnsures_of_wp;
        rx_runner_lower_wp syscall_spec ambient_spec)
    | (rx_outer_head Pure.pure; exact outerProjects_pure _)
    | (rx_outer_head throw; exact outerProjects_throw _)
    | (rx_outer_bind_head throw; apply outerProjects_throw_bind)
    | (rx_outer_bind_head runAtPrefix; apply outerProjects_runAt_bind (syscall_projects _) (syscallAudit_preserves _))
    | (rx_outer_bind_head runAtPrefix; apply outerProjects_runAt_bind (projectsUnder_lift _ _) (auditLift_store skipAmbient (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))))
    | (rx_outer_bind_head ForIn.forIn; apply outerProjects_array_bind (I := fun (acc : World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json) h => AuditInv h acc.1))
    | (rx_outer_head ForIn.forIn; apply outerProjects_array_from (I := fun (acc : World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json) h => AuditInv h acc.1))
    | (rx_outer_bind_head ForIn.forIn; apply outerProjects_array_bind (I := fun (_ : Array Json) h => AuditInv h _))
    | (rx_outer_head ForIn.forIn; apply outerProjects_array_from (I := fun (_ : Array Json) h => AuditInv h _))
    | (rx_outer_head Functor.map; apply outerProjects_map)
    | (rx_outer_head ite; apply outerProjects_ite)
    | maintenance_intro
    | (with_reducible change OuterProjects _ _ _; split <;> try simp_all only [])
  all_goals try (solve | intro h hi; exact AuditInv.store hi rfl)
  all_goals try (solve | intro h hi; exact hi)
  all_goals try (apply outerEnsures_of_wp; rx_runner_lower_wp syscall_spec ambient_spec)
  all_goals try dsimp only [outerStepValue] at *
  all_goals try exact SPred.true_intro
  all_goals try exact ⟨fun _ => .rfl, ExceptConds.entails_true⟩
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; trivial)
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro h hi; exact AuditInv.store hi rfl)
  all_goals first
    | (rw [Array.forIn_pure_yield_eq_foldl]; apply Triple.pure; exact .rfl)
    | (rename_i hi; exact AuditInv.store hi rfl)

/-- Initialize the abstract tail with the source's actual initial/prefilled
product World. All flags and defaulted arrays retain the original definitions. -/
theorem executeTraceHistory_projects_under (trace : Trace) (placeholders : Bool) :
    OuterProjects (fun h => h = []) (executeTraceHistory trace placeholders)
      (executeTraceAudit trace placeholders) := by
  have boot_store (foreign : Bool) : SameView (fun w => wgStoreView w.wg)
      (do Net.Fib.bootTables
          if foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit) := by
    apply SameView.bind
    · intro initial
      exact productRouting_spec _ (fun s => s.2.2.2 = initial)
    · intro _
      split
      · intro initial
        exact productRouting_spec _ (fun s => s.2.2.2 = initial)
      · exact SameView.pure _ _
  have boot_initial (w v : World) (x : Unit)
      (hr : (do Net.Fib.bootTables
                if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables : Leanux.M Unit).run w = .ok (x, v))
      (hi : wgStoreView w.wg = wgStoreView (initialWG trace.net trace.bare)) :
      wgStoreView v.wg = wgStoreView (initialWG trace.net trace.bare) :=
    ((ProjectedAction.iff_run _ _ _).mp (boot_store trace.foreign) w x v hr).trans hi
  rw [executeTraceAudit_eq]
  unfold executeTraceHistory executeTraceWith
  by_cases hp : trace.seccompPrefill > 0
  all_goals simp only [hp, ↓reduceIte]
  all_goals cases (Env.seccompPrefill trace.seccompPrefill ({} : SeccompWorld) (initialTasks trace.rlimit trace.foreign trace.stepped trace.seccompChild))
  all_goals repeat' first
    | contradiction
    | (rx_outer_head throw; exact outerProjects_throw _)
    | with_reducible apply outerProjects_throw_bind
    | (rx_outer_head runnerTail; apply outerProjects_pre (runnerTail_projects _ _))
    | (rx_outer_head ite; apply outerProjects_ite)
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | (with_reducible change OuterProjects _ _ _; split <;> try simp_all only [])
  all_goals
    try intro history hh
    subst_vars
    apply audit_initial
    apply allocation_initial trace.net trace.bare
    first
    | rfl
    | rename_i hrun
      have hb := boot_initial _ _ _ hrun (by rfl)
      simp only [*]

/-- Initialized exact audit projection, including indexed failure histories. -/
theorem executeTraceHistory_projects (trace : Trace) (placeholders : Bool) :
    runPrefixOuter (executeTraceAudit trace placeholders) [] =
      ((runPrefixOuter (executeTraceHistory trace placeholders) []).1,
       auditHistory (runPrefixOuter (executeTraceHistory trace placeholders) []).2) :=
  executeTraceHistory_projects_under trace placeholders [] rfl

/-- Transfer the existing reached-filter and isolated-trial guarantees through
the direct full-audit equality. Trial events are not committed callback entries. -/
theorem executeTraceHistory_trials (trace : Trace) (placeholders : Bool) :
    ∀ p ∈ probeEntries (auditHistory (runPrefixOuter (executeTraceHistory trace placeholders) []).2),
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended,
        LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have he := congrArg Prod.snd (executeTraceHistory_projects trace placeholders)
  simpa only [he] using executeTraceAudit_trials trace placeholders

end Leanux.Proofs.WG.Queues.RxHistory
