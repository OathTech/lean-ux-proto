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
  | mk result hist => cases result <;> simpa only [hr, Except.mapError] using hp

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
  | mk result hist => cases result <;> simpa only [hr] using hp


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
def runnerTail {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace)
    (initialWorld : World) : PrefixOuter E Json := do
  let mut world := initialWorld
  let mut results : Array Int := #[]
  let mut ends : Array (Option (Nat × Nat)) := #[]
  let mut observations : Array Json := #[]
  let mut branches : Array Json := #[]
  let mut fired : Array Json := #[]
  for op in trace.ops do
    let index := results.size
    world := { world with hidden := trace.hidden.map (·[index]!), netRxRaised := false }
    let (ret, w) ← runAtPrefix index world (call (toSyscall results ends index op))
    let (_, w) ← runAtPrefix index w (liftPrefix skipAmbient)
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

def executeTraceWith {E : Type} (call : Syscall → PrefixM E Int) (trace : Trace) (placeholders : Bool := false) : PrefixOuter E Json := do
  let mut world : World := { k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild, env := harnessEnv,
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
  if trace.seccompPrefill > 0 then
    match Env.seccompPrefill trace.seccompPrefill world.k with
    | .ok k => world := { world with k }
    | .error e => throw (0, .invariant e)
  runnerTail call trace world

def executeTraceHistory (trace : Trace) (placeholders : Bool) : PrefixOuter Event Json :=
  executeTraceWith syscall trace placeholders

theorem executeTraceAudit_eq (trace : Trace) (placeholders : Bool) :
    executeTraceAudit trace placeholders = executeTraceWith syscallAudit trace placeholders := by
  rfl

theorem executeTraceHistory_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (executeTraceHistory trace placeholders)
      (Runner.executeTrace trace placeholders) := by
  unfold executeTraceHistory executeTraceWith runnerTail Runner.executeTrace
  repeat' first
    | contradiction
    | with_reducible exact syscall_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible apply runAtPrefix_erases
    | with_reducible exact erasesOuter_pure _
    | with_reducible exact erasesOuter_throw _
    | with_reducible apply erasesOuter_ite
    | with_reducible apply erasesOuter_bind
    | with_reducible apply erasesOuter_map
    | with_reducible apply erasesOuter_array
    | with_reducible apply erasesOuter_forIn
    | intro_forall
    | dsimp only
    | (split <;> try simp_all only [reduceCtorEq])

theorem runAtBoundary_wp {g : Obs α} (hg : PrefixPreserves BoundaryInv BoundarySafe g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜BoundaryInv h w⌝⦄ runAtPrefix index w g
    ⦃post⟨fun out h => ⌜BoundaryInv h out.2⌝, fun _ h => ⌜BoundarySafe h⌝⟩⦄ :=
  runAtPrefix_wp (show PrefixEnsures BoundaryInv BoundarySafe g (fun _ => BoundaryInv) from hg) index w

/-- The initialization and every concrete syscall discharge the state premise;
both WP branches retain safety, including failed prefill and end guards. -/
theorem executeTraceHistory_safe_wp (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceHistory trace placeholders
    ⦃post⟨fun _ h => ⌜BoundarySafe h⌝, fun _ h => ⌜BoundarySafe h⌝⟩⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtBoundary_wp (syscall_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtBoundary_wp (boundaryLift_kernel skipAmbient skipAmbient_sameKernel) index w
  unfold executeTraceHistory executeTraceWith runnerTail
  mvcgen [syscall_spec, ambient_spec]
  all_goals try exact
    ((post⟨fun out h => ⌜BoundaryInv h out.2.1⌝, fun _ h => ⌜BoundarySafe h⌝⟩) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.except (Nat × Stop) (.arg (List Event) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜BoundaryInv h r.2⌝, fun _ h => ⌜BoundarySafe h⌝⟩) :
      Invariant r.2.steps.toList (Array Json)
        (.except (Nat × Stop) (.arg (List Event) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜BoundaryInv h r.2⌝, fun _ h => ⌜BoundarySafe h⌝⟩) :
      Invariant r.2.fired.toList (Array Json)
        (.except (Nat × Stop) (.arg (List Event) .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try (solve | rename_i history hi; exact BoundaryInv.kernel hi rfl)
  all_goals try exact BoundaryInv.safe (by assumption)
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intros; exact BoundaryInv.safe (by assumption))
  all_goals
    rename_i history hh
    subst history
    first
    | exact boundary_initial _ (allocation_initial trace.rlimit trace.net trace.bare trace.foreign
        trace.stepped trace.seccompChild _ rfl)
    | exact boundary_initial _ (audit_initial_prefill trace _ (by assumption)).1
    | exact (boundary_initial _ (allocation_initial trace.rlimit trace.net trace.bare trace.foreign
        trace.stepped trace.seccompChild
        { k := initialKernel trace.rlimit trace.net trace.bare trace.foreign trace.stepped trace.seccompChild,
          env := harnessEnv, timing := Env.timing } rfl)).safe

/-- Safety is unconditional in the original result: Stops preserve their reached
committed history and saved filter-entry validity just as successful JSON does. -/
theorem executeTraceHistory_safe (trace : Trace) (placeholders : Bool) :
    BoundarySafe (runPrefixOuter (executeTraceHistory trace placeholders) []).2 := by
  have hs := (prefixOuter_wp_iff _ _ _ _).mp
    (executeTraceHistory_safe_wp trace placeholders) [] rfl
  cases hr : runPrefixOuter (executeTraceHistory trace placeholders) [] with
  | mk result hist => cases result <;> simpa only [hr] using hs

/-- Exact full-audit correspondence uses the returned World after each indexed
call and the actual prior history, including all reached filter probe payloads. -/
theorem runnerTail_projects (trace : Trace) (w : World) :
    OuterProjects (fun h => AuditInv h w) (runnerTail syscall trace w)
      (runnerTail syscallAudit trace w) := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtAudit_wp (syscallAudit_preserves call) index w
  have ambient_spec (index : Nat) (w : World) :=
    runAtAudit_wp (auditLift_kernel skipAmbient skipAmbient_sameKernel) index w
  unfold runnerTail
  repeat' first
    | contradiction
    | (with_reducible apply outerEnsures_of_wp; mvcgen [syscall_spec, ambient_spec])
    | with_reducible exact outerProjects_pure _
    | with_reducible exact outerProjects_throw _
    | with_reducible apply outerProjects_throw_bind
    | with_reducible apply outerProjects_runAt_bind (syscall_projects _) (syscallAudit_preserves _)
    | with_reducible apply outerProjects_runAt_bind (projectsUnder_lift _ _) (auditLift_kernel skipAmbient skipAmbient_sameKernel)
    | with_reducible apply outerProjects_array_bind (I := fun (acc : World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json) h => AuditInv h acc.1)
    | with_reducible apply outerProjects_array_from (I := fun (acc : World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json) h => AuditInv h acc.1)
    | with_reducible apply outerProjects_array_bind (I := fun (_ : Array Json) h => AuditInv h _)
    | with_reducible apply outerProjects_array_from (I := fun (_ : Array Json) h => AuditInv h _)
    | with_reducible apply outerProjects_map
    | with_reducible apply outerProjects_ite
    | with_reducible intro_forall
    | dsimp only
    | (with_reducible change OuterProjects _ _ _; split <;> try simp_all only [reduceCtorEq])
  all_goals try (solve | intro h hi; exact AuditInv.kernel hi rfl)
  all_goals try (solve | intro h hi; exact hi)
  all_goals try (apply outerEnsures_of_wp; mvcgen [syscall_spec, ambient_spec])
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜AuditInv h r.2⌝, fun _ _ => ⌜True⌝⟩) :
      Invariant r.2.steps.toList (Array Json)
        (.except (Nat × Stop) (.arg (List AuditEvent) .pure)))
  all_goals try
    let r : Unit × World := by assumption
    exact ((post⟨fun _ h => ⌜AuditInv h r.2⌝, fun _ _ => ⌜True⌝⟩) :
      Invariant r.2.fired.toList (Array Json)
        (.except (Nat × Stop) (.arg (List AuditEvent) .pure)))
  all_goals try dsimp +zetaDelta only [outerStepValue] at *
  all_goals try trivial
  all_goals try (solve | intros; assumption)
  all_goals try (solve | rename_i history hi; exact AuditInv.kernel hi rfl)
  all_goals try (solve | intro h hi; exact AuditInv.kernel hi rfl)

/-- Initialize the abstract tail with the source's actual initial/prefilled
Kernel. All flags and defaulted arrays retain the original definitions. -/
theorem executeTraceHistory_projects_under (trace : Trace) (placeholders : Bool) :
    OuterProjects (fun h => h = []) (executeTraceHistory trace placeholders)
      (executeTraceAudit trace placeholders) := by
  rw [executeTraceAudit_eq]
  unfold executeTraceHistory executeTraceWith
  repeat' first
    | contradiction
    | with_reducible exact outerProjects_throw _
    | with_reducible apply outerProjects_throw_bind
    | with_reducible apply outerProjects_pre (runnerTail_projects _ _)
    | with_reducible apply outerProjects_ite
    | with_reducible intro_forall
    | dsimp only
    | (with_reducible change OuterProjects _ _ _; split <;> try simp_all only [reduceCtorEq])
  all_goals
    rename_i history hh
    subst history
    first
    | exact audit_initial (allocation_initial trace.rlimit trace.net trace.bare trace.foreign
        trace.stepped trace.seccompChild _ rfl)
    | exact audit_initial_prefill trace _ (by assumption)

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
      AllocationInv p.history p.world ∧
      (p.world.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.suspended,
        LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have he := congrArg Prod.snd (executeTraceHistory_projects trace placeholders)
  simpa only [he] using executeTraceAudit_trials trace placeholders

end Leanux.Proofs.WG.Queues.RxHistory
