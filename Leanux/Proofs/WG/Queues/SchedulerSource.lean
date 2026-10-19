import Leanux.Proofs.WG.Queues.RxEnvWorkersHistory
import Leanux.Proofs.WG.Queues.PollSource

/-! Shared bodies of the actual RX-history scheduler. Existing access and
probe atoms keep their observed execution; committed workers and NAPI are
explicit product callbacks. The consistency probe still executes the original
copied-World trials, never these replacement committed callbacks. -/
namespace Leanux.Proofs.WG.Queues.RxHistory.SchedulerSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def cryptAheadWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (encrypt : PrefixM E IterResult) (pid : PeerId) : PrefixM E Unit := do
  if (← old (mixed (liftPrefix getAmbient))).hidden.isNone then return
  let some item := (← old (mixed (liftWGObserver (getPeerMixed pid)))).txQueue.all.head? | return
  let some id := item.head? | old (mixed (liftPrefix (invariant "an empty ring item")))
  if (← old (mixed (liftWGObserver (getTxSkbPrefix id)))).state != .uncrypted then return
  let next ← old (mixed (liftPrefix peekHiddenSite))
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let w ← old (mixed (liftPrefix getAmbient))
  let some enc := w.suspended.find? (·.worker == .encryptWorker)
    | old (mixed (throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)")))
  old (mixed (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))))
  let r ← encrypt
  old (mixed (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))))
  match r with
  | .continued =>
    old (mixed (liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x})))
  | .ended => old (mixed (throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)")))
  | .yielded => old (mixed (liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched")))

def iterationWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (encrypt : PrefixM E IterResult) (ahead : PeerId → PrefixM E Unit)
    (tx : PeerId → PrefixM E IterResult) (decrypt receive : PrefixM E IterResult)
    (a : Activation) : PrefixM E IterResult := do
  match a.worker with
  | .encryptWorker => encrypt
  | .txWorker =>
    let some pid := a.pid | old (mixed (liftPrefix (invariant "a tx activation without its peer")))
    ahead pid
    tx pid
  | .decryptWorker => decrypt
  | .receiveWorker => receive
  | w => old (mixed (liftPrefix (invariant s!"{w.symbol} is not a draining worker")))

def runWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (iteration : Activation → PrefixM E IterResult) (a : Activation) : PrefixM E Unit := do
  let occupancy ← old (mixed (activationOccupancyPrefix a))
  let refills ← old (mixed activationRefillsPrefix)
  let mut act := a
  for _ in [0:occupancy + refills + 1] do
    match ← iteration act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) plus the refills its run could take ({refills})")

def dispatchWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (run : Activation → PrefixM E Unit) (worker : Worker) : PrefixM E Bool := do
  let d ← liftPrefix (liftWG getDev)
  let mut pid : Option Nat := none
  match worker with
  | .encryptWorker => if !(← liftPrefix (Env.pendingDevice worker !d.encryptQueue.empty)) then return false
  | .decryptWorker => if !(← liftPrefix (Env.pendingDevice worker !d.decryptQueue.empty)) then return false
  | .receiveWorker => if !(← liftPrefix (Env.pendingDevice worker !d.handshakeQueue.empty)) then return false
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return false
    let p ← match ← liftPrefix (peekUnit .txWorker) with
      | some u => liftPrefix (resolveUnit .txWorker u d.txWorkQueue)
      | none => pure headPid
    old (mixed (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase p}))))
    pid := some p
  | _ => return false
  _ ← liftPrefix (hidden (.sectionStart worker))
  run {worker, pid}
  return true

def scheduleWith {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (dispatch : Worker → PrefixM E Bool) (run : Activation → PrefixM E Unit)
    (napi : PrefixM E Unit) (stack : Option Worker := none) : PrefixM E Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix getAmbient).hidden.isNone then
      let d ← liftPrefix (liftWG getDev)
      let pending := (← liftPrefix getAmbient).pendingWork
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty || pending.contains w.index
        | .decryptWorker => !d.decryptQueue.empty || pending.contains w.index
        | .encryptWorker => !d.encryptQueue.empty || pending.contains w.index
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← dispatch w) then liftPrefix (invariant s!"{w.symbol} has work but was not dispatched")
      continue
    let next ← liftPrefix peekHiddenSite
    if let some (w, true) := next.bind Env.sectionOf then
      if ← dispatch w then continue else return
    if ← old (mixed (pendingNapiPrefix next)) then
      napi
      if (← liftPrefix peekHiddenSite) == some netRx then return
      continue
    match ← old (audit consistentFilterAudit) with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← old (mixed (activationHasWorkPrefix {worker := w})) then
          liftPrefix (unsupported "the records do not determine which suspended worker resumed")
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.filter (· != a)})
      run a
    | _ => liftPrefix (unsupported "the records do not determine which suspended worker resumed")
  liftPrefix (budgetExhausted "the scheduler loop")

def nestedWith {E : Type} (schedule : Option Worker → PrefixM E Unit)
    (self : Worker) : PrefixM E Unit := do
  if ← liftPrefix (Env.condResched self) then schedule (some self)


/-- Each old specialization is definitionally the unchanged observed body. -/
theorem cryptAhead_factor (pid : PeerId) :
    cryptAhead pid = cryptAheadWith (fun {_} a => a) encryptIteration pid := rfl

theorem iteration_factor (a : Activation) :
    activationIteration a = iterationWith (fun {_} a => a) encryptIteration cryptAhead
      (fun pid => mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))))
      decryptIteration Origins.HistoryAdapters.receiveIteration a := rfl

theorem run_factor (a : Activation) :
    activationRun a = runWith (fun {_} a => a) activationIteration a := rfl

theorem dispatch_factor (worker : Worker) :
    RxHistory.dispatch worker = dispatchWith (fun {_} a => a) activationRun worker := rfl

theorem schedule_factor (stack : Option Worker) :
    schedule stack = scheduleWith (fun {_} a => a) RxHistory.dispatch activationRun napiSoftirq stack := rfl

theorem nested_factor (worker : Worker) :
    nestedResched worker = nestedWith (fun stack => schedule stack) worker := rfl

/-- These proof steps reuse the checked action-head guard from PollSource.
Each branch applies an ordinary projection or append rule. -/
macro "scheduler_project_step" : tactic => `(tactic| first
  | (poll_source_head mixed; exact Appends.focus _ _ _)
  | (poll_source_head audit; exact Appends.focus _ _ _)
  | (poll_source_head liftPrefix; first | exact projectsPrefix_lift _ _ | exact Appends.lift _)
  | (poll_source_head Pure.pure; first
      | exact projectsPrefix_pure _ id _
      | exact projectsPrefix_pure _ (projectStep id) _)
  | (poll_source_head ForIn.forIn; first | apply projectsPrefix_range _ id | apply projectsPrefix_forIn _ id)
  | (poll_source_head Bind.bind; first
      | apply projectsPrefix_bind _ id id
      | apply projectsPrefix_bind _ id (projectStep id))
  | (poll_source_head ite; apply projectsPrefix_ite)
  | maintenance_intro
  | dsimp only [id]
  | split)

section
variable {E F : Type} (ρ : E → Option F)
    (old : {α : Type} → Obs α → PrefixM E α)
    (old' : {α : Type} → Obs α → PrefixM F α)
    (ho : ∀ {α : Type} (a : Obs α), Appends a → ProjectsPrefix ρ id (old a) (old' a))

include ho

/-- The committed repair iteration is parameterized; its surrounding accesses
and saved activation update are the original observed atoms. -/
theorem cryptAhead_projects (encrypt : PrefixM E IterResult) (encrypt' : PrefixM F IterResult)
    (he : ProjectsPrefix ρ id encrypt encrypt') (pid : PeerId) :
    ProjectsPrefix ρ id (cryptAheadWith old encrypt pid) (cryptAheadWith old' encrypt' pid) := by
  unfold cryptAheadWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head encrypt; exact he)
    | scheduler_project_step

theorem iteration_projects (encrypt : PrefixM E IterResult) (encrypt' : PrefixM F IterResult)
    (ahead : PeerId → PrefixM E Unit) (ahead' : PeerId → PrefixM F Unit)
    (tx : PeerId → PrefixM E IterResult) (tx' : PeerId → PrefixM F IterResult)
    (decrypt receive : PrefixM E IterResult) (decrypt' receive' : PrefixM F IterResult)
    (he : ProjectsPrefix ρ id encrypt encrypt')
    (ha : ∀ pid, ProjectsPrefix ρ id (ahead pid) (ahead' pid))
    (ht : ∀ pid, ProjectsPrefix ρ id (tx pid) (tx' pid))
    (hd : ProjectsPrefix ρ id decrypt decrypt') (hr : ProjectsPrefix ρ id receive receive')
    (a : Activation) :
    ProjectsPrefix ρ id (iterationWith old encrypt ahead tx decrypt receive a)
      (iterationWith old' encrypt' ahead' tx' decrypt' receive' a) := by
  unfold iterationWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head encrypt; exact he)
    | (poll_source_head ahead; exact ha _)
    | (poll_source_head tx; exact ht _)
    | (poll_source_head decrypt; exact hd)
    | (poll_source_head receive; exact hr)
    | scheduler_project_step

theorem run_projects (iteration : Activation → PrefixM E IterResult)
    (iteration' : Activation → PrefixM F IterResult)
    (hi : ∀ a, ProjectsPrefix ρ id (iteration a) (iteration' a)) (a : Activation) :
    ProjectsPrefix ρ id (runWith old iteration a) (runWith old' iteration' a) := by
  unfold runWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head iteration; exact hi _)
    | scheduler_project_step

theorem dispatch_projects (run : Activation → PrefixM E Unit) (run' : Activation → PrefixM F Unit)
    (hr : ∀ a, ProjectsPrefix ρ id (run a) (run' a)) (worker : Worker) :
    ProjectsPrefix ρ id (dispatchWith old run worker) (dispatchWith old' run' worker) := by
  unfold dispatchWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head run; exact hr _)
    | scheduler_project_step

/-- The probe remains the actual consistentFilterAudit atom, so its copied
trials, marker position and non-hidden Stops are included in this projection. -/
theorem schedule_projects (dispatch : Worker → PrefixM E Bool) (dispatch' : Worker → PrefixM F Bool)
    (run : Activation → PrefixM E Unit) (run' : Activation → PrefixM F Unit)
    (napi : PrefixM E Unit) (napi' : PrefixM F Unit)
    (hd : ∀ worker, ProjectsPrefix ρ id (dispatch worker) (dispatch' worker))
    (hr : ∀ a, ProjectsPrefix ρ id (run a) (run' a)) (hn : ProjectsPrefix ρ id napi napi')
    (stack : Option Worker) :
    ProjectsPrefix ρ id (scheduleWith old dispatch run napi stack)
      (scheduleWith old' dispatch' run' napi' stack) := by
  unfold scheduleWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head dispatch; exact hd _)
    | (poll_source_head run; exact hr _)
    | (poll_source_head napi; exact hn)
    | scheduler_project_step

end

theorem nested_projects {E F : Type} (ρ : E → Option F)
    (schedule : Option Worker → PrefixM E Unit) (schedule' : Option Worker → PrefixM F Unit)
    (hs : ∀ stack, ProjectsPrefix ρ id (schedule stack) (schedule' stack)) (worker : Worker) :
    ProjectsPrefix ρ id (nestedWith schedule worker) (nestedWith schedule' worker) := by
  unfold nestedWith
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro ready
  dsimp only [id]
  apply projectsPrefix_ite
  · intro _; exact hs _
  · intro _; exact projectsPrefix_pure ρ id _

/-- Append proofs inspect the same literal bodies as the projection laws. -/
macro "scheduler_append_step" : tactic => `(tactic| first
  | (poll_source_head mixed; exact Appends.focus _ _ _)
  | (poll_source_head audit; exact Appends.focus _ _ _)
  | (poll_source_head liftPrefix; exact Appends.lift _)
  | (poll_source_head Pure.pure; exact Appends.pure _)
  | (poll_source_head ForIn.forIn; first | apply Appends.range | apply Appends.forIn)
  | (poll_source_head Bind.bind; apply Appends.bind)
  | maintenance_intro
  | dsimp only
  | split)

section
variable {E : Type} (old : {α : Type} → Obs α → PrefixM E α)
    (ho : ∀ {α : Type} (a : Obs α), Appends a → Appends (old a))
include ho

theorem cryptAhead_appends (encrypt : PrefixM E IterResult)
    (he : Appends encrypt) (pid : PeerId) : Appends (cryptAheadWith old encrypt pid) := by
  unfold cryptAheadWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head encrypt; exact he)
    | scheduler_append_step

theorem iteration_appends (encrypt : PrefixM E IterResult) (ahead : PeerId → PrefixM E Unit)
    (tx : PeerId → PrefixM E IterResult) (decrypt receive : PrefixM E IterResult)
    (he : Appends encrypt) (ha : ∀ pid, Appends (ahead pid)) (ht : ∀ pid, Appends (tx pid))
    (hd : Appends decrypt) (hr : Appends receive) (a : Activation) :
    Appends (iterationWith old encrypt ahead tx decrypt receive a) := by
  unfold iterationWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head encrypt; exact he)
    | (poll_source_head ahead; exact ha _)
    | (poll_source_head tx; exact ht _)
    | (poll_source_head decrypt; exact hd)
    | (poll_source_head receive; exact hr)
    | scheduler_append_step

theorem run_appends (iteration : Activation → PrefixM E IterResult)
    (hi : ∀ a, Appends (iteration a)) (a : Activation) : Appends (runWith old iteration a) := by
  unfold runWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head iteration; exact hi _)
    | scheduler_append_step

theorem dispatch_appends (run : Activation → PrefixM E Unit)
    (hr : ∀ a, Appends (run a)) (worker : Worker) : Appends (dispatchWith old run worker) := by
  unfold dispatchWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head run; exact hr _)
    | scheduler_append_step

theorem schedule_appends (dispatch : Worker → PrefixM E Bool)
    (run : Activation → PrefixM E Unit) (napi : PrefixM E Unit)
    (hd : ∀ worker, Appends (dispatch worker)) (hr : ∀ a, Appends (run a))
    (hn : Appends napi) (stack : Option Worker) : Appends (scheduleWith old dispatch run napi stack) := by
  unfold scheduleWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head dispatch; exact hd _)
    | (poll_source_head run; exact hr _)
    | (poll_source_head napi; exact hn)
    | scheduler_append_step

end

theorem nested_appends {E : Type} (schedule : Option Worker → PrefixM E Unit)
    (hs : ∀ stack, Appends (schedule stack)) (worker : Worker) : Appends (nestedWith schedule worker) := by
  unfold nestedWith
  repeat' first
    | (poll_source_head schedule; exact hs _)
    | scheduler_append_step

end Leanux.Proofs.WG.Queues.RxHistory.SchedulerSource
