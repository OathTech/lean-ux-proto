import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.RxWaitAppends

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
open Leanux Leanux.WG Leanux.Proofs.Logged Queues Lifetimes
open RxHistory.SchedulerSource

variable {Attempt : Type}
abbrev Event (Attempt : Type) := Sum RxHistory.Event Attempt
def rxEvent : Event Attempt → Option RxHistory.Event
  | .inl e => some e
  | .inr _ => none
def attempt : Event Attempt → Option Attempt
  | .inl _ => none
  | .inr a => some a
def Safe (valid : List Attempt → Prop) (h : List (Event Attempt)) : Prop :=
  valid (h.filterMap attempt)
def old {α : Type} (g : RxHistory.Obs α) : PrefixM (Event Attempt) α :=
  focusPrefix Sum.inl rxEvent g

theorem old_preserves (valid : List Attempt → Prop) {α : Type} (g : RxHistory.Obs α) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (old g) := by
  intro w h pre
  obtain ⟨suffix,eq⟩ := (Appends.focus Sum.inl rxEvent g) w h
  have kept := focusPrefix_other Sum.inl rxEvent attempt (fun _ => rfl) g w h
  change (runPrefix (old g) w h).2.filterMap attempt = h.filterMap attempt at kept
  have good : Safe valid (runPrefix (old g) w h).2 := by
    unfold Safe
    rw [kept]
    exact pre
  refine ⟨suffix,eq,good,?_⟩
  cases result : (runPrefix (old g) w h).1 with
  | error stop => trivial
  | ok out => exact good

theorem old_appends {α : Type} (g : RxHistory.Obs α) :
    Appends (old (Attempt:=Attempt) g) := Appends.focus _ _ g

theorem old_projects {α : Type} (g : RxHistory.Obs α) (appends : Appends g) :
    ProjectsPrefix (rxEvent (Attempt:=Attempt)) id (old g) g :=
  appends.project_focus Sum.inl rxEvent (fun _ => rfl)

theorem lifted (valid : List Attempt → Prop) {α : Type} (g : Leanux.M α) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (liftPrefix g) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift g
  · exact fun _ _ pre=>pre
  · exact fun _ _ _ _ pre _=>pre

structure Receive (Attempt : Type) (valid : List Attempt → Prop) where
  step : PrefixM (Event Attempt) Bool
  projects : ProjectsPrefix rxEvent id step Origins.HistoryAdapters.receiveStep
  appends : Appends step
  preserves : PrefixPreserves (fun h _ => Safe valid h) (Safe valid) step

variable {valid : List Attempt → Prop}
def receiveIteration (r : Receive Attempt valid) : PrefixM (Event Attempt) IterResult :=
  workerIterPrefix .receiveWorker none r.step (liftPrefix (Env.condResched .receiveWorker))

theorem receiveIteration_preserves (r : Receive Attempt valid) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (receiveIteration r) :=
  workerIterPrefix_preserves _ _ (fun _ _ pre=>pre) r.preserves (lifted valid _)

theorem receiveIteration_projects (r : Receive Attempt valid) :
    ProjectsPrefix rxEvent id (receiveIteration r) Origins.HistoryAdapters.receiveIteration := by
  unfold receiveIteration Origins.HistoryAdapters.receiveIteration workerIterPrefix
  apply projectsPrefix_bind rxEvent id id r.projects
  intro more
  dsimp only [id]
  split
  · exact projectsPrefix_pure _ _ _
  · apply projectsPrefix_bind rxEvent id id (projectsPrefix_lift _ _)
    intro yielded
    exact projectsPrefix_pure _ _ _

theorem receiveIteration_appends (r : Receive Attempt valid) : Appends (receiveIteration r) := by
  unfold receiveIteration workerIterPrefix
  apply r.appends.bind
  intro more
  split
  · exact Appends.pure _
  · exact (Appends.lift _).bind (fun _=>Appends.pure _)

theorem atoms (valid : List Attempt → Prop) :
    AtomContracts (fun h _ => Safe valid h) (Safe valid) (fun {_} g=>old g) :=
  ⟨fun _=>old_preserves valid _,fun _=>old_preserves valid _,
    fun _=>old_preserves valid _,fun _=>old_preserves valid _,
    fun _=>old_preserves valid _,fun _=>old_preserves valid _,
    fun _=>old_preserves valid _,fun _=>old_preserves valid _,old_preserves valid _⟩

def encrypt : PrefixM (Event Attempt) IterResult := old RxHistory.encryptIteration
def decrypt : PrefixM (Event Attempt) IterResult := old RxHistory.decryptIteration
def napi : PrefixM (Event Attempt) Unit := old RxHistory.napiSoftirq
def tx (pid : PeerId) : PrefixM (Event Attempt) IterResult :=
  old (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))))
def ahead (pid : PeerId) : PrefixM (Event Attempt) Unit :=
  cryptAheadWith (fun {_} g=>old g) encrypt pid
def iteration (r : Receive Attempt valid) (a : Activation) : PrefixM (Event Attempt) IterResult :=
  iterationWith (fun {_} g=>old g) encrypt ahead tx decrypt (receiveIteration r) a
def run (r : Receive Attempt valid) (a : Activation) : PrefixM (Event Attempt) Unit :=
  runWith (fun {_} g=>old g) (iteration r) a
def dispatch (r : Receive Attempt valid) (worker : Worker) : PrefixM (Event Attempt) Bool :=
  dispatchWith (fun {_} g=>old g) (run r) worker
def schedule (r : Receive Attempt valid) (stack : Option Worker := none) : PrefixM (Event Attempt) Unit :=
  scheduleWith (fun {_} g=>old g) (dispatch r) (run r) napi stack
def nested (r : Receive Attempt valid) (worker : Worker) : PrefixM (Event Attempt) Unit :=
  nestedWith (fun stack=>schedule r stack) worker

theorem ahead_preserves (valid : List Attempt → Prop) (pid : PeerId) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (ahead pid) :=
  cryptAhead_preserves (I:=fun h _=>Safe valid h) (S:=Safe valid) (fun _ _ pre=>pre) _ (atoms valid) _ (old_preserves valid _) pid
theorem iteration_preserves (r : Receive Attempt valid) (a : Activation) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (iteration r a) :=
  RxHistory.SchedulerSource.iteration_preserves _ (atoms valid) _ _ _ _ _
    (old_preserves valid _) (ahead_preserves valid) (fun _=>old_preserves valid _)
    (old_preserves valid _) (receiveIteration_preserves r) a
theorem run_preserves (r : Receive Attempt valid) (a : Activation) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (run r a) :=
  RxHistory.SchedulerSource.run_preserves (I:=fun h _=>Safe valid h) (S:=Safe valid) (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre)
    _ (atoms valid) _ (iteration_preserves r) a
theorem dispatch_preserves (r : Receive Attempt valid) (worker : Worker) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (dispatch r worker) :=
  RxHistory.SchedulerSource.dispatch_preserves (I:=fun h _=>Safe valid h) (S:=Safe valid) (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre)
    _ (atoms valid) _ (run_preserves r) worker
theorem schedule_preserves (r : Receive Attempt valid) (stack : Option Worker) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (schedule r stack) :=
  RxHistory.SchedulerSource.schedule_preserves (I:=fun h _=>Safe valid h) (S:=Safe valid) (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre)
    _ (atoms valid) _ _ _ (dispatch_preserves r) (run_preserves r) (old_preserves valid _) stack
theorem nested_preserves (r : Receive Attempt valid) (worker : Worker) :
    PrefixPreserves (fun h _ => Safe valid h) (Safe valid) (nested r worker) :=
  RxHistory.SchedulerSource.nested_preserves (I:=fun h _=>Safe valid h) (S:=Safe valid) (fun _ _ pre=>pre) (fun _ _ _ _ pre=>pre)
    _ (schedule_preserves r) worker

theorem encrypt_projects : ProjectsPrefix (rxEvent (Attempt:=Attempt)) id encrypt RxHistory.encryptIteration :=
  old_projects _ (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
theorem decrypt_projects : ProjectsPrefix (rxEvent (Attempt:=Attempt)) id decrypt RxHistory.decryptIteration :=
  old_projects _ (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.decryptIteration_appends)
theorem napi_projects : ProjectsPrefix (rxEvent (Attempt:=Attempt)) id napi RxHistory.napiSoftirq :=
  old_projects _ RxHistory.napiSoftirq_appends
theorem tx_projects (pid : PeerId) : ProjectsPrefix (rxEvent (Attempt:=Attempt)) id (tx pid)
    (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  old_projects _ (Appends.focus _ _ _)
theorem ahead_projects (pid : PeerId) :
    ProjectsPrefix (rxEvent (Attempt:=Attempt)) id (ahead pid) (RxHistory.cryptAhead pid) :=
  RxHistory.SchedulerSource.cryptAhead_projects rxEvent _ (fun {_} g=>g) (fun g ha=>old_projects g ha)
    _ _ encrypt_projects pid
theorem iteration_projects (r : Receive Attempt valid) (a : Activation) :
    ProjectsPrefix rxEvent id (iteration r a) (RxHistory.activationIteration a) :=
  RxHistory.SchedulerSource.iteration_projects rxEvent _ (fun {_} g=>g) (fun g ha=>old_projects g ha)
    _ _ _ _ _ _ _ _ _ _ encrypt_projects ahead_projects tx_projects decrypt_projects
    (receiveIteration_projects r) a
theorem run_projects (r : Receive Attempt valid) (a : Activation) :
    ProjectsPrefix rxEvent id (run r a) (RxHistory.activationRun a) :=
  RxHistory.SchedulerSource.run_projects rxEvent _ (fun {_} g=>g) (fun g ha=>old_projects g ha)
    _ _ (iteration_projects r) a
theorem dispatch_projects (r : Receive Attempt valid) (worker : Worker) :
    ProjectsPrefix rxEvent id (dispatch r worker) (RxHistory.dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_projects rxEvent _ (fun {_} g=>g) (fun g ha=>old_projects g ha)
    _ _ (run_projects r) worker
theorem schedule_projects (r : Receive Attempt valid) (stack : Option Worker) :
    ProjectsPrefix rxEvent id (schedule r stack) (RxHistory.schedule stack) :=
  RxHistory.SchedulerSource.schedule_projects rxEvent _ (fun {_} g=>g) (fun g ha=>old_projects g ha)
    _ _ _ _ _ _ (dispatch_projects r) (run_projects r) napi_projects stack
theorem nested_projects (r : Receive Attempt valid) (worker : Worker) :
    ProjectsPrefix rxEvent id (nested r worker) (RxHistory.nestedResched worker) :=
  RxHistory.SchedulerSource.nested_projects rxEvent _ _ (schedule_projects r) worker

theorem ahead_appends (pid : PeerId) : Appends (ahead (Attempt:=Attempt) pid) :=
  cryptAhead_appends _ (fun g _=>old_appends g) _ (old_appends _) pid
theorem iteration_appends (r : Receive Attempt valid) (a : Activation) : Appends (iteration r a) :=
  RxHistory.SchedulerSource.iteration_appends _ (fun g _=>old_appends g)
    _ _ _ _ _ (old_appends _) ahead_appends (fun _=>old_appends _)
    (old_appends _) (receiveIteration_appends r) a
theorem run_appends (r : Receive Attempt valid) (a : Activation) : Appends (run r a) :=
  RxHistory.SchedulerSource.run_appends _ (fun g _=>old_appends g) _ (iteration_appends r) a
theorem dispatch_appends (r : Receive Attempt valid) (worker : Worker) : Appends (dispatch r worker) :=
  RxHistory.SchedulerSource.dispatch_appends _ (fun g _=>old_appends g) _ (run_appends r) worker
theorem schedule_appends (r : Receive Attempt valid) (stack : Option Worker) : Appends (schedule r stack) :=
  RxHistory.SchedulerSource.schedule_appends _ (fun g _=>old_appends g)
    _ _ _ (dispatch_appends r) (run_appends r) (old_appends _) stack
theorem nested_appends (r : Receive Attempt valid) (worker : Worker) : Appends (nested r worker) :=
  RxHistory.SchedulerSource.nested_appends _ (schedule_appends r) worker

theorem projects_erases {E F α : Type} {ρ : E → Option F} {g : PrefixM E α}
    {old : PrefixM F α} {original : Leanux.M α}
    (project : ProjectsPrefix ρ id g old) (erase : ErasesPrefix old original) :
    ErasesPrefix g original := by
  intro w h
  have same := congrArg Prod.fst (project w h)
  rw [erase w (h.filterMap ρ)] at same
  cases result : (runPrefix g w h).1 <;> simpa [result,Except.map] using same.symm

theorem run_erases (r : Receive Attempt valid) (a : Activation) :
    ErasesPrefix (run r a) (Env.Activation.run a) :=
  projects_erases (run_projects r a) (RxHistory.activationRun_erases a)
theorem dispatch_erases (r : Receive Attempt valid) (worker : Worker) :
    ErasesPrefix (dispatch r worker) (Env.dispatch worker) :=
  projects_erases (dispatch_projects r worker) (RxHistory.dispatch_erases worker)
theorem schedule_erases (r : Receive Attempt valid) (stack : Option Worker) :
    ErasesPrefix (schedule r stack) (Env.schedule stack) :=
  projects_erases (schedule_projects r stack) (RxHistory.schedule_erases stack)
theorem nested_erases (r : Receive Attempt valid) (worker : Worker) :
    ErasesPrefix (nested r worker) (Env.nestedResched worker) :=
  projects_erases (nested_projects r worker) (RxHistory.nestedResched_erases worker)

end Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
