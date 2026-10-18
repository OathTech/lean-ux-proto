import Leanux.Proofs.WG.Queues.JointNetlink
import Leanux.Proofs.WG.Queues.RxWaitAppends
import Leanux.Proofs.WG.Queues.RxSyscallsHistory

/-! One joint wgSet syscall includes the original entry resets, seccomp guard,
descriptor-scoped dispatch, task work, send-worker wait and timer wait. The
two projections use the unchanged full syscall observers on their incoming
histories, without an initialization or allocation premise. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
universe u

def syscallSetWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (dispatch : m Int)
    (sendWorkers idleTimers : m Unit) : m Int := do
  lift (modify fun w => {w with fs := {w.fs with userOut := none,userFds := none}, seccomp := {w.seccomp with emitted := {},translatedLen := none}})
  lift (modifyWG fun g => {g with queuedThisCall := []})
  lift (modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0})
  if (← lift getCurrent).seccomp.mode != .disabled then
    lift (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatch
  for c in Env.windowTailCalls do lift (liftSeccomp (Seccomp.enterHarnessCall c))
  lift (liftFS taskWorkRun)
  sendWorkers
  idleTimers
  pure ()
  return ret

theorem syscallSet_factor (attrs : DeviceAttrs) :
    Leanux.syscall (.wgSet attrs) = syscallSetWith (fun {_} a => a)
      (Leanux.dispatch (.wgSet attrs)) Env.runSendWorkers Env.idleTimers := rfl

theorem syscallSetObserved_factor (attrs : DeviceAttrs) :
    syscallObserved (.wgSet attrs) = syscallSetWith (fun {_} a => liftPrefix a)
      (dispatchObserved (.wgSet attrs)) (liftPrefix Env.runSendWorkers) (liftPrefix Env.idleTimers) := rfl

theorem syscallSetRx_factor (attrs : DeviceAttrs) :
    Queues.RxHistory.syscall (.wgSet attrs) = syscallSetWith (fun {_} a => liftPrefix a)
      (Queues.RxHistory.syscallDispatch (.wgSet attrs)) Queues.RxHistory.runSendWorkers
      Queues.RxHistory.idleTimers := rfl

theorem syscallSetWith_projects {E F : Type} (ρ : E → Option F)
    {dispatch : PrefixM E Int} {lowerDispatch : PrefixM F Int}
    {sendWorkers idleTimers : PrefixM E Unit} {lowerSend lowerTimers : PrefixM F Unit}
    (hd : ProjectsPrefix ρ id dispatch lowerDispatch)
    (hs : ProjectsPrefix ρ id sendWorkers lowerSend)
    (ht : ProjectsPrefix ρ id idleTimers lowerTimers) :
    ProjectsPrefix ρ id (syscallSetWith (fun {_} a => liftPrefix a) dispatch sendWorkers idleTimers)
      (syscallSetWith (fun {_} a => liftPrefix a) lowerDispatch lowerSend lowerTimers) := by
  have tail : ProjectsPrefix ρ id (do
      let ret ← dispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      sendWorkers
      idleTimers
      return ret) (do
      let ret ← lowerDispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      lowerSend
      lowerTimers
      return ret) := by
    apply projectsPrefix_bind ρ id id hd
    intro ret
    apply projectsPrefix_bind ρ id id
    · apply projectsPrefix_forIn ρ id
      intro c acc
      exact projectsPrefix_bind ρ id (projectStep id) (projectsPrefix_lift ρ _)
        (fun _ => projectsPrefix_pure ρ (projectStep id) _)
    · intro _
      apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
      intro _
      apply projectsPrefix_bind ρ id id hs
      intro _
      apply projectsPrefix_bind ρ id id ht
      intro _
      exact projectsPrefix_pure ρ id ret
  unfold syscallSetWith
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro current
  dsimp only [id]
  apply projectsPrefix_ite ρ _ id
  · intro _
    exact projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _) (fun _ => tail)
  · intro _
    exact tail

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration

/-- RX callbacks keep all of their event constructors and every prior RX
entry. Only the other sum branch is outside this focused journal. -/
def rxAction (a : RxHistory.Obs α) : PrefixM Event α := focusPrefix Event.rx rxEvent a

theorem rxAction_rx {a : RxHistory.Obs α} (ha : Appends a) :
    ProjectsPrefix rxEvent id (rxAction a) a := ha.project_focus Event.rx rxEvent (fun _ => rfl)

theorem rxAction_routing {a : RxHistory.Obs α} {source : Leanux.M α}
    (ha : ErasesPrefix a source) :
    ProjectsPrefix routingEvent id (rxAction a) (liftPrefix source) :=
  (show HistoryFrame routingEvent (rxAction a) from
    focusPrefix_other Event.rx rxEvent routingEvent (fun _ => rfl) a).project
    (focusPrefix_erases Event.rx rxEvent ha)

def syscallSet (attrs : DeviceAttrs) : PrefixM Event Int :=
  syscallSetWith (fun {_} a => liftPrefix a) (dispatchSet attrs)
    (rxAction RxHistory.runSendWorkers) (rxAction RxHistory.idleTimers)

theorem syscallSet_routing (attrs : DeviceAttrs) :
    ProjectsPrefix routingEvent id (syscallSet attrs) (syscallObserved (.wgSet attrs)) := by
  rw [syscallSetObserved_factor]
  exact syscallSetWith_projects routingEvent (dispatchSet_routing attrs)
    (rxAction_routing RxHistory.runSendWorkers_erases) (rxAction_routing RxHistory.idleTimers_erases)

theorem syscallSet_rx (attrs : DeviceAttrs) :
    ProjectsPrefix rxEvent id (syscallSet attrs) (RxHistory.syscall (.wgSet attrs)) := by
  rw [syscallSetRx_factor]
  exact syscallSetWith_projects rxEvent (dispatchSet_rx attrs)
    (rxAction_rx RxHistory.runSendWorkers_appends) (rxAction_rx RxHistory.idleTimers_appends)

/-- Erasure comes from the projection of this same execution. No independent
execution is used to align an intermediate state or journal position. -/
theorem syscallSet_erases (attrs : DeviceAttrs) :
    ErasesPrefix (syscallSet attrs) (Leanux.syscall (.wgSet attrs)) := by
  intro w h
  have hp := congrArg Prod.fst (syscallSet_rx attrs w h)
  have he := RxHistory.syscall_erases (.wgSet attrs) w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix (syscallSet attrs) w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix (syscallSet attrs) w h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
