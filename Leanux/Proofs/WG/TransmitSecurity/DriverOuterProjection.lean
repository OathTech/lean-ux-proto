import Leanux.Proofs.WG.TransmitSecurity.DriverTrafficProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverConfigurationProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverLifecycleProjection

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem retained_projects (h : HooksProjects ρ g a) (call : Syscall) :
    ProjectsPrefix ρ id (retainedObserved g call) (retainedObserved a call) := by
  cases call <;> unfold retainedObserved
  case wgUp => exact socketCallOnWith_projects ρ _ (envUp_projects h)
  case wgDown => exact socketCallOnWith_projects ρ _ (envDown_projects h)
  all_goals exact projectsPrefix_lift ρ _

theorem observe_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (observeObserved g) (observeObserved a) :=
  projectsPrefix_bind ρ id id (idleTimers_projects h) (fun _ => projectsPrefix_lift ρ _)

theorem dispatchObserve_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (dispatchObserveObserved g) (dispatchObserveObserved a) := by
  unfold dispatchObserveObserved
  apply projectsPrefix_bind ρ id id (observe_projects h)
  rintro ⟨ret, json⟩
  dsimp only
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  exact socketCallOnWith_projects ρ _ (projectsPrefix_pure ρ id ret)

theorem dispatchSet_projects (h : HooksProjects ρ g a) (attrs : DeviceAttrs) :
    ProjectsPrefix ρ id (dispatchSetObserved g attrs) (dispatchSetObserved a attrs) :=
  netlinkRequestWith_projects ρ ((configDevice_projects h attrs).liftWGObserver ρ id)

theorem dispatchCreate_projects (ρ : E → Option F) :
    ProjectsPrefix ρ id dispatchCreateObserved dispatchCreateObserved :=
  rtnetlinkRequestWith_projects ρ (projectsPrefix_lift ρ _)

theorem dispatchDelete_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (dispatchDeleteObserved g) (dispatchDeleteObserved a) :=
  rtnetlinkRequestWith_projects ρ (envDelete_projects h)

theorem dispatch_projects (h : HooksProjects ρ g a) (call : Syscall) :
    ProjectsPrefix ρ id (dispatchObserved g call) (dispatchObserved a call) := by
  apply dispatchWith_projects _ _ _ _ _ _ _ _ _ ρ
  · exact fun call _ => retained_projects h call
  · exact dispatchSet_projects h
  · exact dispatchCreate_projects ρ
  · exact dispatchDelete_projects h
  · exact syscallXmit_projects h
  · intro family port message tos ll dest
    exact socketCallOnWith_projects ρ _ (inject_projects h family port message tos ll dest)
  · exact flood_projects h
  · exact batch_projects h
  · exact dispatchObserve_projects h

theorem syscall_projects (h : HooksProjects ρ g a) (call : Syscall) :
    ProjectsPrefix ρ id (syscallObserved g call) (syscallObserved a call) :=
  syscallWith_projects ρ (dispatch_projects h call) (sendWorkers_projects h)
    (idleTimers_projects h) (projectsPrefix_lift ρ _) (afterXmit_projects h)
    (afterAdvance_projects h) (projectsPrefix_lift ρ _) call

macro "driver_outer_step " rho:ident : tactic => `(tactic| first
  | (maintenance_head Pure.pure; exact projectsOuter_pure $rho id _)
  | (maintenance_head throw; exact projectsOuter_throw $rho id _)
  | (maintenance_head Bind.bind; apply projectsOuter_bind $rho id id)
  | (maintenance_head ForIn.forIn; first | apply projectsOuter_array $rho | apply projectsOuter_forIn $rho)
  | (maintenance_head ite; apply projectsOuter_ite $rho _ id)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem runnerTail_projects (h : HooksProjects ρ g a) (trace : Runner.Trace) (w : World) :
    ProjectsOuter ρ id (RxHistory.runnerTail (syscallObserved g) trace w)
      (RxHistory.runnerTail (syscallObserved a) trace w) := by
  unfold RxHistory.runnerTail
  repeat' first
    | (maintenance_head runAtPrefix
       apply projectsOuter_runAt_id ρ
       first | exact syscall_projects h _ | exact projectsPrefix_lift ρ _)
    | driver_outer_step ρ

theorem execute_projects (h : HooksProjects ρ g a) (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter ρ id (executeObserved g trace placeholders) (executeObserved a trace placeholders) := by
  unfold executeObserved RxHistory.executeTraceWith
  repeat' first
    | (maintenance_head RxHistory.runnerTail; exact runnerTail_projects h _ _)
    | driver_outer_step ρ

end Leanux.Proofs.WG.TransmitSecurity.Driver
