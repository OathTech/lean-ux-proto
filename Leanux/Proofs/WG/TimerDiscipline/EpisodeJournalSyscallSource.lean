import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalDeferredSource
import Leanux.Proofs.WG.Progress.CommittedSyscallSource

/-! Original syscall composition with its actual idle, advance and observation timer callers. All other original dispatch slots retain their exact execution. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open Configuration

def observe : PrefixM Receipt Int := do
  let (ret,result) ← do
    idle
    liftPrefix Environment.observeTail
  liftPrefix (modifyAmbient fun w => {w with extraOut :=
    (["datagrams","replies","stats"].map (fun k => (k,result.getObjValD k)))})
  socketCallOnWith (fun {_} a=>liftPrefix a) LISTEN4_FD (pure ret)

def quiet (c : Syscall) : PrefixM Receipt Int := liftPrefix (Leanux.dispatch c)

def dispatch (c : Syscall) : PrefixM Receipt Int :=
  dispatchWith quiet (fun attrs=>quiet (.wgSet attrs)) (quiet .wgCreate)
    (quiet .wgDelete) (fun family addr bytes opts=>quiet (.wgXmit family addr bytes opts))
    (fun family port msg tos ll dest=>quiet (.wgInject family port msg tos ll dest))
    (fun count port family msgs=>quiet (.wgFlood count port family msgs))
    (fun items=>quiet (.wgBatch items 0)) observe c

theorem observe_preserves :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory observe := by
  unfold observe
  apply idle_preserves.bind
  intro _
  apply (lift_preserves _).bind
  rintro ⟨ret,result⟩
  apply (lift_preserves _).bind
  intro _
  exact Roaming.RemoteOuterRules.socket (fun h _=>ValidHistory h) ValidHistory
    (fun _ _ hi=>hi) (fun _=>lift_preserves _) _ _
    (PrefixPreserves.pure (I:=fun h _=>ValidHistory h) (S:=ValidHistory)
      (fun _ _ hi=>hi) ret)

theorem observe_erases : ErasesPrefix observe (Leanux.dispatch .wgObserve) := by
  unfold observe Leanux.dispatch
  rw [Environment.observe_eq]
  simp only [bind_assoc]
  apply erasesPrefix_bind idle_erases
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift _)
  rintro ⟨ret,result⟩
  exact erasesPrefix_bind (erasesPrefix_lift _)
    (fun _=>socketCallOnWith_erases _ (erasesPrefix_pure ret))

theorem dispatch_preserves (c : Syscall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (dispatch c) := by
  apply dispatchWith_preserves
  · intro _ _; exact lift_preserves _
  · intro _; exact lift_preserves _
  · exact lift_preserves _
  · exact lift_preserves _
  · intro _ _ _ _; exact lift_preserves _
  · intro _ _ _ _ _ _; exact lift_preserves _
  · intro _ _ _ _; exact lift_preserves _
  · intro _; exact lift_preserves _
  · exact observe_preserves

theorem dispatch_erases (c : Syscall) : ErasesPrefix (dispatch c) (Leanux.dispatch c) := by
  cases c
  case wgObserve => exact observe_erases
  all_goals exact erasesPrefix_lift _

def syscall (c : Syscall) : PrefixM Receipt Int :=
  syscallWith (fun {_} a=>liftPrefix a) (dispatch c)
    (liftPrefix Env.runSendWorkers) idle (liftPrefix Env.routeIntoWg0)
    (liftPrefix Env.afterXmit) afterAdvance (liftPrefix Env.netnsCleanup) c

theorem syscall_preserves (c : Syscall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (syscall c) :=
  SyscallSource.preserves (I:=fun h _=>ValidHistory h) (S:=ValidHistory)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) c _ _ _ _ _ _ _
    (dispatch_preserves c) (lift_preserves _) idle_preserves
    (lift_preserves _) (lift_preserves _) afterAdvance_preserves (lift_preserves _)

theorem syscall_erases (c : Syscall) : ErasesPrefix (syscall c) (Leanux.syscall c) := by
  let lower : PrefixM Empty Int := syscallWith (fun {_} a=>liftPrefix a)
    (liftPrefix (Leanux.dispatch c)) (liftPrefix Env.runSendWorkers)
    (liftPrefix Env.idleTimers) (liftPrefix Env.routeIntoWg0)
    (liftPrefix Env.afterXmit) (liftPrefix Env.afterAdvance) (liftPrefix Env.netnsCleanup) c
  apply Progress.CommittedRuns.Syscalls.empty_projects_erases
    (syscall c) (Configuration.syscallObserved c) lower
  · exact syscallWith_projects _
      (Noise.DriverTags.Initialized.empty_projection _ _ (dispatch_erases c))
      (projectsPrefix_lift _ _)
      (Noise.DriverTags.Initialized.empty_projection _ _ idle_erases)
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _)
      (Noise.DriverTags.Initialized.empty_projection _ _ afterAdvance_erases)
      (projectsPrefix_lift _ _) c
  · rw [Configuration.syscallObserved_factor]
    exact syscallWith_projects _
      (Noise.DriverTags.Initialized.empty_projection _ _ (Configuration.dispatchObserved_erases c))
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) (projectsPrefix_lift _ _)
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) c
  · exact Configuration.syscallObserved_erases c

end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
