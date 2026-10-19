import Leanux.Proofs.WG.Progress.CommittedTrafficSource
import Leanux.Proofs.WG.Progress.CommittedSyscallBridge
import Leanux.Proofs.WG.Lifetimes.DispatchSource
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation
import Leanux.Proofs.WG.Roaming.RemoteOuterRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration

/- Native lifting is used only for the scheduler-free dispatch slots below.
This is not a scheduler-free assertion about every argument to quiet. Native
flush, NAPI, configuration and cleanup callbacks retain their actual errors. -/
def quiet (call : Syscall) : PrefixM Receipt Int := liftPrefix (Leanux.dispatch call)

def observe : PrefixM Receipt Int := do
  let (ret,result) ← Traffic.observe
  liftPrefix (modifyAmbient fun w => {w with extraOut :=
    (["datagrams","replies","stats"].map (fun k => (k,result.getObjValD k)))})
  socketCallOnWith (fun {_} a => liftPrefix a) LISTEN4_FD (pure ret)

def dispatch (call : Syscall) : PrefixM Receipt Int :=
  dispatchWith quiet (fun attrs => quiet (.wgSet attrs)) (quiet .wgCreate)
    (quiet .wgDelete) (fun family addr bytes opts => quiet (.wgXmit family addr bytes opts))
    (fun family port msg tos ll dest => socketCallOnWith (fun {_} a => liftPrefix a)
      SENDER_FD (Traffic.inject family port msg tos ll dest))
    Traffic.flood Traffic.batch observe call

namespace History

theorem observe_preserves (S : List Receipt → Prop)
    (runs : ∀ origin activation, PrefixPreserves (fun h _=>S h) S (run origin activation)) :
    PrefixPreserves (fun h _ => S h) S observe := by
  apply (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.History.observe_preserves S runs).bind
  rintro ⟨ret,result⟩
  apply ((Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _).bind
  intro _
  exact Roaming.RemoteOuterRules.socket (fun h _=>S h) S (fun _ _ hi=>hi)
    (fun _ => (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _) _ _ (PrefixPreserves.pure (I:=fun h _=>S h) (S:=S) (fun _ _ hi=>hi) ret)

end History

theorem observe_preserves :
    PrefixPreserves (fun h _ => ValidHistory h) ValidHistory observe :=
  History.observe_preserves ValidHistory CommittedRuns.run_preserves

theorem observe_erases : ErasesPrefix observe (Leanux.dispatch .wgObserve) := by
  unfold observe Leanux.dispatch
  apply erasesPrefix_bind Traffic.observe_erases
  rintro ⟨ret,result⟩
  exact erasesPrefix_bind (erasesPrefix_lift _)
    (fun _ => socketCallOnWith_erases _ (erasesPrefix_pure ret))

namespace History

theorem dispatch_preserves (S : List Receipt → Prop)
    (runs : ∀ origin activation, PrefixPreserves (fun h _=>S h) S (run origin activation)) (call : Syscall) :
    PrefixPreserves (fun h _=>S h) S (dispatch call) := by
  apply dispatchWith_preserves
  · intro _ _; exact (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _
  · intro _; exact (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _
  · intro _ _ _ _; exact (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _
  · intro family port msg tos ll dest
    exact Roaming.RemoteOuterRules.socket (fun h _=>S h) S (fun _ _ hi=>hi)
      (fun _ => (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _) _ _ ((Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.History.inject_preserves S runs) family port msg tos ll dest)
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.History.flood_preserves S runs)
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Traffic.History.batch_preserves S runs)
  · exact (Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.History.observe_preserves S runs)

end History

theorem dispatch_preserves (call : Syscall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (dispatch call) :=
  History.dispatch_preserves ValidHistory CommittedRuns.run_preserves call

theorem dispatch_erases (call : Syscall) :
    ErasesPrefix (dispatch call) (Leanux.dispatch call) := by
  cases call
  case wgInject family port msg tos ll dest =>
    exact socketCallOnWith_erases _ (Traffic.inject_erases family port msg tos ll dest)
  case wgFlood count port family messages => exact Traffic.flood_erases count port family messages
  case wgBatch items wait => exact Traffic.batch_erases items
  case wgObserve => exact observe_erases
  all_goals exact erasesPrefix_lift _

def syscall (call : Syscall) : PrefixM Receipt Int :=
  syscallWith (fun {_} a=>liftPrefix a) (dispatch call) Deferred.send Deferred.idle
    (liftPrefix Env.routeIntoWg0) Deferred.afterXmit Deferred.afterAdvance
    (liftPrefix Env.netnsCleanup) call

namespace History

theorem syscall_preserves (S : List Receipt → Prop)
    (runs : ∀ origin activation, PrefixPreserves (fun h _=>S h) S (run origin activation)) (call : Syscall) :
    PrefixPreserves (fun h _=>S h) S (syscall call) :=
  SyscallSource.preserves (I:=fun h _=>S h) (S:=S) (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) call _ _ _ _ _ _ _
    ((Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.History.dispatch_preserves S runs) call) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.History.send_preserves S runs) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.History.idle_preserves S runs)
    ((Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.History.afterXmit_preserves S runs) (Leanux.Proofs.WG.Progress.CommittedRuns.Deferred.History.afterAdvance_preserves S runs)
    ((Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _)

end History

theorem syscall_preserves (call : Syscall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (syscall call) :=
  History.syscall_preserves ValidHistory CommittedRuns.run_preserves call

theorem syscall_erases (call : Syscall) : ErasesPrefix (syscall call) (Leanux.syscall call) := by
  let lower : PrefixM Empty Int := syscallWith (fun {_} a=>liftPrefix a)
    (liftPrefix (Leanux.dispatch call)) (liftPrefix Env.runSendWorkers)
    (liftPrefix Env.idleTimers) (liftPrefix Env.routeIntoWg0)
    (liftPrefix Env.afterXmit) (liftPrefix Env.afterAdvance) (liftPrefix Env.netnsCleanup) call
  apply empty_projects_erases (syscall call) (Configuration.syscallObserved call) lower
  · exact syscallWith_projects _
      (Noise.DriverTags.Initialized.empty_projection _ _ (dispatch_erases call))
      (Noise.DriverTags.Initialized.empty_projection _ _ Deferred.send_erases)
      (Noise.DriverTags.Initialized.empty_projection _ _ Deferred.idle_erases)
      (projectsPrefix_lift _ _)
      (Noise.DriverTags.Initialized.empty_projection _ _ Deferred.afterXmit_erases)
      (Noise.DriverTags.Initialized.empty_projection _ _ Deferred.afterAdvance_erases)
      (projectsPrefix_lift _ _) call
  · rw [syscallObserved_factor]
    exact syscallWith_projects _
      (Noise.DriverTags.Initialized.empty_projection _ _ (dispatchObserved_erases call))
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) (projectsPrefix_lift _ _)
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) call
  · exact syscallObserved_erases call


end Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls
