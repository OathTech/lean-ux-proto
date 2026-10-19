import Leanux.Proofs.WG.RetirementSecurity.TxWorkDataDispatch

/-! Ordinary filesystem/seccomp operations retain the actual WG store.
Their ambient effects need not be inert: at an idle operation boundary the
queue-only service obligation survives, and any final suspended actors only
add service capacity. No ambient-frame assumption is used. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

abbrev Ordinary := HolderEntryPollFree.Ordinary
abbrev ProductWGStore (w : World) := wgStoreView w.wg

theorem ordinary_fs_store (action : FS.M α) : SameView ProductWGStore (liftFS action) :=
  fun _=>productFS_spec action _ (fun _ _ _ _ before=>before)

theorem ordinary_task_store (action : TaskM α) : SameView ProductWGStore (liftTask action) :=
  fun _=>productTask_spec action _ (fun _ _ _ before=>before)

theorem ordinary_seccomp_store (action : Seccomp.M α) : SameView ProductWGStore (liftSeccomp action) :=
  fun _=>productSeccomp_spec action _ (fun _ _ _ _ before=>before)

theorem ordinary_ambient_store (action : AmbientM α) : SameView ProductWGStore (liftAmbient action) :=
  fun _=>productAmbient_spec action _ (fun _ _ before=>before)

theorem ordinary_dispatch_store (call : Syscall) (selected : Ordinary call) :
    SameView ProductWGStore (dispatch call) := by
  cases call with
  | eventfd2 count flags=>exact ordinary_fs_store _
  | dup fd=>exact ordinary_fs_store _
  | dup3 oldfd newfd flags=>exact ordinary_fs_store _
  | close fd=>exact ordinary_fs_store _
  | read fd count=>exact ordinary_fs_store _
  | write fd count buf=>exact ordinary_fs_store _
  | pipe2 flags=>exact ordinary_fs_store _
  | fcntl fd cmd arg=>exact ordinary_fs_store _
  | epollCreate1 flags=>exact ordinary_fs_store _
  | epollCtl epfd op fd events data=>exact ordinary_fs_store _
  | epollWait epfd maxevents timeout=>exact ordinary_fs_store _
  | seccompInstall via flags filter len bad mode=>exact ordinary_seccomp_store _
  | seccompProbe nr args target strict=>cases target <;> exact ordinary_seccomp_store _
  | seccompPrctl cmd args=>exact ordinary_seccomp_store _
  | seccompCapdrop=>exact ordinary_seccomp_store _
  | seccompQuery cmd action flags=>exact ordinary_seccomp_store _
  | _=>exact False.elim selected

theorem ordinary_choice (condition : Prop) [Decidable condition] (a b : Leanux.M α)
    (left : Preserves P a) (right : Preserves P b) : Preserves P (if condition then a else b) := by
  split <;> assumption

macro "ordinary_store_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head dispatch
     apply (ordinary_dispatch_store _ (by trivial)).wp (·=$initial))
  | (allocation_release_lift_from FS.M; exact (ordinary_fs_store _).wp (·=$initial))
  | (allocation_release_lift_from Seccomp.M; exact (ordinary_seccomp_store _).wp (·=$initial))
  | (allocation_release_lift_from TaskM; exact (ordinary_task_store _).wp (·=$initial))
  | (allocation_release_lift_from AmbientM; exact (ordinary_ambient_store _).wp (·=$initial))
  | (rx_retention_head liftFS; exact (ordinary_fs_store _).wp (·=$initial))
  | (rx_retention_head liftSeccomp; exact (ordinary_seccomp_store _).wp (·=$initial))
  | (rx_retention_head getCurrent
     exact (ordinary_fs_store (StateT.lift TaskM.getCurrent)).wp (·=$initial))
  | (rx_retention_head modifyWG
     apply hoare_modify
     intro w before
     exact before)
  | (rx_retention_head modifyAmbient
     apply hoare_modify
     intro w before
     exact before)
  | (rx_retention_head _root_.modify
     apply hoare_modify
     intro w before
     exact before)
  | (rx_retention_head unsupported
     exact (ordinary_ambient_store (AmbientM.unsupported _)).wp (·=$initial))
  | rxstack_preserves_join
  | (rx_retention_head ite; apply ordinary_choice)
  | env_operation_step
  | rx_retention_step)

theorem ordinary_syscall_store (call : Syscall) (selected : Ordinary call) :
    SameView ProductWGStore (Leanux.syscall call) := by
  intro initial
  change Preserves (fun w=>ProductWGStore w=initial) _
  unfold Leanux.syscall
  cases call <;> simp only [Ordinary,HolderEntryPollFree.Ordinary] at selected
  all_goals try contradiction
  all_goals
    simp (config:={zeta:=false}) only [syscallNr,Syscall.isNet,Env.windowTailCalls,List.forIn_nil,pure_bind]
    repeat' ordinary_store_step initial

theorem serving_without_actors (before : At (Covered locals crypt) crypt [] w)
    (idle : w.ambient.suspended=[]) : Serving locals crypt [] w.wg := by
  simpa only [At,Serving,idle,actors,List.filterMap_nil,List.append_nil] using before

theorem serving_add_suspended (before : Serving locals crypt [] w.wg) : At (Covered locals crypt) crypt [] w := by
  refine ⟨before.1.actor_cover ?_,before.2⟩
  intro pid present
  have queued : pid∈TxWork.queued w.wg := by simpa only [List.append_nil] using present
  exact List.mem_append_left _ queued

theorem ordinary_syscall_actor (call : Syscall) (selected : Ordinary call)
    (before : At (Covered locals crypt) crypt [] w) (idle : w.ambient.suspended=[])
    (run : (Leanux.syscall call).run w=.ok (result,v)) : At (Covered locals crypt) crypt [] v :=
  serving_add_suspended (serving_store_transport
    ((ProjectedAction.iff_run _ _ _).mp (ordinary_syscall_store call selected) w result v run)
    (serving_without_actors before idle))

end Leanux.Proofs.WG.RetirementSecurity.TxWork
