import Leanux.Proofs.WG.RetirementSecurity.HolderDispatchKeys

/-! Filesystem, routing and clock-only dispatch arms preserve key holders
over their actual WG-store projection. These are typed quiet arms, not a
fallback covering unknown traffic or lifecycle behavior. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem keys_product {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) action := HolderScheduled.keys_product_store same

private theorem keys_fs (action : FS.M α) : Preserves (fun w : World=>HolderAccount temporary w.wg) (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ entry=>entry)

private theorem keys_task (action : TaskM α) : Preserves (fun w : World=>HolderAccount temporary w.wg) (liftTask action) :=
  productTask_spec action _ (fun _ _ _ entry=>entry)

private theorem keys_seccomp (action : Seccomp.M α) : Preserves (fun w : World=>HolderAccount temporary w.wg) (liftSeccomp action) :=
  productSeccomp_spec action _ (fun _ _ _ _ entry=>entry)

private theorem keys_routing (action : Net.M α) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) (monadLift action : Leanux.M α) :=
  keys_product (fun initial=>productRouting_spec action (·=initial))

macro "holder_quiet_step" : tactic => `(tactic| first
  | (allocation_release_lift_from FS.M; exact keys_fs _)
  | (allocation_release_lift_from TaskM; exact keys_task _)
  | (allocation_release_lift_from Seccomp.M; exact keys_seccomp _)
  | (allocation_release_lift_from AmbientM; exact ambient _ key_store _)
  | (allocation_release_lift_from Net.M; exact keys_routing _)
  | (rx_retention_head getWG; exact keys_product (fun initial=>productGetWG_spec (·=initial)))
  | (rx_retention_head getRouting
     exact keys_product (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl))
  | (rx_retention_head modifyRouting; exact keys_routing _)
  | (rx_retention_head modifyEnv; apply (hoare_iff_run _ _ _).mpr; intro w result v entry run; cases run; exact entry)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ entry=>entry) (fun _ _ entry=>entry.2))
  | (rx_retention_head modify; apply hoare_modify; intro w entry; exact HolderPoll.keys_store entry rfl)
  | rx_retention_step)

theorem deladdr (family : Nat) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch (.wgDeladdr family)) :=
  rtnetlink _ key_store _ (keys_product (wgDeladdr_sameKernel family))

theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Preserves (fun w : World=>HolderAccount temporary w.wg)
      (dispatch (.wgDelroute family named dst plen oif typeCode metric)) := by
  apply rtnetlink _ key_store
  unfold Env.wgDelroute
  simp (config:={zeta:=false}) only [unsupported]
  repeat' holder_quiet_step

theorem addroute (dst plen oif typeCode metric mtu flags : Nat) :
    Preserves (fun w : World=>HolderAccount temporary w.wg)
      (dispatch (.wgAddroute dst plen oif typeCode metric mtu flags)) := by
  apply rtnetlink _ key_store
  unfold Env.wgAddroute
  simp (config:={zeta:=false}) only [invariant]
  repeat' holder_quiet_step

theorem addaddr (addr plen : Nat) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch (.wgAddaddr addr plen)) := by
  apply rtnetlink _ key_store
  unfold Env.wgAddaddr
  simp (config:={zeta:=false}) only [unsupported]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World=>HolderAccount temporary w.wg)
       intro x b
       change Preserves (fun w : World=>HolderAccount temporary w.wg) _)
    | holder_quiet_step

theorem advance (ticks : Nat) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch (.wgAdvance ticks)) := by
  unfold dispatch
  simp (config:={zeta:=false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance; exact keys_product (advance_sameKernel _))
    | holder_quiet_step

theorem namespace_close : Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch .wgNetnsClose) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  exact HolderPoll.keys_store entry ((ProjectedAction.iff_run _ _ _).mp SyscallFrames.netnsClose_sameWGStore w result v run)

theorem ordinary (call : Syscall) (selected : HolderEntryPollFree.Ordinary call) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch call) := by
  cases call with
  | eventfd2 count flags=>exact keys_fs _
  | dup fd=>exact keys_fs _
  | dup3 oldfd newfd flags=>exact keys_fs _
  | close fd=>exact keys_fs _
  | read fd count=>exact keys_fs _
  | write fd count buf=>exact keys_fs _
  | pipe2 flags=>exact keys_fs _
  | fcntl fd cmd arg=>exact keys_fs _
  | epollCreate1 flags=>exact keys_fs _
  | epollCtl epfd op fd events data=>exact keys_fs _
  | epollWait epfd maxevents timeout=>exact keys_fs _
  | seccompInstall via flags filter len bad mode=>exact keys_seccomp _
  | seccompProbe nr args target strict=>cases target <;> exact keys_seccomp _
  | seccompPrctl cmd args=>exact keys_seccomp _
  | seccompCapdrop=>exact keys_seccomp _
  | seccompQuery cmd action flags=>exact keys_seccomp _
  | _=>exact False.elim selected

end Leanux.Proofs.WG.RetirementSecurity.HolderDispatch
