import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterDispatchAll

/-! The original syscall body retains its real reset, seccomp, dispatch,
return-to-user worker/timer order and final shape observation. The result is
a native normal-state companion, not a claim about an erased event history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

private theorem reset_queued : Preserves Boundary
    (modifyWG (fun g => {g with queuedThisCall:=[]}) : Leanux.M Unit) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases run
  exact hi.wg_store rfl

private theorem routing_read : Preserves Boundary (getRouting : Leanux.M Net.Routing) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases run
  exact hi

private theorem current_read : Preserves Boundary (Leanux.getCurrent : Leanux.M Task) :=
  NativeFrames.fs (StateT.lift TaskM.getCurrent)

theorem syscall (call : Syscall) : Preserves Boundary (Leanux.syscall call) := by
  unfold Leanux.syscall
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Leanux.dispatch; exact dispatch _)
    | (rx_retention_head Env.runSendWorkers; exact Closed.sendAll_boundary)
    | (rx_retention_head Env.idleTimers; exact Closed.idle_boundary)
    | (rx_retention_head Env.routeIntoWg0; exact NativeFrames.route)
    | (rx_retention_head Env.afterXmit; exact Closed.afterXmit_boundary)
    | (rx_retention_head Env.afterAdvance; exact Closed.afterAdvance_boundary)
    | (rx_retention_head Env.netnsCleanup; exact Controls.cleanup_boundary)
    | (rx_retention_head getRouting; exact routing_read)
    | (rx_retention_head Leanux.getCurrent; exact current_read)
    | (rx_retention_head modifyWG; exact reset_queued)
    | (rx_retention_head modifyAmbient; exact NativeFrames.editAmbient _)
    | (rx_retention_head modify
       apply NativeFrames.world
       intro w
       rfl)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id Boundary
       intro _ _
       change Preserves Boundary _)
    | (allocation_release_lift_from FS.M; exact NativeFrames.fs _)
    | (rx_retention_head liftSeccomp; exact NativeFrames.seccomp _)
    | (allocation_release_lift_from Seccomp.M; exact NativeFrames.seccomp _)
    | (allocation_release_lift_from AmbientM; exact NativeFrames.ambient _)
    | rx_retention_step

/-- The carrier witness is selected at the actual native endpoint. Every
normal return code is covered, without an incoming scheduler contract. -/
theorem syscall_normal (call : Syscall) (hi : Inv cs [] h w)
    (run : (Leanux.syscall call).run w=.ok (result,v)) :
    ∃ k next,HolderEntry.Inv next [] k v ∧ ExactBoundary next [] v.wg :=
  (hoare_iff_run _ _ _).mp (syscall call) w result v ⟨h,cs,hi⟩ run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
