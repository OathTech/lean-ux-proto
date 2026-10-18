import Leanux.Proofs.WG.TransmitSecurity.NonceDispatch

/-! Native syscall entry, dispatch and designated post-workers share one
persistent nonce-allocation journal, including the exact stopped prefix. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration

def syscallObserved (call : Syscall) : PrefixM Allocation Int :=
  syscallWith (fun {_} a => liftPrefix a) (dispatchObserved call)
    sendWorkersObserved idleTimersObserved (liftPrefix Env.routeIntoWg0)
    afterXmitObserved afterAdvanceObserved (liftPrefix Env.netnsCleanup) call

theorem syscallObserved_safe (call : Syscall) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (syscallObserved call) :=
  SyscallSource.preserves (fun _ _ hi => hi.nodup) Frames.wg_store call _ _ _ _ _ _ _
    (dispatchObserved_safe call) sendWorkersObserved_safe idleTimersObserved_safe
    (Frames.stored routeIntoWg0_sameKernel) afterXmitObserved_safe afterAdvanceObserved_safe
    (Frames.product_lift Frames.env_cleanup)

theorem syscallObserved_erases (call : Syscall) :
    ErasesPrefix (syscallObserved call) (Leanux.syscall call) := by
  rw [syscall_factor]
  unfold syscallObserved syscallWith
  repeat' first
    | (maintenance_head dispatchObserved; exact dispatchObserved_erases _)
    | (maintenance_head afterXmitObserved; exact afterXmitObserved_erases)
    | (maintenance_head afterAdvanceObserved; exact afterAdvanceObserved_erases)
    | (maintenance_head idleTimersObserved; exact idleTimersObserved_erases)
    | nonce_traffic_erasure

end Leanux.Proofs.WG.TransmitSecurity.Nonce
