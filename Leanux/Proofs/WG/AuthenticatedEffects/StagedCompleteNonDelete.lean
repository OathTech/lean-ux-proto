import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteOuterComposition

/-! Every non-deletion syscall already carries complete packet accounting.
The original deletion arm remains separate so its stronger native guard entry
cannot be replaced by an unconditional destructor premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Outer
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem dispatch_except_delete (call : Syscall) (different : call≠.wgDelete) :
    Checked (dispatchObserved hooks call) := by
  cases call <;> simp only [dispatchObserved,dispatchWith]
  case wgDelete => exact False.elim (different rfl)
  case wgSet attrs => exact netlink _ (state (config_device attrs))
  case wgCreate => exact rtnetlink _ (wg _ CompleteDeviceCreation.checked)
  case wgXmit family addr payload opts => exact Traffic.syscallXmit family addr payload opts
  case wgInject family port message tos ll dest =>
    exact socket _ _ (Execution.inject family port message tos ll dest)
  case wgFlood count port family messages => exact Execution.flood count port family messages
  case wgBatch items _ => exact Execution.batch items
  case wgObserve => exact dispatch_observe
  all_goals apply Administrative.retained
  all_goals trivial

theorem syscall_except_delete (call : Syscall) (different : call≠.wgDelete) :
    Checked (syscallObserved hooks call) :=
  SyscallSource.preserves carrier_safe store_transport call _ _ _ _ _ _ _
    (dispatch_except_delete call different) Execution.sends Execution.idle
    (product_store _ Framing.routeIntoWg0_sameKernel) Execution.after_xmit Execution.advance cleanup

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Outer
