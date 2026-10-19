import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdministrativeSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixExecutionSources
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Every non-deletion syscall retains all logical prefixes beside complete
packet accounting.
The original deletion arm remains separate so its stronger native guard entry
cannot be replaced by an unconditional destructor premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Outer
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem observe : Checked (observeObserved hooks) :=
  bind_checked Execution.idle (fun _=>DeliverySource.observe_preserves carrier_safe stable _ delivery)

theorem dispatch_observe : Checked (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply bind_checked observe
  rintro ⟨ret,json⟩
  exact bind_checked (ambient _) (fun _=>socket _ _ (pure_checked ret))

theorem dispatch_except_delete (call : Syscall) (different : call≠.wgDelete) :
    Checked (dispatchObserved hooks call) := by
  cases call <;> simp only [dispatchObserved,dispatchWith]
  case wgDelete => exact False.elim (different rfl)
  case wgSet attrs => exact netlink _ (state (ConfigurationConcrete.device attrs))
  case wgCreate => exact rtnetlink _ (wg _ created)
  case wgXmit family addr payload opts => exact Traffic.syscallXmit transmit family addr payload opts
  case wgInject family port message tos ll dest =>
    exact socket _ _ (Execution.inject family port message tos ll dest)
  case wgFlood count port family messages => exact Execution.flood count port family messages
  case wgBatch items _ => exact Execution.batch items
  case wgObserve => exact dispatch_observe
  all_goals apply Administrative.retained env_up env_down
  all_goals trivial

theorem syscall_except_delete (call : Syscall) (different : call≠.wgDelete) :
    Checked (syscallObserved hooks call) :=
  SyscallSource.preserves carrier_safe store_transport call _ _ _ _ _ _ _
    (dispatch_except_delete call different) Execution.sends Execution.idle
    (product_store _ Framing.routeIntoWg0_sameKernel) Execution.after_xmit Execution.advance cleanup

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Outer
