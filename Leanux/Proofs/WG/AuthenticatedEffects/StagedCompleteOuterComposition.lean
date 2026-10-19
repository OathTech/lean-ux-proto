import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdministrativeSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteExecutionSources
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceCreation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerBoundary
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Exact outer composition has one remaining obligation: destruction must
retain the ledger at reset. The premise is visible, so this module makes no
unconditional initialized-conservation claim. All other callbacks are concrete. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Outer
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver

theorem observe : Checked (observeObserved hooks) :=
  bind_checked Execution.idle (fun _ => DeliverySource.observe_preserves carrier_safe stable _ delivery)

theorem dispatch_observe : Checked (dispatchObserveObserved hooks) := by
  unfold dispatchObserveObserved
  apply bind_checked observe
  rintro ⟨ret,json⟩
  exact bind_checked (ambient _) (fun _ => socket _ _ (pure_checked ret))

theorem dispatch (destructor : StateChecked (destructObserved hooks)) (call : Syscall) :
    Checked (dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact Administrative.retained
  · intro attrs; exact netlink _ (state (config_device attrs))
  · exact rtnetlink _ (wg _ CompleteDeviceCreation.checked)
  · exact rtnetlink _ (env_delete destructor)
  · exact Traffic.syscallXmit
  · intro family port message tos ll dest
    exact socket _ _ (Execution.inject family port message tos ll dest)
  · exact Execution.flood
  · exact Execution.batch
  · exact dispatch_observe

theorem syscall (destructor : StateChecked (destructObserved hooks)) (call : Syscall) :
    Checked (syscallObserved hooks call) :=
  SyscallSource.preserves carrier_safe store_transport call _ _ _ _ _ _ _
    (dispatch destructor call) Execution.sends Execution.idle
    (product_store _ Framing.routeIntoWg0_sameKernel) Execution.after_xmit Execution.advance cleanup

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Outer
