import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductNapiFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollNapi

/-! Actual paired NAPI histories and the native allocation account are joined
on the same execution. Native erasure supplies allocation endpoints only. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership

/-- Actual softirq polling retains the paired packet ledger and native allocation account. -/
theorem softirq : Checked (Driver.softirqObserved hooks) :=
  pair_product (source_product CompletePollNapi.softirq) softirq_erases
    (native_allocated_product napiSoftirqPrefix_erases napiSoftirqPrefix_allocation)

/-- Actual inline polling retains the paired packet ledger and native allocation account. -/
theorem inline_poll : Checked (Driver.inlinePollObserved hooks) :=
  pair_product (source_product CompletePollNapi.inline_poll) inline_erases
    (native_allocated_product pollScheduledInlinePrefix_erases pollScheduledInlinePrefix_allocation)

/-- The original IRQ-exit placement retains paired accounting through its selected NAPI path. -/
theorem irq_exit : Checked (Driver.irqExitObserved hooks) :=
  pair_product (source_product CompletePollNapi.irq_exit) irq_exit_erases
    (native_allocated_product napiIrqExitPrefix_erases napiIrqExitPrefix_allocation)

/-- Each original timer dispatch retains paired accounting and its native allocation certificate. -/
theorem timer (pid : PeerId) (timer : PeerTimer) : StateChecked (Driver.timerObserved hooks pid timer) :=
  pair (source_state (CompletePollConcrete.timer pid timer)) (timer_erases pid timer)
    (AllocatedFrames.observed (TimerCallbackCall.erases (.dispatch pid timer))
      (TimerCallbackCall.allocation (.dispatch pid timer)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
