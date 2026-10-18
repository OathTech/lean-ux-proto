import Leanux.Proofs.WG.Noise.PendingPollSource
import Leanux.Proofs.WG.Noise.PendingStackSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Logged Queues

/-- The concrete inner-delivery contract discharges the poll composition's
last callback. No supplied replacement operation or success premise remains. -/
theorem actual_poll (pid : PeerId) (budget : Nat) :
    PrefixPreserves StateInv HistorySafe (RxHistory.observePoll pid budget) :=
  observed_poll PendingStack.deliverInner_native pid budget

theorem actual_napi_softirq : PrefixPreserves StateInv HistorySafe RxHistory.napiSoftirq :=
  napi_softirq PendingStack.deliverInner_native

theorem actual_napi_inline : PrefixPreserves StateInv HistorySafe RxHistory.pollScheduledInline :=
  napi_inline PendingStack.deliverInner_native

theorem actual_napi_irq_exit : PrefixPreserves StateInv HistorySafe RxHistory.napiIrqExit :=
  napi_irq_exit PendingStack.deliverInner_native

end Leanux.Proofs.WG.Noise.PendingSession
