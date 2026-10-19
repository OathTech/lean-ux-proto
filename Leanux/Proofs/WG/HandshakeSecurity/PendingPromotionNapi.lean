import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionStack

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)
variable (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
  (frames : H1PendingPollFrames) (stackFrames : H1PendingStackFrames)

theorem pending : Observed (liftWGPrefix RxNapi.pendingSource) :=
  native _ (fun confirmed => preserves_bind (Carrier.store confirmed getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem scheduled : Observed (liftWGPrefix RxNapi.scheduledSource) :=
  native _ (fun confirmed => preserves_bind (Carrier.store confirmed getDev_sameWGStore)
    (fun _ => preserves_pure _))

include edges quiet frames stackFrames in
theorem softirq : ProductPreserves (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2.2.distinct) product_stable
    (product_safe pending) (native_poll edges quiet frames stackFrames)

include edges quiet frames stackFrames in
theorem inline_poll : ProductPreserves (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2.2.distinct) product_stable
    (product_safe pending) (native_poll edges quiet frames stackFrames)

include edges quiet frames stackFrames in
theorem irq_exit : ProductPreserves (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2.2.distinct) product_stable
    (product_safe scheduled) (softirq edges quiet frames stackFrames)

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
