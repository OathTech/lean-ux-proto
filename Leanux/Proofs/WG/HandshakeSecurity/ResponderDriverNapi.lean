import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverStack

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem pending : Preserves (liftWGPrefix RxNapi.pendingSource) :=
  lift _ (fun confirmed => preserves_bind (carrier_store getDev_sameWGStore confirmed)
    (fun _ => preserves_pure _))

theorem scheduled : Preserves (liftWGPrefix RxNapi.scheduledSource) :=
  lift _ (fun confirmed => preserves_bind (carrier_store getDev_sameWGStore confirmed)
    (fun _ => preserves_pure _))

theorem softirq (H1 : H1ResponderCurrentEdges) : ProductPreserves (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2) product_stable
    (product_safe pending) (native_poll H1)

theorem inline_poll (H1 : H1ResponderCurrentEdges) : ProductPreserves (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2) product_stable
    (product_safe pending) (native_poll H1)

theorem irq_exit (H1 : H1ResponderCurrentEdges) : ProductPreserves (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2) product_stable
    (product_safe scheduled) (softirq H1)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
