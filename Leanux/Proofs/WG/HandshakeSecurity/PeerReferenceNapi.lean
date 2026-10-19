import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceStack

/-! Both native NAPI dispatch modes preserve the same positive-reference carrier. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem pending : Observed (liftWGPrefix RxNapi.pendingSource) :=
  lift _ (preserves_bind (store getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem scheduled : Observed (liftWGPrefix RxNapi.scheduledSource) :=
  lift _ (preserves_bind (store getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem softirq : ProductPreserves (Driver.softirqObserved ExchangeDriver.hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe pending) native_poll

theorem inline_poll : ProductPreserves (Driver.inlinePollObserved ExchangeDriver.hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe pending) native_poll

theorem irq_exit : ProductPreserves (Driver.irqExitObserved ExchangeDriver.hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe scheduled) softirq

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
