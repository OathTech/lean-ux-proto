import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceStack

/-! Both native NAPI dispatch modes preserve the same positive-reference carrier. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem pending : Observed (E := E) (liftWGPrefix RxNapi.pendingSource) :=
  lift _ (preserves_bind (store getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem scheduled : Observed (E := E) (liftWGPrefix RxNapi.scheduledSource) :=
  lift _ (preserves_bind (store getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem softirq : ProductPreserves (E := E) (Driver.softirqObserved EntrySource.hooks (E := E)) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe pending) native_poll

theorem inline_poll : ProductPreserves (E := E) (Driver.inlinePollObserved EntrySource.hooks (E := E)) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe pending) native_poll

theorem irq_exit : ProductPreserves (E := E) (Driver.irqExitObserved EntrySource.hooks (E := E)) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe scheduled) softirq

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
