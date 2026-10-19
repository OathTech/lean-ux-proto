import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialStack

/-! Both actual NAPI modes and IRQ exit carry the same TX material invariant. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem pending_carrier : CarrierSafe (liftWGPrefix RxNapi.pendingSource) :=
  carrier_lift _ (fun _ => preserves_bind (NativeFrames.store getDev_sameWGStore)
    (fun _ => preserves_pure _))
    (preserves_bind (bounds_store getDev_sameWGStore) (fun _ => preserves_pure _))

theorem scheduled_carrier : CarrierSafe (liftWGPrefix RxNapi.scheduledSource) :=
  carrier_lift _ (fun _ => preserves_bind (NativeFrames.store getDev_sameWGStore)
    (fun _ => preserves_pure _))
    (preserves_bind (bounds_store getDev_sameWGStore) (fun _ => preserves_pure _))

theorem softirq_carrier : ProductSafe (Driver.softirqObserved Journal.hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.1.2) product_stable
    (product_state pending_carrier) native_poll_carrier

theorem inline_poll_carrier : ProductSafe (Driver.inlinePollObserved Journal.hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.1.2) product_stable
    (product_state pending_carrier) native_poll_carrier

theorem irq_exit_carrier : ProductSafe (Driver.irqExitObserved Journal.hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.1.2) product_stable
    (product_state scheduled_carrier) softirq_carrier

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
