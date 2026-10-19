import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginDriverStack

/-! Softirq, inline poll and IRQ exit preserve allocation origins through
their actual stack callbacks. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem pending : StateSafe (liftWGPrefix RxNapi.pendingSource) :=
  state_lift _ (fun _ => preserves_bind (NativeFrames.store getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem scheduled : StateSafe (liftWGPrefix RxNapi.scheduledSource) :=
  state_lift _ (fun _ => preserves_bind (NativeFrames.store getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem softirq : ProductSafe (Driver.softirqObserved Journal.hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2) product_stable
    (product_state pending) native_poll

theorem inline_poll : ProductSafe (Driver.inlinePollObserved Journal.hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2) product_stable
    (product_state pending) native_poll

theorem irq_exit : ProductSafe (Driver.irqExitObserved Journal.hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2) product_stable
    (product_state scheduled) softirq

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
