import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveStack

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem pending : Preserves (liftWGPrefix RxNapi.pendingSource) :=
  lift _ (fun confirmed => preserves_bind (frame_store confirmed _ getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem scheduled : Preserves (liftWGPrefix RxNapi.scheduledSource) :=
  lift _ (fun confirmed => preserves_bind (frame_store confirmed _ getDev_sameWGStore)
    (fun _ => preserves_pure _))

theorem softirq : ProductPreserves (Driver.softirqObserved TimestampDriver.hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe pending) native_poll

theorem inline_poll : ProductPreserves (Driver.inlinePollObserved TimestampDriver.hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe pending) native_poll

theorem irq_exit : ProductPreserves (Driver.irqExitObserved TimestampDriver.hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.1) product_stable
    (product_safe scheduled) softirq

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
