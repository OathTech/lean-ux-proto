import Leanux.Proofs.WG.TransmitSecurity.NonceStack

/-! Both actual NAPI entry points and the source IRQ-exit placement preserve
one nonce journal, including any sends produced by the real stack callback. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def softirqObserved : PrefixM Allocation Unit :=
  RxNapi.softirqWith (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) nativePollObserved

def inlinePollObserved : PrefixM Allocation Unit :=
  RxNapi.inlineWith (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) nativePollObserved

def irqExitObserved : PrefixM Allocation Unit :=
  RxNapi.irqExitWith (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) softirqObserved

theorem softirqObserved_erases : ErasesPrefix softirqObserved Env.napiSoftirq :=
  RxNapi.softirq_erases (liftWGObserver_erases (erasesStatePrefix_lift _)) nativePollObserved_erases

theorem inlinePollObserved_erases : ErasesPrefix inlinePollObserved Env.pollScheduledInline :=
  RxNapi.inline_erases (liftWGObserver_erases (erasesStatePrefix_lift _)) nativePollObserved_erases

theorem irqExitObserved_erases : ErasesPrefix irqExitObserved Env.napiIrqExit :=
  RxNapi.irqExit_erases (liftWGObserver_erases (erasesStatePrefix_lift _)) softirqObserved_erases

theorem softirqObserved_safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup softirqObserved :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    (Frames.lift_frame Frames.pending_peers).liftWGObserver nativePollObserved_safe

theorem inlinePollObserved_safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup inlinePollObserved :=
  RxNapi.inline_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    (Frames.lift_frame Frames.pending_peers).liftWGObserver nativePollObserved_safe

theorem irqExitObserved_safe : PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup irqExitObserved :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.nodup) Frames.product_store
    (Frames.lift_frame Frames.scheduled_peers).liftWGObserver softirqObserved_safe

end Leanux.Proofs.WG.TransmitSecurity.Nonce
