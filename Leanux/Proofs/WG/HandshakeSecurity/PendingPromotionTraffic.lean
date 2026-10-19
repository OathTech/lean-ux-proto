import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionTrafficFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

open Responder.DriverCuts (hooks)

theorem receive_entry (frames : H1IngressFrames) (msg : List UInt8) (src : SkbSource) :
    ProductPreserves (Driver.receiveEntryObserved hooks msg src) := by
  rw [Driver.receiveEntry_lift hooks rfl,liftWGObserver_lift]
  exact product_native _ (Carrier.rx_entry frames msg src)

theorem multicast (family addr : Nat) :
    ProductPreserves (Driver.multicastObserved family addr) :=
  product_lift _ (Carrier.multicast family addr)

theorem drain (what : String) (flags : List Bool) :
    ProductPreserves (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem inject (facts : H1DeferredFrames) (ingress : H1IngressFrames) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductPreserves (Driver.injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _ _ _
    (receive_entry ingress) (crypt facts) drain family port msg tos ll dest

theorem after_batch (facts : H1DeferredFrames) :
    ProductPreserves (Driver.afterBatchObserved hooks) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _ _ _ _ _
    (crypt facts) (send_workers facts) (by rw [Driver.sendWorker_lift hooks rfl]; exact send_one facts.flushed) (schedule facts.worker) drain

theorem flood (facts : H1DeferredFrames) (ingress : H1IngressFrames) (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductPreserves (Driver.floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _ _ _ _
    (receive_entry ingress) (inline_poll facts.worker.edges facts.worker.quiet facts.worker.poll facts.worker.stack) (after_batch facts) drain count port family messages

theorem batch_item (facts : H1DeferredFrames) (ingress : H1IngressFrames) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductPreserves (Driver.batchItemObserved hooks d cqes item) := by
  unfold Driver.batchItemObserved
  simp only [show Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact batchItemWith_preserves (fun _ _ hi => hi.2.2.distinct) product_wg_stable _ _ _ _
    (receive_entry ingress) (inline_poll facts.worker.edges facts.worker.quiet facts.worker.poll facts.worker.stack) multicast
    (fun family addr packets mtu => product_safe (transmit facts.worker.quiet facts.worker.stack family addr packets mtu)) d cqes item

theorem batch (facts : H1DeferredFrames) (ingress : H1IngressFrames) (items : List Env.BatchItem) :
    ProductPreserves (Driver.batchObserved hooks items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _ _
    (batch_item facts ingress) (after_batch facts) items

theorem syscall_xmit (facts : H1DeferredFrames) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductPreserves (Driver.syscallXmitObserved hooks family addr payload opts) := by
  unfold Driver.syscallXmitObserved
  simp only [show Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact syscallXmitWith_preserves (fun _ _ hi => hi.2.2.distinct) product_wg_stable _ _ multicast
    (fun family addr packets mtu => product_safe (transmit facts.worker.quiet facts.worker.stack family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
