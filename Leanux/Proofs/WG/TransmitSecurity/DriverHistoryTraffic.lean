import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! History-only contracts through every native fixture traffic caller. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}

private theorem history_safe (h : List E) (_ : World) (hi : Safe h) : Safe h := hi

theorem inject_history (h : ActorHistorySafe Safe g) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductHistorySafe Safe (injectObserved g family port msg tos ll dest) :=
  TrafficSource.inject_preserves history_safe (fun _ _ _ _ hi => hi) _ _ _
    (fun _ _ => History.product_lift _) (crypt_history h) (fun _ _ => History.product_lift _)
    family port msg tos ll dest

theorem afterBatch_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (afterBatchObserved g) :=
  TrafficSource.afterBatch_preserves history_safe (fun _ _ _ _ hi => hi) _ _ _ _ _
    (crypt_history h) (sendWorkers_history h) h.sendWorker (schedule_history h)
    (fun _ _ => History.product_lift _)

theorem flood_history (h : ActorHistorySafe Safe g) (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductHistorySafe Safe (floodObserved g count port family messages) :=
  TrafficSource.flood_preserves history_safe (fun _ _ _ _ hi => hi) _ _ _ _
    (fun _ _ => History.product_lift _) (inline_history h) (afterBatch_history h)
    (fun _ _ => History.product_lift _) count port family messages

theorem batchItem_history (h : ActorHistorySafe Safe g) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductHistorySafe Safe (batchItemObserved g d cqes item) :=
  batchItemWith_preserves history_safe (fun _ _ _ _ hi => hi) _ _ _ _
    (fun _ _ => History.product_lift _) (inline_history h) (fun _ _ => History.product_lift _)
    (fun family addr packets mtu => (transmit_history h family addr packets mtu).liftWGObserver) d cqes item

theorem batch_history (h : ActorHistorySafe Safe g) (items : List Env.BatchItem) :
    ProductHistorySafe Safe (batchObserved g items) :=
  TrafficSource.batch_preserves history_safe (fun _ _ _ _ hi => hi) _ _
    (batchItem_history h) (afterBatch_history h) items

theorem syscallXmit_history (h : ActorHistorySafe Safe g) (family addr : Nat)
    (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductHistorySafe Safe (syscallXmitObserved g family addr payload opts) :=
  syscallXmitWith_preserves history_safe (fun _ _ _ _ hi => hi) _ _ (fun _ _ => History.product_lift _)
    (fun family addr packets mtu => (transmit_history h family addr packets mtu).liftWGObserver) family addr payload opts

end Leanux.Proofs.WG.TransmitSecurity.Driver
