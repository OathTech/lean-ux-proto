import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageFixture
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Supplied fixture packets, ingress and batch operations use the exact source
callbacks. Stack replies keep their receive-derived scope rather than gaining a
local-operation label. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductAt frames (Driver.injectObserved hooks family port msg tos ll dest) := by
  exact TrafficSource.inject_preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ _ _ (fun _ _ => product_lift _)
    (crypt) (fun _ _ => product_lift _) family port msg tos ll dest

theorem after_batch : ProductAt frames (Driver.afterBatchObserved hooks) := by
  exact DeliverySource.afterBatch_preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ _ _ _ _ _ (crypt) (send_workers)
    (send_worker) (fun stack => schedule stack) (fun _ _ => product_lift _) deliver

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductAt frames (Driver.floodObserved hooks count port family messages) := by
  exact TrafficSource.flood_preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ _ _ _ (fun _ _ => product_lift _)
    (inline_poll) (after_batch) (fun _ _ => product_lift _)
    count port family messages

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductAt frames (Driver.batchItemObserved hooks d cqes item) := by
  exact batchItemWith_preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ _ _ _ (fun _ _ => product_lift _)
    (inline_poll) (fun _ _ => product_lift _)
    (fun family addr packets mtu => product_state _ (fixture_transmit family addr packets mtu))
    d cqes item

theorem batch (items : List Env.BatchItem) : ProductAt frames (Driver.batchObserved hooks items) := by
  exact TrafficSource.batch_preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ _ (fun d cqes item => batch_item d cqes item)
    (after_batch) items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductAt frames (Driver.syscallXmitObserved hooks family addr payload opts) := by
  exact syscallXmitWith_preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) _ _ (fun _ _ => product_lift _)
    (fun family addr packets mtu => product_state _ (fixture_transmit family addr packets mtu))
    family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
