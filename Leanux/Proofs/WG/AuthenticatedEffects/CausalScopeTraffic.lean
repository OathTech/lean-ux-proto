import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeFixture
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Supplied fixture packets, ingress and batch operations use the exact source
callbacks. Stack replies keep their receive-derived scope rather than gaining a
local-operation label. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (Driver.injectObserved hooks family port msg tos ll dest) := by
  intro frames
  exact TrafficSource.inject_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ _ _ (fun _ _ => product_lift _ frames)
    (crypt frames) (fun _ _ => product_lift _ frames) family port msg tos ll dest

theorem after_batch : ProductSafe (Driver.afterBatchObserved hooks) := by
  intro frames
  exact DeliverySource.afterBatch_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ _ _ _ _ _ (crypt frames) (send_workers frames)
    (send_worker frames) (fun stack => schedule stack frames) (fun _ _ => product_lift _ frames) (deliver frames)

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe (Driver.floodObserved hooks count port family messages) := by
  intro frames
  exact TrafficSource.flood_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ _ _ _ (fun _ _ => product_lift _ frames)
    (inline_poll frames) (after_batch frames) (fun _ _ => product_lift _ frames)
    count port family messages

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (Driver.batchItemObserved hooks d cqes item) := by
  intro frames
  exact batchItemWith_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ _ _ _ (fun _ _ => product_lift _ frames)
    (inline_poll frames) (fun _ _ => product_lift _ frames)
    (fun family addr packets mtu => product_state _ (fixture_transmit family addr packets mtu) frames)
    d cqes item

theorem batch (items : List Env.BatchItem) : ProductSafe (Driver.batchObserved hooks items) := by
  intro frames
  exact TrafficSource.batch_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ _ (fun d cqes item => batch_item d cqes item frames)
    (after_batch frames) items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (Driver.syscallXmitObserved hooks family addr payload opts) := by
  intro frames
  exact syscallXmitWith_preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) _ _ (fun _ _ => product_lift _ frames)
    (fun family addr packets mtu => product_state _ (fixture_transmit family addr packets mtu) frames)
    family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
