import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierReceive

/-! Shared stack replies and NAPI dispatch retain the same RX carrier and
additional order property through their actual callbacks and native store frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

abbrev ProductInv (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (h : List E) (w : World) : Prop :=
  TransportPublication.Inv (h.filterMap origin) w.wg ∧ (TransportReplay.Safe origin replay h ∧ extra h)

theorem product_store (h : List E) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv extra origin replay h w) :
    ProductInv extra origin replay h v := by
  have dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  change v.wg.dev = w.wg.dev at dev
  exact ⟨hi.1.sameRx (by simp only [RxDisposition.nativeRxStore,dev]),hi.2⟩

theorem product_state {g : WGPrefix E α} (safe : StateSafe extra origin replay g) :
    ProductSafe extra origin replay (liftWGObserver g) := safe.liftWGObserver

theorem product_pure (x : α) : ProductSafe extra origin replay (pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.2) x

theorem product_bind {g : PrefixM E α} {f : α → PrefixM E β}
    (hg : ProductSafe extra origin replay g) (hf : ∀ x, ProductSafe extra origin replay (f x)) :
    ProductSafe extra origin replay (g >>= f) := PrefixPreserves.bind hg hf

theorem reply (h : StagingSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (dst : Nat) (bytes : List UInt8) :
    ProductSafe extra origin replay
      (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved hooks family addr packets mtu)) dst bytes) :=
  reply4With_preserves (I := ProductInv extra origin replay) (fun _ _ hi => hi.2)
    product_store _ (fun family addr packets mtu => product_state (transmit h front family addr packets mtu)) dst bytes

theorem stack (h : StagingSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (bytes : List UInt8) : ProductSafe extra origin replay (stackObserved hooks bytes) := by
  unfold stackObserved
  apply stackReceiveWith_preserves (I := ProductInv extra origin replay) (fun _ _ hi => hi.2) product_store
  intro pkt
  exact receive4With_preserves (I := ProductInv extra origin replay) (fun _ _ hi => hi.2)
    product_store _ (reply h front) pkt

theorem flush (h : StagingSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (packets : List (List UInt8)) : ProductSafe extra origin replay (stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons pkt rest ih =>
    simp only [stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact product_bind (stack h front pkt) (fun _ => ih)

theorem gro_receive (callback : List (List UInt8) → PrefixM E Unit)
    (safe : ∀ packets, ProductSafe extra origin replay (callback packets)) (gro : GroState) (bytes : List UInt8) :
    ProductSafe extra origin replay (napiGroReceivePrefix callback gro bytes) :=
  napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.2) safe gro bytes

theorem gro_flush (callback : List (List UInt8) → PrefixM E Unit)
    (safe : ∀ packets, ProductSafe extra origin replay (callback packets)) (gro : GroState) :
    ProductSafe extra origin replay (napiGroFlushAllPrefix callback gro) :=
  napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.2) safe gro

private theorem pending_rx : SameView RxDisposition.nativeRxStore RxNapi.pendingSource := by
  unfold RxNapi.pendingSource
  apply SameView.bind (TransportPublication.store_rx _ getDev_sameWGStore)
  intro d
  exact SameView.pure _ _

private theorem scheduled_rx : SameView RxDisposition.nativeRxStore RxNapi.scheduledSource := by
  unfold RxNapi.scheduledSource
  apply SameView.bind (TransportPublication.store_rx _ getDev_sameWGStore)
  intro d
  exact SameView.pure _ _

theorem softirq (poll : ∀ pid budget, ProductSafe extra origin replay (nativePollObserved hooks pid budget)) :
    ProductSafe extra origin replay (softirqObserved hooks) :=
  RxNapi.softirq_preserves (I := ProductInv extra origin replay) (fun _ _ hi => hi.2) product_store
    (product_state (state_rx _ pending_rx)) poll

theorem inlinePoll (poll : ∀ pid budget, ProductSafe extra origin replay (nativePollObserved hooks pid budget)) :
    ProductSafe extra origin replay (inlinePollObserved hooks) :=
  RxNapi.inline_preserves (I := ProductInv extra origin replay) (fun _ _ hi => hi.2) product_store
    (product_state (state_rx _ pending_rx)) poll

theorem irqExit (poll : ∀ pid budget, ProductSafe extra origin replay (nativePollObserved hooks pid budget)) :
    ProductSafe extra origin replay (irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (I := ProductInv extra origin replay) (fun _ _ hi => hi.2) product_store
    (product_state (state_rx _ scheduled_rx)) (softirq poll)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
