import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialStaging
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialFrontFrames
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialExecutionConsumer

/-! Actual stack replies preserve RX allocation identity through the shared
transmit source. This discharges the native poll's complete callback contract. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Journal.front family addr packets mtu) :=
  state_observed
    (history_receipt_state _ _ (fun _ => ⟨rfl,by intro p k receipt impossible; cases impossible⟩)
      (Driver.History.state_lift _))
    (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    (fun _ => bounded_front family addr packets mtu)

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved Journal.hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [Journal.hooks]
  apply state_bind (front family addr packets mtu)
  intro result
  cases result with
  | error err => exact state_pure err
  | ok pid =>
    apply state_bind (staging pid)
    intro _
    apply state_bind (state_native _ (fun _ => bounded_peer_put (some pid)))
    intro _
    exact state_pure 0

theorem bounded_device (same : v.dev = w.dev) (before : Bounded h w) : Bounded h v := by
  simpa only [Bounded,Inv,KeyBounds,Certificate,packetStamp,pool,same] using before

theorem product_stable (h : List Journal.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Carrier h w.wg) : Carrier h v.wg := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  exact ⟨bounded_device device hi.1,hi.2⟩

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductSafe (liftPrefix action) := by
  change PrefixEnsures (fun h (w : World) => Carrier h w.wg) Safe _ (fun _ h (w : World) => Carrier h w.wg)
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w value v hi run
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp same w value v run) hi

theorem product_lift (action : Leanux.M α)
    (frame : ∀ h, Preserves (fun w : World => Bounded h w.wg) action) :
    ProductSafe (liftPrefix action) := by
  change PrefixEnsures (fun h (w : World) => Carrier h w.wg) Safe _ (fun _ h (w : World) => Carrier h w.wg)
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w value v hi run
  exact ⟨(hoare_iff_run _ _ _).mp (frame _) w value v hi.1 run,hi.2⟩

theorem product_observed {g : PrefixM Journal.Event α} {action : Leanux.M α}
    (history : Driver.ProductHistorySafe Safe g) (erase : ErasesPrefix g action)
    (frame : ∀ h, Preserves (fun w : World => Bounded h w.wg) action) : ProductSafe g := by
  intro w h hi
  obtain ⟨suffix,appended,safe,_⟩ := history w h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix g w h).1 with
  | error err => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    have native := (erase w h).symm.trans run
    have kept := (hoare_iff_run _ _ _).mp (frame _) w value v hi.1 native
    change Carrier (runPrefix g w h).2 v.wg
    rw [appended]
    exact ⟨by rw [List.filterMap_append]; exact bounded_append kept,appended ▸ safe⟩

theorem stack (bytes : List UInt8) : ProductSafe (Driver.stackObserved Journal.hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.2) product_stable _
    (fun packet => receive4With_preserves (fun _ _ hi => hi.2) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.2) product_stable _
        (fun family addr packets mtu => product_state (transmit family addr packets mtu)) dst reply) packet) bytes

theorem stack_flush (packets : List (List UInt8)) :
    ProductSafe (Driver.stackFlushObserved Journal.hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons packet rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact product_bind (stack packet) (fun _ => ih)

theorem native_poll_closed (pid : PeerId) (budget : Nat) :
    ProductSafe (Driver.nativePollObserved Journal.hooks pid budget) :=
  native_poll (fun pid pkt value => product_state (receive_tail pid pkt value))
    (fun gro bytes => napiGroReceivePrefix_preserves _ (fun _ _ hi => hi.2) stack_flush gro bytes)
    (fun gro => napiGroFlushAllPrefix_preserves _ (fun _ _ hi => hi.2) stack_flush gro) pid budget

private theorem pending : StateSafe (liftWGPrefix RxNapi.pendingSource) := by
  apply state_native
  intro h
  unfold RxNapi.pendingSource
  exact preserves_bind (bounded_store getDev_sameWGStore) (fun _ => preserves_pure _)

private theorem scheduled : StateSafe (liftWGPrefix RxNapi.scheduledSource) := by
  apply state_native
  intro h
  unfold RxNapi.scheduledSource
  exact preserves_bind (bounded_store getDev_sameWGStore) (fun _ => preserves_pure _)

theorem softirq : ProductSafe (Driver.softirqObserved Journal.hooks) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.2) product_stable (product_state pending) native_poll_closed

theorem inline_poll : ProductSafe (Driver.inlinePollObserved Journal.hooks) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.2) product_stable (product_state pending) native_poll_closed

theorem irq_exit : ProductSafe (Driver.irqExitObserved Journal.hooks) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.2) product_stable (product_state scheduled) softirq

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
