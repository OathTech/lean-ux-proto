import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginDriverReceive
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginFrontFrames
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginProductFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames

/-! Actual IPv4 stack replies enter the same origin-carrying TX source. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Journal.front family addr packets mtu) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
    (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    (fun _ => NativeFrames.front family addr packets mtu)

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved Journal.hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (front family addr packets mtu)
  intro result
  cases result with
  | error err => exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)
  | ok pid =>
    apply StatePrefixEnsures.bind (staging pid)
    intro _
    apply StatePrefixEnsures.bind (state_lift _ (fun _ => NativeFrames.peer_put (some pid)))
    intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem product_lift (action : Leanux.M α)
    (native : ∀ h, Preserves (fun w : World => Inv h w.wg) action) :
    ProductSafe (liftPrefix action) :=
  product_quiet (Appends.lift _) (HistoryFrame.lift _ _) (erasesPrefix_lift _) native

theorem product_stable (h : List Journal.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv h w) : ProductInv h v := by
  exact ⟨product_store_inv (receipts h) w v same hi.1,hi.2⟩

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductSafe (liftPrefix action) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w x v hi run
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp same w x v run) hi

theorem stack (bytes : List UInt8) : ProductSafe (Driver.stackObserved Journal.hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.2) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.2) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.2) product_stable _
        (fun family addr packets mtu => product_state (transmit family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush (packets : List (List UInt8)) :
    ProductSafe (Driver.stackFlushObserved Journal.hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stack bytes) (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) :
    ProductSafe (Driver.nativePollObserved Journal.hooks pid budget) :=
  poll pid budget _ stack_flush

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
