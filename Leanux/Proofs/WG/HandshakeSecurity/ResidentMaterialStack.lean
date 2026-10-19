import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialPoll
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialFrontFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames

/-! Actual IPv4 stack replies use the same material-carrying transmit source.
This closes the receive poll's callback obligation, including stopped runs. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem front_carrier (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    CarrierSafe (Journal.front family addr packets mtu) :=
  carrier_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
    (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
    (fun _ => NativeFrames.front family addr packets mtu)
    (bounds_forget (DriverCuts.carrier_tx_front family addr packets mtu))

theorem transmit_carrier (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    CarrierSafe (Driver.transmitObserved Journal.hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [Journal.hooks]
  apply StatePrefixEnsures.bind (front_carrier family addr packets mtu)
  intro result
  cases result with
  | error err => exact carrier_pure err
  | ok pid =>
    apply StatePrefixEnsures.bind (staging_carrier pid)
    intro _
    apply StatePrefixEnsures.bind (carrier_lift _ (fun _ => NativeFrames.peer_put (some pid)) (bounds_peer_put (some pid)))
    intro _
    exact carrier_pure 0

theorem product_lift (action : Leanux.M α)
    (native : ∀ h, Preserves (fun w : World => Inv h w.wg) action)
    (bounds : Preserves (fun w : World => Bounds w.wg) action) :
    ProductSafe (liftPrefix action) :=
  product_quiet (Appends.lift _) (HistoryFrame.lift _ _) (erasesPrefix_lift _) native bounds

theorem product_stable (h : List Journal.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  refine ⟨⟨?_,hi.1.2⟩,?_,CurrentSlots.fields_transport hi.2.2 ?_⟩
  · simpa only [Inv,pool,device] using hi.1.1
  · intro s hs
    apply hi.2.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductSafe (liftPrefix action) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2)
  intro h w x v hi run
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp same w x v run) hi

theorem stack_carrier (bytes : List UInt8) : ProductSafe (Driver.stackObserved Journal.hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.1.2) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.1.2) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.1.2) product_stable _
        (fun family addr packets mtu => product_state (transmit_carrier family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush_carrier (packets : List (List UInt8)) :
    ProductSafe (Driver.stackFlushObserved Journal.hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stack_carrier bytes) (fun _ => ih)

theorem native_poll_carrier (pid : PeerId) (budget : Nat) :
    ProductSafe (Driver.nativePollObserved Journal.hooks pid budget) := by
  rw [Driver.nativePoll_neutral _ rfl rfl]
  exact poll_carrier pid budget _ stack_flush_carrier

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
