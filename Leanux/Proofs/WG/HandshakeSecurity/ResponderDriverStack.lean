import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverFrontFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverPoll
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [hooks]
  apply StatePrefixEnsures.bind (lift _ (carrier_tx_front family addr packets mtu))
  intro result
  cases result with
  | error err => exact pure err
  | ok pid =>
    exact StatePrefixEnsures.bind (staging pid) (fun _ =>
      StatePrefixEnsures.bind (lift _ (carrier_peer_put (some pid))) (fun _ => pure 0))

theorem product_lift (action : Leanux.M α)
    (preserves : ∀ confirmed, Framing.Preserves (fun w : World => Carrier confirmed w.wg) action) :
    ProductPreserves (liftPrefix action) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
  intro h w x v hi run
  exact ⟨(hoare_iff_run _ _ _).mp (preserves (labels h)) w x v hi.1 run, hi.2⟩

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductPreserves (liftPrefix action) := by
  apply product_lift
  intro confirmed
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp same w x v run)
  refine ⟨?_, (hoare_iff_run _ _ _).mp (native_product_store same confirmed) w x v hi.2 run⟩
  intro s hs
  apply hi.1 s
  simpa only [ConfiguredIdentity.view,device] using hs

theorem product_stable (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  refine ⟨⟨?_,hi.1.2.1.frame ?_,CurrentSlots.fields_transport hi.1.2.2 ?_⟩,hi.2⟩
  · intro s hs
    apply hi.1.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold current
    rw [device]
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]

theorem stack (bytes : List UInt8) : ProductPreserves (Driver.stackObserved hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.2) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.2) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.2) product_stable _
        (fun family addr packets mtu => product_safe (transmit family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush (packets : List (List UInt8)) :
    ProductPreserves (Driver.stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stack bytes) (fun _ => ih)

theorem native_poll (H1 : H1ResponderCurrentEdges) (pid : PeerId) (budget : Nat) :
    ProductPreserves (Driver.nativePollObserved hooks pid budget) :=
  poll H1 pid budget _ stack_flush

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
