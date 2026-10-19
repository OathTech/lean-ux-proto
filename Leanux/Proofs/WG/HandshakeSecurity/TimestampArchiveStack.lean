import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveFrontFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames

/-! Native stack replies and their transmit callback retain the same timestamp
archive. This discharges the GRO callback on the original RX poll. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves (Driver.transmitObserved TimestampDriver.hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [TimestampDriver.hooks]
  apply StatePrefixEnsures.bind (lift _ (tx_front family addr packets mtu))
  intro result
  cases result with
  | error err => exact pure err
  | ok pid =>
    exact StatePrefixEnsures.bind (staging pid) (fun _ =>
      StatePrefixEnsures.bind (lift _ (peer_put (some pid))) (fun _ => pure 0))

theorem product_lift (action : Leanux.M α)
    (preserved : ∀ history, Framing.Preserves (fun w : World => StateInv history w.wg) action) :
    ProductPreserves (liftPrefix action) :=
  (PrefixEnsures.lift action (fun _ _ hi => hi.1)
    (fun h w x v hi run => (hoare_iff_run _ _ _).mp (preserved h) w x v hi run)).preserves

theorem product_stable (h : List TimestampReceipt) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv h w) : ProductInv h v := by
  have store := congrArg (fun s : ProductStore43 => s.2.2.2) same
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev store
  have frontier : v.wg.peerCounter = w.wg.peerCounter := congrArg WGStoreView.peerCounter store
  apply state_retained hi
  · intro pid stamp found
    simpa only [freshnessAt,device] using found
  · rw [frontier]
    exact Nat.le_refl _

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductPreserves (liftPrefix action) := by
  apply product_lift
  intro history
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact product_stable history w v ((ProjectedAction.iff_run _ _ _).mp same w x v run) hi

theorem stack (bytes : List UInt8) : ProductPreserves (Driver.stackObserved TimestampDriver.hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.1) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.1) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.1) product_stable _
        (fun family addr packets mtu => product_safe (transmit family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush (packets : List (List UInt8)) :
    ProductPreserves (Driver.stackFlushObserved TimestampDriver.hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stack bytes) (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) :
    ProductPreserves (Driver.nativePollObserved TimestampDriver.hooks pid budget) :=
  poll pid budget _ stack_flush

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
