import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceFrontFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames

/-! Stack replies preserve positive resident counts using the same staging
source. No independent execution history is joined by erasure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Observed (E := E) (Driver.transmitObserved EntrySource.hooks (E := E) family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [EntrySource.hooks]
  apply StatePrefixEnsures.bind (lift _ (tx_front family addr packets mtu))
  intro result
  cases result with
  | error err => exact pure err
  | ok pid =>
    exact StatePrefixEnsures.bind (staging pid) (fun _ =>
      StatePrefixEnsures.bind (lift _ (peer_put (some pid))) (fun _ => pure 0))

theorem product_lift (action : Leanux.M α)
    (preserved : Framing.Preserves (fun w : World => Inv w.wg) action) :
    ProductPreserves (E := E) (liftPrefix action) :=
  (PrefixEnsures.lift action (fun _ _ hi => hi.1)
    (fun _ w x v hi run => ⟨hi.1,(hoare_iff_run _ _ _).mp preserved w x v hi.2 run⟩)).preserves

theorem product_stable (h : List E) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : (ProductInv (E := E)) h w) : (ProductInv (E := E)) h v := by
  have stored := congrArg (fun s : ProductStore43 => s.2.2.2) same
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev stored
  exact ⟨hi.1,by simpa only [Inv,Positive,view,device] using hi.2⟩

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductPreserves (E := E) (liftPrefix action) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have stored := congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w x v run)
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev stored
  simpa only [Inv,Positive,view,device] using hi

theorem stack (bytes : List UInt8) : ProductPreserves (E := E) (Driver.stackObserved EntrySource.hooks (E := E) bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.1) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.1) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.1) product_stable _
        (fun family addr packets mtu => product_safe (transmit family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush (packets : List (List UInt8)) :
    ProductPreserves (E := E) (Driver.stackFlushObserved EntrySource.hooks (E := E) packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stack bytes) (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) :
    ProductPreserves (E := E) (Driver.nativePollObserved EntrySource.hooks (E := E) pid budget) := by
  rw [Driver.nativePoll_neutral _ rfl]
  exact poll pid budget _ stack_flush

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
