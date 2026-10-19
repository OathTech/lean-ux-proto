import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral
import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionFrontFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)

theorem transmit (quiet : H1PendingQuietFrames) (frames : H1PendingStackFrames) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Observed (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  dsimp only [hooks]
  apply StatePrefixEnsures.bind (native _ (Carrier.tx_front frames family addr packets mtu))
  intro result
  cases result with
  | error err => exact pure err
  | ok pid =>
    exact StatePrefixEnsures.bind (staging quiet pid) (fun _ =>
      StatePrefixEnsures.bind (native _ (fun confirmed => Carrier.peer_put confirmed (some pid))) (fun _ => pure 0))

theorem product_lift (action : Leanux.M α)
    (preserves : ∀ confirmed, Framing.Preserves (fun w : World => Carrier confirmed w.wg) action) :
    ProductPreserves (liftPrefix action) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2.2.distinct)
  intro h w x v hi run
  exact (hoare_iff_run _ _ _).mp (preserves (Responder.DriverCuts.labels h)) w x v hi run

theorem product_stable (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  have counter : v.wg.keypairCounter = w.wg.keypairCounter :=
    congrArg (fun s : ProductStore43 => s.2.2.2.keypairCounter) same
  refine ⟨?_,CurrentSlots.fields_transport hi.2.1 ?_,hi.2.2.retained ?_⟩
  · intro s hs
    apply hi.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]
  · have keys : keypairResidents v.wg = keypairResidents w.wg := by
      funext kid
      simp only [keypairResidents,device]
    have projection : view v.wg = view w.wg := by
      simp only [view,nextSlot,keys,device,counter]
    rw [projection]
    exact Retained.refl _

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductPreserves (liftPrefix action) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.2.2.distinct)
  intro h w x v hi run
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp same w x v run) hi

theorem stack (quiet : H1PendingQuietFrames) (frames : H1PendingStackFrames) (bytes : List UInt8) : ProductPreserves (Driver.stackObserved hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.2.2.distinct) product_stable _
        (fun family addr packets mtu => product_safe (transmit quiet frames family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush (quiet : H1PendingQuietFrames) (frames : H1PendingStackFrames) (packets : List (List UInt8)) :
    ProductPreserves (Driver.stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact PrefixPreserves.bind (stack quiet frames bytes) (fun _ => ih)

theorem native_poll (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (frames : H1PendingPollFrames) (stackFrames : H1PendingStackFrames) (pid : PeerId) (budget : Nat) :
    ProductPreserves (Driver.nativePollObserved hooks pid budget) := by
  rw [Driver.nativePoll_neutral _ rfl rfl]
  exact poll edges quiet frames pid budget _ (stack_flush quiet stackFrames)

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
