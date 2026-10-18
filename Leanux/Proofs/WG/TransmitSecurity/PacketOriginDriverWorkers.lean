import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverNapi
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginWorkerFrames

/-! Actual worker callbacks retain both the resident allocation carrier and
the strict-prefix allocation evidence of every completed AEAD receipt. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem product_native (action : WG.M α) (native : ∀ h, Preserves (Inv h) action) :
    ProductSafe (liftPrefix (liftWG action)) :=
  product_lift _ (fun h => PublicationPoll.native_product _ _ (native h))

theorem product_ambient (action : AmbientM α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched (worker : Worker) (site : Decision) :
    ProductSafe (Driver.reschedObserved worker site) :=
  PrefixPreserves.bind (product_store _ (condResched_sameKernel worker))
    (fun _ => product_ambient _)

theorem encrypt_tail_observed (item : Option (List SkbId)) :
    ProductSafe (Driver.encryptTailObserved Journal.hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (encrypt item) (resched _ _)

theorem encrypt_poll : ProductSafe Journal.poll :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ _ (fun _ => rfl) _) (fun _ => rfl))
    (by
      intro w h
      rw [Journal.poll,runPrefix_receiptObserved]
      have erased := focusPrefix_erases Journal.Event.ring Journal.ring? TxRing.poll_erases w h
      cases result : runPrefix (focusPrefix Journal.Event.ring Journal.ring? TxRing.poll) w h with
      | mk outcome history =>
        rw [result] at erased
        cases outcome <;> exact erased)
    (fun _ => PublicationPoll.native_product _ _ NativeFrames.poll)

theorem encrypt_iteration : ProductSafe (Driver.encryptIterObserved Journal.hooks) := by
  unfold Driver.encryptIterObserved
  dsimp only [Journal.hooks]
  exact PrefixPreserves.bind encrypt_poll (fun _ =>
    PrefixPreserves.bind softirq (fun _ => encrypt_tail_observed _))

theorem tx_step (pid : PeerId) : ProductSafe (Journal.transmit pid) :=
  product_quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun e => by cases e <;> rfl) _)
    (focusPrefix_erases _ _ (Completion.step_erases pid))
    (fun _ => PublicationPoll.native_product _ _ (NativeFrames.transmit pid))

theorem tx_iteration (pid : PeerId) : ProductSafe (Driver.txIterObserved Journal.hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (tx_step pid) (resched _ _)

theorem prepare : ProductSafe (Journal.hooks.prepare) :=
  product_quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (AuthenticatedEffects.TransportDriver.prepare_erases _ _)
    (fun _ => PublicationPoll.native_product _ _ NativeFrames.prepare)

theorem decrypt_step : ProductSafe (Driver.decryptStepObserved Journal.hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind softirq
  intro _
  apply PrefixPreserves.bind prepare
  intro item
  cases item with
  | none => exact product_pure _
  | some pid =>
    exact PrefixPreserves.bind irq_exit (fun _ =>
      PrefixPreserves.bind (product_native _ (fun _ => NativeFrames.peer_put (some pid))) (fun _ =>
        PrefixPreserves.bind softirq (fun _ => product_pure _)))

theorem decrypt_iteration : ProductSafe (Driver.decryptIterObserved Journal.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) decrypt_step (resched _ _)

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
