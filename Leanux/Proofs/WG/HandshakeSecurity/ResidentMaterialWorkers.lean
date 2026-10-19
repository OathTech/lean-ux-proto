import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialNapi
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialNativeWorkers

/-! Actual crypt and transmit worker iterations carry allocation-time sending
material through their native NAPI and rescheduling callbacks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem product_native (action : WG.M α) (native : ∀ h, Preserves (Inv h) action)
    (bounds : Preserves Bounds action) : ProductSafe (liftPrefix (liftWG action)) :=
  product_lift _ (fun h => PublicationPoll.native_product _ _ (native h))
    (PublicationPoll.native_product _ _ bounds)

theorem product_ambient (action : AmbientM α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (fun _ => productAmbient_spec action _ (fun _ _ hi => hi))
    (productAmbient_spec action _ (fun _ _ hi => hi))

theorem resched_carrier (worker : Worker) (site : Decision) :
    ProductSafe (Driver.reschedObserved worker site) :=
  PrefixPreserves.bind (product_store _ (condResched_sameKernel worker))
    (fun _ => product_ambient _)

theorem encrypt_tail_carrier (item : Option (List SkbId)) :
    ProductSafe (Driver.encryptTailObserved Journal.hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1.2) (encrypt_carrier item) (resched_carrier _ _)

theorem encrypt_poll_carrier : ProductSafe Journal.poll :=
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
    (PublicationPoll.native_product _ _ (bounds_forget DriverCuts.carrier_encrypt_poll))

theorem encrypt_iteration_carrier : ProductSafe (Driver.encryptIterObserved Journal.hooks) := by
  unfold Driver.encryptIterObserved
  dsimp only [Journal.hooks]
  exact PrefixPreserves.bind encrypt_poll_carrier (fun _ =>
    PrefixPreserves.bind softirq_carrier (fun _ => encrypt_tail_carrier _))

theorem tx_step_carrier (pid : PeerId) : ProductSafe (Journal.transmit pid) :=
  product_quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun e => by cases e <;> rfl) _)
    (focusPrefix_erases _ _ (Completion.step_erases pid))
    (fun _ => PublicationPoll.native_product _ _ (NativeFrames.transmit pid))
    (PublicationPoll.native_product _ _ (bounds_forget (DriverCuts.carrier_tx_step pid)))

theorem tx_iteration_carrier (pid : PeerId) : ProductSafe (Driver.txIterObserved Journal.hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1.2) (tx_step_carrier pid) (resched_carrier _ _)

theorem prepare_carrier : ProductSafe Journal.hooks.prepare :=
  product_quiet (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun _ => rfl) _)
    (AuthenticatedEffects.TransportDriver.prepare_erases _ _)
    (fun _ => PublicationPoll.native_product _ _ NativeFrames.prepare_worker)
    (PublicationPoll.native_product _ _ (bounds_forget DriverCuts.carrier_prepare_worker))

theorem decrypt_step_carrier : ProductSafe (Driver.decryptStepObserved Journal.hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind softirq_carrier
  intro _
  apply PrefixPreserves.bind prepare_carrier
  intro item
  cases item with
  | none => exact product_pure _
  | some pid =>
    exact PrefixPreserves.bind irq_exit_carrier (fun _ =>
      PrefixPreserves.bind (product_native _ (fun _ => NativeFrames.peer_put (some pid)) (bounds_peer_put (some pid))) (fun _ =>
        PrefixPreserves.bind softirq_carrier (fun _ => product_pure _)))

theorem decrypt_iteration_carrier : ProductSafe (Driver.decryptIterObserved Journal.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1.2) decrypt_step_carrier (resched_carrier _ _)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
