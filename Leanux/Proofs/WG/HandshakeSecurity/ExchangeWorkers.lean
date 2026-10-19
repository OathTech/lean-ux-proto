import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1WorkerFrames

/-! Actual worker iterations carry the exchange ledger through native data
callbacks, NAPI and rescheduling, with the receive worker recording exchanges. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000


theorem nativePoll_checked (frames : H1WorkerTagFrames) (pid : PeerId) (budget : Nat) :
    ProductPreserves (Driver.nativePollObserved ExchangeDriver.hooks pid budget) := by
  rw [ExchangeDriver.nativePoll_lift]
  exact product_frame _ (frames.poll pid budget)

theorem softirq_checked (frames : H1WorkerTagFrames) : ProductPreserves (Driver.softirqObserved ExchangeDriver.hooks) := by
  rw [ExchangeDriver.softirq_lift]
  exact product_frame _ frames.softirq

theorem inline_checked (frames : H1WorkerTagFrames) : ProductPreserves (Driver.inlinePollObserved ExchangeDriver.hooks) := by
  rw [ExchangeDriver.inline_lift]
  exact product_frame _ frames.inlinePoll

theorem irqExit_checked (frames : H1WorkerTagFrames) : ProductPreserves (Driver.irqExitObserved ExchangeDriver.hooks) := by
  rw [ExchangeDriver.irqExit_lift]
  exact product_frame _ frames.irqExit

theorem encrypt_tail_frame (frames : H1WorkerTagFrames) (item : Option (List SkbId)) (h : List Event) :
    Framing.Preserves (ProductInv h) (RxWorkers.encryptStepTailSource item) := by
  let P := ProductInv h
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (monadLift (liftSkb a) : Leanux.M α) :=
    PublicationPoll.native_product _ _ (skb_frame h a)
  have encrypt (kid : KeypairId) (pkt : DataPacket) : Framing.Preserves P
      (encryptPacket Env.checksumHelp kid pkt) := frame_product h _ (frames.encryptPacket kid pkt)
  have publish (xs : List SkbId) (state : PacketState) : Framing.Preserves P
      (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (frame h _ (frames.enqueue xs state))
  routing_tx_source [RxWorkers.encryptStepTailSource,getTxSkb,setTxSkb] using [skb,encrypt,publish,effect]

theorem encrypt_poll_frame (h : List Event) : Framing.Preserves (StateInv h) TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (frame_store h _ getDev_sameWGStore)
  intro d
  exact preserves_bind (modify_device (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2}) (fun _ => rfl) h) (fun _ => preserves_pure _)

theorem resched_checked (worker : Worker) (site : Decision) :
    ProductPreserves (Driver.reschedObserved worker site) :=
  PrefixPreserves.bind (product_store _ (condResched_sameKernel worker)) (fun _ => product_ambient _)

theorem encrypt_tail_checked (frames : H1WorkerTagFrames) (item : Option (List SkbId)) :
    ProductPreserves (Driver.encryptTailObserved ExchangeDriver.hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (product_lift _ (encrypt_tail_frame frames item)) (resched_checked _ _)

theorem encrypt_iteration_checked (frames : H1WorkerTagFrames) : ProductPreserves (Driver.encryptIterObserved ExchangeDriver.hooks) := by
  unfold Driver.encryptIterObserved
  dsimp only [ExchangeDriver.hooks]
  exact PrefixPreserves.bind (product_native _ encrypt_poll_frame) (fun _ =>
    PrefixPreserves.bind (softirq_checked frames) (fun _ => encrypt_tail_checked frames _))

theorem tx_iteration_checked (frames : H1WorkerTagFrames) (pid : PeerId) :
    ProductPreserves (Driver.txIterObserved ExchangeDriver.hooks pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (product_native _ (fun h => frame h _ (frames.txStep pid))) (resched_checked _ _)

theorem decrypt_step_checked (frames : H1WorkerTagFrames) : ProductPreserves (Driver.decryptStepObserved ExchangeDriver.hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind (softirq_checked frames)
  intro _
  apply PrefixPreserves.bind (product_native _ (fun h => frame h _ frames.decryptPrepare))
  intro item
  cases item with
  | none => exact product_pure _
  | some pid =>
    exact PrefixPreserves.bind (irqExit_checked frames) (fun _ =>
      PrefixPreserves.bind (product_native _ (peer_put (some pid))) (fun _ =>
        PrefixPreserves.bind (softirq_checked frames) (fun _ => product_pure _)))

theorem decrypt_iteration_checked (frames : H1WorkerTagFrames) : ProductPreserves (Driver.decryptIterObserved ExchangeDriver.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) (decrypt_step_checked frames) (resched_checked _ _)

theorem receive_iteration_checked (H1 : H1ExchangeEdges) (handshake : H1HandshakeTagFrames)
    (data : H1DataTagFrames) : ProductPreserves (Driver.receiveIterObserved ExchangeDriver.hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (product_state (handshake_checked H1 handshake data))
    (product_store _ (condResched_sameKernel .receiveWorker))

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
