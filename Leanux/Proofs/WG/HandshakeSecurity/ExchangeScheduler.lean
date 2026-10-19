import Leanux.Proofs.WG.HandshakeSecurity.ExchangeWorkers

/-! The committed native scheduler carries the exchange ledger across all
worker kinds. Consistency trials remain native copied-state computations and
produce no committed exchange receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000

theorem product_work (f : List PeerId → List PeerId) : ProductPreserves
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _ (modify_device _ (fun _ => rfl))

theorem product_tx_read (id : SkbId) : ProductPreserves (liftPrefix (liftWG (getTxSkb id))) :=
  product_native _ (fun h => skb_frame h (SkbStore.getTx id))

theorem cryptAhead_checked (frames : H1WorkerTagFrames) (pid : PeerId) :
    ProductPreserves (Driver.cryptAheadObserved ExchangeDriver.hooks pid) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration_checked frames)
    | (nonce_product_head liftPrefix; first
       | with_reducible exact product_native _ (read_peer _)
       | exact product_tx_read _
       | with_reducible exact product_work (fun q => q ++ [pid])
       | with_reducible exact product_work (fun q => q.erase pid))
    | (nonce_product_head liftPrefix; first | exact product_ambient _ | with_reducible exact product_stop _)
    | exact product_tx_read _
    | exact product_pure _
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iteration_checked (H1 : H1ExchangeEdges) (handshake : H1HandshakeTagFrames)
    (data : H1DataTagFrames) (frames : H1WorkerTagFrames) (a : Activation) :
    ProductPreserves (Driver.iterationObserved ExchangeDriver.hooks a) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration_checked frames)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration_checked frames)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration_checked H1 handshake data)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration_checked frames _)
    | (nonce_product_head Driver.cryptAheadObserved; exact cryptAhead_checked frames _)
    | (nonce_product_head liftPrefix; first | exact product_ambient _ | with_reducible exact product_stop _)
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule_checked (H1 : H1ExchangeEdges) (handshake : H1HandshakeTagFrames)
    (data : H1DataTagFrames) (frames : H1WorkerTagFrames) (stack : Option Worker) :
    ProductPreserves (Driver.scheduleObserved ExchangeDriver.hooks stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.safe) product_stable
    (fun pid => product_work (fun q => q.erase pid)) _ _
    (iteration_checked H1 handshake data frames) (softirq_checked frames) stack

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
