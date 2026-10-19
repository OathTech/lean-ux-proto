import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTx

/-! Actual scheduler commits retain positive-reference certificates; copied
trials do not add committed exchange receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem product_stop (e : Stop) : ProductPreserves (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run

theorem product_work (f : List PeerId → List PeerId) : ProductPreserves
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _ (modify_device (fun d => {d with txWorkQueue := f d.txWorkQueue}) (fun _ => rfl))

theorem product_tx_read (id : SkbId) : ProductPreserves
    (liftPrefix (liftWG (getTxSkb id))) := by
  apply product_native
  exact skb (SkbStore.getTx id)

theorem crypt_ahead (pid : PeerId) :
    ProductPreserves (Driver.cryptAheadObserved ExchangeDriver.hooks pid) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration)
    | (nonce_product_head liftPrefix; first
       | with_reducible exact product_native _ (read_peer _)
       | exact product_tx_read _
       | with_reducible exact product_work (fun q => q ++ [pid])
       | with_reducible exact product_work (fun q => q.erase pid))
    | (nonce_product_head liftPrefix; first | exact product_ambient _ | with_reducible exact product_stop _)
    | (nonce_product_head Pure.pure; exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iteration (a : Activation) :
    ProductPreserves (Driver.iterationObserved ExchangeDriver.hooks a) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | (nonce_product_head liftPrefix; first | exact product_ambient _ | with_reducible exact product_stop _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule (stack : Option Worker) :
    ProductPreserves (Driver.scheduleObserved ExchangeDriver.hooks stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.1) product_stable
    (fun pid => product_work (fun q => q.erase pid)) _ _ (iteration) (softirq) stack

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
