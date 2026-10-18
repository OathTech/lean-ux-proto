import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHandshake

/-! The actual source scheduler commits worker and NAPI callbacks to one
responder journal. Copied consistency trials do not create committed receipts. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem product_stop (e : Stop) : ProductPreserves (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  intro confirmed
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run

theorem product_work (f : List PeerId → List PeerId) : ProductPreserves
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _ (carrier_modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

theorem product_tx_read (id : SkbId) : ProductPreserves
    (liftPrefix (liftWG (getTxSkb id))) := by
  apply product_native
  intro confirmed
  exact carrier_skb (SkbStore.getTx id) confirmed

theorem crypt_ahead (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    ProductPreserves (Driver.cryptAheadObserved hooks pid) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration H1)
    | (nonce_product_head liftPrefix; first
       | with_reducible exact product_native _ (carrier_read_peer _)
       | exact product_tx_read _
       | with_reducible exact product_work (fun q => q ++ [pid])
       | with_reducible exact product_work (fun q => q.erase pid))
    | (nonce_product_head liftPrefix; first | exact product_ambient _ | with_reducible exact product_stop _)
    | (exact product_tx_read _)
    | exact product_pure _
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iteration (H1 : H1ResponderCurrentEdges) (a : Activation) :
    ProductPreserves (Driver.iterationObserved hooks a) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration H1)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration H1)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration H1)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead H1 _)
    | (nonce_product_head liftPrefix; first | exact product_ambient _ | with_reducible exact product_stop _)
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule (H1 : H1ResponderCurrentEdges) (stack : Option Worker) :
    ProductPreserves (Driver.scheduleObserved hooks stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.2) product_stable
    (fun pid => product_work (fun q => q.erase pid)) _ _ (iteration H1) (softirq H1) stack

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
