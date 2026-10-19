import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverControl
import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionWorkers

/-! The actual source scheduler commits worker and NAPI callbacks to one
responder journal. Copied consistency trials do not create committed receipts. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)

/-- Aggregation of explicitly cited local C2 effects; it contains no initialized
claim, no reachability assumption, and no event-history premise. -/
structure H1WorkerFrames : Prop where
  edges : H1PendingPromotionEdges
  quiet : H1PendingQuietFrames
  poll : H1PendingPollFrames
  stack : H1PendingStackFrames
  handshake : H1PendingHandshakeFrames
  publication : H1PublicationFrame
  transmit : H1TransmitFrames

theorem product_stop (e : Stop) : ProductPreserves (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  intro confirmed
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run

theorem product_work (f : List PeerId → List PeerId) : ProductPreserves
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _ (Carrier.modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

theorem product_tx_read (id : SkbId) : ProductPreserves
    (liftPrefix (liftWG (getTxSkb id))) := by
  apply product_native
  intro confirmed
  exact Carrier.skb confirmed (SkbStore.getTx id)

theorem crypt_ahead (facts : H1WorkerFrames) (pid : PeerId) :
    ProductPreserves (Driver.cryptAheadObserved hooks pid) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration facts.edges facts.quiet facts.poll facts.stack facts.publication)
    | (scheduler_preserve_at getPeer; exact product_native _ (fun confirmed => hoare_consequence (Carrier.get_peer confirmed _) (fun _ hi => hi) (fun _ _ hi => hi.1)))
    | (scheduler_preserve_at getTxSkb; exact product_tx_read _)
    | (scheduler_preserve_at modifyDev; first
       | exact product_work (fun q => q ++ [pid])
       | exact product_work (fun q => q.erase pid))
    | (scheduler_preserve_at throw; exact product_stop _)
    | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
             | scheduler_preserve_at peekHiddenSite | scheduler_preserve_at invariant
       exact product_ambient _)
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | origin_carrier_join_let
    | origin_carrier_join_use
    | maintenance_intro
    | origin_carrier_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iteration (facts : H1WorkerFrames) (a : Activation) : ProductPreserves (Driver.iterationObserved hooks a) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration facts.edges facts.quiet facts.poll facts.stack facts.publication)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration facts.edges facts.quiet facts.poll facts.stack)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration facts.edges facts.quiet facts.handshake)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration facts.transmit facts.handshake _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead facts _)
    | (scheduler_preserve_at invariant; exact product_ambient _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | origin_carrier_join_let
    | origin_carrier_join_use
    | maintenance_intro
    | origin_carrier_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule (facts : H1WorkerFrames) (stack : Option Worker) :
    ProductPreserves (Driver.scheduleObserved hooks stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.2.2.distinct) product_stable
    (fun pid => product_work (fun q => q.erase pid)) _ _ (iteration facts) (softirq facts.edges facts.quiet facts.poll facts.stack) stack

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
