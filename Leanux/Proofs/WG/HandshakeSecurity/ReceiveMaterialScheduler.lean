import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialHandshake
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverControl

/-! The actual scheduler retains RX allocation certificates across every committed
worker callback; consistency trials on copied states do not emit receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem product_stop (e : Stop) : ProductSafe (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run

theorem product_work (f : List PeerId → List PeerId) : ProductSafe
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _
    (fun _ => bounded_modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

theorem product_tx_read (id : SkbId) : ProductSafe (liftPrefix (liftWG (getTxSkb id))) :=
  product_native _ (fun _ => bounded_tx_read id)

theorem crypt_ahead (pid : PeerId) :
    ProductSafe (Driver.cryptAheadObserved Journal.hooks pid) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration)
    | (scheduler_preserve_at getPeer; exact product_native _ (fun _ => bounded_read_peer _))
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

theorem iteration (a : Activation) : ProductSafe (Driver.iterationObserved Journal.hooks a) := by
  change PrefixPreserves (fun h (w : World) => Carrier h w.wg) Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | (scheduler_preserve_at invariant; exact product_ambient _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | origin_carrier_join_let
    | origin_carrier_join_use
    | maintenance_intro
    | origin_carrier_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved Journal.hooks stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.2) product_stable
    (fun pid => product_work (fun q => q.erase pid)) _ _ iteration softirq stack

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
