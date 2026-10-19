import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialHandshake
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverControl

/-! The actual scheduler retains the material carrier across every committed
worker callback; consistency trials on copied states do not emit receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem product_stop (e : Stop) : ProductSafe (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  · intro h
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    cases run
  · apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    cases run

theorem product_work (f : List PeerId → List PeerId) : ProductSafe
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _
    (fun _ => NativeFrames.modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (bounds_forget (DriverCuts.carrier_modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))

theorem product_tx_read (id : SkbId) : ProductSafe (liftPrefix (liftWG (getTxSkb id))) :=
  product_native _ (fun _ => NativeFrames.read_packet id) (bounds_skb (SkbStore.getTx id))

theorem crypt_ahead_carrier (pid : PeerId) :
    ProductSafe (Driver.cryptAheadObserved Journal.hooks pid) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration_carrier)
    | (scheduler_preserve_at getPeer; exact product_native _ (fun _ => NativeFrames.read_peer _) (bounds_read_peer _))
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

theorem iteration_carrier (a : Activation) : ProductSafe (Driver.iterationObserved Journal.hooks a) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encrypt_iteration_carrier)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration_carrier)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration_carrier)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration_carrier _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead_carrier _)
    | (scheduler_preserve_at invariant; exact product_ambient _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | origin_carrier_join_let
    | origin_carrier_join_use
    | maintenance_intro
    | origin_carrier_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule_carrier (stack : Option Worker) : ProductSafe (Driver.scheduleObserved Journal.hooks stack) :=
  SourceScheduler.schedule_preserves (fun _ _ hi => hi.1.2) product_stable
    (fun pid => product_work (fun q => q.erase pid)) _ _ iteration_carrier softirq_carrier stack

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
