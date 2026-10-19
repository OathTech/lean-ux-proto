import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityWorkers

/-! The real draining scheduler retains the staged-origin carrier.
Copied consistency trials are the original SourceScheduler tests; committed
worker iterations run on the same final journal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open AuthenticatedEffects AuthenticatedEffects.CausalJournal Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem product_throw (err : Stop) : ProductSafe (liftPrefix (throw err : Leanux.M α)) := by
  intro w h before
  exact ⟨[],by simp,before.2,True.intro⟩

macro "available_scheduler_native" : tactic => `(tactic| first
  | (available_origin_product_native liftWG
     apply product_wg
     apply state_lift
     intro history
     repeat' first
       | (rx_retention_head getTxSkb; exact Native.skb _)
       | staged_available_native)
  | (first
     | available_origin_product_native getAmbient
     | available_origin_product_native modifyAmbient
     | available_origin_product_native peekHiddenSite
     | available_origin_product_native invariant
     exact product_ambient _)
  | (available_origin_product_native throw; exact product_throw _))

theorem crypt_ahead (pid : PeerId) : ProductSafe (Driver.cryptAheadObserved hooks pid) := by
  unfold Driver.cryptAheadObserved
  repeat' first
    | (available_origin_product_head Driver.encryptIterObserved; exact encrypt_iter)
    | solve | available_scheduler_native
    | available_origin_product_step

theorem iteration (activation : Activation) : ProductSafe (Driver.iterationObserved hooks activation) := by
  unfold Driver.iterationObserved
  repeat' first
    | (available_origin_product_head Driver.encryptIterObserved; exact encrypt_iter)
    | (available_origin_product_head Driver.decryptIterObserved; exact decrypt_iter)
    | (available_origin_product_head Driver.receiveIterObserved; exact receive_iter)
    | (available_origin_product_head Driver.txIterObserved; exact tx_iter _)
    | (available_origin_product_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | solve | available_scheduler_native
    | available_origin_product_step

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved hooks stack) := by
  apply SourceScheduler.schedule_preserves (I := fun h w => Carrier h w.wg)
    (fun _ _ before => before.2) product_stable
  · intro pid
    apply product_wg
    apply state_lift
    intro history
    repeat' staged_available_native
  · exact iteration
  · exact softirq

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
