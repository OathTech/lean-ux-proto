import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedWorkers

/-! The real draining scheduler retains the live delayed-effect carrier.
Copied consistency trials are the original SourceScheduler tests; committed
worker iterations run on the same final journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem product_throw (err : Stop) : ProductSafe (liftPrefix (throw err : Leanux.M α)) := by
  intro w h _
  exact ⟨[],by simp,True.intro,True.intro⟩

macro "causal_delayed_scheduler_native" : tactic => `(tactic| first
  | (causal_delayed_product_native liftWG
     apply product_wg
     first
     | (causal_delayed_native_head getTxSkb; unfold getTxSkb; exact skb _)
     | solve | causal_delayed_native)
  | (first
     | causal_delayed_product_native getAmbient
     | causal_delayed_product_native modifyAmbient
     | causal_delayed_product_native peekHiddenSite
     | causal_delayed_product_native invariant
     exact product_ambient _)
  | (causal_delayed_product_native throw; exact product_throw _))

theorem crypt_ahead (pid : PeerId) : ProductSafe (Driver.cryptAheadObserved hooks pid) := by
  unfold Driver.cryptAheadObserved
  repeat' first
    | (causal_delayed_head Driver.encryptIterObserved; exact encrypt_iter)
    | solve | causal_delayed_scheduler_native
    | causal_delayed_product_step

theorem iteration (activation : Activation) : ProductSafe (Driver.iterationObserved hooks activation) := by
  unfold Driver.iterationObserved
  repeat' first
    | (causal_delayed_head Driver.encryptIterObserved; exact encrypt_iter)
    | (causal_delayed_head Driver.decryptIterObserved; exact decrypt_iter)
    | (causal_delayed_head Driver.receiveIterObserved; exact receive_iter)
    | (causal_delayed_head Driver.txIterObserved; exact tx_iter _)
    | (causal_delayed_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | solve | causal_delayed_scheduler_native
    | causal_delayed_product_step

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved hooks stack) := by
  apply SourceScheduler.schedule_preserves (I := fun h w => Inv h w.wg)
    (fun _ _ _ => True.intro) product_store
  · intro pid
    apply product_wg
    causal_delayed_native
  · exact iteration
  · exact softirq

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
