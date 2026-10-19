import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionWorkers
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionSchedulerFrames

/-! Source composition through the actual draining scheduler. Committed
worker iterations retain their receipts; consistency trials discard their
copied state exactly as the native scheduler does. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity Queues
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem product_throw (stop : Stop) : ProductSafe (liftPrefix (throw stop : Leanux.M α)) := by
  intro w h _
  exact ⟨[],by simp,True.intro,True.intro⟩

macro "emission_scheduler_native" : tactic => `(tactic| first
  | (emission_product_native_head liftWG
     apply product_wg
     apply state_native
     try simp only [getTxSkb]
     sent_frame [] using [skb_sent_spec,getPeer_sent_spec,setPeer_sent_spec])
  | ((first
       | emission_product_native_head getAmbient
       | emission_product_native_head modifyAmbient
       | emission_product_native_head peekHiddenSite
       | emission_product_native_head hidden
       | emission_product_native_head peekUnit
       | emission_product_native_head resolveUnit
       | emission_product_native_head recordBudget
       | emission_product_native_head budgetExhausted
       | emission_product_native_head unsupported
       | emission_product_native_head invariant)
     exact product_ambient _)
  | (emission_product_native_head throw; exact product_throw _))

theorem crypt_ahead (pid : PeerId) : ProductSafe (Driver.cryptAheadObserved hooks pid) := by
  unfold Driver.cryptAheadObserved
  try simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (emission_head Driver.encryptIterObserved; exact encrypt_iter)
    | solve | emission_scheduler_native
    | emission_product_step

theorem iteration (activation : Activation) : ProductSafe (Driver.iterationObserved hooks activation) := by
  unfold Driver.iterationObserved
  repeat' first
    | (emission_head Driver.encryptIterObserved; exact encrypt_iter)
    | (emission_head Driver.decryptIterObserved; exact decrypt_iter)
    | (emission_head Driver.receiveIterObserved; exact receive_iter)
    | (emission_head Driver.txIterObserved; exact tx_iter _)
    | (emission_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | solve | emission_scheduler_native
    | emission_product_step

theorem scheduler_run (activation : Activation) : ProductSafe (SourceScheduler.run (Driver.iterationObserved hooks) activation) := by
  unfold SourceScheduler.run
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (emission_head Driver.iterationObserved; exact iteration _)
    | (emission_product_native_head Env.Activation.occupancy; exact product_native _ (EmissionFrames.occupancy _))
    | solve | emission_scheduler_native
    | emission_product_step

theorem scheduler_dispatch (worker : Worker) : ProductSafe (SourceScheduler.dispatch (Driver.iterationObserved hooks) worker) := by
  unfold SourceScheduler.dispatch
  repeat' first
    | (emission_head SourceScheduler.run; exact scheduler_run _)
    | solve | emission_scheduler_native
    | emission_product_step

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved hooks stack) := by
  unfold Driver.scheduleObserved SourceScheduler.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (emission_head SourceScheduler.run; exact scheduler_run _)
    | (emission_head SourceScheduler.dispatch; exact scheduler_dispatch _)
    | (emission_head Driver.softirqObserved; exact softirq)
    | (emission_product_native_head Lifetimes.pendingNapi; exact product_native _ (EmissionFrames.pending_napi _))
    | (emission_product_native_head Env.Activation.hasWork; exact product_native _ (EmissionFrames.has_work _))
    | (emission_product_native_head List.filterM; exact product_native _
        (filterM_sameKernel EmissionOuter.Sent _ EmissionFrames.consistent _))
    | solve | emission_scheduler_native
    | emission_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
