import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityLifecycle
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityEnvironmentFrames

/-! Environment lifecycle callers carry available staged births across routing updates
and the actual observed up, down and destruction operations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

macro "available_environment_step" : tactic => `(tactic| first
  | (available_origin_product_head upObserved; exact product_state up)
  | (available_origin_product_head downObserved; exact product_state down)
  | (available_origin_product_head destructObserved; exact product_state destruct)
  | (available_origin_product_native Env.requireIdleDevice; exact idle_device)
  | (available_origin_product_native Env.inetdevDestroy; exact inetdev)
  | (available_origin_product_native modifyEnv; exact product_env_edit _)
  | (first | available_origin_product_native Net.Fib.rtCacheFlush | available_origin_product_native Net.Fib.netdevUp
           | available_origin_product_native Net.Fib.netdevDown | available_origin_product_native Net.Fib.netdevUnregister
           | available_origin_product_native modifyRouting
     exact product_routing _)
  | (available_origin_product_native liftM; exact product_routing _)
  | (available_origin_product_native liftWG; first
     | exact product_wg _ (state_lift _ (fun _ => Native.store getDev_sameWGStore))
     | exact product_wg _ (state_lift _ (fun _ => Native.store mayHaveSlept_sameWGStore)))
  | (available_origin_product_native skipCut; exact product_ambient _)
  | dsimp (config := {failIfUnchanged := true}) only
  | available_deferred_step)

theorem env_up : ProductSafe (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' available_environment_step

theorem env_down : ProductSafe (envDownObserved hooks) := by
  unfold envDownObserved SendExchange.envDownWith
  repeat' available_environment_step

theorem env_delete : ProductSafe (envDeleteObserved hooks) := by
  unfold envDeleteObserved SendExchange.envDeleteWith Configuration.envDeleteWith
  dsimp only
  repeat' available_environment_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
