import Leanux.Proofs.WG.TransmitSecurity.StagedLifecycle
import Leanux.Proofs.WG.TransmitSecurity.StagedEnvironmentFrames

/-! Environment lifecycle callers carry staged origins across routing updates
and the actual observed up, down and destruction operations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

macro "staged_environment_step" : tactic => `(tactic| first
  | (staged_origin_product_head upObserved; exact product_state up)
  | (staged_origin_product_head downObserved; exact product_state down)
  | (staged_origin_product_head destructObserved; exact product_state destruct)
  | (staged_origin_product_native Env.requireIdleDevice; exact idle_device)
  | (staged_origin_product_native Env.inetdevDestroy; exact inetdev)
  | (staged_origin_product_native modifyEnv; exact product_env_edit _)
  | (first | staged_origin_product_native Net.Fib.rtCacheFlush | staged_origin_product_native Net.Fib.netdevUp
           | staged_origin_product_native Net.Fib.netdevDown | staged_origin_product_native Net.Fib.netdevUnregister
           | staged_origin_product_native modifyRouting
     exact product_routing _)
  | (staged_origin_product_native liftM; exact product_routing _)
  | (staged_origin_product_native liftWG; first
     | exact product_wg _ (state_lift _ (fun _ => Native.store getDev_sameWGStore))
     | exact product_wg _ (state_lift _ (fun _ => Native.store mayHaveSlept_sameWGStore)))
  | (staged_origin_product_native skipCut; exact product_ambient _)
  | dsimp (config := {failIfUnchanged := true}) only
  | staged_deferred_step)

theorem env_up : ProductSafe (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' staged_environment_step

theorem env_down : ProductSafe (envDownObserved hooks) := by
  unfold envDownObserved SendExchange.envDownWith
  repeat' staged_environment_step

theorem env_delete : ProductSafe (envDeleteObserved hooks) := by
  unfold envDeleteObserved SendExchange.envDeleteWith Configuration.envDeleteWith
  dsimp only
  repeat' staged_environment_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
