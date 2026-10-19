import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEnvironmentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSourceClosed

/-! Actual environment lifecycle wrappers retain paired accounting. The device
destructor contract is explicit pending initialized reset quiescence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal Driver HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "complete_environment_step " destructor:term : tactic => `(tactic| first
  | (complete_product_head upObserved; exact state up)
  | (complete_product_head downObserved; exact state down)
  | (complete_product_head destructObserved; exact state $destructor)
  | (complete_product_native Env.requireIdleDevice; exact idle_device)
  | (complete_product_native Env.inetdevDestroy; exact inetdev)
  | (complete_product_native modifyEnv; exact env_edit _)
  | (first | complete_product_native Net.Fib.rtCacheFlush | complete_product_native Net.Fib.netdevUp
           | complete_product_native Net.Fib.netdevDown | complete_product_native Net.Fib.netdevUnregister
           | complete_product_native modifyRouting
     exact routing _)
  | (complete_product_native liftM; exact routing _)
  | (complete_product_native liftWG; first
     | exact wg _ (state_store _ getDev_sameWGStore)
     | exact wg _ (state_store _ mayHaveSlept_sameWGStore))
  | (complete_product_native skipCut; exact ambient _)
  | dsimp (config := {failIfUnchanged := true}) only
  | complete_deferred_native
  | complete_product_step)

theorem env_up : Checked (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' complete_environment_step (by assumption)

theorem env_down : Checked (envDownObserved hooks) := by
  unfold envDownObserved SendExchange.envDownWith
  repeat' complete_environment_step (by assumption)

theorem env_delete (destructor : StateChecked (destructObserved hooks)) : Checked (envDeleteObserved hooks) := by
  unfold envDeleteObserved SendExchange.envDeleteWith Configuration.envDeleteWith
  dsimp only
  repeat' complete_environment_step destructor

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
