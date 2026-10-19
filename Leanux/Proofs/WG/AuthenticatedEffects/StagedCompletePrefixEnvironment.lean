import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixEnvironmentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationConcrete

/-! Actual opening and shutdown wrappers retain every logical prefix beside
the complete native carrier. Guarded deletion has its own stronger entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal Driver HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "prefix_environment_step " destructor:term : tactic => `(tactic| first
  | (prefix_product_head upObserved; exact state ConfigurationConcrete.up)
  | (prefix_product_head downObserved; exact state ConfigurationConcrete.down)
  | (prefix_product_head destructObserved; exact state $destructor)
  | (prefix_product_native Env.requireIdleDevice; exact idle_device)
  | (prefix_product_native Env.inetdevDestroy; exact inetdev)
  | (prefix_product_native modifyEnv; exact env_edit _)
  | (first | prefix_product_native Net.Fib.rtCacheFlush | prefix_product_native Net.Fib.netdevUp
           | prefix_product_native Net.Fib.netdevDown | prefix_product_native Net.Fib.netdevUnregister
           | prefix_product_native modifyRouting
     exact routing _)
  | (prefix_product_native liftM; exact routing _)
  | (prefix_product_native liftWG; first
     | exact wg _ (state_store _ getDev_sameWGStore)
     | exact wg _ (state_store _ mayHaveSlept_sameWGStore))
  | (prefix_product_native skipCut; exact ambient _)
  | dsimp (config := {failIfUnchanged := true}) only
  | prefix_deferred_native
  | prefix_product_step)

theorem env_up : Checked (envUpObserved hooks) := by
  unfold envUpObserved
  repeat' prefix_environment_step (by assumption)

theorem env_down : Checked (envDownObserved hooks) := by
  unfold envDownObserved SendExchange.envDownWith
  repeat' prefix_environment_step (by assumption)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
