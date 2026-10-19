import Leanux.Proofs.WG.HandshakeSecurity.ExchangeLifecycle

/-! The environment's up/down/delete callers retain the same native exchange
history across routing notifications and actual shutdown/destruction. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem open_checked (facts : H1DriverSourceFacts) :
    Preserves (Driver.openObserved ExchangeDriver.hooks) := by
  unfold Driver.openObserved
  rw [show Driver.fixtureOps ExchangeDriver.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.open_neutral]
  unfold AuthenticatedEffects.FixtureEffects.openWith
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging_checked facts.data _)
    | (nonce_source_head Driver.keepaliveObserved; exact keepalive_checked facts.data _)
    | (nonce_source_head socketInit; exact lift _ (fun h => socket_frame h _ (socketInit_sameSocket _)))
    | exchange_removal_step facts

theorem up_checked (facts : H1DriverSourceFacts) :
    Preserves (Driver.upObserved ExchangeDriver.hooks) := by
  unfold Driver.upObserved
  repeat' first
    | (nonce_source_head Driver.openObserved; exact open_checked facts)
    | exchange_removal_step facts

theorem product_routing (action : Net.M α) :
    ProductPreserves (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store _ (fun initial => productRouting_spec action (fun s => s = initial))

theorem product_env_edit (f : EnvWorld → EnvWorld) :
    ProductPreserves (liftPrefix (modifyEnv f)) := by
  apply product_store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem idle_device_checked : ProductPreserves (liftPrefix Env.requireIdleDevice) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  rw [(RxCredits.idleDevice_normal w v run).1]
  exact hi

theorem inetdev_checked : ProductPreserves (liftPrefix Env.inetdevDestroy) :=
  product_store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store)

macro "exchange_environment_step " facts:term : tactic => `(tactic| first
  | unfold ProductPreserves
  | (scheduler_preserve_at Driver.upObserved; exact product_state (up_checked $facts))
  | (scheduler_preserve_at Driver.downObserved; exact product_state (down_checked $facts))
  | (scheduler_preserve_at Driver.destructObserved; exact product_state (destruct_checked $facts))
  | (scheduler_preserve_at Env.requireIdleDevice; exact idle_device_checked)
  | (scheduler_preserve_at Env.inetdevDestroy; exact inetdev_checked)
  | (scheduler_preserve_at liftM; exact product_routing _)
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at modifyEnv; exact product_env_edit _)
  | (scheduler_preserve_at getDev; exact product_native _ (fun h => frame_store h _ getDev_sameWGStore))
  | (scheduler_preserve_at mayHaveSlept; exact product_native _ (fun h => frame_store h _ mayHaveSlept_sameWGStore))
  | (first | scheduler_preserve_at Net.Fib.rtCacheFlush | scheduler_preserve_at Net.Fib.netdevUp
           | scheduler_preserve_at Net.Fib.netdevDown | scheduler_preserve_at Net.Fib.netdevUnregister
           | scheduler_preserve_at modifyRouting
     exact product_routing _)
  | (first | scheduler_preserve_at skipCut | scheduler_preserve_at unsupported
     exact product_ambient _)
  | (first | nonce_product_head Pure.pure | nonce_product_head pure
     exact product_pure _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | (with_reducible split))

theorem env_up_checked (facts : H1DriverSourceFacts) :
    ProductPreserves (Driver.envUpObserved ExchangeDriver.hooks) := by
  unfold Driver.envUpObserved
  repeat' exchange_environment_step facts

theorem env_down_checked (facts : H1DriverSourceFacts) :
    ProductPreserves (Driver.envDownObserved ExchangeDriver.hooks) := by
  unfold Driver.envDownObserved SendExchange.envDownWith
  repeat' exchange_environment_step facts

theorem env_delete_checked (facts : H1DriverSourceFacts) :
    ProductPreserves (Driver.envDeleteObserved ExchangeDriver.hooks) := by
  unfold Driver.envDeleteObserved SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' exchange_environment_step facts

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
