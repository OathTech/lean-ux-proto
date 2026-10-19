import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceLifecycle

/-! The environment's up/down/delete callers retain the same native exchange
history across routing notifications and actual shutdown/destruction. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option pp.structureInstances false

theorem open_observed :
    Observed (E := E) (Driver.openObserved EntrySource.hooks (E := E)) := by
  unfold Driver.openObserved
  rw [show Driver.fixtureOps EntrySource.hooks (E := E) = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.open_neutral]
  unfold AuthenticatedEffects.FixtureEffects.openWith
  repeat' first
    | (nonce_source_head Driver.stagingObserved; exact staging _)
    | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
    | (nonce_source_head socketInit; exact lift _ (socket (socketInit_sameSocket _)))
    | peer_reference_removal_step

theorem up_observed :
    Observed (E := E) (Driver.upObserved EntrySource.hooks (E := E)) := by
  unfold Driver.upObserved
  repeat' first
    | (nonce_source_head Driver.openObserved; exact open_observed)
    | peer_reference_removal_step

theorem product_routing (action : Net.M α) :
    ProductPreserves (E := E) (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store _ (fun initial => productRouting_spec action (fun s => s = initial))

theorem product_env_edit (f : EnvWorld → EnvWorld) :
    ProductPreserves (E := E) (liftPrefix (modifyEnv f)) := by
  apply product_store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem idle_device_observed : ProductPreserves (E := E) (liftPrefix Env.requireIdleDevice) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  rw [(RxCredits.idleDevice_normal w v run).1]
  exact hi

theorem inetdev_observed : ProductPreserves (E := E) (liftPrefix Env.inetdevDestroy) :=
  product_store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store)

macro "peer_reference_environment_step" : tactic => `(tactic| first
  | unfold ProductPreserves
  | (scheduler_preserve_at Driver.upObserved; exact product_safe (up_observed))
  | (scheduler_preserve_at Driver.downObserved; exact product_safe (down_observed))
  | (scheduler_preserve_at Driver.destructObserved; exact product_safe (destruct_observed))
  | (scheduler_preserve_at Env.requireIdleDevice; exact idle_device_observed)
  | (scheduler_preserve_at Env.inetdevDestroy; exact inetdev_observed)
  | (scheduler_preserve_at liftM; exact product_routing _)
  | (scheduler_preserve_at getWG; exact wg_read)
  | (scheduler_preserve_at modifyEnv; exact product_env_edit _)
  | (scheduler_preserve_at getDev; exact product_native _ (store getDev_sameWGStore))
  | (scheduler_preserve_at mayHaveSlept; exact product_native _ (store mayHaveSlept_sameWGStore))
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

theorem env_up_observed :
    ProductPreserves (E := E) (Driver.envUpObserved EntrySource.hooks (E := E)) := by
  unfold Driver.envUpObserved
  repeat' peer_reference_environment_step

theorem env_down_observed :
    ProductPreserves (E := E) (Driver.envDownObserved EntrySource.hooks (E := E)) := by
  unfold Driver.envDownObserved SendExchange.envDownWith
  repeat' peer_reference_environment_step

theorem env_delete_observed :
    ProductPreserves (E := E) (Driver.envDeleteObserved EntrySource.hooks (E := E)) := by
  unfold Driver.envDeleteObserved SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' peer_reference_environment_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
