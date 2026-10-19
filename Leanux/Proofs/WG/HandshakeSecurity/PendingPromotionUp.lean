import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionEnvironment

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

open Responder.DriverCuts (hooks)

theorem loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Event (ForInStep β))
    (hg : ∀ x b, Observed (g x b)) : Observed (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => StateInv h w) Safe
    (fun _ _ _ _ hi => hi.2.2.distinct) hg

macro "pending_driver_up_step " quiet:term : tactic => `(tactic| first
  | unfold Observed StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | (nonce_source_head Driver.stagingObserved; exact staging $quiet _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive $quiet _)
  | (nonce_source_head socketInit; exact native _ (Carrier.socket (socketInit_sameSocket _)))
  | (nonce_source_head getPeer; exact native _ (fun labels => hoare_consequence (Carrier.get_peer labels _) (fun _ hi => hi) (fun _ _ hi => hi.1)))
  | (nonce_source_head getDev; exact native _ (fun labels => Carrier.store labels getDev_sameWGStore))
  | (nonce_source_head modifyDev
     apply native
     intro confirmed
     apply Carrier.modify_device
     all_goals (intro d; rfl))
  | (nonce_source_head branch; exact ambient _)
  | (nonce_source_head Pure.pure; exact pure _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn; apply loop)
  | maintenance_intro
  | (with_reducible split))

theorem open_device (quiet : H1PendingQuietFrames) : Observed (Driver.openObserved hooks) := by
  unfold Driver.openObserved
  rw [show Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.open_neutral]
  unfold AuthenticatedEffects.FixtureEffects.openWith
  repeat' pending_driver_up_step quiet

theorem up_device (quiet : H1PendingQuietFrames) : Observed (Driver.upObserved hooks) := by
  unfold Driver.upObserved
  repeat' first
    | (nonce_source_head Driver.openObserved; exact open_device quiet)
    | pending_driver_up_step quiet

theorem env_up (facts : H1DeferredFrames) : ProductPreserves (Driver.envUpObserved hooks) := by
  change PrefixPreserves ProductInv Safe _
  have route {α : Type} (a : Net.M α) :
      ProductPreserves (liftPrefix (monadLift a : Leanux.M α)) :=
    product_store _ (fun s => productRouting_spec a (fun t => t = s))
  have edit (f : EnvWorld → EnvWorld) : ProductPreserves (liftPrefix (modifyEnv f)) :=
    product_lift _ (fun _ => by unfold modifyEnv; apply hoare_modify; exact fun _ hi => hi)
  unfold Driver.envUpObserved
  repeat' first
    | (nonce_product_head liftWGObserver; exact product_safe (up_device facts.worker.quiet))
    | (scheduler_preserve_at modifyEnv; exact edit _)
    | (scheduler_preserve_at liftM; exact route _)
    | (scheduler_preserve_at skipCut; exact product_ambient _)
    | pending_driver_deferred_step facts

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
