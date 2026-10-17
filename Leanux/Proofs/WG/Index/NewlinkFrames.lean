import Leanux.Proofs.WG.Index.LifecycleModel
import Leanux.Proofs.WG.Noise.ComponentFrames
import Leanux.WG.Device

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Concrete within-WireGuard preservation support for newlink. The public
claims use the campaign snapshot; no unrelated subsystem is part of the invariant. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def TablesSafeWG (g : WGWorld) : Prop :=
  ∀ d, g.dev = some d → DeviceTablesSafe d

theorem cookieCheckerInit_tables :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ cookieCheckerInit
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold cookieCheckerInit
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.hiddenClock64 .cookieSecretBirthdate) TablesSafeWG)) ?_
  intro birth
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.hidden .cookieSecret) TablesSafeWG)) ?_
  intro secret g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with cookieSecretBirthdate := birth, cookieSecret := secret})}), ambient) = _ at run
  cases run
  intro final present
  cases device : g.dev with
  | none => simp [device] at present
  | some d =>
    simp only [device, Option.map_some, Option.some.injEq] at present
    subst final
    exact pre d device

theorem pubkeyHashtableAlloc_tables :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ pubkeyHashtableAlloc
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold pubkeyHashtableAlloc
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.envOk .pubkeyHashtableAlloc) TablesSafeWG)) ?_
  intro ok
  cases ok with
  | false =>
    intro g ambient result final after pre run
    cases run
    exact pre
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
      ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.hidden .pubkeyHashKey) TablesSafeWG)) ?_
    intro key
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
    · intro g ambient result final after pre run
      change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
        {d with pubkeyHashKey := key})}), ambient) = _ at run
      cases run
      intro final present
      cases device : g.dev with
      | none => simp [device] at present
      | some d =>
        simp only [device, Option.map_some, Option.some.injEq] at present
        subst final
        exact pre d device
    · intro u g ambient result final after pre run
      cases run
      exact pre

theorem ratelimiterInit_tables :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ ratelimiterInit
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  have hmodify (f : WGWorld → WGWorld) (same : ∀ g, (f g).dev = g.dev) :
      Ensures (modify f : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    intro d device
    exact pre d ((same g).symm.trans device)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.branch site value) TablesSafeWG)
  have hpure (value : Int) : Ensures (pure value : WG.M Int) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hundo : Ensures (do
      modify fun g : WGWorld => {g with ratelimiter := {g.ratelimiter with refcnt := g.ratelimiter.refcnt - 1}}
      pure (-ENOMEM : Int)) TablesSafeWG (fun _ => TablesSafeWG) :=
    ensures_bind _ _ (hmodify _ (fun _ => rfl)) (fun _ => hpure _)
  unfold ratelimiterInit
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hmodify _ (fun _ => rfl)) ?_
  intro _
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
  · intro g ambient result final after pre run
    cases run
    exact pre
  · intro current
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro notFirst
    cases notFirst with
    | true => exact hpure 0
    | false =>
      refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
      intro cacheError
      cases cacheError with
      | true => exact hundo
      | false =>
        refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
        intro v4Error
        cases v4Error with
        | true => exact hundo
        | false =>
          refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
          intro v6Error
          cases v6Error with
          | true => exact hundo
          | false =>
            refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
              ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
                (AmbientM.hidden .ratelimiterKey) TablesSafeWG)) ?_
            intro key
            exact ensures_bind _ _ (hmodify _ (fun _ => rfl)) (fun _ => hpure 0)

end Leanux.Proofs.WG.Index
