import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionDumpFrames
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration CurrentEnvironment

private theorem safe (h : List Event) (w : World) (hi : ProductInv h w) :
    Safe h := hi.2.2.distinct

theorem store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v :=
  product_wg_stable h w v same hi

theorem lift_spec (a : Leanux.M α)
    (ha : ∀ h, Framing.Preserves (ProductInv h) a) : ProductPreserves (liftPrefix a) :=
  (PrefixEnsures.lift a safe (fun h w x v hi hr => (hoare_iff_run _ _ _).mp (ha h) w x v hi hr)).preserves

theorem lift_store (a : Leanux.M α) (ha : SameProductStore a) :
    ProductPreserves (liftPrefix a) := product_store a ha

theorem lift_wgStore (a : Leanux.M α)
    (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    ProductPreserves (liftPrefix a) := by
  apply lift_spec
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact store h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem lift_fs (a : FS.M α) : ProductPreserves (liftPrefix (liftFS a)) :=
  lift_spec _ (fun h => productFS_spec a (ProductInv h) (fun w _ _ _ hi => store h w _ rfl hi))

theorem lift_task (a : TaskM α) : ProductPreserves (liftPrefix (liftTask a)) :=
  lift_spec _ (fun h => productTask_spec a (ProductInv h) (fun w _ _ hi => store h w _ rfl hi))

theorem lift_ambient (a : AmbientM α) : ProductPreserves (liftPrefix (liftAmbient a)) :=
  lift_spec _ (fun h => productAmbient_spec a (ProductInv h) (fun w _ hi => store h w _ rfl hi))

theorem lift_seccomp (a : Seccomp.M α) : ProductPreserves (liftPrefix (liftSeccomp a)) :=
  lift_spec _ (fun h => productSeccomp_spec a (ProductInv h) (fun w _ _ _ hi => store h w _ rfl hi))

theorem lift_get : ProductPreserves (liftPrefix (get : Leanux.M World)) :=
  lift_spec _ (fun _ => hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))

theorem lift_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    ProductPreserves (liftPrefix (modify f)) :=
  lift_spec _ (fun h => hoare_modify _ (fun w hi => store h w (f w) (same w) hi))

macro "pending_driver_outer_step" : tactic => `(tactic| first
  | (change PrefixPreserves ProductInv Safe _; current_env_at unsupported; exact lift_ambient (AmbientM.unsupported _))
  | (change PrefixPreserves ProductInv Safe _; current_env_at skipCut; exact lift_ambient (AmbientM.skipCut _))
  | (change PrefixPreserves ProductInv Safe _; current_env_at liftPrefix; first
      | exact lift_fs _
      | exact lift_task _
      | exact lift_ambient _
      | exact lift_seccomp _
      | exact lift_get
      | exact lift_modify _ (fun _ => rfl))
  | (change PrefixPreserves ProductInv Safe _; current_env_at Pure.pure; exact PrefixPreserves.pure safe _)
  | (change PrefixPreserves ProductInv Safe _; current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (change PrefixPreserves ProductInv Safe _; current_env_at ite; apply PrefixPreserves.ite)
  | (change PrefixPreserves ProductInv Safe _; current_env_at dite; split)
  | (maintenance_intro; try dsimp only)
  | (change PrefixPreserves ProductInv Safe _; current_env_match))

/-- The callback is an arbitrary actual product observer, including its Stops.
Descriptor failure returns before calling it, exactly as in the source. -/
theorem socketCallOn (fd : Nat) (body : PrefixM Event Int)
    (hb : ProductPreserves body) :
    ProductPreserves (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves ProductInv Safe _
  unfold socketCallOnWith
  apply PrefixPreserves.bind (lift_fs (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _
    exact hb.bind (fun ret => (lift_fs (fdput f)).bind (fun _ => PrefixPreserves.pure safe ret))

theorem netlinkRequest (body : PrefixM Event Int) (hb : ProductPreserves body) :
    ProductPreserves (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind
    (socketCallOn _ _ ((lift_ambient (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (lift_ambient (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure safe ret)))))
  intro ret
  exact (socketCallOn _ _ (PrefixPreserves.pure safe 0)).bind (fun _ => PrefixPreserves.pure safe ret)

theorem rtnetlinkRequest (body : PrefixM Event Int) (hb : ProductPreserves body) :
    ProductPreserves (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves ProductInv Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (change PrefixPreserves ProductInv Safe _; current_env_at socketCallOnWith; apply socketCallOn)
    | pending_driver_outer_step


end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion.Outer
