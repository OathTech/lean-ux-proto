import Leanux.Proofs.WG.TransmitSecurity.NonceOuterFrames
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Exact descriptor wrappers for nonce observers. Foreign-subsystem leaves
retain the WG projection, and guarded callbacks keep failure histories. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration CurrentEnvironment

private theorem safe (h : List Allocation) (w : World) (hi : Inv (view w.wg) h) : List.Nodup h := hi.nodup

theorem lift_spec (a : Leanux.M α)
    (ha : ∀ h, Preserves ((fun (h : List Allocation) (w : World) => Inv (view w.wg) h) h) a) : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix a) :=
  (PrefixEnsures.lift a safe (fun h w x v hi hr => (hoare_iff_run _ _ _).mp (ha h) w x v hi hr)).preserves

theorem lift_store (a : Leanux.M α) (ha : SameProductStore a) :
    PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix a) := Frames.stored ha

theorem lift_wgStore (a : Leanux.M α)
    (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix a) := by
  apply lift_spec
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact Frames.wg_store h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem lift_fs (a : FS.M α) : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (liftFS a)) :=
  lift_spec _ (fun h => productFS_spec a ((fun (h : List Allocation) (w : World) => Inv (view w.wg) h) h) (fun w _ _ _ hi => Frames.wg_store h w _ rfl hi))

theorem lift_task (a : TaskM α) : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (liftTask a)) :=
  lift_spec _ (fun h => productTask_spec a ((fun (h : List Allocation) (w : World) => Inv (view w.wg) h) h) (fun w _ _ hi => Frames.wg_store h w _ rfl hi))

theorem lift_ambient (a : AmbientM α) : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (liftAmbient a)) :=
  lift_spec _ (fun h => productAmbient_spec a ((fun (h : List Allocation) (w : World) => Inv (view w.wg) h) h) (fun w _ hi => Frames.wg_store h w _ rfl hi))

theorem lift_seccomp (a : Seccomp.M α) : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (liftSeccomp a)) :=
  lift_spec _ (fun h => productSeccomp_spec a ((fun (h : List Allocation) (w : World) => Inv (view w.wg) h) h) (fun w _ _ _ hi => Frames.wg_store h w _ rfl hi))

theorem lift_get : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (get : Leanux.M World)) :=
  lift_spec _ (fun _ => hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))

theorem lift_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (liftPrefix (modify f)) :=
  lift_spec _ (fun h => hoare_modify _ (fun w hi => Frames.wg_store h w (f w) (same w) hi))

macro "nonce_outer_step" : tactic => `(tactic| first
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at unsupported; exact lift_ambient (AmbientM.unsupported _))
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at skipCut; exact lift_ambient (AmbientM.skipCut _))
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at liftPrefix; first
      | exact lift_fs _
      | exact lift_task _
      | exact lift_ambient _
      | exact lift_seccomp _
      | exact lift_get
      | exact lift_modify _ (fun _ => rfl))
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at Pure.pure; exact PrefixPreserves.pure safe _)
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at ite; apply PrefixPreserves.ite)
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at dite; split)
  | (maintenance_intro; try dsimp only)
  | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_match))

/-- The callback is an arbitrary actual product observer, including its Stops.
Descriptor failure returns before calling it, exactly as in the source. -/
theorem socketCallOn (fd : Nat) (body : PrefixM Allocation Int)
    (hb : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup body) :
    PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _
  unfold socketCallOnWith
  apply PrefixPreserves.bind (lift_fs (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _
    exact hb.bind (fun ret => (lift_fs (fdput f)).bind (fun _ => PrefixPreserves.pure safe ret))

theorem netlinkRequest (body : PrefixM Allocation Int) (hb : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup body) :
    PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind
    (socketCallOn _ _ ((lift_ambient (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (lift_ambient (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure safe ret)))))
  intro ret
  exact (socketCallOn _ _ (PrefixPreserves.pure safe 0)).bind (fun _ => PrefixPreserves.pure safe ret)

theorem rtnetlinkRequest (body : PrefixM Allocation Int) (hb : PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup body) :
    PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (change PrefixPreserves (fun (h : List Allocation) (w : World) => Inv (view w.wg) h) List.Nodup _; current_env_at socketCallOnWith; apply socketCallOn)
    | nonce_outer_step


theorem rtnetlinkRequest_erases {body : PrefixM Allocation Int} {a : Leanux.M Int}
    (hb : ErasesPrefix body a) :
    ErasesPrefix (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) (Leanux.rtnetlinkRequest a) := by
  rw [rtnetlinkRequest_factor]
  unfold rtnetlinkRequestWith
  repeat' first
    | with_reducible exact hb
    | (maintenance_head socketCallOnWith; apply socketCallOnWith_erases)
    | nonce_deferred_erasure

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Outer
