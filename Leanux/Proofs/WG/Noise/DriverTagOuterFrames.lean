import Leanux.Proofs.WG.Noise.DriverTagScheduledSource
import Leanux.Proofs.WG.Noise.PendingOuterSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Outer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Leanux.Proofs.WG.Configuration

theorem lift_fs {α : Type} (entry : TagMap) (a : FS.M α) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (liftFS a)) :=
  lift_product_frame entry _ (fun s => productFS_spec a (fun w => tagView w.wg = s)
    (fun _ _ _ _ hi => hi))

theorem lift_task {α : Type} (entry : TagMap) (a : TaskM α) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (liftTask a)) :=
  lift_product_frame entry _ (fun s => productTask_spec a (fun w => tagView w.wg = s)
    (fun _ _ _ hi => hi))

theorem lift_seccomp {α : Type} (entry : TagMap) (a : Seccomp.M α) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (liftSeccomp a)) :=
  lift_product_frame entry _ (fun s => productSeccomp_spec a (fun w => tagView w.wg = s)
    (fun _ _ _ _ hi => hi))

theorem lift_ambient {α : Type} (entry : TagMap) (a : AmbientM α) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (liftAmbient a)) :=
  lift_product_frame entry _ (fun s => productAmbient_spec a (fun w => tagView w.wg = s)
    (fun _ _ hi => hi))

theorem lift_modify (entry : TagMap) (f : World → World)
    (same : ∀ w, tagView (f w).wg = tagView w.wg) :
    PrefixPreserves (StateInv entry) ValidHistory (liftPrefix (modify f)) :=
  lift_product_frame entry _ (fun s => hoare_modify (P := fun w => tagView w.wg = s)
    f (fun w hi => (same w).trans hi))

theorem lift_get (entry : TagMap) : PrefixPreserves (StateInv entry) ValidHistory
    (liftPrefix (get : Leanux.M World)) :=
  lift_product_frame entry _ (fun _ => hoare_consequence (hoare_get _)
    (fun _ hi => hi) (fun _ _ hi => hi.2))

end Leanux.Proofs.WG.Noise.DriverTags.Outer

