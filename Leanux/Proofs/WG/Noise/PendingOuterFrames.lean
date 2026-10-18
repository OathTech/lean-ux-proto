import Leanux.Proofs.WG.Noise.PendingSchedulerCompleteSource
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingOuter
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingSession

theorem lift_store {α : Type} (a : Leanux.M α)
    (same : SameView (fun w : World => wgStoreView w.wg) a) :
    PrefixPreserves StateInv HistorySafe (liftPrefix a) :=
  viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg)
    PendingScheduler.safe state_store same

theorem lift_fs {α : Type} (a : FS.M α) :
    PrefixPreserves StateInv HistorySafe (liftPrefix (liftFS a)) :=
  lift_store _ (fun s => productFS_spec a (fun w => wgStoreView w.wg = s)
    (fun _ _ _ _ hi => hi))

theorem lift_task {α : Type} (a : TaskM α) :
    PrefixPreserves StateInv HistorySafe (liftPrefix (liftTask a)) :=
  lift_store _ (fun s => productTask_spec a (fun w => wgStoreView w.wg = s)
    (fun _ _ _ hi => hi))

theorem lift_seccomp {α : Type} (a : Seccomp.M α) :
    PrefixPreserves StateInv HistorySafe (liftPrefix (liftSeccomp a)) :=
  lift_store _ (fun s => productSeccomp_spec a (fun w => wgStoreView w.wg = s)
    (fun _ _ _ _ hi => hi))

theorem lift_ambient {α : Type} (a : AmbientM α) :
    PrefixPreserves StateInv HistorySafe (liftPrefix (liftAmbient a)) :=
  lift_store _ (fun s => productAmbient_spec a (fun w => wgStoreView w.wg = s)
    (fun _ _ hi => hi))

theorem lift_modify (f : World → World)
    (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    PrefixPreserves StateInv HistorySafe (liftPrefix (modify f)) :=
  lift_store _ (fun s => hoare_modify (P := fun w => wgStoreView w.wg = s)
    f (fun w hi => (same w).trans hi))

theorem lift_get : PrefixPreserves StateInv HistorySafe
    (liftPrefix (get : Leanux.M World)) :=
  lift_store _ (fun _ => hoare_consequence (hoare_get _)
    (fun _ hi => hi) (fun _ _ hi => hi.2))

end Leanux.Proofs.WG.Noise.PendingOuter
