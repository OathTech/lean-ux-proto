import Leanux.Proofs.WG.Noise.PendingDeviceConfigurationFrames
import Leanux.Proofs.WG.Noise.PendingSchedulerFrames
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames
import Leanux.Proofs.WG.Queues.JointDelete
import Leanux.Proofs.WG.Origins.CurrentRemaining

/-! Native pending-ticket preservation for the original environment lifecycle.
The source contracts concern normal results; the actual audit observers also
preserve confirmation-label safety when execution stops. -/

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingEnvironment
open Leanux Leanux.WG Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open PendingSession PendingReception

theorem routing {α : Type} (action : Net.M α) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (monadLift action : Leanux.M α) :=
  PendingScheduler.product_store _ (fun initial => productRouting_spec action (fun s => s = initial)) seen

theorem fixture_modify (f : EnvWorld → EnvWorld) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (modifyEnv f) :=
  PendingScheduler.product_store _ (by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    cases run
    rfl) seen

theorem worker (kind : Worker) (body : Leanux.M Unit) (seen : List Nat)
    (normal : Preserves (fun w : World => NativeInv w.wg seen) body) :
    Preserves (fun w : World => NativeInv w.wg seen) (Env.runWorker kind body) :=
  TimerDiscipline.runWorker_kernel_contract kind body
    (fun wg _ _ _ => NativeInv wg seen) (fun wg _ _ _ => NativeInv wg seen) normal

theorem inetdev_destroy (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) Env.inetdevDestroy :=
  PendingScheduler.product_store _
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store) seen

theorem native_lift {α : Type} (action : WG.M α)
    (normal : ∀ seen, Preserves (fun w => NativeInv w seen) action) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (monadLift action : Leanux.M α) :=
  native_product action normal seen

end Leanux.Proofs.WG.Noise.PendingEnvironment
