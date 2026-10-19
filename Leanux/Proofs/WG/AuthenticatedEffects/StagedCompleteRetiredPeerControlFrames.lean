import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationDeviceSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxHistoryFrames
import Leanux.Proofs.WG.Queues.HolderEntryControls

/-! Native lifecycle control fields are kept in one explicit frame projection.
The upper and lower reference bounds stay on the same chosen holder account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ControlFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem stored {action : WG.M α} (same : SameWGStore action) :
    Preserves (ExactBoundary cs loans) action := ExactBoundary.native_store same

theorem socket {action : WG.M α} (same : SameSocket action) :
    Preserves (ExactBoundary cs loans) action := ExactBoundary.native_fields (NativeFrames.socket same)

theorem modifyDevice (f : Device → Device)
    (same : ∀ w, HolderEncrypt.fields {w with dev := w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (ExactBoundary cs loans) (modifyDev f) := by
  apply hoare_modify
  intro w account
  exact account.fields (same w)

theorem product (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) action :=
  ExactBoundary.product_frame action same

theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

theorem routing (action : Net.M α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (monadLift action : Leanux.M α) :=
  product _ (fun initial => productRouting_spec action (fun s => s=initial))

theorem editEnv (f : EnvWorld → EnvWorld) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (modifyEnv f) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases run
  exact hi

theorem mtu (value : Nat) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.setMtu value) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  apply hi.fields
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar value) w result v run
  have fields : HolderEntryFrames.fields v.wg=HolderEntryFrames.fields w.wg := by
    rw [←HolderEntryFrames.scalar_fields v,←HolderEntryFrames.scalar_fields w,same]
  exact congrArg Prod.fst fields

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ControlFrames
