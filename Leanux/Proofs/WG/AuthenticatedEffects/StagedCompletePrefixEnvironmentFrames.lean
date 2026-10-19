import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeferredFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEnvironmentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteOuterNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceCreation

/-! Native environment leaves keep literal histories; creation and cleanup
retain their original complete native allocation/packet endpoints. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

theorem idle_device : Checked (liftPrefix Env.requireIdleDevice) :=
  native _ CompleteProduct.idle_device

theorem inetdev : Checked (liftPrefix Env.inetdevDestroy) :=
  native _ CompleteProduct.inetdev

theorem cleanup : Checked (liftPrefix Env.netnsCleanup) :=
  native _ CompleteProduct.cleanup

theorem created : StateChecked (liftWGPrefix wgCreate) :=
  StateEnsures.quiet CompleteDeviceCreation.checked (fun _ _ _=>rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
