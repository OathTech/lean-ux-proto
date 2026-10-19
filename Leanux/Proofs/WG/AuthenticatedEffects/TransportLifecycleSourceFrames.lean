import Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycleFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierRemoval

/-! Concrete native leaf frames at the callback-parametric lifecycle cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycle
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransportPublication

theorem pending_rx (pid : PeerId) (message : String) :
    SameView RxDisposition.nativeRxStore (requireNotPending pid message) := by
  unfold requireNotPending
  repeat' first
    | solve | transport_native_rx
    | (snapshot_head Bind.bind; apply SameView.bind)
    | keypairs_intro_forall

theorem finish (history : List TransportDriver.OriginEvent) : Preserves (Inv history)
    (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish) := by
  index_unfold _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head mayHaveSlept; exact TransportPublication.store_preserves mayHaveSlept_sameWGStore history)
    | (rx_retention_head ratelimiterUninit
       exact preserves_of_rx _ (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycleFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycle.limiter_rx) history)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact absent history _ rfl)
    | (rx_retention_head retireDeviceUnits; exact TransportPublication.store_preserves retireDeviceUnits_sameWGStore history)
    | transport_lifecycle_step history

end Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycle
