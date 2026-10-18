import Leanux.Proofs.WG.Index.LifecycleDeviceSource
import Leanux.Proofs.WG.Index.LifecycleEnvironmentRuleSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.LifecycleEnvironment
open Leanux Leanux.WG Noise Queues Queues.RxCredits Queues.RxCredits.DurableHolders
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open ConfigurationIndex

theorem entry_store (cs : Ledger) (loans : Reservations) (w v : WGWorld)
    (same : wgStoreView v=wgStoreView w) (pre : Entry cs loans w) :
    Entry cs loans v := by
  have account : DeviceBoundary.Entry cs loans v := by
    apply (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.fields_keeps) (hi:=pre.1)
    exact congrArg (fun s : WGStoreView =>
      (HolderEncrypt.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8},
       BaseCoherence.view {dev:=s.dev},
       ConfiguredIdentity.view {dev:=s.dev})) same
  have slots := CurrentSlots.fields_transport pre.2.1
    (congrArg (fun s : WGStoreView => CurrentSlots.fields {dev:=s.dev}) same)
  exact ⟨account,slots,fields_core w v
    (congrArg (fun s : WGStoreView => s.dev.map deviceFields) same) pre.2.2⟩

theorem product_entry {α : Type} (cs : Ledger) (loans : Reservations)
    (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World => Entry cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  exact entry_store cs loans w.wg v.wg
    (congrArg (fun s : ProductStore43=>s.2.2.2)
      ((ProjectedAction.iff_run _ _ _).mp same w result v run)) pre

end Leanux.Proofs.WG.Index.LifecycleEnvironment
