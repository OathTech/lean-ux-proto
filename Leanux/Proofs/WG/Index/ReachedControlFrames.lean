import Leanux.Proofs.WG.Index.ReachedControlBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedControls
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem mtu_fields (w : World) :
    (envScalarView w).2.2.2.dev.map ConfigurationIndex.deviceFields =
      ConfigurationIndex.fields w.wg := by
  simp only [envScalarView,envScalarStore,productStoreView,wgStoreView,
    ConfigurationIndex.fields,Option.map_map,Function.comp_def]
  rfl

theorem mtu_core (n : Nat) :
    Preserves (fun w : World=>Reached.Core w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  apply ConfigurationIndex.fields_core w.wg v.wg _ pre
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w result v run
  rw [←mtu_fields v,←mtu_fields w,same]

theorem delete_input_store (cs : Ledger) (w v : World)
    (same : wgStoreView v.wg=wgStoreView w.wg)
    (pre : DeviceAuxEntry.Entry cs [] w.wg ∧ Reached.Core w.wg) :
    DeviceAuxEntry.Entry cs [] v.wg ∧ Reached.Core v.wg :=
  ⟨HolderEntryFrames.store pre.1 same,
    Reached.core_device (congrArg WGStoreView.dev same) pre.2⟩

theorem configuration_wg_store {α : Type} (cs : Ledger) (loans : Reservations)
    (action : Leanux.M α) (same : SameView (fun w : World=>wgStoreView w.wg) action) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  exact LifecycleEnvironment.entry_store cs loans w.wg v.wg
    ((ProjectedAction.iff_run _ _ _).mp same w result v run) pre

theorem route_delete_store (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    SameView (fun w : World=>wgStoreView w.wg)
      (Env.wgDelroute family named dst plen oif typeCode metric) := by
  unfold Env.wgDelroute
  syscall_routing_store

theorem route_add_store (dst plen oif typeCode metric mtu flags : Nat) :
    SameView (fun w : World=>wgStoreView w.wg)
      (Env.wgAddroute dst plen oif typeCode metric mtu flags) := by
  unfold Env.wgAddroute
  syscall_routing_store

theorem address_add_store (addr plen : Nat) :
    SameView (fun w : World=>wgStoreView w.wg) (Env.wgAddaddr addr plen) := by
  unfold Env.wgAddaddr
  syscall_routing_store

end Leanux.Proofs.WG.Index.ReachedControls
