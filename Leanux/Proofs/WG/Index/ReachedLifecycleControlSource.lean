import Leanux.Proofs.WG.Index.ReachedControlFrames
import Leanux.Proofs.WG.Index.ReachedControlJoinSource
import Leanux.Proofs.WG.Index.LifecycleCleanupRuleSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedControls
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem delete_input (cs : Ledger) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs [] w.wg ∧ Reached.Core w.wg) Env.wgDelete := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  have start : ConfigurationIndex.Entry cs [] w.wg := ⟨pre.1.1,pre.1.2.2,pre.2⟩
  obtain ⟨_,_,ending,physical⟩ := (hoare_iff_run _ _ _).mp
    (LifecycleEnvironment.delete_entry cs) w result v ⟨start,pre.1.2.1⟩ run
  exact ⟨⟨ending.1,physical,ending.2.1⟩,ending.2.2⟩

theorem rtnetlink_configuration
    (cs : Ledger) (loans : Reservations) (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) body) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) (rtnetlinkRequest body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec)
    _ (fun w v same pre=>LifecycleEnvironment.entry_store cs loans w.wg v.wg same pre) body keeps

theorem cleanup_entry (cs : Ledger) (loans : Reservations) :
    Preserves (fun w : World=>ConfigurationIndex.Entry cs loans w.wg) Env.netnsCleanup :=
  Noise.LifecycleSource.cleanup_preserves _
    (fun action same=>LifecycleEnvironment.product_entry cs loans action same)
    (LifecycleEnvironment.lift_entry cs loans _ (LifecycleEnvironment.preexit_entry cs loans))

theorem configuration (attrs : DeviceAttrs) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSet attrs)) := by
  apply configuration_pair _ _ (RxHistory.syscallDispatch_erases (.wgSet attrs))
    (fun _=>HolderEntryPollFree.configuration attrs)
  intro cs
  exact DumpCore.netlinkRequest_preserves _ _
    (LifecycleEnvironment.lift_entry cs [] _ (ConfigurationIndex.device_entry cs [] attrs))

theorem create :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgCreate) := by
  apply configuration_pair _ _ (RxHistory.syscallDispatch_erases .wgCreate)
    (fun _=>HolderEntryPollFree.create)
  intro cs
  exact rtnetlink_configuration cs [] _
    (LifecycleEnvironment.lift_entry cs [] _ (LifecycleIndex.create_entry cs []))

theorem up :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgUp) := by
  apply configuration_pair _ _ (RxHistory.syscallDispatch_erases .wgUp)
    (fun _=>HolderEntryPollFree.up)
  intro cs
  exact DumpCore.socketCallOn_preserves _ _ _ (LifecycleEnvironment.up_entry cs [])

theorem down :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgDown) := by
  apply configuration_pair _ _ (RxHistory.syscallDispatch_erases .wgDown)
    (fun _=>HolderEntryPollFree.down)
  intro cs
  exact DumpCore.socketCallOn_preserves _ _ _ (LifecycleEnvironment.down_entry cs [])

theorem delete :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch .wgDelete) := by
  apply original_pair _ _ (RxHistory.syscallDispatch_erases .wgDelete)
    (fun _=>HolderEntryPollFree.delete)
  intro cs w h pre result v run
  have kept := (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec)
    _ (delete_input_store cs) Env.wgDelete (delete_input cs)
  exact ((hoare_iff_run _ _ _).mp kept w result v ⟨pre.1.1,pre.2⟩ run).2

theorem mtu (n : Nat) :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSetMtu n)) := by
  apply original_pair _ _ (RxHistory.syscallDispatch_erases (.wgSetMtu n))
    (fun _=>HolderEntryPollFree.mtu n)
  intro cs w h pre result v run
  exact (hoare_iff_run _ _ _).mp
    (DumpCore.socketCallOn_preserves Reached.Core _ _ (mtu_core n)) w result v pre.2 run

theorem cleanup :
    PrefixPreserves Reached.AnyEntry OwnerChecks.Safe (RxHistory.audit envNetnsCleanupAudit) :=
  configuration_pair _ _ (RxHistory.audit_erases envNetnsCleanupAudit_erases)
    (fun _=>HolderEntryControls.cleanup) (fun cs=>cleanup_entry cs [])

end Leanux.Proofs.WG.Index.ReachedControls
