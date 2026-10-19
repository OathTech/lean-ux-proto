import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerControls

/-! The native control account is paired with the original control observer.
Configuration's additional entry facts are derived from the same outer entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Controls
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem up : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit envWgUpAudit) :=
  Frames.pair_native _ _ (RxHistory.audit_erases envWgUpAudit_erases)
    HolderEntryControls.up RetiredPeer.Controls.env_up

theorem mtu (n : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit (setMtuAudit n)) :=
  Frames.pair_native _ _ (RxHistory.audit_erases (setMtuAudit_erases n))
    (HolderEntryControls.mtu n) (ControlFrames.mtu n)

theorem route : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit routeIntoWg0Audit) :=
  Frames.pair_native _ _ (RxHistory.audit_erases routeIntoWg0Audit_erases)
    HolderEntryControls.route (ControlFrames.product _ routeIntoWg0_sameKernel)

theorem deladdr (family : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit (wgDeladdrAudit family)) :=
  Frames.pair_native _ _ (RxHistory.audit_erases (wgDeladdrAudit_erases family))
    (HolderEntryControls.deladdr family) (ControlFrames.product _ (wgDeladdr_sameKernel family))

theorem delroute (family : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit (wgDelrouteAudit family)) :=
  Frames.pair_native _ _ (RxHistory.audit_erases (wgDelrouteAudit_erases family))
    (HolderEntryControls.delroute family) (ControlFrames.product _ (wgDelroute_sameKernel family))

theorem cleanup : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit envNetnsCleanupAudit) :=
  Frames.pair_native _ _ (RxHistory.audit_erases envNetnsCleanupAudit_erases)
    HolderEntryControls.cleanup RetiredPeer.Controls.cleanup

theorem multicast (family addr : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe
    (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  Frames.pair_native _ _ (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
    (HolderEntryControls.multicast family addr) (ControlFrames.product _
      ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr))

theorem cleanup_boundary : Preserves Boundary Env.netnsCleanup :=
  Frames.boundary _ _ (RxHistory.audit_erases envNetnsCleanupAudit_erases) (fun _ => cleanup)

theorem configuration_store (hi : ConfigurationDeviceBoundary.Entry cs loans w)
    (same : wgStoreView v=wgStoreView w) : ConfigurationDeviceBoundary.Entry cs loans v := by
  apply ConfigurationDevice.fields_keeps _ hi
  exact congrArg (fun s : WGStoreView => ConfigurationDevice.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) same

theorem configuration_native (attrs : DeviceAttrs) :
    Preserves (fun w : World => ConfigurationDeviceBoundary.Entry cs loans w.wg)
      (Leanux.dispatch (.wgSet attrs)) :=
  Frames.netlink _ (fun _ _ same hi => configuration_store hi same) _
    (Frames.lift _ _ (ConfigurationDevice.device attrs))

theorem configuration (attrs : DeviceAttrs) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSet attrs)) := by
  apply Frames.pair _ _ (RxHistory.syscallDispatch_erases _) (HolderEntryPollFree.configuration attrs)
  intro w h hi result v run
  exact ((hoare_iff_run _ _ _).mp (configuration_native attrs) w result v
    ⟨hi.2,hi.1.1.1.2.1,hi.1.1.1.2.2⟩ run).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Controls
