import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterDispatch
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleDelete

/-! The original down/delete wrappers retain their idle guards and descriptor
returns. Deletion uses physical RX support from this same outer entry; it is
not derived merely from disappearance of a device or peer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem env_down : Preserves (fun w : World => ExactBoundary cs loans w.wg) Env.wgDown := by
  unfold Env.wgDown
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact ExactBoundary.lift _ RetiredPeer.Lifecycle.down)
    | (rx_retention_head Env.requireIdleDevice; exact ControlFrames.product _
        (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
    | retired_control_product

theorem down : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.audit envWgDownAudit) :=
  Frames.pair_native _ _ (RxHistory.audit_erases envWgDownAudit_erases) HolderEntryControls.down env_down

theorem down_dispatch : PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch .wgDown) :=
  Dispatch.checked _ HolderEntryPollFree.down
    (Frames.socket _ (fun _ _ same hi => hi.store same) _ _ env_down)

def DeleteEntry (cs : Ledger) (w : World) : Prop :=
  ExactBoundary cs [] w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg

theorem delete_store (hi : DeleteEntry cs w) (same : wgStoreView v.wg=wgStoreView w.wg) : DeleteEntry cs v :=
  ⟨hi.1.store same,HolderStopPhysical.optional_cell hi.2
    (congrArg (fun d : Option Device => RxRing.nativeCell {dev:=d}) (congrArg WGStoreView.dev same))⟩

theorem delete_native : Preserves (DeleteEntry cs) (Leanux.dispatch .wgDelete) :=
  Frames.rtnetlink _ (fun _ _ same hi => delete_store hi same) _ RetiredPeer.Lifecycle.delete

theorem delete : PrefixPreserves (Inv cs []) OwnerChecks.Safe (RxHistory.audit envWgDeleteAudit) := by
  apply Frames.pair _ _ (RxHistory.audit_erases envWgDeleteAudit_erases) HolderEntry.delete
  intro w h hi result v run
  exact ((hoare_iff_run _ _ _).mp RetiredPeer.Lifecycle.delete w result v
    ⟨hi.2,hi.1.1.2.1⟩ run).1

theorem delete_dispatch : PrefixPreserves (Inv cs []) OwnerChecks.Safe (RxHistory.syscallDispatch .wgDelete) := by
  apply Frames.pair _ _ (RxHistory.syscallDispatch_erases _) HolderEntryPollFree.delete
  intro w h hi result v run
  exact ((hoare_iff_run _ _ _).mp delete_native w result v ⟨hi.2,hi.1.1.2.1⟩ run).1

theorem down_boundary : Preserves Boundary Env.wgDown :=
  Frames.boundary _ _ (RxHistory.audit_erases envWgDownAudit_erases) (fun _ => down)

theorem delete_boundary : Preserves Boundary Env.wgDelete :=
  Frames.boundary _ _ (RxHistory.audit_erases envWgDeleteAudit_erases) (fun _ => delete)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Lifecycle
