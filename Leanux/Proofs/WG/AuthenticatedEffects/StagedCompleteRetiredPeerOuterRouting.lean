import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterLifecycle

/-! Retained route/address/clock syscalls change no charged WG holder. The
native guards and original outer observations are kept intact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Dispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

private theorem delroute_native (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg)
      (Env.wgDelroute family named dst plen oif typeCode metric) := by
  unfold Env.wgDelroute
  simp (config := {zeta := false}) only [unsupported]
  repeat' retired_control_product

private theorem addroute_native (dst plen oif typeCode metric mtu flags : Nat) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg)
      (Env.wgAddroute dst plen oif typeCode metric mtu flags) := by
  unfold Env.wgAddroute
  simp (config := {zeta := false}) only [invariant]
  repeat' retired_control_product

private theorem addaddr_native (addr plen : Nat) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.wgAddaddr addr plen) := by
  unfold Env.wgAddaddr
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => ExactBoundary cs loans w.wg)
       intro _ _
       change Preserves (fun w : World => ExactBoundary cs loans w.wg) _)
    | retired_control_product

theorem deladdr (family : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgDeladdr family)) :=
  checked _ (HolderEntryPollFree.deladdr family)
    (Frames.rtnetlink _ (fun _ _ same hi => hi.store same) _
      (ControlFrames.product _ (wgDeladdr_sameKernel family)))

theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgDelroute family named dst plen oif typeCode metric)) :=
  checked _ (HolderEntryPollFree.delroute family named dst plen oif typeCode metric)
    (Frames.rtnetlink _ (fun _ _ same hi => hi.store same) _
      (delroute_native family named dst plen oif typeCode metric))

theorem addroute (dst plen oif typeCode metric mtu flags : Nat) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgAddroute dst plen oif typeCode metric mtu flags)) :=
  checked _ (HolderEntryPollFree.addroute dst plen oif typeCode metric mtu flags)
    (Frames.rtnetlink _ (fun _ _ same hi => hi.store same) _
      (addroute_native dst plen oif typeCode metric mtu flags))

theorem addaddr (addr plen : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgAddaddr addr plen)) :=
  checked _ (HolderEntryPollFree.addaddr addr plen)
    (Frames.rtnetlink _ (fun _ _ same hi => hi.store same) _ (addaddr_native addr plen))

theorem advance (ticks : Nat) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgAdvance ticks)) := by
  apply checked _ (HolderEntryPollFree.advance ticks)
  unfold Leanux.dispatch
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance; exact ControlFrames.product _ (advance_sameKernel _))
    | (allocation_release_lift_from FS.M; exact productFS_spec _ _ (fun _ _ _ _ hi => hi))
    | retired_control_product

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer.Dispatch
