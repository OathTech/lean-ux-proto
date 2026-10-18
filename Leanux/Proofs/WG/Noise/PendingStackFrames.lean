import Leanux.Proofs.WG.Noise.PendingReceptionFrames
import Leanux.Proofs.WG.Noise.PendingObserverSource
import Leanux.Proofs.WG.Queues.CurrentSlotStack
import Leanux.Proofs.WG.Origins.CurrentStack
import Leanux.Proofs.WG.Lifetimes.StackSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise.PendingStack
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PendingReception

/-- Pending-slot projection of C1's exact original destination acquisition. -/
theorem lookupDst_frame (family addr : Nat) :
    SameView PendingTickets.view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.lookupDst_view) family addr)
    w ambient result v after run
  apply PendingTickets.view_same w v ?_
    ((ProjectedAction.iff_run_ambient _ _ _).mp (Keypairs.WGDevice.lookupDst_sameSnapshot family addr)
      w ambient result v after run)
  funext pid
  have next := congrArg (fun item : Option Affiliation.State =>
    item.bind fun s => (s.peers pid).bind (fun cell => cell.2.2.2.2)) same
  simpa [PendingTickets.nextSlots,Affiliation.view,Affiliation.state,Affiliation.peerCell,
    Option.bind_map,Option.map_bind,Option.bind_assoc,Function.comp_def] using next

/-- Pending-view variant of CurrentSlots.trim_preserves. Existing saved-peer
field rules and snapshot source rules cover the actual bounded trim loop. -/
theorem xmitTrim_pending_variant (pid : PeerId) :
    SameView PendingTickets.view (xmitTrim pid) := by
  have fields : SameView CurrentSlots.fields (xmitTrim pid) := by
    intro initial
    change Preserves (fun w => CurrentSlots.fields w = initial) (xmitTrim pid)
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' first
      | (rx_retention_head ForIn.forIn
         apply list_view_spec CurrentSlots.fields (fun s => s = initial)
         intro x b
         change Preserves (fun w => CurrentSlots.fields w = initial) _)
      | slot_fields_step initial
  have keys : Keypairs.SameSnapshot (xmitTrim pid) := by
    snapshot_source [xmitTrim] using [Keypairs.WGFrames.getPeer_sameSnapshot,
      Keypairs.WGFrames.setPeer_sameSnapshot]
  exact PendingTickets.frame_from_fields fields keys

/-- Pending-view variant of CurrentSlots.splice_preserves, retaining both
original peer reads via the shared field proof rules. -/
theorem xmitSplice_pending_variant (pid : PeerId) (packets : List Packet) :
    SameView PendingTickets.view (xmitSplice pid packets) := by
  have fields : SameView CurrentSlots.fields (xmitSplice pid packets) := by
    intro initial
    change Preserves (fun w => CurrentSlots.fields w = initial) (xmitSplice pid packets)
    unfold xmitSplice
    repeat' slot_fields_step initial
  have keys : Keypairs.SameSnapshot (xmitSplice pid packets) := by
    snapshot_source [xmitSplice] using [Keypairs.WGFrames.getPeer_sameSnapshot,
      Keypairs.WGFrames.setPeer_sameSnapshot]
  exact PendingTickets.frame_from_fields fields keys

theorem lookupDst_native (family addr : Nat) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (lookupDst family addr) :=
  native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.lookupDst_view) family addr)
    (CurrentSlots.view_preserves (project := id)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.lookupDst_view) family addr))
    (lookupDst_frame family addr) seen

theorem xmitTrim_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (xmitTrim pid) :=
  native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitTrim_view) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.trim_preserves) pid)
    (xmitTrim_pending_variant pid) seen

theorem xmitSplice_native (pid : PeerId) (packets : List Packet) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (xmitSplice pid packets) :=
  native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitSplice_view) pid packets)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.splice_preserves) pid packets)
    (xmitSplice_pending_variant pid packets) seen

theorem staged_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (sendStagedPackets pid) :=
  native_preserves _ (ConfiguredTraffic.staged pid) (CurrentSlots.sendStagedPackets_preserves pid)
    (PendingTickets.sendStagedPackets_retained pid) seen

end Leanux.Proofs.WG.Noise.PendingStack
