import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedAfterSocket
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionTimerGeometry

/-! Native completion timer operations frame every component of the same
indexed entry: packet frontiers, staged queues, material and physical owners.
Observed callback histories and stopped source cuts are composed separately. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

theorem entry_frame_of_parts {action : WG.M α}
    (material : SameView PacketOrigins.snapshot action)
    (staged : SameView Staged.stagedAt action)
    (geometry : SameView StagingOccurrences.geometry action)
    (ownership : SameView ownershipPointView action) :
    SameView StagedEntry.view action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b native
  exact entry_view_of_parts
    ((ProjectedAction.iff_run_ambient _ _ _).mp material w a value v b native)
    ((ProjectedAction.iff_run_ambient _ _ _).mp staged w a value v b native)
    ((ProjectedAction.iff_run_ambient _ _ _).mp geometry w a value v b native)
    ((ProjectedAction.iff_run_ambient _ _ _).mp ownership w a value v b native)

theorem traversal_entry_view (pid : PeerId) : SameView StagedEntry.view (timersTraversal pid) :=
  entry_frame_of_parts (PacketOrigins.snapshot_wire (timersTraversal_cryptWire pid))
    (Staged.Exact.traversal pid) (CompletionGeometry.timersTraversal_geometry pid)
    (timersTraversal_ownership pid)

theorem dataSent_entry_view (pid : PeerId) : SameView StagedEntry.view (timersDataSent pid) :=
  entry_frame_of_parts (PacketOrigins.snapshot_wire (timersDataSent_cryptWire pid))
    (Staged.Exact.data_sent pid) (CompletionGeometry.timersDataSent_geometry pid)
    (timersDataSent_ownership pid)

theorem authenticated_entry_view (pid : PeerId) :
    SameView StagedEntry.view (timersAnyAuthenticatedPacketSent pid) :=
  entry_frame_of_parts (PacketOrigins.snapshot_wire (delTimer_cryptWire pid .sendKeepalive))
    (Staged.Exact.delete_timer pid .sendKeepalive) (CompletionGeometry.delTimer_geometry pid .sendKeepalive)
    (delTimer_ownership pid .sendKeepalive)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
