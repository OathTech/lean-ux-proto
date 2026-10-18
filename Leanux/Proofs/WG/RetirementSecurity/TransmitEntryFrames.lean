import Leanux.Proofs.WG.RetirementSecurity.RemovalPeerFunding

/-! Native transmit entry changes staging and routing bookkeeping only.
The actual destination lookup contributes a peer borrow, independently from
all key references and packet-allocation geometry. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits StagingOccurrences

namespace TransmitEntry
abbrev Held (temporary : Credits.Ledger) (w : WGWorld) := HolderAccount temporary w ∧ Packets.Inv w

theorem fields {action : WG.M α} (own : SameView ownershipPointView action)
    (geom : SameView geometry action) : Preserves (Held temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp own w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (geometry_bound geom) w a result v b before.2 run⟩

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Held temporary) action :=
  fields (ownershipPoints_kernel _ same)
    (same.of_factor (fun s => geometry {dev := s.dev}) geometry (fun _ => rfl))

theorem trim (pid : PeerId) : Preserves (Held temporary) (xmitTrim pid) := by
  apply fields
  · intro initial
    change Preserves (fun w => ownershipPointView w = initial) _
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' first
      | (rx_retention_head ForIn.forIn
         apply list_view_spec id (fun w => ownershipPointView w = initial)
         intro x b
         change Preserves (fun w => ownershipPointView w = initial) _)
      | ownership_source_step initial
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    unfold xmitTrim
    simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
    repeat' staging_geometry_step initial

theorem splice (pid : PeerId) (packets : List WG.Packet) :
    Preserves (Held temporary) (xmitSplice pid packets) := by
  apply fields
  · intro initial
    change Preserves (fun w => ownershipPointView w = initial) _
    unfold xmitSplice
    repeat' ownership_source_step initial
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    unfold xmitSplice
    repeat' staging_geometry_step initial

theorem errors : Preserves (Held temporary) (modifyDev fun d => {d with txErrors := d.txErrors + 1}) := by
  apply fields
  · exact ownership_modifyDev _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · intro initial
    change Preserves (fun w => geometry w = initial) _
    repeat' staging_geometry_step initial

theorem check (family addr : Nat) (ps : List WG.Packet) (mtu : Nat) :
    Preserves (Held temporary) (Packets.txCheck family addr ps mtu) := by
  unfold Packets.txCheck WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Packets.txHeaders; exact store (txHeaders_kernel _ _ _))
    | (rx_retention_head modifyDev; exact errors)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | allocation_release_step

theorem error (family : Nat) (first : WG.Packet) (ret : Int) :
    Preserves (Held temporary) (Packets.txError family first ret) := by
  unfold Packets.txError skipCutSites
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head loopbackSend; exact store (loopbackSend_kernel _ _))
    | (rx_retention_head modifyDev; exact errors)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (allocation_release_lift_from Net.M; exact store (liftRouting_sameWGStore _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Held temporary)
       intro x b
       change Preserves (Held temporary) _)
    | allocation_release_step

theorem lookup (before : Held temporary w) (family addr : Nat) (a b : Ambient)
    (run : ((lookupDst family addr).run w).run a = .ok ((result,v),b)) : Held temporary v := by
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none =>
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    exact ⟨before.1.points (by
      unfold ownershipPointView keyReferenceView
      simp only [keyAt,ownershipAt,peerAt,packetKeyWords,same]),by simpa only [Packets.Inv,Packets.snapshot,same] using before.2⟩
  | some pid =>
    obtain ⟨d,p,device,found,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev after
    have equal : ownershipPointView v = ownershipPointView (replacePeer w d pid {p with refcount := p.refcount + 1}) := by
      unfold ownershipPointView keyReferenceView
      simp only [keyAt,ownershipAt,peerAt,packetKeyWords,replacePeer,endpoint]
    exact ⟨before.1.points (equal.trans (ownershipPoint_replace device found rfl)),
      by simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,endpoint,device] using before.2⟩

end TransmitEntry
end Leanux.Proofs.WG.RetirementSecurity
